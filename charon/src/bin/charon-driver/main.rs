//! The Charon driver, which calls Rustc with callbacks to compile some Rust
//! crate to LLBC.
// For rustdoc: prevents overflows
#![recursion_limit = "256"]
#![feature(rustc_private)]
#![allow(clippy::arc_with_non_send_sync)]
#![allow(clippy::borrowed_box)]
#![allow(clippy::derivable_impls)]
#![allow(clippy::field_reassign_with_default)]
#![allow(clippy::manual_map)]
#![allow(clippy::mem_replace_with_default)]
#![allow(clippy::useless_format)]
#![feature(deref_patterns)]
#![feature(iter_array_chunks)]
#![feature(iterator_try_collect)]
#![feature(sized_hierarchy)]
#![feature(type_changing_struct_update)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_transform;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_structures;
extern crate rustc_symbol_mangling;
extern crate rustc_target;
extern crate rustc_thread_pool;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

#[macro_use]
extern crate charon_lib;

// Overrides `malloc` & co for the whole process, see the `jemalloc` feature.
#[cfg(all(feature = "jemalloc", not(windows)))]
use tikv_jemalloc_sys as _;
// jemalloc's default configuration (`MALLOC_CONF` overrides it). By default each thread of rustc's
// parallel front-end gets its own arena; a single arena lets them reuse each other's freed memory.
#[cfg(all(feature = "jemalloc", not(windows), not(target_vendor = "apple")))]
#[unsafe(export_name = "malloc_conf")]
static MALLOC_CONF: &u8 = &b"narenas:1\0"[0];

mod driver;
#[macro_use]
pub mod hax;
#[allow(unused)]
#[path = "../charon/toolchain.rs"]
mod toolchain;
mod translate;

use charon_lib::logger;
use std::{fmt, panic};

pub enum CharonFailure {
    /// The usize is the number of errors.
    CharonError(usize),
    RustcError,
    Panic,
    Serialize,
    MiniRustTranslationError,
    MiniRustPanic,
    MiniRustUb,
    MiniRustOther,
}

impl fmt::Display for CharonFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CharonFailure::RustcError => write!(f, "Code failed to compile")?,
            CharonFailure::CharonError(err_count) => write!(
                f,
                "Charon failed to translate this code ({err_count} errors)"
            )?,
            CharonFailure::Panic => write!(f, "Compilation panicked")?,
            CharonFailure::Serialize => write!(f, "Could not serialize output file")?,
            CharonFailure::MiniRustTranslationError => {
                write!(f, "Could not compile the program to MiniRust")?
            }
            CharonFailure::MiniRustPanic => write!(f, "MiniRust program panicked")?,
            CharonFailure::MiniRustUb => write!(f, "MiniRust program encountered UB")?,
            CharonFailure::MiniRustOther => write!(f, "MiniRust execution failed")?,
        }
        Ok(())
    }
}

/// Run charon. Returns the number of warnings generated.
fn run_charon() -> Result<usize, CharonFailure> {
    // Run the driver machinery. This translates the crate and runs the transformation passes, which
    // simplify the items and cleanup the bodies.
    let Some((output, options)) = driver::run_rustc_driver()? else {
        // We didn't run charon.
        return Ok(0);
    };
    let driver::TransformOutput {
        crate_data,
        error_count,
        files,
    } = output;

    // # Final step: move the serialized files to their destination.
    for (tmp, target) in files.map_err(|()| CharonFailure::Serialize)? {
        if std::fs::rename(&tmp, &target).is_err() {
            // E.g. the target is on another file system, or not a regular file.
            let copied = std::fs::copy(&tmp, &target);
            let _ = std::fs::remove_file(&tmp);
            if copied.is_err() {
                log::error!("Could not write to {target:?}");
                return Err(CharonFailure::Serialize);
            }
        }
    }
    let crate_name = crate_data.translated.crate_name.clone();
    #[cfg(feature = "minirust")]
    if options.run_with_minirust {
        charon_lib::timing::time("run-with-minirust", || {
            charon_lib::minirust::run::<minirust_rs::prelude::x86_64>(&crate_data.translated)
        })
        .map_err(|err| {
            use charon_lib::minirust::RunError;
            match err {
                RunError::Translation(error) => {
                    anstream::eprintln!(
                        "{}\n",
                        error.render(&crate_data.translated, charon_lib::errors::Level::ERROR)
                    );
                    CharonFailure::MiniRustTranslationError
                }
                RunError::Panic => CharonFailure::MiniRustPanic,
                RunError::Ub(message) => {
                    anstream::eprintln!("MiniRust UB: {message}");
                    CharonFailure::MiniRustUb
                }
                RunError::Other(error) => {
                    anstream::eprintln!("MiniRust execution failed: {error:?}");
                    CharonFailure::MiniRustOther
                }
            }
        })?;
    }
    // Freeing the translated crate takes a noticeable time; let the OS reclaim it at exit instead.
    std::mem::forget(crate_data);
    charon_lib::timing::report(&crate_name);

    if options.error_on_warnings && error_count != 0 {
        return Err(CharonFailure::CharonError(error_count));
    }

    Ok(error_count)
}

fn main() {
    // Initialize the logger
    logger::initialize_logger();
    charon_lib::transform::ctx::install_panic_hook();

    // Catch any and all panics coming from charon to display a clear error.
    let res = panic::catch_unwind(run_charon)
        .map_err(|_| CharonFailure::Panic)
        .and_then(|x| x);

    match res {
        Ok(warn_count) => {
            if warn_count != 0 {
                let msg = format!("The extraction generated {} warnings", warn_count);
                eprintln!("warning: {}", msg);
            }
        }
        Err(err) => {
            log::error!("{err}");
            let exit_code = match err {
                CharonFailure::CharonError(_)
                | CharonFailure::Serialize
                | CharonFailure::MiniRustTranslationError => 1,
                CharonFailure::RustcError => 2,
                CharonFailure::MiniRustPanic => 3,
                CharonFailure::MiniRustUb => 4,
                CharonFailure::MiniRustOther => 5,
                // This is a real panic, exit with the standard rust panic error code.
                CharonFailure::Panic => 101,
            };
            std::process::exit(exit_code);
        }
    }
}
