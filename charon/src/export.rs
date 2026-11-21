mod compact_json;
mod merge;
pub mod multi_crate;
pub mod multi_target;

use crate::ast::*;
#[cfg(feature = "minirust")]
use crate::errors::Level;
use crate::options::SerializationFormat;
use crate::transform::TransformCtx;
use serde::{Deserialize, Deserializer, Serialize};
use serde_state::{DeserializeState, SerializeState};
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

/// The data of a generic crate. We serialize this to pass it to `charon-ml`, so this must be as
/// stable as possible. This is used for both ULLBC and LLBC.
#[derive(SerializeState, DeserializeState)]
pub struct CrateData {
    /// The version of charon currently being used. `charon-ml` inspects this and errors if it is
    /// trying to read an incompatible version (for now we compare versions for equality).
    #[serde_state(stateless)]
    pub charon_version: CharonVersion,
    pub translated: TranslatedCrate,
    #[serde_state(stateless)]
    #[cfg_attr(feature = "charon_on_charon", charon::opaque)] // Don't change, this would break version detection for old charon-ml
    /// If there were errors, this contains only a partial description of the input crate.
    pub has_errors: bool,
}

impl<'de> Deserialize<'de> for CrateData {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Always provide the state, just in case.
        let state = DedupSerializer::default();
        Self::deserialize_state(&state, deserializer)
    }
}

#[derive(Serialize)]
pub struct CharonVersion(pub String);

/// A postcard flavor that buffers the output before handing it to a writer. `postcard::to_io`
/// instead hands each byte or varint to the writer separately, which is slow.
struct PostcardWriter<W> {
    buf: Vec<u8>,
    writer: W,
}

impl<W: Write> PostcardWriter<W> {
    const FLUSH_THRESHOLD: usize = 1 << 16;

    fn new(writer: W) -> Self {
        PostcardWriter {
            buf: Vec::with_capacity(2 * Self::FLUSH_THRESHOLD),
            writer,
        }
    }

    fn flush(&mut self) -> postcard::Result<()> {
        self.writer
            .write_all(&self.buf)
            .map_err(|_| postcard::Error::SerializeBufferFull)?;
        self.buf.clear();
        Ok(())
    }
}

impl<W: Write> postcard::ser_flavors::Flavor for PostcardWriter<W> {
    type Output = ();
    #[inline(always)]
    fn try_push(&mut self, byte: u8) -> postcard::Result<()> {
        self.try_extend(&[byte])
    }
    #[inline(always)]
    fn try_extend(&mut self, data: &[u8]) -> postcard::Result<()> {
        // Most writes are short varints. We flush the buffer once it reaches `FLUSH_THRESHOLD`
        // bytes and it has room for twice that, so these always fit.
        let len = self.buf.len();
        if data.len() <= 32 && self.buf.capacity() - len >= 32 {
            // SAFETY: there is room for `data` in the buffer.
            unsafe {
                let dst = self.buf.as_mut_ptr().add(len);
                // Copying with a known length avoids a `memcpy` call.
                match *data {
                    [a] => dst.write(a),
                    [a, b] => dst.cast::<[u8; 2]>().write_unaligned([a, b]),
                    [a, b, c] => dst.cast::<[u8; 3]>().write_unaligned([a, b, c]),
                    [a, b, c, d] => dst.cast::<[u8; 4]>().write_unaligned([a, b, c, d]),
                    _ => std::ptr::copy_nonoverlapping(data.as_ptr(), dst, data.len()),
                }
                self.buf.set_len(len + data.len());
            }
        } else {
            self.buf.extend_from_slice(data);
        }
        if self.buf.len() >= Self::FLUSH_THRESHOLD {
            self.flush()?;
        }
        Ok(())
    }
    fn finalize(mut self) -> postcard::Result<()> {
        self.flush()?;
        self.writer
            .flush()
            .map_err(|_| postcard::Error::SerializeBufferFull)
    }
}

impl<'de> Deserialize<'de> for CharonVersion {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        use serde::de::Error;
        let version = String::deserialize(deserializer)?;
        if version != crate::VERSION {
            return Err(D::Error::custom(format!(
                "Incompatible version of charon: \
                this program supports llbc emitted by charon v{} \
                but attempted to read a file emitted by charon v{}",
                crate::VERSION,
                version,
            )));
        }
        Ok(CharonVersion(version))
    }
}

impl CrateData {
    pub fn new(ctx: TransformCtx) -> Self {
        CrateData {
            charon_version: CharonVersion(crate::VERSION.to_owned()),
            has_errors: ctx.has_errors(),
            translated: ctx.translated,
        }
    }

    #[allow(clippy::result_unit_err)]
    pub fn serialize_to_files(
        &self,
        targets: Vec<(PathBuf, SerializationFormat)>,
        deduplicate: bool,
    ) -> Result<(), ()> {
        for (target_filename, format) in targets {
            self.serialize_to_file(&target_filename, format, deduplicate)?;
        }
        Ok(())
    }

    /// Export the translated definitions to a file. With `deduplicate`, repeated values are
    /// written only once and JSON structs are written as arrays of their fields (see
    /// [`compact_json`]); without, the file is easier to inspect.
    #[allow(clippy::result_unit_err)]
    pub fn serialize_to_file(
        &self,
        target_filename: &Path,
        format: SerializationFormat,
        deduplicate: bool,
    ) -> Result<(), ()> {
        // Create the directory, if necessary (note that if the target directory
        // is not specified, there is no need to create it: otherwise we
        // couldn't have read the input file in the first place).
        let target_dir = target_filename.parent().unwrap();
        match std::fs::create_dir_all(target_dir) {
            Ok(()) => (),
            Err(_) => {
                error!("Could not create the directory: {:?}", target_dir);
                return Err(());
            }
        };

        // Create the file.
        let std::io::Result::Ok(outfile) = File::create(target_filename) else {
            error!("Could not open: {:?}", target_filename);
            return Err(());
        };
        // Write to the file.
        match format {
            SerializationFormat::Json if deduplicate => {
                if let Err(err) = self.serialize_compact_json(outfile) {
                    error!("Could not serialize to `{target_filename:?}`: {err}");
                    return Err(());
                }
            }
            SerializationFormat::Json => {
                let mut writer = BufWriter::with_capacity(4 * 1024 * 1024, outfile);
                let with_state = serde_state::WithState::new(self, &());
                if let Err(err) = serde_json::to_writer(&mut writer, &with_state) {
                    error!("Could not serialize to `{target_filename:?}`: {err:?}");
                    return Err(());
                }
            }
            SerializationFormat::Postcard => {
                let flavor = PostcardWriter::new(outfile);
                let result = if deduplicate {
                    let state = DedupSerializer::default();
                    postcard::serialize_with_flavor(
                        &serde_state::WithState::new(self, &state),
                        flavor,
                    )
                } else {
                    postcard::serialize_with_flavor(&serde_state::WithState::new(self, &()), flavor)
                };
                if let Err(err) = result {
                    error!("Could not serialize to `{target_filename:?}`: {err:?}");
                    return Err(());
                }
            }
            #[cfg(feature = "minirust")]
            SerializationFormat::MiniRust => {
                let mut writer = BufWriter::with_capacity(4 * 1024 * 1024, outfile);
                if let Err(err) = crate::minirust::serialize(&self.translated, &mut writer) {
                    anstream::eprintln!("{}\n", err.render(&self.translated, Level::ERROR));
                    return Err(());
                }
            }
            #[cfg(not(feature = "minirust"))]
            SerializationFormat::MiniRust => error!("Charon was built without MiniRust support"),
        }

        // We canonicalize (i.e., make absolute) the path before printing it; this makes it clearer
        // to the user where to find the file.
        let target_filename = std::fs::canonicalize(target_filename).unwrap();
        if self.has_errors {
            info!(
                "Generated the partial (because we encountered errors) file: {}",
                target_filename.to_str().unwrap()
            );
        } else {
            info!("Generated the file: {}", target_filename.to_str().unwrap());
        }
        Ok(())
    }

    /// Write the crate in the compact JSON format, deduplicating values.
    fn serialize_compact_json(&self, file: File) -> Result<(), compact_json::Error> {
        use serde::ser::{SerializeMap, Serializer};
        let state = DedupSerializer::default();
        let mut ser = compact_json::Serializer::new(file);
        // The top-level object keeps its keys: `charon-ml` relies on them to detect files
        // emitted by an incompatible version.
        let mut map = (&mut ser).serialize_map(Some(3))?;
        map.serialize_entry("charon_version", &self.charon_version)?;
        map.serialize_entry(
            "translated",
            &serde_state::WithState::new(&self.translated, &state),
        )?;
        map.serialize_entry("has_errors", &self.has_errors)?;
        map.end()?;
        ser.finish()?;
        Ok(())
    }

    pub fn deserialize_from_file(
        path: &std::path::Path,
        format: SerializationFormat,
    ) -> anyhow::Result<Self> {
        use crate::export::CrateData;
        use anyhow::Context;
        use serde::Deserialize;
        use std::fs::File;
        let file = File::open(path)
            .with_context(|| format!("Failed to read llbc file {}", path.display()))?;
        match format {
            SerializationFormat::Json => {
                let reader = BufReader::new(file);
                let mut deserializer = serde_json::Deserializer::from_reader(reader);
                // Deserialize without recursion limit.
                deserializer.disable_recursion_limit();
                // Grow stack space as needed.
                let deserializer = serde_stacker::Deserializer::new(&mut deserializer);
                Ok(CrateData::deserialize(deserializer)?)
            }
            SerializationFormat::Postcard => {
                let mut reader = BufReader::new(file);
                let mut bytes = Vec::new();
                reader.read_to_end(&mut bytes)?;
                let (crate_data, rem) = postcard::take_from_bytes::<CrateData>(&bytes)
                    .map_err(|err| anyhow::anyhow!("postcard deserialize error: {err:?}"))?;
                if !rem.is_empty() {
                    anyhow::bail!("postcard deserialize error: trailing bytes left in input");
                }
                Ok(crate_data)
            }
            SerializationFormat::MiniRust => {
                anyhow::bail!("MiniRust files cannot be read by Charon")
            }
        }
    }
}
