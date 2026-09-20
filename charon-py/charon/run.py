"""Run the charon binary and read back what it produces.

A script that wants the AST of some crate usually has to build a charon command line, run it, then
find and deserialize the file it wrote. [`extract`] does all three.
"""

from __future__ import annotations

import os
import subprocess
import tempfile
from pathlib import Path
from typing import Optional, Sequence

from .generated.of_json import crate_of_json_file
from .generated.of_postcard import crate_of_postcard_file
from .generated.types import TranslatedCrate

__all__ = ["CharonError", "charon_args", "charon_binary", "extract", "run"]


class CharonError(RuntimeError):
    """The charon binary exited with an error."""


def charon_binary() -> str:
    """The charon binary to run: `$CHARON_BIN` if set, otherwise `charon` from `$PATH`."""
    return os.environ.get("CHARON_BIN", "charon")


def run(
    args: Sequence[str],
    *,
    cwd: Optional[os.PathLike[str] | str] = None,
    binary: Optional[str] = None,
    check: bool = True,
    capture_output: bool = False,
) -> subprocess.CompletedProcess[str]:
    """Run charon with `args`, e.g. `run(["cargo", "--ullbc"], cwd=crate_dir)`."""
    command = [binary or charon_binary(), *args]
    result = subprocess.run(command, cwd=cwd, capture_output=capture_output, text=True)
    if check and result.returncode != 0:
        details = f"\n{result.stderr}" if result.stderr else ""
        raise CharonError(
            f"charon exited with code {result.returncode}: {' '.join(command)}{details}"
        )
    return result


def extract(
    args: Sequence[str],
    *,
    cwd: Optional[os.PathLike[str] | str] = None,
    dest: Optional[os.PathLike[str] | str] = None,
    reuse: bool = False,
    format: str = "postcard",
    binary: Optional[str] = None,
) -> TranslatedCrate:
    """Run charon and deserialize the crate it writes.

    `args` is everything after the binary name, such as
    `["cargo", "--ullbc", "--start-from", "core::intrinsics"]` or
    `["rustc", "--", "foo.rs"]`; `--dest-file` and `--format` are added here, before the `--` that
    separates charon's arguments from the compiler's.

    Pass `dest` to keep the file charon writes, and `reuse=True` to load an existing `dest` instead
    of running charon again — the equivalent of a `--cached` flag for a script that reruns often.
    `format` is the serialization format to ask for; postcard is a good deal faster to read than
    json.
    """
    if format not in ("postcard", "json"):
        raise ValueError(f"unknown serialization format: {format!r}")
    read = crate_of_postcard_file if format == "postcard" else crate_of_json_file

    if dest is not None:
        dest = Path(dest)
        if reuse and dest.exists():
            return read(dest)
        _run_charon(args, dest, format, cwd, binary)
        return read(dest)
    if reuse:
        raise ValueError("`reuse` needs a `dest` to reuse")
    with tempfile.TemporaryDirectory() as tmp_dir:
        output = Path(tmp_dir) / f"crate.{format}"
        _run_charon(args, output, format, cwd, binary)
        return read(output)


def charon_args(args: Sequence[str], dest: Path, format: str) -> list[str]:
    """Insert the arguments that make charon write `dest` in `format`.

    They have to go before the `--` that separates charon's own arguments from the compiler's.
    """
    ours = ["--dest-file", str(dest), f"--format={format}"]
    args = list(args)
    separator = args.index("--") if "--" in args else len(args)
    return args[:separator] + ours + args[separator:]


def _run_charon(
    args: Sequence[str],
    dest: Path,
    format: str,
    cwd: Optional[os.PathLike[str] | str],
    binary: Optional[str],
) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    run(charon_args(args, dest.resolve(), format), cwd=cwd, binary=binary)
