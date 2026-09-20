"""Python bindings for charon's (u)llbc ASTs.

The AST types live in `charon.generated.types`; `charon.of_json` and `charon.of_postcard` read a
file emitted by charon in either of the two serialization formats.
"""

from __future__ import annotations

import json as _json
import os

from .errors import DeserializeError
from .generated.of_json import crate_of_json, crate_of_json_file
from .generated.of_postcard import crate_of_postcard, crate_of_postcard_file
from .generated.types import TranslatedCrate
from .postcard_basic import InputFormat, format_hint
from .version import SUPPORTED_CHARON_VERSION

__all__ = [
    "DeserializeError",
    "SUPPORTED_CHARON_VERSION",
    "crate_of_file",
    "crate_of_json",
    "crate_of_json_file",
    "crate_of_postcard",
    "crate_of_postcard_file",
]


def crate_of_file(path: str | os.PathLike[str]) -> TranslatedCrate:
    """Read a crate from a file in whichever of the two formats it is in."""
    with open(path, "rb") as file:
        contents = file.read()
    hint = format_hint(contents)
    if hint is InputFormat.JSON:
        return crate_of_json(_json.loads(contents))
    if hint is InputFormat.POSTCARD:
        return crate_of_postcard(contents)
    raise DeserializeError(f"Input file is empty: {path}")
