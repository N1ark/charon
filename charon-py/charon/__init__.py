"""Python bindings for charon's (u)llbc ASTs.

The AST types live in `charon.generated.types`; `charon.of_json` and `charon.of_postcard` read a
file emitted by charon in either of the two serialization formats.
"""

from __future__ import annotations

from .errors import DeserializeError
from .generated.of_json import crate_of_json, crate_of_json_file
from .generated.of_postcard import crate_of_postcard, crate_of_postcard_file
from .version import SUPPORTED_CHARON_VERSION

__all__ = [
    "DeserializeError",
    "SUPPORTED_CHARON_VERSION",
    "crate_of_json",
    "crate_of_json_file",
    "crate_of_postcard",
    "crate_of_postcard_file",
]
