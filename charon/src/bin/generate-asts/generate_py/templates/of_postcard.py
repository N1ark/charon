"""WARNING: this file is partially auto-generated. Do not edit `of_postcard.py` by hand. Edit
`generate_py/templates/of_postcard.py` instead, or improve the code generation tool so as to avoid
the need for hand-writing things.

`generate_py/templates/of_postcard.py` contains the manual definitions and some `# __REPLACEn__`
comments. These comments are replaced by auto-generated definitions by running `make
generate-asts` in the crate root. The code-generation code is in `charon/src/bin/generate-asts`.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field

from ..errors import DeserializeError, unknown_variant
from ..postcard_basic import *
from ..version import SUPPORTED_CHARON_VERSION
from .types import *


@dataclass
class OfPostcardCtx:
    """See `charon.generated.of_json.OfJsonCtx`."""

    files: dict[int, File] = field(default_factory=dict)
    ty_dedup: dict[int, Ty] = field(default_factory=dict)
    trait_ref_dedup: dict[int, TraitRef] = field(default_factory=dict)
    constant_expr_dedup: dict[int, ConstantExpr] = field(default_factory=dict)
    exact_size_expr_dedup: dict[int, ExactSizeExpr] = field(default_factory=dict)
    span_dedup: dict[int, Span] = field(default_factory=dict)


# __REPLACE0__


def crate_of_postcard(contents: bytes) -> TranslatedCrate:
    """Read a crate from the bytes of a postcard-serialized file."""
    st = PostcardReader(contents)
    version = string_of_postcard(None, st)
    if version != SUPPORTED_CHARON_VERSION:
        raise DeserializeError(
            "Incompatible version of charon: this program supports llbc emitted by charon "
            f"v{SUPPORTED_CHARON_VERSION} but attempted to read a file emitted by charon "
            f"v{version}."
        )
    ctx = OfPostcardCtx()
    crate = translated_crate_of_postcard(ctx, st)
    bool_of_postcard(ctx, st)  # whether the translation had errors
    ensure_eof(st)
    return crate


def crate_of_postcard_file(path: str | os.PathLike[str]) -> TranslatedCrate:
    """Read a crate from a postcard-serialized `.llbc.postcard`/`.ullbc.postcard` file."""
    with open(path, "rb") as file:
        contents = file.read()
    hint = format_hint(contents)
    if hint is InputFormat.JSON:
        raise DeserializeError(
            f"This file looks like JSON, but Postcard deserialization was requested: {path}. "
            "Please use JSON deserialization or regenerate as Postcard."
        )
    if hint is InputFormat.EMPTY:
        raise DeserializeError(f"Input file is empty: {path}")
    return crate_of_postcard(contents)
