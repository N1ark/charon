"""WARNING: this file is partially auto-generated. Do not edit `of_json.py` by hand. Edit
`generate_py/templates/of_json.py` instead, or improve the code generation tool so as to avoid the
need for hand-writing things.

`generate_py/templates/of_json.py` contains the manual definitions and some `# __REPLACEn__`
comments. These comments are replaced by auto-generated definitions by running `make
generate-asts` in the crate root. The code-generation code is in `charon/src/bin/generate-asts`.
"""

from __future__ import annotations

import json as _json
import os
from dataclasses import dataclass, field

from ..errors import DeserializeError, unknown_variant
from ..json_basic import *
from ..postcard_basic import InputFormat, format_hint
from ..version import SUPPORTED_CHARON_VERSION
from .types import *


@dataclass
class OfJsonCtx:
    """The state threaded through the deserializers.

    Files are serialized once and referred to by id afterwards, and values that come up often are
    deduplicated the same way; these tables hold what we have read so far.
    """

    files: dict[int, File] = field(default_factory=dict)
    ty_kind_dedup: dict[int, TyKind] = field(default_factory=dict)
    trait_ref_contents_dedup: dict[int, TraitRefContents] = field(default_factory=dict)
    constant_expr_dedup: dict[int, ConstantExpr] = field(default_factory=dict)
    exact_size_expr_kind_dedup: dict[int, ExactSizeExprKind] = field(default_factory=dict)
    span_dedup: dict[int, Span] = field(default_factory=dict)


# __REPLACE0__


def crate_of_json(js: Json) -> TranslatedCrate:
    """Read a crate from an already-parsed json value."""
    fields = expect_object(js)
    version = string_of_json(None, fields["charon_version"])
    if version != SUPPORTED_CHARON_VERSION:
        raise DeserializeError(
            "Incompatible version of charon: this program supports llbc emitted by charon "
            f"v{SUPPORTED_CHARON_VERSION} but attempted to read a file emitted by charon "
            f"v{version}."
        )
    return translated_crate_of_json(OfJsonCtx(), fields["translated"])


def crate_of_json_file(path: str | os.PathLike[str]) -> TranslatedCrate:
    """Read a crate from a json-serialized `.llbc`/`.ullbc` file."""
    with open(path, "rb") as file:
        contents = file.read()
    hint = format_hint(contents)
    if hint is InputFormat.POSTCARD:
        raise DeserializeError(
            f"This file looks like Postcard, but JSON deserialization was requested: {path}. "
            "Please use Postcard deserialization or regenerate as JSON."
        )
    if hint is InputFormat.EMPTY:
        raise DeserializeError(f"Input file is empty: {path}")
    return crate_of_json(_json.loads(contents))
