"""Turn AST values back into plain json.

The AST is made of dataclasses, which `json` can't serialize. [`to_jsonish`] rewrites them into
dicts, tagging each one with the name of its class under `"@type"` — the class is what tells an
enum's variants apart, and `@` can't appear in a rust field name, so the tag never collides with
one.

This is a rendering for inspection, not charon's own serialized form: values that were
deduplicated in the file (types, spans) are expanded at every occurrence, so dumping a whole crate
produces a great deal more text than the file it came from. Prefer dumping the items you care
about.
"""

from __future__ import annotations

import dataclasses
import json
from typing import Any, Optional

__all__ = ["dumps", "to_jsonish"]

TYPE_KEY = "@type"


def to_jsonish(value: Any, *, max_depth: Optional[int] = None) -> Any:
    """Convert an AST value into something `json.dumps` accepts.

    Past `max_depth` levels of nesting, values are replaced by `"..."`.
    """
    if max_depth is not None and max_depth <= 0:
        return "..."
    depth = None if max_depth is None else max_depth - 1
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        fields = {
            field.name: to_jsonish(getattr(value, field.name), max_depth=depth)
            for field in dataclasses.fields(value)
        }
        return {TYPE_KEY: type(value).__name__, **fields}
    if isinstance(value, dict):
        return {str(key): to_jsonish(item, max_depth=depth) for key, item in value.items()}
    if isinstance(value, (list, tuple, set, frozenset)):
        return [to_jsonish(item, max_depth=depth) for item in value]
    return repr(value)


def dumps(value: Any, *, indent: Optional[int] = None, max_depth: Optional[int] = None) -> str:
    """Render an AST value as json. Pass `indent` for a human-readable dump."""
    return json.dumps(to_jsonish(value, max_depth=max_depth), indent=indent)
