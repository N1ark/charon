"""WARNING: this file is auto-generated. Do not edit `types.py` by hand. Edit
`generate_py/templates/types.py` instead, or improve the code generation tool so as to avoid the
need for hand-writing things.

`generate_py/templates/types.py` contains the manual definitions and some `# __REPLACEn__`
comments. These comments are replaced by auto-generated definitions by running `make
generate-asts` in the crate root. The code-generation code is in `charon/src/bin/generate-asts`.

Enums are represented as a union of one dataclass per variant, which is how a type checker
understands a tagged union. Since the AST is deeply recursive, all the annotations here are
forward references; `from __future__ import annotations` makes that work.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Generic, NewType, NoReturn, Optional, TypeAlias, TypeVar, Union

T0 = TypeVar("T0")
T1 = TypeVar("T1")
T2 = TypeVar("T2")
T3 = TypeVar("T3")

# __REPLACE0__
