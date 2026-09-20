"""Rendering and matching of item names and types.

Charon names are lists of path elements rather than strings, because an element can be an `impl`
block or an instantiation, which have no canonical spelling. The renderings here are compact and
meant for *identifying* items — looking one up, grouping, printing a table — not for
pretty-printing rust; `charon --print-llbc` does that faithfully.

Passing the crate lets the renderer name the types and traits that path elements refer to by id;
without it those elements fall back to a placeholder.
"""

from __future__ import annotations

import functools
import re
from typing import Optional

from .generated.types import *

__all__ = [
    "builtin_path_elem_ident",
    "impl_elem_to_str",
    "name_matches",
    "name_short",
    "name_to_path",
    "name_to_str",
    "path_elem_to_str",
    "scalar_type_to_str",
    "ty_to_str",
]

_INT_TYPES: dict[type, str] = {
    IntTyIsize: "isize",
    IntTyI8: "i8",
    IntTyI16: "i16",
    IntTyI32: "i32",
    IntTyI64: "i64",
    IntTyI128: "i128",
    UIntTyUsize: "usize",
    UIntTyU8: "u8",
    UIntTyU16: "u16",
    UIntTyU32: "u32",
    UIntTyU64: "u64",
    UIntTyU128: "u128",
}

_FLOAT_TYPES: dict[type, str] = {
    FloatTypeF16: "f16",
    FloatTypeF32: "f32",
    FloatTypeF64: "f64",
    FloatTypeF128: "f128",
}

_BUILTIN_PATH_ELEMS: dict[type, str] = {
    BuiltinPathElemPeStr: "str",
    BuiltinPathElemPeClosure: "closure",
    BuiltinPathElemPeUse: "use",
    BuiltinPathElemPeAnonConst: "const",
    BuiltinPathElemPePromotedConst: "promoted_const",
    BuiltinPathElemPeClosureAsFn: "as_fn",
    BuiltinPathElemPeDropGlue: "drop_glue",
    BuiltinPathElemPeVTable: "vtable",
    BuiltinPathElemPeVTableMethod: "vtable_method",
    BuiltinPathElemPeVTableDropShim: "vtable_drop_shim",
}


def scalar_type_to_str(ty: ScalarType) -> str:
    """The rust spelling of a scalar type, e.g. `u32`."""
    if isinstance(ty, ScalarTypeTInteger):
        return _INT_TYPES[type(ty._0._0)]
    if isinstance(ty, ScalarTypeTFloat):
        return _FLOAT_TYPES[type(ty._0)]
    return "bool" if isinstance(ty, ScalarTypeTBool) else "char"


def builtin_path_elem_ident(elem: BuiltinPathElem) -> str:
    """The name of a path element that doesn't come from the source code."""
    if isinstance(elem, BuiltinPathElemPeTuple):
        return "unit" if elem._0 == 0 else "tuple"
    return _BUILTIN_PATH_ELEMS[type(elem)]


def ty_to_str(ty: Ty, crate: Optional[TranslatedCrate] = None) -> str:
    """A compact rendering of a type.

    Lifetimes and trait references are elided, and the constructs that need a full printer to make
    sense of (patterns, `dyn Trait`, associated types) render as a placeholder.
    """
    if isinstance(ty, TyKindTScalar):
        return scalar_type_to_str(ty._0)
    if isinstance(ty, TyKindTNever):
        return "!"
    if isinstance(ty, TyKindTRef):
        mut = "mut " if isinstance(ty._2, RefKindRMut) else ""
        return f"&{mut}{ty_to_str(ty._1, crate)}"
    if isinstance(ty, TyKindTRawPtr):
        mut = "mut" if isinstance(ty._1, RefKindRMut) else "const"
        return f"*{mut} {ty_to_str(ty._0, crate)}"
    if isinstance(ty, TyKindTArray):
        return f"[{ty_to_str(ty._0, crate)}; _]"
    if isinstance(ty, TyKindTSlice):
        return f"[{ty_to_str(ty._0, crate)}]"
    if isinstance(ty, TyKindTVar):
        var = ty._0
        return f"T{var._0}" if isinstance(var, DeBruijnVarFree) else f"T{var._1}"
    if isinstance(ty, TyKindTAdt):
        return _type_decl_ref_to_str(ty._0, crate)
    if isinstance(ty, TyKindTFnDef):
        return "fn item"
    if isinstance(ty, TyKindTFnPtr):
        return "fn(_)"
    if isinstance(ty, TyKindTDynTrait):
        return "dyn _"
    if isinstance(ty, TyKindTTraitType):
        return "<_ as _>::_"
    if isinstance(ty, TyKindTPtrMetadata):
        return f"<{ty_to_str(ty._0, crate)} as Pointee>::Metadata"
    return "_"


def _type_decl_ref_to_str(tref: TypeDeclRef, crate: Optional[TranslatedCrate]) -> str:
    args = [ty_to_str(arg, crate) for arg in tref.generics.types]
    if isinstance(tref.builtin, BuiltinAdtTTuple):
        # A one-element tuple keeps the comma that distinguishes it from a parenthesized type.
        return f"({args[0]},)" if len(args) == 1 else "({})".format(", ".join(args))
    if isinstance(tref.builtin, BuiltinAdtTStr):
        return "str"
    if isinstance(tref.builtin, BuiltinAdtTBox):
        base = "Box"
    else:
        decl = crate.type_decls.get(tref.id) if crate is not None else None
        base = f"#{tref.id}" if decl is None else (name_short(decl.item_meta.name) or "_")
    return base if not args else "{}<{}>".format(base, ", ".join(args))


def impl_elem_to_str(elem: ImplElem, crate: Optional[TranslatedCrate] = None) -> str:
    """Render the `impl` block a path element refers to."""
    if isinstance(elem, ImplElemTy):
        return f"impl {ty_to_str(elem._0.binder_value, crate)}"
    impl = crate.trait_impls.get(elem._0) if crate is not None else None
    if impl is None:
        return "impl"
    trait = crate.trait_decls.get(impl.impl_trait.id)
    trait_name = name_short(trait.item_meta.name) if trait is not None else None
    # The first type argument of a trait reference is its `Self` type.
    self_args = impl.impl_trait.generics.types
    for_ty = f" for {ty_to_str(self_args[0], crate)}" if self_args else ""
    return f"impl {trait_name or '_'}{for_ty}"


def path_elem_to_str(elem: PathElem, crate: Optional[TranslatedCrate] = None) -> str:
    """Render one element of a name."""
    if isinstance(elem, PathElemPeIdent):
        return elem._0 if elem._1 == 0 else f"{elem._0}#{elem._1}"
    if isinstance(elem, PathElemPeImpl):
        return "{" + impl_elem_to_str(elem._0, crate) + "}"
    if isinstance(elem, PathElemPeInstantiated):
        args = elem._0.binder_value.types
        return "<{}>".format(", ".join(ty_to_str(arg, crate) for arg in args))
    if isinstance(elem, PathElemPeTarget):
        return elem._0
    builtin = elem._0
    # Tuples and `str` are written the way the types themselves are, so that a declaration and its
    # uses don't look like different types.
    if isinstance(builtin, BuiltinPathElemPeTuple):
        return "({})".format(", ".join(["_"] * builtin._0) + ("," if builtin._0 == 1 else ""))
    if isinstance(builtin, (BuiltinPathElemPeStr, BuiltinPathElemPeDropGlue)):
        return builtin_path_elem_ident(builtin)
    ident = builtin_path_elem_ident(builtin)
    return "{" + (ident if elem._1 == 0 else f"{ident}#{elem._1}") + "}"


def name_to_path(name: Name, crate: Optional[TranslatedCrate] = None) -> list[str]:
    """Render each element of a name."""
    return [path_elem_to_str(elem, crate) for elem in name]


def name_to_str(name: Name, crate: Optional[TranslatedCrate] = None) -> str:
    """Render a name as a rust path, e.g. `core::mem::size_of`."""
    return "::".join(name_to_path(name, crate))


def name_short(name: Name) -> Optional[str]:
    """The last identifier of a name, e.g. `size_of` for `core::mem::size_of`.

    Returns `None` for a name that ends in an `impl` block or an instantiation. Builtin elements
    give their identifier rather than their rendering, so the last element of `(_, _)` is `tuple`.
    """
    for elem in reversed(name):
        if isinstance(elem, PathElemPeIdent):
            return elem._0
        if isinstance(elem, PathElemPeBuiltin):
            return builtin_path_elem_ident(elem._0)
        if not isinstance(elem, PathElemPeInstantiated):
            return None
    return None


def name_matches(
    name: Name | str, pattern: str, crate: Optional[TranslatedCrate] = None
) -> bool:
    """Match a name against a glob pattern on its rendered path.

    `*` and `?` stop at a path separator and `**` crosses it, so `core::mem::*` matches
    `core::mem::size_of` but not `core::mem::foo::bar`, which `core::mem::**` does. A pattern with
    no wildcard matches the path exactly or any item under it, so `core::intrinsics` also selects
    `core::intrinsics::size_of`.
    """
    path = name if isinstance(name, str) else name_to_str(name, crate)
    if not any(char in pattern for char in "*?"):
        return path == pattern or path.startswith(pattern + "::")
    return _glob_to_regex(pattern).match(path) is not None


@functools.lru_cache(maxsize=None)
def _glob_to_regex(pattern: str) -> re.Pattern[str]:
    parts = []
    index = 0
    while index < len(pattern):
        char = pattern[index]
        if pattern.startswith("**", index):
            parts.append(".*")
            index += 2
            continue
        if char == "*":
            parts.append("[^:]*")
        elif char == "?":
            parts.append("[^:]")
        else:
            parts.append(re.escape(char))
        index += 1
    return re.compile("".join(parts) + r"\Z")
