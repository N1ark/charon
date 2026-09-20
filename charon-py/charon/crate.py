"""Lookups and small analyses over a translated crate.

A crate stores its declarations in one map per kind, and items refer to each other by id.
[`CrateIndex`] indexes them by path so a script can go from a rust path to a declaration and back,
and the functions around it answer the questions that come up when walking the AST: what kind of
ADT is this, where does this item come from, what are this function's parameters called.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator, Optional, Union

from .generated.types import *
from .names import name_short, name_to_str, ty_to_str

__all__ = [
    "AnyDecl",
    "CrateIndex",
    "ITEM_KINDS",
    "Item",
    "Param",
    "adt_kind",
    "body_locals",
    "doc_comment",
    "fun_params",
    "span_location",
]

#: The kinds of item a crate declares, in the order `CrateIndex` iterates them.
ITEM_KINDS = ("type", "fun", "global", "trait_decl", "trait_impl")

AnyDecl = Union[TypeDecl, FunDecl, GlobalDecl, TraitDecl, TraitImpl]


@dataclass(frozen=True)
class Item:
    """One declaration of a crate, whatever its kind."""

    kind: str
    """One of [`ITEM_KINDS`]."""
    id: int
    """The declaration's id, unique among the items of the same kind."""
    path: str
    """The rendered name, e.g. `core::mem::size_of`."""
    decl: AnyDecl

    @property
    def item_meta(self) -> ItemMeta:
        return self.decl.item_meta

    @property
    def name(self) -> Name:
        return self.decl.item_meta.name

    @property
    def short_name(self) -> Optional[str]:
        """The last identifier of the item's name, e.g. `size_of`."""
        return name_short(self.name)

    @property
    def doc(self) -> Optional[str]:
        """The item's doc comment, if it has one."""
        return doc_comment(self.decl.item_meta)


def doc_comment(meta: Union[ItemMeta, AttrInfo]) -> Optional[str]:
    """The doc comment of an item, field or variant, with its lines joined."""
    attr_info = meta.attr_info if isinstance(meta, ItemMeta) else meta
    lines = [
        attr._0 for attr in attr_info.attributes if isinstance(attr, AttributeAttrDocComment)
    ]
    return "\n".join(lines) if lines else None


def span_location(span: Span) -> Optional[tuple[str, int, int]]:
    """Where a span starts, as `(file, line, column)`.

    `None` when the span points into a file charon didn't record a name for.
    """
    file_name = span.data.file.name
    if not isinstance(file_name, (FileNameVirtual, FileNameLocal, FileNameNotReal)):
        return None
    return file_name._0, span.data.beg_loc.line, span.data.beg_loc.col


def adt_kind(decl: TypeDecl) -> str:
    """How a type is defined: `struct`, `enum`, `union`, `alias`, `opaque` or `error`."""
    if isinstance(decl.kind, TypeDeclKindStruct):
        return "struct"
    if isinstance(decl.kind, TypeDeclKindEnum):
        return "enum"
    if isinstance(decl.kind, TypeDeclKindUnion):
        return "union"
    if isinstance(decl.kind, TypeDeclKindAlias):
        return "alias"
    return "opaque" if isinstance(decl.kind, TypeDeclKindOpaque) else "error"


def body_locals(body: Body) -> Optional[Locals]:
    """The local variables of a function body, for the bodies that have some."""
    if isinstance(body, (BodyUnstructuredBody, BodyStructuredBody)):
        return body._0.locals
    return None


@dataclass(frozen=True)
class Param:
    """One input of a function."""

    index: int
    name: Optional[str]
    """The name the source gives it, when the body records one."""
    ty: Ty


def fun_params(fun: FunDecl) -> list[Param]:
    """The inputs of a function, with their names when the body provides them.

    The types always come from the signature; the names come from the body's locals, or from the
    intrinsic's declaration for an intrinsic, and are `None` for a function whose body we don't
    have.
    """
    inputs = fun.signature.inputs
    names: list[Optional[str]] = [None] * len(inputs)
    if isinstance(fun.body, BodyIntrinsicBody):
        names[: len(fun.body.arg_names)] = fun.body.arg_names[: len(inputs)]
    elif (locals_ := body_locals(fun.body)) is not None:
        # Local 0 holds the return value, then come the `arg_count` inputs.
        args = locals_.locals[1 : locals_.arg_count + 1]
        names[: len(args)] = [local.name for local in args[: len(inputs)]]
    return [Param(index, name, ty) for index, (name, ty) in enumerate(zip(names, inputs))]


class CrateIndex:
    """Indexes the items of a crate by path, and resolves the ids they refer to."""

    def __init__(self, crate: TranslatedCrate) -> None:
        self.crate = crate
        self._items: list[Item] = []
        self._by_kind: dict[str, dict[int, Item]] = {kind: {} for kind in ITEM_KINDS}
        decls_by_kind: list[tuple[str, dict[int, AnyDecl]]] = [
            ("type", crate.type_decls),
            ("fun", crate.fun_decls),
            ("global", crate.global_decls),
            ("trait_decl", crate.trait_decls),
            ("trait_impl", crate.trait_impls),
        ]
        for kind, decls in decls_by_kind:
            for id, decl in decls.items():
                item = Item(kind, id, name_to_str(decl.item_meta.name, crate), decl)
                self._items.append(item)
                self._by_kind[kind][id] = item
        # Several items can share a path, e.g. two methods of different impls of the same trait,
        # since our rendering of an impl block is not unique.
        self._by_path: dict[str, list[Item]] = {}
        for item in self._items:
            self._by_path.setdefault(item.path, []).append(item)

    def items(self, kind: Optional[str] = None) -> Iterator[Item]:
        """Every item of the crate, or every item of one kind."""
        if kind is None:
            yield from self._items
        else:
            yield from self._by_kind[kind].values()

    def find(self, pattern: str, kind: Optional[str] = None) -> list[Item]:
        """The items whose path matches a glob pattern. See `charon.names.name_matches`."""
        from .names import name_matches

        return [item for item in self.items(kind) if name_matches(item.path, pattern)]

    def get(self, path: str, kind: Optional[str] = None) -> Optional[Item]:
        """The item declared at an exact path, if there is exactly one."""
        matches = [
            item for item in self._by_path.get(path, ()) if kind is None or item.kind == kind
        ]
        return matches[0] if len(matches) == 1 else None

    def by_id(self, kind: str, id: int) -> Optional[Item]:
        """The item of the given kind and id."""
        return self._by_kind[kind].get(id)

    def resolve(self, item_id: ItemId) -> Optional[Item]:
        """The item an `ItemId` refers to."""
        kinds: list[tuple[type, str]] = [
            (ItemIdIdType, "type"),
            (ItemIdIdFun, "fun"),
            (ItemIdIdGlobal, "global"),
            (ItemIdIdTraitDecl, "trait_decl"),
            (ItemIdIdTraitImpl, "trait_impl"),
        ]
        for variant, kind in kinds:
            if isinstance(item_id, variant):
                return self.by_id(kind, item_id._0)
        return None

    def type_decl_of(self, ty: Ty) -> Optional[TypeDecl]:
        """The declaration of the ADT a type refers to, if it is one we have."""
        return self.crate.type_decls.get(ty._0.id) if isinstance(ty, TyKindTAdt) else None

    def ty_str(self, ty: Ty) -> str:
        """Render a type, naming the ADTs this crate declares. See `charon.names.ty_to_str`."""
        return ty_to_str(ty, self.crate)

    def path_of(self, name: Name) -> str:
        """Render a name, naming the types and traits this crate declares."""
        return name_to_str(name, self.crate)

    def __len__(self) -> int:
        return len(self._items)
