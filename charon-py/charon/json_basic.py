"""Basic utilities for json deserialization.

The generated deserializers are built out of these. A deserializer takes the context and the json
value to read, and returns the value it read; generic types are curried over the deserializers of
their arguments, so that e.g. a list of spans is read by `list_of_json(span_of_json)`.
"""

from __future__ import annotations

from typing import Any, Callable, Optional, TypeVar

from .errors import DeserializeError

#: A decoded json value, as produced by the `json` module.
Json = Any

T = TypeVar("T")
U = TypeVar("U")
V = TypeVar("V")

#: A function that reads a value of type `T` out of a json value.
JsonDecoder = Callable[[Any, Json], T]


def _describe(js: Json) -> str:
    text = repr(js)
    return text if len(text) <= 200 else text[:200] + "..."


def expect_object(js: Json) -> dict[str, Json]:
    if not isinstance(js, dict):
        raise DeserializeError(f"expected an object, got: {_describe(js)}")
    return js


def expect_list(js: Json, length: Optional[int] = None) -> list[Json]:
    if not isinstance(js, list):
        raise DeserializeError(f"expected a list, got: {_describe(js)}")
    if length is not None and len(js) != length:
        raise DeserializeError(f"expected {length} elements, got: {_describe(js)}")
    return js


def expect_null(js: Json) -> None:
    if js is not None:
        raise DeserializeError(f"expected null, got: {_describe(js)}")


def split_variant(js: Json) -> tuple[str, Json]:
    """Split an externally tagged enum into its tag and its payload.

    Variants without fields are serialized as a bare string, the others as a one-field object.
    """
    if isinstance(js, str):
        return js, None
    if isinstance(js, dict) and len(js) == 1:
        return next(iter(js.items()))
    raise DeserializeError(f"expected an enum variant, got: {_describe(js)}")


def bool_of_json(ctx: Any, js: Json) -> bool:
    if not isinstance(js, bool):
        raise DeserializeError(f"expected a bool, got: {_describe(js)}")
    return js


def int_of_json(ctx: Any, js: Json) -> int:
    # `bool` is a subclass of `int`, hence the extra check.
    if not isinstance(js, int) or isinstance(js, bool):
        raise DeserializeError(f"expected an integer, got: {_describe(js)}")
    return js


def big_int_of_json(ctx: Any, js: Json) -> int:
    """Read an integer that may not fit in a json number, hence be serialized as a string."""
    if isinstance(js, str):
        try:
            return int(js)
        except ValueError:
            raise DeserializeError(f"expected an integer, got: {_describe(js)}") from None
    return int_of_json(ctx, js)


def float_of_json(ctx: Any, js: Json) -> float:
    if not isinstance(js, (int, float)) or isinstance(js, bool):
        raise DeserializeError(f"expected a float, got: {_describe(js)}")
    return float(js)


def string_of_json(ctx: Any, js: Json) -> str:
    if not isinstance(js, str):
        raise DeserializeError(f"expected a string, got: {_describe(js)}")
    return js


def char_of_json(ctx: Any, js: Json) -> str:
    text = string_of_json(ctx, js)
    if len(text) != 1:
        raise DeserializeError(f"expected a single character, got: {_describe(js)}")
    return text


path_buf_of_json = string_of_json


def list_of_json(elem: JsonDecoder[T]) -> JsonDecoder[list[T]]:
    def read(ctx: Any, js: Json) -> list[T]:
        return [elem(ctx, item) for item in expect_list(js)]

    return read


def option_of_json(elem: JsonDecoder[T]) -> JsonDecoder[Optional[T]]:
    def read(ctx: Any, js: Json) -> Optional[T]:
        return None if js is None else elem(ctx, js)

    return read


def box_of_json(elem: JsonDecoder[T]) -> JsonDecoder[T]:
    return elem


def pair_of_json(first: JsonDecoder[T], second: JsonDecoder[U]) -> JsonDecoder[tuple[T, U]]:
    def read(ctx: Any, js: Json) -> tuple[T, U]:
        items = expect_list(js, 2)
        return first(ctx, items[0]), second(ctx, items[1])

    return read


def triple_of_json(
    first: JsonDecoder[T], second: JsonDecoder[U], third: JsonDecoder[V]
) -> JsonDecoder[tuple[T, U, V]]:
    def read(ctx: Any, js: Json) -> tuple[T, U, V]:
        items = expect_list(js, 3)
        return first(ctx, items[0]), second(ctx, items[1]), third(ctx, items[2])

    return read


def range_inclusive_of_json(elem: JsonDecoder[T]) -> JsonDecoder[tuple[T, T]]:
    def read(ctx: Any, js: Json) -> tuple[T, T]:
        fields = expect_object(js)
        return elem(ctx, fields["start"]), elem(ctx, fields["end"])

    return read


def key_value_pair_of_json(
    key: JsonDecoder[T], value: JsonDecoder[U]
) -> JsonDecoder[tuple[T, U]]:
    def read(ctx: Any, js: Json) -> tuple[T, U]:
        fields = expect_object(js)
        return key(ctx, fields["key"]), value(ctx, fields["value"])

    return read


def indexed_map_of_json(key: JsonDecoder[Any], value: JsonDecoder[T]) -> JsonDecoder[dict[int, T]]:
    """Read an `IndexedMap`, serialized as the list of its values indexed by their key.

    The keys are the positions in that list, so `key` is unused; it is taken anyway to keep the
    generated calls uniform.
    """

    def read(ctx: Any, js: Json) -> dict[int, T]:
        entries = list_of_json(option_of_json(value))(ctx, js)
        return {index: entry for index, entry in enumerate(entries) if entry is not None}

    return read


def dedup_val_of_json(
    table: dict[int, T], decode: JsonDecoder[T], ctx: Any, js: Json
) -> T:
    """Read a value that may have been deduplicated in the serialized output.

    The first occurrence of such a value is serialized in full along with an id, and later
    occurrences only mention that id.
    """
    tag, payload = split_variant(js)
    if tag == "Untagged":
        return decode(ctx, payload)
    if tag == "Value":
        items = expect_list(payload, 2)
        value = decode(ctx, items[1])
        table[int_of_json(ctx, items[0])] = value
        return value
    if tag == "Deduplicated":
        try:
            return table[int_of_json(ctx, payload)]
        except KeyError:
            raise DeserializeError(
                "Deduplication key not found; there is a serialization mismatch "
                "between rust and python"
            ) from None
    raise DeserializeError(f"invalid deduplicated value representation: {tag!r}")
