"""Basic utilities for postcard deserialization.

Postcard is a sequential format: there is nothing to match on, values are simply read one after
the other out of a [`PostcardReader`].
"""

from __future__ import annotations

import enum
import struct
from typing import Any, Callable, Optional, TypeVar

from .errors import DeserializeError

T = TypeVar("T")
U = TypeVar("U")
V = TypeVar("V")


class PostcardReader:
    """A cursor over the bytes of a postcard file."""

    __slots__ = ("data", "pos")

    def __init__(self, data: bytes) -> None:
        self.data = data
        self.pos = 0

    def take(self, length: int) -> bytes:
        end = self.pos + length
        if end > len(self.data):
            raise DeserializeError(
                f"unexpected end of postcard input at byte {self.pos}, "
                f"expected {length} more bytes"
            )
        chunk = self.data[self.pos : end]
        self.pos = end
        return chunk

    def take_u8(self) -> int:
        if self.pos >= len(self.data):
            raise DeserializeError(
                f"unexpected end of postcard input at byte {self.pos}, expected 1 more byte"
            )
        byte = self.data[self.pos]
        self.pos += 1
        return byte


#: A function that reads a value of type `T` out of a postcard reader.
PostcardDecoder = Callable[[Any, PostcardReader], T]


class InputFormat(enum.Enum):
    JSON = "json"
    POSTCARD = "postcard"
    EMPTY = "empty"


def format_hint(data: bytes) -> InputFormat:
    """Guess the format of a file from its first bytes."""
    for byte in data[:64]:
        if byte in b" \t\n\r":
            continue
        return InputFormat.JSON if byte == ord("{") else InputFormat.POSTCARD
    return InputFormat.EMPTY


def _read_varint(st: PostcardReader, max_bytes: int, max_last: int) -> int:
    acc = 0
    shift = 0
    for i in range(max_bytes):
        raw = st.take_u8()
        acc |= (raw & 0x7F) << shift
        if not raw & 0x80:
            if i == max_bytes - 1 and raw > max_last:
                raise DeserializeError("invalid postcard varint terminal byte")
            return acc
        shift += 7
    raise DeserializeError("invalid postcard varint")


def _zigzag(value: int) -> int:
    return value >> 1 if value % 2 == 0 else -((value >> 1) + 1)


def bool_of_postcard(ctx: Any, st: PostcardReader) -> bool:
    byte = st.take_u8()
    if byte > 1:
        raise DeserializeError("invalid postcard bool")
    return byte == 1


def u8_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return st.take_u8()


def u16_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return _read_varint(st, 3, 3)


def u32_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return _read_varint(st, 5, 15)


def u64_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return _read_varint(st, 10, 1)


def usize_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return _read_varint(st, 10, 1)


def int_of_postcard(ctx: Any, st: PostcardReader) -> int:
    """The encoding of enum tags and of our strongly-typed ids."""
    return _read_varint(st, 5, 15)


def i8_of_postcard(ctx: Any, st: PostcardReader) -> int:
    byte = st.take_u8()
    return byte if byte < 128 else byte - 256


def i16_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return _zigzag(_read_varint(st, 3, 3))


def i32_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return _zigzag(_read_varint(st, 5, 15))


def i64_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return _zigzag(_read_varint(st, 10, 1))


def isize_of_postcard(ctx: Any, st: PostcardReader) -> int:
    return _zigzag(_read_varint(st, 10, 1))


def string_of_postcard(ctx: Any, st: PostcardReader) -> str:
    length = usize_of_postcard(ctx, st)
    try:
        return st.take(length).decode("utf-8")
    except UnicodeDecodeError:
        raise DeserializeError("invalid postcard utf-8 string") from None


def big_int_of_postcard(ctx: Any, st: PostcardReader) -> int:
    """128-bit integers don't fit in a postcard varint, so they are serialized as strings."""
    raw = string_of_postcard(ctx, st)
    try:
        return int(raw)
    except ValueError:
        raise DeserializeError(f"invalid integer string: {raw!r}") from None


def big_uint_of_postcard(ctx: Any, st: PostcardReader) -> int:
    value = big_int_of_postcard(ctx, st)
    if value < 0:
        raise DeserializeError("expected a non-negative integer string")
    return value


def char_of_postcard(ctx: Any, st: PostcardReader) -> str:
    length = usize_of_postcard(ctx, st)
    if not 1 <= length <= 4:
        raise DeserializeError("invalid postcard char length")
    try:
        return st.take(length).decode("utf-8")
    except UnicodeDecodeError:
        raise DeserializeError("invalid postcard utf-8 char") from None


def f32_of_postcard(ctx: Any, st: PostcardReader) -> float:
    return struct.unpack("<f", st.take(4))[0]


def float_of_postcard(ctx: Any, st: PostcardReader) -> float:
    return struct.unpack("<d", st.take(8))[0]


def list_of_postcard(elem: PostcardDecoder[T]) -> PostcardDecoder[list[T]]:
    def read(ctx: Any, st: PostcardReader) -> list[T]:
        length = usize_of_postcard(ctx, st)
        if length > 1_000_000:
            raise DeserializeError(
                f"suspicious postcard sequence length {length} (read at byte {st.pos})"
            )
        return [elem(ctx, st) for _ in range(length)]

    return read


def option_of_postcard(elem: PostcardDecoder[T]) -> PostcardDecoder[Optional[T]]:
    def read(ctx: Any, st: PostcardReader) -> Optional[T]:
        tag = st.take_u8()
        if tag == 0:
            return None
        if tag == 1:
            return elem(ctx, st)
        raise DeserializeError("invalid postcard option tag")

    return read


def box_of_postcard(elem: PostcardDecoder[T]) -> PostcardDecoder[T]:
    return elem


def pair_of_postcard(
    first: PostcardDecoder[T], second: PostcardDecoder[U]
) -> PostcardDecoder[tuple[T, U]]:
    def read(ctx: Any, st: PostcardReader) -> tuple[T, U]:
        return first(ctx, st), second(ctx, st)

    return read


def triple_of_postcard(
    first: PostcardDecoder[T], second: PostcardDecoder[U], third: PostcardDecoder[V]
) -> PostcardDecoder[tuple[T, U, V]]:
    def read(ctx: Any, st: PostcardReader) -> tuple[T, U, V]:
        return first(ctx, st), second(ctx, st), third(ctx, st)

    return read


def range_inclusive_of_postcard(elem: PostcardDecoder[T]) -> PostcardDecoder[tuple[T, T]]:
    def read(ctx: Any, st: PostcardReader) -> tuple[T, T]:
        return elem(ctx, st), elem(ctx, st)

    return read


def key_value_pair_of_postcard(
    key: PostcardDecoder[T], value: PostcardDecoder[U]
) -> PostcardDecoder[tuple[T, U]]:
    return pair_of_postcard(key, value)


def indexed_map_of_postcard(
    key: PostcardDecoder[Any], value: PostcardDecoder[T]
) -> PostcardDecoder[dict[int, T]]:
    """See `charon.json_basic.indexed_map_of_json`."""

    def read(ctx: Any, st: PostcardReader) -> dict[int, T]:
        entries = list_of_postcard(option_of_postcard(value))(ctx, st)
        return {index: entry for index, entry in enumerate(entries) if entry is not None}

    return read


def dedup_val_of_postcard(
    table: dict[int, T], decode: PostcardDecoder[T]
) -> PostcardDecoder[T]:
    """See `charon.json_basic.dedup_val_of_json`."""

    def read(ctx: Any, st: PostcardReader) -> T:
        tag = int_of_postcard(ctx, st)
        if tag == 0:
            key = int_of_postcard(ctx, st)
            value = decode(ctx, st)
            table[key] = value
            return value
        if tag == 1:
            key = int_of_postcard(ctx, st)
            try:
                return table[key]
            except KeyError:
                raise DeserializeError(
                    "Deduplication key not found; there is a serialization mismatch "
                    "between rust and python"
                ) from None
        if tag == 2:
            return decode(ctx, st)
        raise DeserializeError(f"invalid deduplicated value representation: {tag}")

    return read


def ensure_eof(st: PostcardReader) -> None:
    if st.pos < len(st.data):
        raise DeserializeError(
            f"postcard input has trailing bytes (pos={st.pos}, len={len(st.data)})"
        )
