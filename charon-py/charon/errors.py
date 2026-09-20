"""Errors raised while deserializing a (u)llbc file."""

from __future__ import annotations


class DeserializeError(Exception):
    """The input doesn't match what the deserializer expects.

    This normally means the file was produced by a different version of charon, or that the
    generated deserializers have drifted from the rust definitions.
    """


def unknown_variant(type_name: str, tag: object) -> DeserializeError:
    return DeserializeError(f"unknown variant {tag!r} of `{type_name}`")
