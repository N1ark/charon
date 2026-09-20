"""Deserialize the (u)llbc files produced by charon's test suite.

This mirrors `charon-ml/tests/Test_Deserialize.ml`: every file the rust test suite emits is read
back, in both serialization formats. Reading the same crate from both formats must moreover give
the same value, which is a much stronger check than merely not raising: the two deserializers are
generated independently, so any disagreement about the shape of a type shows up here.

Run it with `make tests` in this directory, or directly with `python3 -m unittest discover tests`.
"""

from __future__ import annotations

import os
import sys
import threading
import unittest
from pathlib import Path
from typing import Callable, TypeVar

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from charon import DeserializeError, crate_of_json_file, crate_of_postcard_file

TESTS_DIR = Path(
    os.environ.get(
        "CHARON_TESTS_DIR", Path(__file__).resolve().parents[2] / "charon" / "tests" / "ui"
    )
)

JSON_SUFFIXES = (".llbc", ".ullbc")
POSTCARD_SUFFIXES = (".llbc.postcard", ".ullbc.postcard")

T = TypeVar("T")


def find_files(suffixes: tuple[str, ...]) -> list[Path]:
    files = [
        path
        for path in TESTS_DIR.rglob("*")
        if path.is_file() and path.name.endswith(suffixes)
    ]
    return sorted(files)


def with_big_stack(action: Callable[[], T]) -> T:
    """Run `action` with enough stack for the AST, which is deeply recursive.

    Python's own recursion limit is easy to raise, but the C stack of the main thread isn't, so we
    run in a thread whose stack we sized ourselves.
    """
    result: list[T] = []
    error: list[BaseException] = []

    def run() -> None:
        old_limit = sys.getrecursionlimit()
        sys.setrecursionlimit(100_000)
        try:
            result.append(action())
        except BaseException as exn:  # re-raised in the calling thread
            error.append(exn)
        finally:
            sys.setrecursionlimit(old_limit)

    old_size = threading.stack_size(256 * 1024 * 1024)
    try:
        thread = threading.Thread(target=run)
        thread.start()
        thread.join()
    finally:
        threading.stack_size(old_size)
    if error:
        raise error[0]
    return result[0]


class TestDeserialize(unittest.TestCase):
    def test_files_were_generated(self) -> None:
        """Guard against silently testing nothing, e.g. when the rust tests haven't been run."""
        self.assertTrue(
            find_files(JSON_SUFFIXES),
            f"no (u)llbc file in {TESTS_DIR}; run the rust test suite first",
        )
        self.assertTrue(find_files(POSTCARD_SUFFIXES), f"no postcard file in {TESTS_DIR}")

    def test_json(self) -> None:
        for path in find_files(JSON_SUFFIXES):
            with self.subTest(file=str(path)):
                with_big_stack(lambda: crate_of_json_file(path))

    def test_postcard(self) -> None:
        for path in find_files(POSTCARD_SUFFIXES):
            with self.subTest(file=str(path)):
                with_big_stack(lambda: crate_of_postcard_file(path))

    def test_both_formats_agree(self) -> None:
        for json_path in find_files(JSON_SUFFIXES):
            postcard_path = Path(str(json_path) + ".postcard")
            if not postcard_path.exists():
                continue
            with self.subTest(file=str(json_path)):
                from_json = with_big_stack(lambda: crate_of_json_file(json_path))
                from_postcard = with_big_stack(lambda: crate_of_postcard_file(postcard_path))
                self.assertEqual(
                    from_json,
                    from_postcard,
                    f"json and postcard disagree on {json_path}",
                )

    def test_cross_format_errors(self) -> None:
        """Feeding a file to the wrong deserializer must say so, rather than fail obscurely."""
        json_path = find_files(JSON_SUFFIXES)[0]
        postcard_path = find_files(POSTCARD_SUFFIXES)[0]
        with self.assertRaises(DeserializeError) as caught:
            crate_of_postcard_file(json_path)
        self.assertIn("looks like JSON", str(caught.exception))
        with self.assertRaises(DeserializeError) as caught:
            crate_of_json_file(postcard_path)
        self.assertIn("looks like Postcard", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
