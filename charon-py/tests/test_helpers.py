"""Tests for the scripting helpers.

The assertions are about invariants that hold of any crate, so that they keep working as charon's
test suite changes; the file they run on is whichever one the rust tests emitted first.
"""

from __future__ import annotations

import io
import json
import sys
import unittest
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import charon
from charon.__main__ import main
from charon.crate import CrateIndex, ITEM_KINDS, adt_kind, doc_comment, fun_params, span_location
from charon.jsonish import TYPE_KEY, to_jsonish
from charon.names import name_matches
from charon.run import charon_args
from test_deserialize import JSON_SUFFIXES, find_files, with_big_stack


def some_crate_file() -> Path:
    files = find_files(JSON_SUFFIXES)
    if not files:
        raise unittest.SkipTest("no (u)llbc file to test on; run the rust test suite first")
    return files[0]


class TestNames(unittest.TestCase):
    def test_exact_pattern_selects_the_item_and_its_children(self) -> None:
        self.assertTrue(name_matches("core::intrinsics", "core::intrinsics"))
        self.assertTrue(name_matches("core::intrinsics::size_of", "core::intrinsics"))
        self.assertFalse(name_matches("core::intrinsics_other", "core::intrinsics"))

    def test_single_star_stops_at_the_separator(self) -> None:
        self.assertTrue(name_matches("core::mem::size_of", "core::mem::*"))
        self.assertFalse(name_matches("core::mem::sub::thing", "core::mem::*"))
        self.assertTrue(name_matches("core::mem::sub::thing", "core::mem::**"))

    def test_patterns_are_anchored(self) -> None:
        self.assertFalse(name_matches("other::core::mem", "core::*"))
        self.assertTrue(name_matches("core::mem", "core::??m"))


class TestCharonArgs(unittest.TestCase):
    def test_output_arguments_go_before_the_separator(self) -> None:
        args = charon_args(["rustc", "--", "foo.rs"], Path("/tmp/out"), "json")
        self.assertEqual(
            args, ["rustc", "--dest-file", "/tmp/out", "--format=json", "--", "foo.rs"]
        )

    def test_output_arguments_are_appended_when_there_is_no_separator(self) -> None:
        args = charon_args(["cargo", "--ullbc"], Path("/tmp/out"), "postcard")
        self.assertEqual(
            args, ["cargo", "--ullbc", "--dest-file", "/tmp/out", "--format=postcard"]
        )


class TestCrateIndex(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.path = some_crate_file()
        cls.crate = with_big_stack(lambda: charon.crate_of_file(cls.path))
        cls.index = CrateIndex(cls.crate)

    def test_every_item_has_a_path_and_a_known_kind(self) -> None:
        self.assertGreater(len(self.index), 0)
        for item in self.index.items():
            self.assertIn(item.kind, ITEM_KINDS)
            self.assertNotEqual(item.path, "")
            self.assertIs(self.index.by_id(item.kind, item.id), item)

    def test_kinds_partition_the_items(self) -> None:
        by_kind = sum(len(list(self.index.items(kind))) for kind in ITEM_KINDS)
        self.assertEqual(by_kind, len(self.index))

    def test_find_matches_paths(self) -> None:
        self.assertEqual(len(self.index.find("**")), len(self.index))
        self.assertEqual(self.index.find("definitely::not::an::item"), [])
        for item in self.index.items():
            self.assertIn(item, self.index.find(item.path))

    def test_get_returns_the_item_at_an_unambiguous_path(self) -> None:
        item = next(iter(self.index.items()))
        found = self.index.get(item.path, item.kind)
        # A path can be shared by several items, in which case `get` declines to pick one.
        self.assertIn(found, (item, None))

    def test_items_can_be_described(self) -> None:
        for item in self.index.items():
            self.assertIsInstance(self.index.path_of(item.name), str)
            self.assertTrue(item.short_name is None or item.short_name != "")
            doc = doc_comment(item.item_meta)
            self.assertTrue(doc is None or isinstance(doc, str))
            location = span_location(item.item_meta.span)
            self.assertTrue(location is None or location[1] >= 0)

    def test_type_declarations_have_a_kind(self) -> None:
        kinds = {"struct", "enum", "union", "alias", "opaque", "error"}
        for item in self.index.items("type"):
            self.assertIn(adt_kind(item.decl), kinds)

    def test_function_parameters_line_up_with_the_signature(self) -> None:
        for item in self.index.items("fun"):
            params = fun_params(item.decl)
            self.assertEqual(len(params), len(item.decl.signature.inputs))
            for index, param in enumerate(params):
                self.assertEqual(param.index, index)
                self.assertIs(param.ty, item.decl.signature.inputs[index])
                self.assertIsInstance(self.index.ty_str(param.ty), str)


class TestJsonish(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.crate = with_big_stack(lambda: charon.crate_of_file(some_crate_file()))

    def test_declarations_dump_to_json(self) -> None:
        index = CrateIndex(self.crate)
        for item in list(index.items())[:20]:
            dumped = json.loads(json.dumps(to_jsonish(item.decl, max_depth=6)))
            self.assertEqual(dumped[TYPE_KEY], type(item.decl).__name__)

    def test_depth_limit_cuts_the_value_off(self) -> None:
        self.assertEqual(to_jsonish(self.crate, max_depth=0), "...")
        shallow = to_jsonish(self.crate, max_depth=1)
        self.assertEqual(shallow[TYPE_KEY], "TranslatedCrate")
        self.assertEqual(shallow["files"], "...")


class TestCli(unittest.TestCase):
    def run_cli(self, *args: str) -> tuple[int, str]:
        output = io.StringIO()
        with redirect_stdout(output):
            code = with_big_stack(lambda: main(list(args)))
        return code, output.getvalue()

    def test_summary_reports_the_item_counts(self) -> None:
        path = str(some_crate_file())
        code, output = self.run_cli("summary", path, "--format", "json")
        self.assertEqual(code, 0)
        summary = json.loads(output)
        self.assertEqual(sum(summary["items_by_kind"].values()), summary["items"])

    def test_items_prints_one_json_object_per_line(self) -> None:
        path = str(some_crate_file())
        code, output = self.run_cli("items", path, "--format", "jsonl")
        self.assertEqual(code, 0)
        records = [json.loads(line) for line in output.splitlines()]
        self.assertTrue(all(record["path"] for record in records))

    def test_no_match_exits_with_one(self) -> None:
        path = str(some_crate_file())
        code, output = self.run_cli("items", path, "--name", "definitely::not::here")
        self.assertEqual(code, 1)
        self.assertEqual(output, "")


if __name__ == "__main__":
    unittest.main()
