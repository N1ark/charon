"""Inspect a charon-produced (u)llbc file from the command line.

    python3 -m charon summary crate.llbc
    python3 -m charon items crate.llbc --kind fun --name 'mycrate::**'
    python3 -m charon show crate.llbc 'mycrate::foo'

`items` and `show` exit with 1 when nothing matched, so they compose with `&&` the way `grep`
does. `--format jsonl` prints one json object per line, which is the easiest shape to feed to
`jq`, `awk` or another script.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from typing import Any, Optional, Sequence

from . import crate_of_file
from .crate import CrateIndex, ITEM_KINDS, Item, adt_kind, span_location
from .jsonish import to_jsonish

#: The columns `--format tsv` prints, in order.
TSV_COLUMNS = ("kind", "id", "path", "file", "line")


def item_record(index: CrateIndex, item: Item) -> dict[str, Any]:
    """The facts about an item that the listing formats show."""
    location = span_location(item.item_meta.span)
    record: dict[str, Any] = {
        "kind": item.kind,
        "id": item.id,
        "path": item.path,
        "short_name": item.short_name,
        "file": location[0] if location else None,
        "line": location[1] if location else None,
        "is_local": item.item_meta.is_local,
        "doc": item.doc,
    }
    if item.kind == "type":
        record["adt_kind"] = adt_kind(item.decl)
    if item.kind == "fun":
        record["arity"] = len(item.decl.signature.inputs)
    return record


def print_records(records: Sequence[dict[str, Any]], format: str) -> None:
    if format == "jsonl":
        for record in records:
            print(json.dumps(record))
    elif format == "json":
        print(json.dumps(records, indent=2))
    elif format == "tsv":
        for record in records:
            print("\t".join("" if record[c] is None else str(record[c]) for c in TSV_COLUMNS))
    else:
        width = max((len(r["kind"]) for r in records), default=0)
        for record in records:
            location = f"{record['file']}:{record['line']}" if record["file"] else "-"
            print(f"{record['kind']:<{width}}  {record['path']}  ({location})")


def select(index: CrateIndex, args: argparse.Namespace, pattern: Optional[str]) -> list[Item]:
    items = index.find(pattern, args.kind) if pattern else list(index.items(args.kind))
    if args.local:
        items = [item for item in items if item.item_meta.is_local]
    return sorted(items, key=lambda item: (item.path, item.kind, item.id))


def cmd_summary(args: argparse.Namespace) -> int:
    crate = crate_of_file(args.file)
    index = CrateIndex(crate)
    counts = Counter(item.kind for item in index.items())
    summary = {
        "crate_name": crate.crate_name,
        "file": str(args.file),
        "files": len(crate.files),
        "items": len(index),
        "items_by_kind": {kind: counts.get(kind, 0) for kind in ITEM_KINDS},
        "local_items": sum(1 for item in index.items() if item.item_meta.is_local),
    }
    if args.format in ("json", "jsonl"):
        print(json.dumps(summary, indent=2 if args.format == "json" else None))
    else:
        print(f"crate:  {summary['crate_name']}")
        print(f"files:  {summary['files']}")
        print(f"items:  {summary['items']} ({summary['local_items']} local)")
        for kind, count in summary["items_by_kind"].items():
            print(f"  {kind:<11} {count}")
    return 0


def cmd_items(args: argparse.Namespace) -> int:
    index = CrateIndex(crate_of_file(args.file))
    items = select(index, args, args.name)
    print_records([item_record(index, item) for item in items], args.format)
    return 0 if items else 1


def cmd_show(args: argparse.Namespace) -> int:
    index = CrateIndex(crate_of_file(args.file))
    items = select(index, args, args.pattern)
    for item in items:
        record = item_record(index, item)
        record["decl"] = to_jsonish(item.decl, max_depth=args.depth)
        print(json.dumps(record, indent=None if args.format == "jsonl" else 2))
    return 0 if items else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python3 -m charon",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    def add_common(subparser: argparse.ArgumentParser) -> None:
        subparser.add_argument("file", help="a .llbc/.ullbc file, in either format")

    summary = subparsers.add_parser("summary", help="what the file contains")
    add_common(summary)
    summary.add_argument("--format", choices=("text", "json", "jsonl"), default="text")
    summary.set_defaults(run=cmd_summary)

    items = subparsers.add_parser("items", help="list the items of the crate")
    add_common(items)
    items.add_argument("--kind", choices=ITEM_KINDS, help="only items of this kind")
    items.add_argument(
        "--name",
        metavar="PATTERN",
        help="only items whose path matches this glob; `*` stops at `::`, `**` crosses it",
    )
    items.add_argument(
        "--local", action="store_true", help="only items defined in the crate itself"
    )
    items.add_argument(
        "--format",
        choices=("text", "json", "jsonl", "tsv"),
        default="text",
        help=f"tsv columns are: {', '.join(TSV_COLUMNS)}",
    )
    items.set_defaults(run=cmd_items)

    show = subparsers.add_parser("show", help="dump the declaration of the matching items as json")
    add_common(show)
    show.add_argument("pattern", help="the path, or a glob matching it")
    show.add_argument("--kind", choices=ITEM_KINDS, help="only items of this kind")
    show.add_argument(
        "--local", action="store_true", help="only items defined in the crate itself"
    )
    show.add_argument(
        "--depth",
        type=int,
        default=None,
        metavar="N",
        help="replace anything nested deeper than N levels with `...`",
    )
    show.add_argument("--format", choices=("json", "jsonl"), default="json")
    show.set_defaults(run=cmd_show)
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    return args.run(args)


if __name__ == "__main__":
    sys.exit(main())
