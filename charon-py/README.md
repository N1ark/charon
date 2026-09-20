# charon-py

Python bindings for the (U)LLBC ASTs produced by [Charon](https://github.com/AeneasVerif/charon),
the python counterpart of `charon-ml`.

```python
from charon import crate_of_file
from charon.crate import CrateIndex, fun_params

index = CrateIndex(crate_of_file("mycrate.llbc"))
for item in index.find("mycrate::**", kind="fun"):
    args = ", ".join(f"{p.name}: {index.ty_str(p.ty)}" for p in fun_params(item.decl))
    print(f"{item.path}({args})")
```

Charon serializes its AST either as json (`.llbc`, `.ullbc`) or as
[postcard](https://postcard.jamesmunns.com) (`.llbc.postcard`, `.ullbc.postcard`).
`crate_of_file` reads either; `crate_of_json_file` and `crate_of_postcard_file` insist on one.
All of them raise `charon.DeserializeError` if the file doesn't match the version of the AST this
package was generated from.

## Scripting

Deserializing gives you the AST exactly as charon defines it, which is not always the shape a
script wants. These modules cover what a consumer otherwise ends up writing itself:

- `charon.names` renders and matches item names. A name is a list of path elements, not a string,
  so `name_to_str` is how you get `core::mem::size_of`, and `name_matches` compares one against a
  glob where `*` stops at `::` and `**` crosses it. `ty_to_str` renders a type compactly — enough
  to tell items apart in a listing, not a faithful pretty-printer.
- `charon.crate` indexes a crate. `CrateIndex` walks all five kinds of item uniformly, looks them
  up by path, and resolves the ids items refer to each other by. Around it, `fun_params` pairs a
  function's input types with the names its body gives them, `adt_kind` says whether a type is a
  struct, an enum or a union, `doc_comment` collects an item's `///` lines, and `span_location`
  turns a span into a `file, line, column`.
- `charon.run` builds a charon command line, runs it and deserializes the result in one call, with
  a `reuse` flag for scripts that rerun often.
- `charon.jsonish` turns any AST value back into plain json, tagging each dataclass with its class
  name so an enum's variants stay distinguishable.

Types, spans and a few other values are deduplicated in the serialized file; the deserializers
resolve all of that, so a script never sees an id it has to look up in a side table.

## Command line

`python3 -m charon` inspects a file without writing a script:

```console
$ python3 -m charon summary mycrate.llbc
$ python3 -m charon items mycrate.llbc --kind fun --local --format tsv
$ python3 -m charon show mycrate.llbc 'mycrate::foo' --depth 5
```

`--format jsonl` prints one json object per item per line, for piping into `jq` or `awk`; `items`
and `show` exit with 1 when nothing matched, so they chain with `&&` the way `grep` does.

## Layout

- `charon/generated/types.py`: the AST types, as dataclasses. An enum is a union of one dataclass
  per variant, so `match`/`isinstance` narrow the type as expected.
- `charon/generated/of_json.py`, `charon/generated/of_postcard.py`: the deserializers.
- `charon/json_basic.py`, `charon/postcard_basic.py`: the hand-written primitives they are built
  out of.
- `charon/names.py`, `charon/crate.py`, `charon/run.py`, `charon/jsonish.py`,
  `charon/__main__.py`: the scripting helpers and the command line, none of them generated.

The files under `charon/generated/` are produced by `make generate-asts` in the repository root,
from the rust definitions themselves; edit `charon/src/bin/generate-asts/generate_py/templates/`
rather than the generated files. The version this package supports is in `charon/version.py`, which
`make` keeps in sync with `charon/Cargo.toml`.

## Tests

`make tests` deserializes every file emitted by charon's rust test suite, in both formats, and
checks that the two agree. It needs those files to exist, so run the rust tests first (`make test`
in the repository root does both).
