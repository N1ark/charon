# charon-py

Python bindings for the (U)LLBC ASTs produced by [Charon](https://github.com/AeneasVerif/charon),
the python counterpart of `charon-ml`.

```python
from charon import crate_of_json_file, crate_of_postcard_file

crate = crate_of_json_file("mycrate.llbc")
for fun in crate.fun_decls.values():
    print(fun.item_meta.name)
```

Charon serializes its AST either as json (`.llbc`, `.ullbc`) or as
[postcard](https://postcard.jamesmunns.com) (`.llbc.postcard`, `.ullbc.postcard`); there is one
entry point per format. Both raise `charon.DeserializeError` if the file doesn't match the version
of the AST this package was generated from.

## Layout

- `charon/generated/types.py`: the AST types, as dataclasses. An enum is a union of one dataclass
  per variant, so `match`/`isinstance` narrow the type as expected.
- `charon/generated/of_json.py`, `charon/generated/of_postcard.py`: the deserializers.
- `charon/json_basic.py`, `charon/postcard_basic.py`: the hand-written primitives they are built
  out of.

The files under `charon/generated/` are produced by `make generate-asts` in the repository root,
from the rust definitions themselves; edit `charon/src/bin/generate-asts/generate_py/templates/`
rather than the generated files. The version this package supports is in `charon/version.py`, which
`make` keeps in sync with `charon/Cargo.toml`.

## Tests

`make tests` deserializes every file emitted by charon's rust test suite, in both formats, and
checks that the two agree. It needs those files to exist, so run the rust tests first (`make test`
in the repository root does both).
