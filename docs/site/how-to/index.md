# How-to guides

## Check the formalization

```bash
cd lean
lake build          # type-checks every proof; a broken proof fails the build
```

The Lean CI workflow runs exactly this, so a green local build is the same
signal CI gives.

## Run the reference pipeline

```bash
cd python
pytest              # parser + synthesis tests
```

To try a spec by hand:

```python
from dts.precedence_parser import parse_spec
spec = parse_spec("handler Auth\nhandler Cache\nbefore Auth Cache")
print(spec.ordered)          # the linear extension
```

## Rebuild the paper

```bash
cd paper
make pdf            # PAPER.md -> paper.pdf via pandoc defaults
make tex            # ...and the LaTeX source
```

`paper.pdf` is committed, so a reader without a TeX/pandoc toolchain still gets
the artifact.

## Add a case study

1. Write the spec (handlers plus `before` relations, or numeric priorities).
2. `parse_spec` it and assert on `spec.ordered` — that assertion is the real
   test, because the order is the synthesis result.
3. Add a `synthesize(body, ordered)` fold and a test alongside it.

A cyclic spec is a case, not a crash: `cyclic_detection` shows the expected
diagnostic.
