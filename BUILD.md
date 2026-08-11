# Build environment

## Pins

| Component  | Pin |
|---|---|
| Lean       | `leanprover/lean4:v4.28.0-rc1` |
| Mathlib    | `58d8468384df017604272605bb0ec709826199e7` |
| Foundation | `55eb586aed3f8791b422f2b78a94028c27fcad3a` |

`lean-toolchain` pins the compiler. `lake-manifest.json` pins Foundation (the
only direct dependency) together with every transitive dependency, at exactly
the revisions Foundation itself pins. Dependency sources are fetched into
`.lake/packages/`, which is git-ignored.

## Building from a clean clone

```sh
lake exe cache get   # Mathlib's precompiled .olean cache
lake build
```

Only Foundation and this development compile from source; Mathlib is reused
from cache.

## Do not run `lake update`

`lake update` re-resolves dependencies against their current branch heads. The
three pins above are mutually compatible; a newer Mathlib is **not** compatible
with Foundation at this revision (renamed APIs cause compile errors). Treat
`lake-manifest.json` as canonical: if it is disturbed, restore it with

```sh
git checkout -- lake-manifest.json lean-toolchain
```

and never regenerate it.
