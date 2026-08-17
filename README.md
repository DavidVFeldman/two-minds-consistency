# Models of arithmetic of two minds about consistency

[![DOI](https://zenodo.org/badge/1330420705.svg)](https://doi.org/10.5281/zenodo.21881585)

Paper and complete Lean 4 formalization.

Whether a model of arithmetic "thinks PA is consistent" is not a property of
the model. It depends on which arithmetization of provability is used, and a
single model can satisfy one entirely natural formalization of "PA is
consistent" while refuting another — where both formalizations define exactly
the true provability relation in the standard model, and each is provably a
sound subpredicate of the standard one.

For machines `T` that never halt, put

```
Pr_T(x) := ∃ y (Proof(y, x) ∧ T has not halted within y steps)
Con_T   := ¬ Pr_T(⌜0 = 1⌝)
```

The main theorem says that the resulting consistency verdicts can be rigged in
every combination not outright ruled out.

**Main Theorem.** Assume PA is consistent, and let `n ≥ 1`. There are Turing
machines `T₁, …, Tₙ`, none of which halts, such that each `Pr_{Tᵢ}` defines
standard provability in ℕ and satisfies necessitation, PA proves
`Con → Con_{Tᵢ}` for each `i`, and for **every** `S ⊆ {1, …, n}` the theory

```
PA + ¬Con + { Con_{Tᵢ} : i ∈ S } + { ¬Con_{Tᵢ} : i ∉ S }
```

is consistent.

Taking `n = 2` and `S = {1}` gives a single model of PA of two minds about the
consistency of PA.

## What is formalized

Everything in the table below is machine-checked with no `sorry` and the
standard axiom footprint `[propext, Classical.choice, Quot.sound]`. See
[`VERIFICATION.md`](VERIFICATION.md) for the full paper-to-Lean crosswalk, the
translations used, and one honest caveat about the `PA` instantiation.

| Paper | Lean |
|---|---|
| Theorem 4.1 (Main Theorem) | `TwoMinds.main` |
| Corollary 4.2 (two minds) | `TwoMinds.two_minds` |
| Lemma 3.1 (Reformulation) | `TwoMinds.reformulation` |
| Proposition 6.2 (Normal form) | `TwoMinds.conBefore_iff_consistent_or_haltR` |
| Proposition 6.4 (Realization, stage-formula form) | `TwoMinds.haltR_rhoStage_iff` |
| Theorem 4.1(1), necessitation | `TwoMinds.necessitation` (also clause 4 of `main`) |
| Theorem 4.1(1), extensional correctness over ℕ | `TwoMinds.provBefore_nat_iff` (also clause 5 of `main`) |

The development is carried out over an **arbitrary** `Δ₁`-axiomatized
recursively enumerable theory `T` extending `IΣ₁`; the statements for `PA` in
the paper are instances.

## Building

Requires [`elan`](https://github.com/leanprover/elan). From a clean clone:

```sh
lake exe cache get
lake build
```

`lean-toolchain` pins the compiler; `lake-manifest.json` pins every
dependency. Do **not** run `lake update` — see [`BUILD.md`](BUILD.md).

## Layout

```
RequestProject/TwoMinds/
  Basic.lean              base setup; Gödel II wrapper
  StageFormula.lean       stage formulas, Pr_T / Con_T, Halt^R, normal form
  Construction.lean       the simultaneous fixed point; reformulation; self-defeat
  Main.lean               Main Theorem and the two-minds corollary
  Necessitation.lean      necessitation (D1) and extensional correctness over ℕ
  StageFormulaProp64.lean realization theorem in stage-formula form
  AXIOMS.txt              raw `#print axioms` output
paper/                    the accompanying paper (source and PDF)
```

The library name `RequestProject` is an artifact of the prover harness the
development was produced with; it has been left untouched so that the
published sources are byte-identical to the verified ones.

## Citing

See [`CITATION.cff`](CITATION.cff). Please cite the paper for the mathematics,
and this repository for the formalization:

> Feldman, D. V. (2026). *Models of arithmetic of two minds about consistency:
> Lean 4 formalization.* Zenodo. https://doi.org/10.5281/zenodo.21881585

That DOI covers all versions and always resolves to the latest; the release
archived here as v1.0.0 is `10.5281/zenodo.21881586`.

## License

MIT for the Lean sources (see [`LICENSE`](LICENSE)). The paper in `paper/` is
© the author, pending publication.
