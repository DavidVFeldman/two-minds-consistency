import RequestProject.TwoMinds.Construction

/-!
# Necessitation and extensional correctness for the trigger family (mini round 3)

Two small consequences of the Main-Theorem construction (`Construction.lean`,
`Main.lean`), requested as round-3 addenda (validation memo A.3.1 / A.3.2):

* **Necessitation (D1) for the machine predicates.** For the never-firing family
  `Θ := Theta T K patf`, if `T ⊢ φ` then `T ⊢ Prov_{Θ i}(⌜φ⌝)`
  (`necessitation`).  The witness is the standard code of a real derivation of `φ`;
  it lies before any trigger stage because no trigger stage is ever standard
  (`not_fires_of_standard`, the model-level form of `never_fires`).

* **Extensional correctness over `ℕ`.** `Prov_{Θ i}` *defines real provability in the
  standard model*: `ℕ ⊨ Prov_{Θ i}(⌜φ⌝) ↔ T ⊢ φ` (`provBefore_nat_iff`).

Both go through the existing semantic idiom (`provable_of_models`, the standard-code
transfer `proof_absolute`, and `provable_of_standard_proof`), with no new machinery.
-/

namespace TwoMinds

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.FirstOrder.Arithmetic.Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] {n : ℕ}

/-- **Evaluation of `Prov_{Θ i}(⌜φ⌝)` in a model.**  In any model `M ⊧ IΣ₁`,
`Prov_{Θ i}` at the standard code `⌜φ⌝` says exactly that some stage `y` carries a
`T`-proof of `φ` at which `η_i` has not yet fired. -/
theorem provBefore_Theta_eval (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (φ : Sentence ℒₒᵣ) :
    Semiformula.Evalbm M ![] ((provBefore (Theta T K patf i)).val/[⌜φ⌝]) ↔
      ∃ y, T.Proof y (⌜φ⌝ : M) ∧ ¬ Fires T K patf i (codeVal T K patf M) y := by
  simp only [provBefore, HierarchySymbol.Semiformula.val_mkSigma, Theta]
  simp [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    Semiterm.val_bShift, Semiformula.eval_rew, Function.comp_def, Rew.q_bvar_succ,
    Rew.q_bvar_zero, Rew.q, Empty.eq_elim, etaC_pi_eval]

/-- **No trigger stage is standard.**  For the family `Θ = Theta T K patf`, in any
model `M ⊧ IΣ₁` the stage formula `η_i` never fires at a standard numeral `(m : M)`.
This is the model-level generalization of `never_fires` (the case `M = ℕ`): a trigger
stage `y₀ ≤ (m : M)` would be standard by `eq_nat_of_lt_nat`, transfer down to `ℕ`
via `proof_absolute`, and make a watched sentence really provable, contradicting
`no_watched_provable`. -/
theorem not_fires_of_standard [Consistent T] (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (m : ℕ) :
    ¬ Fires T K patf i (codeVal T K patf M) (m : M) := by
  rintro ⟨y₀, hy₀le, ⟨⟨j, hj⟩, -⟩, -⟩
  have hlt : y₀ < ((m + 1 : ℕ) : M) :=
    lt_of_le_of_lt hy₀le (by exact_mod_cast Nat.lt_succ_self m)
  obtain ⟨m', rfl⟩ := eq_nat_of_lt_nat hlt
  have hjℕ : T.Proof (m' : ℕ) (⌜deltaFix T K patf j⌝ : ℕ) :=
    (proof_absolute T m' (deltaFix T K patf j)).mpr (by simpa [codeVal] using hj)
  have hprov : T ⊢ deltaFix T K patf j :=
    provable_of_standard_proof (V := ℕ) (n := m') (φ := deltaFix T K patf j) (by simpa using hjℕ)
  have hns : T ⊢ ∼(sigmaC T K patf (patf j)) :=
    Entailment.K!_left (fp_equiv T K patf j) ⨀ hprov
  exact no_watched_provable T K patf (patf j) ⟨j, rfl⟩ hns

/-- **Necessitation / D1 for the machine predicates (Theorem 4.1(1)).**  For the
never-firing family `Θ = Theta T K patf`, external provability implies internal
machine-provability: if `T ⊢ φ` then `T ⊢ Prov_{Θ i}(⌜φ⌝)`. -/
theorem necessitation [Consistent T] (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    {φ : Sentence ℒₒᵣ} (h : T ⊢ φ) :
    T ⊢ (provBefore (Theta T K patf i)).val/[⌜φ⌝] := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  obtain ⟨n0, hn0⟩ := (provable_iff_provable (T := T) (φ := φ)).mpr h
  rw [models_iff, provBefore_Theta_eval]
  exact ⟨(n0 : M), (proof_absolute (M := M) T n0 φ).mp hn0, not_fires_of_standard T K patf i M n0⟩

/-- **Extensional correctness over `ℕ` (Theorem 4.1 conclusion / Lemma 2.3(2)).**
The machine-provability predicate `Prov_{Θ i}` defines real `T`-provability in the
standard model: `ℕ ⊨ Prov_{Θ i}(⌜φ⌝) ↔ T ⊢ φ`.  Forward is `provable_of_standard_proof`;
backward is the standard-code witness together with `not_fires_of_standard`. -/
theorem provBefore_nat_iff [Consistent T] (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    (φ : Sentence ℒₒᵣ) :
    Semiformula.Evalbm ℕ ![] ((provBefore (Theta T K patf i)).val/[⌜φ⌝]) ↔ T ⊢ φ := by
  rw [provBefore_Theta_eval]
  constructor
  · rintro ⟨y, hpf, -⟩
    exact provable_of_standard_proof (V := ℕ) (n := y) (φ := φ) (by simpa using hpf)
  · intro h
    obtain ⟨n0, hn0⟩ := (provable_iff_provable (T := T) (φ := φ)).mpr h
    exact ⟨n0, by simpa using hn0, by simpa using not_fires_of_standard T K patf i ℕ n0⟩

end TwoMinds
