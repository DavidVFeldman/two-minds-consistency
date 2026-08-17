import RequestProject.TwoMinds.StageFormula
import Foundation.FirstOrder.Bootstrapping.FixedPoint

/-!
# The self-referential trigger construction (Layer II′)

This file implements the construction underlying the Main Theorem (Theorem 4.1),
following the *simultaneous Rosser-style syntactic fixed point* strategy: rather than
a parametric formula fixed point, we take the simultaneous diagonal fixed point of the
`K := 2 ^ n` *watched sentences* `δ_S`, one per pattern `S ⊆ Fin n`.  The stage
formulas `η_i` are then explicit, non-self-referential `Δ₁` formulas mentioning the
codes `⌜δ_j⌝` as numeral parameters.

All the self-reference is packaged by Foundation's `exclusiveMultifixedpoint`.
-/

namespace TwoMinds

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.FirstOrder.Arithmetic.Bootstrapping

/-- Hierarchy classification is preserved by finite disjunctions (the disjunction
analogue of `Hierarchy.matrix_conj_iff`). -/
lemma matrix_disj_hier {ξ} {Γ s nn} : ∀ {m} {φ : Fin m → Semiformula ℒₒᵣ ξ nn},
    Hierarchy Γ s (Matrix.disj φ) ↔ ∀ j, Hierarchy Γ s (φ j)
  | 0, _ => by simp [Matrix.disj]
  | _ + 1, φ => by
      rw [show Matrix.disj φ = φ 0 ⋎ Matrix.disj (Matrix.vecTail φ) from rfl]
      simp [matrix_disj_hier, Fin.forall_fin_succ, Matrix.vecTail]

variable (T : ArithmeticTheory) [T.Δ₁]

/-- An enumeration of the `2 ^ n` verdict patterns `S ⊆ Fin n`. -/
noncomputable def patEquiv (n : ℕ) : Fin (2 ^ n) ≃ Finset (Fin n) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

variable {n : ℕ}

/-! ### Templates with `K` free code-variables

In every template below the free variable `#0` is the "working" variable (a stage or
a proof code) and `#(j.succ.succ)` / `#(j.succ)` are the `K` code-variables that will
be substituted by `⌜δ_j⌝`. -/

/-- "Some watched sentence has a proof at `#0`", `Σ`-presentation, arity `K + 1`
(`#0 = w`, code `j` at `#(j.succ)`). -/
noncomputable def watchedSig (K : ℕ) : Semisentence ℒₒᵣ (K + 1) :=
  Matrix.disj (fun j : Fin K => (“!T.proof.sigma #0 #(j.succ)” : Semisentence ℒₒᵣ (K + 1)))

/-- "Some watched sentence has a proof at `#0`", `Π`-presentation. -/
noncomputable def watchedPi (K : ℕ) : Semisentence ℒₒᵣ (K + 1) :=
  Matrix.disj (fun j : Fin K => (“!T.proof.pi #0 #(j.succ)” : Semisentence ℒₒᵣ (K + 1)))

/-- `trig`, `Σ`-presentation, arity `K + 2` (`#0 = y₀`, `#1` unused, code `j` at
`#(j.succ.succ)`): `y₀` is the least stage coding a proof of some watched sentence.

The positive occurrence uses the `Σ`-presentation of `watched`; the minimality clause
`∀ y' < y₀, ¬watched(y')` uses the `Π`-presentation so that its negation stays `Σ₁`. -/
noncomputable def trigSig (K : ℕ) : Semisentence ℒₒᵣ (K + 2) :=
  (Rew.subst (#0 :> fun j : Fin K => #(j.succ.succ)) ▹ watchedSig T K) ⋏
    Semiformula.ballLT (#0) (∼(Rew.subst (#0 :> fun j : Fin K => #(j.succ.succ.succ)) ▹ watchedPi T K))

/-- `trig`, `Π`-presentation (swap `sigma`/`pi`). -/
noncomputable def trigPi (K : ℕ) : Semisentence ℒₒᵣ (K + 2) :=
  (Rew.subst (#0 :> fun j : Fin K => #(j.succ.succ)) ▹ watchedPi T K) ⋏
    Semiformula.ballLT (#0) (∼(Rew.subst (#0 :> fun j : Fin K => #(j.succ.succ.succ)) ▹ watchedSig T K))

/-- `pat_i`, `Σ`-presentation: the least `j` with a proof at `y₀` has `i ∈ S_j`. -/
noncomputable def patSig (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) :
    Semisentence ℒₒᵣ (K + 2) :=
  Matrix.disj (fun j : Fin K =>
    if i ∈ patf j then
      (“!T.proof.sigma #0 #(j.succ.succ)” : Semisentence ℒₒᵣ (K + 2)) ⋏
        Matrix.conj (fun j' : Fin K =>
          if j' < j then (∼(“!T.proof.pi #0 #(j'.succ.succ)” : Semisentence ℒₒᵣ (K + 2)))
          else ⊤)
    else ⊥)

/-- `pat_i`, `Π`-presentation (swap `sigma`/`pi`). -/
noncomputable def patPi (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) :
    Semisentence ℒₒᵣ (K + 2) :=
  Matrix.disj (fun j : Fin K =>
    if i ∈ patf j then
      (“!T.proof.pi #0 #(j.succ.succ)” : Semisentence ℒₒᵣ (K + 2)) ⋏
        Matrix.conj (fun j' : Fin K =>
          if j' < j then (∼(“!T.proof.sigma #0 #(j'.succ.succ)” : Semisentence ℒₒᵣ (K + 2)))
          else ⊤)
    else ⊥)

/-- `η_i`, `Σ`-presentation, arity `K + 1` (`#0 = y`, code `j` at `#(j.succ)`):
`∃ y₀ ≤ y, trig(y₀) ∧ pat_i(y₀)`. -/
noncomputable def etaSigTmpl (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) :
    𝚺₁.Semisentence (K + 1) :=
  .mkSigma (Semiformula.bexLTSucc (#0) ((trigSig T K) ⋏ (patSig T K patf i))) (by
    rw [Hierarchy.bexLTSucc_iff]
    simp only [trigSig, watchedSig, watchedPi, patSig, Hierarchy.and_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply Hierarchy.rew; rw [matrix_disj_hier]; intro j; simp
    · have hB : Hierarchy 𝚷 1
          (Rew.subst (#0 :> fun j : Fin K => (#(j.succ.succ.succ) : Semiterm ℒₒᵣ Empty (K + 3))) ▹
            Matrix.disj (fun j : Fin K => (“!T.proof.pi #0 #(j.succ)” : Semisentence ℒₒᵣ (K + 1)))) := by
        apply Hierarchy.rew; rw [matrix_disj_hier]; intro j; simp
      exact Hierarchy.ballLT_iff.mpr (Hierarchy.neg hB)
    · rw [matrix_disj_hier]
      intro j
      by_cases h : i ∈ patf j
      · simp only [h, if_true, Hierarchy.and_iff, Hierarchy.matrix_conj_iff]
        refine ⟨by simp, fun j' => ?_⟩
        by_cases h' : j' < j <;> simp [h']
      · simp [h])

/-- `η_i`, `Π`-presentation. -/
noncomputable def etaPiTmpl (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) :
    𝚷₁.Semisentence (K + 1) :=
  .mkPi (Semiformula.bexLTSucc (#0) ((trigPi T K) ⋏ (patPi T K patf i))) (by
    rw [Hierarchy.bexLTSucc_iff]
    simp only [trigPi, watchedSig, watchedPi, patPi, Hierarchy.and_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply Hierarchy.rew; rw [matrix_disj_hier]; intro j; simp
    · have hB : Hierarchy 𝚺 1
          (Rew.subst (#0 :> fun j : Fin K => (#(j.succ.succ.succ) : Semiterm ℒₒᵣ Empty (K + 3))) ▹
            Matrix.disj (fun j : Fin K => (“!T.proof.sigma #0 #(j.succ)” : Semisentence ℒₒᵣ (K + 1)))) := by
        apply Hierarchy.rew; rw [matrix_disj_hier]; intro j; simp
      exact Hierarchy.ballLT_iff.mpr (Hierarchy.neg hB)
    · rw [matrix_disj_hier]
      intro j
      by_cases h : i ∈ patf j
      · simp only [h, if_true, Hierarchy.and_iff, Hierarchy.matrix_conj_iff]
        refine ⟨by simp, fun j' => ?_⟩
        by_cases h' : j' < j <;> simp [h']
      · simp [h])

/-- Insert the working variable `p` (as `#0`) and the code variables (`#1..#K`)
into an arity-`K+1` template, inside an arity-`K+1` context (`#0 = p`, codes
`#1..#K`). -/
noncomputable def atCode (K : ℕ) (φ : Semisentence ℒₒᵣ (K + 1)) : Semisentence ℒₒᵣ (K + 1) :=
  (Rew.subst (#0 :> fun j : Fin K => #(j.succ))) ▹ φ

/-- The watched-pattern template `σ_S` with free code variables (arity `K`):
`∃ p, Pf(p, ⌜⊥⌝) ∧ (∀ q < p, ¬Pf(q, ⌜⊥⌝)) ∧ ⋀_{i ∈ S} η_i(p) ∧ ⋀_{i ∉ S} ¬η_i(p)`. -/
noncomputable def sigmaTmpl (K : ℕ) (patf : Fin K → Finset (Fin n)) (S : Finset (Fin n)) :
    Semisentence ℒₒᵣ K :=
  ∃' (
    (“!T.proof.sigma #0 !!(⌜(⊥ : Sentence ℒₒᵣ)⌝)” : Semisentence ℒₒᵣ (K + 1)) ⋏
    (“∀ q < #0, ¬!T.proof.pi q !!(⌜(⊥ : Sentence ℒₒᵣ)⌝)” : Semisentence ℒₒᵣ (K + 1)) ⋏
    (Matrix.conj (fun i : Fin n =>
      if i ∈ S then atCode K (etaSigTmpl T K patf i).val else ⊤)) ⋏
    (Matrix.conj (fun i : Fin n =>
      if i ∉ S then ∼(atCode K (etaPiTmpl T K patf i).val) else ⊤)))

/-- The watched sentences, as the `K` free code variables get bound to their own codes:
`W j := ∼ σ_{S_j}`. -/
noncomputable def watched (K : ℕ) (patf : Fin K → Finset (Fin n)) (j : Fin K) :
    Semisentence ℒₒᵣ K :=
  ∼(sigmaTmpl T K patf (patf j))

/-- The simultaneous fixed point: `δ_j`. -/
noncomputable def deltaFix (K : ℕ) (patf : Fin K → Finset (Fin n)) (j : Fin K) : Sentence ℒₒᵣ :=
  exclusiveMultifixedpoint (watched T K patf) j

/-- The `Δ₁` stage-formula template `η_i` (arity `K + 1`, `#0 = y`, codes `#1..#K`). -/
noncomputable def etaDeltaTmpl (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) :
    𝚫₁.Semisentence (K + 1) :=
  .mkDelta (etaSigTmpl T K patf i) (etaPiTmpl T K patf i)

variable [𝗜𝚺₁ ⪯ T]

/-- The concrete stage formula `η_i`, obtained by substituting the codes `⌜δ_j⌝`. -/
noncomputable def etaC (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) : 𝚫₁.Semisentence 1 :=
  (etaDeltaTmpl T K patf i).rew (Rew.subst (#0 :> fun j : Fin K => ⌜deltaFix T K patf j⌝))

/-- The concrete pattern sentence `σ_S`. -/
noncomputable def sigmaC (K : ℕ) (patf : Fin K → Finset (Fin n)) (S : Finset (Fin n)) :
    Sentence ℒₒᵣ :=
  (Rew.subst (fun j : Fin K => ⌜deltaFix T K patf j⌝)) ▹ (sigmaTmpl T K patf S)

/-- Semantic meaning of `η_i` firing at stage `y` in a model `M ⊧ IΣ₁`: there is a
least trigger stage `y₀ ≤ y` at which some watched sentence `δ_j` has a proof and no
earlier stage does, and the least such `j` has `i ∈ S_j`. -/
def Fires (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    {M : Type} [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (codeval : Fin K → M) (y : M) : Prop :=
  ∃ y₀ ≤ y,
    ((∃ j : Fin K, T.Proof y₀ (codeval j)) ∧
      ∀ y' < y₀, ∀ j : Fin K, ¬ T.Proof y' (codeval j)) ∧
    (∃ j : Fin K, i ∈ patf j ∧ T.Proof y₀ (codeval j) ∧
      ∀ j' : Fin K, j' < j → ¬ T.Proof y₀ (codeval j'))

/-- The values of the code terms `⌜δ_j⌝` in a model. -/
noncomputable def codeVal (K : ℕ) (patf : Fin K → Finset (Fin n))
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (j : Fin K) : M := (⌜deltaFix T K patf j⌝ : M)

/-- **Evaluation of the `Σ`-presentation of `η_i`.** -/
theorem etaC_sigma_eval (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (y : M) :
    Semiformula.Evalbm M ![y] (etaC T K patf i).sigma.val ↔
      Fires T K patf i (codeVal T K patf M) y := by
  simp only [etaC, etaDeltaTmpl, etaSigTmpl, HierarchySymbol.Semiformula.rew,
    HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
    HierarchySymbol.Semiformula.val_rew, trigSig, patSig, watchedSig, watchedPi]
  simp [Semiformula.eval_rew, Function.comp_def, Semiformula.eval_ballLT,
    Matrix.constant_eq_singleton, Fires, codeVal, Semiformula.eval_substs,
    Matrix.comp_vecCons', apply_ite (Semiformula.Evalm M _ _), Matrix.vecHead, Matrix.vecTail]

/-- **Evaluation of the `Π`-presentation of `η_i`.** -/
theorem etaC_pi_eval (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (y : M) :
    Semiformula.Evalbm M ![y] (etaC T K patf i).pi.val ↔
      Fires T K patf i (codeVal T K patf M) y := by
  simp only [etaC, etaDeltaTmpl, etaPiTmpl, HierarchySymbol.Semiformula.rew,
    HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
    HierarchySymbol.Semiformula.val_rew, trigPi, patPi, watchedSig, watchedPi]
  simp [Semiformula.eval_rew, Function.comp_def, Semiformula.eval_ballLT,
    Matrix.constant_eq_singleton, Fires, codeVal, Semiformula.eval_substs,
    Matrix.comp_vecCons', apply_ite (Semiformula.Evalm M _ _), Matrix.vecHead, Matrix.vecTail]

/-- `η_i` is provably proper: both presentations evaluate to `Fires`. -/
theorem etaC_proper (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) :
    (etaC T K patf i).ProvablyProperOn T := by
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  apply HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn
  intro M _ hMT
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  intro e
  rw [Matrix.fun_eq_vec_one (v := e), etaC_sigma_eval, etaC_pi_eval]

/-- `η_i` is provably monotone. -/
theorem etaC_mono (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) :
    T ⊢ “∀ y z, !(etaC T K patf i).pi y → y ≤ z → !(etaC T K patf i).sigma z” := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  have key : ∀ y z : M, Fires T K patf i (codeVal T K patf M) y → y ≤ z →
      Fires T K patf i (codeVal T K patf M) z := by
    rintro y z ⟨y₀, hy₀, htrig, hpat⟩ hyz
    exact ⟨y₀, le_trans hy₀ hyz, htrig, hpat⟩
  simp only [models_iff, Semiformula.eval_all]
  intro y z
  simpa [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    Semiterm.val_bShift, etaC_pi_eval, etaC_sigma_eval] using key y z

/-- The stage-formula family `Θ`. -/
noncomputable def Theta (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) : StageFml T :=
  ⟨etaC T K patf i, etaC_proper T K patf i, etaC_mono T K patf i⟩

/-! ### The pattern conjunction, the fixed-point equivalence and the two core lemmas -/

/-- The pattern conjunction `¬Con ∧ ⋀_{i ∈ S} Con_{η i} ∧ ⋀_{i ∉ S} ¬Con_{η i}`, generic in
the stage-formula family. -/
noncomputable def patConjG (Θ : Fin n → StageFml T) (S : Finset (Fin n)) : Sentence ℒₒᵣ :=
  ∼(↑T.consistent : Sentence ℒₒᵣ) ⋏
    (Matrix.conj (fun i : Fin n =>
      if i ∈ S then (conBefore (Θ i)).val else ⊤)) ⋏
    (Matrix.conj (fun i : Fin n =>
      if i ∈ S then ⊤ else ∼(conBefore (Θ i)).val))

/-- The pattern conjunction for the constructed family. -/
noncomputable def patConj (K : ℕ) (patf : Fin K → Finset (Fin n)) (S : Finset (Fin n)) :
    Sentence ℒₒᵣ :=
  patConjG T (Theta T K patf) S

/-- **Alignment**: substituting the codes into the watched template gives exactly
`∼σ_{S_j}`.  Holds definitionally. -/
theorem watched_subst_eq (K : ℕ) (patf : Fin K → Finset (Fin n)) (j : Fin K) :
    (Rew.subst fun j' : Fin K => ⌜deltaFix T K patf j'⌝) ▹ (watched T K patf j) =
      ∼(sigmaC T K patf (patf j)) := by
  simp [watched, sigmaC]

/-- **Fixed-point equivalence (FP).** `T ⊢ δ_j ⭤ ¬σ_{S_j}`. -/
theorem fp_equiv (K : ℕ) (patf : Fin K → Finset (Fin n)) (j : Fin K) :
    T ⊢ deltaFix T K patf j ⭤ ∼(sigmaC T K patf (patf j)) := by
  have h := exclusiveMultidiagonal (T := T) (watched T K patf) (i := j)
  have e : (Rew.subst fun j' : Fin K => ⌜exclusiveMultifixedpoint (watched T K patf) j'⌝) ▹
      (watched T K patf j) = ∼(sigmaC T K patf (patf j)) := watched_subst_eq T K patf j
  rw [e] at h
  exact h

/-- **Evaluation of the pattern sentence `σ_S`.** -/
theorem sigmaC_eval (K : ℕ) (patf : Fin K → Finset (Fin n)) (S : Finset (Fin n))
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] :
    Semiformula.Evalbm M ![] (sigmaC T K patf S) ↔
      ∃ p, T.Proof p (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M) ∧
        (∀ q < p, ¬ T.Proof q (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M)) ∧
        (∀ i, i ∈ S → Fires T K patf i (codeVal T K patf M) p) ∧
        (∀ i, i ∉ S → ¬ Fires T K patf i (codeVal T K patf M) p) := by
  simp only [sigmaC, sigmaTmpl, atCode, etaSigTmpl, etaPiTmpl,
    HierarchySymbol.Semiformula.val_mkSigma, HierarchySymbol.Semiformula.val_mkPi,
    trigSig, trigPi, patSig, patPi, watchedSig, watchedPi]
  simp [Semiformula.eval_rew, Function.comp_def, Semiformula.eval_ballLT,
    Matrix.constant_eq_singleton, Fires, codeVal, Semiformula.eval_substs,
    Matrix.comp_vecCons', apply_ite (Semiformula.Evalm M _ _), Matrix.vecHead, Matrix.vecTail]

omit [𝗜𝚺₁ ⪯ T] in
/-- `Fires` is monotone in the stage. -/
theorem Fires_mono (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    {M : Type} [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] {codeval : Fin K → M} {y z : M}
    (h : Fires T K patf i codeval y) (hyz : y ≤ z) : Fires T K patf i codeval z := by
  obtain ⟨y₀, hy₀, htrig, hpat⟩ := h
  exact ⟨y₀, le_trans hy₀ hyz, htrig, hpat⟩

/-- **Evaluation of `Con_{η i}` for the constructed family.** -/
theorem conBefore_Theta_eval (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] :
    Semiformula.Evalbm M ![] (conBefore (Theta T K patf i)).val ↔
      ∀ y, T.Proof y (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M) → Fires T K patf i (codeVal T K patf M) y := by
  simp only [conBefore, HierarchySymbol.Semiformula.val_mkPi, Theta]
  simp [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
  constructor
  · intro h y hy
    exact (etaC_pi_eval T K patf i M y).mp (by simpa using h y (by simpa using hy))
  · intro h y hy
    exact (by simpa using (etaC_pi_eval T K patf i M y).mpr (h y (by simpa using hy)))

omit [𝗜𝚺₁ ⪯ T] in
/-- **Least inconsistency proof.** In a model of `IΣ₁`, if there is an inconsistency
proof then there is a least one. -/
theorem exists_least_incons (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]
    (h : ∃ p : M, T.Proof p (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M)) :
    ∃ p : M, T.Proof p (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M) ∧
      ∀ q < p, ¬ T.Proof q (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M) := by
  have hdef : 𝚫-[1].DefinablePred (fun x : M => T.Proof x (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M)) := by
    apply HierarchySymbol.DefinableRel.comp (P := (T.Proof : M → M → Prop)) inferInstance
      (g := fun _ => (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M))
    · definability
    · definability
  obtain ⟨p, hp⟩ := h
  exact InductionOnHierarchy.least_number_sigma 𝚫 1 hdef hp

/-- **Evaluation of the pattern conjunction.** -/
theorem patConj_eval (K : ℕ) (patf : Fin K → Finset (Fin n)) (S : Finset (Fin n))
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] :
    Semiformula.Evalbm M ![] (patConj T K patf S) ↔
      (∃ p, T.Proof p (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M)) ∧
      (∀ i, i ∈ S → ∀ y, T.Proof y (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M) →
          Fires T K patf i (codeVal T K patf M) y) ∧
      (∀ i, i ∉ S → ¬ ∀ y, T.Proof y (⌜(⊥ : Sentence ℒₒᵣ)⌝ : M) →
          Fires T K patf i (codeVal T K patf M) y) := by
  simp only [patConj, patConjG]
  simp [conBefore_Theta_eval, Theory.Consistent, Theory.Provable,
    apply_ite (Semiformula.Evalbm M ![])]

/-- **Reformulation Lemma (L5′ / paper Lemma 3.1).** -/
theorem reformulation (K : ℕ) (patf : Fin K → Finset (Fin n))
    (S : Finset (Fin n)) :
    T ⊢ (sigmaC T K patf S) ⭤ (patConj T K patf S) := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  rw [models_iff]
  simp only [LogicalConnective.HomClass.map_iff, sigmaC_eval, patConj_eval]
  constructor
  · rintro ⟨p, hp, hpleast, hin, hout⟩
    refine ⟨⟨p, hp⟩, ?_, ?_⟩
    · intro i hi y hy
      have hpy : p ≤ y := by by_contra hlt; exact hpleast y (not_le.mp hlt) hy
      exact Fires_mono T K patf i (hin i hi) hpy
    · intro i hi hcon
      exact hout i hi (hcon p hp)
  · rintro ⟨hex, hin, hout⟩
    obtain ⟨p, hp, hpleast⟩ := exists_least_incons T M hex
    refine ⟨p, hp, hpleast, ?_, ?_⟩
    · intro i hi
      exact hin i hi p hp
    · intro i hi hFires
      apply hout i hi
      intro y hy
      have hpy : p ≤ y := by by_contra hlt; exact hpleast y (not_le.mp hlt) hy
      exact Fires_mono T K patf i hFires hpy

omit [𝗜𝚺₁ ⪯ T] in
/-- **Absoluteness of the `Δ₁` proof relation at standard arguments.** The proof
relation `T.Proof` agrees between `ℕ` and any model `M ⊧ IΣ₁` when both arguments are
codes of standard objects (a numeral stage `m` and the code of a fixed sentence `ψ`). -/
theorem proof_absolute {M : Type} [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]
    (m : ℕ) (ψ : Sentence ℒₒᵣ) :
    T.Proof (m : ℕ) (⌜ψ⌝ : ℕ) ↔ T.Proof (m : M) (⌜ψ⌝ : M) := by
  have h := Defined.shigmaOne_absolute M (φ := T.proof)
    (R := fun v : Fin 2 → ℕ ↦ T.Proof (v 0) (v 1))
    (R' := fun v : Fin 2 → M ↦ T.Proof (v 0) (v 1))
    Theory.Proof.defined Theory.Proof.defined ![m, ⌜ψ⌝]
  simpa [Sentence.coe_quote_eq_quote] using h

omit [𝗜𝚺₁ ⪯ T] in
/-- **The trigger characterization.** In a model `M`, if `w` is a least trigger stage
(some `δ_{j0}` has a proof at `w`, none earlier, and `j0` is the least code proved at
`w`), then at every `p ≥ w` the stage formula `η_i` fires iff `i ∈ patf j0`. -/
theorem fires_char (K : ℕ) (patf : Fin K → Finset (Fin n)) (j0 : Fin K)
    {M : Type} [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (w : M)
    (hwj0 : T.Proof w (codeVal T K patf M j0))
    (hwmin : ∀ z < w, ∀ j : Fin K, ¬ T.Proof z (codeVal T K patf M j))
    (hjmin : ∀ j' : Fin K, j' < j0 → ¬ T.Proof w (codeVal T K patf M j'))
    (p : M) (hwp : w ≤ p) (i : Fin n) :
    Fires T K patf i (codeVal T K patf M) p ↔ i ∈ patf j0 := by
  constructor
  · rintro ⟨w', hw'p, ⟨⟨j1, hj1proof⟩, hw'min⟩, ⟨j2, hi2, hj2proof, hj2min⟩⟩
    -- The trigger stage `w'` must be `w`.
    have hw'eq : w' = w := by
      rcases lt_trichotomy w' w with h | h | h
      · exact absurd hj1proof (hwmin w' h j1)
      · exact h
      · exact absurd hwj0 (hw'min w h j0)
    subst hw'eq
    -- The least code `j2` proved at `w'` must be `j0`.
    have hj2eq : j2 = j0 := by
      rcases lt_trichotomy j2 j0 with h | h | h
      · exact absurd hj2proof (hjmin j2 h)
      · exact h
      · exact absurd hwj0 (hj2min j0 h)
    subst hj2eq
    exact hi2
  · intro hi
    exact ⟨w, hwp, ⟨⟨j0, hwj0⟩, hwmin⟩, ⟨j0, hi, hwj0, hjmin⟩⟩

/-- **Semantic pincer (per model).** Given the external least-trigger facts (in `ℕ`)
and that the watched sentence `σ_{patf j0}` is `T`-refutable, every model of `T` is
consistent. -/
theorem models_consistent_of_facts [Consistent T] (K : ℕ) (patf : Fin K → Finset (Fin n))
    (y₀ : ℕ) (j0 : Fin K)
    (hfact1 : T.Proof (y₀ : ℕ) (⌜deltaFix T K patf j0⌝ : ℕ))
    (hfact2 : ∀ m < y₀, ∀ j : Fin K, ¬ T.Proof (m : ℕ) (⌜deltaFix T K patf j⌝ : ℕ))
    (hfact3 : ∀ j' : Fin K, j' < j0 → ¬ T.Proof (y₀ : ℕ) (⌜deltaFix T K patf j'⌝ : ℕ))
    (hfact4 : ∀ m < y₀, ¬ T.Proof (m : ℕ) (⌜(⊥ : Sentence ℒₒᵣ)⌝ : ℕ))
    (hns : T ⊢ ∼(sigmaC T K patf (patf j0)))
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (hMT : M ⊧ₘ* T) :
    T.Consistent M := by
  simp only [Theory.Consistent, Theory.Provable]
  rintro ⟨p0, hp0⟩
  obtain ⟨p, hp, hpleast⟩ := exists_least_incons T M ⟨p0, hp0⟩
  -- Transfer the external facts into `M` at `w := (y₀ : M)`.
  have hwj0 : T.Proof (y₀ : M) (codeVal T K patf M j0) := by
    have := (proof_absolute (M := M) T y₀ (deltaFix T K patf j0)).mp hfact1
    simpa [codeVal] using this
  have hwmin : ∀ z < (y₀ : M), ∀ j : Fin K, ¬ T.Proof z (codeVal T K patf M j) := by
    intro z hz j hProof
    obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat hz
    have hmlt : m < y₀ := by exact_mod_cast hz
    refine hfact2 m hmlt j ?_
    exact (proof_absolute T m (deltaFix T K patf j)).mpr (by simpa [codeVal] using hProof)
  have hjmin : ∀ j' : Fin K, j' < j0 → ¬ T.Proof (y₀ : M) (codeVal T K patf M j') := by
    intro j' hj' hProof
    refine hfact3 j' hj' ?_
    exact (proof_absolute T y₀ (deltaFix T K patf j')).mpr (by simpa [codeVal] using hProof)
  by_cases hwp : (y₀ : M) ≤ p
  · -- Case `(y₀ : M) ≤ p`: `M ⊨ σ_{patf j0}`, contradicting `hns`.
    have hσ : Semiformula.Evalbm M ![] (sigmaC T K patf (patf j0)) := by
      rw [sigmaC_eval]
      refine ⟨p, hp, hpleast, ?_, ?_⟩
      · intro i hi
        exact (fires_char T K patf j0 (y₀ : M) hwj0 hwmin hjmin p hwp i).mpr hi
      · intro i hi hFires
        exact hi ((fires_char T K patf j0 (y₀ : M) hwj0 hwmin hjmin p hwp i).mp hFires)
    have hMσ : ¬ Semiformula.Evalbm M ![] (sigmaC T K patf (patf j0)) := by
      have := consequence_iff.mp (sound! hns) M inferInstance
      simpa [models_iff] using this
    exact hMσ hσ
  · -- Case `p < (y₀ : M)`: `p` is a standard numeral `< y₀`, contradicting `hfact4`.
    have hpw : p < (y₀ : M) := not_le.mp hwp
    obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat hpw
    have hmlt : m < y₀ := by exact_mod_cast hpw
    exact hfact4 m hmlt ((proof_absolute T m (⊥ : Sentence ℒₒᵣ)).mpr hp)

open Classical in
/-- If some watched sentence `δ_{j0}` is `T`-provable, then `T` proves its own
consistency (which, with Gödel II, is a contradiction). -/
theorem consistent_of_delta_provable [Consistent T] (K : ℕ) (patf : Fin K → Finset (Fin n))
    (j0 : Fin K) (h : T ⊢ deltaFix T K patf j0) :
    T ⊢ ↑T.consistent := by
  -- A real proof code (in `ℕ`) of the provable watched sentence `δ_{j0}`.
  obtain ⟨n0, hn0⟩ := (provable_iff_provable (T := T) (φ := deltaFix T K patf j0)).mpr h
  -- The least trigger stage `y₀`: the least `m` at which some `δ_j` has a proof.
  have hQex : ∃ m : ℕ, ∃ j : Fin K, T.Proof (m : ℕ) (⌜deltaFix T K patf j⌝ : ℕ) := ⟨n0, j0, hn0⟩
  set y₀ : ℕ := Nat.find hQex with hy₀def
  have hy₀spec : ∃ j : Fin K, T.Proof (y₀ : ℕ) (⌜deltaFix T K patf j⌝ : ℕ) := Nat.find_spec hQex
  have hy₀min : ∀ m, m < y₀ → ¬ ∃ j : Fin K, T.Proof (m : ℕ) (⌜deltaFix T K patf j⌝ : ℕ) :=
    fun m hm => Nat.find_min hQex hm
  -- The least code index `j1` proved at `y₀`.
  set s : Finset (Fin K) :=
    Finset.univ.filter (fun j => T.Proof (y₀ : ℕ) (⌜deltaFix T K patf j⌝ : ℕ)) with hsdef
  have hsne : s.Nonempty := by
    obtain ⟨j, hj⟩ := hy₀spec
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  set j1 : Fin K := s.min' hsne with hj1def
  have hfact1 : T.Proof (y₀ : ℕ) (⌜deltaFix T K patf j1⌝ : ℕ) :=
    (Finset.mem_filter.mp (Finset.min'_mem s hsne)).2
  have hfact2 : ∀ m < y₀, ∀ j : Fin K, ¬ T.Proof (m : ℕ) (⌜deltaFix T K patf j⌝ : ℕ) :=
    fun m hm j hpf => hy₀min m hm ⟨j, hpf⟩
  have hfact3 : ∀ j' : Fin K, j' < j1 → ¬ T.Proof (y₀ : ℕ) (⌜deltaFix T K patf j'⌝ : ℕ) := by
    intro j' hj' hpf
    have : j' ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpf⟩
    exact absurd (Finset.min'_le s j' this) (not_le.mpr hj')
  have hfact4 : ∀ m < y₀, ¬ T.Proof (m : ℕ) (⌜(⊥ : Sentence ℒₒᵣ)⌝ : ℕ) :=
    fun m _ hpf =>
      absurd
        (provable_of_standard_proof (V := ℕ) (n := m) (φ := (⊥ : Sentence ℒₒᵣ))
          (by simpa using hpf))
        (Entailment.Consistent.not_bot inferInstance)
  -- `δ_{j1}` is provable, so `σ_{patf j1}` is refutable.
  have hδj1 : T ⊢ deltaFix T K patf j1 :=
    provable_of_standard_proof (V := ℕ) (n := y₀) (φ := deltaFix T K patf j1)
      (by simpa using hfact1)
  have hns : T ⊢ ∼(sigmaC T K patf (patf j1)) :=
    Entailment.K!_left (fp_equiv T K patf j1) ⨀ hδj1
  -- Every model of `T` is consistent, hence `T` proves its own consistency.
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  have hcons : T.Consistent M :=
    models_consistent_of_facts T K patf y₀ j1 hfact1 hfact2 hfact3 hfact4 hns M hMT
  simpa [models_iff] using hcons

/-- **Self-defeat (L6′ / core of Theorem 4.1).** No watched sentence is refutable. -/
theorem no_watched_provable [Consistent T] (K : ℕ) (patf : Fin K → Finset (Fin n))
    (S : Finset (Fin n)) (hS : ∃ j : Fin K, patf j = S) :
    T ⊬ ∼(sigmaC T K patf S) := by
  intro hns
  obtain ⟨j0, rfl⟩ := hS
  have hdelta : T ⊢ deltaFix T K patf j0 :=
    Entailment.K!_right (fp_equiv T K patf j0) ⨀ hns
  exact consistent_unprovable T (consistent_of_delta_provable T K patf j0 hdelta)

/-- **Never fires.** In the standard model no `η_i` fires at any standard stage. -/
theorem never_fires [Consistent T] (K : ℕ) (patf : Fin K → Finset (Fin n)) (i : Fin n) (y : ℕ) :
    ¬ Semiformula.Evalbm ℕ ![(y : ℕ)] (etaC T K patf i).val := by
  rw [← HierarchySymbol.Semiformula.val_sigma, etaC_sigma_eval]
  rintro ⟨y₀, -, ⟨⟨j, hj⟩, -⟩, -⟩
  have hprov : T ⊢ deltaFix T K patf j :=
    provable_of_standard_proof (V := ℕ) (n := y₀) (φ := deltaFix T K patf j) (by simpa [codeVal] using hj)
  have hns : T ⊢ ∼(sigmaC T K patf (patf j)) :=
    Entailment.K!_left (fp_equiv T K patf j) ⨀ hprov
  exact no_watched_provable T K patf (patf j) ⟨j, rfl⟩ hns

end TwoMinds
