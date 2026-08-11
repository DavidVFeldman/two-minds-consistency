import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.RestrictedProvability

/-!
# Machine-cutoff provability, via stage formulas

This file formalizes the basic apparatus of

> D. V. Feldman, *Models of arithmetic of two minds about consistency* (draft 2),

following the reduction described in the accompanying instructions:

* **machines are replaced by stage formulas** (§1.1): a Turing machine `T` is used
  only through the `Δ₁` predicate `H_T(y) = "T has halted within y steps"`, which is
  provably monotone.  We therefore work directly with a *stage formula*: a `Δ₁`
  formula `η(y)` in one free variable which is provably monotone.
* **models are replaced by consistency statements** (§1.2).

We fix an arithmetic theory `T` (the paper's `PA`) which has a `Δ₁` axiomatization and
extends `IΣ₁`, so that Foundation's standard provability predicate, the diagonal
lemma, and Gödel's second incompleteness theorem are available.
-/

namespace TwoMinds

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.FirstOrder.Arithmetic.Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁]

/-- A **stage formula**: a `Δ₁` formula `η(y)` in one free variable which is provably
monotone in `y`.  This replaces the paper's halting predicate `H_T(y)`. -/
structure StageFml where
  /-- the underlying `Δ₁` formula `η(y)`. -/
  η : 𝚫₁.Semisentence 1
  /-- `η` is provably proper (its `Σ₁` and `Π₁` presentations are `T`-provably equivalent). -/
  proper : η.ProvablyProperOn T
  /-- `η` is `T`-provably monotone: `∀ y z, η(y) → y ≤ z → η(z)`. -/
  mono : T ⊢ “∀ y z, !η.pi y → y ≤ z → !η.sigma z”

variable {T}

/-- Machine-cutoff provability `Prov_η(x) := ∃ y, Pf(y, x) ∧ ¬ η(y)`:
`x` has a proof appearing before stage `η` fires. -/
noncomputable def provBefore (s : StageFml T) : 𝚺₁.Semisentence 1 := .mkSigma
  “x. ∃ y, !T.proof.sigma y x ∧ ¬!s.η.pi y”

/-- Machine-cutoff consistency, `Π₁` form: `Con_η := ∀ y, Pf(y, ⌜⊥⌝) → η(y)`. -/
noncomputable def conBefore (s : StageFml T) : 𝚷₁.Sentence := .mkPi
  “∀ y, !T.proof.sigma y !!(⌜(⊥ : Sentence ℒₒᵣ)⌝) → !s.η.pi y”

variable [𝗜𝚺₁ ⪯ T]

/-- **L0 (Definition 2.2, `Π₁` form).** `Con_η` is `T`-provably equivalent to
`¬ Prov_η(⌜⊥⌝)`. -/
theorem conBefore_iff_not_provBefore_bot (s : StageFml T) :
    T ⊢ (conBefore s).val ⭤ ∼((provBefore s).val/[⌜(⊥ : Sentence ℒₒᵣ)⌝]) := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  simp [models_iff, conBefore, provBefore, Semiformula.eval_substs, Semiformula.eval_rew,
    Function.comp_def, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Semiterm.val_bShift,
    Empty.eq_elim, Rew.q_bvar_succ, Rew.q_bvar_zero, Rew.q]
  simp only [imp_iff_not_or]

/-- **Lemma 2.3(1), part 1 (subpredicate).** Machine-cutoff provability is a
subpredicate of the standard provability predicate: whatever `Prov_η` counts as a
proof, so does the standard predicate. -/
theorem provBefore_imp_provable (s : StageFml T) :
    T ⊢ “∀ x, !(provBefore s).val x → !T.provable x” := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  simp [models_iff, provBefore, Theory.Provable, Semiformula.eval_substs, Semiformula.eval_rew,
    Function.comp_def, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Semiterm.val_bShift,
    Empty.eq_elim, Rew.q_bvar_succ, Rew.q_bvar_zero, Rew.q]
  intro x y hy _
  exact ⟨y, hy⟩

/-- **Lemma 2.3(1), part 2.** `T ⊢ Con(T) → Con_η(T)`. -/
theorem consistent_imp_conBefore (s : StageFml T) :
    T ⊢ ↑T.consistent ➝ (conBefore s).val := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  simp [models_iff, conBefore, Theory.Consistent, Theory.Provable]
  intro hcon y hy
  exact absurd hy (hcon y)

/-- The Rosser-style "halt before inconsistency" sentence `Halt^R(η)` (Def. 6.1 /
Definition D6): there is a stage `w` at which `η` first fires, and no inconsistency
proof appears before `w`. -/
noncomputable def haltR (s : StageFml T) : 𝚺₁.Sentence := .mkSigma
  “∃ w, (!s.η.sigma w ∧ ∀ y < w, ¬!s.η.pi y) ∧ ∀ q < w, ¬!T.proof.pi q !!(⌜(⊥ : Sentence ℒₒᵣ)⌝)”

open InductionOnHierarchy in
omit [Theory.Δ₁ T] [𝗜𝚺₁ ⪯ T] in
/-- **Least-number principle for a stage predicate.** In a model of `IΣ₁`, if the
proper `Δ₁` stage predicate `η` fires at some `w`, then it has a least firing stage. -/
lemma exists_least_stage (s : StageFml T) {M : Type} [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]
    (hproper : s.η.ProperOn M) {w : M}
    (hw : Semiformula.Evalbm M ![w] s.η.pi.val) :
    ∃ y, Semiformula.Evalbm M ![y] s.η.pi.val ∧
      ∀ z < y, ¬ Semiformula.Evalbm M ![z] s.η.pi.val := by
  have hdef : 𝚫-[1].DefinablePred (fun x : M => Semiformula.Evalbm M ![x] s.η.pi.val) := by
    have hdefV : HierarchySymbol.Defined
        (fun v : Fin 1 → M => Semiformula.Evalbm M ![v 0] s.η.val) s.η := by
      refine ⟨hproper, ?_⟩
      intro v
      rw [Matrix.fun_eq_vec_one (v := v)]
      simp
    have h0 := HierarchySymbol.Defined.to_definable s.η hdefV
    refine HierarchySymbol.Definable.of_iff h0 ?_
    intro x; simp [hproper.iff']
  exact least_number_sigma 𝚫 1 hdef hw

/-- `Haltᴿ(η)` implies machine-cutoff consistency (the `←` direction, second part).
If `η` first fires at `w` with no inconsistency proof before `w`, then every
inconsistency proof lies at a stage `≥ w`, where `η` holds by monotonicity. -/
theorem haltR_imp_conBefore (s : StageFml T) :
    T ⊢ (haltR s).val ➝ (conBefore s).val := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  have hmono := by simpa [models_iff] using consequence_iff.mp (sound! s.mono) M inferInstance
  have hproper := s.proper.properOn M
  simp only [models_iff, haltR, conBefore, HierarchySymbol.Semiformula.val_mkSigma,
    HierarchySymbol.Semiformula.val_mkPi]
  simp [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
  intro w hw_sigma _hw_min hq_min p hp
  have hwp : w ≤ p := by
    by_contra h
    exact hq_min p (not_le.mp h) hp
  have hw_pi : (Semiformula.Eval (standardModel M) ![w] Empty.elim) ↑s.η.pi :=
    (hproper.iff ![w]).mp hw_sigma
  have hp_sigma : (Semiformula.Eval (standardModel M) ![p] Empty.elim) ↑s.η.sigma := by
    have := hmono w p (by simpa [Matrix.constant_eq_singleton] using hw_pi) hwp
    simpa [Matrix.constant_eq_singleton] using this
  exact (hproper.iff ![p]).mp hp_sigma

/-- The `→` direction of the normal form. -/
theorem conBefore_imp_consistent_or_haltR (s : StageFml T) :
    T ⊢ (conBefore s).val ➝ (↑T.consistent ⋎ (haltR s).val) := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  have hproper := s.proper.properOn M
  simp only [models_iff, haltR, conBefore, HierarchySymbol.Semiformula.val_mkSigma,
    HierarchySymbol.Semiformula.val_mkPi]
  simp [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
  intro hconBefore
  by_cases hcon : T.Consistent M
  · exact Or.inl hcon
  · refine Or.inr ?_
    -- `¬Con` gives an actual inconsistency proof `p`, at which `η` fires.
    simp only [Theory.Consistent, Theory.Provable, not_not] at hcon
    obtain ⟨p, hp⟩ := hcon
    have hp_pi : (Semiformula.Eval (standardModel M) ![p] Empty.elim) ↑s.η.pi := hconBefore p hp
    obtain ⟨w, hw_pi, hw_min⟩ := exists_least_stage s hproper (w := p) hp_pi
    refine ⟨w, ⟨(hproper.iff ![w]).mpr hw_pi, hw_min⟩, ?_⟩
    intro q hq hpq
    exact hw_min q hq (hconBefore q hpq)

/-- **Normal form (Proposition 6.2 / Target T5).** For every stage formula,
`T ⊢ Con_η(T) ↔ (Con(T) ∨ Haltᴿ(η))`. -/
theorem conBefore_iff_consistent_or_haltR (s : StageFml T) :
    T ⊢ (conBefore s).val ⭤ (↑T.consistent ⋎ (haltR s).val) :=
  E!_intro (conBefore_imp_consistent_or_haltR s)
    (CA!_of_C!_of_C! (consistent_imp_conBefore s) (haltR_imp_conBefore s))

/-! ### Sanity examples (§8.2)

The trivial never-firing stage formula `⊥` recovers ordinary consistency, and the
fire-at-`0` stage formula `⊤` makes machine-consistency outright provable. -/

/-- The never-firing stage formula `η(y) := ⊥`. -/
noncomputable def botEta : 𝚫₁.Semisentence 1 := .mkDelta (.mkSigma “y. ⊥”) (.mkPi “y. ⊥”)

/-- The fire-at-`0` stage formula `η(y) := ⊤`. -/
noncomputable def topEta : 𝚫₁.Semisentence 1 := .mkDelta (.mkSigma “y. ⊤”) (.mkPi “y. ⊤”)

theorem botEta_proper : (botEta).ProvablyProperOn T := by
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  refine HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn T (fun (M : Type) _ _ => ?_)
  intro e; simp [botEta]
theorem botEta_mono : T ⊢ “∀ y z, !(botEta).pi y → y ≤ z → !(botEta).sigma z” := by
  refine provable_of_models T _ (fun (M : Type) _ _ => ?_)
  simp [models_iff, botEta]
theorem topEta_proper : (topEta).ProvablyProperOn T := by
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  refine HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn T (fun (M : Type) _ _ => ?_)
  intro e; simp [topEta]
theorem topEta_mono : T ⊢ “∀ y z, !(topEta).pi y → y ≤ z → !(topEta).sigma z” := by
  refine provable_of_models T _ (fun (M : Type) _ _ => ?_)
  simp [models_iff, topEta]

/-- The never-firing stage formula packaged as a `StageFml`. -/
noncomputable def botStage : StageFml T := ⟨botEta, botEta_proper, botEta_mono⟩

/-- The fire-at-`0` stage formula packaged as a `StageFml`. -/
noncomputable def topStage : StageFml T := ⟨topEta, topEta_proper, topEta_mono⟩

/-- **Sanity example E1.** The never-firing stage formula recovers ordinary
consistency: `T ⊢ Con_⊥(T) ↔ Con(T)`. -/
theorem conBefore_botStage_iff_consistent :
    T ⊢ (conBefore (botStage (T := T))).val ⭤ ↑T.consistent := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  simp [models_iff, conBefore, botStage, botEta, Theory.Consistent, Theory.Provable]

/-- **Sanity example E2.** The fire-at-`0` stage formula makes machine-consistency
outright provable: `T ⊢ Con_⊤(T)`. -/
theorem conBefore_topStage :
    T ⊢ (conBefore (topStage (T := T))).val := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  simp [models_iff, conBefore, topStage, topEta]

end TwoMinds
