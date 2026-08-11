import RequestProject.TwoMinds.StageFormula

/-!
# Proposition 6.4, stage-formula form (mini round 3, optional item 3)

Working directly with monotone `Δ₁` stage formulas rather than machines (validation
memo E3), the pacing artifact of the paper's Proposition 6.4 disappears: for a `Δ₁`
witness predicate `δ`, the "paced" stage formula is simply

  `η_ρ(y) := ∃ x ≤ y, δ(x)`,

whose first firing stage *is* the least `δ`-witness (the truncation `c = id`).  Its
Rosser-`Haltᴿ` reduct is therefore the natural Rosser sentence `ρ^R`

  `ρ^R := ∃ w, (δ(w) ∧ ∀ x < w, ¬δ(x)) ∧ ∀ q < w, ¬ Pf(q, ⌜⊥⌝)`

("the least `δ`-witness precedes the least inconsistency proof").  We prove

  `T ⊢ Haltᴿ(η_ρ) ⭤ ρ^R`.
-/

namespace TwoMinds

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- The `Σ`-presentation of the paced stage formula `η_ρ(y) := ∃ x ≤ y, δ(x)`. -/
noncomputable def etaRhoSig (d : 𝚫₁.Semisentence 1) : 𝚺₁.Semisentence 1 :=
  .mkSigma “y. ∃ x <⁺ y, !d.sigma x”

/-- The `Π`-presentation of the paced stage formula `η_ρ(y) := ∃ x ≤ y, δ(x)`.
Bounded existential quantification preserves the `Π₁` level. -/
noncomputable def etaRhoPi (d : 𝚫₁.Semisentence 1) : 𝚷₁.Semisentence 1 :=
  .mkPi “y. ∃ x <⁺ y, !d.pi x”

/-- The paced stage formula `η_ρ`. -/
noncomputable def etaRho (d : 𝚫₁.Semisentence 1) : 𝚫₁.Semisentence 1 :=
  .mkDelta (etaRhoSig d) (etaRhoPi d)

/-- **Evaluation of the `Σ`-presentation of `η_ρ`.** -/
theorem etaRho_sigma_eval (d : 𝚫₁.Semisentence 1)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (y : M) :
    Semiformula.Evalbm M ![y] (etaRho d).sigma.val ↔
      ∃ x ≤ y, Semiformula.Evalbm M ![x] d.sigma.val := by
  simp only [etaRho, etaRhoSig, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  simp [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    Matrix.vecHead, Matrix.vecTail]

/-- **Evaluation of the `Π`-presentation of `η_ρ`.** -/
theorem etaRho_pi_eval (d : 𝚫₁.Semisentence 1)
    (M : Type) [ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁] (y : M) :
    Semiformula.Evalbm M ![y] (etaRho d).pi.val ↔
      ∃ x ≤ y, Semiformula.Evalbm M ![x] d.pi.val := by
  simp only [etaRho, etaRhoPi, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  simp [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    Matrix.vecHead, Matrix.vecTail]

/-- `η_ρ` is provably proper. -/
theorem etaRho_proper (d : 𝚫₁.Semisentence 1) (hd : d.ProvablyProperOn T) :
    (etaRho d).ProvablyProperOn T := by
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  apply HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn
  intro M _ hMT
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  have hproper := hd.properOn M
  intro e
  rw [Matrix.fun_eq_vec_one (v := e), etaRho_sigma_eval, etaRho_pi_eval]
  exact exists_congr (fun x => and_congr_right (fun _ => hproper.iff ![x]))

/-- `η_ρ` is provably monotone. -/
theorem etaRho_mono (d : 𝚫₁.Semisentence 1) (hd : d.ProvablyProperOn T) :
    T ⊢ “∀ y z, !(etaRho d).pi y → y ≤ z → !(etaRho d).sigma z” := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  have hproper := hd.properOn M
  have key : ∀ y z : M, (∃ x ≤ y, Semiformula.Evalbm M ![x] d.pi.val) → y ≤ z →
      (∃ x ≤ z, Semiformula.Evalbm M ![x] d.sigma.val) := by
    rintro y z ⟨x, hxy, hx⟩ hyz
    exact ⟨x, le_trans hxy hyz, (hproper.iff ![x]).mpr hx⟩
  simp only [models_iff, Semiformula.eval_all]
  intro y z
  simpa [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    Semiterm.val_bShift, etaRho_pi_eval, etaRho_sigma_eval] using key y z

/-- The paced stage formula packaged as a `StageFml`. -/
noncomputable def rhoStage (d : 𝚫₁.Semisentence 1) (hd : d.ProvablyProperOn T) : StageFml T :=
  ⟨etaRho d, etaRho_proper d hd, etaRho_mono d hd⟩

/-- The Rosser truncation `ρ^R`: the least `δ`-witness precedes the least
inconsistency proof. -/
noncomputable def rhoR (d : 𝚫₁.Semisentence 1) : 𝚺₁.Sentence :=
  .mkSigma “∃ w, (!d.sigma w ∧ ∀ x < w, ¬!d.pi x) ∧
      ∀ q < w, ¬!T.proof.pi q !!(⌜(⊥ : Sentence ℒₒᵣ)⌝)”

/-- **Proposition 6.4 (stage-formula form).** `Haltᴿ(η_ρ)` is `T`-provably equivalent
to the Rosser sentence `ρ^R`: the pacing truncation lands at the identity, so the
first firing stage of `η_ρ` is exactly the least `δ`-witness. -/
theorem haltR_rhoStage_iff (d : 𝚫₁.Semisentence 1) (hd : d.ProvablyProperOn T) :
    T ⊢ (haltR (rhoStage d hd)).val ⭤ (rhoR (T := T) d).val := by
  refine provable_of_models T _ (fun (M : Type) _ hMT => ?_)
  haveI : M ⊧ₘ* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ T hMT
  have hproper := hd.properOn M
  simp only [models_iff, haltR, rhoR, HierarchySymbol.Semiformula.val_mkSigma]
  simp [Semiformula.eval_substs, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    rhoStage, etaRho_sigma_eval, etaRho_pi_eval]
  constructor
  · rintro ⟨w, ⟨⟨x0, hx0w, hSx0⟩, hmin⟩, hq⟩
    have hx0eq : x0 = w := by
      rcases lt_or_eq_of_le hx0w with h | h
      · exact absurd ((hproper.iff ![x0]).mp hSx0) (hmin x0 h x0 (le_refl x0))
      · exact h
    subst hx0eq
    exact ⟨x0, ⟨hSx0, fun x hx => hmin x hx x (le_refl x)⟩, hq⟩
  · rintro ⟨w, ⟨hSw, hlt⟩, hq⟩
    exact ⟨w, ⟨⟨w, le_refl w, hSw⟩, fun y hy x hxy => hlt x (lt_of_le_of_lt hxy hy)⟩, hq⟩

end TwoMinds
