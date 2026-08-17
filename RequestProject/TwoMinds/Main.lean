import RequestProject.TwoMinds.Necessitation
import Foundation.FirstOrder.Incompleteness.Examples

/-!
# The Main Theorem (Theorem 4.1 / 1.1) and the two-minds corollary (Corollary 4.2)

Following the accompanying instructions we formalize the paper's model-existence
statements *proof-theoretically*, as consistency statements (§1.2): "there is a
model of `PA + σ`" becomes `Consistent (PA + σ)`.

The self-referential family is the *simultaneous Rosser-style syntactic fixed point*
built in `Construction.lean`; the self-defeat argument is `no_watched_provable`.
-/

namespace TwoMinds

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {n : ℕ}

/-- The theory realizing the verdict pattern `S`:
`T + ¬Con(T) + {Con_{Θi} : i ∈ S} + {¬Con_{Θi} : i ∉ S}`. -/
noncomputable def patternTheory (Θ : Fin n → StageFml T) (S : Finset (Fin n)) : ArithmeticTheory :=
  insert (∼(↑T.consistent : Sentence ℒₒᵣ))
    (Set.range (fun i : S => (conBefore (Θ i.1)).val)
      ∪ Set.range (fun i : {i : Fin n // i ∉ S} => ∼(conBefore (Θ i.1)).val))

/-- Evaluation of a binary conjunction in a model. -/
private lemma models_and' {M : Type} [Nonempty M] [Structure ℒₒᵣ M] (a b : Sentence ℒₒᵣ) :
    M ⊧ₘ (a ⋏ b) ↔ M ⊧ₘ a ∧ M ⊧ₘ b := by simp [models_iff]

/-- Evaluation of a finite conjunction in a model. -/
private lemma models_matrix_conj' {M : Type} [Nonempty M] [Structure ℒₒᵣ M] {K : ℕ}
    (f : Fin K → Sentence ℒₒᵣ) : M ⊧ₘ Matrix.conj f ↔ ∀ i, M ⊧ₘ (f i) := by
  induction K with
  | zero => simp [Matrix.conj, models_iff]
  | succ k ih =>
    rw [show Matrix.conj f = f 0 ⋏ Matrix.conj (Matrix.vecTail f) from rfl, models_and']
    constructor
    · rintro ⟨h0, ht⟩ i
      exact Fin.cases h0 (fun j => (ih (Matrix.vecTail f)).mp ht j) i
    · intro h
      exact ⟨h 0, (ih _).mpr (fun j => h j.succ)⟩

omit [𝗜𝚺₁ ⪯ T] in
/-- **Bridge lemma.** If `T` does not refute the pattern conjunction, then the pattern
theory is consistent.  We argue semantically: from `T ⊬ ∼patConjG`, adjoining `patConjG`
to `T` is consistent, so it has a model `M`; that model satisfies every member of
`patternTheory` (each is a conjunct of `patConjG`), hence `T + patternTheory` is
satisfiable and therefore consistent. -/
theorem patternTheory_consistent (Θ : Fin n → StageFml T) (S : Finset (Fin n))
    (h : T ⊬ ∼(patConjG T Θ S)) :
    Entailment.Consistent ((T : ArithmeticTheory) + patternTheory Θ S) := by
  have hcon : Entailment.Consistent (insert (patConjG T Θ S) (T : ArithmeticTheory)) := by
    rw [Entailment.consistent_iff_unprovable_bot]
    intro hbot
    exact h (Entailment.N!_iff_CO!.mpr (deduction! hbot))
  obtain ⟨M, hMne, hMstr, hMmodel⟩ := satisfiable_iff.mp (satisfiable_of_consistent hcon)
  have hMT : M ⊧ₘ* (T : ArithmeticTheory) :=
    modelsTheory_iff.mpr (fun {φ} hφ => modelsTheory_iff.mp hMmodel (Set.mem_insert_of_mem _ hφ))
  have hMpat : M ⊧ₘ (patConjG T Θ S) := modelsTheory_iff.mp hMmodel (Set.mem_insert _ _)
  rw [patConjG, models_and', models_and'] at hMpat
  obtain ⟨h1, hA, hB⟩ := hMpat
  refine consistent_of_satisfiable (satisfiable_intro M ?_)
  rw [ModelsTheory.add_iff]
  refine ⟨hMT, modelsTheory_iff.mpr ?_⟩
  intro φ hφ
  rcases Set.mem_insert_iff.mp hφ with rfl | hφ
  · exact h1
  · rcases hφ with ⟨⟨i, hi⟩, rfl⟩ | ⟨⟨i, hi⟩, rfl⟩
    · simpa [hi] using (models_matrix_conj' _).mp hA i
    · simpa [hi] using (models_matrix_conj' _).mp hB i

/-- **Main Theorem (Theorem 4.1).** Assume `T` is consistent and let `n` be given.
There is a family of stage formulas `Θ`, none of which ever fires in the standard
model, such that:

* (1) each `Prov_{Θi}` is a `T`-provable subpredicate of the standard predicate,
  so `T ⊢ Con(T) → Con_{Θi}(T)`;
* (2) for **every** verdict pattern `S ⊆ {1,…,n}`, the theory
  `T + ¬Con(T) + {Con_{Θi} : i ∈ S} + {¬Con_{Θi} : i ∉ S}` is consistent;
* (3) each `Prov_{Θi}` satisfies necessitation (`T ⊢ φ` implies `T ⊢ Prov_{Θi}(⌜φ⌝)`)
  and is extensionally correct: over `ℕ` it defines real `T`-provability.

These are the "only" implications: consistency verdicts can land in any pattern not
outright provably impossible. -/
theorem main [Consistent T] (n : ℕ) :
    ∃ Θ : Fin n → StageFml T,
      (∀ (i : Fin n) (y : ℕ), ¬ Semiformula.Evalbm ℕ ![(y : ℕ)] (Θ i).η.val)
    ∧ (∀ i : Fin n, T ⊢ ↑T.consistent ➝ (conBefore (Θ i)).val)
    ∧ (∀ S : Finset (Fin n), Entailment.Consistent ((T : ArithmeticTheory) + patternTheory Θ S))
    ∧ (∀ (i : Fin n) (φ : Sentence ℒₒᵣ), T ⊢ φ →
        T ⊢ (provBefore (Θ i)).val/[⌜φ⌝])
    ∧ (∀ (i : Fin n) (φ : Sentence ℒₒᵣ),
        Semiformula.Evalbm ℕ ![] ((provBefore (Θ i)).val/[⌜φ⌝]) ↔ T ⊢ φ) := by
  refine ⟨Theta T (2 ^ n) (patEquiv n), ?_, ?_, ?_, ?_, ?_⟩
  · intro i y
    exact never_fires T (2 ^ n) (patEquiv n) i y
  · intro i
    exact consistent_imp_conBefore (Theta T (2 ^ n) (patEquiv n) i)
  · intro S
    apply patternTheory_consistent
    -- `T ⊬ ∼(patConjG T (Theta ...) S)`, using reformulation + self-defeat.
    intro hpat
    have hre : T ⊢ (sigmaC T (2 ^ n) (patEquiv n) S) ⭤ (patConjG T (Theta T (2 ^ n) (patEquiv n)) S) :=
      reformulation T (2 ^ n) (patEquiv n) S
    -- from `T ⊢ ∼patConj` and the equivalence, get `T ⊢ ∼sigmaC`.
    have hns : T ⊢ ∼(sigmaC T (2 ^ n) (patEquiv n) S) :=
      Entailment.K!_right (Entailment.ENN!_of_E! hre) ⨀ hpat
    exact no_watched_provable T (2 ^ n) (patEquiv n) S
      ⟨(patEquiv n).symm S, (patEquiv n).apply_symm_apply S⟩ hns
  · intro i φ h
    exact necessitation T (2 ^ n) (patEquiv n) i h
  · intro i φ
    exact provBefore_nat_iff T (2 ^ n) (patEquiv n) i φ

/-- **Corollary 4.2 (a model of two minds).** There are two machine-consistency
predicates `Con_{s₀}`, `Con_{s₁}` which are

* *extensionally correct*: neither stage formula ever fires in the standard model
  (so, by `conBefore_nat_iff`-style reasoning, each `Con_{sᵢ}` is true exactly when
  `T` is consistent);
* *`T`-provably sound*: `T ⊢ Con(T) → Con_{sᵢ}(T)`;

together with a consistent theory (hence, via completeness, a single model of `T`)
which denies `Con(T)` yet affirms the first machine-consistency statement while
refuting the second. -/
theorem two_minds [Consistent T] :
    ∃ s₀ s₁ : StageFml T,
      (∀ y : ℕ, ¬ Semiformula.Evalbm ℕ ![(y : ℕ)] s₀.η.val)
    ∧ (∀ y : ℕ, ¬ Semiformula.Evalbm ℕ ![(y : ℕ)] s₁.η.val)
    ∧ (T ⊢ ↑T.consistent ➝ (conBefore s₀).val)
    ∧ (T ⊢ ↑T.consistent ➝ (conBefore s₁).val)
    ∧ Entailment.Consistent
        ((T : ArithmeticTheory) +
          ({∼(↑T.consistent : Sentence ℒₒᵣ), (conBefore s₀).val, ∼(conBefore s₁).val} :
            Set (Sentence ℒₒᵣ))) := by
  obtain ⟨Θ, h1, h2, hcons, -, -⟩ := main (T := T) 2
  refine ⟨Θ 0, Θ 1, h1 0, h1 1, h2 0, h2 1, ?_⟩
  refine Entailment.Consistent.of_subset (hcons {0}) ?_
  show (T ∪ _ : Set (Sentence ℒₒᵣ)) ⊆ T ∪ patternTheory Θ {0}
  refine Set.union_subset_union_right _ ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ (Set.mem_union_left _ ?_)
    exact ⟨⟨0, by decide⟩, rfl⟩
  · refine Set.mem_insert_of_mem _ (Set.mem_union_right _ ?_)
    exact ⟨⟨1, by decide⟩, rfl⟩

/-- The extensional-correctness clauses of `two_minds` are doing work: the cheap
`topStage`/`botStage` pair, which satisfies the consistency clause alone, is excluded,
because `topStage` fires already at stage `0`. -/
example : ¬ (∀ y : ℕ, ¬ Semiformula.Evalbm ℕ ![(y : ℕ)] (topStage (T := T)).η.val) :=
  fun h => h 0 (by simp [topStage, topEta])

/-! ### Acceptance test (validation memo A.3.4)

The paper's own instance `T := 𝗣𝗔` elaborates: PA's `Δ₁`, `𝗜𝚺₁ ⪯ 𝗣𝗔` and
`Consistent 𝗣𝗔` instances are all found, so the Main Theorem applies to `𝗣𝗔`. -/
example (n : ℕ) :
    ∃ Θ : Fin n → StageFml 𝗣𝗔,
      (∀ (i : Fin n) (y : ℕ), ¬ Semiformula.Evalbm ℕ ![(y : ℕ)] (Θ i).η.val)
    ∧ (∀ i : Fin n, 𝗣𝗔 ⊢ ↑(𝗣𝗔 : ArithmeticTheory).consistent ➝ (conBefore (Θ i)).val)
    ∧ (∀ S : Finset (Fin n),
        Entailment.Consistent ((𝗣𝗔 : ArithmeticTheory) + patternTheory Θ S))
    ∧ (∀ (i : Fin n) (φ : Sentence ℒₒᵣ), 𝗣𝗔 ⊢ φ →
        𝗣𝗔 ⊢ (provBefore (Θ i)).val/[⌜φ⌝])
    ∧ (∀ (i : Fin n) (φ : Sentence ℒₒᵣ),
        Semiformula.Evalbm ℕ ![] ((provBefore (Θ i)).val/[⌜φ⌝]) ↔ 𝗣𝗔 ⊢ φ) :=
  main (T := 𝗣𝗔) n

end TwoMinds
