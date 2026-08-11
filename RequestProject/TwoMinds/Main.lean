import RequestProject.TwoMinds.Construction

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
  `T + ¬Con(T) + {Con_{Θi} : i ∈ S} + {¬Con_{Θi} : i ∉ S}` is consistent.

These are the "only" implications: consistency verdicts can land in any pattern not
outright provably impossible. -/
theorem main [Consistent T] (n : ℕ) :
    ∃ Θ : Fin n → StageFml T,
      (∀ (i : Fin n) (y : ℕ), ¬ Semiformula.Evalbm ℕ ![(y : ℕ)] (Θ i).η.val)
    ∧ (∀ i : Fin n, T ⊢ ↑T.consistent ➝ (conBefore (Θ i)).val)
    ∧ (∀ S : Finset (Fin n), Entailment.Consistent ((T : ArithmeticTheory) + patternTheory Θ S)) := by
  refine ⟨Theta T (2 ^ n) (patEquiv n), ?_, ?_, ?_⟩
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

/-- **Corollary 4.2 (a model of two minds).** There are two extensionally correct,
`T`-provably sound machine-consistency predicates and a consistent theory (hence,
via completeness, a single model of `T`) which affirms the first while refuting the
second. -/
theorem two_minds [Consistent T] :
    ∃ s₀ s₁ : StageFml T,
      Entailment.Consistent
        ((T : ArithmeticTheory) +
          ({∼(↑T.consistent : Sentence ℒₒᵣ), (conBefore s₀).val, ∼(conBefore s₁).val} :
            Set (Sentence ℒₒᵣ))) := by
  obtain ⟨Θ, _h1, _h2, hcons⟩ := main (T := T) 2
  refine ⟨Θ 0, Θ 1, ?_⟩
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

end TwoMinds
