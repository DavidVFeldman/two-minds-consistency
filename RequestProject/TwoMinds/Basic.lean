import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.RestrictedProvability

/-!
# Two minds about consistency — Foundation setup

Reconnaissance / base setup file. We work with an arithmetic theory `T`
extending `IΣ₁`, with a `Δ₁` axiomatization, so that Foundation's standard
provability predicate, diagonal lemma, and Gödel's second incompleteness
theorem are all available.
-/

namespace TwoMinds

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- Gödel's second incompleteness theorem, external form (wrapper around Foundation). -/
theorem godel_two [Consistent T] : T ⊬ ↑T.consistent :=
  consistent_unprovable T

end TwoMinds
