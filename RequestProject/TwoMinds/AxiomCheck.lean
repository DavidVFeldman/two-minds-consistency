/-
# Axiom audit

Compiled as part of the build, so the audit is checked rather than scripted.
CI parses the `#print axioms` transcript emitted by this file and fails if any
result depends on `sorryAx` or on any axiom outside the standard footprint
`propext`, `Classical.choice`, `Quot.sound`.
-/
import RequestProject.TwoMinds.Main
import RequestProject.TwoMinds.Necessitation
import RequestProject.TwoMinds.StageFormulaProp64

#print axioms TwoMinds.main
#print axioms TwoMinds.two_minds
#print axioms TwoMinds.no_watched_provable
#print axioms TwoMinds.patternTheory_consistent
#print axioms TwoMinds.reformulation
#print axioms TwoMinds.never_fires
#print axioms TwoMinds.necessitation
#print axioms TwoMinds.provBefore_nat_iff
#print axioms TwoMinds.provBefore_Theta_eval
#print axioms TwoMinds.not_fires_of_standard
#print axioms TwoMinds.conBefore_iff_consistent_or_haltR
#print axioms TwoMinds.haltR_rhoStage_iff
#print axioms TwoMinds.etaRho_proper
#print axioms TwoMinds.etaRho_mono
