import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsGuaranteedRoundRobinEf1Factor

/-!
# round_robin_alpha

Topic: fair_division   Node: 183af22b14b1

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 6

The best guaranteed EF1 factor α_RR(n) for n agents under Round-Robin is the supremum of factors α that are guaranteed for n agents under Round-Robin.
-/

/-- The best guaranteed EF1 factor α_RR(n) for n agents under Round-Robin, defined as the supremum of guaranteed factors α. -/
noncomputable def round_robin_alpha (n : ℕ) [NeZero n] : ℝ :=
  sSup {α : ℝ | is_guaranteed_round_robin_ef1_factor n α}
