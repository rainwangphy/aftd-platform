import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceAlpha
import AFTD.Kb.GameTheoryEconomics.IsRoundRobinSequence

/-!
# round_robin_universal_alpha

Topic: fair_division   Node: f3fc30c5fff4

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 6

The universal EF1 approximation factor α_RR for Round-Robin picking sequences is the infimum over all Round-Robin sequences with at least two agents of their guaranteed EF1 factor picking_sequence_alpha.
-/

/-- The universal EF1 approximation factor α_RR for all Round-Robin picking sequence instances with at least two agents. -/
noncomputable def round_robin_universal_alpha : ℝ :=
  sInf {y : ℝ | ∃ (n : ℕ) (seq : List (Fin n)),
    is_round_robin_sequence n seq ∧ 2 ≤ n ∧ y = picking_sequence_alpha n seq}
