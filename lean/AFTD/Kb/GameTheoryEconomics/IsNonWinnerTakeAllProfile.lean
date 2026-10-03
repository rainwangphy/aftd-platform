import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentAllocation
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBids

/-!
# is_non_winner_take_all_profile

Topic: mechanism_design   Node: f1467b96444b

A bid profile is not winner-take-all if at least two distinct agents receive a positive amount of work.
-/

def is_non_winner_take_all_profile (alloc : List ℝ → ℕ → ℝ) {n : ℕ}
    (β : Fin n → List ℝ) : Prop :=
  ∃ i j, i ≠ j ∧ 0 < procurement_agent_allocation alloc (β i) (procurement_others_bids β i) ∧
    0 < procurement_agent_allocation alloc (β j) (procurement_others_bids β j)
