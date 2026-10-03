import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSybilProofProcurement
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.ProportionalShareUtilityEq

/-!
# proportional_share_sybil_proof

Topic: mechanism_design   Node: 533918d5ba76

Every proportional-share mechanism is Sybil-proof: a single bid equal to the sum of an agent's bids gives the same utility.
-/

theorem proportional_share_sybil_proof (pool : ℝ → ℝ) :
    is_sybil_proof_procurement proportional_share_alloc (proportional_share_pay pool) := by
  intro c _ mine hmine
  refine ⟨mine.sum, List.sum_nonneg hmine, fun others _ => ?_⟩
  rw [proportional_share_utility_eq, proportional_share_utility_eq, List.sum_singleton]
