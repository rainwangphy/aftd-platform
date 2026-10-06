import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSybilProofProcurement
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.ProportionalShareUtilityEq

/-!
# proportional_share_sybil_proof

Topic: mechanism_design   Node: 533918d5ba76

Provenance: helper lemma. step towards exists_sybil_proof_ex_post_safe_non_winner_take_all_procurement (Sybil-proof, ex-post safe procurement with non-winner-take-all equilibria, the open question of arXiv:2603.27779 v1, Sec. 6); the single-bid argument is that of arXiv:2603.27779 v1, Lemma 2 (Tullock procurement contest is Sybil-proof), here for any pool depending on the total stake

Every proportional-share mechanism is Sybil-proof: a single bid equal to the sum of an agent's bids gives the same utility.
-/

theorem proportional_share_sybil_proof (pool : ℝ → ℝ) :
    is_sybil_proof_procurement proportional_share_alloc (proportional_share_pay pool) := by
  intro c _ mine hmine
  refine ⟨mine.sum, List.sum_nonneg hmine, fun others _ => ?_⟩
  rw [proportional_share_utility_eq, proportional_share_utility_eq, List.sum_singleton]
