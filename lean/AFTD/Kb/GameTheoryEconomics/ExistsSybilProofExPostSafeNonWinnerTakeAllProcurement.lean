import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsExPostSafeProcurementFor
import AFTD.Kb.GameTheoryEconomics.IsNonWinnerTakeAllProfile
import AFTD.Kb.GameTheoryEconomics.IsProcurementPne
import AFTD.Kb.GameTheoryEconomics.IsSybilProofProcurement
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.ProportionalShareSybilProof
import AFTD.Kb.GameTheoryEconomics.StakeShareExPostSafe
import AFTD.Kb.GameTheoryEconomics.StakeSharePneNonWinnerTakeAll
import AFTD.Kb.GameTheoryEconomics.StakeSharePool
import AFTD.Kb.GameTheoryEconomics.StakeShareTwoAgentPne

/-!
# exists_sybil_proof_ex_post_safe_non_winner_take_all_procurement

Topic: mechanism_design   Node: 6dd5f67d4fa5

There is a procurement mechanism that is Sybil-proof, ex-post safe for all costs at most 1, whose pure Nash equilibria (for costs at most 1) are never winner-take-all, and which has such an equilibrium (costs 1/5 and 9/10).
-/

/-- Answer to the open question of arXiv:2603.27779 (Sec. 6): a procurement mechanism that is Sybil-proof, ex-post safe for every cost up to the floor `1`, whose pure Nash equilibria are never winner-take-all, and which has such an equilibrium. -/
theorem exists_sybil_proof_ex_post_safe_non_winner_take_all_procurement :
    ∃ alloc pay : List ℝ → ℕ → ℝ,
      is_sybil_proof_procurement alloc pay ∧
      (∀ c, c ≤ 1 → is_ex_post_safe_procurement_for alloc pay c) ∧
      (∀ n, 0 < n → ∀ (c : Fin n → ℝ), (∀ i, c i ≤ 1) → ∀ β,
        is_procurement_pne alloc pay c β → is_non_winner_take_all_profile alloc β) ∧
      is_procurement_pne alloc pay ![1/5, 9/10] ![[24/35], [18/35]] :=
  ⟨proportional_share_alloc, proportional_share_pay (stake_share_pool 1 1 2),
    proportional_share_sybil_proof _,
    fun _ hc => stake_share_ex_post_safe one_pos two_pos hc,
    fun _ hn c hc β hβ => stake_share_pne_non_winner_take_all one_pos two_pos hn c hc β hβ,
    stake_share_two_agent_pne⟩
