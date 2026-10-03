import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsNonWinnerTakeAllProfile
import AFTD.Kb.GameTheoryEconomics.IsProcurementPne
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.StakeSharePneExists
import AFTD.Kb.GameTheoryEconomics.StakeSharePneNonWinnerTakeAll
import AFTD.Kb.GameTheoryEconomics.StakeSharePool

/-!
# stake_share_pne_exists_and_non_winner_take_all

Topic: mechanism_design   Node: 6ee3561a3f7c

For n >= 2 agents with costs in [0, L] and K M >= 3 n^2 L, the stake-share mechanism has a pure Nash equilibrium, and every pure Nash equilibrium gives positive work to at least two agents.
-/

/-- For every number of agents and every floor `L`, the stake-share mechanism with `K M ≥ 3 n² L` has, for every cost profile in `[0, L]`, a pure Nash equilibrium, and every pure Nash equilibrium gives positive work to at least two agents. -/
theorem stake_share_pne_exists_and_non_winner_take_all {n : ℕ} (hn : 2 ≤ n) {L K M : ℝ}
    (hL : 0 ≤ L) (hK : 0 < K) (hM : 0 < M) (hKM : 3 * (n : ℝ) ^ 2 * L ≤ K * M)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) :
    (∃ β : Fin n → List ℝ, is_procurement_pne proportional_share_alloc
      (proportional_share_pay (stake_share_pool L K M)) c β) ∧
    ∀ β : Fin n → List ℝ, is_procurement_pne proportional_share_alloc
      (proportional_share_pay (stake_share_pool L K M)) c β →
      is_non_winner_take_all_profile proportional_share_alloc β :=
  ⟨stake_share_pne_exists hn hL hK hM hKM c hc, fun β hβ =>
    stake_share_pne_non_winner_take_all hK hM (by omega) c (fun i => (hc i).2) β hβ⟩
