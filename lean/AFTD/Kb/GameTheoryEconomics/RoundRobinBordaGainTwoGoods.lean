import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinUBest
import AFTD.Kb.GameTheoryEconomics.RoundRobinUTruth

/-!
# round_robin_borda_gain_two_goods

Topic: fair_division   Node: b209439f4f78

Provenance: helper lemma. OP-1439

For m = 2 goods, agent A's best-response Borda utility equals her truthful utility for every pair of rankings (U_best = U_truth).
-/

/-- For m = 2 goods, agent A cannot gain by manipulation in the alternating draft. -/
theorem round_robin_borda_gain_two_goods (rA rB : Fin 2 ≃ Fin 2) :
    round_robin_u_best 2 rA rB = round_robin_u_truth 2 rA rB := by
  revert rA rB
  decide
