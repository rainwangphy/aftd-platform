import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionTradeError
import AFTD.Kb.GameTheoryEconomics.RedistributionShortfall
import AFTD.Kb.GameTheoryEconomics.RedistributionTrade

/-!
# redistribution_trade_error_one

Topic: mechanism_design   Node: c8c0ecc7924c

Provenance: helper lemma. arXiv:2610.10995 Definition 4.1

For every natural number n, report profile θ : Fin n → ℝ, and real number t, the first-order trade error redistribution_trade_error θ 1 t equals redistribution_shortfall t - redistribution_trade θ redistribution_shortfall t.
-/

/-- First-order trade error definition unrolling. -/
theorem redistribution_trade_error_one {n : ℕ} (θ : Fin n → ℝ) (t : ℝ) :
    redistribution_trade_error θ 1 t =
      redistribution_shortfall t - redistribution_trade θ redistribution_shortfall t := by
  simp [redistribution_trade_error]
