import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionTradeError
import AFTD.Kb.GameTheoryEconomics.RedistributionTrade
import AFTD.Kb.GameTheoryEconomics.RedistributionShortfall

/-!
# redistribution_trade_error_succ

Topic: mechanism_design   Node: fce41be8c098

Provenance: helper lemma. arXiv:2610.10995 Definition 4.1

For every natural number n, profile θ : Fin n → ℝ, natural number m, and real number t, the (m + 1)-th order trade residual error at t equals redistribution_trade_error θ m t - redistribution_trade θ (redistribution_trade_error θ m) t.
-/

/-- Recursive update rule for iterated trade error functions. -/
theorem redistribution_trade_error_succ {n : ℕ} (θ : Fin n → ℝ) (m : ℕ) (t : ℝ) :
    redistribution_trade_error θ (m + 1) t =
      redistribution_trade_error θ m t -
        redistribution_trade θ (redistribution_trade_error θ m) t := by
  unfold redistribution_trade_error
  rw [Function.iterate_succ_apply']
