import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionTrade
import AFTD.Kb.GameTheoryEconomics.RedistributionShortfall

/-!
# redistribution_trade_error

Topic: mechanism_design   Node: 2a427d323c84

Provenance: formalization of a published result. Source: scout/2610-10995-asymptotically-optimal-public-project-redistribution-withou.md:609

The m-th order error function E_m = (I - T)^m G after m rounds of trade error correction on the shortfall function G(t) = max(1 - t, 0).
-/

/-- The m-th order error function E_m = (I - T)^m G for the iterated trade operator T on the shortfall function G. -/
noncomputable def redistribution_trade_error {n : ℕ} (θ : Fin n → ℝ) (m : ℕ) : ℝ → ℝ := (fun (f : ℝ → ℝ) (t : ℝ) => f t - redistribution_trade θ f t)^[m] redistribution_shortfall
