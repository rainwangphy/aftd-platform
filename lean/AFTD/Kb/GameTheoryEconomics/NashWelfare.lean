import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# nash_welfare

Topic: fair_division   Node: 57b6289d1d2d

Nash welfare of an allocation σ of m goods to n agents with additive valuations v_i: NW(σ) = ∏_i v_i(X_i), where X_i is the bundle of agent i under σ.
-/

/-- The Nash welfare of the allocation `σ` under additive valuations `v`: the product of the agents' values for their bundles. -/
def nash_welfare {m n : ℕ} (v : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : ℝ :=
  ∏ i, additive_valuation (v i) (bundle_of σ i)
