import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# goods_utility

Topic: fair_division   Node: 1d739397124e

The utility vector of an allocation of goods under additive valuations: agent i's value for her own bundle.
-/

/-- Utility vector of the allocation `σ` (good `x` goes to agent `σ x`) under additive values `u`. -/
def goods_utility {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Fin n → ℝ :=
  fun i => additive_valuation (u i) (bundle_of σ i)
