import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# utilitarian_welfare

Topic: fair_division   Node: e280b381f92e

Provenance: formalization of a published result. Source: The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Sec. 2 (Nash welfare / utilitarian social welfare of an allocation, additive valuations)

Utilitarian social welfare of an allocation σ with additive valuations v_i: SW(σ) = ∑_i v_i(X_i), where X_i is the bundle of agent i under σ.
-/

/-- The utilitarian (social) welfare of the allocation `σ` under additive valuations `v`: the sum of the agents' values for their bundles. -/
def utilitarian_welfare {m n : ℕ} (v : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : ℝ :=
  ∑ i, additive_valuation (v i) (bundle_of σ i)
