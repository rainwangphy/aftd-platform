import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# social_cost

Topic: fair_division   Node: 760fe42338e1

The social cost of an allocation: the sum over agents of their cost for their own bundle.
-/

/-- Social cost of an allocation (arXiv:2410.15738, Sec. 2): `SC(A) = ∑ i, c i (A i)`. -/
def social_cost {m n : ℕ} (c : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : ℝ :=
  ∑ i, additive_valuation (c i) (bundle_of σ i)
