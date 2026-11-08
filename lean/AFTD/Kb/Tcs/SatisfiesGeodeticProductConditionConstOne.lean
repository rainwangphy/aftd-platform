import AFTD.Prelude
import AFTD.Kb.Tcs.SatisfiesGeodeticProductCondition
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# satisfies_geodetic_product_condition_const_one

Topic: graphs   Node: c32ad5ab92c4

Provenance: helper lemma. arXiv:2611.05762, Sec. 4.1

For any diameter d and any bound K ≥ 1, the constant sequence c = 1 satisfies the geodesic product condition for K.
-/

/-- The constant 1 sequence satisfies the geodesic product condition for any K ≥ 1. -/
theorem satisfies_geodetic_product_condition_const_one (d : ℕ) (K : ℕ) (hK : 1 ≤ K) :
    satisfies_geodetic_product_condition d (fun _ => 1) K := by
  intro i
  simpa using hK
