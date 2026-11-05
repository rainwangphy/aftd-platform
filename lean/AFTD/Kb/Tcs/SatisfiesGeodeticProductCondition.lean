import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# satisfies_geodetic_product_condition

Topic: graphs   Node: 7d41a1f698fa

Provenance: formalization of a published result. Source: arXiv:2611.05762, Eq. (1) & Problem 9.2.1

A sequence c : Fin d → ℕ satisfies the geodesic product condition for bound K if for every index i : Fin d, the product of c(j) over all j ≤ i is at most K.
-/

/-- The geodesic product condition: for each distance index i, the product of c_j for j ≤ i is at most K. -/
def satisfies_geodetic_product_condition (d : ℕ) (c : Fin d → ℕ) (K : ℕ) : Prop := ∀ (i : Fin d), ∏ j ∈ Finset.Iic i, c j ≤ K
