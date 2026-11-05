import AFTD.Prelude

/-!
# satisfies_geodetic_c_condition

Topic: graphs   Node: c99cf7bf49fc

Provenance: formalization of a published result. Source: arXiv:2611.05762, Sec. 4.2 & Sec. 4.3

A sequence c : Fin d → ℕ satisfies the arithmetic geodetic condition for bound K if c(i) = 1 for all i with i.val + 1 < d, and c(i) ≤ K for the final index i with i.val + 1 = d.
-/

/-- The arithmetic c-condition for K-geodeticity: c_j = 1 for all j < d-1 and c_{d-1} ≤ K. -/
def satisfies_geodetic_c_condition (d : ℕ) (c : Fin d → ℕ) (K : ℕ) : Prop := (∀ (i : Fin d), i.val + 1 < d → c i = 1) ∧ (∀ (i : Fin d), i.val + 1 = d → c i ≤ K)
