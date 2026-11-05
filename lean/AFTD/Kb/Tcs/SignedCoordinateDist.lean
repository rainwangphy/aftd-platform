import AFTD.Prelude

/-!
# signed_coordinate_dist

Topic: information   Node: 6c55db47544d

Provenance: formalization of a published result. Source: arXiv:2611.00868, Section 2, Eq. (10)

The dictator distance delta(f) of a function f on the Boolean cube is the minimum normalized Hamming distance from f to any signed coordinate indicator x ↦ if x i = b then 1 else 0.
-/

open scoped BigOperators in
/-- Minimum normalized Hamming distance from f to any signed coordinate indicator. -/
noncomputable def signed_coordinate_dist (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ := ⨅ (i : Fin n) (b : Bool),
    (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, if f x ≠ (if x i = b then 1 else 0) then 1 else 0
