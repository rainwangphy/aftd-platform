import AFTD.Prelude
import AFTD.Kb.Optimization.IsConvexPolygonSlackMatrix

/-!
# is_convex_polygon_slack_matrix_nonneg

Topic: integer_programming   Node: 6e65d6df5b7f

Provenance: helper lemma. arXiv:2610.04498 Sec. 2

For any natural number n and any real matrix S : Matrix (Fin n) (Fin n) ℝ, if is_convex_polygon_slack_matrix n S holds, then for all indices i and j in Fin n, 0 ≤ S i j.
-/

/-- Every entry of the slack matrix of a convex polygon in the plane is nonnegative. -/
theorem is_convex_polygon_slack_matrix_nonneg {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : is_convex_polygon_slack_matrix n S) (i j : Fin n) : 0 ≤ S i j := by
  obtain ⟨-, v, ℓ, hv, hext, haff, hconv, hzero, hSij⟩ := hS
  rw [hSij i j]
  have hvj : v j ∈ Set.range v := Set.mem_range_self j
  have hmem : v j ∈ convexHull ℝ (Set.range v) := subset_convexHull ℝ _ hvj
  rw [hconv] at hmem
  exact hmem i
