import AFTD.Prelude
import AFTD.Kb.Tcs.IsReflexivePolytope

/-!
# is_reflexive_simplex

Topic: combinatorics   Node: 56c50c149906

Provenance: formalization of a published result. Source: scout/2611-08819-reflexive-polytopes-can-have-doubly-exponentially-many-vert.md:206

An m-dimensional reflexive simplex S in ℝ^m with affinely independent vertices v_0, ..., v_m in ℝ^m and associated unit partition with denominators k_0, ..., k_m positive integers is a reflexive polytope equal to the convex hull of {v_0, ..., v_m} such that ∑_{i=0}^m 1/k_i = 1 and ∑_{i=0}^m (1/k_i) v_i = 0.
-/

open scoped BigOperators in
/-- An m-dimensional reflexive simplex S with vertices v and associated unit partition denominators k. -/
def is_reflexive_simplex {m : ℕ} (S : Set (Fin m → ℝ)) (v : Fin (m + 1) → (Fin m → ℝ))
    (k : Fin (m + 1) → ℕ) : Prop := is_reflexive_polytope S ∧
  S = convexHull ℝ (Set.range v) ∧
  AffineIndependent ℝ v ∧
  (∀ i, 0 < k i) ∧
  (∑ i, (1 : ℝ) / (k i : ℝ) = 1) ∧
  (∑ i, ((1 : ℝ) / (k i : ℝ)) • v i = 0)
