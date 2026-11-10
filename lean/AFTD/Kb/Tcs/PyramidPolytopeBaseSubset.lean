import AFTD.Prelude
import AFTD.Kb.Tcs.PyramidPolytope

/-!
# pyramid_polytope_base_subset

Topic: combinatorics   Node: fa50e44d6d7f

Provenance: helper lemma. scout/2611-08819-reflexive-polytopes-can-have-doubly-exponentially-many-vert.md:234

Given natural numbers n and m, a subset B of Fin n → ℝ, and a family of vertices v : Fin (m + 1) → (Fin m → ℝ), the image of B under concatenation with v 0, {Fin.append x (v 0) | x ∈ B}, is a subset of the pyramid polytope pyramid_polytope B v in Fin (n + m) → ℝ.
-/

/-- The base polytope B embedded at the first apex v_0 is contained in the pyramid polytope. -/
theorem pyramid_polytope_base_subset {n m : ℕ} (B : Set (Fin n → ℝ))
    (v : Fin (m + 1) → (Fin m → ℝ)) :
    (fun x => Fin.append x (v 0)) '' B ⊆ pyramid_polytope B v :=
  Set.subset_union_left.trans (subset_convexHull ℝ _)
