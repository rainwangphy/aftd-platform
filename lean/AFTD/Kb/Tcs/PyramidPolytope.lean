import AFTD.Prelude

/-!
# pyramid_polytope

Topic: combinatorics   Node: 5b9c2f277e5c

Provenance: formalization of a published result. Source: scout/2611-08819-reflexive-polytopes-can-have-doubly-exponentially-many-vert.md:234

Given natural numbers n and m, a subset B of Fin n → ℝ, and a family of m + 1 vertices v : Fin (m + 1) → (Fin m → ℝ) in Fin m → ℝ, the pyramid polytope pyramid_polytope B v in Fin (n + m) → ℝ is the convex hull in Fin (n + m) → ℝ of the union of the image of B under concatenation with v 0 (namely the points Fin.append x (v 0) for x in B) and the set of apices Fin.append (0 : Fin n → ℝ) (v j.succ) for all j in Fin m.
-/

/-- The m-fold pyramid polytope over a base B in ℝ^n with apices from the vertices of a simplex in ℝ^m. -/
def pyramid_polytope {n m : ℕ} (B : Set (Fin n → ℝ)) (v : Fin (m + 1) → (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) := convexHull ℝ (((fun x => Fin.append x (v 0)) '' B) ∪
    (Set.range (fun j : Fin m => Fin.append (0 : Fin n → ℝ) (v j.succ))))
