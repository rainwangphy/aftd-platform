import AFTD.Prelude

/-!
# permutahedron

Topic: integer_programming   Node: 9735d2955997

Provenance: formalization of a published result. Source: arXiv:2610.04498 Sec. 4.2

For a natural number n, the standard permutahedron on n elements is the convex hull in the space of functions from Fin n to ℝ of the set of permutation vectors ((σ i).val + 1)_{i : Fin n} as σ ranges over all permutations of Fin n.
-/

/-- The standard permutahedron on n elements as the convex hull of permutation vectors. -/
def permutahedron (n : ℕ) : Set (Fin n → ℝ) := convexHull ℝ (Set.range (fun (σ : Equiv.Perm (Fin n)) (i : Fin n) => ((σ i).val + 1 : ℝ)))
