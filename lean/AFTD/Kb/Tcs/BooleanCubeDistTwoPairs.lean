import AFTD.Prelude

/-!
# boolean_cube_dist_two_pairs

Topic: combinatorics   Node: ada840615fb3

Provenance: formalization of a published result. Source: arXiv:2611.04644, Section 1

For a natural number d and a finite set X : Finset (Fin d → Fin 2) of vertices in the boolean cube, boolean_cube_dist_two_pairs X is the cardinality of the finset of ordered pairs (x, y) ∈ X ×ˢ X with hammingDist x y = 2.
-/

/-- The number of ordered pairs of vertices in X at Hamming distance 2. -/
def boolean_cube_dist_two_pairs {d : ℕ} (X : Finset (Fin d → Fin 2)) : ℕ := ((X ×ˢ X).filter (fun p => hammingDist p.1 p.2 = 2)).card
