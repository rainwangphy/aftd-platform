import AFTD.Prelude

/-!
# spatial_occupied_planes

Topic: combinatorics   Node: f6538b66b63d

Provenance: formalization of a published result. Source: arXiv:2610.38864, Section 1

For a finite point set S in ℝ³ and a vector u in ℝ³, the number of affine planes perpendicular to u meeting S is the cardinality of the image of S under the inner product map with u.
-/

/-- The number of affine planes perpendicular to a vector u that meet a finite set S in ℝ³. -/
noncomputable def spatial_occupied_planes
    (S : Finset (EuclideanSpace ℝ (Fin 3)))
    (u : EuclideanSpace ℝ (Fin 3)) : ℕ := (S.image (fun p => inner ℝ p u)).card
