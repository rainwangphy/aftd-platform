import AFTD.Prelude

/-!
# spatial_occupied_lines

Topic: combinatorics   Node: 168ef6661ed1

Provenance: formalization of a published result. Source: arXiv:2610.38864, Section 2

For a finite point set S in ℝ³ and a submodule ℓ of ℝ³, the number of affine lines parallel to ℓ meeting S is the cardinality of the image of S under the quotient map by ℓ.
-/

open Classical in
/-- The number of affine lines parallel to a submodule ℓ that meet a finite set S in ℝ³. -/
noncomputable def spatial_occupied_lines
    (S : Finset (EuclideanSpace ℝ (Fin 3)))
    (ℓ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) : ℕ := (S.image (Submodule.mkQ ℓ)).card
