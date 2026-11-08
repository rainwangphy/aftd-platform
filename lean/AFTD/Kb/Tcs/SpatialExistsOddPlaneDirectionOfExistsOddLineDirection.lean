import AFTD.Prelude
import AFTD.Kb.Tcs.SpatialExistsOrthogonalVectorOccupiedPlanesEqOccupiedLines

/-!
# spatial_exists_odd_plane_direction_of_exists_odd_line_direction

Topic: combinatorics   Node: 6b0334fb0a3d

Provenance: formalization of a published result. Source: arXiv:2610.38864 Proposition 2.2

Let S be a finite point set in ℝ³. If there exists a one-dimensional subspace ℓ of ℝ³ such that the number of affine lines parallel to ℓ meeting S is odd, then there exists a non-zero vector u in ℝ³ such that the number of affine planes perpendicular to u meeting S is odd.
-/

open Module in
open Classical in
/-- If a finite set in ℝ³ has an odd line direction, then it has an odd plane direction. -/
theorem spatial_exists_odd_plane_direction_of_exists_odd_line_direction
    (S : Finset (EuclideanSpace ℝ (Fin 3)))
    (h : ∃ ℓ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      finrank ℝ ℓ = 1 ∧ Odd (S.image (Submodule.mkQ ℓ)).card) :
    ∃ u : EuclideanSpace ℝ (Fin 3), u ≠ 0 ∧ Odd (S.image (fun p => inner ℝ p u)).card := by
  rcases h with ⟨ℓ, hℓ, hodd⟩
  obtain ⟨u, hu_ne, -, hu_eq⟩ := spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines S ℓ hℓ
  exact ⟨u, hu_ne, hu_eq.symm ▸ hodd⟩
