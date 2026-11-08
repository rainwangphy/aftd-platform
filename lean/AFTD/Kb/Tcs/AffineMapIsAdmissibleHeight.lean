import AFTD.Prelude
import AFTD.Kb.Tcs.PlanarAdmissibleHeight

/-!
# affine_map_is_admissible_height

Topic: combinatorics   Node: b421991dee57

Provenance: helper lemma. arXiv:2610.38864 Section 3.1

For any finite set A : Finset (EuclideanSpace ℝ (Fin 2)) in the plane and any affine map f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ, the restriction of f to A is an admissible height function (planar_admissible_height A (fun p => f p)).
-/

/-- Any affine function on ℝ² restricts to an admissible height function on A. -/
theorem affine_map_is_admissible_height (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) :
    planar_admissible_height A (fun p => f (p : EuclideanSpace ℝ (Fin 2))) := by
  intro p q r s c h
  have h1 := AffineMap.linearMap_vsub f (q : EuclideanSpace ℝ (Fin 2)) (p : EuclideanSpace ℝ (Fin 2))
  have h2 := AffineMap.linearMap_vsub f (s : EuclideanSpace ℝ (Fin 2)) (r : EuclideanSpace ℝ (Fin 2))
  simp only [vsub_eq_sub] at h1 h2
  rw [h, map_smul, h2, smul_eq_mul] at h1
  linarith
