import AFTD.Prelude
import AFTD.Kb.NumberTheory.ViewObstructionOffset
import AFTD.Kb.NumberTheory.ViewObstructionRayDist
import AFTD.Kb.NumberTheory.IntToEuclidean
import AFTD.Kb.NumberTheory.ViewObstructionCenter

/-!
# view_obstruction_offset_le_ray_dist

Topic: elementary_number_theory   Node: aab80ab7748f

Provenance: formalization of a published result. Source: arXiv:2610.37711 Lemma 3.2

Offset lower bound: for any linear subspace U ⊆ ℝ^n and any integer direction vector v ∈ ℤ^n orthogonal to U (v ∈ U^⊥), the view-obstruction squared distance d_n(v) is at least the offset δ_U^2 of U.
-/

open Submodule in
/-- Lemma 3.2: the offset δ_U^2 is a lower bound for d_n(v) whenever v ∈ U^⊥. -/
theorem view_obstruction_offset_le_ray_dist
    (n : ℕ) (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (v : Fin n → ℤ)
    (hv : int_to_euclidean n v ∈ Uᗮ) :
    view_obstruction_offset n U ≤ view_obstruction_ray_dist n v := by
  haveI : U.HasOrthogonalProjection := inferInstance
  simp only [view_obstruction_offset, view_obstruction_ray_dist]
  set c := view_obstruction_center n
  apply le_ciInf
  intro t
  apply le_ciInf
  intro z
  set vE := int_to_euclidean n v
  set zE := int_to_euclidean n z
  have hneg : int_to_euclidean n (fun i => -z i) = - int_to_euclidean n z := by
    ext i
    simp [int_to_euclidean]
  have hproj : U.orthogonalProjectionOnto (t • vE - (c + zE)) =
      - U.orthogonalProjectionOnto (c + zE) := by
    rw [map_sub, map_smul, orthogonalProjectionOnto_apply_of_mem_orthogonal hv, smul_zero,
      zero_sub]
  have hδ : view_obstruction_offset n U ≤ ‖U.orthogonalProjectionOnto (c + zE)‖ ^ 2 := by
    have key : ‖U.orthogonalProjectionOnto (c + zE)‖ ^ 2 =
        ‖U.orthogonalProjectionOnto (c - int_to_euclidean n (fun i => -z i))‖ ^ 2 := by
      rw [hneg, sub_neg_eq_add]
    rw [key]
    simp only [view_obstruction_offset]
    exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact sq_nonneg _⟩ _
  have hle : ‖U.orthogonalProjectionOnto (c + zE)‖ ^ 2 ≤
      ‖t • vE - (c + zE)‖ ^ 2 := by
    have h1 : ‖U.orthogonalProjectionOnto (c + zE)‖ =
        ‖U.orthogonalProjectionOnto (t • vE - (c + zE))‖ := by
      rw [hproj, norm_neg]
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) (U.norm_orthogonalProjectionOnto_apply_le _) 2
  exact le_trans hδ hle
