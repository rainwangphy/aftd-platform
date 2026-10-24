import AFTD.Prelude

/-!
# planar_necklace_injective_projection

Topic: fair_division   Node: 1611a42cb2cb

Provenance: helper lemma. step towards planar_necklace_three_agents_three_cuts

For every finite set P of points of ℝ² there is a nonzero linear functional φ : ℝ² → ℝ that is injective on P: if p, q ∈ P and φ p = φ q then p = q.
-/

def planar_necklace_injective_projection_phi (s : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ ℝ + s • LinearMap.snd ℝ ℝ ℝ

lemma planar_necklace_injective_projection_phi_apply (s : ℝ) (p : ℝ × ℝ) :
    planar_necklace_injective_projection_phi s p = p.1 + s * p.2 := rfl

lemma planar_necklace_injective_projection_phi_ne_zero (s : ℝ) :
    planar_necklace_injective_projection_phi s ≠ 0 := by
  intro h
  have h1 : planar_necklace_injective_projection_phi s (1, 0) = 0 := by rw [h]; rfl
  have h2 : planar_necklace_injective_projection_phi s (1, 0) = 1 := by
    dsimp [planar_necklace_injective_projection_phi]
    simp
  linarith

lemma planar_necklace_injective_projection_phi_inj_of_snd_eq
    (s : ℝ) (p q : ℝ × ℝ) (h2 : p.2 = q.2)
    (heq : planar_necklace_injective_projection_phi s p = planar_necklace_injective_projection_phi s q) :
    p = q := by
  rw [planar_necklace_injective_projection_phi_apply, planar_necklace_injective_projection_phi_apply] at heq
  rw [h2] at heq
  have h1 : p.1 = q.1 := by linarith
  exact Prod.ext h1 h2

lemma planar_necklace_injective_projection_slope_eq
    (s : ℝ) (p q : ℝ × ℝ) (h2 : p.2 ≠ q.2) (heq : p.1 + s * p.2 = q.1 + s * q.2) :
    s = (q.1 - p.1) / (p.2 - q.2) := by
  have hsub : s * (p.2 - q.2) = q.1 - p.1 := by linarith
  exact eq_div_of_mul_eq (sub_ne_zero.mpr h2) hsub

open scoped Classical in
noncomputable def planar_necklace_injective_projection_bad_slopes (P : Finset (ℝ × ℝ)) : Finset ℝ :=
  (P ×ˢ P).filter (fun ⟨p, q⟩ => p.2 ≠ q.2) |>.image (fun ⟨p, q⟩ => (q.1 - p.1) / (p.2 - q.2))

/-- A finite point set admits a nonzero linear functional that is injective on it (a generic direction). -/
theorem planar_necklace_injective_projection
    (P : Finset (ℝ × ℝ)) :
    ∃ φ : (ℝ × ℝ) →ₗ[ℝ] ℝ, φ ≠ 0 ∧ ∀ p ∈ P, ∀ q ∈ P, φ p = φ q → p = q := by
  classical
  have hfin := (planar_necklace_injective_projection_bad_slopes P).finite_toSet.exists_notMem
  rcases hfin with ⟨s, hs⟩
  have hs_not_mem : s ∉ planar_necklace_injective_projection_bad_slopes P := by simpa using hs
  use planar_necklace_injective_projection_phi s
  refine ⟨planar_necklace_injective_projection_phi_ne_zero s, fun p hp q hq heq => ?_⟩
  by_cases h2 : p.2 = q.2
  · exact planar_necklace_injective_projection_phi_inj_of_snd_eq s p q h2 heq
  · exfalso
    have hbad : s ∈ planar_necklace_injective_projection_bad_slopes P := by
      apply Finset.mem_image.mpr
      refine ⟨(p, q), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_product.mpr ⟨hp, hq⟩, h2⟩
      · rw [planar_necklace_injective_projection_slope_eq s p q h2]
        exact heq
    exact hs_not_mem hbad
