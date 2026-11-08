import AFTD.Prelude
import AFTD.Kb.Tcs.SpatialOccupiedLines
import AFTD.Kb.Tcs.SpatialOccupiedPlanes

/-!
# spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines

Topic: combinatorics   Node: 77c6886a06dd

Provenance: helper lemma. arXiv:2610.38864, proof of Proposition 2.2

For every finite set S in ℝ³ and every one-dimensional subspace ℓ of ℝ³, there exists a non-zero vector u orthogonal to ℓ such that the number of affine planes perpendicular to u meeting S equals the number of affine lines parallel to ℓ meeting S.
-/

open Classical in
lemma spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines_card_image_eq
    {α β γ : Type*}
    (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (s.image f).card = (s.image g).card := by
  have H : ∀ b ∈ s.image f, ∃ a ∈ s, f a = b := by
    intro b hb; exact Finset.mem_image.mp hb
  choose φ hφ1 hφ2 using H
  apply Finset.card_bij (fun b hb => g (φ b hb))
  · intro b hb
    exact Finset.mem_image.mpr ⟨φ b hb, hφ1 b hb, rfl⟩
  · intro b1 hb1 b2 hb2 heq
    have := (h _ (hφ1 b1 hb1) _ (hφ1 b2 hb2)).mpr heq
    rw [← hφ2 b1 hb1, ← hφ2 b2 hb2, this]
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    have hfa : f a ∈ s.image f := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    refine ⟨f a, hfa, ?_⟩
    have := (h _ (hφ1 (f a) hfa) a ha).mp (hφ2 (f a) hfa)
    exact this

lemma spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines_basis_two_ne_zero
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (b : Module.Basis (Fin 2) ℝ M) (t : ℝ) :
    b 0 + t • b 1 ≠ 0 := by
  intro h
  have h1 : b.repr (b 0 + t • b 1) = 0 := by rw [h, map_zero]
  have h2 := Finsupp.ext_iff.mp h1 0
  rw [map_add, map_smul] at h2
  simp at h2

lemma spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines_mem_of_inner_zero
    (ℓ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (h_rank : Module.finrank ℝ ↥ℓᗮ = 2)
    (v : EuclideanSpace ℝ (Fin 3))
    (h0 : inner ℝ v ((Module.finBasisOfFinrankEq ℝ ↥ℓᗮ h_rank 0 : ↥ℓᗮ) : EuclideanSpace ℝ (Fin 3)) = 0)
    (h1 : inner ℝ v ((Module.finBasisOfFinrankEq ℝ ↥ℓᗮ h_rank 1 : ↥ℓᗮ) : EuclideanSpace ℝ (Fin 3)) = 0) :
    v ∈ ℓ := by
  have : v ∈ ℓᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    let b := Module.finBasisOfFinrankEq ℝ ↥ℓᗮ h_rank
    have hw_sum : (⟨w, hw⟩ : ↥ℓᗮ) = ∑ i : Fin 2, b.repr ⟨w, hw⟩ i • b i := (b.sum_repr ⟨w, hw⟩).symm
    have hw_sum' : w = ∑ i : Fin 2, b.repr ⟨w, hw⟩ i • (b i : EuclideanSpace ℝ (Fin 3)) := by
      exact congr_arg Subtype.val hw_sum
    rw [hw_sum', sum_inner]
    have h_zero : ∀ i : Fin 2, inner ℝ (b.repr ⟨w, hw⟩ i • (b i : EuclideanSpace ℝ (Fin 3))) v = 0 := by
      intro i
      rw [inner_smul_left, real_inner_comm]
      fin_cases i
      · change _ * inner ℝ v (b 0 : EuclideanSpace ℝ (Fin 3)) = 0
        rw [h0, mul_zero]
      · change _ * inner ℝ v (b 1 : EuclideanSpace ℝ (Fin 3)) = 0
        rw [h1, mul_zero]
    simp [h_zero]
  rwa [Submodule.orthogonal_orthogonal (K := ℓ)] at this

open Module in
open Classical in
/-- For any finite set S in ℝ³ and any line direction ℓ, there is a non-zero vector u orthogonal to ℓ whose occupied planes match the occupied lines of ℓ. -/
theorem spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines
    (S : Finset (EuclideanSpace ℝ (Fin 3)))
    (ℓ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hℓ : finrank ℝ ℓ = 1) :
    ∃ u : EuclideanSpace ℝ (Fin 3), u ≠ 0 ∧ u ∈ ℓᗮ ∧
      (S.image (fun p => inner ℝ p u)).card = (S.image (Submodule.mkQ ℓ)).card := by
  have h_rank : finrank ℝ ↥ℓᗮ = 2 := by
    have h := Submodule.finrank_add_finrank_orthogonal ℓ
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h
    omega
  let b := finBasisOfFinrankEq ℝ ↥ℓᗮ h_rank
  let b0 : EuclideanSpace ℝ (Fin 3) := (b 0 : ↥ℓᗮ)
  let b1 : EuclideanSpace ℝ (Fin 3) := (b 1 : ↥ℓᗮ)
  let pairs := (S ×ˢ S).filter (fun p => inner ℝ (p.1 - p.2) b1 ≠ 0)
  let bad_set : Finset ℝ := pairs.image (fun p => - inner ℝ (p.1 - p.2) b0 / inner ℝ (p.1 - p.2) b1)
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad_set
  let u_sub : ↥ℓᗮ := b 0 + t • b 1
  let u : EuclideanSpace ℝ (Fin 3) := (u_sub : ↥ℓᗮ)
  have hu_ne : u ≠ 0 := by
    intro hu
    have : u_sub = 0 := Subtype.ext hu
    exact spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines_basis_two_ne_zero b t this
  have hu_mem : u ∈ ℓᗮ := u_sub.2
  refine ⟨u, hu_ne, hu_mem, ?_⟩
  apply spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines_card_image_eq
  intro p1 hp1 p2 hp2
  constructor
  · intro h_eq
    by_contra h_neq
    have h_diff_not_mem : p1 - p2 ∉ ℓ := by
      intro h_mem
      have : Submodule.mkQ ℓ p1 = Submodule.mkQ ℓ p2 := (Submodule.Quotient.eq ℓ).mpr h_mem
      exact h_neq this
    have h_not_both_zero : ¬(inner ℝ (p1 - p2) b0 = 0 ∧ inner ℝ (p1 - p2) b1 = 0) := by
      intro ⟨h0, h1⟩
      exact h_diff_not_mem (spatial_exists_orthogonal_vector_occupied_planes_eq_occupied_lines_mem_of_inner_zero ℓ h_rank (p1 - p2) h0 h1)
    have hu_exp : inner ℝ (p1 - p2) u = inner ℝ (p1 - p2) b0 + t * inner ℝ (p1 - p2) b1 := by
      change inner ℝ (p1 - p2) (b0 + t • b1) = _
      rw [inner_add_right, inner_smul_right]
    have h_inner_sub : inner ℝ (p1 - p2) u = 0 := by
      rw [inner_sub_left, h_eq, sub_self]
    rw [h_inner_sub] at hu_exp
    by_cases hb1 : inner ℝ (p1 - p2) b1 = 0
    · rw [hb1, mul_zero, add_zero] at hu_exp
      exact h_not_both_zero ⟨hu_exp.symm, hb1⟩
    · have ht_eq : t = - inner ℝ (p1 - p2) b0 / inner ℝ (p1 - p2) b1 := by
        have : t * inner ℝ (p1 - p2) b1 = - inner ℝ (p1 - p2) b0 := by linarith
        exact (eq_div_iff hb1).mpr (by linarith)
      have h_pair_mem : (p1, p2) ∈ pairs := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, hb1⟩
      have ht_mem : t ∈ bad_set := by
        rw [Finset.mem_image]
        refine ⟨(p1, p2), h_pair_mem, ht_eq.symm⟩
      exact ht ht_mem
  · intro h_mkQ
    have h_mem : p1 - p2 ∈ ℓ := (Submodule.Quotient.eq ℓ).mp h_mkQ
    have h0 : inner ℝ (p1 - p2) u = 0 := Submodule.inner_right_of_mem_orthogonal h_mem hu_mem
    rw [inner_sub_left] at h0
    exact sub_eq_zero.mp h0
