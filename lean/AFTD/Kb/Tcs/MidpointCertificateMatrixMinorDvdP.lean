import AFTD.Prelude

/-!
# midpoint_certificate_matrix_minor_dvd_p

Topic: combinatorics   Node: 25f4813bfbb2

Provenance: helper lemma. step towards finset_card_ge_one_add_clog_of_midpoint_balanced

For an injective certificate vector b in (ZMod p)^{k+1} satisfying the midpoint equations with k > 0, the shifted vector b - b(j₀) restricts to a non-zero vector in the kernel of the k x k minor modulo p, so its determinant vanishes modulo p and is divisible by p in Z.
-/

/-- Every k x k minor of a (k+1) x (k+1) midpoint-certificate matrix is divisible by p in ZMod p when k > 0. -/
theorem midpoint_certificate_matrix_minor_dvd_p {p k : ℕ} [Fact p.Prime] (hk : 0 < k)
    (u v : Fin (k + 1) → Fin (k + 1))
    (b : Fin (k + 1) → ZMod p) (hinj : Function.Injective b)
    (hmid : ∀ i, 2 * b i = b (u i) + b (v i))
    (i₀ j₀ : Fin (k + 1)) :
    (p : ℤ) ∣ ((Matrix.of fun (i j : Fin (k + 1)) =>
      (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
      i₀.succAbove j₀.succAbove).det := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap : (((Matrix.of fun (i j : Fin (k + 1)) =>
      (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
      i₀.succAbove j₀.succAbove).det : ZMod p) =
    ((Matrix.of fun (i j : Fin (k + 1)) =>
      (if j = i then (2 : ZMod p) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
      i₀.succAbove j₀.succAbove).det := by
    have h := (RingHom.map_det (Int.castRingHom (ZMod p))
      ((Matrix.of fun (i j : Fin (k + 1)) =>
        (if j = i then (2 : ℤ) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
        i₀.succAbove j₀.succAbove)).symm
    rw [RingHom.mapMatrix_apply] at h
    show (Int.castRingHom (ZMod p)) _ = _
    rw [← h]
    congr 1
    ext i j
    simp
  rw [hmap]
  let M := (Matrix.of fun (i j : Fin (k + 1)) =>
      (if j = i then (2 : ZMod p) else 0) - (if j = u i then 1 else 0) - (if j = v i then 1 else 0)).submatrix
      i₀.succAbove j₀.succAbove
  have h_det_zero : M.det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨fun m => b (j₀.succAbove m) - b j₀, ?_, ?_⟩
    · intro h
      have h0 : (fun m : Fin k => b (j₀.succAbove m) - b j₀) ⟨0, hk⟩ = 0 := by rw [h]; rfl
      dsimp at h0
      have heq : b (j₀.succAbove ⟨0, hk⟩) = b j₀ := sub_eq_zero.mp h0
      have h_inj := hinj heq
      exact Fin.succAbove_ne j₀ ⟨0, hk⟩ h_inj
    · ext l
      rw [Matrix.mulVec]
      dsimp [dotProduct, M]
      have hsplit := Fin.sum_univ_succAbove
        (fun j => ((if j = i₀.succAbove l then (2 : ZMod p) else 0) -
          (if j = u (i₀.succAbove l) then 1 else 0) - (if j = v (i₀.succAbove l) then 1 else 0)) * (b j - b j₀)) j₀
      have hj0 : ((if j₀ = i₀.succAbove l then (2 : ZMod p) else 0) -
          (if j₀ = u (i₀.succAbove l) then 1 else 0) - (if j₀ = v (i₀.succAbove l) then 1 else 0)) * (b j₀ - b j₀) = 0 := by
        rw [sub_self, mul_zero]
      rw [hj0, zero_add] at hsplit
      rw [← hsplit]
      have h1 : ∀ j, (((if j = i₀.succAbove l then (2 : ZMod p) else 0) - (if j = u (i₀.succAbove l) then 1 else 0) - (if j = v (i₀.succAbove l) then 1 else 0)) * (b j - b j₀)) =
        (((if j = i₀.succAbove l then (2 : ZMod p) else 0) - (if j = u (i₀.succAbove l) then 1 else 0) - (if j = v (i₀.succAbove l) then 1 else 0)) * b j) -
        (((if j = i₀.succAbove l then (2 : ZMod p) else 0) - (if j = u (i₀.succAbove l) then 1 else 0) - (if j = v (i₀.succAbove l) then 1 else 0)) * b j₀) := by
        intro j; ring
      simp_rw [h1]
      rw [Finset.sum_sub_distrib]
      have h_left : ∑ j : Fin (k + 1), (((if j = i₀.succAbove l then (2 : ZMod p) else 0) -
          (if j = u (i₀.succAbove l) then 1 else 0) - (if j = v (i₀.succAbove l) then 1 else 0)) * b j) = 0 := by
        have : ∀ j : Fin (k + 1),
          (((if j = i₀.succAbove l then (2 : ZMod p) else 0) - (if j = u (i₀.succAbove l) then 1 else 0) - (if j = v (i₀.succAbove l) then 1 else 0)) * b j) =
          (if j = i₀.succAbove l then 2 * b j else 0) - (if j = u (i₀.succAbove l) then b j else 0) - (if j = v (i₀.succAbove l) then b j else 0) := by
          intro j; split_ifs <;> ring
        simp_rw [this, sub_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq']
        rw [← hmid (i₀.succAbove l)]
        ring
      rw [h_left]
      have h_right : ∑ j : Fin (k + 1), (((if j = i₀.succAbove l then (2 : ZMod p) else 0) -
          (if j = u (i₀.succAbove l) then 1 else 0) - (if j = v (i₀.succAbove l) then 1 else 0)) * b j₀) = 0 := by
        rw [← Finset.sum_mul]
        have h_ones : ∑ j : Fin (k + 1), ((if j = i₀.succAbove l then (2 : ZMod p) else 0) -
            (if j = u (i₀.succAbove l) then 1 else 0) - (if j = v (i₀.succAbove l) then (1 : ZMod p) else 0)) = 0 := by
          simp_rw [sub_sub]
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          simp [Finset.sum_ite_eq']
          ring
        rw [h_ones, zero_mul]
      rw [h_right, sub_zero]
  exact h_det_zero
