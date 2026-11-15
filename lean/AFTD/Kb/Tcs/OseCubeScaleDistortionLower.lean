import AFTD.Prelude

/-!
# ose_cube_scale_distortion_lower

Topic: algorithms   Node: 04bfc0ce7beb

Provenance: helper lemma. arXiv:2611.08546, Section 6.1; Boolean-cube distortion argument

If a two-layer cube has second-layer edge distance s and antipodal distance m, and a noncontracting D-Lipschitz Hilbert map satisfies the antipodal sum inequality, then m≤sqrt(n)*D*s.
-/

theorem ose_cube_scale_distortion_lower (n : ℕ) (hn : 1 ≤ n)
    (M : MetricSpace (Bool × (Fin n → Bool))) (m s D : ℝ) (hm : 0 ≤ m) (hs : 0 < s)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : letI := M
    (∀ x : Fin n → Bool, dist (true,x) (true,fun i => !(x i)) = m) →
    (∀ (x : Fin n → Bool) (i : Fin n), dist (true,x) (true,Function.update x i (!(x i))) = s) →
    ∀ F : (Bool × (Fin n → Bool)) → H,
      (∀ a b, dist a b ≤ dist (F a) (F b) ∧ dist (F a) (F b) ≤ D * dist a b) →
      ((∑ x : Fin n → Bool, dist (F (true,x)) (F (true,fun i => !(x i)))^2) ≤
        ∑ x : Fin n → Bool, ∑ i : Fin n, dist (F (true,x)) (F (true,Function.update x i (!(x i))))^2) →
      m ≤ Real.sqrt (n : ℝ) * (D*s) := by
  intro ha he F hF htype
  let x0 : Fin n → Bool := fun _ => false
  let i0 : Fin n := ⟨0, by omega⟩
  have hDs : 0 ≤ D*s := by
    have h := (hF (true,x0) (true,Function.update x0 i0 (!(x0 i0)))).2
    rw [he x0 i0] at h
    exact le_trans dist_nonneg h
  have hanti : (∑ x : Fin n → Bool, m^2) ≤
      ∑ x : Fin n → Bool, dist (F (true,x)) (F (true,fun i => !(x i)))^2 := by
    apply Finset.sum_le_sum
    intro x hx
    have h := (hF (true,x) (true,fun i => !(x i))).1
    rw [ha x] at h
    exact pow_le_pow_left₀ hm h 2
  have hedge : (∑ x : Fin n → Bool, ∑ i : Fin n,
        dist (F (true,x)) (F (true,Function.update x i (!(x i))))^2) ≤
      ∑ x : Fin n → Bool, ∑ _i : Fin n, (D*s)^2 := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro i hi
    have h := (hF (true,x) (true,Function.update x i (!(x i)))).2
    rw [he x i] at h
    exact pow_le_pow_left₀ dist_nonneg h 2
  have hsum := le_trans (le_trans hanti htype) hedge
  have hN : 0 < (Fintype.card (Fin n → Bool) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Fin n → Bool)
  have hsum' : (Fintype.card (Fin n → Bool) : ℝ) * m^2 ≤
      (Fintype.card (Fin n → Bool) : ℝ) * ((n : ℝ) * (D*s)^2) := by
    simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hsum
  have hc := le_of_mul_le_mul_left hsum' hN
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsq : m^2 ≤ (Real.sqrt (n : ℝ) * (D*s))^2 := by
    rw [mul_pow, Real.sq_sqrt hn0]
    exact hc
  have hr0 : 0 ≤ Real.sqrt (n : ℝ) * (D*s) := mul_nonneg (Real.sqrt_nonneg _) hDs
  exact (pow_le_pow_iff_left₀ hm hr0 (by norm_num : 2 ≠ 0)).1 hsq
