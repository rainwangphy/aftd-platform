import AFTD.Prelude

/-!
# bell_flat_product_coordinate_obstruction

Topic: quantum   Node: 1b6135bb6af3

Provenance: helper lemma. Arithmetic step for the Bell-pair product-basis obstruction related to OP-1653 and experiment 29881; the connection to quantum states is not asserted here.

Let a, x and y be real four-vectors, with x and y orthogonal and each of squared norm one half. Let p and q be real, where q is nonnegative and less than one half. It is impossible that every coordinate satisfies p a_i² + q (x_i² + y_i²) = 1/4 and a_i x_i = 0.
-/

theorem bell_flat_product_coordinate_obstruction
    (a x y : Fin 4 → ℝ) (p q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1 / 2)
    (hx : (∑ i, x i ^ 2) = 1 / 2)
    (hy : (∑ i, y i ^ 2) = 1 / 2)
    (hxy : (∑ i, x i * y i) = 0)
    (hflat : ∀ i, p * a i ^ 2 + q * (x i ^ 2 + y i ^ 2) = 1 / 4)
    (hperp : ∀ i, a i * x i = 0) : False := by
  have hbound (i : Fin 4) : x i ^ 2 + y i ^ 2 ≤ 1 / 2 := by
    have hsum : (x i ^ 2 + y i ^ 2)^2 ≤ ∑ j, (x i * x j + y i * y j) ^ 2 := by
      have h := Finset.single_le_sum (f := fun j : Fin 4 => (x i * x j + y i * y j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [h]
    have hid : ∑ j, (x i * x j + y i * y j) ^ 2 = (x i ^ 2 + y i ^ 2) / 2 := by
      have hx' := congrArg (fun r : ℝ => r * x i ^ 2) hx
      have hy' := congrArg (fun r : ℝ => r * y i ^ 2) hy
      have hxy' := congrArg (fun r : ℝ => r * (2 * x i * y i)) hxy
      simp only [Fin.sum_univ_four] at hx' hy' hxy' ⊢
      nlinarith [hx', hy', hxy']
    by_contra hh
    have ht : 0 < x i ^ 2 + y i ^ 2 := by linarith
    have hn : 0 < (x i ^ 2 + y i ^ 2) - 1 / 2 := by linarith
    have hn' := mul_pos ht hn
    nlinarith [hn']
  have hz : ∀ i, x i = 0 := by
    intro i
    have hai : a i ≠ 0 := by
      intro ha
      have hf := hflat i
      have hb := hbound i
      rw [ha] at hf
      norm_num at hf
      nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hb)]
    exact (mul_eq_zero.mp (hperp i)).resolve_left hai
  simp [hz] at hx
