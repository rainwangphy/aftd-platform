import AFTD.Prelude

/-!
# polynomial_log_concave_mul_linear_nonneg

Topic: graphs   Node: 528600487e6f

Provenance: helper lemma. An algebraic helper for leaf_rich_except_zero_forcing_poly_unimodal, a partial case of OP-1399.

Multiplying a natural-coefficient polynomial that is log-concave with interval support by 1+cX preserves both properties.
-/

open Polynomial

lemma polynomial_log_concave_mul_linear_nonneg_coeff_zero (p : Polynomial ℕ) (c : ℕ) :
    (p * (1 + Polynomial.C c * Polynomial.X)).coeff 0 = p.coeff 0 := by
  have h1 : p * (1 + Polynomial.C c * Polynomial.X) = p + (p * Polynomial.C c) * Polynomial.X := by ring
  rw [h1, coeff_add, coeff_mul_X_zero, add_zero]

lemma polynomial_log_concave_mul_linear_nonneg_coeff_succ (p : Polynomial ℕ) (c : ℕ) (k : ℕ) :
    (p * (1 + Polynomial.C c * Polynomial.X)).coeff (k + 1) = p.coeff (k + 1) + c * p.coeff k := by
  have h1 : p * (1 + Polynomial.C c * Polynomial.X) = p + Polynomial.C c * (p * Polynomial.X) := by ring
  rw [h1, coeff_add, coeff_C_mul, coeff_mul_X]

lemma polynomial_log_concave_mul_linear_nonneg_coeff_ge (p : Polynomial ℕ) (c : ℕ) (n : ℕ) :
    p.coeff n ≤ (p * (1 + Polynomial.C c * Polynomial.X)).coeff n := by
  cases n with
  | zero => rw [polynomial_log_concave_mul_linear_nonneg_coeff_zero]
  | succ n => rw [polynomial_log_concave_mul_linear_nonneg_coeff_succ]; exact Nat.le_add_right _ _

lemma polynomial_log_concave_mul_linear_nonneg_coeff_pos_imp (p : Polynomial ℕ) (c : ℕ) (n : ℕ)
    (h : 0 < (p * (1 + Polynomial.C c * Polynomial.X)).coeff n) :
    0 < p.coeff n ∨ (n > 0 ∧ 0 < p.coeff (n - 1)) := by
  cases n with
  | zero =>
    rw [polynomial_log_concave_mul_linear_nonneg_coeff_zero] at h
    left; exact h
  | succ n =>
    rw [polynomial_log_concave_mul_linear_nonneg_coeff_succ] at h
    rcases Nat.lt_or_ge 0 (p.coeff (n + 1)) with hpos | hzero
    · left; exact hpos
    · right
      have hz : p.coeff (n + 1) = 0 := by omega
      rw [hz, zero_add] at h
      refine ⟨Nat.succ_pos n, ?_⟩
      exact Nat.pos_of_mul_pos_left h

lemma polynomial_log_concave_mul_linear_nonneg_interval_support (p : Polynomial ℕ) (c : ℕ)
    (hint : ∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < p.coeff i → 0 < p.coeff k → 0 < p.coeff j)
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
    (hi : 0 < (p * (1 + Polynomial.C c * Polynomial.X)).coeff i)
    (hk : 0 < (p * (1 + Polynomial.C c * Polynomial.X)).coeff k) :
    0 < (p * (1 + Polynomial.C c * Polynomial.X)).coeff j := by
  rcases eq_or_lt_of_le hjk with rfl | hjk_lt
  · exact hk
  · have hjk' : j ≤ k - 1 := Nat.le_pred_of_lt hjk_lt
    rcases polynomial_log_concave_mul_linear_nonneg_coeff_pos_imp p c i hi with hi1 | ⟨hi_pos, hi2⟩
    · rcases polynomial_log_concave_mul_linear_nonneg_coeff_pos_imp p c k hk with hk1 | ⟨hk_pos, hk2⟩
      · have : 0 < p.coeff j := hint i j k hij hjk hi1 hk1
        exact lt_of_lt_of_le this (polynomial_log_concave_mul_linear_nonneg_coeff_ge p c j)
      · have : 0 < p.coeff j := hint i j (k - 1) hij hjk' hi1 hk2
        exact lt_of_lt_of_le this (polynomial_log_concave_mul_linear_nonneg_coeff_ge p c j)
    · rcases polynomial_log_concave_mul_linear_nonneg_coeff_pos_imp p c k hk with hk1 | ⟨hk_pos, hk2⟩
      · have : 0 < p.coeff j := hint (i - 1) j k (by omega) hjk hi2 hk1
        exact lt_of_lt_of_le this (polynomial_log_concave_mul_linear_nonneg_coeff_ge p c j)
      · have : 0 < p.coeff j := hint (i - 1) j (k - 1) (by omega) hjk' hi2 hk2
        exact lt_of_lt_of_le this (polynomial_log_concave_mul_linear_nonneg_coeff_ge p c j)

lemma polynomial_log_concave_mul_linear_nonneg_coeff_cross_le (p : Polynomial ℕ)
    (hlc : ∀ k : ℕ, p.coeff k * p.coeff (k + 2) ≤ p.coeff (k + 1) * p.coeff (k + 1))
    (hint : ∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < p.coeff i → 0 < p.coeff k → 0 < p.coeff j)
    (m : ℕ) :
    p.coeff m * p.coeff (m + 3) ≤ p.coeff (m + 1) * p.coeff (m + 2) := by
  by_cases hm0 : p.coeff m = 0
  · rw [hm0, zero_mul]; exact Nat.zero_le _
  by_cases hm30 : p.coeff (m + 3) = 0
  · rw [hm30, mul_zero]; exact Nat.zero_le _
  have hm : 0 < p.coeff m := Nat.pos_of_ne_zero hm0
  have hm3 : 0 < p.coeff (m + 3) := Nat.pos_of_ne_zero hm30
  have hm1 : 0 < p.coeff (m + 1) := hint m (m + 1) (m + 3) (by omega) (by omega) hm hm3
  have hm2 : 0 < p.coeff (m + 2) := hint m (m + 2) (m + 3) (by omega) (by omega) hm hm3
  have h1 : p.coeff m * p.coeff (m + 2) ≤ p.coeff (m + 1) * p.coeff (m + 1) := hlc m
  have h2 : p.coeff (m + 1) * p.coeff (m + 3) ≤ p.coeff (m + 2) * p.coeff (m + 2) := hlc (m + 1)
  have h_prod : (p.coeff m * p.coeff (m + 2)) * (p.coeff (m + 1) * p.coeff (m + 3)) ≤
    (p.coeff (m + 1) * p.coeff (m + 1)) * (p.coeff (m + 2) * p.coeff (m + 2)) :=
    Nat.mul_le_mul h1 h2
  have h_rearr : (p.coeff m * p.coeff (m + 3)) * (p.coeff (m + 1) * p.coeff (m + 2)) ≤
    (p.coeff (m + 1) * p.coeff (m + 2)) * (p.coeff (m + 1) * p.coeff (m + 2)) := by
    calc
      (p.coeff m * p.coeff (m + 3)) * (p.coeff (m + 1) * p.coeff (m + 2))
        = (p.coeff m * p.coeff (m + 2)) * (p.coeff (m + 1) * p.coeff (m + 3)) := by ring
      _ ≤ (p.coeff (m + 1) * p.coeff (m + 1)) * (p.coeff (m + 2) * p.coeff (m + 2)) := h_prod
      _ = (p.coeff (m + 1) * p.coeff (m + 2)) * (p.coeff (m + 1) * p.coeff (m + 2)) := by ring
  have h_pos : 0 < p.coeff (m + 1) * p.coeff (m + 2) := mul_pos hm1 hm2
  exact Nat.le_of_mul_le_mul_right h_rearr h_pos

theorem polynomial_log_concave_mul_linear_nonneg (p : Polynomial ℕ) (c : ℕ) (hlc : ∀ k : ℕ, p.coeff k * p.coeff (k + 2) ≤ p.coeff (k + 1) * p.coeff (k + 1)) (hint : ∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < p.coeff i → 0 < p.coeff k → 0 < p.coeff j) : (∀ k : ℕ, (p * (1 + Polynomial.C c * Polynomial.X)).coeff k * (p * (1 + Polynomial.C c * Polynomial.X)).coeff (k + 2) ≤ (p * (1 + Polynomial.C c * Polynomial.X)).coeff (k + 1) * (p * (1 + Polynomial.C c * Polynomial.X)).coeff (k + 1)) ∧ (∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < (p * (1 + Polynomial.C c * Polynomial.X)).coeff i → 0 < (p * (1 + Polynomial.C c * Polynomial.X)).coeff k → 0 < (p * (1 + Polynomial.C c * Polynomial.X)).coeff j) := by
  refine ⟨?_, polynomial_log_concave_mul_linear_nonneg_interval_support p c hint⟩
  intro k
  cases k with
  | zero =>
    rw [polynomial_log_concave_mul_linear_nonneg_coeff_zero,
        polynomial_log_concave_mul_linear_nonneg_coeff_succ,
        polynomial_log_concave_mul_linear_nonneg_coeff_succ]
    have hl : p.coeff 0 * (p.coeff 2 + c * p.coeff 1) = p.coeff 0 * p.coeff 2 + c * (p.coeff 0 * p.coeff 1) := by ring
    have hr : (p.coeff 1 + c * p.coeff 0) * (p.coeff 1 + c * p.coeff 0) =
      p.coeff 1 * p.coeff 1 + (c * (p.coeff 0 * p.coeff 1) + c * (p.coeff 0 * p.coeff 1) + c * c * (p.coeff 0 * p.coeff 0)) := by ring
    rw [hl, hr]
    have h_lc0 : p.coeff 0 * p.coeff 2 ≤ p.coeff 1 * p.coeff 1 := hlc 0
    omega
  | succ m =>
    have h_idx2 : m + 1 + 2 = (m + 2) + 1 := by omega
    have h_idx1 : m + 1 + 1 = m + 2 := by omega
    rw [h_idx2, h_idx1]
    rw [polynomial_log_concave_mul_linear_nonneg_coeff_succ,
        polynomial_log_concave_mul_linear_nonneg_coeff_succ (k := m + 2),
        polynomial_log_concave_mul_linear_nonneg_coeff_succ (k := m + 1)]
    have h1 : p.coeff (m + 1) * p.coeff (m + 3) ≤ p.coeff (m + 2) * p.coeff (m + 2) := hlc (m + 1)
    have h2 := polynomial_log_concave_mul_linear_nonneg_coeff_cross_le p hlc hint m
    have h3 : p.coeff m * p.coeff (m + 2) ≤ p.coeff (m + 1) * p.coeff (m + 1) := hlc m
    have hl : (p.coeff (m + 1) + c * p.coeff m) * (p.coeff (m + 3) + c * p.coeff (m + 2)) =
      p.coeff (m + 1) * p.coeff (m + 3) + c * (p.coeff m * p.coeff (m + 3)) +
      c * (p.coeff (m + 1) * p.coeff (m + 2)) + c * c * (p.coeff m * p.coeff (m + 2)) := by ring
    have hr : (p.coeff (m + 2) + c * p.coeff (m + 1)) * (p.coeff (m + 2) + c * p.coeff (m + 1)) =
      p.coeff (m + 2) * p.coeff (m + 2) + c * (p.coeff (m + 1) * p.coeff (m + 2)) +
      c * (p.coeff (m + 1) * p.coeff (m + 2)) + c * c * (p.coeff (m + 1) * p.coeff (m + 1)) := by ring
    rw [hl, hr]
    have h2' : c * (p.coeff m * p.coeff (m + 3)) ≤ c * (p.coeff (m + 1) * p.coeff (m + 2)) :=
      Nat.mul_le_mul_left c h2
    have h3' : c * c * (p.coeff m * p.coeff (m + 2)) ≤ c * c * (p.coeff (m + 1) * p.coeff (m + 1)) :=
      Nat.mul_le_mul_left (c * c) h3
    omega
