import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingPoly
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# zero_forcing_poly_ulc_implies_log_concave

Topic: graphs   Node: 6f0a3b51ac6f

Provenance: helper lemma. A helper for tree_zero_forcing_poly_unimodal using the proposed ultra-log-concavity route.

For any finite graph, ultra-log-concavity of its zero forcing coefficients implies ordinary log-concavity.
-/

private theorem zero_forcing_poly_ulc_implies_log_concave_coeff_eq_zero
    {V : Type*} [Fintype V] (G : SimpleGraph V) {m : ℕ} (hm : Fintype.card V < m) :
    (zero_forcing_poly G).coeff m = 0 := by
  classical
  have hcoeff : (zero_forcing_poly G).coeff m =
      ∑ S : Finset V,
        (if is_zero_forcing_set G (S : Set V) then Polynomial.X ^ S.card else 0 : Polynomial ℕ).coeff m := by
    rw [zero_forcing_poly]
    simp only [Polynomial.finsetSum_coeff]
  rw [hcoeff]
  apply Finset.sum_eq_zero
  intro S _
  by_cases h : is_zero_forcing_set G (S : Set V)
  · rw [if_pos h, Polynomial.coeff_X_pow, if_neg]
    have hS : S.card ≤ Fintype.card V := Finset.card_le_univ S
    omega
  · simp [h]

private theorem zero_forcing_poly_ulc_implies_log_concave_choose
    (n k : ℕ) (hk : k + 2 ≤ n) :
    Nat.choose n k * Nat.choose n (k + 2) ≤
      Nat.choose n (k + 1) ^ 2 := by
  have hR1 : Nat.choose n (k + 1) * (k + 1) = Nat.choose n k * (n - k) :=
    Nat.choose_succ_right_eq n k
  have hR2 : Nat.choose n (k + 2) * (k + 2) = Nat.choose n (k + 1) * (n - (k + 1)) :=
    Nat.choose_succ_right_eq n (k + 1)
  have hsub : n - (k + 1) = n - k - 1 := by omega
  have hpos : 0 < (n - k) * (k + 2) := by
    apply Nat.mul_pos <;> omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc
    (Nat.choose n k * Nat.choose n (k + 2)) * ((n - k) * (k + 2))
        = (Nat.choose n k * (n - k)) * (Nat.choose n (k + 2) * (k + 2)) := by ring
    _ = (Nat.choose n (k + 1) * (k + 1)) * (Nat.choose n (k + 1) * (n - k - 1)) := by
          rw [hR1, hR2, hsub]
    _ = (Nat.choose n (k + 1) * Nat.choose n (k + 1)) * ((k + 1) * (n - k - 1)) := by ring
    _ ≤ (Nat.choose n (k + 1) * Nat.choose n (k + 1)) * ((n - k) * (k + 2)) := by
          apply Nat.mul_le_mul_left
          calc
            (k + 1) * (n - k - 1) ≤ (k + 1) * (n - k) := by
              apply Nat.mul_le_mul_left
              omega
            _ ≤ (k + 2) * (n - k) := by
              apply Nat.mul_le_mul_right
              omega
            _ = (n - k) * (k + 2) := by ring
    _ = Nat.choose n (k + 1) ^ 2 * ((n - k) * (k + 2)) := by ring

theorem zero_forcing_poly_ulc_implies_log_concave {V : Type*} [Fintype V] (G : SimpleGraph V) (h : ∀ k : ℕ, k + 2 ≤ Fintype.card V → (zero_forcing_poly G).coeff k * (zero_forcing_poly G).coeff (k + 2) * (Nat.choose (Fintype.card V) (k + 1)) ^ 2 ≤ ((zero_forcing_poly G).coeff (k + 1)) ^ 2 * Nat.choose (Fintype.card V) k * Nat.choose (Fintype.card V) (k + 2)) : ∀ k : ℕ, (zero_forcing_poly G).coeff k * (zero_forcing_poly G).coeff (k + 2) ≤ (zero_forcing_poly G).coeff (k + 1) * (zero_forcing_poly G).coeff (k + 1) := by
  intro k
  by_cases hk : k + 2 ≤ Fintype.card V
  · have h1 := h k hk
    have hbin := zero_forcing_poly_ulc_implies_log_concave_choose (Fintype.card V) k hk
    have hCpos : 0 < (Nat.choose (Fintype.card V) (k + 1)) ^ 2 := by
      apply Nat.pow_pos
      exact Nat.choose_pos (by omega)
    have h2 : ((zero_forcing_poly G).coeff (k + 1)) ^ 2 *
        (Nat.choose (Fintype.card V) k * Nat.choose (Fintype.card V) (k + 2)) ≤
        ((zero_forcing_poly G).coeff (k + 1)) ^ 2 *
        (Nat.choose (Fintype.card V) (k + 1)) ^ 2 :=
      Nat.mul_le_mul_left _ hbin
    refine Nat.le_of_mul_le_mul_right ?_ hCpos
    calc
      ((zero_forcing_poly G).coeff k * (zero_forcing_poly G).coeff (k + 2)) *
          (Nat.choose (Fintype.card V) (k + 1)) ^ 2
          = (zero_forcing_poly G).coeff k * (zero_forcing_poly G).coeff (k + 2) *
              (Nat.choose (Fintype.card V) (k + 1)) ^ 2 := by ring
      _ ≤ ((zero_forcing_poly G).coeff (k + 1)) ^ 2 *
            Nat.choose (Fintype.card V) k * Nat.choose (Fintype.card V) (k + 2) := h1
      _ = ((zero_forcing_poly G).coeff (k + 1)) ^ 2 *
            (Nat.choose (Fintype.card V) k * Nat.choose (Fintype.card V) (k + 2)) := by ring
      _ ≤ ((zero_forcing_poly G).coeff (k + 1)) ^ 2 *
            (Nat.choose (Fintype.card V) (k + 1)) ^ 2 := h2
      _ = ((zero_forcing_poly G).coeff (k + 1) * (zero_forcing_poly G).coeff (k + 1)) *
            (Nat.choose (Fintype.card V) (k + 1)) ^ 2 := by ring
  · have hcard : Fintype.card V < k + 2 := by omega
    have hz : (zero_forcing_poly G).coeff (k + 2) = 0 :=
      zero_forcing_poly_ulc_implies_log_concave_coeff_eq_zero G hcard
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _
