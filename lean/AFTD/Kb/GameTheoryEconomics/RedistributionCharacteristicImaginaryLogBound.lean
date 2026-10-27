import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionCharacteristic

/-!
# redistribution_characteristic_imaginary_log_bound

Topic: mechanism_design   Node: c684607a4585

Provenance: helper lemma. Routine finite-characteristic-function helper for IN-251, arXiv:2610.10995 Lemma4.3 Steps1/2 and equation12. These statements do not assert the half-plane boundary integral inequality or the main harmonic error bound. No research advance.

For any real reports and any real y, the characteristic value at i*y is strictly positive in norm and its negative logarithm is at most y times the empirical mean.
-/

open Finset MeasureTheory

theorem redistribution_characteristic_imaginary_log_bound {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (y : ℝ) :
    0 < ‖redistribution_characteristic θ ((y : ℂ)*Complex.I)‖ ∧
      -Real.log ‖redistribution_characteristic θ ((y : ℂ)*Complex.I)‖ ≤
        y * (∑ j, θ j) / (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  set S := 1 / (n : ℝ) * ∑ j, Real.exp (-y * θ j) with hS_def
  have h_char : redistribution_characteristic θ ((y : ℂ) * Complex.I) = (S : ℂ) := by
    rw [hS_def]
    unfold redistribution_characteristic
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have h1 : Complex.I * ((y : ℂ) * Complex.I) * (θ j : ℂ) = - (y : ℂ) * (θ j : ℂ) := by
      calc
        Complex.I * ((y : ℂ) * Complex.I) * (θ j : ℂ)
          = (Complex.I * Complex.I) * (y : ℂ) * (θ j : ℂ) := by ring
        _ = -1 * (y : ℂ) * (θ j : ℂ) := by rw [Complex.I_mul_I]
        _ = -(y : ℂ) * (θ j : ℂ) := by ring
    rw [h1]
  have h_univ : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have h_sum_pos : 0 < ∑ j, Real.exp (-y * θ j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos (-y * θ j)) h_univ
  have hS_pos : 0 < S := mul_pos (one_div_pos.mpr hn_pos) h_sum_pos
  have h_norm : ‖redistribution_characteristic θ ((y : ℂ) * Complex.I)‖ = S := by
    rw [h_char, Complex.norm_real, Real.norm_of_nonneg hS_pos.le]
  refine ⟨by rw [h_norm]; exact hS_pos, ?_⟩
  rw [h_norm]
  set m := - (y * (∑ j, θ j) / (n : ℝ)) with hm_def
  have h_exp_term : ∀ j : Fin n, Real.exp m * (-y * θ j - m + 1) ≤ Real.exp (-y * θ j) := by
    intro j
    have h1 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-y * θ j - m)) (Real.exp_pos m).le
    have h2 : Real.exp m * Real.exp (-y * θ j - m) = Real.exp (-y * θ j) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h2] at h1
    exact h1
  have h_sum : ∑ j : Fin n, (Real.exp m * (-y * θ j - m + 1)) ≤ ∑ j : Fin n, Real.exp (-y * θ j) :=
    Finset.sum_le_sum (fun j _ => h_exp_term j)
  rw [← Finset.mul_sum] at h_sum
  have h_inner : ∑ j : Fin n, (-y * θ j - m + 1) = (n : ℝ) := by
    have h1 : ∑ j : Fin n, (-y * θ j - m + 1) = (∑ j : Fin n, -y * θ j) + ∑ j : Fin n, (1 - m) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1]
    rw [← Finset.mul_sum]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    rw [hm_def]
    field_simp
    ring
  rw [h_inner] at h_sum
  have h_exp_le : Real.exp m ≤ S := by
    rw [hS_def]
    calc
      Real.exp m = Real.exp m * (n : ℝ) * (1 / (n : ℝ)) := by
        rw [mul_assoc, mul_one_div_cancel hn_ne, mul_one]
      _ ≤ (∑ j : Fin n, Real.exp (-y * θ j)) * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right h_sum (one_div_nonneg.mpr hn_pos.le)
      _ = 1 / (n : ℝ) * ∑ j : Fin n, Real.exp (-y * θ j) := by ring
  have hm_le_log : m ≤ Real.log S := (Real.le_log_iff_exp_le hS_pos).mpr h_exp_le
  have h_neg : -Real.log S ≤ -m := neg_le_neg hm_le_log
  rw [hm_def] at h_neg
  have h_cancel : -(- (y * (∑ j, θ j) / (n : ℝ))) = y * (∑ j, θ j) / (n : ℝ) := neg_neg _
  rw [h_cancel] at h_neg
  exact h_neg
