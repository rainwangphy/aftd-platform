import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionCharacteristic

/-!
# redistribution_characteristic_upper_norm

Topic: mechanism_design   Node: c489fa83a6c1

Provenance: helper lemma. Routine finite-characteristic-function helper for IN-251, arXiv:2610.10995 Lemma4.3 Steps1/2 and equation12. These statements do not assert the half-plane boundary integral inequality or the main harmonic error bound. No research advance.

For nonnegative reports, the empirical characteristic function has norm at most one on the closed upper half-plane. Only nonemptiness of the profile and report nonnegativity are assumed.
-/

open Finset MeasureTheory

theorem redistribution_characteristic_upper_norm {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (hθ : ∀ j, 0 ≤ θ j) (z : ℂ) (hz : 0 ≤ z.im) :
    ‖redistribution_characteristic θ z‖ ≤ 1 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ j : Fin n, ‖Complex.exp (Complex.I * z * ((θ j : ℝ) : ℂ))‖ ≤ 1 := by
    intro j
    rw [Complex.norm_exp]
    have hre : (Complex.I * z * ((θ j : ℝ) : ℂ)).re = -z.im * θ j := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre, Real.exp_le_one_iff]
    nlinarith [hz, hθ j]
  have hsum : ‖∑ j : Fin n, Complex.exp (Complex.I * z * ((θ j : ℝ) : ℂ))‖ ≤ n := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ j : Fin n, ‖Complex.exp (Complex.I * z * ((θ j : ℝ) : ℂ))‖
        ≤ ∑ _j : Fin n, (1:ℝ) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = n := by simp
  rw [redistribution_characteristic, norm_mul]
  have hnorm : ‖(1 / (n : ℂ))‖ = 1 / (n:ℝ) := by simp
  rw [hnorm]
  have hpos : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
  calc (1 / (n:ℝ)) * _
      ≤ (1 / (n:ℝ)) * n := mul_le_mul_of_nonneg_left hsum hpos
    _ = 1 := by field_simp
