import AFTD.Prelude
import AFTD.Kb.Tcs.KstCodeMaxDensity
import AFTD.Kb.Tcs.K22CodeMaxDensityLe

/-!
# four_cycle_graph_code_asymptotic_density_eventually_le

Topic: combinatorics   Node: a7813a21a5dd

Provenance: formalization of a published result. Source: arXiv:2301.13305, Proposition 1.5; arXiv:2610.35136, Proposition 3.1

For every real number ε > 0, for eventually all natural numbers n in Filter.atTop, (n : ℝ) * kst_code_max_density 2 2 n ≤ 1 + ε.
-/

/-- For every ε > 0, eventually n * kst_code_max_density 2 2 n ≤ 1 + ε as n tends to infinity. -/
theorem four_cycle_graph_code_asymptotic_density_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) * kst_code_max_density 2 2 n ≤ 1 + ε := by
  rw [Filter.eventually_atTop]
  use ⌈2 / ε⌉₊ + 4
  intro n hn
  have hn4 : 4 ≤ n := by omega
  have h_le : kst_code_max_density 2 2 n ≤ 1 / ((n : ℝ) - 2) := k22_code_max_density_le n hn4
  have h_mul : (n : ℝ) * kst_code_max_density 2 2 n ≤ (n : ℝ) * (1 / ((n : ℝ) - 2)) :=
    mul_le_mul_of_nonneg_left h_le (Nat.cast_nonneg n)
  apply h_mul.trans
  have h_ceil : 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil (2 / ε)
  have hn_cast : (⌈2 / ε⌉₊ : ℝ) + 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have h_pos : 0 < (n : ℝ) - 2 := by
    have : 0 < 2 / ε := div_pos (by norm_num) hε
    linarith
  have h1 : 2 / ε ≤ (n : ℝ) - 2 := by linarith
  have h2 : 2 ≤ ((n : ℝ) - 2) * ε := by
    calc
      2 = (2 / ε) * ε := (div_mul_cancel₀ 2 (ne_of_gt hε)).symm
      _ ≤ ((n : ℝ) - 2) * ε := mul_le_mul_of_nonneg_right h1 (le_of_lt hε)
  have h3 : (n : ℝ) ≤ (1 + ε) * ((n : ℝ) - 2) := by
    calc
      (n : ℝ) = ((n : ℝ) - 2) + 2 := by ring
      _ ≤ ((n : ℝ) - 2) + ((n : ℝ) - 2) * ε := by linarith
      _ = (1 + ε) * ((n : ℝ) - 2) := by ring
  have h4 : (n : ℝ) / ((n : ℝ) - 2) ≤ 1 + ε := (div_le_iff₀ h_pos).mpr h3
  have h5 : (n : ℝ) * (1 / ((n : ℝ) - 2)) = (n : ℝ) / ((n : ℝ) - 2) := mul_one_div (n : ℝ) ((n : ℝ) - 2)
  linarith
