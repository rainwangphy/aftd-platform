import AFTD.Prelude
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope
import AFTD.Kb.Tcs.ForestCarpoolFibonacciGrowth

/-!
# forest_carpool_envelope_exp

Topic: online_algorithms   Node: a45c0c0fe9cc

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

At every positive integer level, the Fibonacci tail envelope is at most exp(-(log 2 / 4) times 2 to the power of half the level).
-/

theorem forest_carpool_envelope_exp (D : ℕ) (hD : 1 ≤ D) :
    forest_carpool_tail_envelope D ≤
      Real.exp (-(Real.log 2 / 4) * (2 : ℝ) ^ ((D : ℝ) / 2)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hU : forest_carpool_tail_envelope D ≤ (1 / 2 : ℝ) ^ Nat.fib D := by
    unfold forest_carpool_tail_envelope
    split_ifs with h
    · subst D
      norm_num [Nat.fib]
    · rfl
  have hpow : (1 / 2 : ℝ) ^ Nat.fib D =
      Real.exp (-Real.log 2 * (Nat.fib D : ℝ)) := by
    calc
      _ = (1 / 2 : ℝ) ^ ((Nat.fib D : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = Real.exp (Real.log (1 / 2 : ℝ) * (Nat.fib D : ℝ)) :=
        Real.rpow_def_of_pos (by norm_num) _
      _ = _ := by rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]]
  have hz : 0 ≤ (2 : ℝ) ^ ((D : ℝ) / 2) := by positivity
  have hfib : (2 : ℝ) ^ ((D : ℝ) / 2) / 4 ≤ (Nat.fib D : ℝ) := by
    by_cases h1 : D = 1
    · subst D
      have hr := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 : ℝ) / 2 ≤ 1 by norm_num)
      norm_num [Nat.fib, Real.rpow_one] at hr ⊢ <;> linarith
    · have h2 : 2 ≤ D := by omega
      have hg := forest_carpool_fibonacci_growth D h2
      have he : (((D : ℝ) - 2) / 2) = (D : ℝ) / 2 - 1 := by ring
      rw [he, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one] at hg
      linarith
  have hmul := mul_le_mul_of_nonneg_left hfib (le_of_lt hlog)
  have hexp : -Real.log 2 * (Nat.fib D : ℝ) ≤
      -(Real.log 2 / 4) * (2 : ℝ) ^ ((D : ℝ) / 2) := by nlinarith
  calc
    _ ≤ (1 / 2 : ℝ) ^ Nat.fib D := hU
    _ = Real.exp (-Real.log 2 * (Nat.fib D : ℝ)) := hpow
    _ ≤ _ := Real.exp_le_exp.mpr hexp
