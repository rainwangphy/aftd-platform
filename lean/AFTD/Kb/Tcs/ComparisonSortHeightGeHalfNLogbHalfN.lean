import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonSortDecisionTreeHeightGe
import AFTD.Kb.Tcs.FactorialGeHalfPowHalf

/-!
# comparison_sort_height_ge_half_n_logb_half_n

Topic: algorithms   Node: 2adde1eefbe6

For every type α, every binary tree t over α, and every natural number n, if n! ≤ t.numLeaves and 2 ≤ n, then (n/2)·log₂(n/2) ≤ t.height. The label type is arbitrary and the statement is purely combinatorial; the comparison-sort lower bound follows as a corollary but is not itself part of the Lean declaration.
-/

theorem comparison_sort_height_ge_half_n_logb_half_n_factorial_ceil (n : ℕ) :
    ((n : ℝ) / 2) ^ ((n + 1) / 2) ≤ (n.factorial : ℝ) := by
  set m := (n + 1) / 2 with hm
  have hmle : m ≤ n := by omega
  have hbase : (n + 1 - m) ^ m ≤ n.factorial := by
    have h1 : (n + 1 - m) ^ m ≤ n.descFactorial m := Nat.pow_sub_le_descFactorial n m
    have h2 : (n - m).factorial * n.descFactorial m = n.factorial :=
      Nat.factorial_mul_descFactorial hmle
    have h3 : n.descFactorial m ≤ (n - m).factorial * n.descFactorial m :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    rw [h2] at h3
    exact le_trans h1 h3
  have hcast : ((n : ℝ) / 2) ≤ ((n + 1 - m : ℕ) : ℝ) := by
    have h : n ≤ 2 * (n + 1 - m) := by omega
    have h' : (n : ℝ) ≤ 2 * ((n + 1 - m : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  calc ((n : ℝ) / 2) ^ ((n + 1) / 2) = ((n : ℝ) / 2) ^ m := by rw [hm]
    _ ≤ ((n + 1 - m : ℕ) : ℝ) ^ m := pow_le_pow_left₀ (by positivity) hcast m
    _ = ((n + 1 - m) ^ m : ℕ) := by rw [Nat.cast_pow]
    _ ≤ (n.factorial : ℝ) := by exact_mod_cast hbase

theorem comparison_sort_height_ge_half_n_logb_half_n {α : Type*} (t : BinaryTree α) (n : ℕ)
    (h : n.factorial ≤ t.numLeaves) (hn : 2 ≤ n) :
    (n : ℝ) / 2 * Real.logb 2 ((n : ℝ) / 2) ≤ (t.height : ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < (n:ℝ)/2 := by linarith
  have hhalf_ge_one : (1:ℝ) ≤ (n:ℝ)/2 := by linarith
  have hlog_nonneg : 0 ≤ Real.logb 2 ((n:ℝ)/2) := Real.logb_nonneg (by norm_num) hhalf_ge_one
  have hpow : ((n:ℝ)/2)^((n+1)/2) ≤ (2:ℝ)^t.height := by
    have hp1 := comparison_sort_height_ge_half_n_logb_half_n_factorial_ceil n
    have hp2 : (n.factorial:ℝ) ≤ (2:ℝ)^t.height := by
      exact_mod_cast comparison_sort_decision_tree_height_ge t n h
    exact hp1.trans hp2
  have hlogineq : (((n+1)/2 : ℕ) : ℝ) * Real.logb 2 ((n:ℝ)/2) ≤ (t.height:ℝ) := by
    have hb : (1:ℝ) < 2 := by norm_num
    have hx : (0:ℝ) < ((n:ℝ)/2)^((n+1)/2) := pow_pos hpos _
    have hy : (0:ℝ) < (2:ℝ)^t.height := pow_pos (by norm_num) _
    have hmono := (Real.logb_le_logb hb hx hy).mpr hpow
    rw [Real.logb_pow, Real.logb_pow] at hmono
    simpa using hmono
  have hle : (n:ℝ)/2 ≤ (((n+1)/2 : ℕ) : ℝ) := by
    have h2 : n ≤ 2 * ((n+1)/2) := by omega
    have h2R : (n:ℝ) ≤ 2 * (((n+1)/2 : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  calc (n:ℝ)/2 * Real.logb 2 ((n:ℝ)/2)
      ≤ (((n+1)/2 : ℕ) : ℝ) * Real.logb 2 ((n:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hle hlog_nonneg
    _ ≤ (t.height:ℝ) := hlogineq
