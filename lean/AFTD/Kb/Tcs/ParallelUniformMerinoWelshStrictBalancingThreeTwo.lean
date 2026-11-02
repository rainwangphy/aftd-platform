import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwRatio
import AFTD.Kb.Tcs.ParallelMwTransfer
import AFTD.Kb.Tcs.ParallelMwRatioThreeTwo
import AFTD.Kb.Tcs.ParallelMwRatioDecreasingTriple

/-!
# parallel_uniform_merino_welsh_strict_balancing_three_two

Topic: combinatorics   Node: 03037aeb23b3

Provenance: original. Related work: OP-670; Experiment 9590

For any function q : Fin 3 → ℕ with 0 < q i for all i : Fin 3, and any indices i, j : Fin 3 with q i + 2 ≤ q j, parallel_mw_ratio 2 (parallel_mw_transfer q i j) < parallel_mw_ratio 2 q.
-/

noncomputable def parallel_uniform_merino_welsh_strict_balancing_three_two_formula (a b c : ℕ) : ℝ :=
  6 * ((2 : ℝ) ^ (a + b + c) - 2 * ((2 : ℝ) ^ a + (2 : ℝ) ^ b + (2 : ℝ) ^ c) + 6) /
    (((a : ℝ) * b + (a : ℝ) * c + (b : ℝ) * c) ^ 2)

lemma parallel_uniform_merino_welsh_strict_balancing_three_two_swap12 (a b c : ℕ) :
    parallel_uniform_merino_welsh_strict_balancing_three_two_formula a b c =
    parallel_uniform_merino_welsh_strict_balancing_three_two_formula b a c := by
  dsimp [parallel_uniform_merino_welsh_strict_balancing_three_two_formula]
  have h1 : a + b + c = b + a + c := by omega
  have h2 : (2 : ℝ) ^ a + (2 : ℝ) ^ b + (2 : ℝ) ^ c = (2 : ℝ) ^ b + (2 : ℝ) ^ a + (2 : ℝ) ^ c := by ring
  have h3 : (a : ℝ) * b + (a : ℝ) * c + (b : ℝ) * c = (b : ℝ) * a + (b : ℝ) * c + (a : ℝ) * c := by ring
  rw [h1, h2, h3]

lemma parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (a b c : ℕ) :
    parallel_uniform_merino_welsh_strict_balancing_three_two_formula a b c =
    parallel_uniform_merino_welsh_strict_balancing_three_two_formula a c b := by
  dsimp [parallel_uniform_merino_welsh_strict_balancing_three_two_formula]
  have h1 : a + b + c = a + c + b := by omega
  have h2 : (2 : ℝ) ^ a + (2 : ℝ) ^ b + (2 : ℝ) ^ c = (2 : ℝ) ^ a + (2 : ℝ) ^ c + (2 : ℝ) ^ b := by ring
  have h3 : (a : ℝ) * b + (a : ℝ) * c + (b : ℝ) * c = (a : ℝ) * c + (a : ℝ) * b + (c : ℝ) * b := by ring
  rw [h1, h2, h3]

lemma parallel_uniform_merino_welsh_strict_balancing_three_two_swap13 (a b c : ℕ) :
    parallel_uniform_merino_welsh_strict_balancing_three_two_formula a b c =
    parallel_uniform_merino_welsh_strict_balancing_three_two_formula c b a := by
  dsimp [parallel_uniform_merino_welsh_strict_balancing_three_two_formula]
  have h1 : a + b + c = c + b + a := by omega
  have h2 : (2 : ℝ) ^ a + (2 : ℝ) ^ b + (2 : ℝ) ^ c = (2 : ℝ) ^ c + (2 : ℝ) ^ b + (2 : ℝ) ^ a := by ring
  have h3 : (a : ℝ) * b + (a : ℝ) * c + (b : ℝ) * c = (c : ℝ) * b + (c : ℝ) * a + (b : ℝ) * a := by ring
  rw [h1, h2, h3]

lemma parallel_uniform_merino_welsh_strict_balancing_three_two_decreasing (a b c : ℕ)
    (ha : 0 < a) (hij : a + 2 ≤ b) (hc : 0 < c) :
    parallel_uniform_merino_welsh_strict_balancing_three_two_formula (a + 1) (b - 1) c <
    parallel_uniform_merino_welsh_strict_balancing_three_two_formula a b c := by
  have h_add : (a + 1) + (b - 1) + c = a + b + c := by omega
  have hb : 1 ≤ b := by omega
  have h := parallel_mw_ratio_decreasing_triple a b c ha hij hc
  dsimp [parallel_uniform_merino_welsh_strict_balancing_three_two_formula]
  rw [h_add]
  push_cast [hb]
  exact h

/-- Base case n = 3, r = 2 of the strict balancing conjecture for the Merino-Welsh ratio. -/
theorem parallel_uniform_merino_welsh_strict_balancing_three_two
    (q : Fin 3 → ℕ) (hq : ∀ i, 0 < q i) (i j : Fin 3) (hij : q i + 2 ≤ q j) :
    parallel_mw_ratio 2 (parallel_mw_transfer q i j) < parallel_mw_ratio 2 q := by
  rw [parallel_mw_ratio_three_two]
  rw [parallel_mw_ratio_three_two q]
  change parallel_uniform_merino_welsh_strict_balancing_three_two_formula
           (parallel_mw_transfer q i j 0)
           (parallel_mw_transfer q i j 1)
           (parallel_mw_transfer q i j 2) <
         parallel_uniform_merino_welsh_strict_balancing_three_two_formula (q 0) (q 1) (q 2)
  have hne : i ≠ j := by rintro rfl; omega
  fin_cases i <;> fin_cases j
  · contradiction
  · -- i = 0, j = 1
    dsimp [parallel_mw_transfer]; simp
    exact parallel_uniform_merino_welsh_strict_balancing_three_two_decreasing (q 0) (q 1) (q 2) (hq 0) hij (hq 2)
  · -- i = 0, j = 2
    dsimp [parallel_mw_transfer]; simp
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (q 0 + 1) (q 1) (q 2 - 1)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (q 0) (q 1) (q 2)]
    exact parallel_uniform_merino_welsh_strict_balancing_three_two_decreasing (q 0) (q 2) (q 1) (hq 0) hij (hq 1)
  · -- i = 1, j = 0
    dsimp [parallel_mw_transfer]; simp
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap12 (q 0 - 1) (q 1 + 1) (q 2)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap12 (q 0) (q 1) (q 2)]
    exact parallel_uniform_merino_welsh_strict_balancing_three_two_decreasing (q 1) (q 0) (q 2) (hq 1) hij (hq 2)
  · contradiction
  · -- i = 1, j = 2
    dsimp [parallel_mw_transfer]; simp
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap12 (q 0) (q 1 + 1) (q 2 - 1)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (q 1 + 1) (q 0) (q 2 - 1)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap12 (q 0) (q 1) (q 2)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (q 1) (q 0) (q 2)]
    exact parallel_uniform_merino_welsh_strict_balancing_three_two_decreasing (q 1) (q 2) (q 0) (hq 1) hij (hq 0)
  · -- i = 2, j = 0
    dsimp [parallel_mw_transfer]; simp
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap13 (q 0 - 1) (q 1) (q 2 + 1)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (q 2 + 1) (q 1) (q 0 - 1)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap13 (q 0) (q 1) (q 2)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (q 2) (q 1) (q 0)]
    exact parallel_uniform_merino_welsh_strict_balancing_three_two_decreasing (q 2) (q 0) (q 1) (hq 2) hij (hq 1)
  · -- i = 2, j = 1
    dsimp [parallel_mw_transfer]; simp
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (q 0) (q 1 - 1) (q 2 + 1)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap12 (q 0) (q 2 + 1) (q 1 - 1)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap23 (q 2 + 1) (q 0) (q 1 - 1)]
    rw [parallel_uniform_merino_welsh_strict_balancing_three_two_swap13 (q 0) (q 1) (q 2)]
    exact parallel_uniform_merino_welsh_strict_balancing_three_two_decreasing (q 2) (q 1) (q 0) (hq 2) hij (hq 0)
  · contradiction
