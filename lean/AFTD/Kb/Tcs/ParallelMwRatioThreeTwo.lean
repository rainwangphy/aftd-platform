import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwRatio
import AFTD.Kb.Tcs.ParallelMwStar
import AFTD.Kb.Tcs.ParallelMwTau
import AFTD.Kb.Tcs.ParallelMwAlpha
import AFTD.Kb.Tcs.ElemSymm

/-!
# parallel_mw_ratio_three_two

Topic: combinatorics   Node: 46109359dc87

Provenance: helper lemma. step towards parallel_uniform_merino_welsh_strict_balancing_three_two

For any profile q : Fin 3 → ℕ, parallel_mw_ratio 2 q equals 6 * (2^(q 0 + q 1 + q 2) - 2 * (2^(q 0) + 2^(q 1) + 2^(q 2)) + 6) / (q 0 * q 1 + q 0 * q 2 + q 1 * q 2)^2.
-/

lemma parallel_mw_ratio_three_two_elem_symm_zero (v : Fin 3 → ℝ) : elem_symm 0 v = 1 := by
  unfold elem_symm
  have : Finset.powersetCard 0 (Finset.univ : Finset (Fin 3)) = {∅} := by decide
  rw [this, Finset.sum_singleton, Finset.prod_empty]

lemma parallel_mw_ratio_three_two_elem_symm_one (v : Fin 3 → ℝ) : elem_symm 1 v = v 0 + v 1 + v 2 := by
  unfold elem_symm
  have : Finset.powersetCard 1 (Finset.univ : Finset (Fin 3)) = {{(0 : Fin 3)}, {1}, {2}} := by decide
  rw [this]
  have h1 : ({(0 : Fin 3)} : Finset (Fin 3)) ∉ ({{(1 : Fin 3)}, {2}} : Finset (Finset (Fin 3))) := by decide
  have h2 : ({(1 : Fin 3)} : Finset (Fin 3)) ∉ ({{(2 : Fin 3)}} : Finset (Finset (Fin 3))) := by decide
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  simp [Finset.prod_singleton]
  ring

lemma parallel_mw_ratio_three_two_elem_symm_two (v : Fin 3 → ℝ) : elem_symm 2 v = v 0 * v 1 + v 0 * v 2 + v 1 * v 2 := by
  unfold elem_symm
  have : Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)) = {{(0 : Fin 3), 1}, {0, 2}, {1, 2}} := by decide
  rw [this]
  have h1 : ({(0 : Fin 3), 1} : Finset (Fin 3)) ∉ ({{(0 : Fin 3), 2}, {1, 2}} : Finset (Finset (Fin 3))) := by decide
  have h2 : ({(0 : Fin 3), 2} : Finset (Fin 3)) ∉ ({{(1 : Fin 3), 2}} : Finset (Finset (Fin 3))) := by decide
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  have p1 : ∏ i ∈ ({(0 : Fin 3), 1} : Finset (Fin 3)), v i = v 0 * v 1 := by
    have : (0 : Fin 3) ∉ ({(1 : Fin 3)} : Finset (Fin 3)) := by decide
    rw [Finset.prod_insert this, Finset.prod_singleton]
  have p2 : ∏ i ∈ ({(0 : Fin 3), 2} : Finset (Fin 3)), v i = v 0 * v 2 := by
    have : (0 : Fin 3) ∉ ({(2 : Fin 3)} : Finset (Fin 3)) := by decide
    rw [Finset.prod_insert this, Finset.prod_singleton]
  have p3 : ∏ i ∈ ({(1 : Fin 3), 2} : Finset (Fin 3)), v i = v 1 * v 2 := by
    have : (1 : Fin 3) ∉ ({(2 : Fin 3)} : Finset (Fin 3)) := by decide
    rw [Finset.prod_insert this, Finset.prod_singleton]
  rw [p1, p2, p3]
  ring

lemma parallel_mw_ratio_three_two_elem_symm_three (v : Fin 3 → ℝ) : elem_symm 3 v = v 0 * v 1 * v 2 := by
  unfold elem_symm
  have : Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)) = {{(0 : Fin 3), 1, 2}} := by decide
  rw [this, Finset.sum_singleton]
  have h0 : (0 : Fin 3) ∉ ({(1 : Fin 3), 2} : Finset (Fin 3)) := by decide
  have h1 : (1 : Fin 3) ∉ ({(2 : Fin 3)} : Finset (Fin 3)) := by decide
  rw [Finset.prod_insert h0, Finset.prod_insert h1, Finset.prod_singleton]
  ring

lemma parallel_mw_ratio_three_two_alpha : parallel_mw_alpha 3 2 = 6 := by
  unfold parallel_mw_alpha
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma parallel_mw_ratio_three_two_star (q : Fin 3 → ℕ) :
    parallel_mw_star 2 q =
      (2 : ℝ) ^ (q 0 + q 1 + q 2) - 2 * ((2 : ℝ) ^ q 0 + (2 : ℝ) ^ q 1 + (2 : ℝ) ^ q 2) + 6 := by
  unfold parallel_mw_star
  have h4 : 3 + 1 = 4 := rfl
  rw [h4]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add]
  have e0 := parallel_mw_ratio_three_two_elem_symm_zero (fun i => (2 : ℝ) ^ q i - 1)
  have e1 := parallel_mw_ratio_three_two_elem_symm_one (fun i => (2 : ℝ) ^ q i - 1)
  have e2 := parallel_mw_ratio_three_two_elem_symm_two (fun i => (2 : ℝ) ^ q i - 1)
  have e3 := parallel_mw_ratio_three_two_elem_symm_three (fun i => (2 : ℝ) ^ q i - 1)
  rw [e0, e1, e2, e3]
  have hpow : (2 : ℝ) ^ (q 0 + q 1 + q 2) = (2 : ℝ) ^ q 0 * (2 : ℝ) ^ q 1 * (2 : ℝ) ^ q 2 := by
    rw [pow_add, pow_add]
  rw [hpow]
  norm_num
  ring

lemma parallel_mw_ratio_three_two_tau (q : Fin 3 → ℕ) :
    parallel_mw_tau 2 q = (q 0 : ℝ) * q 1 + (q 0 : ℝ) * q 2 + (q 1 : ℝ) * q 2 := by
  unfold parallel_mw_tau
  exact parallel_mw_ratio_three_two_elem_symm_two (fun i => (q i : ℝ))

/-- Closed-form coordinate representation of the Merino-Welsh ratio for n = 3 and r = 2. -/
theorem parallel_mw_ratio_three_two (q : Fin 3 → ℕ) :
    parallel_mw_ratio 2 q =
      6 * ((2 : ℝ) ^ (q 0 + q 1 + q 2) - 2 * ((2 : ℝ) ^ q 0 + (2 : ℝ) ^ q 1 + (2 : ℝ) ^ q 2) + 6) /
      ((q 0 : ℝ) * q 1 + (q 0 : ℝ) * q 2 + (q 1 : ℝ) * q 2) ^ 2 := by
  unfold parallel_mw_ratio
  rw [parallel_mw_ratio_three_two_alpha, parallel_mw_ratio_three_two_star, parallel_mw_ratio_three_two_tau]
