import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwRatio
import AFTD.Kb.Tcs.ParallelMwTransfer
import AFTD.Kb.Tcs.ElemSymm
import AFTD.Kb.Tcs.ParallelMwStar
import AFTD.Kb.Tcs.ParallelMwAlpha
import AFTD.Kb.Tcs.ParallelMwTau

/-!
# parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant

Topic: combinatorics   Node: 3019b35696bd

Provenance: original. Related work: OP-670; Experiment 9588

For any natural number n ≥ 3, any function q : Fin n → ℕ with 0 < q k for all k : Fin n, and any indices i, j : Fin n with q i + 2 ≤ q j, parallel_mw_ratio 1 (parallel_mw_transfer q i j) = parallel_mw_ratio 1 q.
-/

open Finset

lemma parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_sum_elem_symm {n : ℕ} (v : Fin n → ℝ) :
    (∑ k ∈ range (n + 1), elem_symm k v) = ∏ i : Fin n, (1 + v i) := by
  unfold elem_symm
  rw [prod_one_add univ]
  have h_biUnion := powerset_card_biUnion (univ : Finset (Fin n))
  have hc : (univ : Finset (Fin n)).card = n := card_fin n
  rw [hc] at h_biUnion
  rw [h_biUnion]
  have h_disj : (↑(range (n + 1)) : Set ℕ).PairwiseDisjoint (fun i => powersetCard i (univ : Finset (Fin n))) := by
    intro a _ b _ hab
    rw [Function.onFun, disjoint_iff_ne]
    intro x hx y hy hxy
    rw [mem_powersetCard] at hx hy
    apply hab
    rw [← hx.2, ← hy.2, hxy]
  rw [sum_biUnion h_disj]

lemma parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_star_one (n : ℕ) (q : Fin n → ℕ) :
    parallel_mw_star 1 q = (2 : ℝ) ^ (∑ i : Fin n, q i) - 2 := by
  have elem_symm_zero : elem_symm 0 (fun i => (2 : ℝ) ^ q i - 1) = 1 := by
    unfold elem_symm
    rw [powersetCard_zero, sum_singleton, prod_empty]
  have h_sum : (∑ k ∈ range (n + 1), elem_symm k (fun i => (2 : ℝ) ^ q i - 1)) =
      (2 : ℝ) ^ (∑ i : Fin n, q i) := by
    have h_prod := parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_sum_elem_symm (fun i => (2 : ℝ) ^ q i - 1)
    rw [h_prod]
    have h_simp : (fun i : Fin n => 1 + ((2 : ℝ) ^ q i - 1)) = fun i => (2 : ℝ) ^ q i := by
      ext i
      ring
    rw [h_simp]
    exact prod_pow_eq_pow_sum univ q 2
  unfold parallel_mw_star
  rw [sum_range_succ']
  have h_zero : (if 0 < 1 then (-1 : ℝ) ^ (1 - 0) else 1) * elem_symm 0 (fun i => (2 : ℝ) ^ q i - 1) = -1 := by
    simp [elem_symm_zero]
  have h_succ : ∀ k ∈ range n, (if k + 1 < 1 then (-1 : ℝ) ^ (1 - (k + 1)) else 1) *
      elem_symm (k + 1) (fun i => (2 : ℝ) ^ q i - 1) = elem_symm (k + 1) (fun i => (2 : ℝ) ^ q i - 1) := by
    intro k _
    have : ¬ (k + 1 < 1) := Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le k))
    simp [this]
  rw [sum_congr rfl h_succ]
  rw [h_zero]
  have h_split : (∑ k ∈ range (n + 1), elem_symm k (fun i => (2 : ℝ) ^ q i - 1)) =
      (∑ k ∈ range n, elem_symm (k + 1) (fun i => (2 : ℝ) ^ q i - 1)) + 1 := by
    rw [sum_range_succ']
    simp [elem_symm_zero]
  linarith

lemma parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_tau_one (n : ℕ) (q : Fin n → ℕ) :
    parallel_mw_tau 1 q = ∑ i : Fin n, (q i : ℝ) := by
  unfold parallel_mw_tau elem_symm
  rw [powersetCard_one]
  rw [sum_map]
  simp

lemma parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_transfer_sum {n : ℕ} (q : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hj : 1 ≤ q j) :
    ∑ k : Fin n, parallel_mw_transfer q i j k = ∑ k : Fin n, q k := by
  have hj_mem : j ∈ (univ : Finset (Fin n)) := mem_univ j
  have hi_mem : i ∈ (univ.erase j) := by
    rw [mem_erase]
    exact ⟨hij, mem_univ i⟩
  have h_split (f : Fin n → ℕ) :
      (∑ k : Fin n, f k) = f j + f i + ∑ k ∈ (univ.erase j).erase i, f k := by
    have h1 : (∑ k : Fin n, f k) = f j + ∑ k ∈ univ.erase j, f k := by
      conv_lhs => rw [← insert_erase hj_mem]
      rw [sum_insert (notMem_erase j univ)]
    have h2 : (∑ k ∈ univ.erase j, f k) = f i + ∑ k ∈ (univ.erase j).erase i, f k := by
      conv_lhs => rw [← insert_erase hi_mem]
      rw [sum_insert (notMem_erase i (univ.erase j))]
    rw [h1, h2, add_assoc]
  rw [h_split (parallel_mw_transfer q i j)]
  rw [h_split q]
  unfold parallel_mw_transfer
  have h_j : Function.update (Function.update q i (q i + 1)) j (q j - 1) j = q j - 1 := by
    simp
  have h_i : Function.update (Function.update q i (q i + 1)) j (q j - 1) i = q i + 1 := by
    simp [hij]
  have h_rest : (∑ k ∈ (univ.erase j).erase i,
      Function.update (Function.update q i (q i + 1)) j (q j - 1) k) =
      ∑ k ∈ (univ.erase j).erase i, q k := by
    refine sum_congr rfl (fun k hk => ?_)
    rw [mem_erase, mem_erase] at hk
    simp [hk.1, hk.2.1]
  rw [h_j, h_i, h_rest]
  omega

/-- At rank r = 1, the Merino-Welsh ratio is invariant under parallel-class transfers. -/
theorem parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant
    (n : ℕ) (hn : 3 ≤ n) (q : Fin n → ℕ) (hq : ∀ k, 0 < q k)
    (i j : Fin n) (hij : q i + 2 ≤ q j) :
    parallel_mw_ratio 1 (parallel_mw_transfer q i j) = parallel_mw_ratio 1 q := by
  have _ := hn
  have hne : i ≠ j := by
    rintro rfl
    omega
  have hj : 1 ≤ q j := by
    have := hq j
    omega
  have hsum : ∑ k : Fin n, parallel_mw_transfer q i j k = ∑ k : Fin n, q k :=
    parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_transfer_sum q i j hne hj
  unfold parallel_mw_ratio
  have hstar : parallel_mw_star 1 (parallel_mw_transfer q i j) = parallel_mw_star 1 q := by
    rw [parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_star_one n (parallel_mw_transfer q i j),
        parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_star_one n q, hsum]
  have htau : parallel_mw_tau 1 (parallel_mw_transfer q i j) = parallel_mw_tau 1 q := by
    rw [parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_tau_one n (parallel_mw_transfer q i j),
        parallel_uniform_merino_welsh_strict_balancing_rank_one_invariant_tau_one n q]
    exact_mod_cast hsum
  rw [hstar, htau]
