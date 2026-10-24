import AFTD.Prelude
import AFTD.Kb.Tcs.PrefixReversal

/-!
# not_prefix_reversal_sum_bound_necessary

Topic: combinatorics   Node: c4ba6f84e6d1

Provenance: original. Related work: refutes `prefix_reversal_sum_bound_necessary`

The statement `prefix_reversal_sum_bound_necessary` is false: The statement claims that m + k ≥ n + 1 is a necessary condition for prefix reversals of lengths k, m, n to generate S_n. However, for (k, m, n) = (2, 3, 5), the prefix reversals of lengths 2, 3, 5 generate the entire symmetric group S_5 (order 120), yet m + k = 5 < 6 = n + 1. Further counterexamples include (k, m, n) = (2, 4, 7), (3, 4, 7), (2, 5, 7), (2, 7, 9), (4, 6, 11), (5, 6, 11), (4, 7, 11), (3, 8, 11), (2, 9, 11).
-/

theorem not_prefix_reversal_sum_bound_necessary : ¬ (∀ (k m n : ℕ)
    (hk : 2 ≤ k) (hkm : k < m) (hmn : m < n)
    (hgen : Subgroup.closure {prefixReversal n k, prefixReversal n m, prefixReversal n n} = ⊤), m + k ≥ n + 1) := by
  intro h
  have g5_eq_top : Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5} = (⊤ : Subgroup (Equiv.Perm (Fin 5))) := by
    open Equiv Perm in
    have ha : prefixReversal 5 2 ∈ Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5} :=
      Subgroup.subset_closure (by simp)
    have hb : prefixReversal 5 3 ∈ Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5} :=
      Subgroup.subset_closure (by simp)
    have hc : prefixReversal 5 5 ∈ Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5} :=
      Subgroup.subset_closure (by simp)
    have ht0 : swap 0 1 ∈ Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5} := by
      have : prefixReversal 5 2 = swap 0 1 := by decide
      rwa [← this]
    have ht1 : swap 1 2 ∈ Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5} := by
      have : prefixReversal 5 2 * prefixReversal 5 3 * prefixReversal 5 2 = swap 1 2 := by decide
      rw [← this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha
    have ht2 : swap 2 3 ∈ Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5} := by
      have : prefixReversal 5 5 * (prefixReversal 5 2 * prefixReversal 5 3 * prefixReversal 5 2) * prefixReversal 5 5 = swap 2 3 := by decide
      rw [← this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha)) hc
    have ht3 : swap 3 4 ∈ Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5} := by
      have : prefixReversal 5 5 * prefixReversal 5 2 * prefixReversal 5 5 = swap 3 4 := by decide
      rw [← this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc ha) hc
    have hrange : Set.range (fun i : Fin 4 => swap i.castSucc i.succ) ⊆
        ((Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5}).toSubmonoid : Set (Perm (Fin 5))) := by
      intro x hx
      rcases hx with ⟨⟨i, hi⟩, rfl⟩
      interval_cases i
      · exact ht0
      · exact ht1
      · exact ht2
      · exact ht3
    have htopM : (Subgroup.closure {prefixReversal 5 2, prefixReversal 5 3, prefixReversal 5 5}).toSubmonoid = ⊤ := by
      rw [eq_top_iff, ← mclosure_swap_castSucc_succ 4, Submonoid.closure_le]
      exact hrange
    ext x
    simp [← Subgroup.mem_toSubmonoid, htopM]
  have hfalse := h 2 3 5 (by omega) (by omega) (by omega) g5_eq_top
  omega
