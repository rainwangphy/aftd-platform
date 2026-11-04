import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphKernelPerfectSubsetQuasikernelCover

/-!
# digraph_two_kernel_perfect_sets_weighted_half_cover

Topic: graphs   Node: 5a7204676cb5

Provenance: helper lemma. Immediate weighted consequence of Lemma 14 of https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i2p53/pdf/, with arcs reversed.

If nonnegative integer vertex weights are supported on the union of two kernel-perfect sets of a finite digraph, some quasi-kernel has at least half the total weight in its closed out-neighborhood.
-/

theorem digraph_two_kernel_perfect_sets_weighted_half_cover
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (w : α → ℕ) (A B : Finset α)
    (hsupport : ∀ v, w v ≠ 0 → v ∈ A ∨ v ∈ B)
    (hperfect : ∀ S ∈ ({A,B} : Finset (Finset α)),
      ∀ T : Finset α, T ⊆ S → ∃ K : Finset α, K ⊆ T ∧
        (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
        (∀ v ∈ T, ∃ u ∈ K, u = v ∨ D.Adj u v)) :
    ∃ Q : Finset α,
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ z, D.Adj u z ∧ D.Adj z v) ∧
      (∑ v ∈ Finset.univ, w v) ≤
        2 * (∑ v ∈ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v), w v) := by
  have h_union : ∑ v ∈ Finset.univ, w v ≤ (∑ v ∈ A, w v) + (∑ v ∈ B, w v) := by
    have h1 : ∑ v ∈ A ∪ B, w v = ∑ v, w v := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      by_contra hc
      exact hx (Finset.mem_union.2 (hsupport x hc))
    rw [← h1, ← Finset.sum_union_inter]
    exact Nat.le_add_right _ _
  have h_cases : (∑ v ∈ Finset.univ, w v) ≤ 2 * (∑ v ∈ A, w v) ∨
                 (∑ v ∈ Finset.univ, w v) ≤ 2 * (∑ v ∈ B, w v) := by
    omega
  rcases h_cases with hA | hB
  · have hA_perf := hperfect A (by simp)
    obtain ⟨Q, hQ1, hQ2, hQ3, -⟩ := digraph_kernel_perfect_subset_quasikernel_cover D A hA_perf
    refine ⟨Q, hQ1, hQ2, ?_⟩
    have hsub : A ⊆ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v) := by
      intro s hs
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ s, hQ3 s hs⟩
    have h_le := Finset.sum_le_sum_of_subset (f := w) hsub
    omega
  · have hB_perf := hperfect B (by simp)
    obtain ⟨Q, hQ1, hQ2, hQ3, -⟩ := digraph_kernel_perfect_subset_quasikernel_cover D B hB_perf
    refine ⟨Q, hQ1, hQ2, ?_⟩
    have hsub : B ⊆ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v) := by
      intro s hs
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ s, hQ3 s hs⟩
    have h_le := Finset.sum_le_sum_of_subset (f := w) hsub
    omega
