import AFTD.Prelude
import AFTD.Kb.Tcs.IsFactorCritical
import AFTD.Kb.Tcs.OddCycleIsFactorCritical
import AFTD.Kb.Tcs.IsMinimalFactorCritical

/-!
# odd_cycle_is_minimal_factor_critical

Topic: graphs   Node: 06d9960075ea

Provenance: helper lemma. arXiv:2611.09072 Claw-free minimal factor-critical and bicritical graphs, proof of Theorem 1.4

For every integer n ≥ 1, the odd cycle graph C_{2n+1} is minimal factor-critical.
-/

theorem odd_cycle_is_minimal_factor_critical_adj_iff (n : ℕ) (hn : 1 ≤ n) (u v : Fin (2 * n + 1)) :
    (SimpleGraph.cycleGraph (2 * n + 1)).Adj u v ↔ v = u - 1 ∨ v = u + 1 := by
  rw [SimpleGraph.cycleGraph_adj']
  constructor
  · rintro (h | h)
    · left
      have : u - v = 1 := by
        apply Fin.ext
        rw [h]
        exact (odd_cycle_is_factor_critical_one_val hn).symm
      rw [← this]
      abel
    · right
      have : v - u = 1 := by
        apply Fin.ext
        rw [h]
        exact (odd_cycle_is_factor_critical_one_val hn).symm
      rw [← this]
      abel
  · rintro (rfl | rfl)
    · left
      have : u - (u - 1) = 1 := by abel
      rw [this]
      exact odd_cycle_is_factor_critical_one_val hn
    · right
      have : u + 1 - u = 1 := by abel
      rw [this]
      exact odd_cycle_is_factor_critical_one_val hn

theorem odd_cycle_is_minimal_factor_critical_ne_sub_one (n : ℕ) (hn : 1 ≤ n) (u : Fin (2 * n + 1)) : u ≠ u - 1 := by
  intro h
  have h1 : (1 : Fin (2 * n + 1)) = 0 := by
    have : u - (u - 1) = 1 := by abel
    rw [← this, ← h, sub_self]
  have h2 := congrArg Fin.val h1
  rw [odd_cycle_is_factor_critical_one_val hn] at h2
  cases h2

theorem odd_cycle_is_minimal_factor_critical_ne_add_one (n : ℕ) (hn : 1 ≤ n) (u : Fin (2 * n + 1)) : u ≠ u + 1 := by
  intro h
  have h1 : (1 : Fin (2 * n + 1)) = 0 := by
    have : (u + 1) - u = 1 := by abel
    rw [← this, ← h, sub_self]
  have h2 := congrArg Fin.val h1
  rw [odd_cycle_is_factor_critical_one_val hn] at h2
  cases h2

/-- The odd cycle graph C_{2n+1} is minimal factor-critical for any n ≥ 1. -/
theorem odd_cycle_is_minimal_factor_critical (n : ℕ) (hn : 1 ≤ n) :
    IsMinimalFactorCritical (SimpleGraph.cycleGraph (2 * n + 1)) := by
  refine ⟨odd_cycle_is_factor_critical n hn, ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | hf x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    have hy : y = x - 1 ∨ y = x + 1 := (odd_cycle_is_minimal_factor_critical_adj_iff n hn x y).mp he
    rcases hy with rfl | rfl
    · intro hFC
      have huv : x ≠ x + 1 := odd_cycle_is_minimal_factor_critical_ne_add_one n hn x
      have h_iso : ∀ w, (SimpleGraph.deleteEdges (SimpleGraph.cycleGraph (2 * n + 1)) {s(x, x - 1)}).Adj x w → w = x + 1 := by
        intro w hw
        rw [SimpleGraph.deleteEdges_adj] at hw
        have hw_adj := (odd_cycle_is_minimal_factor_critical_adj_iff n hn x w).mp hw.1
        rcases hw_adj with rfl | rfl
        · exfalso
          apply hw.2
          exact Set.mem_singleton _
        · rfl
      have h_ex := hFC (x + 1)
      obtain ⟨M, hM⟩ := h_ex
      rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
      obtain ⟨w, hw, -⟩ := hM ⟨x, huv⟩
      have hadj := M.adj_sub hw
      rw [SimpleGraph.induce_adj] at hadj
      have hw_eq := h_iso w.1 hadj
      exact w.2 (by simp [hw_eq])
    · intro hFC
      have huv : x ≠ x - 1 := odd_cycle_is_minimal_factor_critical_ne_sub_one n hn x
      have h_iso : ∀ w, (SimpleGraph.deleteEdges (SimpleGraph.cycleGraph (2 * n + 1)) {s(x, x + 1)}).Adj x w → w = x - 1 := by
        intro w hw
        rw [SimpleGraph.deleteEdges_adj] at hw
        have hw_adj := (odd_cycle_is_minimal_factor_critical_adj_iff n hn x w).mp hw.1
        rcases hw_adj with rfl | rfl
        · rfl
        · exfalso
          apply hw.2
          exact Set.mem_singleton _
      have h_ex := hFC (x - 1)
      obtain ⟨M, hM⟩ := h_ex
      rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
      obtain ⟨w, hw, -⟩ := hM ⟨x, huv⟩
      have hadj := M.adj_sub hw
      rw [SimpleGraph.induce_adj] at hadj
      have hw_eq := h_iso w.1 hadj
      exact w.2 (by simp [hw_eq])
