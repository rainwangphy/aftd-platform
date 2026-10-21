import AFTD.Prelude
import AFTD.Kb.Tcs.FifoQueue
import AFTD.Kb.Tcs.FifoRank
import AFTD.Kb.Tcs.RankPotential

/-!
# rank_potential_offline_evict_hole_bound

Topic: online_algorithms   Node: 96e114162a86

Provenance: formalization of a published result. Source: arXiv:2610.18767 Lemma 3.3(ii)

At an offline fetch, if the evicted page is outside the online cache, the change in rank potential is at most 0 (Lemma 3.3(ii)).
-/

/-- Potential change is at most 0 when offline evicts a hole of online cache. -/
theorem rank_potential_offline_evict_hole_bound {α : Type*} [DecidableEq α] {k : ℕ} (q : FifoQueue α k) (cOpt : Finset α) (p_in p_out : α) (h_out : p_out ∉ q.pages) : (rank_potential q (insert p_in (cOpt.erase p_out)) : ℤ) - (rank_potential q cOpt : ℤ) ≤ 0 := by
  have h_sub : q.pages.toFinset \ insert p_in (cOpt.erase p_out) ⊆ q.pages.toFinset \ cOpt := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    refine ⟨hx.1, ?_⟩
    intro h_cOpt
    have h_not_in : x ∉ insert p_in (cOpt.erase p_out) := hx.2
    rw [Finset.mem_insert, not_or] at h_not_in
    have h_not_erase : x ∉ cOpt.erase p_out := h_not_in.2
    rw [Finset.mem_erase, not_and] at h_not_erase
    have h_x_eq : x = p_out := by
      by_contra h_ne
      exact h_not_erase h_ne h_cOpt
    have h_x_in : x ∈ q.pages := List.mem_toFinset.mp hx.1
    rw [h_x_eq] at h_x_in
    exact h_out h_x_in
  have h_le : rank_potential q (insert p_in (cOpt.erase p_out)) ≤ rank_potential q cOpt := by
    unfold rank_potential
    exact Finset.sum_le_sum_of_subset h_sub
  omega
