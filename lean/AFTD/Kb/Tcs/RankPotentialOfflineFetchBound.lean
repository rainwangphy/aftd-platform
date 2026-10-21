import AFTD.Prelude
import AFTD.Kb.Tcs.FifoQueue
import AFTD.Kb.Tcs.FifoRank
import AFTD.Kb.Tcs.RankPotential
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# rank_potential_offline_fetch_bound

Topic: online_algorithms   Node: 6ce359c9e1bc

Provenance: formalization of a published result. Source: arXiv:2610.18767 Lemma 3.3(i)

At an offline fetch, the increase in rank potential is at most k (Lemma 3.3(i)).
-/

lemma rank_potential_offline_fetch_bound_aux {α : Type*} [DecidableEq α] {k : ℕ}
    (q : FifoQueue α k) (cOpt : Finset α) (p_in p_out : α) :
    rank_potential q (insert p_in (cOpt.erase p_out)) ≤ rank_potential q cOpt + fifo_rank q p_out := by
  unfold rank_potential
  have hsub : q.pages.toFinset \ insert p_in (cOpt.erase p_out) ⊆
      insert p_out (q.pages.toFinset \ cOpt) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase] at hx ⊢
    tauto
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)) ?_
  by_cases h : p_out ∈ q.pages.toFinset \ cOpt
  · rw [Finset.insert_eq_of_mem h]
    exact Nat.le_add_right _ _
  · rw [Finset.sum_insert h]
    omega

/-- Potential increase at an offline fetch is at most k. -/
theorem rank_potential_offline_fetch_bound {α : Type*} [DecidableEq α] {k : ℕ} (q : FifoQueue α k) (cOpt : Finset α) (p_in p_out : α) : (rank_potential q (insert p_in (cOpt.erase p_out)) : ℤ) - (rank_potential q cOpt : ℤ) ≤ (k : ℤ) := by
  have h1 := rank_potential_offline_fetch_bound_aux q cOpt p_in p_out
  have h2 : fifo_rank q p_out ≤ k := by
    unfold fifo_rank
    split
    next h =>
      have h1 := List.idxOf_lt_length_iff.mpr h
      have h2 := q.length_eq
      omega
    next h => exact Nat.zero_le _
  have h3 : rank_potential q (insert p_in (cOpt.erase p_out)) ≤ rank_potential q cOpt + k := by omega
  have h4 : (rank_potential q (insert p_in (cOpt.erase p_out)) : ℤ) ≤ (rank_potential q cOpt : ℤ) + (k : ℤ) := by
    have := Nat.cast_le (α := ℤ).mpr h3
    push_cast at this
    linarith
  linarith
