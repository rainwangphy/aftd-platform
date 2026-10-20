import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphOutCount
import AFTD.Kb.Tcs.DigraphCommonOutCount

/-!
# regular_tournament_five_nearly_doubly_regular

Topic: graphs   Node: 14204e572e2c

Provenance: formalization of a published result. Source: arXiv:2610.25886 (Extremal arborescences in graph orientations), Conjecture 6.1; the order 5 case, checked by computation in the paper

The case k = 1 of the conjecture, in a stronger form: every regular tournament of order 5 is nearly doubly regular (any two distinct vertices have at most one common out-neighbour), so in particular every maximizer is.
-/

theorem regular_tournament_five_nearly_doubly_regular (D : Digraph (Fin 5))
    [DecidableRel D.Adj] (hD : digraph_is_tournament D)
    (hreg : ∀ v, digraph_out_count D v = 2) :
    ∀ i j, i ≠ j → digraph_common_out_count D i j = 0 ∨ digraph_common_out_count D i j = 1 := by
  intro i j hij
  have hsub_i : (Finset.filter (fun v => D.Adj i v ∧ D.Adj j v) Finset.univ) ⊆
      (Finset.filter (fun w => D.Adj i w) Finset.univ) := by
    intro w hw; rw [Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.1⟩
  have hsub_j : (Finset.filter (fun v => D.Adj i v ∧ D.Adj j v) Finset.univ) ⊆
      (Finset.filter (fun w => D.Adj j w) Finset.univ) := by
    intro w hw; rw [Finset.mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.2⟩
  have hle : digraph_common_out_count D i j ≤ 2 := by
    have h1 := Finset.card_le_card hsub_i
    have h2 := hreg i
    exact h1.trans_eq h2
  have hcases : digraph_common_out_count D i j = 0 ∨
                digraph_common_out_count D i j = 1 ∨
                digraph_common_out_count D i j = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · left; exact h0
  · right; exact h1
  · exfalso
    have hcard_comm : (Finset.filter (fun v => D.Adj i v ∧ D.Adj j v) Finset.univ).card = 2 := h2
    have hcard_i : (Finset.filter (fun w => D.Adj i w) Finset.univ).card = 2 := hreg i
    have hcard_j : (Finset.filter (fun w => D.Adj j w) Finset.univ).card = 2 := hreg j
    have heq_i : (Finset.filter (fun v => D.Adj i v ∧ D.Adj j v) Finset.univ) =
        (Finset.filter (fun w => D.Adj i w) Finset.univ) := by
      apply Finset.eq_of_subset_of_card_le hsub_i
      rw [hcard_comm, hcard_i]
    have heq_j : (Finset.filter (fun v => D.Adj i v ∧ D.Adj j v) Finset.univ) =
        (Finset.filter (fun w => D.Adj j w) Finset.univ) := by
      apply Finset.eq_of_subset_of_card_le hsub_j
      rw [hcard_comm, hcard_j]
    have hij_eq : (Finset.filter (fun w => D.Adj i w) Finset.univ) =
        (Finset.filter (fun w => D.Adj j w) Finset.univ) := by
      rw [← heq_i, ← heq_j]
    have htourn := hD.2 i j hij
    by_cases hadj : D.Adj i j
    · have hj_in_i : j ∈ Finset.filter (fun w => D.Adj i w) Finset.univ := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ j, hadj⟩
      rw [hij_eq] at hj_in_i
      rw [Finset.mem_filter] at hj_in_i
      exact hD.1 j hj_in_i.2
    · have h_ji : D.Adj j i := by
        by_contra h_not_ji
        apply hadj
        rwa [htourn]
      have hi_in_j : i ∈ Finset.filter (fun w => D.Adj j w) Finset.univ := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, h_ji⟩
      rw [← hij_eq] at hi_in_j
      rw [Finset.mem_filter] at hi_in_j
      exact hD.1 i hi_in_j.2
