import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphApexOverBidirectedComplete
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_apex_over_bidirected_complete_out_degree

Topic: graphs   Node: 0f1789a3b885

Provenance: helper lemma. Lemma for digraph_min_cut_additive_bound_fails_for_every_d; arXiv:2610.21381 (Optimally large cuts in both directions), Sec. 6.

Every vertex of D_d has outdegree at least d.
-/

theorem digraph_apex_over_bidirected_complete_out_degree (d : ℕ)
    [DecidableRel (digraph_apex_over_bidirected_complete d).Adj] (v : Fin (d + 2)) :
    d ≤ (Finset.univ.filter ((digraph_apex_over_bidirected_complete d).Adj v)).card := by
  have hsub : (Finset.univ.erase v).erase (Fin.last (d + 1)) ⊆
      Finset.univ.filter ((digraph_apex_over_bidirected_complete d).Adj v) := by
    intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hw.2 h.symm, hw.1⟩
  refine le_trans ?_ (Finset.card_le_card hsub)
  have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase v) (a := Fin.last (d + 1))
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at h1
  omega
