import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphApexOverBidirectedComplete
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_apex_over_bidirected_complete_edge_count

Topic: graphs   Node: f24c07b53653

Provenance: helper lemma. Lemma for digraph_min_cut_additive_bound_fails_for_every_d; arXiv:2610.21381 (Optimally large cuts in both directions), Sec. 6.

D_d has (d + 1)² arcs.
-/

theorem digraph_apex_over_bidirected_complete_edge_count (d : ℕ)
    [DecidableRel (digraph_apex_over_bidirected_complete d).Adj] :
    digraph_edge_count (digraph_apex_over_bidirected_complete d) = (d + 1) ^ 2 := by
  have hfib : ∀ v : Fin (d + 2),
      (Finset.univ.filter fun u => (digraph_apex_over_bidirected_complete d).Adj u v).card =
        if v = Fin.last (d + 1) then 0 else d + 1 := by
    intro v
    split_ifs with hv
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u _ h
      exact h.2 hv
    · have : (Finset.univ.filter fun u => (digraph_apex_over_bidirected_complete d).Adj u v) =
          Finset.univ.erase v := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
        exact ⟨fun h => h.1, fun h => ⟨h, hv⟩⟩
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
  have hbij : ∀ v : Fin (d + 2),
      ((Finset.univ.filter fun p : Fin (d + 2) × Fin (d + 2) =>
        (digraph_apex_over_bidirected_complete d).Adj p.1 p.2).filter (fun p => p.2 = v)).card =
      (Finset.univ.filter fun u => (digraph_apex_over_bidirected_complete d).Adj u v).card := by
    intro v
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [← hp.2]
      exact hp.1
    · intro p hp q hq h
      simp only [Finset.mem_filter] at hp hq
      exact Prod.ext h (hp.2.trans hq.2.symm)
    · intro u hu
      refine ⟨(u, v), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact ⟨hu, by simp⟩
  unfold digraph_edge_count
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp only [hbij, hfib]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.last (d + 1))), if_pos rfl, zero_add,
    Finset.sum_congr rfl (fun v hv => if_neg (Finset.ne_of_mem_erase hv)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [show d + 2 - 1 = d + 1 by omega]
  ring
