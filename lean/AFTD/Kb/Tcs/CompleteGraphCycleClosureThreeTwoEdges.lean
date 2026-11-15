import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteGraphCycleClosure
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# complete_graph_cycle_closure_three_two_edges

Topic: graphs   Node: 4503ee19c85b

Provenance: helper lemma. sanity lemma for complete_graph_cycle_closure

In the cycle matroid of K_3, any two edges span the third: the closure of the complement of one edge is the whole edge set.
-/

lemma complete_graph_cycle_closure_three_two_edges_mem_closure (n : ℕ) (F : Set (⊤ : SimpleGraph (Fin n)).edgeSet)
    (x : (⊤ : SimpleGraph (Fin n)).edgeSet) (hx : x ∈ F) :
    x ∈ complete_graph_cycle_closure n F := by
  obtain ⟨u, v, h_eq⟩ : ∃ u v, x.val = s(u, v) := by
    induction x.val using Sym2.inductionOn with
    | hf u v => exact ⟨u, v, rfl⟩
  have hu_ne_v : u ≠ v := by
    have hx_prop := x.prop
    rw [h_eq] at hx_prop
    simp only [SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at hx_prop
    exact hx_prop
  refine ⟨u, v, h_eq, ?_⟩
  apply SimpleGraph.Adj.reachable
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨⟨x, hx, h_eq.symm ▸ rfl⟩, hu_ne_v⟩

theorem complete_graph_cycle_closure_three_two_edges (e : (⊤ : SimpleGraph (Fin 3)).edgeSet) :
    complete_graph_cycle_closure 3 {e}ᶜ = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  by_cases hx : x = e
  · rcases hx with rfl
    fin_cases x
    · dsimp only
      simp only [complete_graph_cycle_closure, Set.mem_ofPred_eq]
      refine ⟨0, 1, rfl, ?_⟩
      apply SimpleGraph.Reachable.trans (v := 2)
      · apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨⟨⟨s(0, 2), by decide⟩, ?_, rfl⟩, by decide⟩
        simp
      · apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨⟨⟨s(1, 2), by decide⟩, ?_, Sym2.eq_swap⟩, by decide⟩
        simp
    · dsimp only
      simp only [complete_graph_cycle_closure, Set.mem_ofPred_eq]
      refine ⟨0, 2, rfl, ?_⟩
      apply SimpleGraph.Reachable.trans (v := 1)
      · apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨⟨⟨s(0, 1), by decide⟩, ?_, rfl⟩, by decide⟩
        simp
      · apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨⟨⟨s(1, 2), by decide⟩, ?_, rfl⟩, by decide⟩
        simp
    · dsimp only
      simp only [complete_graph_cycle_closure, Set.mem_ofPred_eq]
      refine ⟨1, 2, rfl, ?_⟩
      apply SimpleGraph.Reachable.trans (v := 0)
      · apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨⟨⟨s(0, 1), by decide⟩, ?_, Sym2.eq_swap⟩, by decide⟩
        simp
      · apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨⟨⟨s(0, 2), by decide⟩, ?_, rfl⟩, by decide⟩
        simp
  · exact complete_graph_cycle_closure_three_two_edges_mem_closure 3 {e}ᶜ x hx
