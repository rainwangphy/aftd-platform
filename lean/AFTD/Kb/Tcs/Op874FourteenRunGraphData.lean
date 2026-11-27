import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FourteenRunGraph
import AFTD.Kb.Tcs.Op874FourteenRunEdges

/-!
# op874_fourteen_run_graph_data

Topic: graphs   Node: f21d553a352e

Provenance: helper lemma. All-matching maximum-cut palette obstruction for OP-874, using the local criterion in https://arxiv.org/abs/2610.41950.

The displayed fourteen-vertex graph is connected, cubic, bridgeless and bipartite.
-/

private lemma op874_fourteen_run_graph_data_adj_iff (u v : Fin 14) :
    op874_fourteen_run_graph.Adj u v ↔ s(u,v) ∈ op874_fourteen_run_edges ∧ u ≠ v := by
  unfold op874_fourteen_run_graph
  rw [SimpleGraph.fromEdgeSet_adj]
  simp

private lemma op874_fourteen_run_graph_data_ncard (v : Fin 14) :
    (op874_fourteen_run_graph.neighborSet v).ncard = 3 := by
  fin_cases v
  · rw [Set.ncard_eq_three]
    exact ⟨1, 13, 5, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨0, 2, 10, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨1, 3, 7, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨2, 4, 12, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨3, 5, 9, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨4, 6, 0, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨5, 7, 11, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨6, 8, 2, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨7, 9, 13, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨8, 10, 4, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨9, 11, 1, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨10, 12, 6, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨11, 13, 3, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩
  · rw [Set.ncard_eq_three]
    exact ⟨12, 0, 8, by decide, by decide, by decide, by
      ext w; rw [SimpleGraph.mem_neighborSet, op874_fourteen_run_graph_data_adj_iff]
      fin_cases w <;> decide⟩

private lemma op874_fourteen_run_graph_data_degree (v : Fin 14)
    (i : Fintype ↑(op874_fourteen_run_graph.neighborSet v)) :
    @SimpleGraph.degree (Fin 14) op874_fourteen_run_graph v i = 3 := by
  letI := i
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  have hfin : (op874_fourteen_run_graph.neighborSet v).Finite := Set.toFinite _
  calc Fintype.card ↑(op874_fourteen_run_graph.neighborSet v)
      = hfin.toFinset.card := hfin.card_toFinset.symm
    _ = (op874_fourteen_run_graph.neighborSet v).ncard :=
        (Set.ncard_eq_toFinset_card _ hfin).symm
    _ = 3 := op874_fourteen_run_graph_data_ncard v

private lemma op874_fourteen_run_graph_data_cycle_le :
    SimpleGraph.cycleGraph 14 ≤ op874_fourteen_run_graph := by
  intro u v h
  rw [op874_fourteen_run_graph_data_adj_iff]
  revert h
  fin_cases u <;> fin_cases v <;> decide

private lemma op874_fourteen_run_graph_data_isCycles :
    (SimpleGraph.cycleGraph 14).IsCycles := by
  intro v _
  rw [SimpleGraph.cycleGraph_neighborSet]
  apply Set.ncard_pair
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl

private lemma op874_fourteen_run_graph_data_connected :
    op874_fourteen_run_graph.Connected :=
  SimpleGraph.Connected.mono op874_fourteen_run_graph_data_cycle_le
    (SimpleGraph.cycleGraph_connected (n := 13))

private lemma op874_fourteen_run_graph_data_not_bridge (e : Sym2 (Fin 14)) :
    ¬ op874_fourteen_run_graph.IsBridge e := by
  obtain ⟨v, w⟩ := e
  rw [SimpleGraph.isBridge_iff]
  intro h
  by_cases he : s(v, w) ∈ (SimpleGraph.cycleGraph 14).edgeSet
  · have hadj : (SimpleGraph.cycleGraph 14).Adj v w := by
      simpa only [SimpleGraph.mem_edgeSet] using he
    have hr : ((SimpleGraph.cycleGraph 14).deleteEdges {s(v,w)}).Reachable v w :=
      op874_fourteen_run_graph_data_isCycles.reachable_deleteEdges hadj
    have hmono : (SimpleGraph.cycleGraph 14).deleteEdges {s(v,w)} ≤
        op874_fourteen_run_graph.deleteEdges {s(v,w)} :=
      SimpleGraph.deleteEdges_mono op874_fourteen_run_graph_data_cycle_le
    exact h (SimpleGraph.Reachable.mono hmono hr)
  · have hle' : SimpleGraph.cycleGraph 14 ≤
        op874_fourteen_run_graph.deleteEdges {s(v,w)} := by
      intro a b hab
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨op874_fourteen_run_graph_data_cycle_le hab, ?_⟩
      intro hmem
      rw [Set.mem_singleton_iff] at hmem
      exact he (hmem ▸ (SimpleGraph.mem_edgeSet (G := SimpleGraph.cycleGraph 14)).mpr hab)
    exact h ((SimpleGraph.cycleGraph_preconnected (n := 14)).mono hle' v w)

private lemma op874_fourteen_run_graph_data_color :
    ∀ u v : Fin 14, s(u,v) ∈ op874_fourteen_run_edges →
      (u.val % 2 == 0) ≠ (v.val % 2 == 0) := by
  intro u v h
  revert h
  fin_cases u <;> fin_cases v <;> decide

theorem op874_fourteen_run_graph_data :
    let G := op874_fourteen_run_graph
    letI : DecidableRel G.Adj := Classical.decRel _
    G.Connected ∧ G.IsRegularOfDegree 3 ∧ (∀ e, ¬ G.IsBridge e) ∧
    ∃ color : Fin 14 → Bool, ∀ u v, G.Adj u v → color u ≠ color v := by
  dsimp only
  refine ⟨op874_fourteen_run_graph_data_connected, ?_,
    op874_fourteen_run_graph_data_not_bridge, ?_⟩
  · haveI : op874_fourteen_run_graph.LocallyFinite := fun _ => Fintype.ofFinite _
    intro v
    exact op874_fourteen_run_graph_data_degree v _
  · refine ⟨fun i => i.val % 2 == 0, ?_⟩
    intro u v huv
    rw [op874_fourteen_run_graph_data_adj_iff] at huv
    exact op874_fourteen_run_graph_data_color u v huv.1
