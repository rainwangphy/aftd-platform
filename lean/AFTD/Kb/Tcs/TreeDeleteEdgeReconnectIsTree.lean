import AFTD.Prelude
import AFTD.Kb.Tcs.IsTreeIffIsAcyclicAndCard
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# tree_delete_edge_reconnect_isTree

Topic: graphs   Node: c65c7863c82b

Provenance: helper lemma. arXiv:2610.17078 Lemma 3.1 proof

Let T be a tree on a finite vertex type V, and let vw be an edge of T. If u is a vertex not incident to vw (u ≠ v and u ≠ w), then there exists x ∈ {v, w} such that the graph obtained by deleting edge vw and adding edge ux is a tree.
-/

lemma tree_delete_edge_reconnect_isTree_reachable_of_adj_reachable
    {V : Type*} {G G' : SimpleGraph V}
    (h : ∀ ⦃a b : V⦄, G.Adj a b → G'.Reachable a b)
    {x y : V} (r : G.Reachable x y) : G'.Reachable x y := by
  obtain ⟨p⟩ := r
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons hadj _ ih =>
    exact (h hadj).trans ih

/-- Deleting an edge not incident to u in a tree can be reconnected by joining u to one of the edge's endpoints to form a tree. -/
theorem tree_delete_edge_reconnect_isTree
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (u v w : V) (he : T.Adj v w) (huv : u ≠ v) (huw : u ≠ w) :
    ∃ x : V, (x = v ∨ x = w) ∧
      (T.deleteEdges {s(v, w)} ⊔ SimpleGraph.fromEdgeSet {s(u, x)}).IsTree := by
  have hb : T.IsBridge s(v, w) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic he
  have hvw : ¬ (T.deleteEdges {s(v, w)}).Reachable v w :=
    SimpleGraph.isBridge_iff.mp hb
  have h_reach_or : (T.deleteEdges {s(v, w)}).Reachable u v ∨
      (T.deleteEdges {s(v, w)}).Reachable u w := by
    by_cases huw_r : (T.deleteEdges {s(v, w)}).Reachable u w
    · exact Or.inr huw_r
    · left
      obtain ⟨p, hp⟩ := hT.connected.exists_isPath u v
      have h_not_mem : s(v, w) ∉ p.edges :=
        hp.isTrail.not_mem_edges_of_not_reachable huw_r hvw
      exact SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, h_not_mem⟩
  obtain ⟨x, hx_vw, hx_reach⟩ : ∃ x : V, (x = v ∨ x = w) ∧
      ((x = w ∧ (T.deleteEdges {s(v, w)}).Reachable u v) ∨
       (x = v ∧ (T.deleteEdges {s(v, w)}).Reachable u w)) := by
    rcases h_reach_or with h | h
    · exact ⟨w, Or.inr rfl, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨v, Or.inl rfl, Or.inr ⟨rfl, h⟩⟩
  refine ⟨x, hx_vw, ?_⟩
  have hux_ne : u ≠ x := by rcases hx_vw with rfl | rfl <;> assumption
  have hnot : ¬ (T.deleteEdges {s(v, w)}).Adj u x := by
    intro hadj
    rcases hx_reach with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
    · exact hvw (hr.symm.trans hadj.reachable)
    · exact hvw (hadj.symm.reachable.trans hr)
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · have : Nonempty V := hT.connected.nonempty
    let G' := T.deleteEdges {s(v, w)} ⊔ SimpleGraph.fromEdgeSet {s(u, x)}
    have h_le : T.deleteEdges {s(v, w)} ≤ G' := le_sup_left
    have h_ux : G'.Adj u x := by
      apply Or.inr
      rw [SimpleGraph.fromEdgeSet_adj]
      rcases hx_reach with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨Set.mem_singleton _, huw⟩
      · exact ⟨Set.mem_singleton _, huv⟩
    have hvw' : G'.Reachable v w := by
      rcases hx_reach with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
      · exact (hr.mono h_le).symm.trans h_ux.reachable
      · exact (h_ux.symm.reachable).trans (hr.mono h_le)
    have hadj : ∀ ⦃a b : V⦄, T.Adj a b → G'.Reachable a b := by
      intro a b hab
      by_cases h_eq : s(a, b) = s(v, w)
      · rw [Sym2.eq_iff] at h_eq
        rcases h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hvw'
        · exact hvw'.symm
      · have h_del : (T.deleteEdges {s(v, w)}).Adj a b := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨hab, h_eq⟩
        exact (h_le h_del).reachable
    have h_pre : G'.Preconnected := by
      intro a b
      exact tree_delete_edge_reconnect_isTree_reachable_of_adj_reachable hadj (hT.connected.preconnected a b)
    exact ⟨h_pre⟩
  · have h_edge : (SimpleGraph.fromEdgeSet {s(u, x)} : SimpleGraph V).edgeSet = {s(u, x)} := by
      simp [SimpleGraph.edgeSet_fromEdgeSet, hux_ne]
    have h_del : (T.deleteEdges {s(v, w)}).edgeSet = T.edgeSet \ {s(v, w)} := by simp
    have h_sup : (T.deleteEdges {s(v, w)} ⊔ SimpleGraph.fromEdgeSet {s(u, x)}).edgeSet =
        insert s(u, x) (T.edgeSet \ {s(v, w)}) := by
      rw [SimpleGraph.edgeSet_sup, h_del, h_edge, Set.union_singleton]
    have h_not_mem : s(u, x) ∉ T.edgeSet \ {s(v, w)} := by
      rw [← h_del]
      exact mt (T.deleteEdges {s(v, w)}).mem_edgeSet.mp hnot
    have h_card_T : Nat.card T.edgeSet + 1 = Nat.card V :=
      (is_tree_iff_is_acyclic_and_card T).mp hT |>.2
    rw [Nat.card_coe_set_eq, h_sup, Set.ncard_insert_of_notMem h_not_mem,
      Set.ncard_sdiff_singleton_add_one (T.mem_edgeSet.mpr he), ← Nat.card_coe_set_eq]
    exact h_card_T
