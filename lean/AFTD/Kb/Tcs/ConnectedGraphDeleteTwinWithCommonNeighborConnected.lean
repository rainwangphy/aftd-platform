import AFTD.Prelude
import AFTD.Kb.Tcs.ConnectedGraphDeleteFalseTwinConnected
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# connected_graph_delete_twin_with_common_neighbor_connected

Topic: graphs   Node: d70e915a819b

Provenance: helper lemma. OP-1957: extension of the false-twin bridge route to adjacent and nonadjacent twins.

If two distinct vertices have identical neighbors outside the pair and a common neighbor, deleting either one preserves connectedness of a connected graph.
-/

theorem connected_graph_delete_twin_with_common_neighbor_connected {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) (x y z : V) (hxy : x ≠ y)
    (hxz : G.Adj x z) (hyz : G.Adj y z)
    (htwin : ∀ a, a ≠ x → a ≠ y → (G.Adj x a ↔ G.Adj y a)) :
    (G.induce {a | a ≠ y}).Connected := by
  classical
  by_cases hxyadj : G.Adj x y
  · let F := G.deleteEdges {s(x,y)}
    have hz_x : z ≠ x := hxz.ne.symm
    have hz_y : z ≠ y := hyz.ne.symm
    have hxzF : F.Adj x z := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hxz, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hz_y h
      · exact hxy h
    have hyzF : F.Adj y z := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hyz, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact hxy h.symm
      · exact hz_x h
    have hr : F.Reachable x y := hxzF.reachable.trans hyzF.symm.reachable
    have hfconn : F.Connected := by
      exact hconn.connected_delete_edge_of_not_isBridge (x := x) (y := y)
        (by rw [SimpleGraph.isBridge_iff]; exact not_not.mpr hr)
    have hFtwins : F.neighborSet x = F.neighborSet y := by
      ext a
      change F.Adj x a ↔ F.Adj y a
      by_cases hax : a = x
      · subst a
        simp [F, SimpleGraph.deleteEdges_adj, Sym2.eq_iff, hxy]
      · by_cases hay : a = y
        · subst a
          simp [F, SimpleGraph.deleteEdges_adj, Sym2.eq_iff, hxy]
        · simp only [F, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
          have hxa : x ≠ a := fun h => hax h.symm
          have hya : y ≠ a := fun h => hay h.symm
          simp [hxy,hxy.symm,hax,hay,hxa,hya,htwin a hax hay]
    have hfdel := connected_graph_delete_false_twin_connected F hfconn x y hxy hFtwins
    have heq : F.induce {a | a ≠ y} = G.induce {a | a ≠ y} := by
      ext a b
      simp only [F, SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj,
        Set.mem_singleton_iff, Sym2.eq_iff]
      constructor
      · exact And.left
      · intro hab
        refine ⟨hab, ?_⟩
        rintro (⟨_, hb⟩ | ⟨ha, _⟩)
        · exact b.property hb
        · exact a.property ha
    rw [heq] at hfdel
    exact hfdel
  · have hyxadj : ¬ G.Adj y x := fun h => hxyadj h.symm
    have ht : G.neighborSet x = G.neighborSet y := by
      ext a
      change G.Adj x a ↔ G.Adj y a
      by_cases hax : a = x
      · subst a
        simp [hxyadj, hyxadj]
      · by_cases hay : a = y
        · subst a
          simp [hxyadj, hyxadj]
        · exact htwin a hax hay
    exact connected_graph_delete_false_twin_connected G hconn x y hxy ht
