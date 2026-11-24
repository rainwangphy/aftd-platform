import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierPartitionWithOddEndpoints
import AFTD.Kb.Tcs.PerfectMatchingSingleExitShoreIsOdd
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# forced_matching_edge_barrier_partition_all_cases

Topic: graphs   Node: 1a18fb6e5d69

Provenance: helper lemma. OP-1957, forced-edge barrier including bridge case

A forced matching edge admits the stated barrier partition with odd endpoint shores, whether or not deleting it leaves the endpoints connected. The separator may be empty.
-/

set_option maxHeartbeats 3000000

theorem forced_matching_edge_barrier_partition_all_cases
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : G.Adj u v)
    (hP : ∃ P : G.Subgraph, P.IsPerfectMatching)
    (hforced : ¬ ∃ P : (G.deleteEdges {s(u,v)}).Subgraph, P.IsPerfectMatching) :
    ∃ S X Y U : Finset V,
      Disjoint S X ∧ Disjoint S Y ∧ Disjoint S U ∧
      Disjoint X Y ∧ Disjoint X U ∧ Disjoint Y U ∧
      S ∪ X ∪ Y ∪ U = Finset.univ ∧ u ∈ X ∧ v ∈ Y ∧
      (∀ x ∈ X, ∀ y ∈ Y, G.Adj x y → x = u ∧ y = v) ∧
      (∀ w ∈ U, ∀ z ∈ X ∪ Y, ¬ G.Adj w z) ∧
      S.card ≤ (G.induce {a | a ∈ U}).oddComponents.ncard ∧ Odd X.card ∧ Odd Y.card := by
  classical
  by_cases hpath : (G.deleteEdges {s(u,v)}).Reachable u v
  · obtain ⟨S,X,Y,U,_,hrest⟩ := forced_matching_edge_barrier_partition_with_odd_endpoints G u v huv hP hforced hpath
    exact ⟨S,X,Y,U,hrest⟩
  · obtain ⟨P,hP⟩ := hP
    have hPuv : P.Adj u v := by
      by_contra hnot
      have hsub : ∀ a b, P.Adj a b → (G.deleteEdges {s(u,v)}).Adj a b := by
        intro a b hab
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨P.adj_sub hab, ?_⟩
        simp only [Set.mem_singleton_iff,not_false_eq_true]
        intro he
        rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact hnot (ha ▸ hb ▸ hab)
        · exact hnot (hb ▸ ha ▸ hab.symm)
      let Q : (G.deleteEdges {s(u,v)}).Subgraph :=
        ⟨P.verts,P.Adj,(fun {a b} hab => hsub a b hab),P.edge_vert,P.symm⟩
      exact hforced ⟨Q,⟨hP.1,hP.2⟩⟩
    let H := G.deleteEdges {s(u,v)}
    let X : Finset V := Finset.univ.filter (fun a => H.Reachable u a)
    let Y : Finset V := Finset.univ \ X
    have huX : u ∈ X := by simp [X,SimpleGraph.Reachable.rfl]
    have hvY : v ∈ Y := by simp [Y,X,H,hpath]
    have hXY : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro a haX haY
      exact (Finset.mem_sdiff.mp haY).2 haX
    have hcover : X ∪ Y = Finset.univ := by
      ext z
      simp [Y]
    have hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=u ∧ b=v := by
      intro a ha b hb hab
      have hna : ¬ H.Adj a b := by
        intro hh
        have hua : H.Reachable u a := (Finset.mem_filter.mp ha).2
        have hub : H.Reachable u b := hua.trans hh.reachable
        have hbX : b ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hub⟩
        exact (Finset.mem_sdiff.mp hb).2 hbX
      have he : s(a,b)=s(u,v) := by
        by_contra hn
        apply hna
        apply SimpleGraph.deleteEdges_adj.mpr
        exact ⟨hab, by simpa using hn⟩
      rcases Sym2.eq_iff.mp he with h | h
      · exact h
      · have hnotv : v ∉ X := fun hv => Finset.disjoint_left.mp hXY hv hvY
        exact False.elim (hnotv (h.1 ▸ ha))
    have hnotvX : v ∉ X := fun h => Finset.disjoint_left.mp hXY h hvY
    have hnotuY : u ∉ Y := fun h => Finset.disjoint_left.mp hXY huX h
    have hclosedX : ∀ a ∈ X, ∀ b, P.Adj a b → b ∉ X → a=u ∧ b=v := by
      intro a ha b hab hb
      have hbY : b ∈ Y := by simp [Y,hb]
      exact hcross a ha b hbY (P.adj_sub hab)
    have hclosedY : ∀ a ∈ Y, ∀ b, P.Adj a b → b ∉ Y → a=v ∧ b=u := by
      intro a ha b hab hb
      have hbX : b ∈ X := by simpa [Y] using hb
      have hh := hcross b hbX a ha (P.adj_sub hab).symm
      exact ⟨hh.2,hh.1⟩
    have hoddX := perfect_matching_single_exit_shore_is_odd G P hP X u v huX hnotvX hPuv hclosedX
    have hoddY := perfect_matching_single_exit_shore_is_odd G P hP Y v u hvY hnotuY hPuv.symm hclosedY
    refine ⟨∅,X,Y,∅,by simp,by simp,by simp,hXY,by simp,by simp,?_,huX,hvY,hcross,?_,?_,hoddX,hoddY⟩
    · simpa using hcover
    · simp
    · simp
