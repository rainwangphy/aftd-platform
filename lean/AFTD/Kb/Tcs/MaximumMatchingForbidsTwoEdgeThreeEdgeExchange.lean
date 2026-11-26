import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.ResidualMatchingNumSingleEdgeExchangeIffCritical

/-!
# maximum_matching_forbids_two_edge_three_edge_exchange

Topic: graphs   Node: 97c6fec5381b

Provenance: helper lemma. Maximum-matching exchange for OP-1957; https://arxiv.org/abs/1011.3384.

A maximum matching forbids replacing two matching edges by two edges from distinct uncovered vertices and an edge joining the two remaining endpoints.
-/

theorem maximum_matching_forbids_two_edge_three_edge_exchange
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (M : G.Subgraph) (hM : M.IsMatching)
    (hMS : M.verts ⊆ (S : Set V))
    (hmax : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (S : Set V) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (u v a b c d : V) (huS : u ∈ S) (hvS : v ∈ S)
    (hu : u ∉ M.verts) (hv : v ∉ M.verts) (huv : u ≠ v)
    (hab : M.Adj a b) (hcd : M.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hua : G.Adj u a) (hvc : G.Adj v c) (hbdEdge : G.Adj b d) : False := by
  set_option maxHeartbeats 4000000 in
    classical
    have haM : a ∈ M.verts := M.edge_vert hab
    have hbM : b ∈ M.verts := M.edge_vert hab.symm
    have hcM : c ∈ M.verts := M.edge_vert hcd
    have hdM : d ∈ M.verts := M.edge_vert hcd.symm
    have habne : a ≠ b := G.ne_of_adj (M.adj_sub hab)
    have hcdne : c ≠ d := G.ne_of_adj (M.adj_sub hcd)
    let T : Set (Sym2 V) := {s(a,b),s(c,d)}
    have he1 : s(a,b) ∈ M.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hab
    have he2 : s(c,d) ∈ M.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hcd
    have hene : s(a,b) ≠ s(c,d) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨h,_⟩
      · exact hac h
      · exact had h
    have hTM : T ⊆ M.edgeSet := by
      intro e he
      simp only [T,Set.mem_insert_iff,Set.mem_singleton_iff] at he
      rcases he with rfl | rfl <;> assumption
    obtain ⟨D,hD,hDedge⟩ := residual_matching_num_single_edge_exchange_iff_critical_del hM T
    have hDsub : D.verts ⊆ M.verts := by
      intro x hx
      obtain ⟨y,hxy,_⟩ := hD hx
      have hh : s(x,y) ∈ D.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hxy
      rw [hDedge] at hh
      exact M.edge_vert (SimpleGraph.Subgraph.mem_edgeSet.mp hh.1)
    have hnotD : ∀ p q, M.Adj p q → s(p,q) ∈ T → p ∉ D.verts := by
      intro p q hpq hpT hpD
      obtain ⟨z,hpz,_⟩ := hD hpD
      have hh : s(p,z) ∈ D.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hpz
      rw [hDedge] at hh
      have hpzM : M.Adj p z := SimpleGraph.Subgraph.mem_edgeSet.mp hh.1
      have hz : z=q := (hM (M.edge_vert hpq)).unique hpzM hpq
      subst z
      exact hh.2 hpT
    have haD : a ∉ D.verts := hnotD a b hab (by simp [T])
    have hbD : b ∉ D.verts := hnotD b a hab.symm (by simp [T,Sym2.eq_swap])
    have hcD : c ∉ D.verts := hnotD c d hcd (by simp [T])
    have hdD : d ∉ D.verts := hnotD d c hcd.symm (by simp [T,Sym2.eq_swap])
    have hTcard : T.ncard = 2 := by simpa [T] using (Set.ncard_pair hene)
    have hcard : D.edgeSet.ncard + 2 = M.edgeSet.ncard := by
      have hh := Set.ncard_sdiff_add_ncard_of_subset hTM (Set.toFinite M.edgeSet)
      rw [← hDedge,hTcard] at hh
      exact hh
    let f : Fin 3 → V := ![u,v,b]
    let g : Fin 3 → V := ![a,c,d]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    have hg : Function.Injective g := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [g]
    have hfg : ∀ i j, f i ≠ g j := by
      intro i j heq
      fin_cases i <;> fin_cases j <;> simp_all [f,g]
    have hadj : ∀ i, G.Adj (f i) (g i) := by
      intro i
      fin_cases i <;> simp_all [f,g]
    obtain ⟨E,hE,hEcard,hEverts⟩ := indexed_disjoint_cross_edges_form_matching G 3 f g hf hg hfg hadj
    have hDE : Disjoint D.verts E.verts := by
      apply Set.disjoint_left.mpr
      intro x hxD hxE
      rw [hEverts] at hxE
      rcases hxE with ⟨i,hi⟩ | ⟨i,hi⟩
      · have hxM := hDsub hxD
        fin_cases i <;> simp_all [f]
      · fin_cases i <;> simp_all [g]
    have hsup := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard D E hD hE hDE
    have hsub : (D ⊔ E).verts ⊆ (S : Set V) := by
      intro x hx
      change x ∈ D.verts ∪ E.verts at hx
      rcases hx with hxD | hxE
      · exact hMS (hDsub hxD)
      · rw [hEverts] at hxE
        have haS := hMS haM
        have hbS := hMS hbM
        have hcS := hMS hcM
        have hdS := hMS hdM
        rcases hxE with ⟨i,hi⟩ | ⟨i,hi⟩
        · fin_cases i <;> simp_all [f]
        · fin_cases i <;> simp_all [g]
    have hh := hmax (D ⊔ E) hsup.1 hsub
    rw [hsup.2,hEcard] at hh
    omega
