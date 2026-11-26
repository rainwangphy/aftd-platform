import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.ResidualMatchingNumSingleEdgeExchangeIffCritical

/-!
# maximum_matching_forbids_one_edge_two_uncovered_exchange

Topic: graphs   Node: cc166a79caa0

Provenance: helper lemma. Maximum-matching exchange for OP-1957; https://arxiv.org/abs/1011.3384.

A maximum matching cannot contain an edge whose two endpoints have distinct uncovered neighbors.
-/

theorem maximum_matching_forbids_one_edge_two_uncovered_exchange
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (M : G.Subgraph) (hM : M.IsMatching)
    (hMS : M.verts ⊆ (S : Set V))
    (hmax : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (S : Set V) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (u v a b : V) (huS : u ∈ S) (hvS : v ∈ S)
    (hu : u ∉ M.verts) (hv : v ∉ M.verts) (huv : u ≠ v)
    (hab : M.Adj a b) (hua : G.Adj u a) (hvb : G.Adj v b) : False := by
  set_option maxHeartbeats 4000000 in
    classical
    have haM : a ∈ M.verts := M.edge_vert hab
    have hbM : b ∈ M.verts := M.edge_vert hab.symm
    have habne : a ≠ b := G.ne_of_adj (M.adj_sub hab)
    obtain ⟨D,hD,hDedge⟩ := residual_matching_num_single_edge_exchange_iff_critical_del hM ({s(a,b)} : Set (Sym2 V))
    have hDsub : D.verts ⊆ M.verts := by
      intro x hx
      obtain ⟨y,hxy,_⟩ := hD hx
      have hh : s(x,y) ∈ D.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hxy
      rw [hDedge] at hh
      exact M.edge_vert (SimpleGraph.Subgraph.mem_edgeSet.mp hh.1)
    have haD : a ∉ D.verts := by
      intro ha
      obtain ⟨z,haz,_⟩ := hD ha
      have hh : s(a,z) ∈ D.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr haz
      rw [hDedge] at hh
      have hazM : M.Adj a z := SimpleGraph.Subgraph.mem_edgeSet.mp hh.1
      have hz : z=b := (hM haM).unique hazM hab
      subst z
      exact hh.2 (by simp)
    have hbD : b ∉ D.verts := by
      intro hb
      obtain ⟨z,hbz,_⟩ := hD hb
      have hh : s(b,z) ∈ D.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hbz
      rw [hDedge] at hh
      have hbzM : M.Adj b z := SimpleGraph.Subgraph.mem_edgeSet.mp hh.1
      have hz : z=a := (hM hbM).unique hbzM hab.symm
      subst z
      apply hh.2
      simp [Sym2.eq_swap]
    have he : s(a,b) ∈ M.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hab
    have hcard : D.edgeSet.ncard + 1 = M.edgeSet.ncard := by
      have hs : ({s(a,b)} : Set (Sym2 V)) ⊆ M.edgeSet := by simpa using he
      have hh := Set.ncard_sdiff_add_ncard_of_subset hs (Set.toFinite M.edgeSet)
      simpa [← hDedge] using hh
    let f : Fin 2 → V := ![u,v]
    let g : Fin 2 → V := ![a,b]
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
    obtain ⟨E,hE,hEcard,hEverts⟩ := indexed_disjoint_cross_edges_form_matching G 2 f g hf hg hfg hadj
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
        rcases hxE with ⟨i,hi⟩ | ⟨i,hi⟩
        · fin_cases i <;> simp_all [f]
        · have haS := hMS haM
          have hbS := hMS hbM
          fin_cases i <;> simp_all [g]
    have hh := hmax (D ⊔ E) hsup.1 hsub
    rw [hsup.2,hEcard] at hh
    omega
