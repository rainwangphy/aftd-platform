import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum
import AFTD.Kb.Tcs.GraphMatchingNumLeEncardEdgeSet
import AFTD.Kb.Tcs.GraphMatchingNumMono
import AFTD.Kb.Tcs.GraphIsMaximumMatching
import AFTD.Kb.Tcs.Support

/-!
# residual_matching_num_single_edge_exchange_iff_critical

Topic: approximation   Node: 26f4694cb3f4

Provenance: formalization of a published result. Source: arXiv:2610.27833, Lemma 1

Let G be a finite simple graph on a finite vertex type V, M a maximum matching of G, u an M-free vertex, and vw an edge of M such that uv is an edge of G. Then there exists a maximum matching M' of G with edge set (M \ {vw}) ∪ {uv}, and the matching number of the residual graph G \ M' equals ν(G \ M) + 1 if and only if the matching number of (G \ M) + vw equals ν(G \ M) + 1.
-/

open scoped Sym2

lemma residual_matching_num_single_edge_exchange_iff_critical_copy
    {V : Type*} {H K : SimpleGraph V} (N : H.Subgraph) (hN : N.IsMatching)
    (h : N.edgeSet ⊆ K.edgeSet) :
    ∃ N' : K.Subgraph, N'.IsMatching ∧ N'.edgeSet = N.edgeSet := by
  let N' : K.Subgraph :=
    { verts := N.verts
      Adj := N.Adj
      adj_sub := by
        intro x y hxy
        have hmem : s(x, y) ∈ K.edgeSet := h (by rwa [SimpleGraph.Subgraph.mem_edgeSet])
        rwa [SimpleGraph.mem_edgeSet] at hmem
      edge_vert := by
        intro x y hxy
        exact N.edge_vert hxy
      symm := N.symm }
  refine ⟨N', hN, ?_⟩
  ext e
  induction e using Sym2.ind with
  | _ x y => rw [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Subgraph.mem_edgeSet]

lemma residual_matching_num_single_edge_exchange_iff_critical_del
    {V : Type*} {H : SimpleGraph V} {N : H.Subgraph} (hN : N.IsMatching)
    (T : Set (Sym2 V)) :
    ∃ N' : H.Subgraph, N'.IsMatching ∧ N'.edgeSet = N.edgeSet \ T := by
  refine ⟨(N.deleteEdges T).induce (N.deleteEdges T).support, ?_, ?_⟩
  · intro x hx
    rw [SimpleGraph.Subgraph.induce_verts, SimpleGraph.Subgraph.mem_support] at hx
    obtain ⟨y, hxy⟩ := hx
    rw [SimpleGraph.Subgraph.deleteEdges_adj] at hxy
    refine ⟨y, ?_, ?_⟩
    · change ((N.deleteEdges T).induce (N.deleteEdges T).support).Adj x y
      rw [SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.deleteEdges_adj]
      refine ⟨by rw [SimpleGraph.Subgraph.mem_support]; exact ⟨y, hxy⟩, ?_, hxy⟩
      rw [SimpleGraph.Subgraph.mem_support]; exact ⟨x, SimpleGraph.Subgraph.adj_symm _ hxy⟩
    · intro z hz
      rw [SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.deleteEdges_adj] at hz
      exact (hN hxy.1.fst_mem).unique hz.2.2.1 hxy.1
  · ext e
    refine Sym2.ind (fun x y => ?_) e
    rw [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Subgraph.induce_adj,
        SimpleGraph.Subgraph.deleteEdges_adj, Set.mem_sdiff, SimpleGraph.Subgraph.mem_edgeSet]
    simp only [SimpleGraph.Subgraph.mem_support]
    constructor
    · rintro ⟨_, _, h, hT⟩; exact ⟨h, hT⟩
    · rintro ⟨h, hT⟩
      refine ⟨⟨y, ?_⟩, ⟨x, ?_⟩, h, hT⟩
      · rw [SimpleGraph.Subgraph.deleteEdges_adj]; exact ⟨h, hT⟩
      · rw [SimpleGraph.Subgraph.deleteEdges_adj]; exact ⟨SimpleGraph.Subgraph.adj_symm N h, by rwa [Sym2.eq_swap]⟩

lemma residual_matching_num_single_edge_exchange_iff_critical_replace
    {V : Type*} {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) {u v w : V} (hu : u ∉ M.verts) (hvw : M.Adj v w) (huv : G.Adj u v) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧ M'.edgeSet = (M.edgeSet \ {s(v, w)}) ∪ {s(u, v)} := by
  obtain ⟨D, hDmatch, hDedge⟩ := residual_matching_num_single_edge_exchange_iff_critical_del hM {s(v, w)}
  have hdisj : Disjoint D.support (G.subgraphOfAdj huv).support := by
    rw [SimpleGraph.support_subgraphOfAdj]
    rw [Set.disjoint_insert_right, Set.disjoint_singleton_right]
    constructor
    · intro huD
      have : D.support ⊆ M.verts := by
        intro x hx
        rw [SimpleGraph.Subgraph.mem_support] at hx
        obtain ⟨y, hy⟩ := hx
        have : s(x, y) ∈ D.edgeSet := by rwa [SimpleGraph.Subgraph.mem_edgeSet]
        rw [hDedge] at this
        have hMadj : M.Adj x y := by
          have := this.1
          rwa [SimpleGraph.Subgraph.mem_edgeSet] at this
        exact hMadj.fst_mem
      exact hu (this huD)
    · intro hvD
      rw [SimpleGraph.Subgraph.mem_support] at hvD
      obtain ⟨z, hz⟩ := hvD
      have : s(v, z) ∈ D.edgeSet := by rwa [SimpleGraph.Subgraph.mem_edgeSet]
      rw [hDedge, Set.mem_sdiff, SimpleGraph.Subgraph.mem_edgeSet] at this
      have hMadj : M.Adj v z := this.1
      have hnot : s(v, z) ∉ ({s(v, w)} : Set (Sym2 V)) := this.2
      have hz_eq_w : z = w := (hM hvw.fst_mem).unique hMadj hvw
      subst hz_eq_w
      exact hnot (Set.mem_singleton _)
  refine ⟨D ⊔ G.subgraphOfAdj huv, ?_, ?_⟩
  · exact SimpleGraph.Subgraph.IsMatching.sup hDmatch (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj huv) hdisj
  · rw [SimpleGraph.Subgraph.edgeSet_sup, hDedge, SimpleGraph.edgeSet_subgraphOfAdj]

lemma residual_matching_num_single_edge_exchange_iff_critical_card
    {α : Type*} (E : Set α) {a b : α} (ha : a ∈ E) (hb : b ∉ E) :
    ((E \ {a}) ∪ {b}).encard = E.encard := by
  have hd : Disjoint (E \ {a}) ({b} : Set α) := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨h, -⟩
    exact hb h
  rw [Set.encard_union_eq hd, Set.encard_singleton, ← Set.encard_sdiff_add_encard_of_subset (Set.singleton_subset_iff.mpr ha), Set.encard_singleton]

lemma residual_matching_num_single_edge_exchange_iff_critical_num_ne_top
    {V : Type*} [Fintype V] (H : SimpleGraph V) :
    graph_matching_num H ≠ ⊤ := by
  have : H.edgeSet.encard ≠ ⊤ := by
    rw [Set.encard_ne_top_iff]
    exact Set.toFinite H.edgeSet
  exact ne_top_of_le_ne_top this (graph_matching_num_le_encard_edgeSet H)

lemma residual_matching_num_single_edge_exchange_iff_critical_num_mono
    {V : Type*} {H K : SimpleGraph V} (h : H.edgeSet ⊆ K.edgeSet) :
    graph_matching_num H ≤ graph_matching_num K := by
  apply graph_matching_num_mono
  intro x y hxy
  have : s(x, y) ∈ K.edgeSet := h (by rwa [SimpleGraph.mem_edgeSet])
  rwa [SimpleGraph.mem_edgeSet] at this

lemma residual_matching_num_single_edge_exchange_iff_critical_lt_succ_eq
    {a b : ℕ∞} (ha : a ≠ ⊤) (h1 : b ≤ a + 1) (h2 : a < b) : b = a + 1 := by
  have : a + 1 ≤ b := (ENat.add_one_le_iff ha).mpr h2
  exact le_antisymm h1 this

lemma residual_matching_num_single_edge_exchange_iff_critical_one_edge
    {V : Type*} (H : SimpleGraph V) (u v : V) :
    graph_matching_num (H ⊔ SimpleGraph.edge u v) ≤ graph_matching_num H + 1 := by
  unfold graph_matching_num
  apply iSup_le
  intro N
  apply iSup_le
  intro hN
  by_cases hmem : s(u, v) ∈ N.edgeSet
  · obtain ⟨N0, hN0match, hN0edge⟩ := residual_matching_num_single_edge_exchange_iff_critical_del hN {s(u, v)}
    have hsub : N0.edgeSet ⊆ H.edgeSet := by
      rw [hN0edge]
      intro e he
      have heN : e ∈ (H ⊔ SimpleGraph.edge u v).edgeSet := N.edgeSet_subset he.1
      rw [SimpleGraph.edgeSet_sup, Set.mem_union] at heN
      rcases heN with heH | heE
      · exact heH
      · rw [SimpleGraph.edgeSet_edge] at heE
        exfalso
        exact he.2 (Set.mem_singleton_iff.mpr heE.1)
    obtain ⟨N', hN'match, hN'edge⟩ := residual_matching_num_single_edge_exchange_iff_critical_copy N0 hN0match hsub
    have hle : N'.edgeSet.encard ≤ ⨆ (M : H.Subgraph) (_ : M.IsMatching), M.edgeSet.encard :=
      le_iSup_of_le N' (le_iSup_of_le hN'match le_rfl)
    have heq : N.edgeSet.encard = N0.edgeSet.encard + 1 := by
      rw [hN0edge]
      have hsing : ({s(u, v)} : Set (Sym2 V)).encard = 1 := Set.encard_singleton _
      rw [← hsing]
      exact (Set.encard_sdiff_add_encard_of_subset (Set.singleton_subset_iff.mpr hmem)).symm
    rw [heq, ← hN'edge]
    gcongr
  · have hsub : N.edgeSet ⊆ H.edgeSet := by
      intro e he
      have heN : e ∈ (H ⊔ SimpleGraph.edge u v).edgeSet := N.edgeSet_subset he
      rw [SimpleGraph.edgeSet_sup, Set.mem_union] at heN
      rcases heN with heH | heE
      · exact heH
      · rw [SimpleGraph.edgeSet_edge] at heE
        have : e = s(u, v) := heE.1
        subst this
        exact False.elim (hmem he)
    obtain ⟨N', hN'match, hN'edge⟩ := residual_matching_num_single_edge_exchange_iff_critical_copy N hN hsub
    have hle : N'.edgeSet.encard ≤ ⨆ (M : H.Subgraph) (_ : M.IsMatching), M.edgeSet.encard :=
      le_iSup_of_le N' (le_iSup_of_le hN'match le_rfl)
    rw [← hN'edge]
    exact le_trans hle le_self_add

lemma residual_matching_num_single_edge_exchange_iff_critical_upper
    {V : Type*} {G : SimpleGraph V} {M : G.Subgraph} {v w u : V}
    (hvw : M.Adj v w) :
    (G.deleteEdges ((M.edgeSet \ {s(v, w)}) ∪ {s(u, v)})).edgeSet ⊆
      ((G.deleteEdges M.edgeSet) ⊔ SimpleGraph.edge v w).edgeSet := by
  intro e he
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff] at he
  rw [SimpleGraph.edgeSet_sup, Set.mem_union, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff]
  by_cases hevw : e = s(v, w)
  · right
    subst hevw
    rw [SimpleGraph.edgeSet_edge, Set.mem_sdiff, Set.mem_singleton_iff]
    refine ⟨rfl, ?_⟩
    intro hd
    exact hvw.ne (Sym2.mk_isDiag_iff.mp hd)
  · left
    refine ⟨he.1, ?_⟩
    intro heM
    have : e ∈ (M.edgeSet \ {s(v, w)}) ∪ {s(u, v)} := by
      left
      exact ⟨heM, hevw⟩
    exact he.2 this

lemma residual_matching_num_single_edge_exchange_iff_critical_lower
    {V : Type*} {G : SimpleGraph V} {M : G.Subgraph} {v w u : V}
    (hvw : M.Adj v w) {e : Sym2 V}
    (heH : e ∈ ((G.deleteEdges M.edgeSet) ⊔ SimpleGraph.edge v w).edgeSet)
    (hne : e ≠ s(u, v)) :
    e ∈ (G.deleteEdges ((M.edgeSet \ {s(v, w)}) ∪ {s(u, v)})).edgeSet := by
  rw [SimpleGraph.edgeSet_sup, Set.mem_union, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff] at heH
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  rcases heH with ⟨heG, heM⟩ | heE
  · refine ⟨heG, ?_⟩
    rintro (⟨heM2, -⟩ | rfl)
    · exact heM heM2
    · exact hne rfl
  · rw [SimpleGraph.edgeSet_edge, Set.mem_sdiff, Set.mem_singleton_iff] at heE
    have he_eq : e = s(v, w) := heE.1
    subst he_eq
    have hvwG : s(v, w) ∈ G.edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact M.adj_sub hvw
    refine ⟨hvwG, ?_⟩
    rintro (⟨-, hnot⟩ | h_eq)
    · exact hnot rfl
    · exact hne h_eq

lemma residual_matching_num_single_edge_exchange_iff_critical_uv_notin
    {V : Type*} {G : SimpleGraph V} {M : G.Subgraph}
    {H : SimpleGraph V} (K : H.Subgraph) (hK : K.IsMatching)
    {u v w : V} (hu : u ∉ M.verts) (hvw : M.Adj v w)
    (hvwK : s(v, w) ∈ K.edgeSet) :
    s(u, v) ∉ K.edgeSet := by
  intro huvK
  have hKvw : K.Adj v w := by rwa [SimpleGraph.Subgraph.mem_edgeSet] at hvwK
  have hKuv : K.Adj u v := by rwa [SimpleGraph.Subgraph.mem_edgeSet] at huvK
  have hKvu : K.Adj v u := SimpleGraph.Subgraph.adj_symm K hKuv
  have hu_eq_w : u = w := (hK hKvw.fst_mem).unique hKvu hKvw
  subst hu_eq_w
  exact hu hvw.snd_mem

/-- Residual matching number increases under single-edge exchange if and only if the exchanged edge is critical. -/
theorem residual_matching_num_single_edge_exchange_iff_critical {V : Type*} [Fintype V]
    (G : SimpleGraph V) (M : G.Subgraph) (hM : graph_is_maximum_matching G M)
    (u v w : V) (hu : u ∉ M.verts) (hvw : M.Adj v w) (huv : G.Adj u v) :
    ∃ M' : G.Subgraph,
      M'.edgeSet = (M.edgeSet \ {s(v, w)}) ∪ {s(u, v)} ∧
      graph_is_maximum_matching G M' ∧
      (graph_matching_num (G.deleteEdges M'.edgeSet) =
          graph_matching_num (G.deleteEdges M.edgeSet) + 1 ↔
        graph_matching_num ((G.deleteEdges M.edgeSet) ⊔ SimpleGraph.edge v w) =
          graph_matching_num (G.deleteEdges M.edgeSet) + 1) := by
  obtain ⟨hMmatch, hMcard⟩ := hM
  have hbE : s(u, v) ∉ M.edgeSet := fun h =>
    hu (M.edge_vert (by rwa [SimpleGraph.Subgraph.mem_edgeSet] at h))
  obtain ⟨M', hM'match, hM'edge⟩ :=
    residual_matching_num_single_edge_exchange_iff_critical_replace hMmatch hu hvw huv
  have hM'card : graph_is_maximum_matching G M' := by
    refine ⟨hM'match, ?_⟩
    rw [hM'edge, residual_matching_num_single_edge_exchange_iff_critical_card M.edgeSet (by rw [SimpleGraph.Subgraph.mem_edgeSet]; exact hvw) hbE,
      hMcard]
  refine ⟨M', hM'edge, hM'card, ?_⟩
  rw [hM'edge]
  set μ := graph_matching_num (G.deleteEdges M.edgeSet)
  have hμtop : μ ≠ ⊤ := residual_matching_num_single_edge_exchange_iff_critical_num_ne_top _
  have hone : μ < μ + 1 := (ENat.lt_add_one_iff hμtop).mpr le_rfl
  have hupper : graph_matching_num (G.deleteEdges ((M.edgeSet \ {s(v, w)}) ∪ {s(u, v)})) ≤ μ + 1 :=
    le_trans
      (residual_matching_num_single_edge_exchange_iff_critical_num_mono (residual_matching_num_single_edge_exchange_iff_critical_upper hvw))
      (residual_matching_num_single_edge_exchange_iff_critical_one_edge _ v w)
  have hHup : graph_matching_num ((G.deleteEdges M.edgeSet) ⊔ SimpleGraph.edge v w) ≤ μ + 1 :=
    residual_matching_num_single_edge_exchange_iff_critical_one_edge _ v w
  constructor
  · intro h
    refine residual_matching_num_single_edge_exchange_iff_critical_lt_succ_eq hμtop hHup ?_
    calc μ < μ + 1 := hone
      _ = graph_matching_num (G.deleteEdges ((M.edgeSet \ {s(v, w)}) ∪ {s(u, v)})) := h.symm
      _ ≤ graph_matching_num ((G.deleteEdges M.edgeSet) ⊔ SimpleGraph.edge v w) :=
        residual_matching_num_single_edge_exchange_iff_critical_num_mono (residual_matching_num_single_edge_exchange_iff_critical_upper hvw)
  · intro h
    have hlt : μ < graph_matching_num ((G.deleteEdges M.edgeSet) ⊔ SimpleGraph.edge v w) := by
      rw [h]
      exact hone
    unfold graph_matching_num at hlt
    rw [lt_iSup_iff] at hlt
    obtain ⟨K, hK⟩ := hlt
    rw [lt_iSup_iff] at hK
    obtain ⟨hKmatch, hKencard⟩ := hK
    have hvwK : s(v, w) ∈ K.edgeSet := by
      by_contra hnot
      have hsub : K.edgeSet ⊆ (G.deleteEdges M.edgeSet).edgeSet := by
        intro e he
        have heH : e ∈ ((G.deleteEdges M.edgeSet) ⊔ SimpleGraph.edge v w).edgeSet := K.edgeSet_subset he
        rw [SimpleGraph.edgeSet_sup, Set.mem_union] at heH
        rcases heH with he1 | he2
        · exact he1
        · rw [SimpleGraph.edgeSet_edge] at he2
          have : e = s(v, w) := he2.1
          subst this
          exact False.elim (hnot he)
      obtain ⟨K', hK'match, hK'edge⟩ := residual_matching_num_single_edge_exchange_iff_critical_copy K hKmatch hsub
      have hle : K'.edgeSet.encard ≤ μ :=
        le_iSup_of_le K' (le_iSup_of_le hK'match le_rfl)
      rw [hK'edge] at hle
      exact lt_irrefl _ (lt_of_le_of_lt hle hKencard)
    have huvK : s(u, v) ∉ K.edgeSet :=
      residual_matching_num_single_edge_exchange_iff_critical_uv_notin K hKmatch hu hvw hvwK
    have hKsub : K.edgeSet ⊆ (G.deleteEdges ((M.edgeSet \ {s(v, w)}) ∪ {s(u, v)})).edgeSet := by
      intro e he
      exact residual_matching_num_single_edge_exchange_iff_critical_lower hvw (K.edgeSet_subset he) (fun heuv => huvK (heuv ▸ he))
    obtain ⟨K', hK'match, hK'edge⟩ := residual_matching_num_single_edge_exchange_iff_critical_copy K hKmatch hKsub
    have hKle : K'.edgeSet.encard ≤ graph_matching_num (G.deleteEdges ((M.edgeSet \ {s(v, w)}) ∪ {s(u, v)})) :=
      le_iSup_of_le K' (le_iSup_of_le hK'match le_rfl)
    rw [hK'edge] at hKle
    have hlt2 : μ < graph_matching_num (G.deleteEdges ((M.edgeSet \ {s(v, w)}) ∪ {s(u, v)})) :=
      lt_of_lt_of_le hKencard hKle
    exact residual_matching_num_single_edge_exchange_iff_critical_lt_succ_eq hμtop hupper hlt2
