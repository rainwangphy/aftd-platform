import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.G

/-!
# subcubic_rich_neighbor_five_isolated_vertex_extend

Topic: graphs   Node: 70551c1c96f4

Provenance: helper lemma. step towards subcubic_maxDegree_induce_V3_le_two_exists_rich_neighbor_five_coloring

If v is an isolated vertex of the finite simple graph G and the induced subgraph of G on the vertices other than v admits a rich-neighbor 5-edge-colouring, then G admits one.
-/

lemma subcubic_rich_neighbor_five_isolated_vertex_extend_not_mem_edge {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hiso : G.degree v = 0) (e : G.edgeSet) : ¬ v ∈ (e : Sym2 V) := by
  intro hv
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h x y =>
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · have hnb : y ∈ G.neighborFinset v := by
        simp only [SimpleGraph.mem_neighborFinset]
        exact he
      have hpos : 0 < G.degree v := Finset.card_pos.mpr ⟨y, hnb⟩
      omega
    · have hnb : x ∈ G.neighborFinset v := by
        simp only [SimpleGraph.mem_neighborFinset]
        exact he.symm
      have hpos : 0 < G.degree v := Finset.card_pos.mpr ⟨x, hnb⟩
      omega

lemma subcubic_rich_neighbor_five_isolated_vertex_extend_to_edgeSet_prop {V : Type*}
    (G : SimpleGraph V) (s : Set V) (e : (G.induce s).edgeSet) :
    Sym2.map Subtype.val e.1 ∈ G.edgeSet := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    rw [SimpleGraph.mem_edgeSet] at he
    exact he

def subcubic_rich_neighbor_five_isolated_vertex_extend_toG {V : Type*}
    (G : SimpleGraph V) (s : Set V) (e : (G.induce s).edgeSet) : G.edgeSet :=
  ⟨Sym2.map Subtype.val e.1, subcubic_rich_neighbor_five_isolated_vertex_extend_to_edgeSet_prop G s e⟩

lemma subcubic_rich_neighbor_five_isolated_vertex_extend_toG_injective {V : Type*}
    (G : SimpleGraph V) (s : Set V) :
    Function.Injective (subcubic_rich_neighbor_five_isolated_vertex_extend_toG G s) := by
  intro e₁ e₂ h
  obtain ⟨e₁, h₁⟩ := e₁
  obtain ⟨e₂, h₂⟩ := e₂
  simp only [subcubic_rich_neighbor_five_isolated_vertex_extend_toG, Subtype.mk.injEq] at h
  exact Subtype.ext (Sym2.map.injective Subtype.val_injective h)

lemma subcubic_rich_neighbor_five_isolated_vertex_extend_toG_surjective {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hiso : G.degree v = 0) :
    Function.Surjective (subcubic_rich_neighbor_five_isolated_vertex_extend_toG G {w | w ≠ v}) := by
  intro ⟨e, he⟩
  induction e using Sym2.ind with
  | h x y =>
    have hxv : x ≠ v := by
      intro h
      apply subcubic_rich_neighbor_five_isolated_vertex_extend_not_mem_edge G v hiso ⟨s(x, y), he⟩
      simp [h]
    have hyv : y ≠ v := by
      intro h
      apply subcubic_rich_neighbor_five_isolated_vertex_extend_not_mem_edge G v hiso ⟨s(x, y), he⟩
      simp [h]
    let x' : {w | w ≠ v} := ⟨x, hxv⟩
    let y' : {w | w ≠ v} := ⟨y, hyv⟩
    have he' : s(x', y') ∈ (G.induce {w | w ≠ v}).edgeSet := by
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj]
      exact he
    refine ⟨⟨s(x', y'), he'⟩, ?_⟩
    apply Subtype.ext
    change Sym2.map Subtype.val s(x', y') = s(x, y)
    rw [Sym2.map_mk]

lemma subcubic_rich_neighbor_five_isolated_vertex_extend_toG_adj_iff {V : Type*}
    (G : SimpleGraph V) (s : Set V) (e₁ e₂ : (G.induce s).edgeSet) :
    G.lineGraph.Adj (subcubic_rich_neighbor_five_isolated_vertex_extend_toG G s e₁)
      (subcubic_rich_neighbor_five_isolated_vertex_extend_toG G s e₂) ↔
      (G.induce s).lineGraph.Adj e₁ e₂ := by
  rw [SimpleGraph.lineGraph_adj_iff_exists, SimpleGraph.lineGraph_adj_iff_exists]
  have hne : subcubic_rich_neighbor_five_isolated_vertex_extend_toG G s e₁ ≠
      subcubic_rich_neighbor_five_isolated_vertex_extend_toG G s e₂ ↔ e₁ ≠ e₂ :=
    (subcubic_rich_neighbor_five_isolated_vertex_extend_toG_injective G s).ne_iff
  rw [hne]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨w, hw₁, hw₂⟩
    rw [subcubic_rich_neighbor_five_isolated_vertex_extend_toG, Subtype.coe_mk, Sym2.mem_map] at hw₁ hw₂
    rcases hw₁ with ⟨u₁, hu₁, rfl⟩
    rcases hw₂ with ⟨u₂, hu₂, hu_eq⟩
    have : u₁ = u₂ := Subtype.ext hu_eq.symm
    subst this
    exact ⟨u₁, hu₁, hu₂⟩
  · rintro ⟨u, hu₁, hu₂⟩
    refine ⟨u.val, ?_, ?_⟩
    · rw [subcubic_rich_neighbor_five_isolated_vertex_extend_toG, Subtype.coe_mk, Sym2.mem_map]
      exact ⟨u, hu₁, rfl⟩
    · rw [subcubic_rich_neighbor_five_isolated_vertex_extend_toG, Subtype.coe_mk, Sym2.mem_map]
      exact ⟨u, hu₂, rfl⟩

noncomputable def subcubic_rich_neighbor_five_isolated_vertex_extend_iso {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hiso : G.degree v = 0) :
    (G.induce {w | w ≠ v}).lineGraph ≃g G.lineGraph where
  toEquiv := Equiv.ofBijective (subcubic_rich_neighbor_five_isolated_vertex_extend_toG G {w | w ≠ v})
    ⟨subcubic_rich_neighbor_five_isolated_vertex_extend_toG_injective G _,
     subcubic_rich_neighbor_five_isolated_vertex_extend_toG_surjective G v hiso⟩
  map_rel_iff' := by
    intro a b
    exact subcubic_rich_neighbor_five_isolated_vertex_extend_toG_adj_iff G _ a b

lemma subcubic_rich_neighbor_five_isolated_vertex_extend_rich_edge_transport
    {V₁ V₂ α : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    (iso : G₁.lineGraph ≃g G₂.lineGraph) (c₁ : G₁.lineGraph.Coloring α) (e₁ : G₁.edgeSet) :
    simple_graph_edge_is_rich G₂ (c₁.comp iso.symm.toHom) (iso e₁) ↔
    simple_graph_edge_is_rich G₁ c₁ e₁ := by
  dsimp [simple_graph_edge_is_rich]
  constructor
  · intro h f₁ g₁ hadj_f hadj_g hne
    have hadj_f₂ : G₂.lineGraph.Adj (iso e₁) (iso f₁) := iso.map_adj_iff.mpr hadj_f
    have hadj_g₂ : G₂.lineGraph.Adj (iso e₁) (iso g₁) := iso.map_adj_iff.mpr hadj_g
    have hne₂ : iso f₁ ≠ iso g₁ := iso.toEquiv.injective.ne hne
    have hdiff := h (iso f₁) (iso g₁) hadj_f₂ hadj_g₂ hne₂
    change c₁ (iso.symm (iso f₁)) ≠ c₁ (iso.symm (iso g₁)) at hdiff
    simp only [RelIso.symm_apply_apply] at hdiff
    exact hdiff
  · intro h f₂ g₂ hadj_f hadj_g hne
    have hadj_f₁ : G₁.lineGraph.Adj e₁ (iso.symm f₂) := by
      have := iso.symm.map_adj_iff.mpr hadj_f
      simpa using this
    have hadj_g₁ : G₁.lineGraph.Adj e₁ (iso.symm g₂) := by
      have := iso.symm.map_adj_iff.mpr hadj_g
      simpa using this
    have hne₁ : iso.symm f₂ ≠ iso.symm g₂ := iso.symm.toEquiv.injective.ne hne
    have hdiff := h (iso.symm f₂) (iso.symm g₂) hadj_f₁ hadj_g₁ hne₁
    exact hdiff

lemma subcubic_rich_neighbor_five_isolated_vertex_extend_rich_neighbor_transport
    {V₁ V₂ α : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    (iso : G₁.lineGraph ≃g G₂.lineGraph) (c₁ : G₁.lineGraph.Coloring α)
    (hc₁ : simple_graph_is_rich_neighbor_coloring G₁ c₁) :
    simple_graph_is_rich_neighbor_coloring G₂ (c₁.comp iso.symm.toHom) := by
  dsimp [simple_graph_is_rich_neighbor_coloring] at hc₁ ⊢
  intro e₂ ⟨f₂, hadj₂⟩
  let e₁ := iso.symm e₂
  have hadj₁ : G₁.lineGraph.Adj e₁ (iso.symm f₂) := by
    have := iso.symm.map_adj_iff.mpr hadj₂
    simpa using this
  obtain ⟨f₁, hadj_f₁, hrich₁⟩ := hc₁ e₁ ⟨iso.symm f₂, hadj₁⟩
  refine ⟨iso f₁, ?_, ?_⟩
  · have := iso.map_adj_iff.mpr hadj_f₁
    simpa [e₁] using this
  · exact (subcubic_rich_neighbor_five_isolated_vertex_extend_rich_edge_transport G₁ G₂ iso c₁ f₁).mpr hrich₁

/-- Deleting an isolated vertex does not change the edge set, so a rich-neighbour 5-edge-colouring of the induced subgraph on the remaining vertices transports to the whole graph. -/
theorem subcubic_rich_neighbor_five_isolated_vertex_extend {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hiso : G.degree v = 0)
    (hc : ∃ c : (G.induce {w | w ≠ v}).lineGraph.Coloring (Fin 5),
      simple_graph_is_rich_neighbor_coloring (G.induce {w | w ≠ v}) c) :
    ∃ c : G.lineGraph.Coloring (Fin 5), simple_graph_is_rich_neighbor_coloring G c := by
  obtain ⟨c, hc⟩ := hc
  let iso := subcubic_rich_neighbor_five_isolated_vertex_extend_iso G v hiso
  exact ⟨c.comp iso.symm.toHom,
    subcubic_rich_neighbor_five_isolated_vertex_extend_rich_neighbor_transport _ _ iso c hc⟩
