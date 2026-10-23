import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLeafEdgeNeighborsAdj
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard

Topic: graphs   Node: 7d6dd7c8ac1e

Provenance: helper lemma. step towards subcubic_isAcyclic_exists_rich_neighbor_five_coloring; replaces simple_graph_strong_five_edge_coloring_extend_leaf, whose Finset.filter count needs a DecidablePred instance that only the REPL session supplied, so that statement does not elaborate in the offline build

Given a leaf edge e of G with at most 4 other edges within distance 2 of e in the line graph (counted with Set.ncard), any strong 5-edge-colouring of G minus e extends to a strong 5-edge-colouring of G.
-/

def simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet) (f : G.edgeSet) (hf : f ≠ e) :
    (G.deleteEdges {e.val}).edgeSet :=
  ⟨f.val, by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨f.property, fun h => hf (Subtype.ext h)⟩⟩

@[simp] lemma simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner_val
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet) (f : G.edgeSet) (hf : f ≠ e) :
    (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f hf).val = f.val := rfl

lemma simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet)
    {f g : G.edgeSet} (hf : f ≠ e) (hg : g ≠ e) (h : G.lineGraph.Adj f g) :
    (G.deleteEdges {e.val}).lineGraph.Adj
      (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f hf)
      (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e g hg) := by
  refine ⟨?_, ?_⟩
  · intro heq
    exact h.1 (Subtype.ext (by have := congrArg Subtype.val heq; simpa using this))
  · simpa using h.2

lemma simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner_ne {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet)
    {f g : G.edgeSet} (hf : f ≠ e) (hg : g ≠ e) (h : f ≠ g) :
    simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f hf ≠
      simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e g hg := by
  intro heq
  exact h (Subtype.ext (by have := congrArg Subtype.val heq; simpa using this))

lemma simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_fresh (s : Finset (Fin 5)) (h : s.card ≤ 4) :
    ∃ k : Fin 5, k ∉ s := by
  by_contra hk
  push Not at hk
  have hsub : (Finset.univ : Finset (Fin 5)) ⊆ s := fun x _ => hk x
  have h1 : (Finset.univ : Finset (Fin 5)).card ≤ s.card := Finset.card_le_card hsub
  have h2 : (Finset.univ : Finset (Fin 5)).card = 5 := rfl
  omega

theorem simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G.edgeSet) (v : V) (hv : v ∈ e.val) (hleaf : G.degree v = 1)
    (hdeg : {f : G.edgeSet | f ≠ e ∧ (G.lineGraph.Adj e f ∨
      ∃ g : G.edgeSet, G.lineGraph.Adj g e ∧ G.lineGraph.Adj g f)}.ncard ≤ 4)
    (hc : ∃ c : (G.deleteEdges {e.val}).lineGraph.Coloring (Fin 5),
      ∀ f, simple_graph_edge_is_rich (G.deleteEdges {e.val}) c f) :
    ∃ c : G.lineGraph.Coloring (Fin 5), ∀ f, simple_graph_edge_is_rich G c f := by
  classical
  obtain ⟨c, hc⟩ := hc
  -- the edges within distance two of e, taken from `hdeg` itself
  obtain ⟨N, hN, hNcard⟩ : ∃ N : Finset G.edgeSet, (∀ f, f ∈ N ↔ (f ≠ e ∧
      (G.lineGraph.Adj e f ∨ ∃ g : G.edgeSet, G.lineGraph.Adj g e ∧ G.lineGraph.Adj g f))) ∧
      N.card ≤ 4 := by
    refine ⟨Set.toFinset {f : G.edgeSet | f ≠ e ∧ (G.lineGraph.Adj e f ∨
      ∃ g : G.edgeSet, G.lineGraph.Adj g e ∧ G.lineGraph.Adj g f)}, fun f => ?_, ?_⟩
    · rw [Set.mem_toFinset, Set.mem_ofPred_eq]
    · rw [← Set.ncard_eq_toFinset_card']
      exact hdeg
  let col0 : G.edgeSet → Fin 5 := fun f =>
    if h : f = e then 0 else c (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f h)
  obtain ⟨k, hk⟩ := simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_fresh (N.image col0)
    (Finset.card_image_le.trans hNcard)
  let col : G.edgeSet → Fin 5 := fun f =>
    if h : f = e then k else c (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f h)
  have col_ne : ∀ (f : G.edgeSet) (hf : f ≠ e),
      col f = c (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f hf) := by
    intro f hf; exact dif_neg hf
  have col_e : col e = k := dif_pos rfl
  have hkey : ∀ (f : G.edgeSet) (hf : f ≠ e),
      (G.lineGraph.Adj e f ∨ ∃ g : G.edgeSet, G.lineGraph.Adj g e ∧ G.lineGraph.Adj g f) →
      c (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f hf) ≠ k := by
    intro f hf h hck
    apply hk
    refine Finset.mem_image.mpr ⟨f, (hN f).mpr ⟨hf, h⟩, ?_⟩
    show (if h : f = e then 0 else c (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f h)) = k
    rw [dif_neg hf]
    exact hck
  have hproper : ∀ {f g : G.edgeSet}, G.lineGraph.Adj f g → col f ≠ col g := by
    intro f g hfg
    by_cases hfe : f = e
    · subst hfe
      have hge : g ≠ f := fun h => hfg.1 h.symm
      rw [col_e, col_ne g hge]
      exact (hkey g hge (Or.inl hfg)).symm
    · by_cases hge : g = e
      · subst hge
        rw [col_ne f hfe, col_e]
        exact hkey f hfe (Or.inl hfg.symm)
      · rw [col_ne f hfe, col_ne g hge]
        exact c.valid (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner_adj G e hfe hge hfg)
  refine ⟨{ toFun := col, map_rel' := fun {f g} h => hproper h }, ?_⟩
  intro f g h hfg hfh hgh
  show col g ≠ col h
  by_cases hfe : f = e
  · subst hfe
    have hge : g ≠ f := fun h' => hfg.1 h'.symm
    have hhe : h ≠ f := fun h' => hfh.1 h'.symm
    have hadj : G.lineGraph.Adj g h := simple_graph_leaf_edge_neighbors_adj G f v hv hleaf g h hfg hfh hgh
    rw [col_ne g hge, col_ne h hhe]
    exact c.valid (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner_adj G f hge hhe hadj)
  · by_cases hge : g = e
    · subst hge
      have hhe : h ≠ g := fun h' => hgh (h'.symm)
      rw [col_e, col_ne h hhe]
      exact (hkey h hhe (Or.inr ⟨f, hfg, hfh⟩)).symm
    · by_cases hhe : h = e
      · subst hhe
        rw [col_ne g hge, col_e]
        exact hkey g hge (Or.inr ⟨f, hfh, hfg⟩)
      · rw [col_ne g hge, col_ne h hhe]
        exact hc (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner G e f hfe) _ _
          (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner_adj G e hfe hge hfg)
          (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner_adj G e hfe hhe hfh)
          (simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard_corner_ne G e hge hhe hgh)
