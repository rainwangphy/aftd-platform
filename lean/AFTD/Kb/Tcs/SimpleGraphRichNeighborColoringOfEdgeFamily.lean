import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# simple_graph_rich_neighbor_coloring_of_edge_family

Topic: graphs   Node: 690ba245cb42

Provenance: helper lemma. Coloring-certificate transfer helper for OP-309 (arXiv:2610.21868, Conjecture1.1), used by the cyclic-family partial case and the pendant-triple graph adapter.

An indexed family of non-loop edges with colors yields a rich-neighbor coloring of its edge-family graph whenever properness and a rich-neighbor witness hold for every choice of edge indices. The indexing may contain duplicates.
-/

theorem simple_graph_rich_neighbor_coloring_of_edge_family {V E α : Type*} (F : E → Sym2 V)
    (hdiag : ∀ i, ¬ (F i).IsDiag) (c : E → α)
    (hp : ∀ i j, F i ≠ F j → (∃ v, v ∈ F i ∧ v ∈ F j) → c i ≠ c j)
    (hr : ∀ i, ∃ j, F i ≠ F j ∧ (∃ v, v ∈ F i ∧ v ∈ F j) ∧
      ∀ k l, F k ≠ F l → (F j ≠ F k ∧ ∃ v, v ∈ F j ∧ v ∈ F k) →
        (F j ≠ F l ∧ ∃ v, v ∈ F j ∧ v ∈ F l) → c k ≠ c l) :
    ∃ c : (SimpleGraph.fromEdgeSet (Set.range F)).lineGraph.Coloring α,
      simple_graph_is_rich_neighbor_coloring (SimpleGraph.fromEdgeSet (Set.range F)) c := by
  classical
  let G := SimpleGraph.fromEdgeSet (Set.range F)
  have hmem (i : E) : F i ∈ G.edgeSet := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨i,rfl⟩,hdiag i⟩
  let e : E → G.edgeSet := fun i => ⟨F i,hmem i⟩
  have hsurj : Function.Surjective e := by
    intro f
    have hf : f.val ∈ Set.range F \ Sym2.diagSet := by
      simpa only [G,SimpleGraph.edgeSet_fromEdgeSet] using f.property
    obtain ⟨i,hi⟩ := hf.1
    exact ⟨i,Subtype.ext hi⟩
  let idx : G.edgeSet → E := fun f => Classical.choose (hsurj f)
  have hidx (f : G.edgeSet) : F (idx f) = f.val :=
    congrArg Subtype.val (Classical.choose_spec (hsurj f))
  let col : G.edgeSet → α := fun f => c (idx f)
  have hproper : ∀ {f g : G.edgeSet}, G.lineGraph.Adj f g → col f ≠ col g := by
    intro f g hfg
    obtain ⟨hne,v,hvf,hvg⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hfg
    apply hp (idx f) (idx g)
    · rw [hidx,hidx]; exact fun h => hne (Subtype.ext h)
    · exact ⟨v,by simpa [hidx] using hvf,by simpa [hidx] using hvg⟩
  let coloring : G.lineGraph.Coloring α := { toFun := col, map_rel' := hproper }
  refine ⟨coloring, ?_⟩
  intro f _
  obtain ⟨j,hne,hshare,hrich⟩ := hr (idx f)
  have hfj : G.lineGraph.Adj f (e j) := by
    apply SimpleGraph.lineGraph_adj_iff_exists.mpr
    refine ⟨?_,?_⟩
    · intro h; apply hne; rw [hidx]; exact congrArg Subtype.val h
    · simpa [hidx,e] using hshare
  refine ⟨e j,hfj,?_⟩
  intro g h hjg hjh hgh
  apply hrich (idx g) (idx h)
  · rw [hidx,hidx]; exact fun h => hgh (Subtype.ext h)
  · obtain ⟨hne,v,hvj,hvg⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hjg
    refine ⟨?_,v,by simpa [e] using hvj,by simpa [hidx] using hvg⟩
    intro h; exact hne (Subtype.ext (by simpa [e,hidx] using h))
  · obtain ⟨hne,v,hvj,hvh⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hjh
    refine ⟨?_,v,by simpa [e] using hvj,by simpa [hidx] using hvh⟩
    intro h; exact hne (Subtype.ext (by simpa [e,hidx] using h))
