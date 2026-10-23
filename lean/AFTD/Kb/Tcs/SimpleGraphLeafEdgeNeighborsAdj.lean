import AFTD.Prelude

/-!
# simple_graph_leaf_edge_neighbors_adj

Topic: graphs   Node: 05cd1a199ce7

Provenance: helper lemma. step towards simple_graph_strong_five_edge_coloring_extend_leaf

Any two distinct lineGraph neighbors of a leaf edge e in G are adjacent in the line graph, because both must share the non-leaf endpoint of e.
-/

lemma simple_graph_leaf_edge_neighbors_adj_edge_eq_of_mem_of_degree_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e f : G.edgeSet) (v : V) (hleaf : G.degree v = 1) (he : v ∈ e.val) (hf : v ∈ f.val) :
    e = f := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hleaf
  obtain ⟨w, _, huniq⟩ := hleaf
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp he
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hf
  have haA : G.Adj v a := (SimpleGraph.mem_edgeSet G).mp (ha ▸ e.property)
  have hbA : G.Adj v b := (SimpleGraph.mem_edgeSet G).mp (hb ▸ f.property)
  exact Subtype.ext (by rw [ha, hb, huniq a haA, huniq b hbA])

/-- Any two distinct lineGraph neighbors of a leaf edge e in G are adjacent in the line graph, because both must share the non-leaf endpoint of e. -/
theorem simple_graph_leaf_edge_neighbors_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G.edgeSet) (v : V) (hv : v ∈ e.val) (hleaf : G.degree v = 1)
    (f g : G.edgeSet) (hf : G.lineGraph.Adj e f) (hg : G.lineGraph.Adj e g) (hfg : f ≠ g) :
    G.lineGraph.Adj f g := by
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hf hg ⊢
  obtain ⟨hef, x, hxe, hxf⟩ := hf
  obtain ⟨heg, y, hye, hyg⟩ := hg
  obtain ⟨w, _, huniq⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := G) (v := v)).mp hleaf
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp hv
  have haA : G.Adj v a := (SimpleGraph.mem_edgeSet G).mp (ha ▸ e.property)
  have haw : a = w := huniq a haA
  have hew : e.val = s(v, w) := by rw [ha, haw]
  have key : ∀ z : V, z ∈ e.val → z ≠ v → z = w := by
    intro z hz hzv
    rw [hew, Sym2.mem_iff] at hz
    exact hz.resolve_left hzv
  have hxv : x ≠ v := by
    intro hxv
    exact hef (simple_graph_leaf_edge_neighbors_adj_edge_eq_of_mem_of_degree_eq_one
      G f e v hleaf (hxv ▸ hxf) hv).symm
  have hyv : y ≠ v := by
    intro hyv
    exact heg (simple_graph_leaf_edge_neighbors_adj_edge_eq_of_mem_of_degree_eq_one
      G g e v hleaf (hyv ▸ hyg) hv).symm
  exact ⟨hfg, w, (key x hxe hxv) ▸ hxf, (key y hye hyv) ▸ hyg⟩
