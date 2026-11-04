import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily

/-!
# simple_graph_triangle_edge_family_induce_map

Topic: graphs   Node: a9ba9065680c

Provenance: helper lemma. Induced-side transport for the published separator reduction, https://www.cs.tau.ac.il/~krivelev/2.pdf, Lemma 5.

The image of the triangle edge-family of an induced graph is exactly the original graph triangle edge-family restricted to triangles inside the retained vertex set.
-/

private theorem in519_vertex_edges_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (s : Finset α) :
    finite_vertex_set_edge_encoding (s.map f) = (finite_vertex_set_edge_encoding s).map f.sym2Map := by
  classical
  apply Finset.ext
  intro e
  constructor
  · intro he
    have he' := Finset.mem_filter.mp he
    rw [Finset.sym2_map] at he'
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp he'.1
    apply Finset.mem_map.mpr
    refine ⟨z,Finset.mem_filter.mpr ⟨hz,?_⟩,rfl⟩
    intro hzdiag
    apply he'.2
    exact hzdiag.map
  · intro he
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp he
    have hz' := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · rw [Finset.sym2_map]
      exact Finset.mem_map.mpr ⟨z,hz'.1,rfl⟩
    · intro hzdiag
      apply hz'.2
      exact (Sym2.isDiag_map f.injective).mp hzdiag

open Classical

theorem simple_graph_triangle_edge_family_induce_map {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    (simple_graph_triangle_edge_family (G.induce (S : Set V))).image
        (fun E => E.map (Function.Embedding.subtype (fun x => x ∈ S)).sym2Map) =
      (((Finset.univ : Finset (Finset V)).filter
        (fun t => G.IsNClique 3 t ∧ t ⊆ S)).image finite_vertex_set_edge_encoding) := by
  have henc : ∀ t' : Finset (S : Set V),
      finite_vertex_set_edge_encoding (t'.map (Function.Embedding.subtype _)) =
        (finite_vertex_set_edge_encoding t').map
          (Function.Embedding.subtype (fun x => x ∈ S)).sym2Map := by
    intro t'
    simp only [finite_vertex_set_edge_encoding]
    rw [Finset.sym2_map, Finset.filter_map]
    congr 1
    ext e
    simp only [Finset.mem_filter, Function.comp, Function.Embedding.sym2Map_apply,
      Function.Embedding.coe_subtype]
    rw [Sym2.isDiag_map Subtype.val_injective]
  ext E
  simp only [simple_graph_triangle_edge_family, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨E', ⟨t', ht', rfl⟩, rfl⟩
    refine ⟨t'.map (Function.Embedding.subtype _), ⟨?_, ?_⟩, henc t'⟩
    · exact (SimpleGraph.isNClique_induce_iff (G := G) (S : Set V) t' 3).mp ht'
    · intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
      exact y.2
  · rintro ⟨t, ⟨ht, hS⟩, rfl⟩
    let t' : Finset (S : Set V) := t.subtype (fun x => x ∈ (S : Set V))
    have hmap : t'.map (Function.Embedding.subtype _) = t :=
      Finset.subtype_map_of_mem (fun x hx => Finset.mem_coe.mpr (hS hx))
    refine ⟨finite_vertex_set_edge_encoding t', ⟨t', ?_, rfl⟩, ?_⟩
    · rw [SimpleGraph.isNClique_induce_iff, hmap]
      exact ht
    · rw [← henc, hmap]
