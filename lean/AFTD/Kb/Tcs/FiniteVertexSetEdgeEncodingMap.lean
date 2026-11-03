import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# finite_vertex_set_edge_encoding_map

Topic: graphs   Node: 9b575b077969

Provenance: helper lemma. Graph separator transport infrastructure.

Encoding non-diagonal vertex pairs commutes with injective relabeling.
-/

theorem finite_vertex_set_edge_encoding_map {α β : Type*} [DecidableEq α] [DecidableEq β]
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
