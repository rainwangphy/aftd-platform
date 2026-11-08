import AFTD.Prelude

/-!
# multipartite_upper_bound_color_class

Topic: quantum_mechanics   Node: 13631738172e

Provenance: helper lemma. step towards multipartite_graph_state_tripartite_info_upper_bound

The colour class of a colouring of the vertex set of a complete multipartite graph: the vertices whose colour lies in the finite set X ⊆ Fin 4.
-/

/-- The set of vertices of `Σ i, V i` whose colour under `c` lies in `X`. -/
noncomputable def multipartite_upper_bound_color_class {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, Fintype (V i)] (c : (Σ i, V i) → Fin 4) (X : Finset (Fin 4)) :
    Finset (Σ i, V i) := Finset.univ.filter (fun v => c v ∈ X)
