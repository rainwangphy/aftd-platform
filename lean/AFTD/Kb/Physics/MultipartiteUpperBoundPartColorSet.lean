import AFTD.Prelude

/-!
# multipartite_upper_bound_part_color_set

Topic: quantum_mechanics   Node: 9f22135f70b6

Provenance: helper lemma. step towards multipartite_graph_state_tripartite_info_upper_bound

The set of colours that actually occur on a single part V i of a complete multipartite graph.
-/

/-- The set of colours occurring on the part `V i`. -/
noncomputable def multipartite_upper_bound_part_color_set {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, Fintype (V i)] (c : (Σ i, V i) → Fin 4) (i : ι) : Finset (Fin 4) := Finset.univ.image (fun v : V i => c ⟨i, v⟩)
