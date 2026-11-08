import AFTD.Prelude

/-!
# multipartite_upper_bound_split_parts

Topic: quantum_mechanics   Node: 133f28d155a5

Provenance: helper lemma. step towards multipartite_graph_state_tripartite_info_upper_bound

The parts of the multipartite graph whose colour set meets X but is not contained in X — i.e. the parts split by the cut at the colour class of X.
-/

/-- The parts whose colour set meets `X` but is not contained in `X`. -/
noncomputable def multipartite_upper_bound_split_parts {ι : Type*} [Fintype ι]
    (T : ι → Finset (Fin 4)) (X : Finset (Fin 4)) : Finset ι := Finset.univ.filter (fun i => (T i ∩ X).Nonempty ∧ ¬ (T i ⊆ X))
