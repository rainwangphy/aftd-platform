import AFTD.Prelude
import AFTD.Kb.Tcs.IsPerronVector
import AFTD.Kb.Tcs.IsPrincipalVertex

/-!
# exists_principal_vertex_of_is_perron_vector

Topic: graphs   Node: 11098020929f

Provenance: helper lemma. folklore

In any finite nonempty simple graph G, if there exists a Perron vector vec, then there exists a principal vertex u of G.
-/

/-- If a finite nonempty simple graph has a Perron vector, then it has a principal vertex. -/
theorem exists_principal_vertex_of_is_perron_vector
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) (vec : V → ℝ) (hvec : is_perron_vector G vec) :
    ∃ u : V, is_principal_vertex G u := by
  obtain ⟨u, hu⟩ := Finite.exists_max vec
  exact ⟨u, vec, hvec, hu⟩
