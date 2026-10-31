import AFTD.Prelude

/-!
# simple_graph_radius_eq_one_imp_exists_universal

Topic: graphs   Node: d768b814c3d1

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_interpolation

Any finite simple graph of radius 1 contains a universal vertex (adjacent to all other vertices).
-/

/-- A finite simple graph of radius 1 has a universal vertex. -/
theorem simple_graph_radius_eq_one_imp_exists_universal {V : Type*} [Fintype V] (G : SimpleGraph V) (hrad : G.radius = 1) : ∃ v : V, ∀ w : V, w ≠ v → G.Adj v w := by
  have hne : Nonempty V := by
    by_contra h
    have hem : IsEmpty V := not_nonempty_iff.mp h
    rw [SimpleGraph.radius_eq_top_of_isEmpty (α := V) (G := G)] at hrad
    simp at hrad
  obtain ⟨u, hu⟩ := G.exists_eccent_eq_radius
  refine ⟨u, fun w hw => ?_⟩
  exact G.eccent_le_one_iff u |>.mp (by rw [hu, hrad]) w (Ne.symm hw)
