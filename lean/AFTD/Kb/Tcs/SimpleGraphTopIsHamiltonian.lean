import AFTD.Prelude

/-!
# simple_graph_top_is_hamiltonian

Topic: graphs   Node: 5ad588e5802e

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_interpolation

The complete graph on at least three vertices contains a Hamilton cycle.
-/

/-- The complete graph on `Fin (n + 3)` is Hamiltonian, using the Eulerian cycle of `cycleGraph`. -/
private theorem simple_graph_top_is_hamiltonian_fin (n : ℕ) :
    (⊤ : SimpleGraph (Fin (n + 3))).IsHamiltonian := by
  refine SimpleGraph.IsHamiltonian.mono (G := SimpleGraph.cycleGraph (n + 3)) le_top ?_
  intro _
  refine ⟨0, SimpleGraph.cycleGraph.cycle n, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  exact ⟨SimpleGraph.cycleGraph.isCycle_cycle, by simp⟩

/-- The complete graph on at least three vertices is Hamiltonian. -/
theorem simple_graph_top_is_hamiltonian {V : Type*} [Fintype V] [DecidableEq V] (hV : 3 ≤ Fintype.card V) : (⊤ : SimpleGraph V).IsHamiltonian := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨Fintype.card V - 3, by omega⟩
  let φ : Fin (m + 3) ≃ V := (finCongr hm.symm).trans (Fintype.equivFin V).symm
  let f : (⊤ : SimpleGraph (Fin (m + 3))) →g (⊤ : SimpleGraph V) :=
    ⟨φ, by
      intro a b hab
      rw [SimpleGraph.top_adj] at hab ⊢
      exact fun h => hab (φ.injective h)⟩
  intro _
  obtain ⟨a₀, p, hp⟩ := simple_graph_top_is_hamiltonian_fin m
    (by have : Fintype.card (Fin (m + 3)) = m + 3 := Fintype.card_fin _; omega)
  exact ⟨φ a₀, p.map f, hp.map φ.bijective⟩
