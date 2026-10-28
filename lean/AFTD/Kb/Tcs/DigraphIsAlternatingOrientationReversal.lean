import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsAlternatingOrientation
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# digraph_is_alternating_orientation_reversal

Topic: graphs   Node: f6310963a2d8

Provenance: helper lemma. step towards three_connected_plane_eulerian_arborescence_minimizers_alternating

The reversal of an alternating orientation of a graph for a rotation system σ is also an alternating orientation for σ.
-/

/-- The reversal of an alternating orientation of a graph for a rotation system σ is also an alternating orientation for σ. -/
theorem digraph_is_alternating_orientation_reversal {V : Type*}
    (G : SimpleGraph V) (σ : Equiv.Perm G.Dart) (D : Digraph V)
    (hD : digraph_is_alternating_orientation G σ D) :
    digraph_is_alternating_orientation G σ ⟨fun u v => D.Adj v u⟩ := by
  obtain ⟨⟨hor, hirr⟩, halt⟩ := hD
  constructor
  · constructor
    · intro u v
      exact or_comm.trans (hor u v)
    · intro u v
      exact hirr v u
  · intro d
    have key : ∀ e : G.Dart, D.Adj e.toProd.2 e.toProd.1 ↔ ¬ D.Adj e.toProd.1 e.toProd.2 := by
      intro e
      have h1 : D.Adj e.toProd.1 e.toProd.2 ∨ D.Adj e.toProd.2 e.toProd.1 :=
        (hor e.toProd.1 e.toProd.2).mpr e.adj
      have h2 : ¬ (D.Adj e.toProd.1 e.toProd.2 ∧ D.Adj e.toProd.2 e.toProd.1) :=
        hirr e.toProd.1 e.toProd.2
      constructor
      · intro h h'; exact h2 ⟨h', h⟩
      · intro h
        rcases h1 with h' | h'
        · exact absurd h' h
        · exact h'
    show D.Adj d.toProd.2 d.toProd.1 ↔ ¬ D.Adj (σ d).toProd.2 (σ d).toProd.1
    rw [key d, halt d, key (σ d)]
