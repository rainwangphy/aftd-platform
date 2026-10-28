import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsEulerianOrientation
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# digraph_eulerian_orientation_reversal

Topic: graphs   Node: deb4b0457d94

Provenance: helper lemma. step towards three_connected_plane_eulerian_arborescence_minimizers_alternating

The reversal of an Eulerian orientation of a simple graph is also an Eulerian orientation.
-/

/-- The reversal of an Eulerian orientation of a simple graph is also an Eulerian orientation. -/
theorem digraph_eulerian_orientation_reversal {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Digraph (Fin n)) [DecidableRel D.Adj]
    (hD : digraph_is_eulerian_orientation G D) :
    @digraph_is_eulerian_orientation n G ⟨fun u v => D.Adj v u⟩
      (fun u v => inferInstanceAs (Decidable (D.Adj v u))) := by
  unfold digraph_is_eulerian_orientation at *
  rcases hD with ⟨⟨h1, h2⟩, hD_deg⟩
  constructor
  · constructor
    · intro u v
      rw [or_comm]
      exact h1 u v
    · intro u v
      rw [and_comm]
      exact h2 u v
  · intro v
    exact (hD_deg v).symm
