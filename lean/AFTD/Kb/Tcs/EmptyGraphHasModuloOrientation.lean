import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasModuloOrientation

/-!
# empty_graph_has_modulo_orientation

Topic: graphs   Node: 76cf31736161

Provenance: helper lemma. folklore

For every natural number q, the empty simple graph on the empty type Empty has a modulo-q orientation.
-/

/-- The empty graph on the empty vertex type has a modulo-q orientation for every modulus q. -/
theorem empty_graph_has_modulo_orientation (q : ℕ) : simple_graph_has_modulo_orientation (⊥ : SimpleGraph Empty) q := by
  unfold simple_graph_has_modulo_orientation
  refine ⟨fun _ _ => False, ⟨fun u => isEmptyElim u, fun u => isEmptyElim u⟩, fun v => isEmptyElim v⟩
