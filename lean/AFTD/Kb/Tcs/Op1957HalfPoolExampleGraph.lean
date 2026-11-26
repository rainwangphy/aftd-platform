import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957HalfPoolExampleForbidden

/-!
# op1957_half_pool_example_graph

Topic: graphs   Node: f9fe6a7ea9c8

Provenance: helper lemma. OP-1957; explicit 52-vertex half-pool graph, experiments 39914, 39920, and 39925.

The 52-vertex graph whose edges are the distinct pairs forbidden in neither order.
-/

def op1957_half_pool_example_graph : SimpleGraph (Fin 52) := {
  Adj u v := u ≠ v ∧ ¬ op1957_half_pool_example_forbidden u v ∧ ¬ op1957_half_pool_example_forbidden v u
  symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩
}
