import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957ExceptionalPoolExampleForbidden

/-!
# op1957_exceptional_pool_example_graph

Topic: graphs   Node: 8a79079aa625

Provenance: helper lemma. OP-1957; exceptional 44-vertex graph, experiments 40070–40073.

The exceptional 44-vertex graph with edges at the distinct pairs forbidden in neither order.
-/

def op1957_exceptional_pool_example_graph : SimpleGraph (Fin 44) := {
  Adj u v := u ≠ v ∧ ¬ op1957_exceptional_pool_example_forbidden u v ∧ ¬ op1957_exceptional_pool_example_forbidden v u
  symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩
}
