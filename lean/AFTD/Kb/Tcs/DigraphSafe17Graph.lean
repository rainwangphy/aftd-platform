import AFTD.Prelude

/-!
# digraph_safe17_graph

Topic: graphs   Node: d37097c98c87

Provenance: helper lemma. Explicit safe-cycle obstruction for OP-110; experiments 13258 and 13260.

The seventeen-vertex cyclic digraph with the displayed seven out-steps.
-/

def digraph_safe17_graph : Digraph (Fin 17) := ⟨fun u v => (v-u).val ∈ ({1,2,3,5,6,7,13} : Finset ℕ)⟩
