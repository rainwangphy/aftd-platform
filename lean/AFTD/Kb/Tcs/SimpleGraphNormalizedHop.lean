import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_normalized_hop

Topic: graphs   Node: 363d098afd1e

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

A permutation p is allowed relative to baseline h0 when h0*p is an actual hop. Relative p may fix vertices; the resulting actual hop still moves every vertex to a neighbour.
-/

def simple_graph_normalized_hop {V : Type*} (G : SimpleGraph V)
    (h₀ p : Equiv.Perm V) : Prop := simple_graph_is_hop G (h₀*p)
