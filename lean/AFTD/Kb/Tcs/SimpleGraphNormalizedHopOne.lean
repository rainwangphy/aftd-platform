import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_normalized_hop_one

Topic: graphs   Node: 576d4ec0c7e9

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

The identity is allowed relative to any baseline hop.
-/

theorem simple_graph_normalized_hop_one {V : Type*} (G : SimpleGraph V)
    (h₀ : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀) :
    simple_graph_normalized_hop G h₀ 1 := by
  simpa [simple_graph_normalized_hop] using hh₀
