import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroup
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupSquareInv
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_normalized_hop_group_square

Topic: graphs   Node: 9a51934661cc

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

The square of a baseline hop belongs to the normalized subgroup.
-/

theorem simple_graph_normalized_hop_group_square {V : Type*}
    (G : SimpleGraph V) (h₀ : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀) :
    h₀*h₀ ∈ simple_graph_normalized_hop_group G h₀ := by
  have hh := (simple_graph_normalized_hop_group G h₀).inv_mem
    (simple_graph_normalized_hop_group_square_inv G h₀ hh₀)
  simpa using hh
