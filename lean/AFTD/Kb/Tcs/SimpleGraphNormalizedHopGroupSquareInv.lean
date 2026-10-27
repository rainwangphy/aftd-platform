import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphIsHopInv
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop

/-!
# simple_graph_normalized_hop_group_square_inv

Topic: graphs   Node: 5be7c88ab2a0

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

The inverse square of a baseline hop belongs to the normalized subgroup.
-/

theorem simple_graph_normalized_hop_group_square_inv {V : Type*}
    (G : SimpleGraph V) (h₀ : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀) :
    h₀⁻¹*h₀⁻¹ ∈ simple_graph_normalized_hop_group G h₀ := by
  apply Subgroup.subset_closure
  change simple_graph_is_hop G (h₀*(h₀⁻¹*h₀⁻¹))
  simpa [mul_assoc] using simple_graph_is_hop_inv G h₀ hh₀
