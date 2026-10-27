import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroup
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupSquareInv
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupConjugate
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupSquare
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_normalized_hop_group_conjugate_inv

Topic: graphs   Node: 49abdcdc3ace

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

Conjugation by the inverse baseline also preserves the normalized subgroup.
-/

theorem simple_graph_normalized_hop_group_conjugate_inv {V : Type*}
    (G : SimpleGraph V) (h₀ p : Equiv.Perm V)
    (hh₀ : simple_graph_is_hop G h₀)
    (hp : p ∈ simple_graph_normalized_hop_group G h₀) :
    h₀⁻¹*p*h₀ ∈ simple_graph_normalized_hop_group G h₀ := by
  let K := simple_graph_normalized_hop_group G h₀
  have hm := simple_graph_normalized_hop_group_conjugate G h₀ p hh₀ hp
  have hs := simple_graph_normalized_hop_group_square G h₀ hh₀
  have hsi := simple_graph_normalized_hop_group_square_inv G h₀ hh₀
  have hh := K.mul_mem (K.mul_mem hsi hm) hs
  convert hh using 1 <;> group
