import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroup
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupSquareInv
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphIsHopInv

/-!
# simple_graph_normalized_hop_conjugate_mem

Topic: graphs   Node: 4cd595b06471

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

Conjugating one normalized allowed permutation by the baseline yields an element of the normalized SUBGROUP, without claiming it stays in the normalized generating set.
-/

theorem simple_graph_normalized_hop_conjugate_mem {V : Type*}
    (G : SimpleGraph V) (h₀ p : Equiv.Perm V)
    (hh₀ : simple_graph_is_hop G h₀) (hp : simple_graph_normalized_hop G h₀ p) :
    h₀*p*h₀⁻¹ ∈ simple_graph_normalized_hop_group G h₀ := by
  let K := simple_graph_normalized_hop_group G h₀
  have hq : h₀⁻¹*(h₀*p)⁻¹ ∈ K := by
    apply Subgroup.subset_closure
    change simple_graph_is_hop G (h₀*(h₀⁻¹*(h₀*p)⁻¹))
    simpa [mul_assoc] using simple_graph_is_hop_inv G (h₀*p) hp
  have hs : h₀⁻¹*h₀⁻¹ ∈ K :=
    simple_graph_normalized_hop_group_square_inv G h₀ hh₀
  convert K.mul_mem (K.inv_mem hq) hs using 1 <;> group
