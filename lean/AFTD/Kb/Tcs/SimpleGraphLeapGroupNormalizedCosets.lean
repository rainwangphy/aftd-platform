import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroup
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupSquareInv
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupConjugate
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupSquare
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroupConjugateInv
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop

/-!
# simple_graph_leap_group_normalized_cosets

Topic: graphs   Node: b2c6b30646b2

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

Every leap lies in the normalized subgroup or in its left coset by the baseline hop. Together with containment, this gives index at most two WITHIN the leap group, not within the full permutation group. No finite, connected or diameter hypothesis is asserted.
-/

theorem simple_graph_leap_group_normalized_cosets {V : Type*}
    (G : SimpleGraph V) (h₀ : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀) :
    ∀ g ∈ simple_graph_leap_group G,
      g ∈ simple_graph_normalized_hop_group G h₀ ∨
        h₀⁻¹*g ∈ simple_graph_normalized_hop_group G h₀ := by
  let K := simple_graph_normalized_hop_group G h₀
  intro g hg
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
  · intro h hh
    right
    apply Subgroup.subset_closure
    change simple_graph_is_hop G (h₀*(h₀⁻¹*h))
    simpa [mul_assoc] using hh
  · exact Or.inl K.one_mem
  · intro x y hx hy hcx hcy
    rcases hcx with hcx | hcx <;> rcases hcy with hcy | hcy
    · exact Or.inl (K.mul_mem hcx hcy)
    · right
      have hc := simple_graph_normalized_hop_group_conjugate_inv G h₀ x hh₀ hcx
      have hh := K.mul_mem hc hcy
      convert hh using 1 <;> group
    · right
      simpa [mul_assoc] using K.mul_mem hcx hcy
    · left
      have hc := simple_graph_normalized_hop_group_conjugate G h₀ (h₀⁻¹*x) hh₀ hcx
      have hs := simple_graph_normalized_hop_group_square G h₀ hh₀
      have hh := K.mul_mem (K.mul_mem hc hs) hcy
      convert hh using 1 <;> group
  · intro x hx hcx
    rcases hcx with hcx | hcx
    · exact Or.inl (K.inv_mem hcx)
    · right
      have hc := simple_graph_normalized_hop_group_conjugate_inv G h₀
        (h₀⁻¹*x)⁻¹ hh₀ (K.inv_mem hcx)
      have hs := simple_graph_normalized_hop_group_square_inv G h₀ hh₀
      have hh := K.mul_mem hc hs
      convert hh using 1 <;> group
