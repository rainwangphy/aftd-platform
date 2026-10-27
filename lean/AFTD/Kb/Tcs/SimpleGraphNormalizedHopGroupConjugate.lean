import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroup
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopConjugateMem
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop

/-!
# simple_graph_normalized_hop_group_conjugate

Topic: graphs   Node: adc642a0cf40

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

Conjugation by the baseline preserves the normalized subgroup.
-/

theorem simple_graph_normalized_hop_group_conjugate {V : Type*}
    (G : SimpleGraph V) (h₀ p : Equiv.Perm V)
    (hh₀ : simple_graph_is_hop G h₀)
    (hp : p ∈ simple_graph_normalized_hop_group G h₀) :
    h₀*p*h₀⁻¹ ∈ simple_graph_normalized_hop_group G h₀ := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hp
  · intro p hp
    exact simple_graph_normalized_hop_conjugate_mem G h₀ p hh₀ hp
  · simp
  · intro x y hx hy hcx hcy
    have hh := (simple_graph_normalized_hop_group G h₀).mul_mem hcx hcy
    convert hh using 1 <;> group
  · intro x hx hcx
    have hh := (simple_graph_normalized_hop_group G h₀).inv_mem hcx
    convert hh using 1 <;> group
