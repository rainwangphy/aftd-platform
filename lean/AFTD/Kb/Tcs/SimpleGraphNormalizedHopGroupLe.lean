import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNormalizedHopGroup
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphIsHopInv
import AFTD.Kb.Tcs.SimpleGraphNormalizedHop

/-!
# simple_graph_normalized_hop_group_le

Topic: graphs   Node: ccd4e1859dbc

Provenance: helper lemma. Uniform structural helper for IN-262 / OP-543, using the hop and leap-group definitions of arXiv:2610.18463. The universal quadratic word bound is a question proposed here, not a theorem of that paper. No diameter estimate or research advance is claimed by this algebraic normalization.

For a fixed baseline hop, its normalized subgroup is contained in the original leap group.
-/

theorem simple_graph_normalized_hop_group_le {V : Type*}
    (G : SimpleGraph V) (h₀ : Equiv.Perm V) (hh₀ : simple_graph_is_hop G h₀) :
    simple_graph_normalized_hop_group G h₀ ≤ simple_graph_leap_group G := by
  rw [simple_graph_normalized_hop_group, Subgroup.closure_le]
  intro p hp
  have ha : h₀⁻¹ ∈ simple_graph_leap_group G :=
    Subgroup.subset_closure (simple_graph_is_hop_inv G h₀ hh₀)
  have hb : h₀*p ∈ simple_graph_leap_group G := Subgroup.subset_closure hp
  simpa [mul_assoc] using (simple_graph_leap_group G).mul_mem ha hb
