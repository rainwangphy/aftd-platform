import AFTD.Prelude
import AFTD.Kb.Tcs.C7BoxK3Graph
import AFTD.Kb.Tcs.C7BoxK3Distance

/-!
# c7_box_k3_graph_decidable_adj

Topic: graphs   Node: c2ab2ba197ef

Provenance: helper lemma. step towards not_forall_power_well_covered_diam_le_three_and_twin_free_bounded

Adjacency in C_7 (box) C_3 is decidable, since it is a Boolean condition on c7_box_k3_distance.
-/

/-- Decidability of adjacency in `c7_box_k3_graph`, needed for `decide` on finite facts. -/
instance c7_box_k3_graph_decidable_adj : DecidableRel c7_box_k3_graph.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v ∧ c7_box_k3_distance u v = 1))
