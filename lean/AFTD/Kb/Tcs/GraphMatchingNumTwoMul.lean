import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# graph_matching_num_two_mul

Topic: graphs   Node: 1871c5a4a0b0

Provenance: helper lemma. step towards graph_matching_num_two_mul_le_card

Twice the matching number of G equals the supremum of twice the edge cardinalities of all matchings in G.
-/

/-- Twice the matching number of G equals the supremum of twice the edge cardinalities of all matchings in G. -/
theorem graph_matching_num_two_mul {V : Type*} (G : SimpleGraph V) :
    2 * graph_matching_num G = ⨆ (M : SimpleGraph.Subgraph G) (_ : M.IsMatching), 2 * M.edgeSet.encard := by
  simp_rw [graph_matching_num, ENat.mul_iSup]
