import AFTD.Prelude
import AFTD.Kb.Tcs.GtsGraph

/-!
# op223_adjacent_shift_retains_beneficiary_edges

Topic: graphs   Node: 95cd5c824769

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1

An adjacent generalized tree shift retains every edge incident to its beneficiary.
-/

open SimpleGraph

theorem op223_adjacent_shift_retains_beneficiary_edges {V : Type*}
    (T : SimpleGraph V) (u v w : V) (huv : T.Adj u v) (huw : T.Adj u w) :
    (gts_graph T u v u).Adj u w := by
  classical
  simp only [gts_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj]
  left
  refine ⟨huw, ?_⟩
  rintro ⟨z, hz, hvz, hzu⟩
  rcases Sym2.eq_iff.mp hz with ⟨huv', hwz⟩ | ⟨huz, hwv⟩
  · exact huv.ne huv'
  · exact hzu huz.symm
