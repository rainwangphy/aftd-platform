import AFTD.Prelude
import AFTD.Kb.Tcs.TuranHypergraph

/-!
# turan_hypergraph_four_card

Topic: combinatorics   Node: b39eb2dcc6f7

Provenance: helper lemma. arXiv:2611.16654:389

The balanced 3-partite Turán hypergraph T₄ on 4 vertices has exactly 3 hyperedges.
-/

/-- T_4 has 3 edges. -/
theorem turan_hypergraph_four_card : (turan_hypergraph 4).card = 3 := by decide
