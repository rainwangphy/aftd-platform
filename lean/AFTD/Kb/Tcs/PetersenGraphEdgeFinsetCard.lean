import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenGraph

/-!
# petersen_graph_edgeFinset_card

Topic: np_completeness   Node: 02fb68fba18a

Provenance: helper lemma. Sanity check of petersen_graph (P10 has 15 edges), for arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs)

The Petersen graph petersen_graph has 15 edges (its edgeFinset, with adjacency decided by Disjoint, has card 15).
-/

theorem petersen_graph_edgeFinset_card :
    letI : DecidableRel petersen_graph.Adj := fun s t => inferInstanceAs (Decidable (Disjoint s.1 t.1))
    petersen_graph.edgeFinset.card = 15 := by
  decide
