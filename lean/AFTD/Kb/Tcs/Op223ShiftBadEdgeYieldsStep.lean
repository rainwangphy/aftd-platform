import AFTD.Prelude
import AFTD.Kb.Tcs.Op223AdjacentShiftRetainsBeneficiaryEdges
import AFTD.Kb.Tcs.Op223AdjacentIsGeneralizedTreeShift
import AFTD.Kb.Tcs.Op223GtsIsTree
import AFTD.Kb.Tcs.NonsustainableGtsStep
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.Tcs.IsNonsustainableTree
import AFTD.Kb.Tcs.IsGeneralizedTreeShift
import AFTD.Kb.Tcs.GtsGraph
import AFTD.Kb.Tcs.IsSustainableTree

/-!
# op223_shift_bad_edge_yields_step

Topic: graphs   Node: 5dc8276f9d34

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1

If a nonsustainable tree undergoes an adjacent shift and a retained beneficiary edge remains nonsustainable, the shift is a step between nonsustainable trees.
-/

open SimpleGraph

theorem op223_shift_bad_edge_yields_step {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : is_nonsustainable_tree T) (u v w : V)
    (huv : T.Adj u v) (huw : T.Adj u w)
    (hbad : ¬ is_sustainable_edge (gts_graph T u v u) s(u,w)) :
    nonsustainable_gts_step T (gts_graph T u v u) := by
  have hs := op223_adjacent_is_generalized_tree_shift T hT.1 u v huv
  have ht := op223_gts_is_tree T (gts_graph T u v u) hs
  have he := op223_adjacent_shift_retains_beneficiary_edges T u v w huv huw
  refine ⟨hT, ⟨ht, ?_⟩, hs⟩
  intro h
  exact hbad (h.2 s(u,w) he)
