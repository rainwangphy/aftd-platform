import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIndepQueryTree
import AFTD.Kb.Tcs.MatroidIndepQueryTreeDepth

/-!
# matroid_indep_query_tree_depth_leaf

Topic: algorithms   Node: b667c9103f53

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

A leaf of an independence-query tree has depth 0.
-/

theorem matroid_indep_query_tree_depth_leaf {α : Type*} (b : Bool) :
    (MatroidIndepQueryTree.leaf b : MatroidIndepQueryTree α).depth = 0 := by
  rfl
