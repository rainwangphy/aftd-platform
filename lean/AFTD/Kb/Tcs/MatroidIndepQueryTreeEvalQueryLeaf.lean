import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIndepQueryTree
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEval

/-!
# matroid_indep_query_tree_eval_query_leaf

Topic: algorithms   Node: 0ec36c55c6b0

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

The one-query tree that asks S and outputs c on yes and b on no evaluates, on an oracle o, to c if o S = true and to b otherwise.
-/

theorem matroid_indep_query_tree_eval_query_leaf {α : Type*} (o : Finset α → Bool) (S : Finset α) (b c : Bool) :
    (MatroidIndepQueryTree.query S (.leaf b) (.leaf c)).eval o = if o S = true then c else b := by
  rfl
