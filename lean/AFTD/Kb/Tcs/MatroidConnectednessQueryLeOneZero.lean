import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnectednessQueryLe
import AFTD.Kb.Tcs.MatroidConnectedOfSubsingleton
import AFTD.Kb.Tcs.MatroidConnected
import AFTD.Kb.Tcs.MatroidIndepQueryTree
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEval
import AFTD.Kb.Tcs.MatroidIndepQueryTreeDepth

/-!
# matroid_connectedness_query_le_one_zero

Topic: algorithms   Node: c5c4e88c20f8

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

On a one-element ground set no query is needed: every matroid is connected.
-/

theorem matroid_connectedness_query_le_one_zero : matroid_connectedness_query_le 1 0 := by
  refine ⟨.leaf true, le_rfl, fun M _ o _ => ?_⟩
  simp only [MatroidIndepQueryTree.eval, true_iff]
  exact matroid_connected_of_subsingleton M Set.subsingleton_of_subsingleton
