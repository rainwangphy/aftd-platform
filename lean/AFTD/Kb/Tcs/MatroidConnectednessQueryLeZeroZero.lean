import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidIndepQueryTree
import AFTD.Kb.Tcs.MatroidConnected
import AFTD.Kb.Tcs.MatroidConnectedOfSubsingleton
import AFTD.Kb.Tcs.MatroidIndepQueryTreeDepth
import AFTD.Kb.Tcs.MatroidConnectednessQueryLe
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEval

/-!
# matroid_connectedness_query_le_zero_zero

Topic: algorithms   Node: bc1c82436e36

Provenance: helper lemma. step towards matroid_connectedness_query_linear

The zero-element matroid requires 0 queries: on an empty ground set the matroid is vacuously connected.
-/

/-- On an empty ground set no query is needed: the matroid is vacuously connected. -/
theorem matroid_connectedness_query_le_zero_zero : matroid_connectedness_query_le 0 0 := by
  refine ⟨MatroidIndepQueryTree.leaf true, ?_, ?_⟩
  · simp [MatroidIndepQueryTree.depth]
  · intro M hM o ho
    have hconn : matroid_connected M := by
      apply matroid_connected_of_subsingleton
      rw [hM]
      exact Set.subsingleton_univ
    simp [MatroidIndepQueryTree.eval, hconn]
