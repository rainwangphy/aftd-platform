import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnectednessQueryLe
import AFTD.Kb.Tcs.MatroidIndepQueryTreeEval
import AFTD.Kb.Tcs.MatroidIndepQueryTreeDepth
import AFTD.Kb.Tcs.MatroidConnected
import AFTD.Kb.Tcs.MatroidIndepQueryTree

/-!
# matroid_connectedness_query_le_mono

Topic: algorithms   Node: 69ff5617f4ec

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

If connectedness of matroids on n elements can be decided with q independence queries, it can be decided with q' queries for every q' ≥ q.
-/

theorem matroid_connectedness_query_le_mono {n q q' : ℕ} (h : q ≤ q')
    (hq : matroid_connectedness_query_le n q) : matroid_connectedness_query_le n q' := by
  obtain ⟨T, hT, hM⟩ := hq
  exact ⟨T, hT.trans h, hM⟩
