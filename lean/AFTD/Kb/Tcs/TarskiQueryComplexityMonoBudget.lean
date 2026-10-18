import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.Tcs.TarskiQueryComplexityLe

/-!
# tarski_query_complexity_mono_budget

Topic: algorithms   Node: 0ec4c362c26b

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Query complexity is monotone in the query budget: any algorithm using at most q queries also satisfies the bound for any q' ≥ q.
-/

/-- Query complexity is monotone in the query budget: any algorithm using at most q queries also satisfies the bound for any q' ≥ q. -/
theorem tarski_query_complexity_mono_budget (n k q q' : ℕ)
    (h : tarski_query_complexity_le n k q) (hle : q ≤ q') :
    tarski_query_complexity_le n k q' := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, fun f hf => ⟨(ht f hf).1, le_trans (ht f hf).2 hle⟩⟩
