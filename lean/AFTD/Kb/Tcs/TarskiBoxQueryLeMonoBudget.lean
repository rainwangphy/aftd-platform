import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLe
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.Tcs.TarskiQueryComplexityMonoBudget

/-!
# tarski_box_query_le_mono_budget

Topic: algorithms   Node: 853c0db5cbcb

Provenance: helper lemma. step towards tarski_box_query_le_five_log_sq

The box-local query invariant is monotone in the query budget: a box algorithm using at most q queries also satisfies the invariant for every larger budget q'.
-/

/-- Box-form analogue of tarski_query_complexity_mono_budget: the same tree witnesses the invariant for any larger budget. -/
theorem tarski_box_query_le_mono_budget (n k q q' : ℕ)
    (h : tarski_box_query_le n k q) (hle : q ≤ q') : tarski_box_query_le n k q' := by
  intro a b hab
  obtain ⟨t, ht⟩ := h a b hab
  refine ⟨t, fun f hf ha hb => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := ht f hf ha hb
  exact ⟨h1, h2, h3, le_trans h4 hle⟩
