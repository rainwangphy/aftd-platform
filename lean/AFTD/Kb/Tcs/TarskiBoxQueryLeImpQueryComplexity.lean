import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLe
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.TarskiQueryComplexityLe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.Tcs.TarskiQueryTree

/-!
# tarski_box_query_le_imp_query_complexity

Topic: algorithms   Node: 51e6b6d514fa

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

The box-local invariant implies the ambient query complexity notion, by taking the full box [0, n−1]^k (needs n ≥ 1 since Fin n has no Bot/Top for general n).
-/

/-- Box-local invariant on the full grid gives the ambient query-complexity bound. -/
theorem tarski_box_query_le_imp_query_complexity (n k q : ℕ) (hn : 1 ≤ n)
    (h : tarski_box_query_le n k q) : tarski_query_complexity_le n k q := by
  haveI : NeZero n := ⟨by omega⟩
  unfold tarski_box_query_le at h
  unfold tarski_query_complexity_le
  let a : Fin k → Fin n := fun _ => ⟨0, by omega⟩
  let b : Fin k → Fin n := fun _ => ⟨n - 1, by omega⟩
  have hab : a ≤ b := by
    intro i
    exact Fin.zero_le _
  obtain ⟨t, ht⟩ := h a b hab
  refine ⟨t, ?_⟩
  intro f hf
  have hfa : a ≤ f a := fun _ => Fin.zero_le _
  have hfb : f b ≤ b := by
    intro i
    rw [Fin.le_def]
    have := (f b i).isLt
    show (f b i : ℕ) ≤ n - 1
    omega
  obtain ⟨-, -, hfix, hcost⟩ := ht f hf hfa hfb
  exact ⟨hfix, hcost⟩
