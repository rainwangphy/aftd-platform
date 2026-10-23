import AFTD.Prelude
import AFTD.Kb.Tcs.StrictMajority

/-!
# strictMajority_all_ones

Topic: circuits   Node: c4de19e03b6f

Provenance: helper lemma. folklore

For any integer n > 0, evaluating the strict Majority function on the all-ones input yields true.
-/

/-- For n > 0, the all-ones input satisfies strict Majority. -/
theorem strictMajority_all_ones (n : ℕ) (hn : 0 < n) :
    strictMajority n (fun _ => true) = true := by
  unfold strictMajority
  simp
  omega
