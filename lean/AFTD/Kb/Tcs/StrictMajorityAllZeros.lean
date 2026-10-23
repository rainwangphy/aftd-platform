import AFTD.Prelude
import AFTD.Kb.Tcs.StrictMajority

/-!
# strictMajority_all_zeros

Topic: circuits   Node: 0dcd9eb58a94

Provenance: helper lemma. folklore

For any natural number n, evaluating the strict Majority function on the all-zeros input yields false.
-/

/-- The all-zeros input does not satisfy strict Majority. -/
theorem strictMajority_all_zeros (n : ℕ) :
    strictMajority n (fun _ => false) = false := by
  simp [strictMajority]
