import AFTD.Prelude
import AFTD.Kb.Tcs.PellNumber

/-!
# pell_number_mono_succ

Topic: automata   Node: 4d38d44d1229

Provenance: helper lemma. step towards pell_prefix_block_step

The Pell numbers are nondecreasing: P(m) ≤ P(m+1).
-/

/-- Pell numbers are nondecreasing, `pell_number m ≤ pell_number (m+1)`. -/
theorem pell_number_mono_succ (m : ℕ) : pell_number m ≤ pell_number (m + 1) := by
  induction m with
  | zero => decide
  | succ k =>
    have : pell_number (k + 1 + 1) = pell_number k + 2 * pell_number (k + 1) := rfl
    omega
