import AFTD.Prelude
import AFTD.Kb.Tcs.PellNumberMonoSucc
import AFTD.Kb.Tcs.PellNumber

/-!
# pell_number_two_mul_sub_add

Topic: automata   Node: 7a6b65145789

Provenance: helper lemma. step towards pell_prefix_block_step

2(P(m+1) - P(m)) + 2 P(m) = 2 P(m+1).
-/

/-- Truncated-subtraction identity `2 * (pell_number (m+1) - pell_number m) + 2 * pell_number m = 2 * pell_number (m+1)`. -/
theorem pell_number_two_mul_sub_add (m : ℕ) : 2 * (pell_number (m + 1) - pell_number m) + 2 * pell_number m = 2 * pell_number (m + 1) := by
  have hle := pell_number_mono_succ m
  omega
