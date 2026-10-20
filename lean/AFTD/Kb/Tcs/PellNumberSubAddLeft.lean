import AFTD.Prelude
import AFTD.Kb.Tcs.PellNumberMonoSucc
import AFTD.Kb.Tcs.PellNumber

/-!
# pell_number_sub_add_left

Topic: automata   Node: e57e626f648c

Provenance: helper lemma. step towards pell_prefix_block_step

P(m+1) - P(m) + 2 P(m) = P(m+2) - P(m+1).
-/

/-- Truncated-subtraction identity `(pell_number (m+1) - pell_number m) + 2 * pell_number m = pell_number (m+2) - pell_number (m+1)`. -/
theorem pell_number_sub_add_left (m : ℕ) : (pell_number (m + 1) - pell_number m) + 2 * pell_number m = pell_number (m + 2) - pell_number (m + 1) := by
  have hrec : pell_number (m + 2) = pell_number m + 2 * pell_number (m + 1) := rfl
  have h1 := pell_number_mono_succ m
  omega
