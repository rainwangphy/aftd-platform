import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryRepetitionCode
import AFTD.Kb.Tcs.IsJointPerfectCode
import AFTD.Kb.Tcs.BinaryRepetitionCodeCard
import AFTD.Kb.Tcs.BinaryRepetitionCodeIsJointErrorCorrectingDetecting
import AFTD.Kb.Tcs.SumChooseJointBoundBinary
import AFTD.Kb.Tcs.IsJointErrorCorrectingDetecting

/-!
# binary_repetition_code_is_joint_perfect_code

Topic: information   Node: 34e89d1881e4

Provenance: formalization of a published result. Source: arXiv:2611.18156 Theorem IV.3

For an explicit natural number n with 2 ≤ n and natural numbers c, c' such that 2 * c + c' + 1 = n, the binary repetition code of length n is a (c, c') joint perfect code, that is, `is_joint_perfect_code c c' (binary_repetition_code n)` holds.
-/

/-- Binary repetition codes of length n ≥ 2 are (c, c') joint perfect codes for all c, c' with 2c + c' + 1 = n (Theorem IV.3). -/
theorem binary_repetition_code_is_joint_perfect_code (n c c' : ℕ) (hn : 2 ≤ n)
    (h_dim : 2 * c + c' + 1 = n) :
    is_joint_perfect_code c c' (binary_repetition_code n) := by
  refine ⟨binary_repetition_code_is_joint_error_correcting_detecting n c c' hn h_dim, ?_⟩
  simp only [binary_repetition_code_card n (by omega), show (2 - 1 : ℕ) = 1 from rfl,
    one_pow, mul_one, sum_choose_joint_bound_binary n c c' h_dim]
