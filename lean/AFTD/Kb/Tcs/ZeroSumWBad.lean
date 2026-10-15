import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumAdmissible
import AFTD.Kb.Tcs.ZeroSumGoodSubseq

/-!
# zero_sum_w_bad

Topic: combinatorics   Node: 79d3582825f4

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems), Sec. 1 (w-bad sequences).

An admissible sequence is w-bad when no nonempty subsequence satisfies (1.2).
-/

/-- `w`-bad: admissible, and no nonempty subsequence satisfies (1.2). -/
def zero_sum_w_bad (n : ℕ) {r : ℕ} (A : List (Fin r → ℤ)) : Prop :=
  zero_sum_admissible n A ∧ ∀ I, ¬ zero_sum_good_subseq n A I
