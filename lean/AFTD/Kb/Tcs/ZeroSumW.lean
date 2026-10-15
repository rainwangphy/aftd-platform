import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumAdmissible
import AFTD.Kb.Tcs.ZeroSumGoodSubseq

/-!
# zero_sum_w

Topic: combinatorics   Node: 182efa062b0c

Provenance: formalization of a published result. Source: arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems), Sec. 1 (w_r(n), Sun's Definition 1.3).

w_r(n): the least N such that every admissible sequence of length N in ℤ^r has a nonempty subsequence whose sum is ≡ 0 (mod n) but ≢ 0 (mod n²) (⊤ if there is no such N).
-/

/-- `w_r(n)`, the least length forcing a subsequence with (1.2). -/
noncomputable def zero_sum_w (r n : ℕ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : ∀ A : List (Fin r → ℤ), A.length = N → zero_sum_admissible n A →
    ∃ I, zero_sum_good_subseq n A I), (N : ℕ∞)
