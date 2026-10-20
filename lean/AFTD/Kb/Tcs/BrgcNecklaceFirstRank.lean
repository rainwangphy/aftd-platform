import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BitwordIsRotation

/-!
# brgc_necklace_first_rank

Topic: combinatorics   Node: e654de59e4f1

Provenance: formalization of a published result. Source: arXiv:2610.24758 (Optimal single-track Gray codes from Gray-ordered necklaces), Conjecture 1 (prime case of a conjecture from 2007), Sec. 1; first occurrences and the list D_n

t is the BRGC rank of the first occurrence of a nonconstant binary necklace of length n: t < 2^n, the word g(t) is neither 0^n nor 1^n, and no smaller rank s gives a word g(s) in the same necklace. The list D_n orders the nonconstant necklaces by these ranks.
-/

/-- t is the BRGC rank of the first occurrence of a nonconstant binary necklace of length n: t < 2^n, the word g(t) is neither 0^n nor 1^n, and no smaller rank s gives a word g(s) in the same necklace. The list D_n orders the nonconstant necklaces by these ranks. -/
def brgc_necklace_first_rank (n t : ℕ) : Prop :=
  t < 2 ^ n ∧ brgc_word t ≠ 0 ∧ brgc_word t ≠ 2 ^ n - 1 ∧
    ∀ s < t, ¬ bitword_is_rotation n (brgc_word s) (brgc_word t)
