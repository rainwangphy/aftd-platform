import AFTD.Prelude

/-!
# bitword_rotate

Topic: combinatorics   Node: c5e0de593f0e

Provenance: formalization of a published result. Source: arXiv:2610.24758 (Optimal single-track Gray codes from Gray-ordered necklaces), Conjecture 1 (prime case of a conjecture from 2007), Sec. 1; cyclic shift of words

Cyclic rotation of an n-bit word x (a number below 2^n) by one position: the word is shifted up and its top bit moves to the bottom.
-/

/-- Cyclic rotation of an n-bit word x (a number below 2^n) by one position: the word is shifted up and its top bit moves to the bottom. -/
def bitword_rotate (n x : ℕ) : ℕ := (2 * x) % 2 ^ n + x / 2 ^ (n - 1)
