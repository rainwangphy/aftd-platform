import AFTD.Prelude

/-!
# brgc_word

Topic: combinatorics   Node: f4531bc8dd10

Provenance: formalization of a published result. Source: arXiv:2610.24758 (Optimal single-track Gray codes from Gray-ordered necklaces), Conjecture 1 (prime case of a conjecture from 2007), Sec. 1; the BRGC g(t) = t xor floor(t/2) of Sec. 1

The binary reflected Gray code word of rank t, read as a binary number: g(t) = t xor floor(t/2).
-/

/-- The binary reflected Gray code word of rank t, read as a binary number: g(t) = t xor floor(t/2). -/
def brgc_word (t : ℕ) : ℕ := t ^^^ (t / 2)
