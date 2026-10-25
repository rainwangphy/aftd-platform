import AFTD.Prelude

/-!
# brgc_inverse

Topic: combinatorics   Node: 3a778c67c86f

Provenance: formalization of a published result. Source: Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

The inverse prefix-parity transform on n-bit binary words, computed as the exclusive-or of all right shifts by less than n.
-/

def brgc_inverse : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => x ^^^ brgc_inverse n (x / 2)
