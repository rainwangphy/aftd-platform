import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BitwordRotateIterateCut

/-!
# bitword_rotate_iterate_self

Topic: combinatorics   Node: 8e1778896e53

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

Left rotation n times fixes every nonconstant n-bit word when n is at least two.
-/

theorem bitword_rotate_iterate_self (n x : ℕ) (hn : 2 ≤ n) (hx0 : 0 < x)
    (hx1 : x < 2 ^ n - 1) : (bitword_rotate n)^[n] x = x := by
  have hx : x < 2 ^ n := by omega
  have hh := bitword_rotate_iterate_cut hn (show n + 0 = n by omega) hx
    (show (0 : ℕ) < 2 ^ 0 by decide)
    (show 0 < 2 ^ 0 * x + 0 by simpa using hx0)
    (show 2 ^ 0 * x + 0 < 2 ^ n - 1 by simpa using hx1)
  simpa using hh
