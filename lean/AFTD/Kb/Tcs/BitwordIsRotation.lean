import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordRotate

/-!
# bitword_is_rotation

Topic: combinatorics   Node: 69aea49867ca

Provenance: formalization of a published result. Source: arXiv:2610.24758 (Optimal single-track Gray codes from Gray-ordered necklaces), Conjecture 1 (prime case of a conjecture from 2007), Sec. 1; necklaces as classes under cyclic shift

The n-bit word y is a cyclic rotation of the n-bit word x, i.e. x and y lie in the same binary necklace.
-/

/-- The n-bit word y is a cyclic rotation of the n-bit word x, i.e. x and y lie in the same binary necklace. -/
def bitword_is_rotation (n x y : ℕ) : Prop := ∃ r < n, (bitword_rotate n)^[r] x = y
