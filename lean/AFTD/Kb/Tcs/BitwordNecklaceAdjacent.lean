import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordRotate

/-!
# bitword_necklace_adjacent

Topic: combinatorics   Node: b657b3186480

Provenance: formalization of a published result. Source: arXiv:2610.24758 (Optimal single-track Gray codes from Gray-ordered necklaces), Conjecture 1 (prime case of a conjecture from 2007), Sec. 1; the necklace graph Q_n

The necklaces of the n-bit words x and y are adjacent in the necklace graph Q_n: some rotation of x differs from y in exactly one bit.
-/

/-- The necklaces of the n-bit words x and y are adjacent in the necklace graph Q_n: some rotation of x differs from y in exactly one bit. -/
def bitword_necklace_adjacent (n x y : ℕ) : Prop :=
  ∃ r < n, ∃ i < n, (bitword_rotate n)^[r] x ^^^ y = 2 ^ i
