import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordRotate

/-!
# bitword_is_aperiodic

Topic: combinatorics   Node: 03dbf732fee5

Provenance: formalization of a published result. Source: arXiv:2610.24758 (Optimal single-track Gray codes from Gray-ordered necklaces), Conjecture 1 and the remark after it; periodic necklaces are the exceptions at composite n

The n-bit word x is aperiodic (primitive): no rotation by 0 < r < n fixes it, i.e. its necklace has n distinct rotations.
-/

/-- The `n`-bit word `x` is aperiodic: no rotation by `0 < r < n` fixes it. -/
def bitword_is_aperiodic (n x : ℕ) : Prop :=
  ∀ r, 0 < r → r < n → (bitword_rotate n)^[r] x ≠ x
