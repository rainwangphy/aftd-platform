import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsRotation
import AFTD.Kb.Tcs.BitwordRotateIterateSelf
import AFTD.Kb.Tcs.BitwordRotate

/-!
# bitword_is_rotation_symm_of_nonconstant

Topic: combinatorics   Node: a2449df11344

Provenance: helper lemma. Rotation bookkeeping for OP-392, arXiv:2610.24758, Conjecture 1.

For length at least two, cyclic-rotation equivalence is symmetric on a nonconstant n-bit word.
-/

theorem bitword_is_rotation_symm_of_nonconstant (n x y : ℕ) (hn : 2 ≤ n) (hx0 : 0 < x) (hx1 : x < 2 ^ n - 1) (h : bitword_is_rotation n x y) : bitword_is_rotation n y x := by
  obtain ⟨r, hr, hry⟩ := h
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · exact ⟨0, by omega, by simpa using hry.symm⟩
  · refine ⟨n - r, by omega, ?_⟩
    rw [← hry, ← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hr)]
    exact bitword_rotate_iterate_self n x hn hx0 hx1
