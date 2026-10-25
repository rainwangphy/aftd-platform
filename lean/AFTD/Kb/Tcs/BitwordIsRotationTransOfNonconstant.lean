import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsRotation
import AFTD.Kb.Tcs.BitwordRotateIterateSelf
import AFTD.Kb.Tcs.BitwordRotate

/-!
# bitword_is_rotation_trans_of_nonconstant

Topic: combinatorics   Node: 34f461424a14

Provenance: helper lemma. Rotation bookkeeping for OP-392, arXiv:2610.24758, Conjecture 1.

For length at least two, cyclic-rotation equivalence is transitive when the initial word is a nonconstant n-bit word.
-/

theorem bitword_is_rotation_trans_of_nonconstant (n x y z : ℕ) (hn : 2 ≤ n) (hx0 : 0 < x) (hx1 : x < 2 ^ n - 1) (hxy : bitword_is_rotation n x y) (hyz : bitword_is_rotation n y z) : bitword_is_rotation n x z := by
  obtain ⟨r, hr, hry⟩ := hxy
  obtain ⟨s, hs, hsz⟩ := hyz
  refine ⟨(r + s) % n, Nat.mod_lt _ (by omega), ?_⟩
  have hper : Function.IsPeriodicPt (bitword_rotate n) n x :=
    bitword_rotate_iterate_self n x hn hx0 hx1
  have hstep : (bitword_rotate n)^[r + s] x = z := by
    rw [Nat.add_comm, Function.iterate_add_apply, hry, hsz]
  rw [hper.iterate_mod_apply (r + s), hstep]
