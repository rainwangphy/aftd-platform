import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.GoodSlopesMemIff

/-!
# zero_mem_good_slopes

Topic: elementary_number_theory   Node: c934f0946403

Provenance: helper lemma. step towards good_slopes_gap_mod_105

Zero is always a good slope of every permutation of ℤ/nℤ, since x ↦ f(x) + 0·x = f(x) is a permutation; in particular D_n(f) is nonempty: (good_slopes n f).Nonempty.
-/

/-- Non-vacuity witness for good_slopes: 0 is always a good slope. -/
theorem zero_mem_good_slopes (n : ℕ) [NeZero n] (f : Equiv.Perm (ZMod n)) : (0 : ZMod n) ∈ good_slopes n f := by
  rw [good_slopes_mem_iff]
  simp only [zero_mul, add_zero]
  exact f.bijective
