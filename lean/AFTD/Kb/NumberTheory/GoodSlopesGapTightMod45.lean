import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.IsExtremalPerm

/-!
# good_slopes_gap_tight_mod_45

Topic: elementary_number_theory   Node: 28c1ca73d677

Provenance: formalization of a published result. Source: arXiv:2611.04551 Section 9, lines 4426-4443

There exists a non-extremal permutation f of ℤ/45ℤ with exactly 18 good slopes, demonstrating that the gap bound φ(45)(q - 2)/(q - 1) = 18 is attained for n = 45.
-/

def good_slopes_gap_tight_mod_45_f : Equiv.Perm (ZMod 45) where
  toFun x := if x.val % 9 == 0 then 2 * x else x
  invFun y := if y.val % 9 == 0 then 23 * y else y
  left_inv x := by
    revert x; decide
  right_inv y := by
    revert y; decide

/-- The gap bound φ(45)(5 - 2)/(5 - 1) = 18 for good slopes on ℤ/45ℤ is sharp: there exists a non-extremal permutation of ℤ/45ℤ with exactly 18 good slopes. -/
theorem good_slopes_gap_tight_mod_45 : ∃ f : Equiv.Perm (ZMod 45), ¬ is_extremal_perm 45 f ∧ (good_slopes 45 f).card = 18 := by
  have hc : (good_slopes 45 good_slopes_gap_tight_mod_45_f).card = 18 := by decide
  refine ⟨good_slopes_gap_tight_mod_45_f, ?_, hc⟩
  intro h
  change (good_slopes 45 good_slopes_gap_tight_mod_45_f).card = Nat.totient 45 at h
  rw [hc] at h
  revert h
  decide
