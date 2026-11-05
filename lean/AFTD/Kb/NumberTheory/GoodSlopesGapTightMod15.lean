import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.IsExtremalPerm

/-!
# good_slopes_gap_tight_mod_15

Topic: elementary_number_theory   Node: e0743c30a523

Provenance: formalization of a published result. Source: arXiv:2611.04551 Proposition 9.6

There exists a non-extremal permutation f of ℤ/15ℤ with exactly 6 good slopes, demonstrating that the gap bound φ(15)(q - 2)/(q - 1) = 6 is attained for n = 15.
-/

def good_slopes_gap_tight_mod_15_f : Equiv.Perm (ZMod 15) where
  toFun x := if x.val % 3 == 0 then 2 * x else x
  invFun y := if y.val % 3 == 0 then 8 * y else y
  left_inv := by decide
  right_inv := by decide

/-- The gap bound φ(15)(5 - 2)/(5 - 1) = 6 for good slopes on ℤ/15ℤ is sharp: there exists a non-extremal permutation of ℤ/15ℤ with exactly 6 good slopes. -/
theorem good_slopes_gap_tight_mod_15 : ∃ f : Equiv.Perm (ZMod 15), ¬ is_extremal_perm 15 f ∧ (good_slopes 15 f).card = 6 := by
  have hc : (good_slopes 15 good_slopes_gap_tight_mod_15_f).card = 6 := by decide
  refine ⟨good_slopes_gap_tight_mod_15_f, ?_, hc⟩
  intro h
  change (good_slopes 15 good_slopes_gap_tight_mod_15_f).card = Nat.totient 15 at h
  rw [hc] at h
  revert h
  decide
