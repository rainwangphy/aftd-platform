import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber35CrtRectangleExclusion

/-!
# good_slopes_gap105_from_rectangle

Topic: elementary_number_theory   Node: a0583e6f4010

Provenance: helper lemma. Final logical step of the 105-point reduction for OP-1027.

A permutation modulo 105 has at most 40 good slopes if any hypothetical excess produces a 35-point fiber with the stated rectangle and width properties.
-/

theorem good_slopes_gap105_from_rectangle (f : Equiv.Perm (ZMod 105))
  (hextract : 40 < (good_slopes 105 f).card → ∃ (S : Finset (ZMod 35 × ZMod 35)) (a₁ a₂ : ZMod 5) (t : ZMod 7), S.card = 35 ∧ (∀ x : ZMod 35, (S.filter fun p => p.1 = x).card ≤ 3) ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₁ ≠ a₂ ∧ t ≠ 0 ∧ (∀ b : ZMod 35, IsUnit b → (((ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) b ≠ a₁) ∧ (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) b ≠ a₂)) ∨ ((ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ t) ∧ (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ 2*t) ∧ (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ 4*t))) → b ∈ good_slopes_point_directions 35 S) ∧ (∃ b : ZMod 35, IsUnit b ∧ b ∉ good_slopes_point_directions 35 S)) :
  (good_slopes 105 f).card ≤ 40 := by
  by_contra hh
  have hlarge : 40 < (good_slopes 105 f).card := by omega
  obtain ⟨S,a₁,a₂,t,hcard,hwidth,ha₁,ha₂,ha,ht,hgood,hbad⟩ := hextract hlarge
  exact good_slopes_fiber35_crt_rectangle_exclusion S hcard hwidth a₁ a₂ t ha₁ ha₂ ha ht hgood hbad
