import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.GoodSlopesMissingPrime105

/-!
# good_slopes_unit_cover_mod105

Topic: elementary_number_theory   Node: beb49b9f976f

Provenance: helper lemma. The modulus 105 instance of arXiv:2611.01465, Theorem 3.1(i), used for OP-1027.

For every permutation modulo 105, a unit c exists such that adding c to each good slope yields a unit modulo 105.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
private def c3 : ZMod 105 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 105) (ZMod 3)
private def c5 : ZMod 105 →+* ZMod 5 := ZMod.castHom (by decide : 5 ∣ 105) (ZMod 5)
private def c7 : ZMod 105 →+* ZMod 7 := ZMod.castHom (by decide : 7 ∣ 105) (ZMod 7)
private def crt (a : ZMod 3) (b : ZMod 5) (c : ZMod 7) : ZMod 105 :=
  70 * a.val + 21 * b.val + 15 * c.val
private theorem crt3 : ∀ a : ZMod 3, ∀ b : ZMod 5, ∀ c : ZMod 7, c3 (crt a b c) = a := by decide +revert
private theorem crt5 : ∀ a : ZMod 3, ∀ b : ZMod 5, ∀ c : ZMod 7, c5 (crt a b c) = b := by decide +revert
private theorem crt7 : ∀ a : ZMod 3, ∀ b : ZMod 5, ∀ c : ZMod 7, c7 (crt a b c) = c := by decide +revert
private theorem unit105 : ∀ x : ZMod 105, Nat.Coprime x.val 105 ↔ c3 x ≠ 0 ∧ c5 x ≠ 0 ∧ c7 x ≠ 0 := by decide +revert

theorem good_slopes_unit_cover_mod105 (f : Equiv.Perm (ZMod 105)) : ∃ c : ZMod 105, IsUnit c ∧ ∀ m ∈ good_slopes 105 f, IsUnit (m+c) := by
  obtain ⟨a, ha⟩ := good_slopes_missing_prime105 3 (Or.inl rfl) (by decide) f
  obtain ⟨b, hb⟩ := good_slopes_missing_prime105 5 (Or.inr (Or.inl rfl)) (by decide) f
  obtain ⟨d, hd⟩ := good_slopes_missing_prime105 7 (Or.inr (Or.inr rfl)) (by decide) f
  let c := crt (-a) (-b) (-d)
  have hc3 : c3 c = -a := crt3 _ _ _
  have hc5 : c5 c = -b := crt5 _ _ _
  have hc7 : c7 c = -d := crt7 _ _ _
  have hzero : (0 : ZMod 105) ∈ good_slopes 105 f := by
    unfold good_slopes
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_mul, add_zero]
    exact f.bijective
  have hunit (z : ZMod 105) : IsUnit z ↔ Nat.Coprime z.val 105 := by
    simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime z.val 105)
  have hshift (m : ZMod 105) (hm : m ∈ good_slopes 105 f) : IsUnit (m+c) := by
    apply (hunit _).2
    apply (unit105 _).2
    have h3 : c3 (m+c) ≠ 0 := by
      intro h; apply ha m hm
      have : c3 m - a = 0 := by simpa only [map_add, hc3, sub_eq_add_neg] using h
      exact sub_eq_zero.mp this
    have h5 : c5 (m+c) ≠ 0 := by
      intro h; apply hb m hm
      have : c5 m - b = 0 := by simpa only [map_add, hc5, sub_eq_add_neg] using h
      exact sub_eq_zero.mp this
    have h7 : c7 (m+c) ≠ 0 := by
      intro h; apply hd m hm
      have : c7 m - d = 0 := by simpa only [map_add, hc7, sub_eq_add_neg] using h
      exact sub_eq_zero.mp this
    exact ⟨h3, h5, h7⟩
  refine ⟨c, ?_, hshift⟩
  simpa using hshift 0 hzero
