import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesFiber15Form
import AFTD.Kb.NumberTheory.GoodSlopesFiber15AnchoredRigidity

/-!
# good_slopes_fiber15_neighbors_force

Topic: elementary_number_theory   Node: 7f5c53a07c0d

Provenance: helper lemma. Direction-neighbor rigidity for OP-1027, tested in experiment 21991, using the normalized argument good_slopes_fiber15_anchored_rigidity.

On any set of points over the residues modulo 15, if y+4x is surjective and the forms y+7x, y+11x and y+13x are injective, then y+x is injective.
-/

private theorem fiber15_unit_test : ∀ d : ZMod 15, 6*d ≠ 0 → 10*d ≠ 0 → IsUnit d := by decide

theorem good_slopes_fiber15_neighbors_force (S : Set (ZMod 15 × ZMod 15)) (h4 : ∀ t, ∃ p ∈ S, good_slopes_fiber15_form 4 p = t) (h7 : Set.InjOn (good_slopes_fiber15_form 7) S) (h11 : Set.InjOn (good_slopes_fiber15_form 11) S) (h13 : Set.InjOn (good_slopes_fiber15_form 13) S) : Set.InjOn (good_slopes_fiber15_form 1) S := by
  intro p hp q hq heq
  by_contra hne
  let d : ZMod 15 := q.1 - p.1
  have hdy : q.2 - p.2 = -d := by
    dsimp [d, good_slopes_fiber15_form] at *
    linear_combination -heq
  have hdiff (a : ZMod 15) : good_slopes_fiber15_form a q - good_slopes_fiber15_form a p = (a-1)*d := by
    dsimp [good_slopes_fiber15_form, d]
    dsimp [d] at hdy
    linear_combination hdy
  have hd6 : 6*d ≠ 0 := by
    intro hz
    apply hne
    apply h7 hp hq
    have hh := hdiff 7
    have hh' : good_slopes_fiber15_form 7 q - good_slopes_fiber15_form 7 p = 0 := by
      rw [hh]
      convert hz using 1 <;> ring
    exact (sub_eq_zero.mp hh').symm
  have hd10 : 10*d ≠ 0 := by
    intro hz
    apply hne
    apply h11 hp hq
    have hh := hdiff 11
    have hh' : good_slopes_fiber15_form 11 q - good_slopes_fiber15_form 11 p = 0 := by
      rw [hh]
      convert hz using 1 <;> ring
    exact (sub_eq_zero.mp hh').symm
  obtain ⟨u, hu⟩ := fiber15_unit_test d hd6 hd10
  let e : (ZMod 15 × ZMod 15) ≃ (ZMod 15 × ZMod 15) :=
    (Equiv.subRight p).trans ((u⁻¹).mulLeft.prodCongr (u⁻¹).mulLeft)
  let T : Set (ZMod 15 × ZMod 15) := e '' S
  have heform (a : ZMod 15) (r : ZMod 15 × ZMod 15) :
      good_slopes_fiber15_form a (e r) = (↑(u⁻¹) : ZMod 15) * (good_slopes_fiber15_form a r - good_slopes_fiber15_form a p) := by
    simp [e, good_slopes_fiber15_form, Units.mulLeft_apply]
    ring
  have hT0 : (0,0) ∈ T := by
    refine ⟨p,hp,?_⟩
    ext <;> simp [e]
  have hT1 : (1,14) ∈ T := by
    refine ⟨q,hq,?_⟩
    apply Prod.ext
    · change (↑(u⁻¹) : ZMod 15) * (q.1-p.1) = 1
      change (↑(u⁻¹) : ZMod 15) * d = 1
      rw [← hu]
      exact Units.inv_mul u
    · change (↑(u⁻¹) : ZMod 15) * (q.2-p.2) = 14
      rw [hdy, ← hu]
      have h14 : (14 : ZMod 15) = -1 := by decide
      rw [h14, mul_neg, Units.inv_mul]
  have hT4 : ∀ t, ∃ r ∈ T, good_slopes_fiber15_form 4 r = t := by
    intro t
    obtain ⟨r,hr,hr4⟩ := h4 ((u : ZMod 15)*t + good_slopes_fiber15_form 4 p)
    refine ⟨e r, ⟨r,hr,rfl⟩, ?_⟩
    rw [heform,hr4]
    simp [mul_add, ← mul_assoc]
  have hTinj (a : ZMod 15) (ha : Set.InjOn (good_slopes_fiber15_form a) S) :
      Set.InjOn (good_slopes_fiber15_form a) T := by
    intro r hr s hs hrs
    obtain ⟨r,hr,rfl⟩ := hr
    obtain ⟨s,hs,rfl⟩ := hs
    apply congrArg e
    apply ha hr hs
    rw [heform,heform] at hrs
    have hh := congrArg (fun z : ZMod 15 => (u : ZMod 15)*z) hrs
    have hh' : good_slopes_fiber15_form a r - good_slopes_fiber15_form a p =
        good_slopes_fiber15_form a s - good_slopes_fiber15_form a p := by
      have huinv : (u : ZMod 15) * (↑(u⁻¹) : ZMod 15) = 1 := Units.mul_inv u
      simpa only [← mul_assoc, huinv, one_mul] using hh
    linear_combination hh'
  exact good_slopes_fiber15_anchored_rigidity T hT0 hT1 hT4 (hTinj 7 h7) (hTinj 11 h11) (hTinj 13 h13)
