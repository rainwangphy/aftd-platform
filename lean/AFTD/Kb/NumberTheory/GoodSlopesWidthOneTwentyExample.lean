import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_width_one_twenty_example

Topic: elementary_number_theory   Node: e612a2b2b970

Provenance: helper lemma. Explicit linear witness y = 20x over ZMod 35, following experiment 22049 for OP-1027.

There is a 35-point set with at most one point over each first coordinate, a bad unit direction and at least 20 good unit directions. Thus a bound of 16 cannot follow from the first-coordinate width bound alone.
-/

theorem good_slopes_width_one_twenty_example :
    ∃ S : Finset (ZMod 35 × ZMod 35), S.card = 35 ∧
      (∀ x : ZMod 35, (S.filter fun p => p.1 = x).card ≤ 1) ∧
      (1 : ZMod 35) ∉ good_slopes_point_directions 35 S ∧
      20 ≤ (good_slopes_point_directions 35 S).card := by
  classical
  let S : Finset (ZMod 35 × ZMod 35) := Finset.univ.image fun x : ZMod 35 => (x,20*x)
  let A : Finset (ZMod 35) := {2,3,4,6,9,11,12,13,16,17,18,19,23,24,26,27,31,32,33,34}
  have hA : A.card = 20 := by decide
  have hAunit : ∀ a ∈ A, IsUnit a ∧ IsUnit (20+a) := by decide
  have hp : ∀ p ∈ S, p.2 = 20 * p.1 := by
    intro p hp
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hp
    rfl
  have hcard : S.card = 35 := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x _ y _ h
      exact congrArg Prod.fst h
  have hwidth : ∀ x : ZMod 35, (S.filter fun p => p.1 = x).card ≤ 1 := by
    intro x
    apply Finset.card_le_one.mpr
    intro p hpm q hqm
    have hps := (Finset.mem_filter.mp hpm).1
    have hqs := (Finset.mem_filter.mp hqm).1
    have hfst : p.1 = q.1 := (Finset.mem_filter.mp hpm).2.trans (Finset.mem_filter.mp hqm).2.symm
    apply Prod.ext hfst
    rw [hp p hps, hp q hqs, hfst]
  have hbad : (1 : ZMod 35) ∉ good_slopes_point_directions 35 S := by
    intro h
    have hi : Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + 1 * p.1) S := by
      simpa [good_slopes_point_directions] using h
    have h0 : ((0,0) : ZMod 35 × ZMod 35) ∈ S := by
      apply Finset.mem_image.mpr
      exact ⟨0,Finset.mem_univ _,by norm_num⟩
    have h5 : ((5,30) : ZMod 35 × ZMod 35) ∈ S := by
      apply Finset.mem_image.mpr
      exact ⟨5,Finset.mem_univ _,by decide⟩
    have heq := hi h0 h5 (by decide)
    have : (0 : ZMod 35) = 5 := congrArg Prod.fst heq
    exact (by decide : (0 : ZMod 35) ≠ 5) this
  have hsub : A ⊆ good_slopes_point_directions 35 S := by
    intro a ha
    have hu := hAunit a ha
    simp only [good_slopes_point_directions, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hu.1, ?_⟩
    intro p hps q hqs heq
    have hmul : (20+a)*p.1 = (20+a)*q.1 := by
      simpa [hp p hps, hp q hqs, add_mul] using heq
    have hfst : p.1 = q.1 := hu.2.mul_right_injective hmul
    apply Prod.ext hfst
    rw [hp p hps, hp q hqs, hfst]
  exact ⟨S,hcard,hwidth,hbad,by calc
    20 = A.card := hA.symm
    _ ≤ (good_slopes_point_directions 35 S).card := Finset.card_le_card hsub⟩
