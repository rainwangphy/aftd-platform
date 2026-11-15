import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.IsExtremalPerm
import AFTD.Kb.NumberTheory.GoodSlopesMemIff
import AFTD.Kb.NumberTheory.ZeroMemGoodSlopes
import AFTD.Kb.NumberTheory.GoodSlopesUnitCoverMod105
import AFTD.Kb.NumberTheory.GoodSlopesTwoRowFiberRigidity

/-!
# good_slopes_gap_mod_105

Topic: elementary_number_theory   Node: 413c2276b6bd

Provenance: original. Related work: arXiv:2611.04551, Question 10.2 and Table 3; the modulus-105 case is left open there.

Every non-extremal permutation f of ℤ/105ℤ satisfies |D_{105}(f)| ≤ 40: (good_slopes 105 f).card ≤ 40.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

private def gs105_c3 : ZMod 105 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 105) (ZMod 3)
private def gs105_c35 : ZMod 105 →+* ZMod 35 := ZMod.castHom (by decide : 35 ∣ 105) (ZMod 35)
private def gs105_crt (a : ZMod 3) (b : ZMod 35) : ZMod 105 := 70 * a.val + 36 * b.val
private theorem gs105_crt3 : ∀ a : ZMod 3, ∀ b : ZMod 35, gs105_c3 (gs105_crt a b) = a := by decide +revert
private theorem gs105_crt35 : ∀ a : ZMod 3, ∀ b : ZMod 35, gs105_c35 (gs105_crt a b) = b := by decide +revert
private theorem gs105_crt_self : ∀ x : ZMod 105, gs105_crt (gs105_c3 x) (gs105_c35 x) = x := by decide +revert
private def gs105_split (x : ZMod 105) : ZMod 3 × ZMod 35 := (gs105_c3 x,gs105_c35 x)
private theorem gs105_split_crt (a : ZMod 3) (b : ZMod 35) : gs105_split (gs105_crt a b) = (a,b) := by simp [gs105_split, gs105_crt3, gs105_crt35]
private theorem gs105_split_bij : Function.Bijective gs105_split := by
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hc := congrArg (fun p : ZMod 3 × ZMod 35 => gs105_crt p.1 p.2) h
    simpa only [gs105_split, gs105_crt_self] using hc
  · intro p
    refine ⟨gs105_crt p.1 p.2, ?_⟩
    exact gs105_split_crt _ _

private theorem gs105_unit3 : ∀ a : ZMod 3, IsUnit a ↔ a = 1 ∨ a = 2 := by decide +revert

private theorem gs105_bij_pair_iff (f : ZMod 105 → ZMod 105) (m : ZMod 105) :
    Function.Bijective (fun x => f x + m*x) ↔
    Function.Bijective (fun x => (gs105_c3 (f x) + gs105_c3 m * gs105_c3 x, gs105_c35 (f x) + gs105_c35 m * gs105_c35 x)) := by
  have h := gs105_split_bij.of_comp_iff' (fun x => f x + m*x)
  simpa only [Function.comp_def, gs105_split, map_add, map_mul] using h.symm

open Finset

/-- For the smallest unsettled modulus n = 105, every non-extremal permutation has at most 40 good slopes. -/
theorem good_slopes_gap_mod_105 (f : Equiv.Perm (ZMod 105)) (hf : ¬ is_extremal_perm 105 f) : (good_slopes 105 f).card ≤ 40 := by
  classical
  by_contra hnot
  have hlarge : 40 < (good_slopes 105 f).card := by omega
  obtain ⟨c, hc, hcover⟩ := good_slopes_unit_cover_mod105 f
  let normalized105 : ZMod 105 → ZMod 105 := fun x => f x - c*x
  let A : Finset (ZMod 105) := (good_slopes 105 f).image (fun m => m+c)
  have hA (u : ZMod 105) : u ∈ A ↔ Function.Bijective (fun x => normalized105 x + u*x) := by
    constructor
    · intro hu
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hu
      have hm' := (mem_filter.mp hm).2
      have he : (fun x : ZMod 105 => normalized105 x + (m+c)*x) = (fun x => f x + m*x) := by
        funext x
        dsimp [normalized105]
        ring
      rw [he]
      exact hm'
    · intro hu
      apply mem_image.mpr
      refine ⟨u-c, ?_, by ring⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      have he : (fun x : ZMod 105 => f x + (u-c)*x) = (fun x => normalized105 x + u*x) := by
        funext x
        dsimp [normalized105]
        ring
      rw [he]
      exact hu
  have hAunit : ∀ u ∈ A, IsUnit u := by
    intro u hu
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hu
    exact hcover m hm
  have hAcard : A.card = (good_slopes 105 f).card :=
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
  let pairs105 : Finset (ZMod 3 × ZMod 35) := A.image gs105_split
  have hFcard : pairs105.card = A.card := Finset.card_image_of_injective _ gs105_split_bij.1
  have hFmem (a : ZMod 3) (b : ZMod 35) : (a,b) ∈ pairs105 ↔ gs105_crt a b ∈ A := by
    constructor
    · intro h
      obtain ⟨u, hu, he⟩ := mem_image.mp h
      have heq : u = gs105_crt a b := gs105_split_bij.1 (he.trans (gs105_split_crt a b).symm)
      simpa [heq] using hu
    · intro h
      exact mem_image.mpr ⟨gs105_crt a b, h, gs105_split_crt a b⟩
  have hF (a : ZMod 3) (b : ZMod 35) : (a,b) ∈ pairs105 ↔
      IsUnit a ∧ IsUnit b ∧ Function.Injective (fun x : ZMod 105 =>
        (gs105_c3 (normalized105 x) + a*gs105_c3 x, gs105_c35 (normalized105 x) + b*gs105_c35 x)) := by
    constructor
    · intro h
      have hu : IsUnit (gs105_crt a b) := hAunit _ ((hFmem a b).1 h)
      have huv : IsUnit a ∧ IsUnit b := by
        constructor
        · simpa only [gs105_crt3] using gs105_c3.isUnit_map hu
        · simpa only [gs105_crt35] using gs105_c35.isUnit_map hu
      have hbij := (gs105_bij_pair_iff normalized105 (gs105_crt a b)).1 ((hA _).1 ((hFmem a b).1 h))
      rw [gs105_crt3, gs105_crt35] at hbij
      exact ⟨huv.1, huv.2, hbij.1⟩
    · rintro ⟨ha, hb, hi⟩
      apply (hFmem a b).2
      apply (hA _).2
      apply (gs105_bij_pair_iff normalized105 (gs105_crt a b)).2
      rw [gs105_crt3, gs105_crt35]
      exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hi, by simp⟩
  let R : ZMod 3 → Finset (ZMod 35) := fun a => univ.filter fun b =>
      IsUnit b ∧ Function.Injective (fun x : ZMod 105 => (gs105_c3 (normalized105 x) + a*gs105_c3 x, gs105_c35 (normalized105 x) + b*gs105_c35 x))
  have hdecomp : pairs105 = (({1} : Finset (ZMod 3)) ×ˢ R 1) ∪ (({2} : Finset (ZMod 3)) ×ˢ R 2) := by
    ext ⟨a,b⟩
    rw [hF a b]
    simp only [mem_union, mem_product, mem_singleton, R, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨ha, hb, hi⟩
      rcases (gs105_unit3 a).1 ha with ha | ha
      · left
        subst a
        exact ⟨rfl, hb, hi⟩
      · right
        subst a
        exact ⟨rfl, hb, hi⟩
    · rintro (⟨ha, hb, hi⟩ | ⟨ha, hb, hi⟩)
      · subst a
        exact ⟨(gs105_unit3 1).2 (Or.inl rfl), hb, hi⟩
      · subst a
        exact ⟨(gs105_unit3 2).2 (Or.inr rfl), hb, hi⟩
  have hdisj : Disjoint (({1} : Finset (ZMod 3)) ×ˢ R 1) (({2} : Finset (ZMod 3)) ×ˢ R 2) := by
    apply Finset.disjoint_left.mpr
    intro ⟨a,b⟩ h1 h2
    simp only [mem_product, mem_singleton] at h1 h2
    have h12 : (1 : ZMod 3) ≠ 2 := by decide
    exact h12 (h1.1.symm.trans h2.1)
  have hcount : pairs105.card = (R 1).card + (R 2).card := by
    rw [hdecomp, card_union_of_disjoint hdisj, card_product, card_product]
    simp
  have hrows : 40 < (R 1).card + (R 2).card := by
    rw [← hcount, hFcard, hAcard]
    exact hlarge
  have hstrong := good_slopes_two_row_fiber_rigidity gs105_c3 (fun x => gs105_c3 (normalized105 x)) gs105_c35 (fun x => gs105_c35 (normalized105 x)) 1 2
      (by simp) (by change Function.Injective gs105_split; exact gs105_split_bij.1) (by simpa [R] using hrows)
  have hAll : ∀ u : ZMod 105, IsUnit u → u ∈ A := by
    intro u hu
    have hu' : IsUnit (gs105_c3 u) ∧ IsUnit (gs105_c35 u) := ⟨gs105_c3.isUnit_map hu, gs105_c35.isUnit_map hu⟩
    have ha := (gs105_unit3 _).1 hu'.1
    apply (hA u).2
    apply (gs105_bij_pair_iff normalized105 u).2
    apply (Fintype.bijective_iff_injective_and_card _).2
    refine ⟨?_, by simp⟩
    rcases ha with ha | ha
    · rw [ha]
      exact hstrong.1 _ hu'.2
    · rw [ha]
      exact hstrong.2 _ hu'.2
  let U : Finset (ZMod 105) := univ.filter fun u => IsUnit u
  have hAU : A = U := by
    ext u
    simp only [U, mem_filter, mem_univ, true_and]
    exact ⟨hAunit u, hAll u⟩
  have hUcard : U.card = 48 := by decide
  apply hf
  unfold is_extremal_perm
  have ht : Nat.totient 105 = 48 := by decide
  rw [hAU, hUcard] at hAcard
  omega
