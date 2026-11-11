import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesFiber35Rect2
import AFTD.Kb.NumberTheory.GoodSlopesFiber35Rect3
import AFTD.Kb.NumberTheory.GoodSlopesFiber35Width3Rect4
import AFTD.Kb.Tcs.F

/-!
# good_slopes_fiber35_unanchored_rect

Topic: elementary_number_theory   Node: e5384b42183c

Provenance: helper lemma. Unanchored form of the three checked normalized rectangle obstructions in the OP-1027 reduction.

For any 35-point set of x-width at most three, injectivity in the 18 directions outside any of the three normalized two-by-three rectangles forces direction 1 to be injective too.
-/

private theorem aftd_rect35_normalize_width
    (S : Finset (ZMod 35 × ZMod 35)) (p q : ZMod 35 × ZMod 35)
    (hp : p ∈ S) (hq : q ∈ S) (a u : (ZMod 35)ˣ)
    (hdelta : q.1 - p.1 = (u : ZMod 35))
    (hcollision : q.2 + (a : ZMod 35) * q.1 = p.2 + (a : ZMod 35) * p.1)
    (hwidth : ∀ x : ZMod 35, (S.filter fun r => r.1 = x).card ≤ 3) :
    ∃ T : Finset (ZMod 35 × ZMod 35), T.card = S.card ∧ (0,0) ∈ T ∧ (1,34) ∈ T ∧
      (∀ x : ZMod 35, (T.filter fun r => r.1 = x).card ≤ 3) ∧
      ∀ b : ZMod 35,
        Set.InjOn (fun r : ZMod 35 × ZMod 35 => r.2 + ((a : ZMod 35)*b)*r.1) S →
        Set.InjOn (fun r : ZMod 35 × ZMod 35 => r.2 + b*r.1) T := by
  classical
  let v : (ZMod 35)ˣ := a*u
  let F : ZMod 35 × ZMod 35 → ZMod 35 × ZMod 35 := fun r =>
    (((u⁻¹ : (ZMod 35)ˣ) : ZMod 35) * (r.1-p.1),
     ((v⁻¹ : (ZMod 35)ˣ) : ZMod 35) * (r.2-p.2))
  have hF : Function.Injective F := by
    intro r s heq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    change ((u⁻¹ : (ZMod 35)ˣ) : ZMod 35) * (r.1-p.1) =
      ((u⁻¹ : (ZMod 35)ˣ) : ZMod 35) * (s.1-p.1) at hx
    change ((v⁻¹ : (ZMod 35)ˣ) : ZMod 35) * (r.2-p.2) =
      ((v⁻¹ : (ZMod 35)ˣ) : ZMod 35) * (s.2-p.2) at hy
    have hx' := (u⁻¹).isUnit.mul_right_injective hx
    have hy' := (v⁻¹).isUnit.mul_right_injective hy
    apply Prod.ext
    · linear_combination hx'
    · linear_combination hy'
  have hscale (r : ZMod 35 × ZMod 35) (b : ZMod 35) :
      (v : ZMod 35) * ((F r).2 + b*(F r).1) =
      (r.2-p.2) + ((a : ZMod 35)*b)*(r.1-p.1) := by
    have ha : (a : ZMod 35)*((a⁻¹ : (ZMod 35)ˣ) : ZMod 35) = 1 := by simp
    have hu : (u : ZMod 35)*((u⁻¹ : (ZMod 35)ˣ) : ZMod 35) = 1 := by simp
    have hv : (v : ZMod 35)*((v⁻¹ : (ZMod 35)ˣ) : ZMod 35) = 1 := by simp
    change (v : ZMod 35) * (((v⁻¹ : (ZMod 35)ˣ) : ZMod 35)*(r.2-p.2) +
      b*(((u⁻¹ : (ZMod 35)ˣ) : ZMod 35)*(r.1-p.1))) = _
    have hva : (v : ZMod 35)*((u⁻¹ : (ZMod 35)ˣ) : ZMod 35) = (a : ZMod 35) := by
      dsimp [v]
      simp [mul_assoc]
    calc
      _ = ((v : ZMod 35)*((v⁻¹ : (ZMod 35)ˣ) : ZMod 35))*(r.2-p.2) +
          ((v : ZMod 35)*((u⁻¹ : (ZMod 35)ˣ) : ZMod 35))*b*(r.1-p.1) := by ring
      _ = _ := by rw [hv,hva]; ring
  let T := S.image F
  have hcard : T.card = S.card := Finset.card_image_of_injective S hF
  have hp0 : (0,0) ∈ T := by
    apply Finset.mem_image.mpr
    refine ⟨p,hp,?_⟩
    simp [F]
  have hq1 : (1,34) ∈ T := by
    apply Finset.mem_image.mpr
    refine ⟨q,hq,?_⟩
    apply Prod.ext
    · dsimp [F]
      rw [hdelta]
      simp
    · dsimp [F]
      have hy : q.2-p.2 = -(a : ZMod 35)*(u : ZMod 35) := by
        rw [← hdelta]
        linear_combination hcollision
      have hy' : q.2-p.2 = -(v : ZMod 35) := by simpa [v] using hy
      have hv : ((v⁻¹ : (ZMod 35)ˣ) : ZMod 35) * (v : ZMod 35) = 1 := by simp
      rw [hy',mul_neg,hv]
      decide
  have hcoord (r : ZMod 35 × ZMod 35) (x : ZMod 35) : (F r).1 = x ↔ r.1 = p.1 + (u : ZMod 35)*x := by
    constructor
    · intro heq
      have hx := congrArg (fun z : ZMod 35 => (u : ZMod 35)*z) heq
      change (u : ZMod 35)*(((u⁻¹ : (ZMod 35)ˣ) : ZMod 35)*(r.1-p.1)) = (u : ZMod 35)*x at hx
      have hu : (u : ZMod 35)*((u⁻¹ : (ZMod 35)ˣ) : ZMod 35) = 1 := by simp
      rw [← mul_assoc,hu,one_mul] at hx
      linear_combination hx
    · intro heq
      change ((u⁻¹ : (ZMod 35)ˣ) : ZMod 35)*(r.1-p.1) = x
      rw [heq]
      have hx : p.1 + (u : ZMod 35)*x - p.1 = (u : ZMod 35)*x := by ring
      rw [hx,← mul_assoc]
      simp
  have hwidthT : ∀ x : ZMod 35, (T.filter fun r => r.1 = x).card ≤ 3 := by
    intro x
    have heq : T.filter (fun r => r.1 = x) = (S.filter fun r => r.1 = p.1+(u : ZMod 35)*x).image F := by
      ext r
      simp only [T,Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨⟨q,hq,rfl⟩,hx⟩
        exact ⟨q,⟨hq,(hcoord q x).mp hx⟩,rfl⟩
      · rintro ⟨q,⟨hq,hx⟩,rfl⟩
        exact ⟨⟨q,hq,rfl⟩,(hcoord q x).mpr hx⟩
    rw [heq,Finset.card_image_of_injective _ hF]
    exact hwidth _
  refine ⟨T,hcard,hp0,hq1,hwidthT,?_⟩
  intro b hb r hr s hs heq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hs
  have hs' := congrArg (fun z : ZMod 35 => (v : ZMod 35)*z) heq
  rw [hscale,hscale] at hs'
  have hform : x.2 + ((a : ZMod 35)*b)*x.1 = y.2 + ((a : ZMod 35)*b)*y.1 := by
    linear_combination hs'
  exact congrArg F (hb hx hy hform)



private def aftd_rect35_Units : Finset (ZMod 35) :=
  {1,2,3,4,6,8,9,11,12,13,16,17,18,19,22,23,24,26,27,29,31,32,33,34}
private def aftd_rect35_Nonunits : Finset (ZMod 35) := {5,7,10,14,15,20,21,25,28,30}
private def aftd_rect35_Neighbors : Finset (ZMod 35) := {6,8,11,16,22,26,29,31}

private theorem aftd_rect35__unit_table : ∀ a : ZMod 35, Nat.Coprime a.val 35 ↔ a ∈ aftd_rect35_Units := by decide

private theorem aftd_rect35__nonunit_table : ∀ a : ZMod 35, a ∈ aftd_rect35_Units ∨ a = 0 ∨ a ∈ aftd_rect35_Nonunits := by decide

private theorem aftd_rect35__nonunit_collisions : ∀ u ∈ aftd_rect35_Nonunits,
    4 ≤ (aftd_rect35_Units.filter fun b => (b-1)*u=0).card := by decide

private theorem aftd_rect35__neighbor_props : aftd_rect35_Neighbors.card = 8 ∧
    ∀ b ∈ aftd_rect35_Neighbors, b ∈ aftd_rect35_Units ∧ b ≠ 1 := by decide

private theorem aftd_rect35__units_card : aftd_rect35_Units.card = 24 := by decide


private def aftd_rect35_RectGood (r : Fin 3) : Finset (ZMod 35) :=
  if r = 0 then {3,4,6,8,9,12,13,17,18,19,23,24,26,27,29,31,33,34}
  else if r = 1 then {2,3,4,6,9,12,13,17,19,22,24,26,27,29,31,32,33,34}
  else {2,3,6,8,12,13,17,18,19,22,23,24,26,27,31,32,33,34}

private theorem aftd_rect35__nonunit_rect_hit : ∀ (r : Fin 3) (u : ZMod 35), u ∈ aftd_rect35_Nonunits →
    ∃ b ∈ aftd_rect35_RectGood r, (b-1)*u = 0 := by decide

theorem good_slopes_fiber35_unanchored_rect
    (S : Finset (ZMod 35 × ZMod 35)) (hcard : S.card = 35)
    (hwidth : ∀ x : ZMod 35, (S.filter fun p => p.1 = x).card ≤ 3)
    (r : Fin 3) (hinj : ∀ b ∈ (if r = 0 then ({3,4,6,8,9,12,13,17,18,19,23,24,26,27,29,31,33,34} : Finset (ZMod 35)) else if r = 1 then {2,3,4,6,9,12,13,17,19,22,24,26,27,29,31,32,33,34} else {2,3,6,8,12,13,17,18,19,22,23,24,26,27,31,32,33,34}),
      Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+b*p.1) S)
    (hbad : ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+p.1) S) : False := by
  change ∀ b ∈ aftd_rect35_RectGood r, Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+b*p.1) S at hinj
  classical
  have hunit (x : ZMod 35) : IsUnit x ↔ x ∈ aftd_rect35_Units := by
    calc
      IsUnit x ↔ Nat.Coprime x.val 35 := by
        simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime x.val 35)
      _ ↔ x ∈ aftd_rect35_Units := aftd_rect35__unit_table x
  change ¬ (∀ p ∈ S, ∀ q ∈ S, p.2+p.1 = q.2+q.1 → p=q) at hbad
  push_neg at hbad
  obtain ⟨p,hp,q,hq,hpq,hne⟩ := hbad
  let u := q.1-p.1
  have hu0 : u ≠ 0 := by
    intro hz
    have hx : q.1 = p.1 := sub_eq_zero.mp hz
    have hy : q.2 = p.2 := by rw [hx] at hpq; exact add_right_cancel hpq.symm
    exact hne (Prod.ext hx.symm hy.symm)
  have hu : IsUnit u := by
    by_contra hnu
    have huN : u ∈ aftd_rect35_Nonunits := by
      rcases aftd_rect35__nonunit_table u with h | h | h
      · exact False.elim (hnu ((hunit u).mpr h))
      · exact False.elim (hu0 h)
      · exact h
    obtain ⟨b,hb,hzero⟩ := aftd_rect35__nonunit_rect_hit r u huN
    apply hne
    apply hinj b hb hp hq
    dsimp [u] at hzero
    linear_combination hpq - hzero
  let uu : (ZMod 35)ˣ := hu.unit
  have huv : (uu : ZMod 35) = u := hu.unit_spec
  obtain ⟨T,hTc,hT0,hT1,hTwidth,hTgood⟩ :=
    aftd_rect35_normalize_width S p q hp hq 1 uu (by simpa [huv,u]) (by simpa using hpq.symm) hwidth
  have hinjT : ∀ b ∈ aftd_rect35_RectGood r,
      Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+b*p.1) T := by
    intro b hb
    simpa using hTgood b (by simpa using hinj b hb)
  have hcover : ∀ b ∈ aftd_rect35_RectGood r, ∀ t : ZMod 35, ∃ p ∈ T, p.2+b*p.1=t := by
    intro b hb t
    have himage : (T.image (fun p : ZMod 35 × ZMod 35 => p.2+b*p.1)).card = 35 := by
      rw [Finset.card_image_of_injOn (hinjT b hb),hTc,hcard]
    have hfull : T.image (fun p : ZMod 35 × ZMod 35 => p.2+b*p.1) = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using himage
    have ht : t ∈ T.image (fun p : ZMod 35 × ZMod 35 => p.2+b*p.1) := by rw [hfull]; exact Finset.mem_univ t
    exact Finset.mem_image.mp ht
  fin_cases r
  · apply good_slopes_fiber35_rect2 T hT0 hT1
    · exact hinjT
    · exact hcover
  · apply good_slopes_fiber35_rect3 T hT0 hT1
    · exact hinjT
    · exact hcover
  · apply good_slopes_fiber35_width3_rect4 T hT0 hT1
    · exact hinjT
    · exact hcover
    · exact hTwidth
