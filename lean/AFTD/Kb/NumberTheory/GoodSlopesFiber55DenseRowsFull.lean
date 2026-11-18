import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesPrime11SixGoodLines
import AFTD.Kb.NumberTheory.GoodSlopesFiveLevelsNoVertical

/-!
# good_slopes_fiber55_dense_rows_full

Topic: elementary_number_theory   Node: 3e5b0d38ba02

Provenance: helper lemma. Two-row structural step for the colored 55-point fiber in OP-1027.

For a three-colored 55-point set with same-color injectivity of x and every unit form, if two distinct nonzero mod-five slope rows each contain at least six good unit directions, the first row is entirely good.
-/

noncomputable def good_slopes_fiber55_dense_rows_full_p5 : ZMod 55 →+* ZMod 5 :=
  ZMod.castHom (by decide : (5:ℕ) ∣ 55) (ZMod 5)

noncomputable def good_slopes_fiber55_dense_rows_full_p11 : ZMod 55 →+* ZMod 11 :=
  ZMod.castHom (by decide : (11:ℕ) ∣ 55) (ZMod 11)

noncomputable def good_slopes_fiber55_dense_rows_full_crtp (z : ZMod 55) : ZMod 5 × ZMod 11 :=
  (good_slopes_fiber55_dense_rows_full_p5 z, good_slopes_fiber55_dense_rows_full_p11 z)

noncomputable def good_slopes_fiber55_dense_rows_full_phi (a : ZMod 5) (p : ZMod 55 × ZMod 55) : ZMod 5 :=
  good_slopes_fiber55_dense_rows_full_p5 p.2 + a * good_slopes_fiber55_dense_rows_full_p5 p.1

noncomputable def good_slopes_fiber55_dense_rows_full_psi (c : ZMod 11) (p : ZMod 55 × ZMod 55) : ZMod 11 :=
  good_slopes_fiber55_dense_rows_full_p11 p.2 + c * good_slopes_fiber55_dense_rows_full_p11 p.1

noncomputable def good_slopes_fiber55_dense_rows_full_lvl (a : ZMod 5) (S : Finset (ZMod 55 × ZMod 55)) (t : ZMod 5) :
    Finset (ZMod 55 × ZMod 55) :=
  S.filter (fun p => good_slopes_fiber55_dense_rows_full_phi a p = t)

noncomputable def good_slopes_fiber55_dense_rows_full_pair11 (p : ZMod 55 × ZMod 55) : ZMod 11 × ZMod 11 :=
  (good_slopes_fiber55_dense_rows_full_p11 p.1, good_slopes_fiber55_dense_rows_full_p11 p.2)

noncomputable def good_slopes_fiber55_dense_rows_full_T (a : ZMod 5) (S : Finset (ZMod 55 × ZMod 55)) (t : ZMod 5) :
    Finset (ZMod 11 × ZMod 11) :=
  (good_slopes_fiber55_dense_rows_full_lvl a S t).image good_slopes_fiber55_dense_rows_full_pair11

noncomputable def good_slopes_fiber55_dense_rows_full_goodrow (S : Finset (ZMod 55 × ZMod 55)) (a : ZMod 5) :
    Finset (ZMod 55) :=
  (good_slopes_point_directions 55 S).filter (fun b => b.val % 5 = a.val)

noncomputable def good_slopes_fiber55_dense_rows_full_gset (S : Finset (ZMod 55 × ZMod 55)) (a : ZMod 5) :
    Finset (ZMod 11) :=
  (good_slopes_fiber55_dense_rows_full_goodrow S a).image good_slopes_fiber55_dense_rows_full_p11

/-- The pair of reductions modulo 5 and 11 is injective on `ZMod 55`. -/
theorem good_slopes_fiber55_dense_rows_full_crtp_inj (z w : ZMod 55)
    (h : good_slopes_fiber55_dense_rows_full_crtp z = good_slopes_fiber55_dense_rows_full_crtp w) : z = w := by
  have h1 : (z.val : ZMod 5) = (w.val : ZMod 5) := by
    have hf := congrArg Prod.fst h
    simp only [good_slopes_fiber55_dense_rows_full_crtp, good_slopes_fiber55_dense_rows_full_p5,
      ZMod.castHom_apply, ZMod.cast_eq_val] at hf
    exact hf
  have h2 : (z.val : ZMod 11) = (w.val : ZMod 11) := by
    have hf := congrArg Prod.snd h
    simp only [good_slopes_fiber55_dense_rows_full_crtp, good_slopes_fiber55_dense_rows_full_p11,
      ZMod.castHom_apply, ZMod.cast_eq_val] at hf
    exact hf
  have h1' : z.val ≡ w.val [MOD 5] := by rw [← ZMod.natCast_eq_natCast_iff]; exact h1
  have h2' : z.val ≡ w.val [MOD 11] := by rw [← ZMod.natCast_eq_natCast_iff]; exact h2
  have h3 : z.val ≡ w.val [MOD 55] := by
    rw [← Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 5 11 by decide)]
    exact ⟨h1', h2'⟩
  have h4 : z.val = w.val := Nat.ModEq.eq_of_lt_of_lt h3 (ZMod.val_lt z) (ZMod.val_lt w)
  exact ZMod.val_injective 55 h4

/-- The CRT reduction of a linear-form value is given by `phi` and `psi`. -/
theorem good_slopes_fiber55_dense_rows_full_crtp_form (b : ZMod 55) (a : ZMod 5) (c : ZMod 11)
    (hb5 : good_slopes_fiber55_dense_rows_full_p5 b = a)
    (hb11 : good_slopes_fiber55_dense_rows_full_p11 b = c) (p : ZMod 55 × ZMod 55) :
    good_slopes_fiber55_dense_rows_full_crtp (p.2 + b*p.1) =
      (good_slopes_fiber55_dense_rows_full_phi a p, good_slopes_fiber55_dense_rows_full_psi c p) := by
  have h : good_slopes_fiber55_dense_rows_full_crtp (p.2 + b*p.1) =
      (good_slopes_fiber55_dense_rows_full_phi (good_slopes_fiber55_dense_rows_full_p5 b) p,
       good_slopes_fiber55_dense_rows_full_psi (good_slopes_fiber55_dense_rows_full_p11 b) p) := by
    simp only [good_slopes_fiber55_dense_rows_full_crtp, good_slopes_fiber55_dense_rows_full_phi,
      good_slopes_fiber55_dense_rows_full_psi, map_add, map_mul]
  rw [h, hb5, hb11]

/-- Equality of two linear-form values splits into the mod-5 and mod-11 components. -/
theorem good_slopes_fiber55_dense_rows_full_form_congr (b : ZMod 55) (a : ZMod 5) (c : ZMod 11)
    (hb5 : good_slopes_fiber55_dense_rows_full_p5 b = a)
    (hb11 : good_slopes_fiber55_dense_rows_full_p11 b = c) (p q : ZMod 55 × ZMod 55) :
    (p.2 + b*p.1 = q.2 + b*q.1) ↔
      ((good_slopes_fiber55_dense_rows_full_phi a p, good_slopes_fiber55_dense_rows_full_psi c p) =
       (good_slopes_fiber55_dense_rows_full_phi a q, good_slopes_fiber55_dense_rows_full_psi c q)) := by
  constructor
  · intro h
    rw [← good_slopes_fiber55_dense_rows_full_crtp_form b a c hb5 hb11 p,
      ← good_slopes_fiber55_dense_rows_full_crtp_form b a c hb5 hb11 q, h]
  · intro h
    apply good_slopes_fiber55_dense_rows_full_crtp_inj
    rw [good_slopes_fiber55_dense_rows_full_crtp_form b a c hb5 hb11 p,
      good_slopes_fiber55_dense_rows_full_crtp_form b a c hb5 hb11 q, h]

/-- The reduction modulo 5 is determined by the residue of the value modulo 5. -/
theorem good_slopes_fiber55_dense_rows_full_p5_eq_of_val (b : ZMod 55) (a : ZMod 5)
    (h : b.val % 5 = a.val) : good_slopes_fiber55_dense_rows_full_p5 b = a := by
  apply ZMod.val_injective
  rw [show (good_slopes_fiber55_dense_rows_full_p5 b).val = b.val % 5 from by
    simp only [good_slopes_fiber55_dense_rows_full_p5, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]]
  exact h

/-- The reduction modulo 11 is injective on the good directions of a fixed mod-5 row. -/
theorem good_slopes_fiber55_dense_rows_full_p11_injOn_goodrow
    (S : Finset (ZMod 55 × ZMod 55)) (a : ZMod 5) :
    Set.InjOn good_slopes_fiber55_dense_rows_full_p11 ↑(good_slopes_fiber55_dense_rows_full_goodrow S a) := by
  intro b hb b' hb' h
  have hb5 : good_slopes_fiber55_dense_rows_full_p5 b = a :=
    good_slopes_fiber55_dense_rows_full_p5_eq_of_val b a (Finset.mem_filter.mp hb).2
  have hb'5 : good_slopes_fiber55_dense_rows_full_p5 b' = a :=
    good_slopes_fiber55_dense_rows_full_p5_eq_of_val b' a (Finset.mem_filter.mp hb').2
  apply good_slopes_fiber55_dense_rows_full_crtp_inj
  simp only [good_slopes_fiber55_dense_rows_full_crtp]
  rw [hb5, hb'5, h]

/-- The mod-11 projection is injective on a level set when one mod-11 form is injective there. -/
theorem good_slopes_fiber55_dense_rows_full_pair11_injOn (a : ZMod 5) (S : Finset (ZMod 55 × ZMod 55))
    (c0 : ZMod 11) (t : ZMod 5)
    (hinj : Set.InjOn (good_slopes_fiber55_dense_rows_full_psi c0) ↑(good_slopes_fiber55_dense_rows_full_lvl a S t)) :
    Set.InjOn good_slopes_fiber55_dense_rows_full_pair11 ↑(good_slopes_fiber55_dense_rows_full_lvl a S t) := by
  intro p hp q hq h
  apply hinj hp hq
  simp only [good_slopes_fiber55_dense_rows_full_pair11, good_slopes_fiber55_dense_rows_full_psi] at h ⊢
  rw [Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- The cardinality of the mod-11 image of a level set. -/
theorem good_slopes_fiber55_dense_rows_full_T_card (a : ZMod 5) (S : Finset (ZMod 55 × ZMod 55))
    (c0 : ZMod 11) (t : ZMod 5)
    (hinj : Set.InjOn (good_slopes_fiber55_dense_rows_full_psi c0) ↑(good_slopes_fiber55_dense_rows_full_lvl a S t)) :
    (good_slopes_fiber55_dense_rows_full_T a S t).card = (good_slopes_fiber55_dense_rows_full_lvl a S t).card :=
  Finset.card_image_of_injOn (good_slopes_fiber55_dense_rows_full_pair11_injOn a S c0 t hinj)

/-- The levels of the mod-5 form partition `S`. -/
theorem good_slopes_fiber55_dense_rows_full_sum_lvl (a : ZMod 5) (S : Finset (ZMod 55 × ZMod 55)) :
    S.card = ∑ t : ZMod 5, (good_slopes_fiber55_dense_rows_full_lvl a S t).card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := good_slopes_fiber55_dense_rows_full_phi a) (s := S)
    (t := (Finset.univ : Finset (ZMod 5))) (by intro x hx; exact Finset.mem_univ _)
  simpa [good_slopes_fiber55_dense_rows_full_lvl] using h

/-- An injective mod-11 form bounds a level set by eleven points. -/
theorem good_slopes_fiber55_dense_rows_full_lvl_le (a : ZMod 5) (S : Finset (ZMod 55 × ZMod 55))
    (c0 : ZMod 11) (t : ZMod 5)
    (hinj : Set.InjOn (good_slopes_fiber55_dense_rows_full_psi c0) ↑(good_slopes_fiber55_dense_rows_full_lvl a S t)) :
    (good_slopes_fiber55_dense_rows_full_lvl a S t).card ≤ 11 := by
  have h1 : ((good_slopes_fiber55_dense_rows_full_lvl a S t).image (good_slopes_fiber55_dense_rows_full_psi c0)).card
      = (good_slopes_fiber55_dense_rows_full_lvl a S t).card := Finset.card_image_of_injOn hinj
  have h2 : ((good_slopes_fiber55_dense_rows_full_lvl a S t).image (good_slopes_fiber55_dense_rows_full_psi c0)).card
      ≤ Fintype.card (ZMod 11) := Finset.card_le_univ _
  have h3 : Fintype.card (ZMod 11) = 11 := ZMod.card 11
  omega

/-- Every level set of the mod-5 form has exactly eleven points. -/
theorem good_slopes_fiber55_dense_rows_full_lvl_eq (a : ZMod 5) (S : Finset (ZMod 55 × ZMod 55))
    (hcard : S.card = 55)
    (hle : ∀ t, (good_slopes_fiber55_dense_rows_full_lvl a S t).card ≤ 11) :
    ∀ t, (good_slopes_fiber55_dense_rows_full_lvl a S t).card = 11 := by
  intro t0
  have hsum := good_slopes_fiber55_dense_rows_full_sum_lvl a S
  rw [hcard] at hsum
  have hsum' : ∑ t : ZMod 5, (good_slopes_fiber55_dense_rows_full_lvl a S t).card = 55 := hsum.symm
  have hconst : ∑ t : ZMod 5, (11:ℕ) = 55 := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    norm_num
  by_contra hne
  have hlt : (good_slopes_fiber55_dense_rows_full_lvl a S t0).card < 11 := lt_of_le_of_ne (hle t0) hne
  have hstrict : ∑ t : ZMod 5, (good_slopes_fiber55_dense_rows_full_lvl a S t).card < ∑ t : ZMod 5, (11:ℕ) :=
    Finset.sum_lt_sum (fun t _ => hle t) ⟨t0, Finset.mem_univ _, hlt⟩
  rw [hsum', hconst] at hstrict
  exact lt_irrefl _ hstrict

/-- A set injectively colored by three colors has at most three points. -/
theorem good_slopes_fiber55_dense_rows_full_card_le_three (L : Finset (ZMod 55 × ZMod 55))
    (f : (ZMod 55 × ZMod 55) → Fin 3) (hinj : Set.InjOn f ↑L) : L.card ≤ 3 := by
  have h1 : (L.image f).card = L.card := Finset.card_image_of_injOn hinj
  have h2 : (L.image f).card ≤ Fintype.card (Fin 3) := Finset.card_le_univ _
  have h3 : Fintype.card (Fin 3) = 3 := by simp
  omega

/-- A good direction makes the corresponding mod-11 form injective on every level set. -/
theorem good_slopes_fiber55_dense_rows_full_psi_injOn_lvl_of_good (a : ZMod 5)
    (S : Finset (ZMod 55 × ZMod 55)) (t : ZMod 5) (b0 : ZMod 55)
    (hb5 : good_slopes_fiber55_dense_rows_full_p5 b0 = a)
    (hinj : Set.InjOn (fun p : ZMod 55 × ZMod 55 => p.2 + b0*p.1) ↑S) :
    Set.InjOn (good_slopes_fiber55_dense_rows_full_psi (good_slopes_fiber55_dense_rows_full_p11 b0))
      ↑(good_slopes_fiber55_dense_rows_full_lvl a S t) := by
  intro p hp q hq h
  have hpS := (Finset.mem_filter.mp hp).1
  have hqS := (Finset.mem_filter.mp hq).1
  have hpphi := (Finset.mem_filter.mp hp).2
  have hqphi := (Finset.mem_filter.mp hq).2
  apply hinj hpS hqS
  exact (good_slopes_fiber55_dense_rows_full_form_congr b0 a
    (good_slopes_fiber55_dense_rows_full_p11 b0) hb5 rfl p q).mpr
    (Prod.ext_iff.mpr ⟨hpphi.trans hqphi.symm, h⟩)

/-- Each direction of the dense row is injective on the mod-11 image of every level set. -/
theorem good_slopes_fiber55_dense_rows_full_G_injOn_T (a : ZMod 5) (S : Finset (ZMod 55 × ZMod 55))
    (t : ZMod 5) (cin : ZMod 11) (hcin : cin ∈ good_slopes_fiber55_dense_rows_full_gset S a) :
    Set.InjOn (fun q : ZMod 11 × ZMod 11 => q.2 + cin * q.1)
      ↑(good_slopes_fiber55_dense_rows_full_T a S t) := by
  obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp hcin
  have hbgood : b ∈ good_slopes_point_directions 55 S := (Finset.mem_filter.mp hb).1
  have hbval : b.val % 5 = a.val := (Finset.mem_filter.mp hb).2
  have hb5 : good_slopes_fiber55_dense_rows_full_p5 b = a :=
    good_slopes_fiber55_dense_rows_full_p5_eq_of_val b a hbval
  have hbdata : IsUnit b ∧ Set.InjOn (fun p : ZMod 55 × ZMod 55 => p.2 + b * p.1) ↑S := by
    simpa [good_slopes_point_directions] using hbgood
  have hbinj := hbdata.2
  intro q1 hq1 q2 hq2 hform
  obtain ⟨p1, hp1, hp1eq⟩ := Finset.mem_image.mp hq1
  obtain ⟨p2, hp2, hp2eq⟩ := Finset.mem_image.mp hq2
  subst hp1eq
  subst hp2eq
  have hphi1 : good_slopes_fiber55_dense_rows_full_phi a p1 = t := (Finset.mem_filter.mp hp1).2
  have hphi2 : good_slopes_fiber55_dense_rows_full_phi a p2 = t := (Finset.mem_filter.mp hp2).2
  have hpsi : good_slopes_fiber55_dense_rows_full_psi cin p1 = good_slopes_fiber55_dense_rows_full_psi cin p2 := by
    simpa [good_slopes_fiber55_dense_rows_full_psi, good_slopes_fiber55_dense_rows_full_pair11] using hform
  have hp1S := (Finset.mem_filter.mp hp1).1
  have hp2S := (Finset.mem_filter.mp hp2).1
  have hf : p1.2 + b*p1.1 = p2.2 + b*p2.1 :=
    (good_slopes_fiber55_dense_rows_full_form_congr b a cin hb5 hbc p1 p2).mpr
      (Prod.ext_iff.mpr ⟨hphi1.trans hphi2.symm, hpsi⟩)
  have hpeq : p1 = p2 := hbinj hp1S hp2S hf
  rw [hpeq]

/-- A vertical level set gives injectivity for every mod-11 form. -/
theorem good_slopes_fiber55_dense_rows_full_psi_injOn_of_vertical (a : ZMod 5)
    (S : Finset (ZMod 55 × ZMod 55)) (t : ZMod 5) (c : ZMod 11)
    (hpairinj : Set.InjOn good_slopes_fiber55_dense_rows_full_pair11
      ↑(good_slopes_fiber55_dense_rows_full_lvl a S t))
    (x0 : ZMod 11) (hline : ∀ q ∈ good_slopes_fiber55_dense_rows_full_T a S t, q.1 = x0) :
    Set.InjOn (good_slopes_fiber55_dense_rows_full_psi c) ↑(good_slopes_fiber55_dense_rows_full_lvl a S t) := by
  intro p1 hp1 p2 hp2 hpsi
  have hin1 : good_slopes_fiber55_dense_rows_full_pair11 p1 ∈ good_slopes_fiber55_dense_rows_full_T a S t :=
    Finset.mem_image.mpr ⟨p1, hp1, rfl⟩
  have hin2 : good_slopes_fiber55_dense_rows_full_pair11 p2 ∈ good_slopes_fiber55_dense_rows_full_T a S t :=
    Finset.mem_image.mpr ⟨p2, hp2, rfl⟩
  have hx1 := hline _ hin1
  have hx2 := hline _ hin2
  have hv : (good_slopes_fiber55_dense_rows_full_pair11 p1).2 + c*(good_slopes_fiber55_dense_rows_full_pair11 p1).1
      = (good_slopes_fiber55_dense_rows_full_pair11 p2).2 + c*(good_slopes_fiber55_dense_rows_full_pair11 p2).1 := by
    simpa [good_slopes_fiber55_dense_rows_full_psi, good_slopes_fiber55_dense_rows_full_pair11] using hpsi
  have hy : (good_slopes_fiber55_dense_rows_full_pair11 p1).2
      = (good_slopes_fiber55_dense_rows_full_pair11 p2).2 := by
    rw [hx1, hx2] at hv
    exact add_right_cancel hv
  apply hpairinj hp1 hp2
  exact Prod.ext_iff.mpr ⟨hx1.trans hx2.symm, hy⟩

/-- A non-slanted level set gives injectivity for every other mod-11 form. -/
theorem good_slopes_fiber55_dense_rows_full_psi_injOn_of_line (a : ZMod 5)
    (S : Finset (ZMod 55 × ZMod 55)) (t : ZMod 5) (c : ZMod 11)
    (hpairinj : Set.InjOn good_slopes_fiber55_dense_rows_full_pair11
      ↑(good_slopes_fiber55_dense_rows_full_lvl a S t))
    (a0 β : ZMod 11) (hline : ∀ q ∈ good_slopes_fiber55_dense_rows_full_T a S t, q.2 + a0*q.1 = β)
    (hne : c ≠ a0) :
    Set.InjOn (good_slopes_fiber55_dense_rows_full_psi c) ↑(good_slopes_fiber55_dense_rows_full_lvl a S t) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  intro p1 hp1 p2 hp2 hpsi
  have hin1 : good_slopes_fiber55_dense_rows_full_pair11 p1 ∈ good_slopes_fiber55_dense_rows_full_T a S t :=
    Finset.mem_image.mpr ⟨p1, hp1, rfl⟩
  have hin2 : good_slopes_fiber55_dense_rows_full_pair11 p2 ∈ good_slopes_fiber55_dense_rows_full_T a S t :=
    Finset.mem_image.mpr ⟨p2, hp2, rfl⟩
  have hβ1 := hline _ hin1
  have hβ2 := hline _ hin2
  have hv : (good_slopes_fiber55_dense_rows_full_pair11 p1).2 + c*(good_slopes_fiber55_dense_rows_full_pair11 p1).1
      = (good_slopes_fiber55_dense_rows_full_pair11 p2).2 + c*(good_slopes_fiber55_dense_rows_full_pair11 p2).1 := by
    simpa [good_slopes_fiber55_dense_rows_full_psi, good_slopes_fiber55_dense_rows_full_pair11] using hpsi
  have hx : (good_slopes_fiber55_dense_rows_full_pair11 p1).1
      = (good_slopes_fiber55_dense_rows_full_pair11 p2).1 := by
    have e : (c - a0) * (good_slopes_fiber55_dense_rows_full_pair11 p1).1
        = (c - a0) * (good_slopes_fiber55_dense_rows_full_pair11 p2).1 := by
      linear_combination hv - hβ1 + hβ2
    exact mul_left_cancel₀ (sub_ne_zero.mpr hne) e
  have hy : (good_slopes_fiber55_dense_rows_full_pair11 p1).2
      = (good_slopes_fiber55_dense_rows_full_pair11 p2).2 := by
    rw [hx] at hv
    exact add_right_cancel hv
  apply hpairinj hp1 hp2
  exact Prod.ext_iff.mpr ⟨hx, hy⟩

/-- A slanted level set whose direction equals the target direction contradicts the color hypothesis. -/
theorem good_slopes_fiber55_dense_rows_full_contradiction_of_line_dir (a : ZMod 5)
    (S : Finset (ZMod 55 × ZMod 55)) (t : ZMod 5) (color : (ZMod 55 × ZMod 55) → Fin 3)
    (b : ZMod 55) (c : ZMod 11)
    (hb5 : good_slopes_fiber55_dense_rows_full_p5 b = a)
    (hb11 : good_slopes_fiber55_dense_rows_full_p11 b = c)
    (hc : ∀ b : ZMod 55, IsUnit b → ∀ p ∈ S, ∀ q ∈ S,
      color p = color q → p.2 + b*p.1 = q.2 + b*q.1 → p = q)
    (hunit : IsUnit b)
    (hlevel : (good_slopes_fiber55_dense_rows_full_lvl a S t).card = 11)
    (β : ZMod 11)
    (hline : ∀ q ∈ good_slopes_fiber55_dense_rows_full_T a S t,
      q.2 + c*q.1 = β) : False := by
  have hcol : Set.InjOn color ↑(good_slopes_fiber55_dense_rows_full_lvl a S t) := by
    intro p hp q hq hcolor
    have hpS := (Finset.mem_filter.mp hp).1
    have hqS := (Finset.mem_filter.mp hq).1
    have hpphi := (Finset.mem_filter.mp hp).2
    have hqphi := (Finset.mem_filter.mp hq).2
    have hpβ : good_slopes_fiber55_dense_rows_full_psi c p = β := by
      have := hline (good_slopes_fiber55_dense_rows_full_pair11 p)
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      simpa [good_slopes_fiber55_dense_rows_full_psi, good_slopes_fiber55_dense_rows_full_pair11] using this
    have hqβ : good_slopes_fiber55_dense_rows_full_psi c q = β := by
      have := hline (good_slopes_fiber55_dense_rows_full_pair11 q)
        (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      simpa [good_slopes_fiber55_dense_rows_full_psi, good_slopes_fiber55_dense_rows_full_pair11] using this
    apply hc b hunit p hpS q hqS hcolor
    exact (good_slopes_fiber55_dense_rows_full_form_congr b a c hb5 hb11 p q).mpr
      (Prod.ext_iff.mpr ⟨hpphi.trans hqphi.symm, hpβ.trans hqβ.symm⟩)
  have hle3 : (good_slopes_fiber55_dense_rows_full_lvl a S t).card ≤ 3 :=
    good_slopes_fiber55_dense_rows_full_card_le_three _ color hcol
  omega

theorem good_slopes_fiber55_dense_rows_full
    (S : Finset (ZMod 55 × ZMod 55)) (color : (ZMod 55 × ZMod 55) → Fin 3)
    (hcard : S.card = 55)
    (hx : ∀ p ∈ S, ∀ q ∈ S, color p = color q → p.1 = q.1 → p = q)
    (hc : ∀ b : ZMod 55, IsUnit b → ∀ p ∈ S, ∀ q ∈ S,
      color p = color q → p.2 + b*p.1 = q.2 + b*q.1 → p = q)
    (a a' : ZMod 5) (ha : IsUnit a) (ha' : IsUnit a') (hne : a ≠ a')
    (hdense : 6 ≤ ((good_slopes_point_directions 55 S).filter fun b => b.val % 5 = a.val).card)
    (hdense' : 6 ≤ ((good_slopes_point_directions 55 S).filter fun b => b.val % 5 = a'.val).card) :
    ∀ b : ZMod 55, IsUnit b → b.val % 5 = a.val → b ∈ good_slopes_point_directions 55 S := by
  classical
  have hGRne : (good_slopes_fiber55_dense_rows_full_goodrow S a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have hden := hdense
    rw [show ((good_slopes_point_directions 55 S).filter fun b => b.val % 5 = a.val) =
      good_slopes_fiber55_dense_rows_full_goodrow S a from rfl, hE] at hden
    simp at hden
  obtain ⟨b0, hb0⟩ := hGRne
  have hb0good : b0 ∈ good_slopes_point_directions 55 S := (Finset.mem_filter.mp hb0).1
  have hb0val : b0.val % 5 = a.val := (Finset.mem_filter.mp hb0).2
  have hb05 : good_slopes_fiber55_dense_rows_full_p5 b0 = a :=
    good_slopes_fiber55_dense_rows_full_p5_eq_of_val b0 a hb0val
  have hb0inj : Set.InjOn (fun p : ZMod 55 × ZMod 55 => p.2 + b0*p.1) ↑S := by
    have h := hb0good
    simp only [good_slopes_point_directions, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.2
  have hc0 : ∀ t, Set.InjOn (good_slopes_fiber55_dense_rows_full_psi (good_slopes_fiber55_dense_rows_full_p11 b0))
      ↑(good_slopes_fiber55_dense_rows_full_lvl a S t) :=
    fun t => good_slopes_fiber55_dense_rows_full_psi_injOn_lvl_of_good a S t b0 hb05 hb0inj
  have hlevel_le : ∀ t, (good_slopes_fiber55_dense_rows_full_lvl a S t).card ≤ 11 :=
    fun t => good_slopes_fiber55_dense_rows_full_lvl_le a S (good_slopes_fiber55_dense_rows_full_p11 b0) t (hc0 t)
  have hlevel : ∀ t, (good_slopes_fiber55_dense_rows_full_lvl a S t).card = 11 :=
    good_slopes_fiber55_dense_rows_full_lvl_eq a S hcard hlevel_le
  have hTcard : ∀ t, (good_slopes_fiber55_dense_rows_full_T a S t).card = 11 := by
    intro t
    rw [good_slopes_fiber55_dense_rows_full_T_card a S (good_slopes_fiber55_dense_rows_full_p11 b0) t (hc0 t)]
    exact hlevel t
  have hGcard : 6 ≤ (good_slopes_fiber55_dense_rows_full_gset S a).card := by
    rw [show (good_slopes_fiber55_dense_rows_full_gset S a).card =
      (good_slopes_fiber55_dense_rows_full_goodrow S a).card from
      Finset.card_image_of_injOn (good_slopes_fiber55_dense_rows_full_p11_injOn_goodrow S a)]
    exact hdense
  have hline : ∀ t, (∃ x, ∀ q ∈ good_slopes_fiber55_dense_rows_full_T a S t, q.1 = x) ∨
      (∃ a0 β, ∀ q ∈ good_slopes_fiber55_dense_rows_full_T a S t, q.2 + a0*q.1 = β) :=
    fun t => good_slopes_prime11_six_good_lines (good_slopes_fiber55_dense_rows_full_T a S t)
      (good_slopes_fiber55_dense_rows_full_gset S a) (hTcard t) hGcard
      (good_slopes_fiber55_dense_rows_full_G_injOn_T a S t)
  intro b hbunit hbval
  have hb5 : good_slopes_fiber55_dense_rows_full_p5 b = a :=
    good_slopes_fiber55_dense_rows_full_p5_eq_of_val b a hbval
  have hpsiinj : ∀ t, Set.InjOn (good_slopes_fiber55_dense_rows_full_psi (good_slopes_fiber55_dense_rows_full_p11 b))
      ↑(good_slopes_fiber55_dense_rows_full_lvl a S t) := by
    intro t
    have hpair := good_slopes_fiber55_dense_rows_full_pair11_injOn a S
      (good_slopes_fiber55_dense_rows_full_p11 b0) t (hc0 t)
    rcases hline t with ⟨x0, hx0⟩ | ⟨a0, β, hβ⟩
    · exact good_slopes_fiber55_dense_rows_full_psi_injOn_of_vertical a S t
        (good_slopes_fiber55_dense_rows_full_p11 b) hpair x0 hx0
    · by_cases hca : good_slopes_fiber55_dense_rows_full_p11 b = a0
      · exfalso
        exact good_slopes_fiber55_dense_rows_full_contradiction_of_line_dir a S t color b
          (good_slopes_fiber55_dense_rows_full_p11 b) hb5 rfl hc hbunit (hlevel t) β
          (fun q hq => by rw [hca]; exact hβ q hq)
      · exact good_slopes_fiber55_dense_rows_full_psi_injOn_of_line a S t
          (good_slopes_fiber55_dense_rows_full_p11 b) hpair a0 β hβ hca
  simp only [good_slopes_point_directions, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hbunit, ?_⟩
  intro p hp q hq hform
  have hcongr := (good_slopes_fiber55_dense_rows_full_form_congr b a
    (good_slopes_fiber55_dense_rows_full_p11 b) hb5 rfl p q).mp hform
  have hphi : good_slopes_fiber55_dense_rows_full_phi a p = good_slopes_fiber55_dense_rows_full_phi a q :=
    congrArg Prod.fst hcongr
  have hpsi : good_slopes_fiber55_dense_rows_full_psi (good_slopes_fiber55_dense_rows_full_p11 b) p
      = good_slopes_fiber55_dense_rows_full_psi (good_slopes_fiber55_dense_rows_full_p11 b) q :=
    congrArg Prod.snd hcongr
  exact hpsiinj (good_slopes_fiber55_dense_rows_full_phi a p)
    (Finset.mem_filter.mpr ⟨hp, rfl⟩) (Finset.mem_filter.mpr ⟨hq, hphi.symm⟩) hpsi
