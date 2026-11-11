import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber35UnanchoredRect
import AFTD.Kb.NumberTheory.GoodSlopes35RectangleTable

/-!
# good_slopes_fiber35_crt_rectangle_exclusion

Topic: elementary_number_theory   Node: 07b9d3cddaae

Provenance: helper lemma. CRT normalization of the three checked 35-point rectangle obstructions in the reduction for OP-1027.

A 35-point set with x-width at most three cannot have all unit directions good outside a rectangle whose mod-5 coordinates are two nonzero residues and whose mod-7 coordinates form a nonzero multiple of {1,2,4}, while any unit direction is bad.
-/

set_option maxHeartbeats 4000000
private def aftd_crt35_good (r : Fin 3) : Finset (ZMod 35) :=
  if r = 0 then {3,4,6,8,9,12,13,17,18,19,23,24,26,27,29,31,33,34}
  else if r = 1 then {2,3,4,6,9,12,13,17,19,22,24,26,27,29,31,32,33,34}
  else {2,3,6,8,12,13,17,18,19,22,23,24,26,27,31,32,33,34}

private def aftd_crt35_unit : Finset (ZMod 35) :=
  {1,2,3,4,6,8,9,11,12,13,16,17,18,19,22,23,24,26,27,29,31,32,33,34}

private theorem aftd_crt35__good_units : ∀ r : Fin 3, aftd_crt35_good r ⊆ aftd_crt35_unit := by decide

private theorem aftd_crt35__unit_table : ∀ b : ZMod 35, Nat.Coprime b.val 35 ↔ b ∈ aftd_crt35_unit := by decide

private def aftd_crt35_ratio (r : Fin 3) : ZMod 5 := (r.val + 2 : ℕ)

private theorem aftd_crt35__ratio5_table : ∀ (a₁ a₂ x : ZMod 5),
    a₁ ≠ 0 → a₂ ≠ 0 → a₁ ≠ a₂ → (x = a₁ ∨ x = a₂) →
    ∃ r : Fin 3, ∀ z : ZMod 5, z ≠ 1 → z ≠ aftd_crt35_ratio r → x*z ≠ a₁ ∧ x*z ≠ a₂ := by decide

private theorem aftd_crt35__coset7_table : ∀ (t y : ZMod 7), t ≠ 0 →
    (y = t ∨ y = 2*t ∨ y = 4*t) → ∀ z : ZMod 7, z ≠ 1 → z ≠ 2 → z ≠ 4 →
    y*z ≠ t ∧ y*z ≠ 2*t ∧ y*z ≠ 4*t := by decide

private theorem aftd_crt35__mask_table : ∀ (r : Fin 3) (b : ZMod 35), b ∈ aftd_crt35_good r →
    ((ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) b ≠ 1) ∧
     (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) b ≠ aftd_crt35_ratio r)) ∨
    ((ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ 1) ∧
     (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ 2) ∧
     (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ 4)) := by decide

private theorem aftd_crt35__rectangle_normalization_table :
    ∀ (a₁ a₂ x : ZMod 5) (t y : ZMod 7),
      a₁ ≠ 0 → a₂ ≠ 0 → a₁ ≠ a₂ → t ≠ 0 → (x = a₁ ∨ x = a₂) →
      (y = t ∨ y = 2*t ∨ y = 4*t) →
      ∃ r : Fin 3, ∀ b ∈ aftd_crt35_good r,
        ((x*(ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) b) ≠ a₁) ∧
         (x*(ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) b) ≠ a₂)) ∨
        ((y*(ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b) ≠ t) ∧
         (y*(ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b) ≠ 2*t) ∧
         (y*(ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b) ≠ 4*t)) := by
  intro a₁ a₂ x t y h1 h2 hne ht hx hy
  obtain ⟨r,hr⟩ := aftd_crt35__ratio5_table a₁ a₂ x h1 h2 hne hx
  refine ⟨r,?_⟩
  intro b hb
  rcases aftd_crt35__mask_table r b hb with h5 | h7
  · exact Or.inl (hr _ h5.1 h5.2)
  · exact Or.inr (aftd_crt35__coset7_table t y ht hy _ h7.1 h7.2.1 h7.2.2)

theorem good_slopes_fiber35_crt_rectangle_exclusion (S : Finset (ZMod 35 × ZMod 35)) (hcard : S.card = 35) (hwidth : ∀ x : ZMod 35, (S.filter fun p => p.1 = x).card ≤ 3) (a₁ a₂ : ZMod 5) (t : ZMod 7) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha : a₁ ≠ a₂) (ht : t ≠ 0) (hgood : ∀ b : ZMod 35, IsUnit b → (((ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) b ≠ a₁) ∧ (ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5) b ≠ a₂)) ∨ ((ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ t) ∧ (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ 2*t) ∧ (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7) b ≠ 4*t))) → b ∈ good_slopes_point_directions 35 S) (hbad : ∃ b : ZMod 35, IsUnit b ∧ b ∉ good_slopes_point_directions 35 S) : False := by
  classical
  obtain ⟨a,hau,habad⟩ := hbad
  let c5 : ZMod 35 →+* ZMod 5 := ZMod.castHom (by decide : 5 ∣ 35) (ZMod 5)
  let c7 : ZMod 35 →+* ZMod 7 := ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)
  have h5 : c5 a = a₁ ∨ c5 a = a₂ := by
    by_contra hh
    have h1 : c5 a ≠ a₁ := fun h => hh (Or.inl h)
    have h2 : c5 a ≠ a₂ := fun h => hh (Or.inr h)
    exact habad (hgood a hau (Or.inl ⟨h1,h2⟩))
  have h7 : c7 a = t ∨ c7 a = 2*t ∨ c7 a = 4*t := by
    by_contra hh
    have h1 : c7 a ≠ t := fun h => hh (Or.inl h)
    have h2 : c7 a ≠ 2*t := fun h => hh (Or.inr (Or.inl h))
    have h3 : c7 a ≠ 4*t := fun h => hh (Or.inr (Or.inr h))
    exact habad (hgood a hau (Or.inr ⟨h1,h2,h3⟩))
  obtain ⟨r,hr⟩ := aftd_crt35__rectangle_normalization_table a₁ a₂ (c5 a) t (c7 a) ha₁ ha₂ ha ht h5 h7
  let au : (ZMod 35)ˣ := hau.unit
  have hav : (au : ZMod 35) = a := hau.unit_spec
  let aftd_crt_scale_map : ZMod 35 × ZMod 35 → ZMod 35 × ZMod 35 := fun p => (p.1,((au⁻¹ : (ZMod 35)ˣ) : ZMod 35)*p.2)
  have hH : Function.Injective aftd_crt_scale_map := by
    intro p q heq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    change p.1 = q.1 at hx
    change ((au⁻¹ : (ZMod 35)ˣ) : ZMod 35)*p.2 = ((au⁻¹ : (ZMod 35)ˣ) : ZMod 35)*q.2 at hy
    exact Prod.ext hx ((au⁻¹).isUnit.mul_right_injective hy)
  have hscale (p : ZMod 35 × ZMod 35) (b : ZMod 35) :
      a*((aftd_crt_scale_map p).2+b*(aftd_crt_scale_map p).1) = p.2+(a*b)*p.1 := by
    have haa : a*((au⁻¹ : (ZMod 35)ˣ) : ZMod 35) = 1 := by rw [← hav]; simp
    change a*(((au⁻¹ : (ZMod 35)ˣ) : ZMod 35)*p.2+b*p.1) = _
    calc
      _ = (a*((au⁻¹ : (ZMod 35)ˣ) : ZMod 35))*p.2+(a*b)*p.1 := by ring
      _ = _ := by rw [haa]; ring
  let T := S.image aftd_crt_scale_map
  have hTc : T.card = 35 := by rw [Finset.card_image_of_injective _ hH,hcard]
  have hTwidth : ∀ x : ZMod 35, (T.filter fun p => p.1=x).card ≤ 3 := by
    intro x
    have heq : T.filter (fun p => p.1=x) = (S.filter fun p => p.1=x).image aftd_crt_scale_map := by
      ext p
      simp only [T,Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨⟨q,hq,rfl⟩,hx⟩
        exact ⟨q,⟨hq,hx⟩,rfl⟩
      · rintro ⟨q,⟨hq,hx⟩,rfl⟩
        exact ⟨⟨q,hq,rfl⟩,hx⟩
    rw [heq,Finset.card_image_of_injective _ hH]
    exact hwidth x
  have hTbad : ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+p.1) T := by
    intro hi
    apply habad
    have haform : Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+a*p.1) S := by
      intro p hp q hq heq
      apply hH
      apply hi (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hq)
      apply hau.mul_right_injective
      calc
        _ = p.2+a*p.1 := by simpa using hscale p 1
        _ = q.2+a*q.1 := heq
        _ = _ := by symm; simpa using hscale q 1
    simp [good_slopes_point_directions,hau,haform]
  have hTgood : ∀ b ∈ aftd_crt35_good r,
      Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+b*p.1) T := by
    intro b hb p hp q hq heq
    have hbu : IsUnit b := by
      have hh : Nat.Coprime b.val 35 := (aftd_crt35__unit_table b).mpr (aftd_crt35__good_units r hb)
      simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime b.val 35).mpr hh
    have hout := hr b hb
    have hout' : ((c5 (a*b) ≠ a₁) ∧ (c5 (a*b) ≠ a₂)) ∨
        ((c7 (a*b) ≠ t) ∧ (c7 (a*b) ≠ 2*t) ∧ (c7 (a*b) ≠ 4*t)) := by
      simpa only [map_mul] using hout
    have hg := hgood (a*b) (hau.mul hbu) hout'
    have hi : Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+(a*b)*p.1) S :=
      (Finset.mem_filter.mp hg).2.2
    obtain ⟨x,hx,hxp⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,hyq⟩ := Finset.mem_image.mp hq
    have heq' : (aftd_crt_scale_map x).2+b*(aftd_crt_scale_map x).1 = (aftd_crt_scale_map y).2+b*(aftd_crt_scale_map y).1 := by simpa [hxp,hyq] using heq
    have hh := congrArg (fun z : ZMod 35 => a*z) heq'
    rw [hscale,hscale] at hh
    have hxy : x = y := hi hx hy hh
    exact hxp.symm.trans ((congrArg aftd_crt_scale_map hxy).trans hyq)
  apply good_slopes_fiber35_unanchored_rect T hTc hTwidth r
  · exact hTgood
  · exact hTbad
