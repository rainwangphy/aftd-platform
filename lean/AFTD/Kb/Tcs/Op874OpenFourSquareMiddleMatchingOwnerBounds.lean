import AFTD.Prelude
import AFTD.Kb.Tcs.Op874UnusedLowColorHasUniqueHiddenPort
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.M
import AFTD.Kb.Tcs.Bit

/-!
# op874_open_four_square_middle_matching_owner_bounds

Topic: graphs   Node: d69d252ca5f8

Provenance: helper lemma. OP-874 opened four-square same-bit path ownership transfer; experiment 41917.

For the displayed opened four-square block with arbitrary opened-port bits, the stated local six-color compatibility conditions force at most one matching-port owner on each of the three-vertex paths 13–14–15 and 9–8–11.
-/

private def in1242mid_oL : Fin 25 → Fin 18 := ![0,0,0,1,1,2,3,4,4,4,5,5,6,7,8,8,9,10,10,11,12,12,12,13,14]
private def in1242mid_oR : Fin 25 → Fin 18 := ![1,2,3,2,14,3,15,5,6,7,6,9,7,8,9,11,10,11,16,13,13,15,17,14,15]
private def in1242mid_oends (e : Fin 25) : Sym2 (Fin 18) := s(in1242mid_oL e,in1242mid_oR e)
private def in1242mid_oM : Finset (Fin 25) := {1,4,6,8,11,13,18,19,22}
private def in1242mid_oT : Fin 18 → Fin 3 → Fin 25 :=
    ![![0,2,1],![0,3,4],![3,5,1],![2,5,6],
      ![7,9,8],![7,10,11],![10,12,8],![9,12,13],
      ![14,15,13],![14,16,11],![16,17,18],![15,17,19],
      ![20,21,22],![20,23,19],![23,24,4],![21,24,6],
      ![18,18,18],![22,22,22]]
private def in1242mid_obit (x y : Bool) : Fin 18 → Bool :=
    ![true,false,true,false,true,false,true,false,false,false,x,false,y,false,false,false,x,y]
private def in1242mid_olow (x y : Bool) (v : Fin 18) : Fin 6 := cycle_matching_low_color (!(in1242mid_obit x y v))

set_option maxHeartbeats 4000000 in
private theorem in1242mid_otable : ∀ v : Fin 18, v.val < 16 →
    (∀ j, v ∈ in1242mid_oends (in1242mid_oT v j)) ∧ Function.Injective (in1242mid_oT v) ∧
    in1242mid_oT v 2 ∈ in1242mid_oM ∧ in1242mid_oT v 0 ∉ in1242mid_oM ∧ in1242mid_oT v 1 ∉ in1242mid_oM := by decide

set_option maxHeartbeats 4000000 in
private theorem in1242mid_obits (x y : Bool) : ∀ v : Fin 18, v.val < 16 →
    in1242mid_obit x y v = in1242mid_obit x y (in1242mid_oL (in1242mid_oT v 2)) := by
  cases x <;> cases y <;> decide

set_option maxHeartbeats 4000000 in
private theorem in1242mid_oedgefacts (x y : Bool) : ∀ e ∈ in1242mid_oM, e ≠ 18 → e ≠ 22 →
    (in1242mid_oL e).val < 16 ∧ (in1242mid_oR e).val < 16 ∧
    in1242mid_obit x y (in1242mid_oL e) = in1242mid_obit x y (in1242mid_oR e) ∧ in1242mid_oT (in1242mid_oL e) 2 = e ∧ in1242mid_oT (in1242mid_oR e) 2 = e := by
  cases x <;> cases y <;> decide


set_option maxHeartbeats 4000000 in
theorem in1242_open_middle_owner_bounds (x y : Bool)
    (h : Fin 18 → Fin 25 → Fin 6)
    (hhidden : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ in1242mid_oends e → v ∈ in1242mid_oends f → e ≠ f → h v e ≠ h v f)
    (hstrong : ∀ e, (in1242mid_oL e).val < 16 → (in1242mid_oR e).val < 16 → ∀ f g,
      in1242mid_oL e ∈ in1242mid_oends f → in1242mid_oR e ∈ in1242mid_oends g → f ≠ e → g ≠ e → h (in1242mid_oL e) f ≠ h (in1242mid_oR e) g)
    (hlow : ∀ v : Fin 18, v.val < 16 → ∃ j, h v (in1242mid_oT v j) = in1242mid_olow x y v) :
    let m : Fin 18 → ℕ := fun v => if h v (in1242mid_oT v 2) = in1242mid_olow x y v then 1 else 0
    m 13 + m 14 + m 15 ≤ 1 ∧ m 8 + m 9 + m 11 ≤ 1 := by
  classical
  let sel : Fin 18 → Fin 3 → ℕ := fun v j => if h v (in1242mid_oT v j) = in1242mid_olow x y v then 1 else 0
  have part (v : Fin 18) (hv : v.val < 16) : sel v 0 + sel v 1 + sel v 2 = 1 := by
    obtain ⟨j,hj⟩ := hlow v hv
    have ht := in1242mid_otable v hv
    have uniq (a b : Fin 3) (ha : h v (in1242mid_oT v a) = in1242mid_olow x y v)
        (hb : h v (in1242mid_oT v b) = in1242mid_olow x y v) : a=b := by
      by_contra hne
      exact (hhidden v hv _ _ (ht.1 a) (ht.1 b) (fun he => hne (ht.2.1 he))) (ha.trans hb.symm)
    fin_cases j
    · change h v (in1242mid_oT v 0) = in1242mid_olow x y v at hj
      have h1 : h v (in1242mid_oT v 1) ≠ in1242mid_olow x y v := by
        intro hh; exact (by decide : (0 : Fin 3) ≠ 1) (uniq 0 1 hj hh)
      have h2 : h v (in1242mid_oT v 2) ≠ in1242mid_olow x y v := by
        intro hh; exact (by decide : (0 : Fin 3) ≠ 2) (uniq 0 2 hj hh)
      simp [sel,hj,h1,h2]
    · change h v (in1242mid_oT v 1) = in1242mid_olow x y v at hj
      have h0 : h v (in1242mid_oT v 0) ≠ in1242mid_olow x y v := by
        intro hh; exact (by decide : (1 : Fin 3) ≠ 0) (uniq 1 0 hj hh)
      have h2 : h v (in1242mid_oT v 2) ≠ in1242mid_olow x y v := by
        intro hh; exact (by decide : (1 : Fin 3) ≠ 2) (uniq 1 2 hj hh)
      simp [sel,hj,h0,h2]
    · change h v (in1242mid_oT v 2) = in1242mid_olow x y v at hj
      have h0 : h v (in1242mid_oT v 0) ≠ in1242mid_olow x y v := by
        intro hh; exact (by decide : (2 : Fin 3) ≠ 0) (uniq 2 0 hj hh)
      have h1 : h v (in1242mid_oT v 1) ≠ in1242mid_olow x y v := by
        intro hh; exact (by decide : (2 : Fin 3) ≠ 1) (uniq 2 1 hj hh)
      simp [sel,hj,h0,h1]
  have required (e : Fin 25) (hl : (in1242mid_oL e).val < 16) (hr : (in1242mid_oR e).val < 16)
      (hb : in1242mid_obit x y (in1242mid_oL e) = in1242mid_obit x y (in1242mid_oR e)) :
      h (in1242mid_oL e) e = in1242mid_olow x y (in1242mid_oL e) ∨ h (in1242mid_oR e) e = in1242mid_olow x y (in1242mid_oR e) := by
    by_contra hn
    push Not at hn
    obtain ⟨p,hp⟩ := hlow (in1242mid_oL e) hl
    obtain ⟨q,hq⟩ := hlow (in1242mid_oR e) hr
    have hpe : in1242mid_oT (in1242mid_oL e) p ≠ e := by intro he; rw [he] at hp; exact hn.1 hp
    have hqe : in1242mid_oT (in1242mid_oR e) q ≠ e := by intro he; rw [he] at hq; exact hn.2 hq
    have hlr : in1242mid_olow x y (in1242mid_oL e) = in1242mid_olow x y (in1242mid_oR e) := by simp [in1242mid_olow,hb]
    exact (hstrong e hl hr _ _ ((in1242mid_otable _ hl).1 p) ((in1242mid_otable _ hr).1 q) hpe hqe)
      (hp.trans (hlr.trans hq.symm))
  have b23 : in1242mid_obit x y (in1242mid_oL 23)=in1242mid_obit x y (in1242mid_oR 23) := by cases x <;> cases y <;> decide
  have h23 := required 23 (by decide) (by decide) b23
  have c23 : 1 ≤ sel 13 1 + sel 14 0 := by
    change h 13 23 = in1242mid_olow x y 13 ∨ h 14 23 = in1242mid_olow x y 14 at h23
    change 1 ≤ (if h 13 23 = in1242mid_olow x y 13 then 1 else 0) +
      (if h 14 23 = in1242mid_olow x y 14 then 1 else 0)
    rcases h23 with hh | hh <;> simp [hh]
  have b24 : in1242mid_obit x y (in1242mid_oL 24)=in1242mid_obit x y (in1242mid_oR 24) := by cases x <;> cases y <;> decide
  have h24 := required 24 (by decide) (by decide) b24
  have c24 : 1 ≤ sel 14 1 + sel 15 1 := by
    change h 14 24 = in1242mid_olow x y 14 ∨ h 15 24 = in1242mid_olow x y 15 at h24
    change 1 ≤ (if h 14 24 = in1242mid_olow x y 14 then 1 else 0) +
      (if h 15 24 = in1242mid_olow x y 15 then 1 else 0)
    rcases h24 with hh | hh <;> simp [hh]
  have b14 : in1242mid_obit x y (in1242mid_oL 14)=in1242mid_obit x y (in1242mid_oR 14) := by cases x <;> cases y <;> decide
  have h14 := required 14 (by decide) (by decide) b14
  have c14 : 1 ≤ sel 8 0 + sel 9 0 := by
    change h 8 14 = in1242mid_olow x y 8 ∨ h 9 14 = in1242mid_olow x y 9 at h14
    change 1 ≤ (if h 8 14 = in1242mid_olow x y 8 then 1 else 0) +
      (if h 9 14 = in1242mid_olow x y 9 then 1 else 0)
    rcases h14 with hh | hh <;> simp [hh]
  have b15 : in1242mid_obit x y (in1242mid_oL 15)=in1242mid_obit x y (in1242mid_oR 15) := by cases x <;> cases y <;> decide
  have h15 := required 15 (by decide) (by decide) b15
  have c15 : 1 ≤ sel 8 1 + sel 11 0 := by
    change h 8 15 = in1242mid_olow x y 8 ∨ h 11 15 = in1242mid_olow x y 11 at h15
    change 1 ≤ (if h 8 15 = in1242mid_olow x y 8 then 1 else 0) +
      (if h 11 15 = in1242mid_olow x y 11 then 1 else 0)
    rcases h15 with hh | hh <;> simp [hh]
  have p13 := part 13 (by decide)
  have p14 := part 14 (by decide)
  have p15 := part 15 (by decide)
  have p8 := part 8 (by decide)
  have p9 := part 9 (by decide)
  have p11 := part 11 (by decide)
  change sel 13 2 + sel 14 2 + sel 15 2 ≤ 1 ∧ sel 8 2 + sel 9 2 + sel 11 2 ≤ 1
  omega



set_option maxHeartbeats 4000000 in
theorem in1242_middle_public (x y : Bool) :
  let L : Fin 25 → Fin 18 := ![0,0,0,1,1,2,3,4,4,4,5,5,6,7,8,8,9,10,10,11,12,12,12,13,14]
  let R : Fin 25 → Fin 18 := ![1,2,3,2,14,3,15,5,6,7,6,9,7,8,9,11,10,11,16,13,13,15,17,14,15]
  let ends : Fin 25 → Sym2 (Fin 18) := fun e => s(L e,R e)
  let M : Finset (Fin 25) := {1,4,6,8,11,13,18,19,22}
  let T : Fin 18 → Fin 3 → Fin 25 :=
    ![![0,2,1],![0,3,4],![3,5,1],![2,5,6],![7,9,8],![7,10,11],![10,12,8],![9,12,13],![14,15,13],![14,16,11],![16,17,18],![15,17,19],![20,21,22],![20,23,19],![23,24,4],![21,24,6],![18,18,18],![22,22,22]]
  let bit : Fin 18 → Bool := ![true,false,true,false,true,false,true,false,false,false,x,false,y,false,false,false,x,y]
  let low : Fin 18 → Fin 6 := fun v => cycle_matching_low_color (!(bit v))
  ∀
    (h : Fin 18 → Fin 25 → Fin 6)
    (hhidden : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → h v e ≠ h v f)
    (hstrong : ∀ e, (L e).val < 16 → (R e).val < 16 → ∀ f g,
      L e ∈ ends f → R e ∈ ends g → f ≠ e → g ≠ e → h (L e) f ≠ h (R e) g)
    (hlow : ∀ v : Fin 18, v.val < 16 → ∃ j, h v (T v j) = low v),
    let m : Fin 18 → ℕ := fun v => if h v (T v 2) = low v then 1 else 0
    m 13 + m 14 + m 15 ≤ 1 ∧ m 8 + m 9 + m 11 ≤ 1 := by
  dsimp only
  intro h hhidden hstrong hlow
  exact in1242_open_middle_owner_bounds x y h hhidden hstrong hlow



set_option maxHeartbeats 4000000 in
theorem in1242_open_middle_full (x y : Bool)
    (c : Fin 25 → Fin 6) (h : Fin 18 → Fin 25 → Fin 6)
    (hcext : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ in1242mid_oends e → v ∈ in1242mid_oends f → e ≠ f → c e ≠ c f)
    (hhidden : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ in1242mid_oends e → v ∈ in1242mid_oends f → e ≠ f → h v e ≠ h v f)
    (havoid : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ in1242mid_oends e → v ∈ in1242mid_oends f → h v e ≠ c f)
    (hstrong : ∀ e, (in1242mid_oL e).val < 16 → (in1242mid_oR e).val < 16 → ∀ f g,
      in1242mid_oL e ∈ in1242mid_oends f → in1242mid_oR e ∈ in1242mid_oends g → f ≠ e → g ≠ e → h (in1242mid_oL e) f ≠ h (in1242mid_oR e) g)
    (hmatch : ∀ e ∈ in1242mid_oM, c e = if in1242mid_obit x y (in1242mid_oL e) then 1 else 0)
    (hfactor : ∀ e ∉ in1242mid_oM, 2 ≤ (c e).val)
    (hexact : ∀ e ∈ in1242mid_oM, e ≠ 18 → e ≠ 22 →
      ¬ (h (in1242mid_oL e) e = (if in1242mid_obit x y (in1242mid_oL e) then 0 else 1) ∧
          h (in1242mid_oR e) e = (if in1242mid_obit x y (in1242mid_oR e) then 0 else 1))) :
    let m : Fin 18 → ℕ := fun v => if h v (in1242mid_oT v 2) = in1242mid_olow x y v then 1 else 0
    m 13 + m 14 + m 15 ≤ 1 ∧ m 8 + m 9 + m 11 ≤ 1 := by
  classical
  have low_exists (v : Fin 18) (hv : v.val < 16) : ∃ j, h v (in1242mid_oT v j) = in1242mid_olow x y v := by
    have ht := in1242mid_otable v hv
    let z : Fin 3 → Fin 6 := fun j => h v (in1242mid_oT v j)
    have hz : Function.Injective z := by
      intro a b hab
      by_contra hn
      have hne : in1242mid_oT v a ≠ in1242mid_oT v b := fun he => hn (ht.2.1 he)
      exact (hhidden v hv (in1242mid_oT v a) (in1242mid_oT v b) (ht.1 a) (ht.1 b) hne) hab
    have hh : ∀ p, z p ≠ cycle_matching_low_color (in1242mid_obit x y v) ∧
        z p ≠ c (in1242mid_oT v 0) ∧ z p ≠ c (in1242mid_oT v 1) := by
      intro p
      have hm := hmatch (in1242mid_oT v 2) ht.2.2.1
      have hb := in1242mid_obits x y v hv
      rw [← hb] at hm
      refine ⟨?_,havoid v hv (in1242mid_oT v p) (in1242mid_oT v 0) (ht.1 p) (ht.1 0),
        havoid v hv (in1242mid_oT v p) (in1242mid_oT v 1) (ht.1 p) (ht.1 1)⟩
      have hav := havoid v hv (in1242mid_oT v p) (in1242mid_oT v 2) (ht.1 p) (ht.1 2)
      cases hbit : in1242mid_obit x y v <;> simp [z,cycle_matching_low_color,hbit] at hm ⊢ <;> simpa [hm] using hav
    have ha := hfactor (in1242mid_oT v 0) ht.2.2.2.1
    have hd := hfactor (in1242mid_oT v 1) ht.2.2.2.2
    have had := hcext v hv (in1242mid_oT v 0) (in1242mid_oT v 1) (ht.1 0) (ht.1 1)
      (fun he => (by decide : (0 : Fin 3) ≠ 1) (ht.2.1 he))
    obtain ⟨p,hp,_⟩ := op874_unused_low_color_has_unique_hidden_port (in1242mid_obit x y v)
      (c (in1242mid_oT v 0)) (c (in1242mid_oT v 1)) z ha hd had hz hh
    exact ⟨p,hp⟩
  exact in1242_open_middle_owner_bounds x y h hhidden hstrong low_exists

theorem op874_open_four_square_middle_matching_owner_bounds (x y : Bool) :
  let L : Fin 25 → Fin 18 := ![0,0,0,1,1,2,3,4,4,4,5,5,6,7,8,8,9,10,10,11,12,12,12,13,14]
  let R : Fin 25 → Fin 18 := ![1,2,3,2,14,3,15,5,6,7,6,9,7,8,9,11,10,11,16,13,13,15,17,14,15]
  let ends : Fin 25 → Sym2 (Fin 18) := fun e => s(L e,R e)
  let M : Finset (Fin 25) := {1,4,6,8,11,13,18,19,22}
  let T : Fin 18 → Fin 3 → Fin 25 :=
    ![![0,2,1],![0,3,4],![3,5,1],![2,5,6],![7,9,8],![7,10,11],![10,12,8],![9,12,13],![14,15,13],![14,16,11],![16,17,18],![15,17,19],![20,21,22],![20,23,19],![23,24,4],![21,24,6],![18,18,18],![22,22,22]]
  let bit : Fin 18 → Bool := ![true,false,true,false,true,false,true,false,false,false,x,false,y,false,false,false,x,y]
  let low : Fin 18 → Fin 6 := fun v => cycle_matching_low_color (!(bit v))
  ∀
    (c : Fin 25 → Fin 6) (h : Fin 18 → Fin 25 → Fin 6)
    (hcext : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → c e ≠ c f)
    (hhidden : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → h v e ≠ h v f)
    (havoid : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ ends e → v ∈ ends f → h v e ≠ c f)
    (hstrong : ∀ e, (L e).val < 16 → (R e).val < 16 → ∀ f g,
      L e ∈ ends f → R e ∈ ends g → f ≠ e → g ≠ e → h (L e) f ≠ h (R e) g)
    (hmatch : ∀ e ∈ M, c e = if bit (L e) then 1 else 0)
    (hfactor : ∀ e ∉ M, 2 ≤ (c e).val)
    (hexact : ∀ e ∈ M, e ≠ 18 → e ≠ 22 →
      ¬ (h (L e) e = (if bit (L e) then 0 else 1) ∧
          h (R e) e = (if bit (R e) then 0 else 1))),
    let m : Fin 18 → ℕ := fun v => if h v (T v 2) = low v then 1 else 0
    m 13 + m 14 + m 15 ≤ 1 ∧ m 8 + m 9 + m 11 ≤ 1 := by
  dsimp only
  intro c h hcext hhidden havoid hstrong hmatch hfactor hexact
  exact in1242_open_middle_full x y c h hcext hhidden havoid hstrong hmatch hfactor hexact
