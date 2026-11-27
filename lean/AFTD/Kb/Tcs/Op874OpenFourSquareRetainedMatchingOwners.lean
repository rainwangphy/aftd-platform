import AFTD.Prelude
import AFTD.Kb.Tcs.Op874UnusedLowColorHasUniqueHiddenPort
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.G

/-!
# op874_open_four_square_retained_matching_owners

Topic: graphs   Node: 46cdbd599493

Provenance: helper lemma. OP-874 opened four-square matching-port ownership transfer; experiment 41917.

For the displayed opened four-square block with arbitrary bits at its two opened matching ports, any local six-color assignment satisfying the displayed compatibility, palette, and retained-edge exact-ownership conditions assigns the unused low color to exactly one endpoint of each of the seven retained matching edges.
-/

private def oL : Fin 25 → Fin 18 := ![0,0,0,1,1,2,3,4,4,4,5,5,6,7,8,8,9,10,10,11,12,12,12,13,14]
private def oR : Fin 25 → Fin 18 := ![1,2,3,2,14,3,15,5,6,7,6,9,7,8,9,11,10,11,16,13,13,15,17,14,15]
private def oends (e : Fin 25) : Sym2 (Fin 18) := s(oL e,oR e)
private def oM : Finset (Fin 25) := {1,4,6,8,11,13,18,19,22}
private def oT : Fin 18 → Fin 3 → Fin 25 :=
    ![![0,2,1],![0,3,4],![3,5,1],![2,5,6],
      ![7,9,8],![7,10,11],![10,12,8],![9,12,13],
      ![14,15,13],![14,16,11],![16,17,18],![15,17,19],
      ![20,21,22],![20,23,19],![23,24,4],![21,24,6],
      ![18,18,18],![22,22,22]]
private def obit (x y : Bool) : Fin 18 → Bool :=
    ![true,false,true,false,true,false,true,false,false,false,x,false,y,false,false,false,x,y]
private def olow (x y : Bool) (v : Fin 18) : Fin 6 := cycle_matching_low_color (!(obit x y v))

set_option maxHeartbeats 4000000 in
private theorem otable : ∀ v : Fin 18, v.val < 16 →
    (∀ j, v ∈ oends (oT v j)) ∧ Function.Injective (oT v) ∧
    oT v 2 ∈ oM ∧ oT v 0 ∉ oM ∧ oT v 1 ∉ oM := by decide

set_option maxHeartbeats 4000000 in
private theorem obits (x y : Bool) : ∀ v : Fin 18, v.val < 16 →
    obit x y v = obit x y (oL (oT v 2)) := by
  cases x <;> cases y <;> decide

set_option maxHeartbeats 4000000 in
private theorem oedgefacts (x y : Bool) : ∀ e ∈ oM, e ≠ 18 → e ≠ 22 →
    (oL e).val < 16 ∧ (oR e).val < 16 ∧
    obit x y (oL e) = obit x y (oR e) ∧ oT (oL e) 2 = e ∧ oT (oR e) 2 = e := by
  cases x <;> cases y <;> decide

set_option maxHeartbeats 4000000 in
theorem in1242_open_block_owner_equations (x y : Bool)
    (c : Fin 25 → Fin 6) (h : Fin 18 → Fin 25 → Fin 6)
    (hcext : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ oends e → v ∈ oends f → e ≠ f → c e ≠ c f)
    (hhidden : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ oends e → v ∈ oends f → e ≠ f → h v e ≠ h v f)
    (havoid : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ oends e → v ∈ oends f → h v e ≠ c f)
    (hstrong : ∀ e, (oL e).val < 16 → (oR e).val < 16 → ∀ f g,
      oL e ∈ oends f → oR e ∈ oends g → f ≠ e → g ≠ e → h (oL e) f ≠ h (oR e) g)
    (hmatch : ∀ e ∈ oM, c e = if obit x y (oL e) then 1 else 0)
    (hfactor : ∀ e ∉ oM, 2 ≤ (c e).val)
    (hexact : ∀ e ∈ oM, e ≠ 18 → e ≠ 22 →
      ¬ (h (oL e) e = (if obit x y (oL e) then 0 else 1) ∧
          h (oR e) e = (if obit x y (oR e) then 0 else 1))) :
    let m : Fin 18 → ℕ := fun v => if h v (oT v 2) = olow x y v then 1 else 0
    ∀ e ∈ oM, e ≠ 18 → e ≠ 22 → m (oL e) + m (oR e) = 1 := by
  classical
  have olow_eq (v : Fin 18) : olow x y v = if obit x y v then 0 else 1 := by
    cases hbit : obit x y v <;> simp [olow,cycle_matching_low_color,hbit]
  have low_exists (v : Fin 18) (hv : v.val < 16) : ∃ j, h v (oT v j) = olow x y v := by
    have ht := otable v hv
    let z : Fin 3 → Fin 6 := fun j => h v (oT v j)
    have hz : Function.Injective z := by
      intro a b hab
      by_contra hn
      have hne : oT v a ≠ oT v b := fun he => hn (ht.2.1 he)
      exact (hhidden v hv (oT v a) (oT v b) (ht.1 a) (ht.1 b) hne) hab
    have hh : ∀ p, z p ≠ cycle_matching_low_color (obit x y v) ∧
        z p ≠ c (oT v 0) ∧ z p ≠ c (oT v 1) := by
      intro p
      have hm := hmatch (oT v 2) ht.2.2.1
      have hb := obits x y v hv
      rw [← hb] at hm
      refine ⟨?_,havoid v hv (oT v p) (oT v 0) (ht.1 p) (ht.1 0),
        havoid v hv (oT v p) (oT v 1) (ht.1 p) (ht.1 1)⟩
      have hav := havoid v hv (oT v p) (oT v 2) (ht.1 p) (ht.1 2)
      cases hbit : obit x y v <;> simp [z,cycle_matching_low_color,hbit] at hm ⊢ <;> simpa [hm] using hav
    have ha := hfactor (oT v 0) ht.2.2.2.1
    have hd := hfactor (oT v 1) ht.2.2.2.2
    have had := hcext v hv (oT v 0) (oT v 1) (ht.1 0) (ht.1 1)
      (fun he => (by decide : (0 : Fin 3) ≠ 1) (ht.2.1 he))
    obtain ⟨p,hp,_⟩ := op874_unused_low_color_has_unique_hidden_port (obit x y v)
      (c (oT v 0)) (c (oT v 1)) z ha hd had hz hh
    exact ⟨p,hp⟩
  have required (e : Fin 25) (hl : (oL e).val < 16) (hr : (oR e).val < 16)
      (hb : obit x y (oL e) = obit x y (oR e)) :
      h (oL e) e = olow x y (oL e) ∨ h (oR e) e = olow x y (oR e) := by
    by_contra hn
    push Not at hn
    obtain ⟨p,hp⟩ := low_exists (oL e) hl
    obtain ⟨q,hq⟩ := low_exists (oR e) hr
    have hpe : oT (oL e) p ≠ e := by intro he; rw [he] at hp; exact hn.1 hp
    have hqe : oT (oR e) q ≠ e := by intro he; rw [he] at hq; exact hn.2 hq
    have hlr : olow x y (oL e) = olow x y (oR e) := by simp [olow,hb]
    exact (hstrong e hl hr _ _ ((otable _ hl).1 p) ((otable _ hr).1 q) hpe hqe)
      (hp.trans (hlr.trans hq.symm))
  intro m e he h18 h22
  obtain ⟨hl,hr,hb,hsl,hsr⟩ := oedgefacts x y e he h18 h22
  have hreq := required e hl hr hb
  have hn : ¬ (h (oL e) e = olow x y (oL e) ∧ h (oR e) e = olow x y (oR e)) := by
    simpa [olow_eq] using hexact e he h18 h22
  dsimp only [m]
  rw [hsl,hsr]
  by_cases hu : h (oL e) e = olow x y (oL e)
  · have hv : h (oR e) e ≠ olow x y (oR e) := fun hh => hn ⟨hu,hh⟩
    simp [hu,hv]
  · have hv : h (oR e) e = olow x y (oR e) := hreq.resolve_left hu
    simp [hu,hv]

theorem op874_open_four_square_retained_matching_owners (x y : Bool) :
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
    ∀ e ∈ M, e ≠ 18 → e ≠ 22 → m (L e) + m (R e) = 1 := by
  dsimp only
  intro c h hcext hhidden havoid hstrong hmatch hfactor hexact
  exact in1242_open_block_owner_equations x y c h hcext hhidden havoid hstrong hmatch hfactor hexact
