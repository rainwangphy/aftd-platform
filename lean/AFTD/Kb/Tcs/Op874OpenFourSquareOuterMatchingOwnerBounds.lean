import AFTD.Prelude
import AFTD.Kb.Tcs.Op874AlternatingSquareMatchingOwnerBound
import AFTD.Kb.Tcs.Op874UnusedLowColorHasUniqueHiddenPort
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.CycleFactorHighColor
import AFTD.Kb.Tcs.G

/-!
# op874_open_four_square_outer_matching_owner_bounds

Topic: graphs   Node: f9d923471b0f

Provenance: helper lemma. OP-874 opened four-square global-pair ownership transfer; experiment 41917.

Both outer squares in the opened block have at most two matching owners when unselected factor edges use one global high pair.
-/

private def in1242outer_oL : Fin 25 → Fin 18 := ![0,0,0,1,1,2,3,4,4,4,5,5,6,7,8,8,9,10,10,11,12,12,12,13,14]
private def in1242outer_oR : Fin 25 → Fin 18 := ![1,2,3,2,14,3,15,5,6,7,6,9,7,8,9,11,10,11,16,13,13,15,17,14,15]
private def in1242outer_oends (e : Fin 25) : Sym2 (Fin 18) := s(in1242outer_oL e,in1242outer_oR e)
private def in1242outer_oM : Finset (Fin 25) := {1,4,6,8,11,13,18,19,22}
private def in1242outer_oT : Fin 18 → Fin 3 → Fin 25 :=
    ![![0,2,1],![0,3,4],![3,5,1],![2,5,6],
      ![7,9,8],![7,10,11],![10,12,8],![9,12,13],
      ![14,15,13],![14,16,11],![16,17,18],![15,17,19],
      ![20,21,22],![20,23,19],![23,24,4],![21,24,6],
      ![18,18,18],![22,22,22]]
private def in1242outer_obit (x y : Bool) : Fin 18 → Bool :=
    ![true,false,true,false,true,false,true,false,false,false,x,false,y,false,false,false,x,y]
private def in1242outer_olow (x y : Bool) (v : Fin 18) : Fin 6 := cycle_matching_low_color (!(in1242outer_obit x y v))

set_option maxHeartbeats 4000000 in
private theorem in1242outer_otable : ∀ v : Fin 18, v.val < 16 →
    (∀ j, v ∈ in1242outer_oends (in1242outer_oT v j)) ∧ Function.Injective (in1242outer_oT v) ∧
    in1242outer_oT v 2 ∈ in1242outer_oM ∧ in1242outer_oT v 0 ∉ in1242outer_oM ∧ in1242outer_oT v 1 ∉ in1242outer_oM := by decide

set_option maxHeartbeats 4000000 in
private theorem in1242outer_obits (x y : Bool) : ∀ v : Fin 18, v.val < 16 →
    in1242outer_obit x y v = in1242outer_obit x y (in1242outer_oL (in1242outer_oT v 2)) := by
  cases x <;> cases y <;> decide

set_option maxHeartbeats 4000000 in
private theorem in1242outer_oedgefacts (x y : Bool) : ∀ e ∈ in1242outer_oM, e ≠ 18 → e ≠ 22 →
    (in1242outer_oL e).val < 16 ∧ (in1242outer_oR e).val < 16 ∧
    in1242outer_obit x y (in1242outer_oL e) = in1242outer_obit x y (in1242outer_oR e) ∧ in1242outer_oT (in1242outer_oL e) 2 = e ∧ in1242outer_oT (in1242outer_oR e) 2 = e := by
  cases x <;> cases y <;> decide



private def in1242outer_ov : Fin 2 → Fin 4 → Fin 18 := ![![0,1,2,3],![4,5,6,7]]
private def in1242outer_oe : Fin 2 → Fin 4 → Fin 25 := ![![0,3,5,2],![7,10,12,9]]
private def in1242outer_op (k : Fin 2) (i : Fin 4) : Fin 3 → Fin 25 :=
  ![in1242outer_oe k (i-1),in1242outer_oe k i,in1242outer_oT (in1242outer_ov k i) 2]

set_option maxHeartbeats 4000000 in
private theorem in1242outer_square_facts : ∀ k i,
  (in1242outer_ov k i).val < 16 ∧ (∀ p, in1242outer_ov k i ∈ in1242outer_oends (in1242outer_op k i p)) ∧
  Function.Injective (in1242outer_op k i) ∧ in1242outer_oe k i ∉ in1242outer_oM ∧
  (in1242outer_op k i 0 ≠ in1242outer_oe k i ∧ in1242outer_op k i 2 ≠ in1242outer_oe k i) ∧
  (in1242outer_op k (i+1) 1 ≠ in1242outer_oe k i ∧ in1242outer_op k (i+1) 2 ≠ in1242outer_oe k i) ∧
  ((in1242outer_oL (in1242outer_oe k i)=in1242outer_ov k i ∧ in1242outer_oR (in1242outer_oe k i)=in1242outer_ov k (i+1)) ∨
   (in1242outer_oR (in1242outer_oe k i)=in1242outer_ov k i ∧ in1242outer_oL (in1242outer_oe k i)=in1242outer_ov k (i+1))) ∧
  (∀ q, ∃ p, in1242outer_op k i p = in1242outer_oT (in1242outer_ov k i) q) := by decide

set_option maxHeartbeats 4000000 in
theorem in1242outer_in1242_outer_block_bounds (x y : Bool)
    (c : Fin 25 → Fin 6) (h : Fin 18 → Fin 25 → Fin 6)
    (hcext : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ in1242outer_oends e → v ∈ in1242outer_oends f → e ≠ f → c e ≠ c f)
    (hhidden : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ in1242outer_oends e → v ∈ in1242outer_oends f → e ≠ f → h v e ≠ h v f)
    (havoid : ∀ v : Fin 18, v.val < 16 → ∀ e f, v ∈ in1242outer_oends e → v ∈ in1242outer_oends f → h v e ≠ c f)
    (hstrong : ∀ e, (in1242outer_oL e).val < 16 → (in1242outer_oR e).val < 16 → ∀ f g,
      in1242outer_oL e ∈ in1242outer_oends f → in1242outer_oR e ∈ in1242outer_oends g → f ≠ e → g ≠ e → h (in1242outer_oL e) f ≠ h (in1242outer_oR e) g)
    (hmatch : ∀ e ∈ in1242outer_oM, c e = if in1242outer_obit x y (in1242outer_oL e) then 1 else 0)
    (hfactor : ∀ e ∉ in1242outer_oM, 2 ≤ (c e).val)
    (hglobal : ∀ e ∉ in1242outer_oM, h (in1242outer_oL e) e ≠ in1242outer_olow x y (in1242outer_oL e) →
      h (in1242outer_oR e) e ≠ in1242outer_olow x y (in1242outer_oR e) → c e = 2 ∨ c e = 3)
    (howners : let m : Fin 18 → ℕ := fun v => if h v (in1242outer_oT v 2) = in1242outer_olow x y v then 1 else 0
      m 0 + m 2 = 1 ∧ m 4 + m 6 = 1) :
    let m : Fin 18 → ℕ := fun v => if h v (in1242outer_oT v 2) = in1242outer_olow x y v then 1 else 0
    m 0 + m 1 + m 2 + m 3 ≤ 2 ∧ m 4 + m 5 + m 6 + m 7 ≤ 2 := by
  classical
  have low_exists (v : Fin 18) (hv : v.val < 16) : ∃ j, h v (in1242outer_oT v j) = in1242outer_olow x y v := by
    have ht := in1242outer_otable v hv
    let z : Fin 3 → Fin 6 := fun j => h v (in1242outer_oT v j)
    have hz : Function.Injective z := by
      intro a b hab
      by_contra hn
      have hne : in1242outer_oT v a ≠ in1242outer_oT v b := fun he => hn (ht.2.1 he)
      exact (hhidden v hv (in1242outer_oT v a) (in1242outer_oT v b) (ht.1 a) (ht.1 b) hne) hab
    have hh : ∀ p, z p ≠ cycle_matching_low_color (in1242outer_obit x y v) ∧
        z p ≠ c (in1242outer_oT v 0) ∧ z p ≠ c (in1242outer_oT v 1) := by
      intro p
      have hm := hmatch (in1242outer_oT v 2) ht.2.2.1
      have hb := in1242outer_obits x y v hv
      rw [← hb] at hm
      refine ⟨?_,havoid v hv (in1242outer_oT v p) (in1242outer_oT v 0) (ht.1 p) (ht.1 0),
        havoid v hv (in1242outer_oT v p) (in1242outer_oT v 1) (ht.1 p) (ht.1 1)⟩
      have hav := havoid v hv (in1242outer_oT v p) (in1242outer_oT v 2) (ht.1 p) (ht.1 2)
      cases hbit : in1242outer_obit x y v <;> simp [z,cycle_matching_low_color,hbit] at hm ⊢ <;> simpa [hm] using hav
    have ha := hfactor (in1242outer_oT v 0) ht.2.2.2.1
    have hd := hfactor (in1242outer_oT v 1) ht.2.2.2.2
    have had := hcext v hv (in1242outer_oT v 0) (in1242outer_oT v 1) (ht.1 0) (ht.1 1)
      (fun he => (by decide : (0 : Fin 3) ≠ 1) (ht.2.1 he))
    obtain ⟨p,hp,_⟩ := op874_unused_low_color_has_unique_hidden_port (in1242outer_obit x y v)
      (c (in1242outer_oT v 0)) (c (in1242outer_oT v 1)) z ha hd had hz hh
    exact ⟨p,hp⟩
  have bound (k : Fin 2) :
      (if h (in1242outer_ov k 0) (in1242outer_oT (in1242outer_ov k 0) 2) = in1242outer_olow x y (in1242outer_ov k 0) then 1 else 0 : ℕ) +
      (if h (in1242outer_ov k 1) (in1242outer_oT (in1242outer_ov k 1) 2) = in1242outer_olow x y (in1242outer_ov k 1) then 1 else 0) +
      (if h (in1242outer_ov k 2) (in1242outer_oT (in1242outer_ov k 2) 2) = in1242outer_olow x y (in1242outer_ov k 2) then 1 else 0) +
      (if h (in1242outer_ov k 3) (in1242outer_oT (in1242outer_ov k 3) 2) = in1242outer_olow x y (in1242outer_ov k 3) then 1 else 0) ≤ 2 := by
    let b : Fin 4 → Bool := fun i => in1242outer_obit x y (in1242outer_ov k i)
    let e : Fin 4 → Fin 4 := fun i => ⟨(c (in1242outer_oe k i)).val - 2, by
      have hf := hfactor (in1242outer_oe k i) (in1242outer_square_facts k i).2.2.2.1
      have hc := (c (in1242outer_oe k i)).isLt
      omega⟩
    let z : Fin 4 → Fin 3 → Fin 6 := fun i p => h (in1242outer_ov k i) (in1242outer_op k i p)
    have ceq (i : Fin 4) : cycle_factor_high_color (e i) = c (in1242outer_oe k i) := by
      apply Fin.ext
      have hf := hfactor (in1242outer_oe k i) (in1242outer_square_facts k i).2.2.2.1
      dsimp [cycle_factor_high_color,e]
      omega
    have zinj (i : Fin 4) : Function.Injective (z i) := by
      intro p q he
      by_contra hpq
      have hf := in1242outer_square_facts k i
      exact hhidden (in1242outer_ov k i) hf.1 (in1242outer_op k i p) (in1242outer_op k i q)
        (hf.2.1 p) (hf.2.1 q) (fun hh => hpq (hf.2.2.1 hh)) he
    have properly : ∀ i, e (i-1) ≠ e i := by
      intro i he
      have hf := in1242outer_square_facts k i
      have hh := hcext (in1242outer_ov k i) hf.1 (in1242outer_op k i 0) (in1242outer_op k i 1)
        (hf.2.1 0) (hf.2.1 1) (fun h => (by decide : (0 : Fin 3) ≠ 1) (hf.2.2.1 h))
      apply hh
      change c (in1242outer_oe k (i-1)) = c (in1242outer_oe k i)
      rw [← ceq (i-1), ← ceq i, he]
    have avoids : ∀ i p, z i p ≠ cycle_matching_low_color (b i) ∧
        z i p ≠ cycle_factor_high_color (e (i-1)) ∧ z i p ≠ cycle_factor_high_color (e i) := by
      intro i p
      have hf := in1242outer_square_facts k i
      have ht := in1242outer_otable (in1242outer_ov k i) hf.1
      have hm := hmatch (in1242outer_oT (in1242outer_ov k i) 2) ht.2.2.1
      have hb := in1242outer_obits x y (in1242outer_ov k i) hf.1
      rw [← hb] at hm
      have hl := havoid (in1242outer_ov k i) hf.1 (in1242outer_op k i p) (in1242outer_oT (in1242outer_ov k i) 2)
        (hf.2.1 p) (ht.1 2)
      refine ⟨?_,?_,?_⟩
      · cases hbit : in1242outer_obit x y (in1242outer_ov k i) <;> simp [z,b,cycle_matching_low_color,hbit] at hm ⊢ <;> simpa [hm] using hl
      · rw [ceq]
        exact havoid (in1242outer_ov k i) hf.1 (in1242outer_op k i p) (in1242outer_op k i 0) (hf.2.1 p) (hf.2.1 0)
      · rw [ceq]
        exact havoid (in1242outer_ov k i) hf.1 (in1242outer_op k i p) (in1242outer_op k i 1) (hf.2.1 p) (hf.2.1 1)
    have strong : ∀ i, z i 0 ≠ z (i+1) 1 ∧ z i 0 ≠ z (i+1) 2 ∧
        z i 2 ≠ z (i+1) 1 ∧ z i 2 ≠ z (i+1) 2 := by
      intro i
      have hf := in1242outer_square_facts k i
      have hg := in1242outer_square_facts k (i+1)
      have hs (p q : Fin 3) (hp : in1242outer_op k i p ≠ in1242outer_oe k i)
          (hq : in1242outer_op k (i+1) q ≠ in1242outer_oe k i) : z i p ≠ z (i+1) q := by
        rcases hf.2.2.2.2.2.2.1 with ⟨hl,hr⟩ | ⟨hr,hl⟩
        · have hh := hstrong (in1242outer_oe k i) (by rw [hl]; exact hf.1) (by rw [hr]; exact hg.1)
            (in1242outer_op k i p) (in1242outer_op k (i+1) q) (by rw [hl]; exact hf.2.1 p)
            (by rw [hr]; exact hg.2.1 q) hp hq
          simpa [z,hl,hr] using hh
        · have hh := hstrong (in1242outer_oe k i) (by rw [hl]; exact hg.1) (by rw [hr]; exact hf.1)
            (in1242outer_op k (i+1) q) (in1242outer_op k i p) (by rw [hl]; exact hg.2.1 q)
            (by rw [hr]; exact hf.2.1 p) hq hp
          have hrev : z (i+1) q ≠ z i p := by simpa [z,hl,hr] using hh
          exact hrev.symm
      exact ⟨hs 0 1 hf.2.2.2.2.1.1 hf.2.2.2.2.2.1.1,
        hs 0 2 hf.2.2.2.2.1.1 hf.2.2.2.2.2.1.2,
        hs 2 1 hf.2.2.2.2.1.2 hf.2.2.2.2.2.1.1,
        hs 2 2 hf.2.2.2.2.1.2 hf.2.2.2.2.2.1.2⟩
    have part (i : Fin 4) :
        (if z i 0 = cycle_matching_low_color (!b i) then 1 else 0 : ℕ) +
        (if z i 1 = cycle_matching_low_color (!b i) then 1 else 0) +
        (if z i 2 = cycle_matching_low_color (!b i) then 1 else 0) = 1 := by
      obtain ⟨q,hq⟩ := low_exists (in1242outer_ov k i) (in1242outer_square_facts k i).1
      obtain ⟨p,hp⟩ := (in1242outer_square_facts k i).2.2.2.2.2.2.2 q
      have hpz : z i p = cycle_matching_low_color (!b i) := by simpa [z,b,in1242outer_olow,hp] using hq
      have uniq (a d : Fin 3) (ha : z i a = cycle_matching_low_color (!b i))
          (hd : z i d = cycle_matching_low_color (!b i)) : a=d := zinj i (ha.trans hd.symm)
      fin_cases p
      · change z i 0 = cycle_matching_low_color (!b i) at hpz
        have h1 : z i 1 ≠ cycle_matching_low_color (!b i) := fun hh => (by decide : (0 : Fin 3) ≠ 1) (uniq 0 1 hpz hh)
        have h2 : z i 2 ≠ cycle_matching_low_color (!b i) := fun hh => (by decide : (0 : Fin 3) ≠ 2) (uniq 0 2 hpz hh)
        simp [hpz,h1,h2]
      · change z i 1 = cycle_matching_low_color (!b i) at hpz
        have h0 : z i 0 ≠ cycle_matching_low_color (!b i) := fun hh => (by decide : (1 : Fin 3) ≠ 0) (uniq 1 0 hpz hh)
        have h2 : z i 2 ≠ cycle_matching_low_color (!b i) := fun hh => (by decide : (1 : Fin 3) ≠ 2) (uniq 1 2 hpz hh)
        simp [hpz,h0,h2]
      · change z i 2 = cycle_matching_low_color (!b i) at hpz
        have h0 : z i 0 ≠ cycle_matching_low_color (!b i) := fun hh => (by decide : (2 : Fin 3) ≠ 0) (uniq 2 0 hpz hh)
        have h1 : z i 1 ≠ cycle_matching_low_color (!b i) := fun hh => (by decide : (2 : Fin 3) ≠ 1) (uniq 2 1 hpz hh)
        simp [hpz,h0,h1]
    have chord : (if z 0 2 = cycle_matching_low_color (!b 0) then 1 else 0 : ℕ) +
        (if z 2 2 = cycle_matching_low_color (!b 2) then 1 else 0) = 1 := by
      fin_cases k
      · exact howners.1
      · exact howners.2
    have global : ∀ i, z i 1 ≠ cycle_matching_low_color (!b i) →
        z (i+1) 0 ≠ cycle_matching_low_color (!b (i+1)) → e i = 0 ∨ e i = 1 := by
      intro i ha hb
      have hf := in1242outer_square_facts k i
      have pred : (i+1)-1=i := by fin_cases i <;> decide
      have ha' : h (in1242outer_ov k i) (in1242outer_oe k i) ≠ in1242outer_olow x y (in1242outer_ov k i) := ha
      have hb' : h (in1242outer_ov k (i+1)) (in1242outer_oe k i) ≠ in1242outer_olow x y (in1242outer_ov k (i+1)) := by
        simpa [z,b,in1242outer_op,in1242outer_olow,pred] using hb
      have hc : c (in1242outer_oe k i)=2 ∨ c (in1242outer_oe k i)=3 := by
        rcases hf.2.2.2.2.2.2.1 with ⟨hl,hr⟩ | ⟨hr,hl⟩
        · exact hglobal (in1242outer_oe k i) hf.2.2.2.1 (by simpa [hl] using ha') (by simpa [hr] using hb')
        · exact hglobal (in1242outer_oe k i) hf.2.2.2.1 (by simpa [hl] using hb') (by simpa [hr] using ha')
      rcases hc with hc | hc
      · left; apply Fin.ext; have hv := congrArg Fin.val hc; dsimp [e]; simp at hv; omega
      · right; apply Fin.ext; have hv := congrArg Fin.val hc; dsimp [e]; simp at hv; omega
    have hh := op874_alternating_square_matching_owner_bound b e z properly zinj avoids strong part chord global
    change (if h (in1242outer_ov k 0) (in1242outer_oT (in1242outer_ov k 0) 2) = in1242outer_olow x y (in1242outer_ov k 0) then 1 else 0 : ℕ) +
      (if h (in1242outer_ov k 1) (in1242outer_oT (in1242outer_ov k 1) 2) = in1242outer_olow x y (in1242outer_ov k 1) then 1 else 0) +
      (if h (in1242outer_ov k 2) (in1242outer_oT (in1242outer_ov k 2) 2) = in1242outer_olow x y (in1242outer_ov k 2) then 1 else 0) +
      (if h (in1242outer_ov k 3) (in1242outer_oT (in1242outer_ov k 3) 2) = in1242outer_olow x y (in1242outer_ov k 3) then 1 else 0) ≤ 2 at hh
    exact hh
  have h0 := bound 0
  have h1 := bound 1
  exact ⟨h0,h1⟩

theorem op874_open_four_square_outer_matching_owner_bounds (x y : Bool) :
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
    (hglobal : ∀ e ∉ M, h (L e) e ≠ low (L e) →
      h (R e) e ≠ low (R e) → c e = 2 ∨ c e = 3)
    (howners : let m : Fin 18 → ℕ := fun v => if h v (T v 2) = low v then 1 else 0
      m 0 + m 2 = 1 ∧ m 4 + m 6 = 1),
    let m : Fin 18 → ℕ := fun v => if h v (T v 2) = low v then 1 else 0
    m 0 + m 1 + m 2 + m 3 ≤ 2 ∧ m 4 + m 5 + m 6 + m 7 ≤ 2 := by
  dsimp only
  intro c h hcext hhidden havoid hstrong hmatch hfactor hglobal howners
  exact in1242outer_in1242_outer_block_bounds x y c h hcext hhidden havoid hstrong hmatch hfactor hglobal howners
