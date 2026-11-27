import AFTD.Prelude
import AFTD.Kb.Tcs.Bit
import AFTD.Kb.Tcs.F

/-!
# op874_four_matchings_window_cube_c01

Topic: graphs   Node: f80af80909db

Provenance: helper lemma. OP-874 campaign: one cube of the SAT refutation behind op874_four_matchings_no_common_window_factor_word (experiment 43341)

For the four displayed saturated matchings of the 8- and 12-cycle factor with the displayed bit assignment, there is no high factor-coloring f with compatible exact-owner local states for all four matchings and both forced four-window requirements in which additionally f(10) = 0, f(11) = 1, f(12) = 0, f(13) = 1.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

namespace IN1204

def L : Fin 4 → Fin 30 → Fin 20 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,5,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,5,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,6,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,6,9,10,12,14,16]]
def R : Fin 4 → Fin 30 → Fin 20 := ![![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,6,8,7,11,15,13,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,6,11,7,8,13,15,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,8,5,7,11,15,13,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,11,5,7,8,15,13,18,17,19]]
def inc : Fin 4 → Fin 20 → Fin 3 → Fin 30 := ![![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,24],![5,6,21],![6,7,23],![8,19,22],![8,9,25],![9,10,26],![10,11,24],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,24],![5,6,21],![6,7,23],![8,19,24],![8,9,25],![9,10,26],![10,11,22],![11,12,27],![12,13,25],![13,14,28],![14,15,26],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,22],![5,6,24],![6,7,23],![8,19,21],![8,9,25],![9,10,26],![10,11,24],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,22],![5,6,24],![6,7,23],![8,19,24],![8,9,25],![9,10,26],![10,11,21],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,28],![17,18,27],![18,19,29]]]
def bit : Fin 20 → Bool := ![true,false,false,true,true,false,false,true,false,false,false,false,true,false,true,false,true,true,true,true]
def W1 : Fin 6 → Fin 20 := ![10,11,12,13,14,15]
def W2 : Fin 6 → Fin 20 := ![11,12,13,14,15,16]

def color (f : Fin 20 → Fin 4) : Fin 4 → Fin 30 → Fin 6 := fun q e =>
  if he : e.val < 20 then ⟨(f ⟨e.val, he⟩).val + 2, by omega⟩
  else if bit (L q e) then 1 else 0

def P (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) : Prop :=
  (∀ q : Fin 4, ∀ v : Fin 20, ∀ i j : Fin 3,
    i ≠ j → color f q (inc q v i) ≠ color f q (inc q v j) ∧ h q v (inc q v i) ≠ h q v (inc q v j)) ∧
  (∀ q : Fin 4, ∀ v : Fin 20, ∀ i j : Fin 3, h q v (inc q v i) ≠ color f q (inc q v j)) ∧
  (∀ q : Fin 4, ∀ e : Fin 30, ∀ i j : Fin 3,
    inc q (L q e) i ≠ e → inc q (R q e) j ≠ e →
    h q (L q e) (inc q (L q e) i) ≠ h q (R q e) (inc q (R q e) j)) ∧
  (∀ q : Fin 4, ∀ e : Fin 30, 20 ≤ e.val →
    ¬ (h q (L q e) e = (if bit (L q e) then 0 else 1) ∧
       h q (R q e) e = (if bit (R q e) then 0 else 1))) ∧
  (∀ k : Fin 4, ∃ j : Fin 6, f (W1 j) = k) ∧
  (∀ k : Fin 4, ∃ j : Fin 6, f (W2 j) = k)

def Fa (e : Fin 20) (c : Fin 4) : ℕ := 1 + 4 * e.val + c.val
def Ha (q : Fin 4) (v : Fin 20) (i : Fin 3) (x : Fin 6) : ℕ :=
  81 + 360 * q.val + 18 * v.val + 6 * i.val + x.val

def val (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) : Sat.Valuation := fun n =>
  (∃ e c, n = Fa e c ∧ f e = c) ∨ (∃ q v i x, n = Ha q v i x ∧ h q v (inc q v i) = x)

section
variable (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6)

theorem valF (e : Fin 20) (c : Fin 4) : val f h (Fa e c) ↔ f e = c := by
  constructor
  · rintro (⟨e', c', h0, hw⟩ | ⟨q, v, i, x, h0, -⟩)
    · unfold Fa at h0
      have h1 : e = e' := Fin.ext (by omega)
      have h2 : c = c' := Fin.ext (by omega)
      rw [h1, h2]; exact hw
    · unfold Fa Ha at h0; omega
  · intro hw; exact Or.inl ⟨e, c, rfl, hw⟩

theorem valH (q : Fin 4) (v : Fin 20) (i : Fin 3) (x : Fin 6) :
    val f h (Ha q v i x) ↔ h q v (inc q v i) = x := by
  constructor
  · rintro (⟨e', c', h0, -⟩ | ⟨q', v', i', x', h0, hh⟩)
    · unfold Fa Ha at h0; omega
    · unfold Ha at h0
      have h1 : q = q' := Fin.ext (by omega)
      have h2 : v = v' := Fin.ext (by omega)
      have h3 : i = i' := Fin.ext (by omega)
      have h4 : x = x' := Fin.ext (by omega)
      rw [h1, h2, h3, h4]; exact hh
  · intro hh; exact Or.inr ⟨q, v, i, x, rfl, hh⟩

end

theorem sat_of (v : Sat.Valuation) (c : Sat.Clause)
    (h : (∀ l, List.Mem l c → v.neg l) → False) : v.satisfies c := by
  change List Sat.Literal at c
  induction c with
  | nil => exact h (fun l hl => by cases hl)
  | cons a as ih =>
    intro ha
    exact ih (fun hall => h (fun l hl => by
      cases hl with
      | head => exact ha
      | tail _ hl => exact hall l hl))

theorem neg_of_sat (v : Sat.Valuation) (c : Sat.Clause) (hs : v.satisfies c) :
    (∀ l, List.Mem l c → v.neg l) → False := by
  change List Sat.Literal at c
  induction c with
  | nil => intro _; exact hs
  | cons a as ih =>
    intro hall
    exact ih (hs (hall a (List.Mem.head _))) (fun l hl => hall l (List.Mem.tail _ hl))

theorem sat_reverse (v : Sat.Valuation) (c : List Sat.Literal) (hs : v.satisfies c.reverse) :
    v.satisfies c :=
  sat_of v c (fun hall => neg_of_sat v _ hs (fun l hl => hall l (List.mem_reverse.mp hl)))

def c2 (c : Fin 4) : Fin 6 := ⟨c.val + 2, by omega⟩
def e20 (e : Fin 30) : Fin 20 := ⟨e.val % 20, Nat.mod_lt _ (by norm_num)⟩
def e30 (e : Fin 20) : Fin 30 := ⟨e.val, by omega⟩
def mcol (q : Fin 4) (e : Fin 30) : Fin 6 := if bit (L q e) then 1 else 0
def opp (v : Fin 20) : Fin 6 := if bit v then 0 else 1

inductive Tag
  | A (e : Fin 20)
  | B (e : Fin 20) (c1 c2 : Fin 4)
  | C (q : Fin 4) (v : Fin 20) (i : Fin 3)
  | D (q : Fin 4) (v : Fin 20) (i : Fin 3) (x1 x2 : Fin 6)
  | E (q : Fin 4) (v : Fin 20) (i j : Fin 3) (c : Fin 4)
  | F (q : Fin 4) (v : Fin 20) (i j : Fin 3) (x : Fin 6)
  | G (q : Fin 4) (v : Fin 20) (i j : Fin 3) (c : Fin 4)
  | G' (q : Fin 4) (v : Fin 20) (i j : Fin 3)
  | H (q : Fin 4) (e : Fin 30) (i j : Fin 3) (x : Fin 6)
  | I (q : Fin 4) (e : Fin 30) (i j : Fin 3)
  | J1 (k : Fin 4)
  | J2 (k : Fin 4)

open Sat in
def gen : Tag → List Literal
  | .A e => (List.finRange 4).map fun c => .pos (Fa e c)
  | .B e c1 c2 => [.neg (Fa e c1), .neg (Fa e c2)]
  | .C q v i => (List.finRange 6).map fun x => .pos (Ha q v i x)
  | .D q v i x1 x2 => [.neg (Ha q v i x1), .neg (Ha q v i x2)]
  | .E q v i j c => [.neg (Fa (e20 (inc q v i)) c), .neg (Fa (e20 (inc q v j)) c)]
  | .F q v i j x => [.neg (Ha q v i x), .neg (Ha q v j x)]
  | .G q v i j c => [.neg (Ha q v i (c2 c)), .neg (Fa (e20 (inc q v j)) c)]
  | .G' q v i j => [.neg (Ha q v i (mcol q (inc q v j)))]
  | .H q e i j x => [.neg (Ha q (L q e) i x), .neg (Ha q (R q e) j x)]
  | .I q e i j => [.neg (Ha q (L q e) i (opp (L q e))), .neg (Ha q (R q e) j (opp (R q e)))]
  | .J1 k => (List.finRange 6).map fun j => .pos (Fa (W1 j) k)
  | .J2 k => (List.finRange 6).map fun j => .pos (Fa (W2 j) k)

def cond : Tag → Bool
  | .B _ c1 c2 => decide (c1 ≠ c2)
  | .D _ _ _ x1 x2 => decide (x1 ≠ x2)
  | .E q v i j _ => decide (i ≠ j ∧ (inc q v i).val < 20 ∧ (inc q v j).val < 20)
  | .F _ _ i j _ => decide (i ≠ j)
  | .G q v _ j _ => decide ((inc q v j).val < 20)
  | .G' q v _ j => decide (¬ (inc q v j).val < 20)
  | .H q e i j _ => decide (inc q (L q e) i ≠ e ∧ inc q (R q e) j ≠ e)
  | .I q e i j => decide (20 ≤ e.val ∧ inc q (L q e) i = e ∧ inc q (R q e) j = e)
  | _ => true

theorem color_lt (f : Fin 20 → Fin 4) (q : Fin 4) (e : Fin 30) (he : e.val < 20) :
    color f q e = c2 (f (e20 e)) := by
  unfold color c2 e20
  rw [dif_pos he]
  have : (⟨e.val, he⟩ : Fin 20) = ⟨e.val % 20, Nat.mod_lt _ (by norm_num)⟩ :=
    Fin.ext (Nat.mod_eq_of_lt he).symm
  exact Fin.ext (by simp only [this])

theorem color_ge (f : Fin 20 → Fin 4) (q : Fin 4) (e : Fin 30) (he : ¬ e.val < 20) :
    color f q e = mcol q e := by
  unfold color mcol
  rw [dif_neg he]

theorem c2_inj {a b : Fin 4} (h : c2 a = c2 b) : a = b := by
  unfold c2 at h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem gen_sound (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) (hP : P f h)
    (t : Tag) (ht : cond t = true) : (val f h).satisfies (gen t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  have vF := valF f h
  have vH := valH f h
  apply sat_of
  intro hall
  have hn : ∀ n, List.Mem (Sat.Literal.neg n) (gen t) → val f h n := fun n hm => hall _ hm
  have hp : ∀ n, List.Mem (Sat.Literal.pos n) (gen t) → ¬ val f h n := fun n hm => hall _ hm
  have n1 : ∀ a b, gen t = [Sat.Literal.neg a, Sat.Literal.neg b] → val f h a := by
    intro a b e; exact hn a (by rw [e]; exact List.Mem.head _)
  have n2 : ∀ a b, gen t = [Sat.Literal.neg a, Sat.Literal.neg b] → val f h b := by
    intro a b e; exact hn b (by rw [e]; exact List.Mem.tail _ (List.Mem.head _))
  cases t with
  | A e => exact hp _ (List.mem_map.2 ⟨f e, List.mem_finRange _, rfl⟩) ((vF _ _).2 rfl)
  | B e a b =>
    have ea := (vF _ _).1 (n1 _ _ rfl)
    have eb := (vF _ _).1 (n2 _ _ rfl)
    simp only [cond, decide_eq_true_eq] at ht
    exact ht (ea.symm.trans eb)
  | C q v i => exact hp _ (List.mem_map.2 ⟨_, List.mem_finRange _, rfl⟩) ((vH _ _ _ _).2 rfl)
  | D q v i a b =>
    have ea := (vH _ _ _ _).1 (n1 _ _ rfl)
    have eb := (vH _ _ _ _).1 (n2 _ _ rfl)
    simp only [cond, decide_eq_true_eq] at ht
    exact ht (ea.symm.trans eb)
  | E q v i j c =>
    have ea := (vF _ _).1 (n1 _ _ rfl)
    have eb := (vF _ _).1 (n2 _ _ rfl)
    simp only [cond, decide_eq_true_eq] at ht
    obtain ⟨hij, hi, hj⟩ := ht
    apply (h1 q v i j hij).1
    rw [color_lt f q _ hi, color_lt f q _ hj, ea, eb]
  | F q v i j x =>
    have ea := (vH _ _ _ _).1 (n1 _ _ rfl)
    have eb := (vH _ _ _ _).1 (n2 _ _ rfl)
    simp only [cond, decide_eq_true_eq] at ht
    exact (h1 q v i j ht).2 (ea.trans eb.symm)
  | G q v i j c =>
    have ea := (vH _ _ _ _).1 (n1 _ _ rfl)
    have eb := (vF _ _).1 (n2 _ _ rfl)
    simp only [cond, decide_eq_true_eq] at ht
    apply h2 q v i j
    rw [color_lt f q _ ht, ea, eb]
  | G' q v i j =>
    have ea := (vH _ _ _ _).1 (hn _ (List.Mem.head _))
    simp only [cond, decide_eq_true_eq] at ht
    apply h2 q v i j
    rw [color_ge f q _ ht, ea]
  | H q e i j x =>
    have ea := (vH _ _ _ _).1 (n1 _ _ rfl)
    have eb := (vH _ _ _ _).1 (n2 _ _ rfl)
    simp only [cond, decide_eq_true_eq] at ht
    exact h3 q e i j ht.1 ht.2 (ea.trans eb.symm)
  | I q e i j =>
    have ea := (vH _ _ _ _).1 (n1 _ _ rfl)
    have eb := (vH _ _ _ _).1 (n2 _ _ rfl)
    simp only [cond, decide_eq_true_eq] at ht
    obtain ⟨hge, hi, hj⟩ := ht
    rw [hi] at ea
    rw [hj] at eb
    exact h4 q e hge ⟨ea, eb⟩
  | J1 k =>
    obtain ⟨j, hj⟩ := h5 k
    exact hp _ (List.mem_map.2 ⟨j, List.mem_finRange _, rfl⟩) ((vF _ _).2 hj)
  | J2 k =>
    obtain ⟨j, hj⟩ := h6 k
    exact hp _ (List.mem_map.2 ⟨j, List.mem_finRange _, rfl⟩) ((vF _ _).2 hj)

def lb : Sat.Literal → Sat.Literal → Bool
  | .pos a, .pos b => a == b
  | .neg a, .neg b => a == b
  | _, _ => false

def cb : List Sat.Literal → List Sat.Literal → Bool
  | [], [] => true
  | a :: as, b :: bs => lb a b && cb as bs
  | _, _ => false

theorem lb_eq : ∀ a b : Sat.Literal, lb a b = true → a = b
  | .pos a, .pos b, h => by simp only [lb, beq_iff_eq] at h; rw [h]
  | .neg a, .neg b, h => by simp only [lb, beq_iff_eq] at h; rw [h]
  | .pos _, .neg _, h => by simp [lb] at h
  | .neg _, .pos _, h => by simp [lb] at h

theorem cb_eq : ∀ a b : List Sat.Literal, cb a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [cb, Bool.and_eq_true] at h
    rw [lb_eq a b h.1, cb_eq as bs h.2]
  | [], _ :: _, h => by simp [cb] at h
  | _ :: _, [], h => by simp [cb] at h

def atom : Sat.Literal → ℕ
  | .pos n => n
  | .neg n => n

def fe (n : ℕ) : Fin 20 := ⟨(n - 1) / 4 % 20, Nat.mod_lt _ (by norm_num)⟩
def fc (n : ℕ) : Fin 4 := ⟨(n - 1) % 4, Nat.mod_lt _ (by norm_num)⟩
def hq (n : ℕ) : Fin 4 := ⟨(n - 81) / 360 % 4, Nat.mod_lt _ (by norm_num)⟩
def hv (n : ℕ) : Fin 20 := ⟨(n - 81) / 18 % 20, Nat.mod_lt _ (by norm_num)⟩
def hi (n : ℕ) : Fin 3 := ⟨(n - 81) / 6 % 3, Nat.mod_lt _ (by norm_num)⟩
def hx (n : ℕ) : Fin 6 := ⟨(n - 81) % 6, Nat.mod_lt _ (by norm_num)⟩

def cands2 (a b : ℕ) : List Tag :=
  if a ≤ 80 then
    if b ≤ 80 then
      Tag.B (fe a) (fc a) (fc b) ::
        ([L 0 (e30 (fe a)), R 0 (e30 (fe a))].flatMap fun v => (List.finRange 3).flatMap fun i =>
          (List.finRange 3).map fun j => Tag.E 0 v i j (fc a))
    else []
  else if b ≤ 80 then (List.finRange 3).map fun j => Tag.G (hq a) (hv a) (hi a) j (fc b)
  else Tag.D (hq a) (hv a) (hi a) (hx a) (hx b) :: Tag.F (hq a) (hv a) (hi a) (hi b) (hx a) ::
    (((List.finRange 30).filter fun e => L (hq a) e == hv a && R (hq a) e == hv b).flatMap fun e =>
      [Tag.H (hq a) e (hi a) (hi b) (hx a), Tag.I (hq a) e (hi a) (hi b)])

def cands : List Sat.Literal → List Tag
  | [l] => (List.finRange 3).map fun j => Tag.G' (hq (atom l)) (hv (atom l)) (hi (atom l)) j
  | [l1, l2] => cands2 (atom l1) (atom l2)
  | [l, _, _, _] => [Tag.A (fe (atom l))]
  | [l, _, _, _, _, _] =>
      if atom l ≤ 80 then [Tag.J1 (fc (atom l)), Tag.J2 (fc (atom l))]
      else [Tag.C (hq (atom l)) (hv (atom l)) (hi (atom l))]
  | _ => []

def chkT (c : List Sat.Literal) : Bool := (cands c).any fun t => cond t && cb c (gen t)

def chk (cube : List Sat.Literal) (c : List Sat.Literal) : Bool :=
  cube.any (fun l => cb c [l]) || chkT c || chkT c.reverse

theorem chkT_sound (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) (hP : P f h)
    (c : List Sat.Literal) (hc : chkT c = true) : (val f h).satisfies c := by
  unfold chkT at hc
  obtain ⟨t, -, ht⟩ := List.any_eq_true.mp hc
  simp only [Bool.and_eq_true] at ht
  rw [cb_eq _ _ ht.2]
  exact gen_sound f h hP t ht.1

theorem fmla_sound (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) (hP : P f h)
    (cube : List Sat.Literal) (hcube : ∀ l ∈ cube, (val f h).satisfies [l])
    (fm : Sat.Fmla) (hf : fm.all (chk cube) = true) : (val f h).satisfies_fmla fm :=
  ⟨fun c hc => by
    have hc' := List.all_eq_true.mp hf c hc
    unfold chk at hc'
    simp only [Bool.or_eq_true] at hc'
    rcases hc' with (hc' | hc') | hc'
    · obtain ⟨l, hl, e⟩ := List.any_eq_true.mp hc'
      rw [cb_eq _ _ e]; exact hcube l hl
    · exact chkT_sound f h hP c hc'
    · exact sat_reverse _ _ (chkT_sound f h hP _ hc')⟩

theorem sat_pos (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) (e : Fin 20) (c : Fin 4)
    (hw : f e = c) : (val f h).satisfies [Sat.Literal.pos (Fa e c)] :=
  sat_of _ _ (fun hall => hall _ (List.Mem.head _) ((valF f h e c).2 hw))

theorem sat_neg (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6) (e : Fin 20) (c : Fin 4)
    (hw : f e ≠ c) : (val f h).satisfies [Sat.Literal.neg (Fa e c)] :=
  sat_of _ _ (fun hall => hw ((valF f h e c).1 (hall _ (List.Mem.head _))))

open Lean Elab Command in
elab "in1204_lrat_core " nm:ident ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  Command.liftTermElabM do
    let cnf ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) lrat
    let (_,ctx,_,proof) ← Mathlib.Tactic.Sat.fromLRATAux cnf lrat nm.getId
    addDecl <| Declaration.defnDecl {
      name := nm.getId ++ `formula, levelParams := [], type := mkConst ``Sat.Fmla, value := ctx,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
    addDecl <| Declaration.thmDecl {
      name := nm.getId ++ `sat_proof, levelParams := [], type := ← Meta.inferType proof, value := proof }

end IN1204

in1204_lrat_core IN1204.c01 "p cnf 1521 194\n34 35 36 37 0\n38 39 40 41 0\n-37 -36 0\n-44 -42 0\n-45 -42 0\n-48 -47 0\n-49 -47 0\n-52 -50 0\n-53 -50 0\n-56 -55 0\n-57 -55 0\n-61 -60 0\n-64 -65 0\n-36 -40 0\n-37 -41 0\n-38 -42 0\n1324 1325 1326 1327 1328 1329 0\n-1325 -1327 0\n-1328 -1327 0\n-1329 -1327 0\n-34 -1326 0\n-1327 -35 0\n-1328 -36 0\n-1332 -1326 0\n-1333 -1327 0\n-1328 -40 0\n-1329 -41 0\n-1338 -1326 0\n-1339 -1327 0\n-1324 0\n1330 1331 1332 1333 1334 1335 0\n-1334 -36 0\n-1335 -37 0\n-1334 -40 0\n-1335 -41 0\n-1332 -1338 0\n-1333 -1339 0\n-1330 0\n1336 1337 1338 1339 1340 1341 0\n-34 -1338 0\n-1339 -35 0\n-1340 -36 0\n-1340 -40 0\n-1341 -41 0\n-1336 0\n1342 1343 1344 1345 1346 1347 0\n-1345 -1343 0\n-1345 -1346 0\n-1345 -1347 0\n-39 -1345 0\n-40 -1346 0\n-41 -1347 0\n-1343 -1349 0\n-1351 -1345 0\n-1352 -1346 0\n-1353 -1347 0\n-1344 -42 0\n-1355 -1343 0\n-1345 -1357 0\n-1358 -1346 0\n-1359 -1347 0\n-1342 0\n1348 1349 1350 1351 1352 1353 0\n-1352 -1349 0\n-39 -1351 0\n-1352 -40 0\n-1353 -41 0\n-1350 -42 0\n-1355 -1349 0\n-1351 -1357 0\n-1352 -1358 0\n-1359 -1353 0\n-1348 0\n1354 1355 1356 1357 1358 1359 0\n-39 -1357 0\n-40 -1358 0\n-41 -1359 0\n-1356 -42 0\n-1354 0\n1366 1367 1368 1369 1370 1371 0\n-1368 -42 0\n-1369 -47 0\n-1376 -1370 0\n-1371 -1377 0\n-1366 0\n1372 1373 1374 1375 1376 1377 0\n-1376 -1377 0\n-1374 -42 0\n-1375 -47 0\n-1372 0\n1378 1379 1380 1381 1382 1383 0\n-1381 -47 0\n-1384 -1378 0\n-1389 -1383 0\n-1380 -50 0\n-1378 -1390 0\n-1395 -1383 0\n-1379 0\n1384 1385 1386 1387 1388 1389 0\n-1387 -47 0\n-1386 -50 0\n-1384 -1390 0\n-1389 -1395 0\n-1385 0\n1390 1391 1392 1393 1394 1395 0\n-1393 -47 0\n-1392 -50 0\n-1391 0\n1396 1397 1398 1399 1400 1401 0\n-1398 -50 0\n-1397 -1403 0\n-1400 -1406 0\n-1407 -1401 0\n-1399 -55 0\n-1413 -1401 0\n-1396 0\n1402 1403 1404 1405 1406 1407 0\n-1404 -50 0\n-1405 -55 0\n-1413 -1407 0\n-1402 0\n1408 1409 1410 1411 1412 1413 0\n-1410 -50 0\n-1411 -55 0\n-1408 0\n1432 1433 1434 1435 1436 1437 0\n-1436 -60 0\n-1437 -61 0\n-1440 -1434 0\n-1441 -1435 0\n-1436 -64 0\n-1437 -65 0\n-1432 0\n1438 1439 1440 1441 1442 1443 0\n-1440 -1441 0\n-1442 -60 0\n-61 -1443 0\n-1442 -64 0\n-65 -1443 0\n-1438 0\n-1325 -1349 0\n-1328 -1352 0\n-1329 -1353 0\n-1325 -1355 0\n-1328 -1358 0\n-1329 -1359 0\n-1337 -1349 0\n-1340 -1352 0\n-1341 -1353 0\n-1337 -1355 0\n-1340 -1358 0\n-1341 -1359 0\n-1367 -1343 0\n-1370 -1346 0\n-1371 -1347 0\n-1373 -1343 0\n-1376 -1346 0\n-1377 -1347 0\n-1367 -1355 0\n-1370 -1358 0\n-1359 -1371 0\n-1373 -1355 0\n-1376 -1358 0\n-1359 -1377 0\n-1388 -1376 0\n-1394 -1376 0\n-1383 -1407 0\n-1382 -1412 0\n-1395 -1407 0\n-1434 -1326 0\n-1435 -1327 0\n-1440 -1326 0\n-1441 -1327 0\n-1433 -1331 0\n-1439 -1331 0\n-1397 -1343 0\n-1400 -1346 0\n-1347 -1401 0\n-1403 -1343 0\n-1406 -1346 0\n-1407 -1347 0\n-1397 -1349 0\n-1400 -1352 0\n-1353 -1401 0\n-1403 -1349 0\n-1406 -1352 0\n-1407 -1353 0\n-1409 -1355 0\n44 48 52 56 60 64 0\n45 49 53 57 61 65 0\n42 0\n47 0\n50 0\n55 0\n" "194 d 3 18 19 20 23 42 47 48 49 87 91 92 93 94 95 96 97 98 99 100 101 102 103 104 105 106 107 108 115 120 122 123 124 125 135 165 166 167 168 169 188 0\n195 -1357 1343 1346 1349 1352 0 62 73 191 57 68 59 70 46 63 56 0\n196 -1347 1349 1352 1355 1357 0 73 79 191 16 68 78 56 63 65 52 2 76 74 61 0\n196 d 52 61 0\n197 -1400 1343 1349 1355 0 62 73 79 191 16 57 68 78 177 183 195 196 46 50 54 63 67 72 2 74 76 0\n198 -1352 1343 1347 1355 1357 0 62 79 191 16 57 78 55 66 46 50 2 77 74 71 0\n198 d 71 0\n199 1357 1343 1347 1349 1353 1355 0 62 73 79 191 16 57 68 78 198 63 54 46 60 74 77 65 2 51 0\n199 d 198 65 51 0\n200 -1403 1355 0 62 73 116 191 193 194 57 68 110 114 179 111 185 197 109 178 184 199 59 70 46 63 55 0\n200 d 111 185 197 0\n201 -1352 1355 0 62 116 121 191 193 194 57 110 118 114 119 55 200 64 183 186 117 113 181 187 109 176 199 46 59 0\n201 d 64 183 186 0\n202 -1346 39 1351 1403 0 73 116 121 191 193 194 68 110 118 114 119 55 177 180 117 113 187 109 63 182 0\n203 -1349 1345 1346 0 62 116 121 191 193 194 57 110 118 114 119 69 182 200 53 46 178 109 112 117 181 0\n203 d 53 178 181 0\n204 -1357 1352 1403 0 73 116 121 191 193 194 68 110 118 114 119 59 70 75 202 203 195 63 187 117 176 184 109 112 0\n204 d 70 75 202 176 184 112 0\n205 -1359 1367 1373 0 85 90 191 192 81 88 82 89 161 80 83 86 164 0\n205 d 161 164 0\n206 -1343 0 79 85 90 191 192 78 81 88 82 89 179 156 153 58 201 204 205 74 160 80 84 86 163 0\n206 d 179 156 153 58 205 160 163 0\n207 -1347 1349 1352 1357 0 85 90 191 192 81 88 82 89 155 158 196 159 162 80 86 83 0\n207 d 196 0\n208 -1338 36 1325 1328 1329 1331 1334 0 30 38 28 36 40 17 22 25 1 31 33 0\n209 1331 36 1325 1328 1329 1334 1337 1340 1341 0 30 38 45 208 39 29 37 41 17 21 24 1 31 33 0\n209 d 208 33 0\n210 -1442 0 191 192 193 194 4 6 8 10 138 189 136 0\n210 d 138 136 0\n211 -64 1433 1434 1439 1440 0 133 140 191 192 193 194 5 7 9 11 210 131 13 190 128 137 126 134 130 0\n211 d 13 0\n212 -1331 1434 1440 0 133 140 191 192 193 194 4 5 6 7 8 9 10 11 210 174 175 211 189 127 12 190 132 139 126 134 130 0\n212 d 211 12 130 0\n215 -1358 41 1347 0 62 191 16 57 206 76 2 50 46 60 0\n215 d 60 0\n216 -1326 -1331 0 170 172 212 0\n216 d 170 172 212 0\n217 -1443 0 191 192 193 194 5 7 9 11 137 190 139 0\n217 d 137 139 0\n218 -1353 1326 1327 1328 1357 1358 0 30 79 191 78 72 143 74 17 144 0\n219 1327 1326 1328 1351 1352 1357 1358 0 30 73 79 191 68 78 218 63 69 141 74 17 146 0\n219 d 218 0\n220 -1331 1328 1351 1352 1357 1358 1436 1437 0 133 140 210 217 174 175 216 219 171 173 126 134 129 0\n220 d 219 0\n224 -1436 0 191 192 193 194 4 6 8 10 127 131 189 0\n224 d 4 6 8 10 127 131 189 0\n225 -1437 0 191 192 193 194 5 7 9 11 128 132 190 0\n225 d 5 7 9 11 128 132 190 0\n226 -1357 41 1347 0 62 85 90 191 192 57 81 88 82 89 206 59 46 55 154 157 204 200 159 162 80 86 84 0\n227 -1346 1367 1373 0 85 90 191 192 81 88 82 89 154 80 157 86 84 0\n227 d 154 157 84 0\n228 -1353 1328 1351 1352 0 62 79 191 16 57 78 206 224 225 67 56 72 143 149 215 226 74 220 144 150 159 162 227 46 50 2 14 34 43 209 0\n228 d 56 72 143 149 215 226 0\n229 1358 39 1328 1351 1352 0 73 79 191 16 68 78 224 225 228 63 69 141 147 200 204 74 77 2 220 146 152 14 34 43 209 0\n229 d 220 146 152 14 34 43 209 0\n230 -1327 1331 1334 1335 1337 1340 1341 0 38 45 29 39 25 31 36 0\n230 d 25 36 0\n231 1334 1325 1328 1329 1331 1335 1337 1340 1341 0 30 38 45 230 17 28 39 24 37 31 0\n231 d 230 24 37 31 0\n232 -1326 36 37 1337 1340 1341 0 45 21 1 28 39 41 0\n232 d 21 28 41 0\n233 36 37 1325 1328 1329 1337 1340 1341 0 30 45 232 17 22 29 1 39 40 0\n233 d 232 22 29 1 39 40 0\n234 -1345 1328 1352 0 30 73 133 140 191 16 68 210 217 224 225 50 54 228 63 229 141 147 76 2 15 27 35 44 151 233 32 231 174 175 216 17 171 173 126 134 129 0\n234 d 228 229 141 147 76 151 0\n235 -1327 1433 1439 0 133 140 210 217 224 225 171 173 126 134 129 0\n235 d 171 173 126 134 129 0\n239 -1349 1345 0 116 121 193 194 110 118 114 119 69 200 182 203 180 117 177 113 109 0\n239 d 110 114 182 203 177 113 109 0\n240 -1355 -1346 0 159 162 227 0\n240 d 227 0\n241 -1346 1349 0 121 193 194 118 119 206 55 180 240 200 117 204 207 187 199 0\n241 d 118 119 180 240 200 117 204 187 199 0\n242 1352 1328 0 62 191 57 206 234 239 241 195 46 207 0\n242 d 234 0\n243 -1347 1367 1373 0 85 90 191 192 81 88 82 89 155 158 80 86 83 0\n243 d 81 88 82 89 155 158 80 86 83 0\n244 1328 0 30 62 191 16 57 206 242 55 66 148 201 144 150 159 162 243 46 50 2 15 27 35 44 233 32 231 174 175 216 235 17 0\n244 d 242 55 66 148 201 144 150 159 162 243 15 27 35 44 233 32 231 174 175 216 235 17 0\n245 -1345 0 73 79 191 16 68 78 244 26 142 145 59 50 54 2 67 77 63 74 69 0\n245 d 16 68 78 26 145 59 50 54 2 67 77 63 74 69 0\n247 0 62 191 57 206 244 142 245 239 241 46 195 207 0\n"

theorem op874_four_matchings_window_cube_c01 :
    let L : Fin 4 → Fin 30 → Fin 20 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,5,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,5,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,6,9,10,12,14,16],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,6,9,10,12,14,16]]
    let R : Fin 4 → Fin 30 → Fin 20 := ![![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,6,8,7,11,15,13,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,6,11,7,8,13,15,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,8,5,7,11,15,13,17,18,19],![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,11,5,7,8,15,13,18,17,19]]
    let inc : Fin 4 → Fin 20 → Fin 3 → Fin 30 := ![![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,24],![5,6,21],![6,7,23],![8,19,22],![8,9,25],![9,10,26],![10,11,24],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,24],![5,6,21],![6,7,23],![8,19,24],![8,9,25],![9,10,26],![10,11,22],![11,12,27],![12,13,25],![13,14,28],![14,15,26],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,22],![5,6,24],![6,7,23],![8,19,21],![8,9,25],![9,10,26],![10,11,24],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,27],![17,18,28],![18,19,29]],![![0,7,20],![0,1,21],![1,2,22],![2,3,23],![3,4,20],![4,5,22],![5,6,24],![6,7,23],![8,19,24],![8,9,25],![9,10,26],![10,11,21],![11,12,27],![12,13,26],![13,14,28],![14,15,25],![15,16,29],![16,17,28],![17,18,27],![18,19,29]]]
    let bit : Fin 20 → Bool := ![true,false,false,true,true,false,false,true,false,false,false,false,true,false,true,false,true,true,true,true]
    ¬ ∃ (f : Fin 20 → Fin 4) (h : Fin 4 → Fin 20 → Fin 30 → Fin 6),
      (let color : Fin 4 → Fin 30 → Fin 6 := fun q e =>
        if he : e.val < 20 then ⟨(f ⟨e.val, he⟩).val + 2, by omega⟩
        else if bit (L q e) then 1 else 0
      (∀ q : Fin 4, ∀ v : Fin 20, ∀ i j : Fin 3,
        i ≠ j → color q (inc q v i) ≠ color q (inc q v j) ∧ h q v (inc q v i) ≠ h q v (inc q v j)) ∧
      (∀ q : Fin 4, ∀ v : Fin 20, ∀ i j : Fin 3, h q v (inc q v i) ≠ color q (inc q v j)) ∧
      (∀ q : Fin 4, ∀ e : Fin 30, ∀ i j : Fin 3,
        inc q (L q e) i ≠ e → inc q (R q e) j ≠ e →
        h q (L q e) (inc q (L q e) i) ≠ h q (R q e) (inc q (R q e) j)) ∧
      (∀ q : Fin 4, ∀ e : Fin 30, 20 ≤ e.val →
        ¬ (h q (L q e) e = (if bit (L q e) then 0 else 1) ∧
           h q (R q e) e = (if bit (R q e) then 0 else 1))) ∧
      (∀ k : Fin 4, ∃ j : Fin 6, f ((![10,11,12,13,14,15] : Fin 6 → Fin 20) j) = k) ∧
      (∀ k : Fin 4, ∃ j : Fin 6, f ((![11,12,13,14,15,16] : Fin 6 → Fin 20) j) = k)) ∧
      (f 10 = 0 ∧ f 11 = 1 ∧ f 12 = 0 ∧ f 13 = 1) := by
  intro L R inc bit
  rintro ⟨f, h, hP, ⟨u0, u1, u2, u3⟩⟩
  have hF : (IN1204.val f h).satisfies_fmla IN1204.c01.formula :=
    IN1204.fmla_sound f h hP [Sat.Literal.pos (IN1204.Fa 10 0), Sat.Literal.pos (IN1204.Fa 11 1), Sat.Literal.pos (IN1204.Fa 12 0), Sat.Literal.pos (IN1204.Fa 13 1)] (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact IN1204.sat_pos f h _ _ u0
      · exact IN1204.sat_pos f h _ _ u1
      · exact IN1204.sat_pos f h _ _ u2
      · exact IN1204.sat_pos f h _ _ u3
      ) _ (by decide +kernel)
  exact IN1204.c01.sat_proof _ hF
