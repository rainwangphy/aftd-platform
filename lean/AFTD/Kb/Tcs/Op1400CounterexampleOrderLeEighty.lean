import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForced
import AFTD.Kb.Tcs.PolynomialIsUnimodal
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForcingPoly

/-!
# op_1400_counterexample_order_le_eighty

Topic: graphs   Node: 9f6db6eeeab5

Provenance: formalization of a published result. Source: arXiv:2611.11352 Sec. 3, Question 2

Open Problem OP-1400: there exists a natural number n ≤ 80 and a simple graph G on Fin n with decidable adjacency whose zero forcing polynomial is not unimodal.
-/

namespace Op1400Cex

def AT : ℕ := 988516377098322429452817833896824765222276111927724320404473748599943602605291889595179374535843122736987115705005505676

def adjOf (v : ℕ) : ℕ := Nat.mod (Nat.shiftRight AT (Nat.mul 20 v)) 1048576
def tb (m i : ℕ) : Bool := !(Nat.beq (Nat.land 1 (Nat.shiftRight m i)) 0)
def isS (s : ℕ) : Bool := cond (Nat.beq s 0) false (Nat.beq s (Nat.pow 2 (Nat.log2 s)))
def VL : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]
def fsL (w : ℕ) (l : List ℕ) : Option ℕ :=
  List.rec none (fun v _ r => cond (tb w v) r (cond (isS (Nat.land (adjOf v) w)) (some v) r)) l
def fs0 (w : ℕ) : Option ℕ := fsL w VL
/-- union u1 of the white vertices' neighbourhoods, u2 of the vertices with two white neighbours,
and the unprocessed white vertices -/
def uLoop (f : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (fun rem u1 u2 => (u1, u2, rem))
    (fun _ ih rem u1 u2 => cond (Nat.beq rem 0) (u1, u2, rem)
      (ih (Nat.xor rem (Nat.pow 2 (Nat.log2 rem))) (Nat.lor u1 (adjOf (Nat.log2 rem)))
        (Nat.lor u2 (Nat.land u1 (adjOf (Nat.log2 rem)))))) f
def eSet (w : ℕ) : ℕ :=
  Nat.xor (uLoop 6 w 0 0).1 (Nat.land (uLoop 6 w 0 0).1 (Nat.lor (uLoop 6 w 0 0).2.1 w))
def chk (w v : ℕ) : Bool := Nat.blt v 20 && (!(tb w v) && isS (Nat.land (adjOf v) w))
def fs (w : ℕ) : Option ℕ :=
  cond (Nat.beq w 0) none
    (cond (Nat.beq (uLoop 6 w 0 0).2.2 0)
      (cond (Nat.beq (eSet w) 0) none
        (cond (chk w (Nat.log2 (eSet w))) (some (Nat.log2 (eSet w))) (fs0 w)))
      (fs0 w))

def run (f : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun w => w)
    (fun _ ih w => Option.rec w (fun v => ih (Nat.xor w (Nat.land (adjOf v) w))) (fs w)) f
def vR (r : ℕ) : ℕ := cond (Nat.beq (Nat.mod r 1048576) 0) 1 (Option.rec 0 (fun _ => 100000) (fs r))
def zR (r : ℕ) : ℕ := cond (Nat.beq (Nat.mod r 1048576) 0) 1 0
def Vf (w : ℕ) : ℕ := vR (run 6 w)
def Zf (w : ℕ) : ℕ := zR (run 6 w)

/-- sum of f (acc ||| msk s) over the k-subsets s of range n -/
def cntN (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => f acc
  | 0, _ + 1, _ => 0
  | n + 1, k + 1, acc => cntN f n (k + 1) acc + cntN f n k (acc ||| 2 ^ n)

theorem tb_eq (m i : ℕ) : tb m i = m.testBit i := by
  unfold tb Nat.testBit
  cases h : Nat.beq (Nat.land 1 (Nat.shiftRight m i)) 0
  · have : Nat.land 1 (Nat.shiftRight m i) ≠ 0 := fun h' => by
      rw [h'] at h; exact absurd h (by decide)
    simp only [Bool.not_false]
    exact (bne_iff_ne.2 this).symm
  · have := Nat.eq_of_beq_eq_true h
    simp only [Bool.not_true]
    exact (bne_eq_false_iff_eq.2 this).symm

theorem isS_spec {s : ℕ} (h : isS s = true) : ∃ x, s = 2 ^ x := by
  unfold isS at h
  cases h0 : Nat.beq s 0 <;> rw [h0] at h
  · exact ⟨Nat.log2 s, Nat.eq_of_beq_eq_true h⟩
  · simp at h

theorem isS_two_pow (y : ℕ) : isS (2 ^ y) = true := by
  unfold isS
  have h1 : Nat.beq (2 ^ y) 0 = false := by
    cases h : Nat.beq (2 ^ y) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) (by positivity)
  rw [h1]
  show Nat.beq (2 ^ y) (2 ^ Nat.log2 (2 ^ y)) = true
  rw [Nat.log2_two_pow]; exact Nat.beq_refl _

theorem mem_VL {v : ℕ} : v ∈ VL ↔ v < 20 := by
  simp only [VL, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem adj_symm : ∀ u v : Fin 20, (adjOf u.val).testBit v.val = true →
    (adjOf v.val).testBit u.val = true := by decide +kernel
theorem adj_irrefl : ∀ u : Fin 20, (adjOf u.val).testBit u.val = false := by decide +kernel

theorem adjOf_lt (v : ℕ) : adjOf v < 2 ^ 20 := Nat.mod_lt _ (by norm_num)

theorem testBit_adjOf_ge {v i : ℕ} (h : 20 ≤ i) : (adjOf v).testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (adjOf_lt v) (Nat.pow_le_pow_right (by norm_num) h))

theorem fsL_some (w : ℕ) : ∀ (l : List ℕ) {x : ℕ}, fsL w l = some x →
    x ∈ l ∧ w.testBit x = false ∧ isS (adjOf x &&& w) = true
  | [], x, h => by simp [fsL] at h
  | v :: l, x, h => by
    change cond (tb w v) (fsL w l) (cond (isS (Nat.land (adjOf v) w)) (some v) (fsL w l)) = some x at h
    cases h1 : tb w v
    · cases h2 : isS (Nat.land (adjOf v) w)
      · simp only [h1, h2, cond_false] at h
        obtain ⟨a, b, c⟩ := fsL_some w l h; exact ⟨List.mem_cons_of_mem _ a, b, c⟩
      · simp only [h1, h2, cond_false, cond_true, Option.some.injEq] at h; subst h
        exact ⟨List.mem_cons_self, by rw [← tb_eq]; exact h1, h2⟩
    · simp only [h1, cond_true] at h
      obtain ⟨a, b, c⟩ := fsL_some w l h; exact ⟨List.mem_cons_of_mem _ a, b, c⟩

theorem fsL_none (w : ℕ) : ∀ (l : List ℕ), fsL w l = none →
    ∀ v ∈ l, w.testBit v = true ∨ isS (adjOf v &&& w) = false
  | [], _, v, hv => by simp at hv
  | u :: l, h, v, hv => by
    change cond (tb w u) (fsL w l) (cond (isS (Nat.land (adjOf u) w)) (some u) (fsL w l)) = none at h
    have hl : fsL w l = none := by
      cases h1 : tb w u
      · cases h2 : isS (Nat.land (adjOf u) w)
        · simpa only [h1, h2, cond_false] using h
        · simp only [h1, h2, cond_false, cond_true] at h; exact absurd h (by simp)
      · simpa only [h1, cond_true] using h
    rcases List.mem_cons.1 hv with rfl | hv
    · cases h1 : tb w v
      · cases h2 : isS (Nat.land (adjOf v) w)
        · exact Or.inr (by first | rfl | exact h2)
        · simp only [h1, h2, cond_false, cond_true] at h; exact absurd h (by simp)
      · left; rw [← tb_eq]; exact h1
    · exact fsL_none w l hl v hv

theorem fs0_some {w v : ℕ} (h : fs0 w = some v) :
    v < 20 ∧ w.testBit v = false ∧ ∃ x, adjOf v &&& w = 2 ^ x := by
  obtain ⟨a, b, c⟩ := fsL_some w VL h
  exact ⟨mem_VL.1 a, b, isS_spec c⟩

theorem fs0_none {w : ℕ} (h : fs0 w = none) (v : ℕ) (hv : v < 20) (hb : w.testBit v = false)
    (y : ℕ) : adjOf v &&& w ≠ 2 ^ y := by
  intro he
  rcases fsL_none w VL h v (mem_VL.2 hv) with h1 | h1
  · rw [hb] at h1; exact absurd h1 (by simp)
  · rw [he, isS_two_pow] at h1; exact absurd h1 (by simp)

theorem AT_lt : AT < 2 ^ 400 := by decide +kernel

theorem adjOf_ge {y : ℕ} (hy : 20 ≤ y) : adjOf y = 0 := by
  unfold adjOf
  have : Nat.shiftRight AT (Nat.mul 20 y) = 0 := by
    show AT >>> (20 * y) = 0
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    exact lt_of_lt_of_le AT_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [this]

def Inv (w rem u1 u2 : ℕ) : Prop :=
  (∀ i, rem.testBit i = true → w.testBit i = true) ∧
  (∀ y v, w.testBit y = true → rem.testBit y = false → (adjOf y).testBit v = true →
    u1.testBit v = true) ∧
  (∀ v, u1.testBit v = true →
    ∃ y, w.testBit y = true ∧ rem.testBit y = false ∧ (adjOf y).testBit v = true) ∧
  (∀ v, u2.testBit v = true → ∃ y1 y2, y1 ≠ y2 ∧ w.testBit y1 = true ∧ w.testBit y2 = true ∧
    (adjOf y1).testBit v = true ∧ (adjOf y2).testBit v = true)

theorem uLoop_succ (f rem u1 u2 : ℕ) : uLoop (f + 1) rem u1 u2 =
    cond (Nat.beq rem 0) (u1, u2, rem)
      (uLoop f (rem ^^^ 2 ^ Nat.log2 rem) (u1 ||| adjOf (Nat.log2 rem))
        (u2 ||| (u1 &&& adjOf (Nat.log2 rem)))) := rfl

theorem inv_step {w rem u1 u2 : ℕ} (hrem : rem ≠ 0) (h : Inv w rem u1 u2) :
    Inv w (rem ^^^ 2 ^ Nat.log2 rem) (u1 ||| adjOf (Nat.log2 rem))
      (u2 ||| (u1 &&& adjOf (Nat.log2 rem))) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hy0 : rem.testBit (Nat.log2 rem) = true := Nat.testBit_log2 hrem
  have hr : ∀ i, (rem ^^^ 2 ^ Nat.log2 rem).testBit i = (rem.testBit i ^^ decide (Nat.log2 rem = i)) := by
    intro i; rw [Nat.testBit_xor, Nat.testBit_two_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hr] at hi
    by_cases hiy : Nat.log2 rem = i
    · subst hiy; simp [hy0] at hi
    · simp [hiy] at hi; exact h1 i hi
  · intro y v hw hry ha
    rw [Nat.testBit_or]
    by_cases hyy : Nat.log2 rem = y
    · subst hyy; simp [ha]
    · rw [hr] at hry; simp [hyy] at hry
      simp [h2 y v hw hry ha]
  · intro v hv
    rw [Nat.testBit_or] at hv
    cases hu : u1.testBit v
    · rw [hu] at hv
      simp only [Bool.false_or] at hv
      refine ⟨Nat.log2 rem, h1 _ hy0, ?_, hv⟩
      rw [hr]; simp [hy0]
    · obtain ⟨y, hwy, hry, hay⟩ := h3 v hu
      refine ⟨y, hwy, ?_, hay⟩
      rw [hr]
      have : Nat.log2 rem ≠ y := fun e => by rw [e] at hy0; rw [hy0] at hry; exact absurd hry (by simp)
      simp [this, hry]
  · intro v hv
    rw [Nat.testBit_or, Nat.testBit_and] at hv
    cases hu2 : u2.testBit v
    · rw [hu2] at hv
      simp only [Bool.false_or, Bool.and_eq_true] at hv
      obtain ⟨y, hwy, hry, hay⟩ := h3 v hv.1
      have : y ≠ Nat.log2 rem := fun e => by rw [← e] at hy0; rw [hy0] at hry; exact absurd hry (by simp)
      exact ⟨y, Nat.log2 rem, this, hwy, h1 _ hy0, hay, hv.2⟩
    · exact h4 v hu2

theorem uLoop_inv (w : ℕ) : ∀ f rem u1 u2, Inv w rem u1 u2 →
    Inv w (uLoop f rem u1 u2).2.2 (uLoop f rem u1 u2).1 (uLoop f rem u1 u2).2.1
  | 0, rem, u1, u2, h => h
  | f + 1, rem, u1, u2, h => by
    rw [uLoop_succ]
    cases h0 : Nat.beq rem 0
    · simp only [cond_false]
      exact uLoop_inv w f _ _ _ (inv_step (Nat.ne_of_beq_eq_false h0) h)
    · simpa only [cond_true] using h

theorem inv_init (w : ℕ) : Inv w w 0 0 := by
  refine ⟨fun i h => h, ?_, ?_, ?_⟩
  · intro y v hw hr; rw [hw] at hr; exact absurd hr (by simp)
  · intro v hv; simp at hv
  · intro v hv; simp at hv

theorem fast_stall {w : ℕ} (hrem : (uLoop 6 w 0 0).2.2 = 0) (hE : eSet w = 0) (v : ℕ) (hv : v < 20)
    (hb : w.testBit v = false) (x : ℕ) : adjOf v &&& w ≠ 2 ^ x := by
  intro hs
  have hI := uLoop_inv w 6 w 0 0 (inv_init w)
  rw [hrem] at hI
  obtain ⟨_, h2, _, h4⟩ := hI
  have hbit : ∀ i, (adjOf v &&& w).testBit i = decide (x = i) := by
    intro i; rw [hs, Nat.testBit_two_pow]
  have hx := hbit x
  simp only [Nat.testBit_and, decide_true, Bool.and_eq_true] at hx
  have hx20 : x < 20 := by
    by_contra hc; rw [testBit_adjOf_ge (by omega)] at hx; exact absurd hx.1 (by simp)
  have hxv : (adjOf x).testBit v = true := adj_symm ⟨v, hv⟩ ⟨x, hx20⟩ hx.1
  have hu1 := h2 x v hx.2 (by simp) hxv
  have hEv : (eSet w).testBit v = false := by rw [hE]; simp
  unfold eSet at hEv
  simp only [show ∀ a b : ℕ, Nat.xor a b = a ^^^ b from fun _ _ => rfl,
    show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl,
    show ∀ a b : ℕ, Nat.lor a b = a ||| b from fun _ _ => rfl,
    Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, hu1, hb] at hEv
  have hu2 : (uLoop 6 w 0 0).2.1.testBit v = true := by
    cases h : (uLoop 6 w 0 0).2.1.testBit v
    · rw [h] at hEv; simp at hEv
    · rfl
  obtain ⟨y1, y2, hne, hw1, hw2, ha1, ha2⟩ := h4 v hu2
  have hy1 : y1 < 20 := by
    by_contra hc; rw [adjOf_ge (by omega)] at ha1; simp at ha1
  have hy2 : y2 < 20 := by
    by_contra hc; rw [adjOf_ge (by omega)] at ha2; simp at ha2
  have e1 := hbit y1
  have e2 := hbit y2
  rw [Nat.testBit_and, adj_symm ⟨y1, hy1⟩ ⟨v, hv⟩ ha1, hw1] at e1
  rw [Nat.testBit_and, adj_symm ⟨y2, hy2⟩ ⟨v, hv⟩ ha2, hw2] at e2
  simp only [Bool.and_self, Bool.true_eq, decide_eq_true_eq] at e1 e2
  exact hne (e1.symm.trans e2)

theorem forceStep_some {w v : ℕ} (h : fs w = some v) :
    v < 20 ∧ w.testBit v = false ∧ ∃ x, adjOf v &&& w = 2 ^ x := by
  unfold fs at h
  cases h0 : Nat.beq w 0
  · cases hr : Nat.beq (uLoop 6 w 0 0).2.2 0
    · simp only [h0, hr, cond_false] at h; exact fs0_some h
    · cases h1 : Nat.beq (eSet w) 0
      · cases h2 : chk w (Nat.log2 (eSet w))
        · simp only [h0, hr, h1, h2, cond_false, cond_true] at h; exact fs0_some h
        · simp only [h0, hr, h1, h2, cond_false, cond_true, Option.some.injEq] at h
          subst h
          simp only [chk, Bool.and_eq_true, Bool.not_eq_true'] at h2
          obtain ⟨ha, hb, hc⟩ := h2
          exact ⟨Nat.le_of_ble_eq_true ha, by rw [← tb_eq]; exact hb, isS_spec hc⟩
      · simp only [h0, hr, h1, cond_false, cond_true] at h; exact absurd h (by simp)
  · simp only [h0, cond_true] at h; exact absurd h (by simp)

theorem forceStep_none {w : ℕ} (h : fs w = none) (v : ℕ) (hv : v < 20) (hb : w.testBit v = false)
    (y : ℕ) : adjOf v &&& w ≠ 2 ^ y := by
  unfold fs at h
  cases h0 : Nat.beq w 0
  · cases hr : Nat.beq (uLoop 6 w 0 0).2.2 0
    · apply fs0_none _ v hv hb y
      simpa only [h0, hr, cond_false] using h
    · cases h1 : Nat.beq (eSet w) 0
      · apply fs0_none _ v hv hb y
        cases h2 : chk w (Nat.log2 (eSet w))
        · simpa only [h0, hr, h1, h2, cond_false, cond_true] using h
        · simp only [h0, hr, h1, h2, cond_false, cond_true] at h; exact absurd h (by simp)
      · exact fast_stall (Nat.eq_of_beq_eq_true hr) (Nat.eq_of_beq_eq_true h1) v hv hb y
  · rw [Nat.eq_of_beq_eq_true h0, Nat.and_zero]
    exact (Nat.two_pow_pos y).ne

theorem run_succ (f w : ℕ) : run (f + 1) w = Option.rec w (fun v => run f (w ^^^ (adjOf v &&& w))) (fs w) := rfl

def G : SimpleGraph (Fin 20) := SimpleGraph.fromRel (fun u v => (adjOf u.val).testBit v.val = true)

theorem adj_iff {u v : Fin 20} : G.Adj u v ↔ (adjOf u.val).testBit v.val = true := by
  simp only [G, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact adj_symm _ _ h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl; rw [adj_irrefl] at h; exact absurd h (by simp)

instance : DecidableRel G.Adj := fun _ _ => decidable_of_iff _ adj_iff.symm

theorem run_sub : ∀ f w i, (run f w).testBit i = true → w.testBit i = true
  | 0, w, i, h => h
  | f + 1, w, i, h => by
    rw [run_succ] at h
    cases hx : fs w with
    | none => rw [hx] at h; exact h
    | some x =>
      rw [hx] at h
      have := run_sub f _ i h
      simp [Nat.testBit_xor, Nat.testBit_and] at this
      by_cases hw : w.testBit i <;> simp_all

theorem run_sound (S : Set (Fin 20)) : ∀ f w, (∀ v : Fin 20, w.testBit v.val = false → ZeroForced G S v) →
    ∀ v : Fin 20, (run f w).testBit v.val = false → ZeroForced G S v
  | 0, w, hw => hw
  | f + 1, w, hw => by
    rw [run_succ]
    cases hu : fs w with
    | none => exact hw
    | some u =>
      obtain ⟨hu24, hub, x, hsx⟩ := forceStep_some hu
      apply run_sound S f
      have hbit : ∀ i, ((adjOf u &&& w).testBit i = true ↔ i = x) := by
        intro i; rw [hsx, Nat.testBit_two_pow]; simp [eq_comm]
      have hxa : (adjOf u).testBit x = true := by
        have := (hbit x).2 rfl; simp [Nat.testBit_and] at this; exact this.1
      have hx24 : x < 20 := by
        by_contra hc; rw [testBit_adjOf_ge (by omega)] at hxa; exact absurd hxa (by simp)
      have hfu : ZeroForced G S ⟨u, hu24⟩ := hw ⟨u, hu24⟩ hub
      intro v hv
      by_cases hvw : w.testBit v.val = true
      · have hva : (adjOf u).testBit v.val = true := by
          simp [Nat.testBit_xor, Nat.testBit_and, hvw] at hv; exact hv
        have hvx : v.val = x := (hbit v.val).1 (by simp [Nat.testBit_and, hva, hvw])
        have : v = ⟨x, hx24⟩ := Fin.ext hvx
        subst this
        refine ZeroForced.step _ _ hfu (adj_iff.2 hxa) ?_
        intro y hy hyx
        apply hw
        by_contra hyw
        simp only [Bool.not_eq_false] at hyw
        have := (hbit y.val).1 (by simp [Nat.testBit_and, hyw]; exact adj_iff.1 hy)
        exact hyx (Fin.ext this)
      · exact hw v (by simpa using hvw)

theorem stall_not_forced (S : Set (Fin 20)) (r : ℕ) (hr : fs r = none)
    (hS : ∀ v ∈ S, r.testBit v.val = false) : ∀ y, ZeroForced G S y → r.testBit y.val = false := by
  intro y hy
  induction hy with
  | init v hv => exact hS v hv
  | step u y hu huy hall ihu ihall =>
    by_contra hry
    simp only [Bool.not_eq_false] at hry
    have hs : adjOf u.val &&& r = 2 ^ y.val := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_two_pow, Nat.testBit_and]
      by_cases hi : i < 20
      · by_cases hiy : i = y.val
        · subst hiy; simp [hry]; exact adj_iff.1 huy
        · have : (adjOf u.val).testBit i = true → r.testBit i = false := fun ha =>
            ihall ⟨i, hi⟩ (adj_iff.2 ha) (fun h => hiy (by rw [← h]))
          have hne : decide (y.val = i) = false := by simp; omega
          rw [hne]
          cases ha : (adjOf u.val).testBit i
          · simp
          · simp [this ha]
      · rw [testBit_adjOf_ge (by omega)]; simp; omega
    exact forceStep_none hr u.val u.isLt ihu y.val hs

def msk (s : Finset ℕ) : ℕ := s.fold (· ||| ·) 0 (fun i => 2 ^ i)

theorem testBit_msk (s : Finset ℕ) (i : ℕ) : (msk s).testBit i = decide (i ∈ s) := by
  induction s using Finset.induction_on with
  | empty => simp [msk]
  | insert a s ha ih =>
    unfold msk at *
    rw [Finset.fold_insert ha, Nat.testBit_or, ih, Nat.testBit_two_pow]
    by_cases h : i = a <;> simp [h, eq_comm]

theorem cntN_eq (f : ℕ → ℕ) : ∀ n k acc,
    cntN f n k acc = ∑ s ∈ (Finset.range n).powersetCard k, f (acc ||| msk s)
  | n, 0, acc => by simp [cntN, msk]
  | 0, k + 1, acc => by
    rw [Finset.range_zero, Finset.powersetCard_eq_empty.2 (by simp)]; rfl
  | n + 1, k + 1, acc => by
    rw [cntN, cntN_eq f n (k + 1) acc, cntN_eq f n k (acc ||| 2 ^ n), Finset.range_add_one,
      Finset.powersetCard_succ_insert Finset.notMem_range_self, Finset.sum_union, Finset.sum_image]
    · congr 1
      apply Finset.sum_congr rfl
      intro s hs
      have hn : n ∉ s := fun h => by
        have := (Finset.mem_powersetCard.1 hs).1 h; simp at this
      unfold msk
      rw [Finset.fold_insert hn]
      simp [Nat.or_assoc]
    · intro s hs t ht hst
      have hns : n ∉ s := fun h => by have := (Finset.mem_powersetCard.1 hs).1 h; simp at this
      have hnt : n ∉ t := fun h => by have := (Finset.mem_powersetCard.1 ht).1 h; simp at this
      have := congrArg (fun u => u.erase n) hst
      simpa [Finset.erase_insert hns, Finset.erase_insert hnt] using this
    · rw [Finset.disjoint_left]
      intro s hs hs'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs'
      have := (Finset.mem_powersetCard.1 hs).1 (Finset.mem_insert_self n t)
      simp at this

theorem cntN_top (f : ℕ → ℕ) : ∀ n k acc,
    cntN f n (k + 1) acc = ∑ m ∈ Finset.range n, cntN f m k (acc ||| 2 ^ m)
  | 0, k, acc => by simp [cntN]
  | n + 1, k, acc => by
    rw [cntN, cntN_top f n k acc, Finset.sum_range_succ]

open scoped Classical in
theorem coeff_zfp (j : ℕ) : (zero_forcing_poly G).coeff j =
    (Finset.univ.filter (fun S : Finset (Fin 20) => S.card = j ∧ is_zero_forcing_set G (S : Set (Fin 20)))).card := by
  unfold zero_forcing_poly
  rw [Polynomial.finsetSum_coeff, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : is_zero_forcing_set G (S : Set (Fin 20))
  · by_cases hj : S.card = j
    · simp [h, hj, Polynomial.coeff_X_pow]
    · simp [h, hj, Polynomial.coeff_X_pow, Ne.symm hj]
  · simp [h]

/-- decode a subset of range 20 -/
def dec (s : Finset ℕ) : Finset (Fin 20) := Finset.univ.filter (fun v : Fin 20 => v.val ∈ s)

theorem map_dec {s : Finset ℕ} (hs : s ⊆ Finset.range 20) : (dec s).map Fin.valEmbedding = s := by
  ext x; simp only [dec, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hx; exact ⟨⟨x, by simpa using hs hx⟩, hx, rfl⟩

open scoped Classical in
/-- the j-th coefficient as a sum over the (20 - j)-subsets of range 20 of white vertices -/
theorem coeff_sum (j : ℕ) (hj : j ≤ 20) : (zero_forcing_poly G).coeff j =
    ∑ s ∈ (Finset.range 20).powersetCard (20 - j),
      if is_zero_forcing_set G (((dec s)ᶜ : Finset (Fin 20)) : Set (Fin 20)) then 1 else 0 := by
  rw [coeff_zfp, ← Finset.card_filter]
  apply Finset.card_nbij' (fun S => Sᶜ.map Fin.valEmbedding) (fun s => (dec s)ᶜ)
  · intro S hS
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS
    simp only [Finset.coe_filter, Finset.mem_powersetCard, Set.mem_ofPred_eq]
    have hsub : Sᶜ.map Fin.valEmbedding ⊆ Finset.range 20 := by
      intro x hx; simp at hx; obtain ⟨a, _, rfl⟩ := hx; simp
    refine ⟨⟨hsub, by rw [Finset.card_map, Finset.card_compl, hS.1]; simp⟩, ?_⟩
    have : (dec (Sᶜ.map Fin.valEmbedding))ᶜ = S := by ext v; simp [dec, Fin.val_inj]
    rw [this]; exact hS.2
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_powersetCard, Set.mem_ofPred_eq] at hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨?_, hs.2⟩
    rw [Finset.card_compl, ← Finset.card_map Fin.valEmbedding, map_dec hs.1.1, hs.1.2]
    simp; omega
  · intro S _; ext v; simp [dec, Fin.val_inj]
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_powersetCard, Set.mem_ofPred_eq] at hs
    simp [map_dec hs.1.1]

theorem testBit_msk_dec {s : Finset ℕ} (hs : s ⊆ Finset.range 20) (v : Fin 20) :
    (msk s).testBit v.val = decide (v ∉ (dec s)ᶜ) := by
  rw [testBit_msk]; simp [dec]

theorem run_mod_zero {r : ℕ} (h : r % 1048576 = 0) (v : ℕ) (hv : v < 20) : r.testBit v = false := by
  have := congrArg (fun r => r.testBit v) h
  simp only [show (1048576 : ℕ) = 2 ^ 20 by norm_num, Nat.testBit_mod_two_pow, Nat.zero_testBit] at this
  simpa [hv] using this

theorem run_mod_ne {r : ℕ} (h : r % 1048576 ≠ 0) : ∃ v < 20, r.testBit v = true := by
  by_contra hc
  push Not at hc
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (1048576 : ℕ) = 2 ^ 20 by norm_num, Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < 20
  · simp [hi, hc i hi]
  · simp [hi]

/-- lower bound side: a positive Zf certifies a zero forcing set -/
theorem Zf_le {s : Finset ℕ} (hs : s ⊆ Finset.range 20) :
    Zf (msk s) ≤ (open scoped Classical in
      if is_zero_forcing_set G (((dec s)ᶜ : Finset (Fin 20)) : Set (Fin 20)) then 1 else 0) := by
  classical
  unfold Zf zR
  cases h0 : Nat.beq (Nat.mod (run 6 (msk s)) 1048576) 0
  · simp
  · have h0' := Nat.eq_of_beq_eq_true h0
    have hzf : is_zero_forcing_set G (((dec s)ᶜ : Finset (Fin 20)) : Set (Fin 20)) := by
      intro v
      apply run_sound _ 6 (msk s)
      · intro u hu
        apply ZeroForced.init
        rw [testBit_msk_dec hs] at hu
        simpa using hu
      · exact run_mod_zero h0' v.val v.isLt
    rw [if_pos hzf]; simp

/-- upper bound side: a zero forcing set has Vf ≥ 1 -/
theorem le_Vf {s : Finset ℕ} (hs : s ⊆ Finset.range 20) :
    (open scoped Classical in
      if is_zero_forcing_set G (((dec s)ᶜ : Finset (Fin 20)) : Set (Fin 20)) then 1 else 0) ≤ Vf (msk s) := by
  classical
  by_cases hzf : is_zero_forcing_set G (((dec s)ᶜ : Finset (Fin 20)) : Set (Fin 20))
  · rw [if_pos hzf]
    unfold Vf vR
    cases h0 : Nat.beq (Nat.mod (run 6 (msk s)) 1048576) 0
    · have h0' : run 6 (msk s) % 1048576 ≠ 0 := fun h => by
        have : Nat.beq (Nat.mod (run 6 (msk s)) 1048576) 0 = true := by
          show Nat.beq (run 6 (msk s) % 1048576) 0 = true
          rw [h]; rfl
        rw [this] at h0; exact absurd h0 (by simp)
      cases hf : fs (run 6 (msk s))
      · exfalso
        obtain ⟨v, hv, hb⟩ := run_mod_ne h0'
        have hS : ∀ y ∈ (((dec s)ᶜ : Finset (Fin 20)) : Set (Fin 20)), (run 6 (msk s)).testBit y.val = false := by
          intro y hy
          cases hr : (run 6 (msk s)).testBit y.val
          · rfl
          · have := run_sub 6 (msk s) y.val hr
            rw [testBit_msk_dec hs] at this
            simp at hy this; exact absurd this hy
        have := stall_not_forced _ _ hf hS ⟨v, hv⟩ (hzf ⟨v, hv⟩)
        simp [this] at hb
      · simp
    · simp
  · rw [if_neg hzf]; exact Nat.zero_le _

theorem coeff_ge (j : ℕ) (hj : j ≤ 20) :
    cntN Zf 20 (20 - j) 0 ≤ (zero_forcing_poly G).coeff j := by
  classical
  rw [coeff_sum j hj, cntN_eq]
  apply Finset.sum_le_sum
  intro s hs
  rw [Nat.zero_or]
  exact Zf_le (Finset.mem_powersetCard.1 hs).1

theorem coeff_le (j : ℕ) (hj : j ≤ 20) :
    (zero_forcing_poly G).coeff j ≤ cntN Vf 20 (20 - j) 0 := by
  classical
  rw [coeff_sum j hj, cntN_eq]
  apply Finset.sum_le_sum
  intro s hs
  rw [Nat.zero_or]
  exact le_Vf (Finset.mem_powersetCard.1 hs).1

theorem not_unimodal_of {p : Polynomial ℕ} {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (h1 : p.coeff b < p.coeff a) (h2 : p.coeff b < p.coeff c) : ¬ polynomial_is_unimodal p := by
  rintro ⟨m, hup, hdown⟩
  by_cases hbm : b ≤ m
  · exact absurd (hup hab.le hbm) (not_le.2 h1)
  · exact absurd (hdown (by omega) hbc.le) (not_le.2 h2)

set_option maxRecDepth 100000 in
theorem cz3 : cntN Zf 20 3 0 = 939 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_0 : cntN Vf 0 3 (0 ||| 2 ^ 0) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_1 : cntN Vf 1 3 (0 ||| 2 ^ 1) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_2 : cntN Vf 2 3 (0 ||| 2 ^ 2) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_3 : cntN Vf 3 3 (0 ||| 2 ^ 3) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_4 : cntN Vf 4 3 (0 ||| 2 ^ 4) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_5 : cntN Vf 5 3 (0 ||| 2 ^ 5) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_6 : cntN Vf 6 3 (0 ||| 2 ^ 6) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_7 : cntN Vf 7 3 (0 ||| 2 ^ 7) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_8 : cntN Vf 8 3 (0 ||| 2 ^ 8) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_9 : cntN Vf 9 3 (0 ||| 2 ^ 9) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_10 : cntN Vf 10 3 (0 ||| 2 ^ 10) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_11 : cntN Vf 11 3 (0 ||| 2 ^ 11) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_12 : cntN Vf 12 3 (0 ||| 2 ^ 12) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_13 : cntN Vf 13 3 (0 ||| 2 ^ 13) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_14 : cntN Vf 14 3 (0 ||| 2 ^ 14) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_15 : cntN Vf 15 3 (0 ||| 2 ^ 15) = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_16 : cntN Vf 16 3 (0 ||| 2 ^ 16) = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_17 : cntN Vf 17 3 (0 ||| 2 ^ 17) = 172 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_18 : cntN Vf 18 3 (0 ||| 2 ^ 18) = 258 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cv4_19 : cntN Vf 19 3 (0 ||| 2 ^ 19) = 359 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_17_15 : cntN Zf 15 3 (0 ||| 2 ^ 17 ||| 2 ^ 15) = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_17_16 : cntN Zf 16 3 (0 ||| 2 ^ 17 ||| 2 ^ 16) = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_18_15 : cntN Zf 15 3 (0 ||| 2 ^ 18 ||| 2 ^ 15) = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_18_16 : cntN Zf 16 3 (0 ||| 2 ^ 18 ||| 2 ^ 16) = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_18_17 : cntN Zf 17 3 (0 ||| 2 ^ 18 ||| 2 ^ 17) = 172 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_19_15 : cntN Zf 15 3 (0 ||| 2 ^ 19 ||| 2 ^ 15) = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_19_16 : cntN Zf 16 3 (0 ||| 2 ^ 19 ||| 2 ^ 16) = 60 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_19_17 : cntN Zf 17 3 (0 ||| 2 ^ 19 ||| 2 ^ 17) = 172 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cz5_19_18 : cntN Zf 18 3 (0 ||| 2 ^ 19 ||| 2 ^ 18) = 228 := by decide +kernel

theorem v4 : cntN Vf 20 4 0 = 909 := by
  have e : cntN Vf 20 4 0 = ∑ m ∈ Finset.range 20, cntN Vf m 3 (0 ||| 2 ^ m) := cntN_top Vf 20 3 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e
  rw [e, cv4_0, cv4_1, cv4_2, cv4_3, cv4_4, cv4_5, cv4_6, cv4_7, cv4_8, cv4_9, cv4_10, cv4_11, cv4_12, cv4_13, cv4_14, cv4_15, cv4_16, cv4_17, cv4_18, cv4_19]

theorem z5 : 932 ≤ cntN Zf 20 5 0 := by
  have e : cntN Zf 20 5 0 = ∑ m ∈ Finset.range 20, cntN Zf m 4 (0 ||| 2 ^ m) := cntN_top Zf 20 4 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e
  have e17 : cntN Zf 17 4 (0 ||| 2 ^ 17) = ∑ m' ∈ Finset.range 17, cntN Zf m' 3 (0 ||| 2 ^ 17 ||| 2 ^ m') := cntN_top Zf 17 3 _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e17
  have e18 : cntN Zf 18 4 (0 ||| 2 ^ 18) = ∑ m' ∈ Finset.range 18, cntN Zf m' 3 (0 ||| 2 ^ 18 ||| 2 ^ m') := cntN_top Zf 18 3 _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e18
  have e19 : cntN Zf 19 4 (0 ||| 2 ^ 19) = ∑ m' ∈ Finset.range 19, cntN Zf m' 3 (0 ||| 2 ^ 19 ||| 2 ^ m') := cntN_top Zf 19 3 _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e19
  have := cz5_17_15; have := cz5_17_16; have := cz5_18_15; have := cz5_18_16; have := cz5_18_17; have := cz5_19_15; have := cz5_19_16; have := cz5_19_17; have := cz5_19_18
  omega

end Op1400Cex

/-- Open Problem OP-1400: there exists a simple graph of order at most 80 with a non-unimodal zero forcing polynomial. -/
theorem op_1400_counterexample_order_le_eighty :
    ∃ (n : ℕ) (_ : n ≤ 80) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      ¬ polynomial_is_unimodal (zero_forcing_poly G) := by
  have h15 : Op1400Cex.cntN Op1400Cex.Zf 20 5 0 ≤ (zero_forcing_poly Op1400Cex.G).coeff 15 :=
    Op1400Cex.coeff_ge 15 (by norm_num)
  have h16 : (zero_forcing_poly Op1400Cex.G).coeff 16 ≤ Op1400Cex.cntN Op1400Cex.Vf 20 4 0 :=
    Op1400Cex.coeff_le 16 (by norm_num)
  have h17 : Op1400Cex.cntN Op1400Cex.Zf 20 3 0 ≤ (zero_forcing_poly Op1400Cex.G).coeff 17 :=
    Op1400Cex.coeff_ge 17 (by norm_num)
  rw [Op1400Cex.cz3] at h17
  rw [Op1400Cex.v4] at h16
  have := Op1400Cex.z5
  exact ⟨20, by norm_num, Op1400Cex.G, inferInstance,
    Op1400Cex.not_unimodal_of (a := 15) (b := 16) (c := 17) (by norm_num) (by norm_num) (by omega) (by omega)⟩
