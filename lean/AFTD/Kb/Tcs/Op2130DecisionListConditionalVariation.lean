import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130VariationSumLower
import AFTD.Kb.Tcs.C

/-!
# op2130_decision_list_conditional_variation

Topic: online_algorithms   Node: 3cc2392909d5

Provenance: helper lemma. OP-2130, fair-bit alternating decision-list martingale

For an odd number N of fair bits, the signed alternating OR/AND decision list has pathwise conditional-mean quadratic variation at least (N-2)/4 on the tape that takes the non-deciding branch at every gate.
-/

def op2130_outer_decision : Bool → List Bool → Bool
  | _, [] => false
  | isAnd, b :: bs => if isAnd then b && op2130_outer_decision false bs else b || op2130_outer_decision true bs

set_option maxHeartbeats 1000000


theorem op2130_logical_sum_bool_tapes_succ {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : (Fin (n+1) → Bool) → A) :
    (∑ r, f r) = ∑ s : Fin n → Bool, (f (Fin.cons false s) + f (Fin.cons true s)) := by
  classical
  calc
    (∑ r, f r) = ∑ p : Bool × (Fin n → Bool), f ((Fin.consEquiv fun _ => Bool) p) :=
      ((Fin.consEquiv fun _ => Bool).sum_comp f).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.consEquiv_apply, Finset.sum_add_distrib]
      ac_rfl

def op2130_logical_count_decision : Bool → List Bool → Bool
  | _, [] => false
  | isAnd, b::bs => if isAnd then b && op2130_logical_count_decision false bs else b || op2130_logical_count_decision true bs



def op2130_nondecd_bit (v : Bool) (i : ℕ) : Bool :=
  if i%2=0 then v else !v

def op2130_nondecd_prefix {n : ℕ} (v : Bool) (t : ℕ) (r : Fin n → Bool) : Prop :=
  ∀ i : Fin n, i.val < t → r i = op2130_nondecd_bit v i.val

theorem op2130_nondecd_bit_succ (v : Bool) (i : ℕ) :
    op2130_nondecd_bit v (i+1) = op2130_nondecd_bit (!v) i := by
  by_cases h : i%2=0
  · have hs : (i+1)%2 ≠ 0 := by omega
    simp [op2130_nondecd_bit,h,hs]
  · have hs : (i+1)%2 = 0 := by omega
    cases v <;> simp [op2130_nondecd_bit,h,hs]

theorem op2130_nondecd_prefix_succ {n : ℕ} (v : Bool) (t : ℕ) (r : Fin (n+1) → Bool) :
    op2130_nondecd_prefix v (t+1) r ↔ r 0 = v ∧
      op2130_nondecd_prefix (!v) t (fun i => r i.succ) := by
  constructor
  · intro h
    constructor
    · have hh := h 0 (by simp)
      simpa [op2130_nondecd_bit] using hh
    · intro i hi
      have hh := h i.succ (by simp only [Fin.val_succ]; omega)
      simpa only [Fin.val_succ,op2130_nondecd_bit_succ] using hh
  · rintro ⟨h0,ht⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · intro _; simpa [op2130_nondecd_bit] using h0
    · intro j hj
      have hh := ht j (by simp only [Fin.val_succ] at hj; omega)
      simpa only [Fin.val_succ,op2130_nondecd_bit_succ] using hh

theorem op2130_decision_prefix_sum_succ (n t : ℕ) (v : Bool) (f : Bool → ℝ) :
    (by classical exact (∑ r : Fin (n+1) → Bool,
      if op2130_nondecd_prefix v (t+1) r then f (op2130_logical_count_decision v (List.ofFn r)) else 0) =
    (∑ r : Fin n → Bool,
      if op2130_nondecd_prefix (!v) t r then f (op2130_logical_count_decision (!v) (List.ofFn r)) else 0)) := by
  classical
  rw [op2130_logical_sum_bool_tapes_succ]
  apply Finset.sum_congr rfl
  intro r hr
  rw [op2130_nondecd_prefix_succ,op2130_nondecd_prefix_succ]
  cases v <;> simp [List.ofFn_succ,op2130_logical_count_decision]

noncomputable def op2130_sign_mean (v : Bool) (n : ℕ) : ℝ :=
  (∑ r : Fin n → Bool, if op2130_logical_count_decision v (List.ofFn r) then (-1:ℝ) else 1) / (2:ℝ)^n

theorem op2130_sign_mean_recurrence (n : ℕ) :
    op2130_sign_mean true (n+1) = (1 + op2130_sign_mean false n)/2 ∧
    op2130_sign_mean false (n+1) = (-1 + op2130_sign_mean true n)/2 := by
  constructor
  · unfold op2130_sign_mean
    rw [op2130_logical_sum_bool_tapes_succ]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, op2130_logical_count_decision,
      Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte, Finset.sum_add_distrib]
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    rw [pow_succ]
    have hn : (2:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    push_cast
    ring
  · unfold op2130_sign_mean
    rw [op2130_logical_sum_bool_tapes_succ]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, op2130_logical_count_decision,
      Bool.false_or, Bool.true_or, ↓reduceIte, Finset.sum_add_distrib, if_true]
    try simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    rw [pow_succ]
    have hn : (2:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    push_cast
    simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

noncomputable def op2130_nondecd_mean (v : Bool) (n t : ℕ) : ℝ := by
  classical
  exact (∑ r : Fin n → Bool,
    if op2130_nondecd_prefix v t r then
      (if op2130_logical_count_decision v (List.ofFn r) then (-1:ℝ) else 1) else 0) / (2:ℝ)^(n-t)

theorem op2130_nondecd_mean_succ (v : Bool) (n t : ℕ) :
    op2130_nondecd_mean v (n+1) (t+1) = op2130_nondecd_mean (!v) n t := by
  classical
  unfold op2130_nondecd_mean
  have hh := op2130_decision_prefix_sum_succ n t v (fun b => if b then (-1:ℝ) else 1)
  rw [show n+1-(t+1)=n-t by omega]
  congr 1

def op2130_toggle : Bool → ℕ → Bool
  | v, 0 => v
  | v, t+1 => op2130_toggle (!v) t

theorem op2130_nondecd_mean_strip (v : Bool) (n t : ℕ) :
    op2130_nondecd_mean v (n+t) t = op2130_sign_mean (op2130_toggle v t) n := by
  induction t generalizing v with
  | zero =>
      classical
      simp [op2130_nondecd_mean,op2130_sign_mean,op2130_nondecd_prefix,op2130_toggle]
      congr 1
  | succ t ih =>
      rw [show n+(t+1) = (n+t)+1 by omega, op2130_nondecd_mean_succ]
      simpa only [op2130_toggle] using ih (!v)

theorem op2130_sign_mean_bounds (n : ℕ) :
    -1 ≤ op2130_sign_mean true n ∧ op2130_sign_mean true n ≤ 1 ∧
    -1 ≤ op2130_sign_mean false n ∧ op2130_sign_mean false n ≤ 1 ∧
    0 ≤ op2130_sign_mean true n ∧ (0 < n → op2130_sign_mean false n ≤ 0) := by
  induction n with
  | zero =>
      have he : ∀ r : Fin 0 → Bool, List.ofFn r = [] := by intro r; simp
      simp [op2130_sign_mean,he,op2130_logical_count_decision]
  | succ n ih =>
      have hr := op2130_sign_mean_recurrence n
      rcases ih with ⟨a,b,c,d,e,f⟩
      rw [hr.1,hr.2]
      refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> try linarith
      intro _
      linarith

theorem op2130_toggle_eq (v : Bool) (t : ℕ) :
    op2130_toggle v t = if t%2=0 then v else !v := by
  induction t generalizing v with
  | zero => simp [op2130_toggle]
  | succ t ih =>
      simp only [op2130_toggle, ih]
      by_cases ht : t%2=0
      · have hs : (t+1)%2 ≠ 0 := by omega
        cases v <;> simp [ht,hs]
      · have hs : (t+1)%2=0 := by omega
        cases v <;> simp [ht,hs]

theorem op2130_nondecd_increment_lower (N t : ℕ) (hodd : N%2=1) (ht : t < N) :
    (1:ℝ)/2 ≤ |op2130_nondecd_mean false N (t+1) - op2130_nondecd_mean false N t| := by
  let n := N-(t+1)
  have hN : N = n+(t+1) := by dsimp [n]; omega
  have hn1 : N = (n+1)+t := by omega
  have qbefore := op2130_nondecd_mean_strip false (n+1) t
  have qafter := op2130_nondecd_mean_strip false n (t+1)
  rw [← hn1] at qbefore
  rw [← hN] at qafter
  rw [qbefore,qafter]
  rw [op2130_toggle_eq,op2130_toggle_eq]
  by_cases he : t%2=0
  · have ho : (t+1)%2 ≠ 0 := by omega
    simp only [he,ho,if_true,if_false,Bool.not_false]
    have hr := (op2130_sign_mean_recurrence n).2
    rw [hr]
    have hb := (op2130_sign_mean_bounds n).2.2.2.2.1
    rw [abs_of_nonneg (by linarith : 0 ≤ op2130_sign_mean true n - (-1 + op2130_sign_mean true n)/2)]
    linarith
  · have ho : (t+1)%2=0 := by omega
    have hp : 0 < n := by dsimp [n]; omega
    simp only [he,ho,if_true,if_false,Bool.not_false]
    have hr := (op2130_sign_mean_recurrence n).1
    rw [hr]
    have hb := (op2130_sign_mean_bounds n).2.2.2.2.2 hp
    rw [abs_of_nonpos (by linarith : op2130_sign_mean false n - (1 + op2130_sign_mean false n)/2 ≤ 0)]
    linarith

theorem op2130_nondecd_variation_lower (N : ℕ) (hodd : N%2=1) :
    (N:ℝ)/4 ≤ ∑ t ∈ Finset.range N,
      (op2130_nondecd_mean false N (t+1) - op2130_nondecd_mean false N t)^2 := by
  have each : ∀ t ∈ Finset.range N, (1:ℝ)/4 ≤
      (op2130_nondecd_mean false N (t+1) - op2130_nondecd_mean false N t)^2 := by
    intro t ht
    have h := op2130_nondecd_increment_lower N t hodd (Finset.mem_range.mp ht)
    have hsq := sq_abs (op2130_nondecd_mean false N (t+1) - op2130_nondecd_mean false N t)
    nlinarith [sq_nonneg (|op2130_nondecd_mean false N (t+1) - op2130_nondecd_mean false N t| - 1/2)]
  have hs := Finset.sum_le_sum (s := Finset.range N) each
  simpa [div_eq_mul_inv] using hs

theorem op2130_outer_eq_count (v : Bool) (xs : List Bool) :
    op2130_outer_decision v xs = op2130_logical_count_decision v xs := by
  induction xs generalizing v with
  | nil => cases v <;> rfl
  | cons x xs ih => cases v <;> simp [op2130_outer_decision,op2130_logical_count_decision,ih]

theorem op2130_nondecd_bit_false (t : ℕ) :
    op2130_nondecd_bit false t = (t%2 == 1) := by
  by_cases ht : t%2=0
  · have ho : t%2 ≠ 1 := by omega
    simp [op2130_nondecd_bit,ht,ho]
  · have ho : t%2=1 := by omega
    simp [op2130_nondecd_bit,ht,ho]

theorem op2130_decision_list_conditional_variation (N : ℕ) (hN : 3 ≤ N) (hodd : N % 2 = 1) : let X : (Fin N → Bool) → ℝ := fun r => if op2130_outer_decision false (List.ofFn r) then -1 else 1; let Q : ℕ → (Fin N → Bool) → ℝ := fun t a => (∑ b : Fin N → Bool, if ∀ i : Fin N, i.val < t → b i = a i then X b else 0) / (2 : ℝ) ^ (N-t); let r : Fin N → Bool := fun i => i.val % 2 == 1; ((N : ℝ)-2)/4 ≤ ∑ t ∈ Finset.range N, (Q (t+1) r - Q t r) ^ 2 := by
  classical
  let X : (Fin N → Bool) → ℝ := fun r => if op2130_outer_decision false (List.ofFn r) then -1 else 1
  let Q : ℕ → (Fin N → Bool) → ℝ := fun t a =>
    (∑ b : Fin N → Bool, if ∀ i : Fin N, i.val < t → b i = a i then X b else 0) / (2 : ℝ) ^ (N-t)
  let r : Fin N → Bool := fun i => i.val % 2 == 1
  have hQ (t : ℕ) : Q t r = op2130_nondecd_mean false N t := by
    dsimp only [Q,r,op2130_nondecd_mean]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    have hc : (∀ i : Fin N, i.val < t → b i = (i.val%2 == 1)) ↔
        op2130_nondecd_prefix false t b := by
      simp only [op2130_nondecd_prefix,op2130_nondecd_bit_false]
    rw [if_congr hc rfl rfl]
    simp only [X,op2130_outer_eq_count]
  change ((N:ℝ)-2)/4 ≤ ∑ t ∈ Finset.range N, (Q (t+1) r - Q t r)^2
  simp only [hQ]
  have hh := op2130_nondecd_variation_lower N hodd
  linarith
