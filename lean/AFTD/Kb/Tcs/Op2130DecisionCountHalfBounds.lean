import AFTD.Prelude

/-!
# op2130_decision_count_half_bounds

Topic: online_algorithms   Node: 380be3cdc3ad

Provenance: helper lemma. OP-2130, Boolean decision-list probability

Among fair Boolean tapes, a nonempty AND-rooted alternating decision list is true on at most half the tapes and an OR-rooted one on at least half. Helpers split a Boolean tape at its first bit and establish exact counting recurrences.
-/

set_option maxHeartbeats 1000000

theorem op2130_sum_bool_tapes_succ {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : (Fin (n+1) → Bool) → A) :
    (∑ r, f r) = ∑ s : Fin n → Bool, (f (Fin.cons false s) + f (Fin.cons true s)) := by
  classical
  calc
    (∑ r, f r) = ∑ p : Bool × (Fin n → Bool), f ((Fin.consEquiv fun _ => Bool) p) :=
      ((Fin.consEquiv fun _ => Bool).sum_comp f).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.consEquiv_apply, Finset.sum_add_distrib]
      ac_rfl

def op2130_count_decision : Bool → List Bool → Bool
  | _, [] => false
  | isAnd, b::bs => if isAnd then b && op2130_count_decision false bs else b || op2130_count_decision true bs

def op2130_decision_true_count (isAnd : Bool) (n : ℕ) : ℕ :=
  ∑ r : Fin n → Bool, if op2130_count_decision isAnd (List.ofFn r) then 1 else 0

theorem op2130_decision_count_recurrence (n : ℕ) :
    op2130_decision_true_count true (n+1) = op2130_decision_true_count false n ∧
    op2130_decision_true_count false (n+1) = 2^n + op2130_decision_true_count true n := by
  constructor
  · unfold op2130_decision_true_count
    rw [op2130_sum_bool_tapes_succ]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, op2130_count_decision,
      Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte, zero_add]
  · unfold op2130_decision_true_count
    rw [op2130_sum_bool_tapes_succ]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, op2130_count_decision,
      Bool.false_or, Bool.true_or, ↓reduceIte, add_comm 1, Finset.sum_add_distrib]
    simp [Fintype.card_fun, add_comm]

theorem op2130_decision_true_count_le (v : Bool) (n : ℕ) :
    op2130_decision_true_count v n ≤ 2^n := by
  unfold op2130_decision_true_count
  calc
    (∑ r : Fin n → Bool, if op2130_count_decision v (List.ofFn r) then 1 else 0) ≤
        ∑ _r : Fin n → Bool, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro r hr
      split <;> omega
    _ = 2^n := by simp

theorem op2130_decision_count_half_bounds (n : ℕ) :
    op2130_decision_true_count true (n+1) ≤ 2^n ∧
    2^n ≤ op2130_decision_true_count false (n+1) := by
  have h := op2130_decision_count_recurrence n
  constructor
  · rw [h.1]; exact op2130_decision_true_count_le false n
  · rw [h.2]; omega
