import AFTD.Prelude

/-!
# op874_cycle_difference_labels_integrate

Topic: graphs   Node: 7594c228862f

Provenance: helper lemma. OP-874: four high colors represented as two-bit vectors

On any nonempty cycle, assign one of the three nonzero two-bit differences to each position. If every difference occurs with the same parity as the cycle length, these differences integrate to a cyclic assignment of four two-bit colors, with neighboring colors distinct and with the prescribed difference at every position.
-/

open BigOperators

def op874_cycle_diffBB (t : Fin 3) : Bool × Bool :=
  match t with
  | 0 => (true, false)
  | 1 => (false, true)
  | 2 => (true, true)

def op874_cycle_fromBB (v : Bool × Bool) : Fin 4 :=
  ⟨(if v.1 then 1 else 0) + 2 * (if v.2 then 1 else 0), by
    cases v.1 <;> cases v.2 <;> decide⟩

lemma op874_cycle_fromBB_diffBB (t : Fin 3) : (op874_cycle_fromBB (op874_cycle_diffBB t)).val = t.val + 1 := by
  fin_cases t <;> rfl

lemma op874_cycle_xor_fromBB (v w : Bool × Bool) :
    Nat.xor (op874_cycle_fromBB v).val (op874_cycle_fromBB (v + w)).val = (op874_cycle_fromBB w).val := by
  cases v; cases w; rename_i a b c d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma op874_cycle_xor_fromBB_zero (v : Bool × Bool) :
    Nat.xor (op874_cycle_fromBB v).val (op874_cycle_fromBB 0).val = (op874_cycle_fromBB v).val := by
  cases v; rename_i a b
  cases a <;> cases b <;> rfl

lemma op874_cycle_bool_prod_eq_of_add_eq_zero {v w : Bool × Bool} (h : v + w = 0) : v = w := by
  cases v; cases w; rename_i a b c d
  ext <;> (revert a b c d; decide)

lemma op874_cycle_smul_bool_prod (c : ℕ) (x : Bool × Bool) : c • x = (c % 2) • x := by
  have h2 : (2 : ℕ) • x = 0 := by
    cases x; rename_i a b
    ext <;> (cases a <;> cases b <;> rfl)
  have hd : c = c / 2 * 2 + c % 2 := by omega
  nth_rw 1 [hd]
  rw [add_smul, mul_smul, h2, smul_zero, zero_add]

lemma op874_cycle_sum_diffBB : ∑ t : Fin 3, op874_cycle_diffBB t = 0 := by
  change op874_cycle_diffBB 0 + op874_cycle_diffBB 1 + op874_cycle_diffBB 2 = 0
  ext <;> decide

lemma op874_cycle_sum_d_zero (n : ℕ) [NeZero n] (d : Fin n → Fin 3)
    (hparity : ∀ t : Fin 3, ((Finset.univ : Finset (Fin n)).filter fun i => d i = t).card % 2 = n % 2) :
    ∑ i : Fin n, op874_cycle_diffBB (d i) = 0 := by
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset (Fin n)) d op874_cycle_diffBB]
  have h_const : ∀ j : Fin 3, (∑ i ∈ Finset.univ with d i = j, op874_cycle_diffBB j) =
      (((Finset.univ : Finset (Fin n)).filter fun i => d i = j).card % 2) • op874_cycle_diffBB j := by
    intro j
    rw [Finset.sum_const, op874_cycle_smul_bool_prod]
  simp_rw [h_const, hparity]
  rw [← Finset.smul_sum, op874_cycle_sum_diffBB, smul_zero]

theorem op874_cycle_difference_labels_integrate (n : ℕ) [NeZero n] (d : Fin n → Fin 3) (hparity : ∀ t : Fin 3, ((Finset.univ : Finset (Fin n)).filter fun i => d i = t).card % 2 = n % 2) : ∃ h : Fin n → Fin 4, ∀ i : Fin n, h i ≠ h (i + 1) ∧ Nat.xor (h i).val (h (i + 1)).val = (d i).val + 1 := by
  let F : ℕ → Bool × Bool := fun j => if h : j < n then op874_cycle_diffBB (d ⟨j, h⟩) else 0
  let S : ℕ → Bool × Bool := fun k => ∑ j ∈ Finset.range k, F j
  have hSn : S n = 0 := by
    have h1 : S n = ∑ i : Fin n, op874_cycle_diffBB (d i) := by
      exact (Finset.sum_fin_eq_sum_range (fun i => op874_cycle_diffBB (d i))).symm
    rw [h1, op874_cycle_sum_d_zero n d hparity]
  have hS0 : S 0 = 0 := Finset.sum_range_zero F
  use fun i => op874_cycle_fromBB (S i.val)
  intro i
  have hF : F i.val = op874_cycle_diffBB (d i) := by
    dsimp [F]
    exact if_pos i.isLt
  have hS_succ : S (i.val + 1) = S i.val + op874_cycle_diffBB (d i) := by
    dsimp [S]
    rw [Finset.sum_range_succ, hF]
  have hxor : Nat.xor (op874_cycle_fromBB (S i.val)).val (op874_cycle_fromBB (S (i + 1).val)).val = (d i).val + 1 := by
    by_cases hlt : i.val + 1 < n
    · have h_succ : (i + 1).val = i.val + 1 := by
        have hn : 1 < n := by omega
        rw [Fin.val_add, Fin.val_one' n, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hlt]
      rw [h_succ, hS_succ, op874_cycle_xor_fromBB, op874_cycle_fromBB_diffBB]
    · have heq : i.val + 1 = n := by
        have := i.isLt
        omega
      have h_zero : (i + 1).val = 0 := by
        by_cases hn : n = 1
        · subst hn
          have : i = 0 := Subsingleton.elim _ _
          subst this
          rfl
        · have hn1 : 1 < n := by omega
          rw [Fin.val_add, Fin.val_one' n, Nat.mod_eq_of_lt hn1, heq, Nat.mod_self]
      rw [h_zero, hS0]
      have hS_eq : S i.val = op874_cycle_diffBB (d i) := by
        have htmp := hS_succ
        rw [heq, hSn] at htmp
        exact op874_cycle_bool_prod_eq_of_add_eq_zero htmp.symm
      rw [hS_eq, op874_cycle_xor_fromBB_zero, op874_cycle_fromBB_diffBB]
  refine ⟨?_, hxor⟩
  intro h_eq
  have h_val_eq : (op874_cycle_fromBB (S i.val)).val = (op874_cycle_fromBB (S (i + 1).val)).val :=
    congrArg Fin.val h_eq
  have h_contr := hxor
  rw [h_val_eq] at h_contr
  have h_zero_xor : Nat.xor (op874_cycle_fromBB (S (i + 1).val)).val (op874_cycle_fromBB (S (i + 1).val)).val = 0 :=
    Nat.xor_self _
  rw [h_zero_xor] at h_contr
  omega
