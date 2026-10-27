import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique

/-!
# cycle_power_exact_owner_order_cut_inequality

Topic: combinatorics   Node: a995d1d62f3b

Provenance: helper lemma. Routine formal bridge for OP-205 / RT-1 owner-order LP route, experiment6658. The owner-order hypothesis is explicit; this does not prove it for optimal covers or prove the numerical LP certificate.

A nondecreasing sequence of unique exact-edge owner roots satisfies every cumulative cut inequality: the indicator of the next owner being at most a cut is no greater than the corresponding old indicator. This justifies the stochastic order cuts used in the exploratory linear relaxation.
-/

open Finset

theorem cycle_power_exact_owner_order_cut_inequality
    (D q : ℕ) (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (range q).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-q)).toNat) = 1)
    (horder : ∀ (v : ℤ) (a b : ℕ), a < q → b < q →
      x (v-(a : ℤ)) a = true → x (v-(a : ℤ)) (a+D-q) = true →
      x (v+1-(b : ℤ)) b = true → x (v+1-(b : ℤ)) (b+D-q) = true → b ≤ a+1) :
    ∀ v C : ℤ,
      (range q).sum (fun b => if v+1-(b : ℤ) ≤ C then
        (x (v+1-(b : ℤ)) b && x (v+1-(b : ℤ)) (b+D-q)).toNat else 0) ≤
      (range q).sum (fun a => if v-(a : ℤ) ≤ C then
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-q)).toNat else 0) := by
  intro v C
  by_cases hL : (range q).sum (fun b => if v+1-(b : ℤ) ≤ C then
      (x (v+1-(b : ℤ)) b && x (v+1-(b : ℤ)) (b+D-q)).toNat else 0) = 0
  · rw [hL]
    exact Nat.zero_le _
  · have hL_le_one : (range q).sum (fun b => if v+1-(b : ℤ) ≤ C then
        (x (v+1-(b : ℤ)) b && x (v+1-(b : ℤ)) (b+D-q)).toNat else 0) ≤ 1 := by
      have hle : (range q).sum (fun b => if v+1-(b : ℤ) ≤ C then
          (x (v+1-(b : ℤ)) b && x (v+1-(b : ℤ)) (b+D-q)).toNat else 0) ≤
        (range q).sum (fun b => (x (v+1-(b : ℤ)) b && x (v+1-(b : ℤ)) (b+D-q)).toNat) := by
        apply sum_le_sum
        intro i _
        split_ifs <;> omega
      rw [hexact (v + 1)] at hle
      exact hle
    obtain ⟨b, hb_mem, hb_ne⟩ := exists_ne_zero_of_sum_ne_zero hL
    rw [mem_range] at hb_mem
    have hb_props : v + 1 - (b : ℤ) ≤ C ∧
        x (v+1-(b : ℤ)) b = true ∧
        x (v+1-(b : ℤ)) (b+D-q) = true := by
      split_ifs at hb_ne with hC
      · have hbool : (x (v + 1 - (b : ℤ)) b && x (v + 1 - (b : ℤ)) (b + D - q)) = true := by
          revert hb_ne
          cases (x (v + 1 - (b : ℤ)) b && x (v + 1 - (b : ℤ)) (b + D - q)) <;> simp
        rw [Bool.and_eq_true] at hbool
        exact ⟨hC, hbool.1, hbool.2⟩
      · contradiction
    have hne_a : (range q).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-q)).toNat) ≠ 0 := by
      rw [hexact v]
      decide
    obtain ⟨a, ha_mem, ha_ne⟩ := exists_ne_zero_of_sum_ne_zero hne_a
    rw [mem_range] at ha_mem
    have ha_bool : (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + D - q)) = true := by
      revert ha_ne
      cases (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + D - q)) <;> simp
    rw [Bool.and_eq_true] at ha_bool
    have hba : b ≤ a + 1 :=
      horder v a b ha_mem hb_mem ha_bool.1 ha_bool.2 hb_props.2.1 hb_props.2.2
    have ha_le_C : v - (a : ℤ) ≤ C := by omega
    have hpos_a : (if v-(a : ℤ) ≤ C then
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-q)).toNat else 0) = 1 := by
      rw [if_pos ha_le_C, ha_bool.1, ha_bool.2]
      rfl
    have hone_le_R : 1 ≤ (range q).sum (fun a => if v-(a : ℤ) ≤ C then
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-q)).toNat else 0) := by
      have hle := @single_le_sum ℕ ℕ _ _ (fun a => if v-(a : ℤ) ≤ C then
          (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-q)).toNat else 0) (range q) _
          (fun i _ => Nat.zero_le _) a (mem_range.mpr ha_mem)
      rw [hpos_a] at hle
      exact hle
    exact le_trans hL_le_one hone_le_R
