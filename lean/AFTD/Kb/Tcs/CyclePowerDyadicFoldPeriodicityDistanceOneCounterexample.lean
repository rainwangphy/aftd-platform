import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_fold_periodicity_distance_one_counterexample

Topic: combinatorics   Node: 858a8784bc7f

Provenance: helper lemma. RT-1, defective-half fold-count reduction

There is an exponent-three tight zero-phase dyadic profile with exact lower-rank owners, the defective top-owner and active-count equations, periodic corrected lower count, and coverage at distance one, but with a defect at zero. The profile does not cover distance two at zero, so it does not satisfy full coverage.
-/

namespace RT1In723
open Finset
def rt1_short_x (p : ℤ) (a : ℕ) : Bool :=
  (if p = -3 then 147 else if p % 4 = 0 then 139 else if p % 4 = 1 then 155 else if p % 4 = 2 then 147 else 131 : ℕ).testBit a

def rt1_short_e (v : ℤ) : Bool := decide (v = 0)

theorem rt1_short_tight (p : ℤ) : cycle_power_dyadic_class_weight 3 (rt1_short_x p) = (range 8).sum (fun a => (rt1_short_x p a).toNat) := by
  by_cases h : p = -3
  · subst p; decide
  · have h0 : 0 ≤ p % 4 := Int.emod_nonneg _ (by norm_num)
    have h4 : p % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    generalize hp : p % 4 = r at *
    have hx : rt1_short_x p = (fun a => (if r = 0 then 139 else if r = 1 then 155 else if r = 2 then 147 else 131 : ℕ).testBit a) := by
      funext a; simp [rt1_short_x, h, hp]
    rw [hx]
    interval_cases r <;> decide

theorem rt1_short_count (v : ℤ) : (range 8).sum (fun a => (rt1_short_x (v-(a:ℤ)) a).toNat) + (rt1_short_e v).toNat = 4 := by
  by_cases hs : -12 ≤ v ∧ v ≤ 12
  · obtain ⟨hlo,hhi⟩ := hs
    interval_cases v <;> decide
  · have hv : v < -12 ∨ 12 < v := by omega
    rcases hv with hv | hv
    all_goals
      have h0 : 0 ≤ v % 4 := Int.emod_nonneg _ (by norm_num)
      have h4 : v % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
      generalize hp : v % 4 = r at *
      have hx (a : ℕ) (ha : a < 8) : rt1_short_x (v-(a:ℤ)) = fun b => (if (r-(a:ℤ)) % 4 = 0 then 139 else if (r-(a:ℤ)) % 4 = 1 then 155 else if (r-(a:ℤ)) % 4 = 2 then 147 else 131 : ℕ).testBit b := by
        funext b
        have hn : v-(a:ℤ) ≠ -3 := by omega
        simp [rt1_short_x, hn, Int.sub_emod, hp]
      have hz : v ≠ 0 := by omega
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hx 0 (by omega), hx 1 (by omega), hx 2 (by omega), hx 3 (by omega), hx 4 (by omega), hx 5 (by omega), hx 6 (by omega), hx 7 (by omega), rt1_short_e, hz, decide_false]
      interval_cases r <;> decide

theorem rt1_short_pairs_and_balance (v : ℤ) :
  (range 1).sum (fun a => (rt1_short_x (v-(a:ℤ)) a && rt1_short_x (v-(a:ℤ)) (a+7)).toNat) = 1 ∧
  (range 2).sum (fun a => (rt1_short_x (v-(a:ℤ)) a && rt1_short_x (v-(a:ℤ)) (a+6)).toNat) = 1 ∧
  (range 4).sum (fun a => (rt1_short_x (v-(a:ℤ)) a && rt1_short_x (v-(a:ℤ)) (a+4)).toNat) + (rt1_short_e v).toNat = 1 ∧
  (range 4).sum (fun a => (rt1_short_x (v-(a:ℤ)) a).toNat) + (rt1_short_e v).toNat =
    (range 4).sum (fun a => (rt1_short_x (v+4-(a:ℤ)) a).toNat) + (rt1_short_e (v+4)).toNat := by
  by_cases hs : -12 ≤ v ∧ v ≤ 12
  · obtain ⟨hlo,hhi⟩ := hs
    interval_cases v <;> decide
  · have hv : v < -12 ∨ 12 < v := by omega
    rcases hv with hv | hv
    all_goals
      have h0 : 0 ≤ v % 4 := Int.emod_nonneg _ (by norm_num)
      have h4 : v % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
      generalize hp : v % 4 = r at *
      have hx (d : ℤ) (hd : -7 ≤ d ∧ d ≤ 4) : rt1_short_x (v+d) = fun b => (if (r+d) % 4 = 0 then 139 else if (r+d) % 4 = 1 then 155 else if (r+d) % 4 = 2 then 147 else 131 : ℕ).testBit b := by
        funext b
        have hn : v+d ≠ -3 := by omega
        simp [rt1_short_x, hn, Int.add_emod, hp]
      have hz : v ≠ 0 := by omega
      have hz4 : v+4 ≠ 0 := by omega
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, rt1_short_e, hz, hz4, decide_false]
      norm_num only [Nat.cast_ofNat] at *
      simp only [show v - (0:ℤ) = v+0 by omega, show v - (1:ℤ) = v+(-1) by omega, show v - (2:ℤ) = v+(-2) by omega, show v - (3:ℤ) = v+(-3) by omega, show v+4-(0:ℤ) = v+4 by omega, show v+4-(1:ℤ) = v+3 by omega, show v+4-(2:ℤ) = v+2 by omega, show v+4-(3:ℤ) = v+1 by omega,
        hx 0 (by omega), hx (-1) (by omega), hx (-2) (by omega), hx (-3) (by omega), hx 1 (by omega), hx 2 (by omega), hx 3 (by omega), hx 4 (by omega)]
      interval_cases r <;> decide

theorem rt1_short_cover_one (v : ℤ) : ∃ a : ℕ, a < 7 ∧ rt1_short_x (v-(a:ℤ)) a = true ∧ rt1_short_x (v-(a:ℤ)) (a+1) = true := by
  refine ⟨0, by decide, ?_, ?_⟩ <;> simp only [Nat.cast_zero, sub_zero, Nat.zero_add, rt1_short_x] <;> split_ifs <;> decide


end RT1In723
open RT1In723

theorem cycle_power_dyadic_fold_periodicity_distance_one_counterexample :
  ∃ (y : ℤ → ℕ → Bool) (e : ℤ → Bool),
    (∀ p, cycle_power_dyadic_class_weight 3 (y p) = (Finset.range 8).sum (fun a => (y p a).toNat)) ∧
    (∀ j < 2, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+8-2^j)).toNat) = 1) ∧
    (∀ v : ℤ, (Finset.range 4).sum (fun a => (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+4)).toNat) + (e v).toNat = 1) ∧
    (∀ v : ℤ, (Finset.range 8).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat = 4) ∧
    (∀ v : ℤ, (Finset.range 4).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat = (Finset.range 4).sum (fun a => (y (v+4-(a:ℤ)) a).toNat) + (e (v+4)).toNat) ∧
    (∀ v : ℤ, ∃ a : ℕ, a < 7 ∧ y (v-(a:ℤ)) a = true ∧ y (v-(a:ℤ)) (a+1) = true) ∧
    e 0 = true ∧ ¬ (∃ a : ℕ, a < 6 ∧ y (-(a:ℤ)) a = true ∧ y (-(a:ℤ)) (a+2) = true) := by
  refine ⟨rt1_short_x, rt1_short_e, rt1_short_tight, ?_, ?_, rt1_short_count, ?_, rt1_short_cover_one, ?_, ?_⟩
  · intro j hj v
    have h := rt1_short_pairs_and_balance v
    interval_cases j <;> norm_num at *
    · exact h.1
    · exact h.2.1
  · intro v
    exact (rt1_short_pairs_and_balance v).2.2.1
  · intro v
    exact (rt1_short_pairs_and_balance v).2.2.2
  · decide
  · decide
