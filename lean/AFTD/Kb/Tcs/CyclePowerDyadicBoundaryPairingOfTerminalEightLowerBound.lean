import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerSevenTightTypeSequenceOneIffSix
import AFTD.Kb.Tcs.CyclePowerDyadicRankCountBalance
import AFTD.Kb.Tcs.PeriodicCountEqOfShiftBalanceOfLowerBound

/-!
# cycle_power_dyadic_boundary_pairing_of_terminal_eight_lower_bound

Topic: combinatorics   Node: 2a5caa290d3d

Provenance: helper lemma. Conditional uniform reduction in OP-205 / RT-1 following arXiv:2610.15635. This does not prove the terminal-count lower bound, constant-count pruning, the classification of covers, or the main conjecture. No research advance is claimed.

For any dyadic radius at least eight, a periodic tight Boolean class model with exact dyadic-edge coverage and all ordinary coverage has paired boundary bits whenever its terminal eight-position compressed active count is at least four at every integer vertex.
-/

open Finset

theorem cycle_power_eight_integer_boundary_of_count
    (z : ℤ → ℕ → Bool)
    (hcount : ∀ v : ℤ, (range 8).sum (fun a => (z (v - (a : ℤ)) a).toNat) = 4)
    (hexact : ∀ j < 3, ∀ v : ℤ, (range (2 ^ j)).sum (fun a =>
      (z (v - (a : ℤ)) a && z (v - (a : ℤ)) (a + 8 - 2 ^ j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 8 → ∀ v : ℤ,
      ∃ a < 8 - d, z (v - (a : ℤ)) a = true ∧ z (v - (a : ℤ)) (a + d) = true)
    (h51 : ∀ p, z p 5 = true → z p 1 = true)
    (h26 : ∀ p, z p 2 = true → z p 6 = true) :
    ∀ p, z p 1 = z p 6 := by
  have hends : ∀ p, z p 0 = true ∧ z p 7 = true := by
    intro p
    have h := hexact 0 (by omega) p
    norm_num [sum_range_succ] at h
    clear hcount hexact hcover h51 h26
    cases h0 : z p 0 <;> cases h7 : z p 7 <;> simp_all
  intro p
  let y : ℤ → Fin 8 → Bool := fun a j => z (p + a) j
  suffices hh : y 0 1 = y 0 6 by simpa [y] using hh
  apply cycle_power_seven_tight_type_sequence_core y
    (fun a => (hends _).1) (fun a => (hends _).2)
  · rintro o _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    have h := hcount (p + o)
    simp only [sum_range_succ, sum_range_zero, zero_add] at h
    norm_num only [Nat.cast_ofNat, sub_zero] at h
    have h0 := (hends (p + o)).1
    have h7 := (hends (p + o - 7)).2
    simp only [h0, h7, Bool.toNat_true] at h
    dsimp [y]
    simp only [add_sub_assoc] at h ⊢
    omega
  · rintro o _ _ _ rfl rfl rfl
    have h := hexact 2 (by omega) (p + o)
    norm_num only [pow_succ, pow_zero, Nat.reduceMul, sum_range_succ, sum_range_zero,
      zero_add, Nat.reduceAdd, Nat.reduceSub] at h
    simp only [sub_zero] at h
    simp only [(hends (p + o)).1, (hends (p + o - 3)).2,
      Bool.true_and, Bool.and_true] at h
    dsimp [y]
    simpa only [add_sub_assoc] using h
  · rintro o _ rfl
    have h := hexact 1 (by omega) (p + o)
    norm_num only [pow_succ, pow_zero, Nat.reduceMul, sum_range_succ, sum_range_zero,
      zero_add, Nat.reduceAdd, Nat.reduceSub] at h
    simp only [sub_zero] at h
    simp only [(hends (p + o)).1, (hends (p + o - 1)).2,
      Bool.true_and, Bool.and_true] at h
    dsimp [y]
    simp only [add_sub_assoc] at h ⊢
    omega
  · intro d o hd
    have hdb : 1 ≤ d ∧ d < 8 := by
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> omega
    obtain ⟨a, ha, h1, h2⟩ := hcover d hdb.1 hdb.2 (p + o)
    let j : Fin 8 := ⟨a, by omega⟩
    refine ⟨j, ?_, ?_, ?_⟩
    · change a + d ≤ 7
      omega
    · dsimp [y, j]
      simpa only [add_sub_assoc] using h1
    · dsimp [y, j]
      simpa only [add_sub_assoc] using h2
  · intro a
    exact h51 (p + a)
  · intro a
    exact h26 (p + a)

theorem cycle_power_dyadic_boundary_pairing_of_terminal_eight_count
    (m : ℕ) (hm : 3 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (range (2 ^ m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2 ^ j)).sum (fun a =>
      (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2 ^ m → ∀ v : ℤ,
      ∃ a < 2 ^ m - d, x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + d) = true)
    (hterminal : ∀ v : ℤ, (range 8).sum (fun a =>
      (if a < 4 then x (v - (a : ℤ)) a else
        x (v - (a : ℤ)) (a + (2 ^ m - 8))).toNat) = 4) :
    ∀ p : ℤ, x p 1 = x p (2 ^ m - 2) := by
  have hD : 8 ≤ 2 ^ m := by
    have h : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hm
    norm_num at h
    exact h
  let z : ℤ → ℕ → Bool := fun p a =>
    if a < 4 then x p a else x p (a + (2 ^ m - 8))
  have he : ∀ j < 3, ∀ v : ℤ, (range (2 ^ j)).sum (fun a =>
      (z (v - (a : ℤ)) a && z (v - (a : ℤ)) (a + 8 - 2 ^ j)).toNat) = 1 := by
    intro j hj v
    have hj4 : 2 ^ j ≤ 4 := by
      have h : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : j ≤ 2)
      norm_num at h
      exact h
    refine Eq.trans ?_ (hexact j (by omega) v)
    apply sum_congr rfl
    intro a ha
    have ha' := mem_range.mp ha
    have hl : a < 4 := by omega
    have hr : ¬a + 8 - 2 ^ j < 4 := by omega
    have hi : a + 8 - 2 ^ j + (2 ^ m - 8) = a + 2 ^ m - 2 ^ j := by omega
    simp only [z, if_pos hl, if_neg hr, hi]
  have hc : ∀ d : ℕ, 1 ≤ d → d < 8 → ∀ v : ℤ,
      ∃ a < 8 - d, z (v - (a : ℤ)) a = true ∧
        z (v - (a : ℤ)) (a + d) = true := by
    intro d hd hd8 v
    by_cases hm3 : m = 3
    · subst m
      simpa [z] using hcover d hd (by norm_num; omega) v
    have hrank : 3 < m := by omega
    let delta := 2 ^ m - 8 + d
    have hdelta : 1 ≤ delta ∧ delta < 2 ^ m := by dsimp [delta]; omega
    obtain ⟨a, ha, h1, h2⟩ := hcover delta hdelta.1 hdelta.2 v
    have ha8 : a < 8 - d := by dsimp [delta] at ha; omega
    have hidx : a + delta = a + d + (2 ^ m - 8) := by dsimp [delta]; omega
    rw [hidx] at h2
    have hp := cycle_power_dyadic_tight_class_parent m 3 (by omega) hrank
      (x (v - (a : ℤ))) (htight _)
    refine ⟨a, ha8, ?_, ?_⟩
    · by_cases hl : a < 4
      · simpa only [z, if_pos hl] using h1
      · have hh := (hp a (by norm_num; omega)).2 (by norm_num; omega) h1
        have hi : a + 2 ^ m - 2 ^ 3 = a + (2 ^ m - 8) := by norm_num; omega
        simpa only [z, if_neg hl, hi] using hh
    · by_cases hl : a + d < 4
      · have hi : a + d + 2 ^ m - 2 ^ 3 = a + d + (2 ^ m - 8) := by norm_num; omega
        have hh := (hp (a + d) (by norm_num; omega)).1 (by norm_num; omega)
          (by simpa only [hi] using h2)
        simpa only [z, if_pos hl] using hh
      · simpa only [z, if_neg hl] using h2
  have h51 : ∀ p, z p 5 = true → z p 1 = true := by
    intro p h
    have hp := (cycle_power_dyadic_tight_class_parent m 2 (by omega) (by omega)
      (x p) (htight p) 1 (by norm_num)).1 (by norm_num)
    norm_num only [pow_succ, pow_zero, Nat.reduceMul] at hp
    have hi : 1 + 2 ^ m - 4 = 5 + (2 ^ m - 8) := by omega
    rw [hi] at hp
    apply hp
    simpa [z] using h
  have h26 : ∀ p, z p 2 = true → z p 6 = true := by
    intro p h
    have hp := (cycle_power_dyadic_tight_class_parent m 2 (by omega) (by omega)
      (x p) (htight p) 2 (by norm_num)).2 (by norm_num)
    norm_num only [pow_succ, pow_zero, Nat.reduceMul] at hp
    have hi : 2 + 2 ^ m - 4 = 6 + (2 ^ m - 8) := by omega
    have hh := hp (by simpa [z] using h)
    rw [hi] at hh
    simpa [z] using hh
  have hcount : ∀ v : ℤ, (range 8).sum (fun a => (z (v - (a : ℤ)) a).toNat) = 4 := hterminal
  have hb := cycle_power_eight_integer_boundary_of_count z hcount he hc h51 h26
  intro p
  have hi : 6 + (2 ^ m - 8) = 2 ^ m - 2 := by omega
  simpa [z, hi] using hb p

theorem cycle_power_dyadic_boundary_pairing_of_terminal_eight_lower_bound
    (m n : ℕ) (hm : 3 ≤ m) (hn : 0 < n) (x : ℤ → ℕ → Bool)
    (hperiod : ∀ p a, x (p + (n : ℤ)) a = x p a)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (range (2 ^ m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2 ^ j)).sum (fun a =>
      (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2 ^ m → ∀ v : ℤ,
      ∃ a < 2 ^ m - d, x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + d) = true)
    (hlower : ∀ v : ℤ, 4 ≤ (range 8).sum (fun a =>
      (if a < 4 then x (v - (a : ℤ)) a else
        x (v - (a : ℤ)) (a + (2 ^ m - 8))).toNat)) :
    ∀ p : ℤ, x p 1 = x p (2 ^ m - 2) := by
  have hD : 8 ≤ 2 ^ m := by
    have h : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hm
    norm_num at h
    exact h
  have hends : ∀ p, x p 0 = true ∧ x p (2 ^ m - 1) = true := by
    intro p
    have h := hexact 0 (by omega) p
    norm_num [sum_range_succ] at h
    clear hperiod htight hexact hcover hlower
    cases h0 : x p 0 <;> cases hlast : x p (2 ^ m - 1) <;> simp_all
  have h1 : ∀ v : ℤ, (x (v - 1) 1).toNat + (x v (2 ^ m - 2)).toNat = 1 := by
    intro v
    have h := cycle_power_dyadic_rank_count_balance m 1 (by omega) (by omega) x htight
      (hexact 1 (by omega)) v
    norm_num [sum_range_succ] at h
    simpa using h
  have h2 : ∀ v : ℤ,
      (x v (2 ^ m - 4)).toNat + (x (v - 1) (2 ^ m - 3)).toNat +
        (x (v - 2) 2).toNat + (x (v - 3) 3).toNat = 1 := by
    intro v
    have h := cycle_power_dyadic_rank_count_balance m 2 (by omega) (by omega) x htight
      (hexact 2 (by omega)) v
    norm_num [sum_range_succ] at h
    have hs : v + ((2 ^ m - 4 : ℕ) : ℤ) - (((2 ^ m - 4 : ℕ) : ℤ) + 1) = v - 1 := by
      ring
    have hi : (2 ^ m - 4 : ℕ) + 1 = 2 ^ m - 3 := by omega
    rw [hs, hi] at h
    omega
  let C : ℤ → ℕ := fun v => (range 8).sum (fun a =>
    (if a < 4 then x (v - (a : ℤ)) a else
      x (v - (a : ℤ)) (a + (2 ^ m - 8))).toNat)
  let F : ℤ → ℕ := fun v =>
    (x v (2 ^ m - 2)).toNat + (x (v - 2) (2 ^ m - 2)).toNat +
      (x (v - 4) (2 ^ m - 2)).toNat +
      (x v (2 ^ m - 4)).toNat + (x (v - 1) (2 ^ m - 3)).toNat +
      (x (v - 2) (2 ^ m - 4)).toNat + (x (v - 3) (2 ^ m - 3)).toNat
  have hbal : ∀ v, C v + F v = 4 + F (v - 2) := by
    intro v
    have he1 := h1 v
    have he2 := h2 v
    have hi4 : 4 + (2 ^ m - 8) = 2 ^ m - 4 := by omega
    have hi5 : 5 + (2 ^ m - 8) = 2 ^ m - 3 := by omega
    have hi6 : 6 + (2 ^ m - 8) = 2 ^ m - 2 := by omega
    have hi7 : 7 + (2 ^ m - 8) = 2 ^ m - 1 := by omega
    have hz := (hends v).1
    have hl := (hends (v - 7)).2
    norm_num [C, F, sum_range_succ, hi4, hi5, hi6, hi7, hz, hl, sub_sub]
    omega
  have hpF : Function.Periodic F (n : ℤ) := by
    intro v
    have hs : ∀ (d : ℤ) (a : ℕ), x ((v + (n : ℤ)) - d) a = x (v - d) a := by
      intro d a
      rw [show v + (n : ℤ) - d = (v - d) + (n : ℤ) by ring, hperiod]
    dsimp [F]
    rw [hperiod, hs, hs, hperiod, hs, hs, hs]
  have heq : ∀ v, C v = 4 :=
    periodic_count_eq_of_shift_balance_of_lower_bound n 4 hn (-2) C F hpF
      (by intro v; simpa only [sub_eq_add_neg] using hbal v) hlower
  exact cycle_power_dyadic_boundary_pairing_of_terminal_eight_count m hm x htight
    hexact hcover heq
