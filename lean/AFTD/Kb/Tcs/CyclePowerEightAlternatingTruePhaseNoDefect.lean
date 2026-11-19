import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerEightAlternatingFalsePhaseNoDefect
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_eight_alternating_true_phase_no_defect

Topic: combinatorics   Node: b4152e8e6a3c

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635; finite computations 29006, 29007 and 29023.

If the first inner bit alternates in a zero-phase defective exponent-three model, no defect can occur at a root where that bit is true.
-/

namespace RT1Phase1119
open RT1False942

theorem band1119 (a b : Bool) : (a && b).toNat ≤ a.toNat ∧ (a && b).toNat ≤ b.toNat := by
  cases a <;> cases b <;> decide
theorem ble1119 (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
theorem bimp1119 (a b : Bool) (h : a = true → b = true) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all
theorem btrue1119 {b : Bool} (h : b = true) : b.toNat = 1 := by simp [h]
theorem bfalse1119 {b : Bool} (h : b = false) : b.toNat = 0 := by simp [h]

theorem rk1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v w : ℤ) (hw : w = v - 1) :
    (x v 6).toNat + (x w 1).toNat = 1 := by
  subst hw; exact (rt1_false_semantics939 x e h).1 v

theorem tp1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) :
    (x v 4).toNat + (x v1 5).toNat + (x v2 2).toNat + (x v3 3).toNat + (e v).toNat = 1 := by
  subst h1 h2 h3; exact (rt1_false_semantics939 x e h).2.1 v

theorem ct1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 v4 v5 v6 v7 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4)
    (h5 : v5 = v - 5) (h6 : v6 = v - 6) (h7 : v7 = v - 7) :
    (x v 0).toNat + (x v1 1).toNat + (x v2 2).toNat + (x v3 3).toNat + (x v4 4).toNat +
      (x v5 5).toNat + (x v6 6).toNat + (x v7 7).toNat + (e v).toNat = 4 := by
  subst h1 h2 h3 h4 h5 h6 h7; exact (rt1_false_semantics939 x e h).2.2 v

theorem cv1_1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 v4 v5 v6 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4)
    (h5 : v5 = v - 5) (h6 : v6 = v - 6) :
    1 ≤ (x v 0 && x v 1).toNat + (x v1 1 && x v1 2).toNat + (x v2 2 && x v2 3).toNat +
      (x v3 3 && x v3 4).toNat + (x v4 4 && x v4 5).toNat + (x v5 5 && x v5 6).toNat +
      (x v6 6 && x v6 7).toNat := by
  subst h1 h2 h3 h4 h5 h6
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 1 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega

theorem cv2_1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 v4 v5 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4)
    (h5 : v5 = v - 5) :
    1 ≤ (x v 0 && x v 2).toNat + (x v1 1 && x v1 3).toNat + (x v2 2 && x v2 4).toNat +
      (x v3 3 && x v3 5).toNat + (x v4 4 && x v4 6).toNat + (x v5 5 && x v5 7).toNat := by
  subst h1 h2 h3 h4 h5
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 2 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega

theorem cv3_1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 v4 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4) :
    1 ≤ (x v 0 && x v 3).toNat + (x v1 1 && x v1 4).toNat + (x v2 2 && x v2 5).toNat +
      (x v3 3 && x v3 6).toNat + (x v4 4 && x v4 7).toNat := by
  subst h1 h2 h3 h4
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 3 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega

theorem cv5_1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) :
    1 ≤ (x v 0 && x v 5).toNat + (x v1 1 && x v1 6).toNat + (x v2 2 && x v2 7).toNat := by
  subst h1 h2
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 5 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega


theorem alt1119 (x : ℤ → ℕ → Bool) (halt : ∀ p : ℤ, x (p + 1) 1 = !(x p 1)) (p q : ℤ)
    (hq : q = p + 1) : (x p 1).toNat + (x q 1).toNat = 1 := by
  subst hq; rw [halt p]; cases x p 1 <;> decide

theorem true_origin1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0) (halt : ∀ p : ℤ, x (p + 1) 1 = !(x p 1))
    (h0 : x 0 1 = true) (he0 : e 0 = true) : False := by
  obtain ⟨hend, hp⟩ := rt1_bridge_base895 x e hm
  have := ct1119 x e hm (-2) (-3) (-4) (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := ct1119 x e hm 0 (-1) (-2) (-3) (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := ct1119 x e hm 2 1 0 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := cv2_1119 x e hm (-2) (-3) (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := cv2_1119 x e hm 0 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := rk1119 x e hm (-4) (-5) (by norm_num)
  have := rk1119 x e hm (-6) (-7) (by norm_num)
  have := rk1119 x e hm (-8) (-9) (by norm_num)
  have := tp1119 x e hm (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num)
  have := band1119 (x (-2) 0) (x (-2) 2)
  have := band1119 (x (-3) 1) (x (-3) 3)
  have := band1119 (x (-4) 2) (x (-4) 4)
  have := band1119 (x (-5) 3) (x (-5) 5)
  have := band1119 (x (-6) 4) (x (-6) 6)
  have := band1119 (x (-7) 5) (x (-7) 7)
  have := band1119 (x 0 0) (x 0 2)
  have := band1119 (x (-1) 1) (x (-1) 3)
  have := band1119 (x (-2) 2) (x (-2) 4)
  have := band1119 (x (-3) 3) (x (-3) 5)
  have := band1119 (x (-4) 4) (x (-4) 6)
  have := band1119 (x (-5) 5) (x (-5) 7)
  have := btrue1119 (hend (-9)).1
  have := btrue1119 (hend (-9)).2
  have := bimp1119 _ _ (hp (-9)).2.1
  have := bimp1119 _ _ (hp (-9)).2.2.2.2.1
  have := btrue1119 (hend (-8)).1
  have := btrue1119 (hend (-8)).2
  have := bimp1119 _ _ (hp (-8)).2.1
  have := bimp1119 _ _ (hp (-8)).2.2.2.2.1
  have := btrue1119 (hend (-7)).1
  have := btrue1119 (hend (-7)).2
  have := bimp1119 _ _ (hp (-7)).2.1
  have := bimp1119 _ _ (hp (-7)).2.2.2.2.1
  have := btrue1119 (hend (-6)).1
  have := btrue1119 (hend (-6)).2
  have := bimp1119 _ _ (hp (-6)).2.1
  have := bimp1119 _ _ (hp (-6)).2.2.2.2.1
  have := btrue1119 (hend (-5)).1
  have := btrue1119 (hend (-5)).2
  have := bimp1119 _ _ (hp (-5)).2.1
  have := bimp1119 _ _ (hp (-5)).2.2.2.2.1
  have := btrue1119 (hend (-4)).1
  have := btrue1119 (hend (-4)).2
  have := bimp1119 _ _ (hp (-4)).2.1
  have := bimp1119 _ _ (hp (-4)).2.2.2.2.1
  have := btrue1119 (hend (-3)).1
  have := btrue1119 (hend (-3)).2
  have := bimp1119 _ _ (hp (-3)).2.1
  have := bimp1119 _ _ (hp (-3)).2.2.2.2.1
  have := btrue1119 (hend (-2)).1
  have := btrue1119 (hend (-2)).2
  have := bimp1119 _ _ (hp (-2)).2.1
  have := bimp1119 _ _ (hp (-2)).2.2.2.2.1
  have := btrue1119 (hend (-1)).1
  have := btrue1119 (hend (-1)).2
  have := bimp1119 _ _ (hp (-1)).2.1
  have := bimp1119 _ _ (hp (-1)).2.2.2.2.1
  have := btrue1119 (hend 0).1
  have := btrue1119 (hend 0).2
  have := bimp1119 _ _ (hp 0).2.1
  have := bimp1119 _ _ (hp 0).2.2.2.2.1
  have := btrue1119 (hend 1).1
  have := btrue1119 (hend 1).2
  have := bimp1119 _ _ (hp 1).2.1
  have := bimp1119 _ _ (hp 1).2.2.2.2.1
  have := btrue1119 (hend 2).1
  have := btrue1119 (hend 2).2
  have := bimp1119 _ _ (hp 2).2.1
  have := bimp1119 _ _ (hp 2).2.2.2.2.1
  have := ble1119 (x (-9) 1)
  have := ble1119 (x (-9) 2)
  have := ble1119 (x (-9) 5)
  have := ble1119 (x (-9) 6)
  have := ble1119 (x (-9) 7)
  have := ble1119 (x (-8) 1)
  have := ble1119 (x (-8) 2)
  have := ble1119 (x (-8) 5)
  have := ble1119 (x (-8) 6)
  have := ble1119 (x (-7) 1)
  have := ble1119 (x (-7) 2)
  have := ble1119 (x (-7) 5)
  have := ble1119 (x (-7) 6)
  have := ble1119 (x (-7) 7)
  have := ble1119 (x (-6) 1)
  have := ble1119 (x (-6) 2)
  have := ble1119 (x (-6) 4)
  have := ble1119 (x (-6) 5)
  have := ble1119 (x (-6) 6)
  have := ble1119 (x (-5) 1)
  have := ble1119 (x (-5) 2)
  have := ble1119 (x (-5) 3)
  have := ble1119 (x (-5) 5)
  have := ble1119 (x (-5) 6)
  have := ble1119 (x (-5) 7)
  have := ble1119 (x (-4) 1)
  have := ble1119 (x (-4) 2)
  have := ble1119 (x (-4) 4)
  have := ble1119 (x (-4) 5)
  have := ble1119 (x (-4) 6)
  have := ble1119 (x (-3) 1)
  have := ble1119 (x (-3) 2)
  have := ble1119 (x (-3) 3)
  have := ble1119 (x (-3) 5)
  have := ble1119 (x (-3) 6)
  have := ble1119 (x (-2) 0)
  have := ble1119 (x (-2) 1)
  have := ble1119 (x (-2) 2)
  have := ble1119 (x (-2) 4)
  have := ble1119 (x (-2) 5)
  have := ble1119 (x (-2) 6)
  have := ble1119 (x (-1) 1)
  have := ble1119 (x (-1) 2)
  have := ble1119 (x (-1) 3)
  have := ble1119 (x (-1) 5)
  have := ble1119 (x (-1) 6)
  have := ble1119 (x 0 0)
  have := ble1119 (x 0 1)
  have := ble1119 (x 0 2)
  have := ble1119 (x 0 5)
  have := ble1119 (x 0 6)
  have := ble1119 (x 1 1)
  have := ble1119 (x 1 2)
  have := ble1119 (x 1 5)
  have := ble1119 (x 1 6)
  have := ble1119 (x 2 0)
  have := ble1119 (x 2 1)
  have := ble1119 (x 2 2)
  have := ble1119 (x 2 5)
  have := ble1119 (x 2 6)
  have := ble1119 (e (-2))
  have := ble1119 (e 0)
  have := ble1119 (e 2)
  have := alt1119 x halt (-10) (-9) (by norm_num)
  have := alt1119 x halt (-9) (-8) (by norm_num)
  have := alt1119 x halt (-8) (-7) (by norm_num)
  have := alt1119 x halt (-7) (-6) (by norm_num)
  have := alt1119 x halt (-6) (-5) (by norm_num)
  have := alt1119 x halt (-5) (-4) (by norm_num)
  have := alt1119 x halt (-4) (-3) (by norm_num)
  have := alt1119 x halt (-3) (-2) (by norm_num)
  have := alt1119 x halt (-2) (-1) (by norm_num)
  have := alt1119 x halt (-1) 0 (by norm_num)
  have := alt1119 x halt 0 1 (by norm_num)
  have := alt1119 x halt 1 2 (by norm_num)
  have := alt1119 x halt 2 3 (by norm_num)
  have := btrue1119 h0
  have := btrue1119 he0
  omega


theorem true_phase1119 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0)
    (halt : ∀ p : ℤ, x (p + 1) 1 = !(x p 1)) :
    ∀ p : ℤ, x p 1 = true → e p = false := by
  intro p hp1
  cases he : e p with
  | false => rfl
  | true =>
    have hs := rt1_model_shift_upper895 x e hm p
    refine False.elim (true_origin1119 _ _ hs ?_ ?_ ?_)
    · intro q
      have hh := halt (p + q)
      simpa only [add_assoc] using hh
    · simpa using hp1
    · simpa using he

end RT1Phase1119

theorem cycle_power_eight_alternating_true_phase_no_defect (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0)
    (halt : ∀ p : ℤ, x (p + 1) 1 = !(x p 1)) :
    ∀ p : ℤ, x p 1 = true → e p = false := by
  have _ := @cycle_power_eight_alternating_false_phase_no_defect
  exact RT1Phase1119.true_phase1119 x e hm halt
