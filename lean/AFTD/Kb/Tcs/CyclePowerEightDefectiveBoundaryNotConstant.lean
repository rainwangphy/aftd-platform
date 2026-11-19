import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerEightAlternatingFalsePhaseNoDefect
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_eight_defective_boundary_not_constant

Topic: combinatorics   Node: 83ce9a9f9ea7

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635; finite computations 29006, 29007 and 29023.

In a zero-phase defective exponent-three model, the first inner bit cannot be constant false and cannot be constant true.
-/

namespace RT1Const1119
open RT1False942

theorem band1119c (a b : Bool) : (a && b).toNat ≤ a.toNat ∧ (a && b).toNat ≤ b.toNat := by
  cases a <;> cases b <;> decide
theorem ble1119c (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
theorem bimp1119c (a b : Bool) (h : a = true → b = true) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all
theorem btrue1119c {b : Bool} (h : b = true) : b.toNat = 1 := by simp [h]
theorem bfalse1119c {b : Bool} (h : b = false) : b.toNat = 0 := by simp [h]

theorem rk1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v w : ℤ) (hw : w = v - 1) :
    (x v 6).toNat + (x w 1).toNat = 1 := by
  subst hw; exact (rt1_false_semantics939 x e h).1 v

theorem tp1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) :
    (x v 4).toNat + (x v1 5).toNat + (x v2 2).toNat + (x v3 3).toNat + (e v).toNat = 1 := by
  subst h1 h2 h3; exact (rt1_false_semantics939 x e h).2.1 v

theorem ct1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 v4 v5 v6 v7 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4)
    (h5 : v5 = v - 5) (h6 : v6 = v - 6) (h7 : v7 = v - 7) :
    (x v 0).toNat + (x v1 1).toNat + (x v2 2).toNat + (x v3 3).toNat + (x v4 4).toNat +
      (x v5 5).toNat + (x v6 6).toNat + (x v7 7).toNat + (e v).toNat = 4 := by
  subst h1 h2 h3 h4 h5 h6 h7; exact (rt1_false_semantics939 x e h).2.2 v

theorem cv1_1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
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

theorem cv2_1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 v4 v5 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4)
    (h5 : v5 = v - 5) :
    1 ≤ (x v 0 && x v 2).toNat + (x v1 1 && x v1 3).toNat + (x v2 2 && x v2 4).toNat +
      (x v3 3 && x v3 5).toNat + (x v4 4 && x v4 6).toNat + (x v5 5 && x v5 7).toNat := by
  subst h1 h2 h3 h4 h5
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 2 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega

theorem cv3_1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 v3 v4 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4) :
    1 ≤ (x v 0 && x v 3).toNat + (x v1 1 && x v1 4).toNat + (x v2 2 && x v2 5).toNat +
      (x v3 3 && x v3 6).toNat + (x v4 4 && x v4 7).toNat := by
  subst h1 h2 h3 h4
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 3 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega

theorem cv5_1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v v1 v2 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) :
    1 ≤ (x v 0 && x v 5).toNat + (x v1 1 && x v1 6).toNat + (x v2 2 && x v2 7).toNat := by
  subst h1 h2
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 5 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega


theorem alt1119c (x : ℤ → ℕ → Bool) (halt : ∀ p : ℤ, x (p + 1) 1 = !(x p 1)) (p q : ℤ)
    (hq : q = p + 1) : (x p 1).toNat + (x q 1).toNat = 1 := by
  subst hq; rw [halt p]; cases x p 1 <;> decide

theorem const_false1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0) (hb : ∀ p : ℤ, x p 1 = false) : False := by
  obtain ⟨hend, hp⟩ := rt1_bridge_base895 x e hm
  have := cv2_1119c x e hm (-4) (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := cv3_1119c x e hm (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := cv5_1119c x e hm (-5) (-6) (-7) (by norm_num) (by norm_num)
  have := cv5_1119c x e hm (-6) (-7) (-8) (by norm_num) (by norm_num)
  have := cv5_1119c x e hm (-8) (-9) (-10) (by norm_num) (by norm_num)
  have := cv5_1119c x e hm (-9) (-10) (-11) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-8) (-9) (-10) (-11) (by norm_num) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num)
  have := band1119c (x (-4) 0) (x (-4) 2)
  have := band1119c (x (-5) 1) (x (-5) 3)
  have := band1119c (x (-6) 2) (x (-6) 4)
  have := band1119c (x (-7) 3) (x (-7) 5)
  have := band1119c (x (-8) 4) (x (-8) 6)
  have := band1119c (x (-9) 5) (x (-9) 7)
  have := band1119c (x (-5) 0) (x (-5) 3)
  have := band1119c (x (-6) 1) (x (-6) 4)
  have := band1119c (x (-7) 2) (x (-7) 5)
  have := band1119c (x (-8) 3) (x (-8) 6)
  have := band1119c (x (-9) 4) (x (-9) 7)
  have := band1119c (x (-5) 0) (x (-5) 5)
  have := band1119c (x (-6) 1) (x (-6) 6)
  have := band1119c (x (-7) 2) (x (-7) 7)
  have := band1119c (x (-6) 0) (x (-6) 5)
  have := band1119c (x (-7) 1) (x (-7) 6)
  have := band1119c (x (-8) 2) (x (-8) 7)
  have := band1119c (x (-8) 0) (x (-8) 5)
  have := band1119c (x (-9) 1) (x (-9) 6)
  have := band1119c (x (-10) 2) (x (-10) 7)
  have := band1119c (x (-9) 0) (x (-9) 5)
  have := band1119c (x (-10) 1) (x (-10) 6)
  have := band1119c (x (-11) 2) (x (-11) 7)
  have := btrue1119c (hend (-12)).1
  have := btrue1119c (hend (-12)).2
  have := bimp1119c _ _ (hp (-12)).2.1
  have := bimp1119c _ _ (hp (-12)).2.2.2.2.1
  have := btrue1119c (hend (-11)).1
  have := btrue1119c (hend (-11)).2
  have := bimp1119c _ _ (hp (-11)).2.1
  have := bimp1119c _ _ (hp (-11)).2.2.2.2.1
  have := btrue1119c (hend (-10)).1
  have := btrue1119c (hend (-10)).2
  have := bimp1119c _ _ (hp (-10)).2.1
  have := bimp1119c _ _ (hp (-10)).2.2.2.2.1
  have := btrue1119c (hend (-9)).1
  have := btrue1119c (hend (-9)).2
  have := bimp1119c _ _ (hp (-9)).2.1
  have := bimp1119c _ _ (hp (-9)).2.2.2.2.1
  have := btrue1119c (hend (-8)).1
  have := btrue1119c (hend (-8)).2
  have := bimp1119c _ _ (hp (-8)).2.1
  have := bimp1119c _ _ (hp (-8)).2.2.2.2.1
  have := btrue1119c (hend (-7)).1
  have := btrue1119c (hend (-7)).2
  have := bimp1119c _ _ (hp (-7)).2.1
  have := bimp1119c _ _ (hp (-7)).2.2.2.2.1
  have := btrue1119c (hend (-6)).1
  have := btrue1119c (hend (-6)).2
  have := bimp1119c _ _ (hp (-6)).2.1
  have := bimp1119c _ _ (hp (-6)).2.2.2.2.1
  have := btrue1119c (hend (-5)).1
  have := btrue1119c (hend (-5)).2
  have := bimp1119c _ _ (hp (-5)).2.1
  have := bimp1119c _ _ (hp (-5)).2.2.2.2.1
  have := btrue1119c (hend (-4)).1
  have := btrue1119c (hend (-4)).2
  have := bimp1119c _ _ (hp (-4)).2.1
  have := bimp1119c _ _ (hp (-4)).2.2.2.2.1
  have := btrue1119c (hend (-3)).1
  have := btrue1119c (hend (-3)).2
  have := bimp1119c _ _ (hp (-3)).2.1
  have := bimp1119c _ _ (hp (-3)).2.2.2.2.1
  have := btrue1119c (hend (-2)).1
  have := btrue1119c (hend (-2)).2
  have := bimp1119c _ _ (hp (-2)).2.1
  have := bimp1119c _ _ (hp (-2)).2.2.2.2.1
  have := ble1119c (x (-12) 1)
  have := ble1119c (x (-12) 2)
  have := ble1119c (x (-12) 3)
  have := ble1119c (x (-12) 5)
  have := ble1119c (x (-12) 6)
  have := ble1119c (x (-11) 1)
  have := ble1119c (x (-11) 2)
  have := ble1119c (x (-11) 3)
  have := ble1119c (x (-11) 5)
  have := ble1119c (x (-11) 6)
  have := ble1119c (x (-11) 7)
  have := ble1119c (x (-10) 1)
  have := ble1119c (x (-10) 2)
  have := ble1119c (x (-10) 5)
  have := ble1119c (x (-10) 6)
  have := ble1119c (x (-10) 7)
  have := ble1119c (x (-9) 0)
  have := ble1119c (x (-9) 1)
  have := ble1119c (x (-9) 2)
  have := ble1119c (x (-9) 3)
  have := ble1119c (x (-9) 4)
  have := ble1119c (x (-9) 5)
  have := ble1119c (x (-9) 6)
  have := ble1119c (x (-9) 7)
  have := ble1119c (x (-8) 0)
  have := ble1119c (x (-8) 1)
  have := ble1119c (x (-8) 2)
  have := ble1119c (x (-8) 3)
  have := ble1119c (x (-8) 4)
  have := ble1119c (x (-8) 5)
  have := ble1119c (x (-8) 6)
  have := ble1119c (x (-8) 7)
  have := ble1119c (x (-7) 1)
  have := ble1119c (x (-7) 2)
  have := ble1119c (x (-7) 3)
  have := ble1119c (x (-7) 5)
  have := ble1119c (x (-7) 6)
  have := ble1119c (x (-7) 7)
  have := ble1119c (x (-6) 0)
  have := ble1119c (x (-6) 1)
  have := ble1119c (x (-6) 2)
  have := ble1119c (x (-6) 4)
  have := ble1119c (x (-6) 5)
  have := ble1119c (x (-6) 6)
  have := ble1119c (x (-5) 0)
  have := ble1119c (x (-5) 1)
  have := ble1119c (x (-5) 2)
  have := ble1119c (x (-5) 3)
  have := ble1119c (x (-5) 4)
  have := ble1119c (x (-5) 5)
  have := ble1119c (x (-5) 6)
  have := ble1119c (x (-4) 0)
  have := ble1119c (x (-4) 1)
  have := ble1119c (x (-4) 2)
  have := ble1119c (x (-4) 5)
  have := ble1119c (x (-4) 6)
  have := ble1119c (x (-3) 1)
  have := ble1119c (x (-3) 2)
  have := ble1119c (x (-3) 5)
  have := ble1119c (x (-3) 6)
  have := ble1119c (x (-2) 1)
  have := ble1119c (x (-2) 2)
  have := ble1119c (x (-2) 4)
  have := ble1119c (x (-2) 5)
  have := ble1119c (x (-2) 6)
  have := ble1119c (e (-9))
  have := ble1119c (e (-8))
  have := ble1119c (e (-6))
  have := ble1119c (e (-5))
  have := ble1119c (e (-2))
  have := bfalse1119c (hb (-12))
  have := bfalse1119c (hb (-11))
  have := bfalse1119c (hb (-10))
  have := bfalse1119c (hb (-9))
  have := bfalse1119c (hb (-8))
  have := bfalse1119c (hb (-7))
  have := bfalse1119c (hb (-6))
  have := bfalse1119c (hb (-5))
  have := bfalse1119c (hb (-4))
  have := bfalse1119c (hb (-3))
  have := bfalse1119c (hb (-2))
  omega

theorem const_true1119c (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0) (hb : ∀ p : ℤ, x p 1 = true) : False := by
  obtain ⟨hend, hp⟩ := rt1_bridge_base895 x e hm
  have := cv2_1119c x e hm (-5) (-6) (-7) (-8) (-9) (-10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := cv3_1119c x e hm (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := cv5_1119c x e hm (-3) (-4) (-5) (by norm_num) (by norm_num)
  have := cv5_1119c x e hm (-4) (-5) (-6) (by norm_num) (by norm_num)
  have := cv5_1119c x e hm (-6) (-7) (-8) (by norm_num) (by norm_num)
  have := cv5_1119c x e hm (-7) (-8) (-9) (by norm_num) (by norm_num)
  have := rk1119c x e hm (-4) (-5) (by norm_num)
  have := rk1119c x e hm (-5) (-6) (by norm_num)
  have := rk1119c x e hm (-6) (-7) (by norm_num)
  have := rk1119c x e hm (-7) (-8) (by norm_num)
  have := rk1119c x e hm (-8) (-9) (by norm_num)
  have := rk1119c x e hm (-9) (-10) (by norm_num)
  have := tp1119c x e hm (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num)
  have := tp1119c x e hm (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num)
  have := band1119c (x (-5) 0) (x (-5) 2)
  have := band1119c (x (-6) 1) (x (-6) 3)
  have := band1119c (x (-7) 2) (x (-7) 4)
  have := band1119c (x (-8) 3) (x (-8) 5)
  have := band1119c (x (-9) 4) (x (-9) 6)
  have := band1119c (x (-10) 5) (x (-10) 7)
  have := band1119c (x (-5) 0) (x (-5) 3)
  have := band1119c (x (-6) 1) (x (-6) 4)
  have := band1119c (x (-7) 2) (x (-7) 5)
  have := band1119c (x (-8) 3) (x (-8) 6)
  have := band1119c (x (-9) 4) (x (-9) 7)
  have := band1119c (x (-3) 0) (x (-3) 5)
  have := band1119c (x (-4) 1) (x (-4) 6)
  have := band1119c (x (-5) 2) (x (-5) 7)
  have := band1119c (x (-4) 0) (x (-4) 5)
  have := band1119c (x (-5) 1) (x (-5) 6)
  have := band1119c (x (-6) 2) (x (-6) 7)
  have := band1119c (x (-6) 0) (x (-6) 5)
  have := band1119c (x (-7) 1) (x (-7) 6)
  have := band1119c (x (-8) 2) (x (-8) 7)
  have := band1119c (x (-7) 0) (x (-7) 5)
  have := band1119c (x (-8) 1) (x (-8) 6)
  have := band1119c (x (-9) 2) (x (-9) 7)
  have := btrue1119c (hend (-12)).1
  have := btrue1119c (hend (-12)).2
  have := bimp1119c _ _ (hp (-12)).2.1
  have := bimp1119c _ _ (hp (-12)).2.2.2.2.1
  have := btrue1119c (hend (-11)).1
  have := btrue1119c (hend (-11)).2
  have := bimp1119c _ _ (hp (-11)).2.1
  have := bimp1119c _ _ (hp (-11)).2.2.2.2.1
  have := btrue1119c (hend (-10)).1
  have := btrue1119c (hend (-10)).2
  have := bimp1119c _ _ (hp (-10)).2.1
  have := bimp1119c _ _ (hp (-10)).2.2.2.2.1
  have := btrue1119c (hend (-9)).1
  have := btrue1119c (hend (-9)).2
  have := bimp1119c _ _ (hp (-9)).2.1
  have := bimp1119c _ _ (hp (-9)).2.2.2.2.1
  have := btrue1119c (hend (-8)).1
  have := btrue1119c (hend (-8)).2
  have := bimp1119c _ _ (hp (-8)).2.1
  have := bimp1119c _ _ (hp (-8)).2.2.2.2.1
  have := btrue1119c (hend (-7)).1
  have := btrue1119c (hend (-7)).2
  have := bimp1119c _ _ (hp (-7)).2.1
  have := bimp1119c _ _ (hp (-7)).2.2.2.2.1
  have := btrue1119c (hend (-6)).1
  have := btrue1119c (hend (-6)).2
  have := bimp1119c _ _ (hp (-6)).2.1
  have := bimp1119c _ _ (hp (-6)).2.2.2.2.1
  have := btrue1119c (hend (-5)).1
  have := btrue1119c (hend (-5)).2
  have := bimp1119c _ _ (hp (-5)).2.1
  have := bimp1119c _ _ (hp (-5)).2.2.2.2.1
  have := btrue1119c (hend (-4)).1
  have := btrue1119c (hend (-4)).2
  have := bimp1119c _ _ (hp (-4)).2.1
  have := bimp1119c _ _ (hp (-4)).2.2.2.2.1
  have := btrue1119c (hend (-3)).1
  have := btrue1119c (hend (-3)).2
  have := bimp1119c _ _ (hp (-3)).2.1
  have := bimp1119c _ _ (hp (-3)).2.2.2.2.1
  have := btrue1119c (hend (-2)).1
  have := btrue1119c (hend (-2)).2
  have := bimp1119c _ _ (hp (-2)).2.1
  have := bimp1119c _ _ (hp (-2)).2.2.2.2.1
  have := ble1119c (x (-12) 1)
  have := ble1119c (x (-12) 2)
  have := ble1119c (x (-12) 3)
  have := ble1119c (x (-12) 5)
  have := ble1119c (x (-12) 6)
  have := ble1119c (x (-11) 1)
  have := ble1119c (x (-11) 2)
  have := ble1119c (x (-11) 5)
  have := ble1119c (x (-11) 6)
  have := ble1119c (x (-10) 1)
  have := ble1119c (x (-10) 2)
  have := ble1119c (x (-10) 5)
  have := ble1119c (x (-10) 6)
  have := ble1119c (x (-10) 7)
  have := ble1119c (x (-9) 1)
  have := ble1119c (x (-9) 2)
  have := ble1119c (x (-9) 3)
  have := ble1119c (x (-9) 4)
  have := ble1119c (x (-9) 5)
  have := ble1119c (x (-9) 6)
  have := ble1119c (x (-9) 7)
  have := ble1119c (x (-8) 1)
  have := ble1119c (x (-8) 2)
  have := ble1119c (x (-8) 3)
  have := ble1119c (x (-8) 5)
  have := ble1119c (x (-8) 6)
  have := ble1119c (x (-8) 7)
  have := ble1119c (x (-7) 0)
  have := ble1119c (x (-7) 1)
  have := ble1119c (x (-7) 2)
  have := ble1119c (x (-7) 4)
  have := ble1119c (x (-7) 5)
  have := ble1119c (x (-7) 6)
  have := ble1119c (x (-6) 0)
  have := ble1119c (x (-6) 1)
  have := ble1119c (x (-6) 2)
  have := ble1119c (x (-6) 3)
  have := ble1119c (x (-6) 4)
  have := ble1119c (x (-6) 5)
  have := ble1119c (x (-6) 6)
  have := ble1119c (x (-6) 7)
  have := ble1119c (x (-5) 0)
  have := ble1119c (x (-5) 1)
  have := ble1119c (x (-5) 2)
  have := ble1119c (x (-5) 3)
  have := ble1119c (x (-5) 4)
  have := ble1119c (x (-5) 5)
  have := ble1119c (x (-5) 6)
  have := ble1119c (x (-5) 7)
  have := ble1119c (x (-4) 0)
  have := ble1119c (x (-4) 1)
  have := ble1119c (x (-4) 2)
  have := ble1119c (x (-4) 5)
  have := ble1119c (x (-4) 6)
  have := ble1119c (x (-3) 0)
  have := ble1119c (x (-3) 1)
  have := ble1119c (x (-3) 2)
  have := ble1119c (x (-3) 4)
  have := ble1119c (x (-3) 5)
  have := ble1119c (x (-3) 6)
  have := ble1119c (x (-2) 1)
  have := ble1119c (x (-2) 2)
  have := ble1119c (x (-2) 4)
  have := ble1119c (x (-2) 5)
  have := ble1119c (x (-2) 6)
  have := ble1119c (e (-9))
  have := ble1119c (e (-6))
  have := ble1119c (e (-5))
  have := ble1119c (e (-3))
  have := ble1119c (e (-2))
  have := btrue1119c (hb (-12))
  have := btrue1119c (hb (-11))
  have := btrue1119c (hb (-10))
  have := btrue1119c (hb (-9))
  have := btrue1119c (hb (-8))
  have := btrue1119c (hb (-7))
  have := btrue1119c (hb (-6))
  have := btrue1119c (hb (-5))
  have := btrue1119c (hb (-4))
  have := btrue1119c (hb (-3))
  have := btrue1119c (hb (-2))
  omega


end RT1Const1119

theorem cycle_power_eight_defective_boundary_not_constant (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0) :
    (¬ ∀ p : ℤ, x p 1 = false) ∧ (¬ ∀ p : ℤ, x p 1 = true) := by
  have _ := @cycle_power_eight_alternating_false_phase_no_defect
  exact ⟨fun hb => RT1Const1119.const_false1119c x e hm hb, fun hb => RT1Const1119.const_true1119c x e hm hb⟩
