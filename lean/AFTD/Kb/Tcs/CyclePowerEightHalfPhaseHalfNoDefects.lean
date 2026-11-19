import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.G

/-!
# cycle_power_eight_half_phase_half_no_defects

Topic: combinatorics   Node: 1e80ae9b77bb

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635; the half-phase companion of cycle_power_eight_zero_phase_half_no_defects, needed (with it) for the hnodefect hypothesis of cycle_power_dyadic_middle_bits_from_defective_halves at t = 3; SAT core experiment 34387.

In an exponent-three dyadic defective half model with phase shift 4 (half the half-span; the top-rank ownership at v loses one exactly when there is a defect at v + 4), no defect occurs anywhere.
-/

namespace RT1Half1119
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem band1119h (a b : Bool) : (a && b).toNat ≤ a.toNat ∧ (a && b).toNat ≤ b.toNat := by
  cases a <;> cases b <;> decide
theorem ble1119h (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
theorem bimp1119h (a b : Bool) (h : a = true → b = true) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all
theorem btrue1119h {b : Bool} (h : b = true) : b.toNat = 1 := by simp [h]
theorem bfalse1119h {b : Bool} (h : b = false) : b.toNat = 0 := by simp [h]


theorem bridge1119h (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (s : ℤ)
    (h : cycle_power_dyadic_defective_half_model 3 y e s) :
    (∀ p, y p 0 = true ∧ y p 7 = true) ∧
    (∀ p, (y p 1 = true → y p 7 = true) ∧ (y p 2 = true → y p 6 = true) ∧
          (y p 3 = true → y p 7 = true) ∧ (y p 4 = true → y p 0 = true) ∧
          (y p 5 = true → y p 1 = true) ∧ (y p 6 = true → y p 0 = true)) := by
  constructor
  · intro p
    have hex := h.2.1 0 (by omega) p
    simp only [pow_zero, Finset.sum_range_one, Nat.cast_zero, sub_zero, zero_add] at hex
    cases h0 : y p 0 <;> cases h7 : y p 7 <;> simp_all
  · intro p
    have h1 := cycle_power_dyadic_tight_class_parent 3 1 (by omega) (by omega) (y p) (h.1 p)
    have h2 := cycle_power_dyadic_tight_class_parent 3 2 (by omega) (by omega) (y p) (h.1 p)
    have a := (h1 1 (by norm_num)).2 (by norm_num)
    have b := (h2 2 (by norm_num)).2 (by norm_num)
    have c := (h2 3 (by norm_num)).2 (by norm_num)
    have d := (h2 0 (by norm_num)).1 (by norm_num)
    have f := (h2 1 (by norm_num)).1 (by norm_num)
    have g := (h1 0 (by norm_num)).1 (by norm_num)
    norm_num at a b c d f g
    exact ⟨a,b,c,d,f,g⟩

private theorem bpa1119h (a b : Bool) (h : a = true → b = true) : (a && b) = a := by
  cases a <;> cases b <;> simp_all

theorem sem1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool) (s : ℤ)
    (h : cycle_power_dyadic_defective_half_model 3 x e s) :
    (∀ v : ℤ, (x v 6).toNat + (x (v-1) 1).toNat = 1) ∧
    (∀ v : ℤ, (x v 4).toNat + (x (v-1) 5).toNat + (x (v-2) 2).toNat +
       (x (v-3) 3).toNat + (e (v + s)).toNat = 1) ∧
    (∀ v : ℤ, (x v 0).toNat + (x (v-1) 1).toNat + (x (v-2) 2).toNat +
       (x (v-3) 3).toNat + (x (v-4) 4).toNat + (x (v-5) 5).toNat +
       (x (v-6) 6).toNat + (x (v-7) 7).toNat + (e v).toNat = 4) := by
  obtain ⟨hend, hp⟩ := bridge1119h x e s h
  have hpa (p : ℤ) : (x p 1 && x p 5) = x p 5 := by
    rw [Bool.and_comm]; exact bpa1119h _ _ (hp p).2.2.2.2.1
  have hpb (p : ℤ) : (x p 2 && x p 6) = x p 2 :=
    bpa1119h _ _ (hp p).2.1
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have hh := h.2.1 1 (by omega) v
    norm_num [Finset.sum_range_succ, hend, hpa, hpb] at hh ⊢
    exact hh
  · intro v
    have hh := h.2.2.1 v
    norm_num [Finset.sum_range_succ, hend, hpa, hpb] at hh ⊢
    exact hh
  · intro v
    have hh := h.2.2.2.2 v
    norm_num [Finset.sum_range_succ] at hh ⊢
    exact hh

theorem shift1119h (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (s : ℤ)
    (h : cycle_power_dyadic_defective_half_model 3 y e s) (v : ℤ) :
    cycle_power_dyadic_defective_half_model 3 (fun p a => y (v+p) a) (fun p => e (v+p)) s := by
  rcases h with ⟨hw, hl, ht, hc, hn⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hw (v+p)
  · intro j hj p
    simpa only [add_sub_assoc] using hl j hj (v+p)
  · intro p
    simpa only [add_sub_assoc, add_assoc] using ht (v+p)
  · intro d hd hd8 hd4 p
    obtain ⟨a,ha,ha1,ha2⟩ := hc d hd hd8 hd4 (v+p)
    refine ⟨a, ha, ?_, ?_⟩
    · simpa only [add_sub_assoc] using ha1
    · simpa only [add_sub_assoc] using ha2
  · intro p
    simpa only [add_sub_assoc] using hn (v+p)

theorem rk1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool) (s : ℤ)
    (h : cycle_power_dyadic_defective_half_model 3 x e s) (v w : ℤ) (hw : w = v - 1) :
    (x v 6).toNat + (x w 1).toNat = 1 := by
  subst hw; exact (sem1119h x e s h).1 v

theorem tp1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool) (s : ℤ)
    (h : cycle_power_dyadic_defective_half_model 3 x e s) (v v1 v2 v3 w : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (hw : w = v + s) :
    (x v 4).toNat + (x v1 5).toNat + (x v2 2).toNat + (x v3 3).toNat + (e w).toNat = 1 := by
  subst h1 h2 h3 hw; exact (sem1119h x e s h).2.1 v

theorem ct1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool) (s : ℤ)
    (h : cycle_power_dyadic_defective_half_model 3 x e s) (v v1 v2 v3 v4 v5 v6 v7 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4)
    (h5 : v5 = v - 5) (h6 : v6 = v - 6) (h7 : v7 = v - 7) :
    (x v 0).toNat + (x v1 1).toNat + (x v2 2).toNat + (x v3 3).toNat + (x v4 4).toNat +
      (x v5 5).toNat + (x v6 6).toNat + (x v7 7).toNat + (e v).toNat = 4 := by
  subst h1 h2 h3 h4 h5 h6 h7; exact (sem1119h x e s h).2.2 v

theorem cv1_1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (s : ℤ) (h : cycle_power_dyadic_defective_half_model 3 x e s) (v v1 v2 v3 v4 v5 v6 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4)
    (h5 : v5 = v - 5) (h6 : v6 = v - 6) :
    1 ≤ (x v 0 && x v 1).toNat + (x v1 1 && x v1 2).toNat + (x v2 2 && x v2 3).toNat +
      (x v3 3 && x v3 4).toNat + (x v4 4 && x v4 5).toNat + (x v5 5 && x v5 6).toNat +
      (x v6 6 && x v6 7).toNat := by
  subst h1 h2 h3 h4 h5 h6
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 1 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega

theorem cv2_1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (s : ℤ) (h : cycle_power_dyadic_defective_half_model 3 x e s) (v v1 v2 v3 v4 v5 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4)
    (h5 : v5 = v - 5) :
    1 ≤ (x v 0 && x v 2).toNat + (x v1 1 && x v1 3).toNat + (x v2 2 && x v2 4).toNat +
      (x v3 3 && x v3 5).toNat + (x v4 4 && x v4 6).toNat + (x v5 5 && x v5 7).toNat := by
  subst h1 h2 h3 h4 h5
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 2 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega

theorem cv3_1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (s : ℤ) (h : cycle_power_dyadic_defective_half_model 3 x e s) (v v1 v2 v3 v4 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) (h3 : v3 = v - 3) (h4 : v4 = v - 4) :
    1 ≤ (x v 0 && x v 3).toNat + (x v1 1 && x v1 4).toNat + (x v2 2 && x v2 5).toNat +
      (x v3 3 && x v3 6).toNat + (x v4 4 && x v4 7).toNat := by
  subst h1 h2 h3 h4
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 3 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega

theorem cv5_1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (s : ℤ) (h : cycle_power_dyadic_defective_half_model 3 x e s) (v v1 v2 : ℤ)
    (h1 : v1 = v - 1) (h2 : v2 = v - 2) :
    1 ≤ (x v 0 && x v 5).toNat + (x v1 1 && x v1 6).toNat + (x v2 2 && x v2 7).toNat := by
  subst h1 h2
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 5 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2 <;> simp [h1, h2] <;> omega


theorem origin1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 4) (he0 : e 0 = true) : False := by
  obtain ⟨hend, hp⟩ := bridge1119h x e 4 hm
  have c0 := ct1119h x e 4 hm (-1) (-2) (-3) (-4) (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c1 := ct1119h x e 4 hm (-2) (-3) (-4) (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c2 := ct1119h x e 4 hm (-5) (-6) (-7) (-8) (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c3 := ct1119h x e 4 hm 0 (-1) (-2) (-3) (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c4 := ct1119h x e 4 hm 1 0 (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c5 := ct1119h x e 4 hm 3 2 1 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c6 := ct1119h x e 4 hm 4 3 2 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c7 := ct1119h x e 4 hm 6 5 4 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c8 := cv1_1119h x e 4 hm (-5) (-6) (-7) (-8) (-9) (-10) (-11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c9 := (band1119h (x (-5) 0) (x (-5) 1)).1
  have c10 := (band1119h (x (-5) 0) (x (-5) 1)).2
  have c11 := (band1119h (x (-6) 1) (x (-6) 2)).1
  have c12 := (band1119h (x (-6) 1) (x (-6) 2)).2
  have c13 := (band1119h (x (-7) 2) (x (-7) 3)).1
  have c14 := (band1119h (x (-7) 2) (x (-7) 3)).2
  have c15 := (band1119h (x (-8) 3) (x (-8) 4)).1
  have c16 := (band1119h (x (-8) 3) (x (-8) 4)).2
  have c17 := (band1119h (x (-9) 4) (x (-9) 5)).1
  have c18 := (band1119h (x (-9) 4) (x (-9) 5)).2
  have c19 := (band1119h (x (-10) 5) (x (-10) 6)).1
  have c20 := (band1119h (x (-10) 5) (x (-10) 6)).2
  have c21 := (band1119h (x (-11) 6) (x (-11) 7)).1
  have c22 := (band1119h (x (-11) 6) (x (-11) 7)).2
  have c23 := cv1_1119h x e 4 hm 0 (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c24 := (band1119h (x 0 0) (x 0 1)).1
  have c25 := (band1119h (x 0 0) (x 0 1)).2
  have c26 := (band1119h (x (-1) 1) (x (-1) 2)).1
  have c27 := (band1119h (x (-1) 1) (x (-1) 2)).2
  have c28 := (band1119h (x (-2) 2) (x (-2) 3)).1
  have c29 := (band1119h (x (-2) 2) (x (-2) 3)).2
  have c30 := (band1119h (x (-3) 3) (x (-3) 4)).1
  have c31 := (band1119h (x (-3) 3) (x (-3) 4)).2
  have c32 := (band1119h (x (-4) 4) (x (-4) 5)).1
  have c33 := (band1119h (x (-4) 4) (x (-4) 5)).2
  have c34 := (band1119h (x (-5) 5) (x (-5) 6)).1
  have c35 := (band1119h (x (-5) 5) (x (-5) 6)).2
  have c36 := (band1119h (x (-6) 6) (x (-6) 7)).1
  have c37 := (band1119h (x (-6) 6) (x (-6) 7)).2
  have c38 := cv1_1119h x e 4 hm 5 4 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c39 := (band1119h (x 5 0) (x 5 1)).1
  have c40 := (band1119h (x 5 0) (x 5 1)).2
  have c41 := (band1119h (x 4 1) (x 4 2)).1
  have c42 := (band1119h (x 4 1) (x 4 2)).2
  have c43 := (band1119h (x 3 2) (x 3 3)).1
  have c44 := (band1119h (x 3 2) (x 3 3)).2
  have c45 := (band1119h (x 2 3) (x 2 4)).1
  have c46 := (band1119h (x 2 3) (x 2 4)).2
  have c47 := (band1119h (x 1 4) (x 1 5)).1
  have c48 := (band1119h (x 1 4) (x 1 5)).2
  have c49 := (band1119h (x 0 5) (x 0 6)).1
  have c50 := (band1119h (x 0 5) (x 0 6)).2
  have c51 := (band1119h (x (-1) 6) (x (-1) 7)).1
  have c52 := (band1119h (x (-1) 6) (x (-1) 7)).2
  have c53 := cv2_1119h x e 4 hm (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c54 := (band1119h (x (-1) 0) (x (-1) 2)).1
  have c55 := (band1119h (x (-1) 0) (x (-1) 2)).2
  have c56 := (band1119h (x (-2) 1) (x (-2) 3)).1
  have c57 := (band1119h (x (-2) 1) (x (-2) 3)).2
  have c58 := (band1119h (x (-3) 2) (x (-3) 4)).1
  have c59 := (band1119h (x (-3) 2) (x (-3) 4)).2
  have c60 := (band1119h (x (-4) 3) (x (-4) 5)).1
  have c61 := (band1119h (x (-4) 3) (x (-4) 5)).2
  have c62 := (band1119h (x (-5) 4) (x (-5) 6)).1
  have c63 := (band1119h (x (-5) 4) (x (-5) 6)).2
  have c64 := (band1119h (x (-6) 5) (x (-6) 7)).1
  have c65 := (band1119h (x (-6) 5) (x (-6) 7)).2
  have c66 := cv2_1119h x e 4 hm (-2) (-3) (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c67 := (band1119h (x (-2) 0) (x (-2) 2)).1
  have c68 := (band1119h (x (-2) 0) (x (-2) 2)).2
  have c69 := (band1119h (x (-3) 1) (x (-3) 3)).1
  have c70 := (band1119h (x (-3) 1) (x (-3) 3)).2
  have c71 := (band1119h (x (-4) 2) (x (-4) 4)).1
  have c72 := (band1119h (x (-4) 2) (x (-4) 4)).2
  have c73 := (band1119h (x (-5) 3) (x (-5) 5)).1
  have c74 := (band1119h (x (-5) 3) (x (-5) 5)).2
  have c75 := (band1119h (x (-6) 4) (x (-6) 6)).1
  have c76 := (band1119h (x (-6) 4) (x (-6) 6)).2
  have c77 := (band1119h (x (-7) 5) (x (-7) 7)).1
  have c78 := (band1119h (x (-7) 5) (x (-7) 7)).2
  have c79 := cv3_1119h x e 4 hm (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c80 := (band1119h (x (-2) 0) (x (-2) 3)).1
  have c81 := (band1119h (x (-2) 0) (x (-2) 3)).2
  have c82 := (band1119h (x (-3) 1) (x (-3) 4)).1
  have c83 := (band1119h (x (-3) 1) (x (-3) 4)).2
  have c84 := (band1119h (x (-4) 2) (x (-4) 5)).1
  have c85 := (band1119h (x (-4) 2) (x (-4) 5)).2
  have c86 := (band1119h (x (-5) 3) (x (-5) 6)).1
  have c87 := (band1119h (x (-5) 3) (x (-5) 6)).2
  have c88 := (band1119h (x (-6) 4) (x (-6) 7)).1
  have c89 := (band1119h (x (-6) 4) (x (-6) 7)).2
  have c90 := cv3_1119h x e 4 hm 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c91 := (band1119h (x 0 0) (x 0 3)).1
  have c92 := (band1119h (x 0 0) (x 0 3)).2
  have c93 := (band1119h (x (-1) 1) (x (-1) 4)).1
  have c94 := (band1119h (x (-1) 1) (x (-1) 4)).2
  have c95 := (band1119h (x (-2) 2) (x (-2) 5)).1
  have c96 := (band1119h (x (-2) 2) (x (-2) 5)).2
  have c97 := (band1119h (x (-3) 3) (x (-3) 6)).1
  have c98 := (band1119h (x (-3) 3) (x (-3) 6)).2
  have c99 := (band1119h (x (-4) 4) (x (-4) 7)).1
  have c100 := (band1119h (x (-4) 4) (x (-4) 7)).2
  have c101 := cv3_1119h x e 4 hm 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c102 := (band1119h (x 1 0) (x 1 3)).1
  have c103 := (band1119h (x 1 0) (x 1 3)).2
  have c104 := (band1119h (x 0 1) (x 0 4)).1
  have c105 := (band1119h (x 0 1) (x 0 4)).2
  have c106 := (band1119h (x (-1) 2) (x (-1) 5)).1
  have c107 := (band1119h (x (-1) 2) (x (-1) 5)).2
  have c108 := (band1119h (x (-2) 3) (x (-2) 6)).1
  have c109 := (band1119h (x (-2) 3) (x (-2) 6)).2
  have c110 := (band1119h (x (-3) 4) (x (-3) 7)).1
  have c111 := (band1119h (x (-3) 4) (x (-3) 7)).2
  have c112 := cv5_1119h x e 4 hm (-1) (-2) (-3) (by norm_num) (by norm_num)
  have c113 := (band1119h (x (-1) 0) (x (-1) 5)).1
  have c114 := (band1119h (x (-1) 0) (x (-1) 5)).2
  have c115 := (band1119h (x (-2) 1) (x (-2) 6)).1
  have c116 := (band1119h (x (-2) 1) (x (-2) 6)).2
  have c117 := (band1119h (x (-3) 2) (x (-3) 7)).1
  have c118 := (band1119h (x (-3) 2) (x (-3) 7)).2
  have c119 := cv5_1119h x e 4 hm (-2) (-3) (-4) (by norm_num) (by norm_num)
  have c120 := (band1119h (x (-2) 0) (x (-2) 5)).1
  have c121 := (band1119h (x (-2) 0) (x (-2) 5)).2
  have c122 := (band1119h (x (-3) 1) (x (-3) 6)).1
  have c123 := (band1119h (x (-3) 1) (x (-3) 6)).2
  have c124 := (band1119h (x (-4) 2) (x (-4) 7)).1
  have c125 := (band1119h (x (-4) 2) (x (-4) 7)).2
  have c126 := cv5_1119h x e 4 hm (-4) (-5) (-6) (by norm_num) (by norm_num)
  have c127 := (band1119h (x (-4) 0) (x (-4) 5)).1
  have c128 := (band1119h (x (-4) 0) (x (-4) 5)).2
  have c129 := (band1119h (x (-5) 1) (x (-5) 6)).1
  have c130 := (band1119h (x (-5) 1) (x (-5) 6)).2
  have c131 := (band1119h (x (-6) 2) (x (-6) 7)).1
  have c132 := (band1119h (x (-6) 2) (x (-6) 7)).2
  have c133 := cv5_1119h x e 4 hm (-5) (-6) (-7) (by norm_num) (by norm_num)
  have c134 := (band1119h (x (-5) 0) (x (-5) 5)).1
  have c135 := (band1119h (x (-5) 0) (x (-5) 5)).2
  have c136 := (band1119h (x (-6) 1) (x (-6) 6)).1
  have c137 := (band1119h (x (-6) 1) (x (-6) 6)).2
  have c138 := (band1119h (x (-7) 2) (x (-7) 7)).1
  have c139 := (band1119h (x (-7) 2) (x (-7) 7)).2
  have c140 := cv5_1119h x e 4 hm (-6) (-7) (-8) (by norm_num) (by norm_num)
  have c141 := (band1119h (x (-6) 0) (x (-6) 5)).1
  have c142 := (band1119h (x (-6) 0) (x (-6) 5)).2
  have c143 := (band1119h (x (-7) 1) (x (-7) 6)).1
  have c144 := (band1119h (x (-7) 1) (x (-7) 6)).2
  have c145 := (band1119h (x (-8) 2) (x (-8) 7)).1
  have c146 := (band1119h (x (-8) 2) (x (-8) 7)).2
  have c147 := cv5_1119h x e 4 hm 0 (-1) (-2) (by norm_num) (by norm_num)
  have c148 := (band1119h (x 0 0) (x 0 5)).1
  have c149 := (band1119h (x 0 0) (x 0 5)).2
  have c150 := (band1119h (x (-1) 1) (x (-1) 6)).1
  have c151 := (band1119h (x (-1) 1) (x (-1) 6)).2
  have c152 := (band1119h (x (-2) 2) (x (-2) 7)).1
  have c153 := (band1119h (x (-2) 2) (x (-2) 7)).2
  have c154 := cv5_1119h x e 4 hm 1 0 (-1) (by norm_num) (by norm_num)
  have c155 := (band1119h (x 1 0) (x 1 5)).1
  have c156 := (band1119h (x 1 0) (x 1 5)).2
  have c157 := (band1119h (x 0 1) (x 0 6)).1
  have c158 := (band1119h (x 0 1) (x 0 6)).2
  have c159 := (band1119h (x (-1) 2) (x (-1) 7)).1
  have c160 := (band1119h (x (-1) 2) (x (-1) 7)).2
  have c161 := cv5_1119h x e 4 hm 3 2 1 (by norm_num) (by norm_num)
  have c162 := (band1119h (x 3 0) (x 3 5)).1
  have c163 := (band1119h (x 3 0) (x 3 5)).2
  have c164 := (band1119h (x 2 1) (x 2 6)).1
  have c165 := (band1119h (x 2 1) (x 2 6)).2
  have c166 := (band1119h (x 1 2) (x 1 7)).1
  have c167 := (band1119h (x 1 2) (x 1 7)).2
  have c168 := rk1119h x e 4 hm (-1) (-2) (by norm_num)
  have c169 := rk1119h x e 4 hm (-3) (-4) (by norm_num)
  have c170 := rk1119h x e 4 hm (-4) (-5) (by norm_num)
  have c171 := rk1119h x e 4 hm (-5) (-6) (by norm_num)
  have c172 := rk1119h x e 4 hm 0 (-1) (by norm_num)
  have c173 := tp1119h x e 4 hm (-1) (-2) (-3) (-4) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c174 := tp1119h x e 4 hm (-4) (-5) (-6) (-7) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c175 := tp1119h x e 4 hm 1 0 (-1) (-2) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c176 := btrue1119h (hend (-12)).1
  have c177 := btrue1119h (hend (-12)).2
  have c178 := bimp1119h _ _ (hp (-12)).2.1
  have c179 := bimp1119h _ _ (hp (-12)).2.2.2.2.1
  have c180 := btrue1119h (hend (-11)).1
  have c181 := btrue1119h (hend (-11)).2
  have c182 := bimp1119h _ _ (hp (-11)).2.1
  have c183 := bimp1119h _ _ (hp (-11)).2.2.2.2.1
  have c184 := btrue1119h (hend (-10)).1
  have c185 := btrue1119h (hend (-10)).2
  have c186 := bimp1119h _ _ (hp (-10)).2.1
  have c187 := bimp1119h _ _ (hp (-10)).2.2.2.2.1
  have c188 := btrue1119h (hend (-9)).1
  have c189 := btrue1119h (hend (-9)).2
  have c190 := bimp1119h _ _ (hp (-9)).2.1
  have c191 := bimp1119h _ _ (hp (-9)).2.2.2.2.1
  have c192 := btrue1119h (hend (-8)).1
  have c193 := btrue1119h (hend (-8)).2
  have c194 := bimp1119h _ _ (hp (-8)).2.1
  have c195 := bimp1119h _ _ (hp (-8)).2.2.2.2.1
  have c196 := btrue1119h (hend (-7)).1
  have c197 := btrue1119h (hend (-7)).2
  have c198 := bimp1119h _ _ (hp (-7)).2.1
  have c199 := bimp1119h _ _ (hp (-7)).2.2.2.2.1
  have c200 := btrue1119h (hend (-6)).1
  have c201 := btrue1119h (hend (-6)).2
  have c202 := bimp1119h _ _ (hp (-6)).2.1
  have c203 := bimp1119h _ _ (hp (-6)).2.2.2.2.1
  have c204 := btrue1119h (hend (-5)).1
  have c205 := btrue1119h (hend (-5)).2
  have c206 := bimp1119h _ _ (hp (-5)).2.1
  have c207 := bimp1119h _ _ (hp (-5)).2.2.2.2.1
  have c208 := btrue1119h (hend (-4)).1
  have c209 := btrue1119h (hend (-4)).2
  have c210 := bimp1119h _ _ (hp (-4)).2.1
  have c211 := bimp1119h _ _ (hp (-4)).2.2.2.2.1
  have c212 := btrue1119h (hend (-3)).1
  have c213 := btrue1119h (hend (-3)).2
  have c214 := bimp1119h _ _ (hp (-3)).2.1
  have c215 := bimp1119h _ _ (hp (-3)).2.2.2.2.1
  have c216 := btrue1119h (hend (-2)).1
  have c217 := btrue1119h (hend (-2)).2
  have c218 := bimp1119h _ _ (hp (-2)).2.1
  have c219 := bimp1119h _ _ (hp (-2)).2.2.2.2.1
  have c220 := btrue1119h (hend (-1)).1
  have c221 := btrue1119h (hend (-1)).2
  have c222 := bimp1119h _ _ (hp (-1)).2.1
  have c223 := bimp1119h _ _ (hp (-1)).2.2.2.2.1
  have c224 := btrue1119h (hend 0).1
  have c225 := btrue1119h (hend 0).2
  have c226 := bimp1119h _ _ (hp 0).2.1
  have c227 := bimp1119h _ _ (hp 0).2.2.2.2.1
  have c228 := btrue1119h (hend 1).1
  have c229 := btrue1119h (hend 1).2
  have c230 := bimp1119h _ _ (hp 1).2.1
  have c231 := bimp1119h _ _ (hp 1).2.2.2.2.1
  have c232 := btrue1119h (hend 2).1
  have c233 := btrue1119h (hend 2).2
  have c234 := bimp1119h _ _ (hp 2).2.1
  have c235 := bimp1119h _ _ (hp 2).2.2.2.2.1
  have c236 := btrue1119h (hend 3).1
  have c237 := btrue1119h (hend 3).2
  have c238 := bimp1119h _ _ (hp 3).2.1
  have c239 := bimp1119h _ _ (hp 3).2.2.2.2.1
  have c240 := btrue1119h (hend 4).1
  have c241 := btrue1119h (hend 4).2
  have c242 := bimp1119h _ _ (hp 4).2.1
  have c243 := bimp1119h _ _ (hp 4).2.2.2.2.1
  have c244 := btrue1119h (hend 5).1
  have c245 := btrue1119h (hend 5).2
  have c246 := bimp1119h _ _ (hp 5).2.1
  have c247 := bimp1119h _ _ (hp 5).2.2.2.2.1
  have c248 := btrue1119h (hend 6).1
  have c249 := btrue1119h (hend 6).2
  have c250 := bimp1119h _ _ (hp 6).2.1
  have c251 := bimp1119h _ _ (hp 6).2.2.2.2.1
  have c252 := btrue1119h he0
  have b0 := ble1119h (x (-1) 0 && x (-1) 2)
  have b1 := ble1119h (x (-1) 0 && x (-1) 5)
  have b2 := ble1119h (x (-1) 1 && x (-1) 2)
  have b3 := ble1119h (x (-1) 1 && x (-1) 4)
  have b4 := ble1119h (x (-1) 1 && x (-1) 6)
  have b5 := ble1119h (x (-1) 2 && x (-1) 5)
  have b6 := ble1119h (x (-1) 2 && x (-1) 7)
  have b7 := ble1119h (x (-1) 6 && x (-1) 7)
  have b8 := ble1119h (x (-10) 5 && x (-10) 6)
  have b9 := ble1119h (x (-11) 6 && x (-11) 7)
  have b10 := ble1119h (x (-2) 0 && x (-2) 2)
  have b11 := ble1119h (x (-2) 0 && x (-2) 3)
  have b12 := ble1119h (x (-2) 0 && x (-2) 5)
  have b13 := ble1119h (x (-2) 1 && x (-2) 3)
  have b14 := ble1119h (x (-2) 1 && x (-2) 6)
  have b15 := ble1119h (x (-2) 2 && x (-2) 3)
  have b16 := ble1119h (x (-2) 2 && x (-2) 5)
  have b17 := ble1119h (x (-2) 2 && x (-2) 7)
  have b18 := ble1119h (x (-2) 3 && x (-2) 6)
  have b19 := ble1119h (x (-3) 1 && x (-3) 3)
  have b20 := ble1119h (x (-3) 1 && x (-3) 4)
  have b21 := ble1119h (x (-3) 1 && x (-3) 6)
  have b22 := ble1119h (x (-3) 2 && x (-3) 4)
  have b23 := ble1119h (x (-3) 2 && x (-3) 7)
  have b24 := ble1119h (x (-3) 3 && x (-3) 4)
  have b25 := ble1119h (x (-3) 3 && x (-3) 6)
  have b26 := ble1119h (x (-3) 4 && x (-3) 7)
  have b27 := ble1119h (x (-4) 0 && x (-4) 5)
  have b28 := ble1119h (x (-4) 2 && x (-4) 4)
  have b29 := ble1119h (x (-4) 2 && x (-4) 5)
  have b30 := ble1119h (x (-4) 2 && x (-4) 7)
  have b31 := ble1119h (x (-4) 3 && x (-4) 5)
  have b32 := ble1119h (x (-4) 4 && x (-4) 5)
  have b33 := ble1119h (x (-4) 4 && x (-4) 7)
  have b34 := ble1119h (x (-5) 0 && x (-5) 1)
  have b35 := ble1119h (x (-5) 0 && x (-5) 5)
  have b36 := ble1119h (x (-5) 1 && x (-5) 6)
  have b37 := ble1119h (x (-5) 3 && x (-5) 5)
  have b38 := ble1119h (x (-5) 3 && x (-5) 6)
  have b39 := ble1119h (x (-5) 4 && x (-5) 6)
  have b40 := ble1119h (x (-5) 5 && x (-5) 6)
  have b41 := ble1119h (x (-6) 0 && x (-6) 5)
  have b42 := ble1119h (x (-6) 1 && x (-6) 2)
  have b43 := ble1119h (x (-6) 1 && x (-6) 6)
  have b44 := ble1119h (x (-6) 2 && x (-6) 7)
  have b45 := ble1119h (x (-6) 4 && x (-6) 6)
  have b46 := ble1119h (x (-6) 4 && x (-6) 7)
  have b47 := ble1119h (x (-6) 5 && x (-6) 7)
  have b48 := ble1119h (x (-6) 6 && x (-6) 7)
  have b49 := ble1119h (x (-7) 1 && x (-7) 6)
  have b50 := ble1119h (x (-7) 2 && x (-7) 3)
  have b51 := ble1119h (x (-7) 2 && x (-7) 7)
  have b52 := ble1119h (x (-7) 5 && x (-7) 7)
  have b53 := ble1119h (x (-8) 2 && x (-8) 7)
  have b54 := ble1119h (x (-8) 3 && x (-8) 4)
  have b55 := ble1119h (x (-9) 4 && x (-9) 5)
  have b56 := ble1119h (x 0 0 && x 0 1)
  have b57 := ble1119h (x 0 0 && x 0 3)
  have b58 := ble1119h (x 0 0 && x 0 5)
  have b59 := ble1119h (x 0 1 && x 0 4)
  have b60 := ble1119h (x 0 1 && x 0 6)
  have b61 := ble1119h (x 0 5 && x 0 6)
  have b62 := ble1119h (x 1 0 && x 1 3)
  have b63 := ble1119h (x 1 0 && x 1 5)
  have b64 := ble1119h (x 1 2 && x 1 7)
  have b65 := ble1119h (x 1 4 && x 1 5)
  have b66 := ble1119h (x 2 1 && x 2 6)
  have b67 := ble1119h (x 2 3 && x 2 4)
  have b68 := ble1119h (x 3 0 && x 3 5)
  have b69 := ble1119h (x 3 2 && x 3 3)
  have b70 := ble1119h (x 4 1 && x 4 2)
  have b71 := ble1119h (x 5 0 && x 5 1)
  have b72 := ble1119h (e (-1))
  have b73 := ble1119h (e (-2))
  have b74 := ble1119h (e (-5))
  have b75 := ble1119h (e 0)
  have b76 := ble1119h (e 1)
  have b77 := ble1119h (e 3)
  have b78 := ble1119h (e 4)
  have b79 := ble1119h (e 5)
  have b80 := ble1119h (e 6)
  have b81 := ble1119h (x (-1) 0)
  have b82 := ble1119h (x (-1) 1)
  have b83 := ble1119h (x (-1) 2)
  have b84 := ble1119h (x (-1) 4)
  have b85 := ble1119h (x (-1) 5)
  have b86 := ble1119h (x (-1) 6)
  have b87 := ble1119h (x (-1) 7)
  have b88 := ble1119h (x (-10) 0)
  have b89 := ble1119h (x (-10) 1)
  have b90 := ble1119h (x (-10) 2)
  have b91 := ble1119h (x (-10) 5)
  have b92 := ble1119h (x (-10) 6)
  have b93 := ble1119h (x (-10) 7)
  have b94 := ble1119h (x (-11) 0)
  have b95 := ble1119h (x (-11) 1)
  have b96 := ble1119h (x (-11) 2)
  have b97 := ble1119h (x (-11) 5)
  have b98 := ble1119h (x (-11) 6)
  have b99 := ble1119h (x (-11) 7)
  have b100 := ble1119h (x (-12) 0)
  have b101 := ble1119h (x (-12) 1)
  have b102 := ble1119h (x (-12) 2)
  have b103 := ble1119h (x (-12) 5)
  have b104 := ble1119h (x (-12) 6)
  have b105 := ble1119h (x (-12) 7)
  have b106 := ble1119h (x (-2) 0)
  have b107 := ble1119h (x (-2) 1)
  have b108 := ble1119h (x (-2) 2)
  have b109 := ble1119h (x (-2) 3)
  have b110 := ble1119h (x (-2) 5)
  have b111 := ble1119h (x (-2) 6)
  have b112 := ble1119h (x (-2) 7)
  have b113 := ble1119h (x (-3) 0)
  have b114 := ble1119h (x (-3) 1)
  have b115 := ble1119h (x (-3) 2)
  have b116 := ble1119h (x (-3) 3)
  have b117 := ble1119h (x (-3) 4)
  have b118 := ble1119h (x (-3) 5)
  have b119 := ble1119h (x (-3) 6)
  have b120 := ble1119h (x (-3) 7)
  have b121 := ble1119h (x (-4) 0)
  have b122 := ble1119h (x (-4) 1)
  have b123 := ble1119h (x (-4) 2)
  have b124 := ble1119h (x (-4) 3)
  have b125 := ble1119h (x (-4) 4)
  have b126 := ble1119h (x (-4) 5)
  have b127 := ble1119h (x (-4) 6)
  have b128 := ble1119h (x (-4) 7)
  have b129 := ble1119h (x (-5) 0)
  have b130 := ble1119h (x (-5) 1)
  have b131 := ble1119h (x (-5) 2)
  have b132 := ble1119h (x (-5) 3)
  have b133 := ble1119h (x (-5) 4)
  have b134 := ble1119h (x (-5) 5)
  have b135 := ble1119h (x (-5) 6)
  have b136 := ble1119h (x (-5) 7)
  have b137 := ble1119h (x (-6) 0)
  have b138 := ble1119h (x (-6) 1)
  have b139 := ble1119h (x (-6) 2)
  have b140 := ble1119h (x (-6) 4)
  have b141 := ble1119h (x (-6) 5)
  have b142 := ble1119h (x (-6) 6)
  have b143 := ble1119h (x (-6) 7)
  have b144 := ble1119h (x (-7) 0)
  have b145 := ble1119h (x (-7) 1)
  have b146 := ble1119h (x (-7) 2)
  have b147 := ble1119h (x (-7) 3)
  have b148 := ble1119h (x (-7) 5)
  have b149 := ble1119h (x (-7) 6)
  have b150 := ble1119h (x (-7) 7)
  have b151 := ble1119h (x (-8) 0)
  have b152 := ble1119h (x (-8) 1)
  have b153 := ble1119h (x (-8) 2)
  have b154 := ble1119h (x (-8) 3)
  have b155 := ble1119h (x (-8) 4)
  have b156 := ble1119h (x (-8) 5)
  have b157 := ble1119h (x (-8) 6)
  have b158 := ble1119h (x (-8) 7)
  have b159 := ble1119h (x (-9) 0)
  have b160 := ble1119h (x (-9) 1)
  have b161 := ble1119h (x (-9) 2)
  have b162 := ble1119h (x (-9) 4)
  have b163 := ble1119h (x (-9) 5)
  have b164 := ble1119h (x (-9) 6)
  have b165 := ble1119h (x (-9) 7)
  have b166 := ble1119h (x 0 0)
  have b167 := ble1119h (x 0 1)
  have b168 := ble1119h (x 0 2)
  have b169 := ble1119h (x 0 3)
  have b170 := ble1119h (x 0 4)
  have b171 := ble1119h (x 0 5)
  have b172 := ble1119h (x 0 6)
  have b173 := ble1119h (x 0 7)
  have b174 := ble1119h (x 1 0)
  have b175 := ble1119h (x 1 1)
  have b176 := ble1119h (x 1 2)
  have b177 := ble1119h (x 1 3)
  have b178 := ble1119h (x 1 4)
  have b179 := ble1119h (x 1 5)
  have b180 := ble1119h (x 1 6)
  have b181 := ble1119h (x 1 7)
  have b182 := ble1119h (x 2 0)
  have b183 := ble1119h (x 2 1)
  have b184 := ble1119h (x 2 2)
  have b185 := ble1119h (x 2 3)
  have b186 := ble1119h (x 2 4)
  have b187 := ble1119h (x 2 5)
  have b188 := ble1119h (x 2 6)
  have b189 := ble1119h (x 2 7)
  have b190 := ble1119h (x 3 0)
  have b191 := ble1119h (x 3 1)
  have b192 := ble1119h (x 3 2)
  have b193 := ble1119h (x 3 3)
  have b194 := ble1119h (x 3 5)
  have b195 := ble1119h (x 3 6)
  have b196 := ble1119h (x 3 7)
  have b197 := ble1119h (x 4 0)
  have b198 := ble1119h (x 4 1)
  have b199 := ble1119h (x 4 2)
  have b200 := ble1119h (x 4 5)
  have b201 := ble1119h (x 4 6)
  have b202 := ble1119h (x 4 7)
  have b203 := ble1119h (x 5 0)
  have b204 := ble1119h (x 5 1)
  have b205 := ble1119h (x 5 2)
  have b206 := ble1119h (x 5 5)
  have b207 := ble1119h (x 5 6)
  have b208 := ble1119h (x 5 7)
  have b209 := ble1119h (x 6 0)
  have b210 := ble1119h (x 6 1)
  have b211 := ble1119h (x 6 2)
  have b212 := ble1119h (x 6 5)
  have b213 := ble1119h (x 6 6)
  have b214 := ble1119h (x 6 7)
  have f1 : (x (-12) 0).toNat = 1 := by clear * - c176 b100; omega
  have f2 : (x (-12) 7).toNat = 1 := by clear * - c177 b105; omega
  have f3 : (x (-11) 0).toNat = 1 := by clear * - c180 b94; omega
  have f4 : (x (-11) 7).toNat = 1 := by clear * - c181 b99; omega
  have f5 : (x (-10) 0).toNat = 1 := by clear * - c184 b88; omega
  have f6 : (x (-10) 7).toNat = 1 := by clear * - c185 b93; omega
  have f7 : (x (-9) 0).toNat = 1 := by clear * - c188 b159; omega
  have f8 : (x (-9) 7).toNat = 1 := by clear * - c189 b165; omega
  have f9 : (x (-8) 0).toNat = 1 := by clear * - c192 b151; omega
  have f10 : (x (-8) 7).toNat = 1 := by clear * - c193 b158; omega
  have f11 : (x (-7) 0).toNat = 1 := by clear * - c196 b144; omega
  have f12 : (x (-7) 7).toNat = 1 := by clear * - c197 b150; omega
  have f13 : (x (-6) 0).toNat = 1 := by clear * - c200 b137; omega
  have f14 : (x (-6) 7).toNat = 1 := by clear * - c201 b143; omega
  have f15 : (x (-5) 0).toNat = 1 := by clear * - c204 b129; omega
  have f16 : (x (-5) 7).toNat = 1 := by clear * - c205 b136; omega
  have f17 : (x (-4) 0).toNat = 1 := by clear * - c208 b121; omega
  have f18 : (x (-4) 7).toNat = 1 := by clear * - c209 b128; omega
  have f19 : (x (-3) 0).toNat = 1 := by clear * - c212 b113; omega
  have f20 : (x (-3) 7).toNat = 1 := by clear * - c213 b120; omega
  have f21 : (x (-2) 0).toNat = 1 := by clear * - c216 b106; omega
  have f22 : (x (-2) 7).toNat = 1 := by clear * - c217 b112; omega
  have f23 : (x (-1) 0).toNat = 1 := by clear * - c220 b81; omega
  have f24 : (x (-1) 7).toNat = 1 := by clear * - c221 b87; omega
  have f25 : (x 0 0).toNat = 1 := by clear * - c224 b166; omega
  have f26 : (x 0 7).toNat = 1 := by clear * - c225 b173; omega
  have f27 : (x 1 0).toNat = 1 := by clear * - c228 b174; omega
  have f28 : (x 1 7).toNat = 1 := by clear * - c229 b181; omega
  have f29 : (x 2 0).toNat = 1 := by clear * - c232 b182; omega
  have f30 : (x 2 7).toNat = 1 := by clear * - c233 b189; omega
  have f31 : (x 3 0).toNat = 1 := by clear * - c236 b190; omega
  have f32 : (x 3 7).toNat = 1 := by clear * - c237 b196; omega
  have f33 : (x 4 0).toNat = 1 := by clear * - c240 b197; omega
  have f34 : (x 4 7).toNat = 1 := by clear * - c241 b202; omega
  have f35 : (x 5 0).toNat = 1 := by clear * - c244 b203; omega
  have f36 : (x 5 7).toNat = 1 := by clear * - c245 b208; omega
  have f37 : (x 6 0).toNat = 1 := by clear * - c248 b209; omega
  have f38 : (x 6 7).toNat = 1 := by clear * - c249 b214; omega
  have f39 : (e 0).toNat = 1 := by clear * - c252 b75; omega
  have f40 : (x (-4) 4).toNat = 0 := by clear * - c174 f39 b125 b134 b139 b147 b75; omega
  have f41 : (x (-5) 5).toNat = 0 := by clear * - c174 f39 b125 b134 b139 b147 b75; omega
  have f42 : (x (-6) 2).toNat = 0 := by clear * - c174 f39 b125 b134 b139 b147 b75; omega
  have f43 : (x (-7) 3).toNat = 0 := by clear * - c174 f39 b125 b134 b139 b147 b75; omega
  have f44 : (x (-6) 1 && x (-6) 2).toNat = 0 := by clear * - c12 f42 b42 b139; omega
  have f45 : (x (-7) 2 && x (-7) 3).toNat = 0 := by clear * - c14 f43 b50 b147; omega
  have f46 : (x (-4) 4 && x (-4) 5).toNat = 0 := by clear * - c32 f40 b32 b125; omega
  have f47 : (x (-5) 5 && x (-5) 6).toNat = 0 := by clear * - c34 f41 b40 b134; omega
  have f48 : (x (-4) 2 && x (-4) 4).toNat = 0 := by clear * - c72 f40 b28 b125; omega
  have f49 : (x (-5) 3 && x (-5) 5).toNat = 0 := by clear * - c74 f41 b37 b134; omega
  have f50 : (x (-4) 4 && x (-4) 7).toNat = 0 := by clear * - c99 f40 b33 b125; omega
  have f51 : (x (-6) 2 && x (-6) 7).toNat = 0 := by clear * - c131 f42 b44 b139; omega
  have f52 : (x (-5) 0 && x (-5) 5).toNat = 0 := by clear * - c135 f41 b35 b134; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b135 with f53 | f53
  · have f54 : (x (-5) 4 && x (-5) 6).toNat = 0 := by clear * - c63 f53 b39 b135; omega
    have f55 : (x (-5) 3 && x (-5) 6).toNat = 0 := by clear * - c87 f53 b38 b135; omega
    have f56 : (x (-5) 1 && x (-5) 6).toNat = 0 := by clear * - c130 f53 b36 b135; omega
    have f57 : (x (-4) 0 && x (-4) 5).toNat = 1 := by clear * - c126 f56 f51 b27 b36 b44; omega
    have f58 : (x (-4) 5).toNat = 1 := by clear * - c128 f57 b27 b126; omega
    have f59 : (x (-6) 1).toNat = 1 := by clear * - c171 f53 b135 b138; omega
    have f60 : (x (-5) 2).toNat = 0 := by clear * - c206 f53 b131 b135; omega
    have f61 : (x (-4) 1).toNat = 1 := by clear * - c211 f58 b126 b122; omega
    have f62 : (x (-3) 6).toNat = 0 := by clear * - c169 f61 b119 b122; omega
    have f63 : (x (-3) 3 && x (-3) 6).toNat = 0 := by clear * - c98 f62 b25 b119; omega
    have f64 : (x (-3) 1 && x (-3) 6).toNat = 0 := by clear * - c123 f62 b21 b119; omega
    have f65 : (x (-3) 2).toNat = 0 := by clear * - c214 f62 b115 b119; omega
    have f66 : (x (-3) 2 && x (-3) 4).toNat = 0 := by clear * - c58 f65 b22 b115; omega
    have f67 : (x (-3) 2 && x (-3) 7).toNat = 0 := by clear * - c117 f65 b23 b115; omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b146 with f68 | f68
    · have f69 : (x (-7) 2 && x (-7) 7).toNat = 0 := by clear * - c138 f68 b51 b146; omega
      have f70 : (x (-6) 1 && x (-6) 6).toNat = 1 := by clear * - c133 f52 f69 b35 b43 b51; omega
      have f71 : (x (-6) 6).toNat = 1 := by clear * - c137 f70 b43 b142; omega
      have f72 : (x (-1) 1).toNat = 0 := by clear * - c3 f25 f40 f41 f71 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f73 : (x (-2) 2).toNat = 0 := by clear * - c3 f25 f40 f41 f71 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f74 : (x (-3) 3).toNat = 0 := by clear * - c3 f25 f40 f41 f71 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f75 : (x (-1) 1 && x (-1) 2).toNat = 0 := by clear * - c26 f72 b2 b82; omega
      have f76 : (x (-2) 2 && x (-2) 3).toNat = 0 := by clear * - c28 f73 b15 b108; omega
      have f77 : (x (-3) 3 && x (-3) 4).toNat = 0 := by clear * - c30 f74 b24 b116; omega
      have f78 : (x (-2) 0 && x (-2) 2).toNat = 0 := by clear * - c68 f73 b10 b108; omega
      have f79 : (x (-3) 1 && x (-3) 3).toNat = 0 := by clear * - c70 f74 b19 b116; omega
      have f80 : (x (-1) 1 && x (-1) 4).toNat = 0 := by clear * - c93 f72 b3 b82; omega
      have f81 : (x (-2) 2 && x (-2) 5).toNat = 0 := by clear * - c95 f73 b16 b108; omega
      have f82 : (x 0 0 && x 0 3).toNat = 1 := by clear * - c90 f80 f81 f63 f50 b57 b3 b16 b25 b33; omega
      have f83 : (x 0 3).toNat = 1 := by clear * - c92 f82 b57 b169; omega
      have f84 : (x (-1) 1 && x (-1) 6).toNat = 0 := by clear * - c150 f72 b4 b82; omega
      have f85 : (x (-2) 2 && x (-2) 7).toNat = 0 := by clear * - c152 f73 b17 b108; omega
      have f86 : (x 0 0 && x 0 5).toNat = 1 := by clear * - c147 f84 f85 b58 b4 b17; omega
      have f87 : (x 0 5).toNat = 1 := by clear * - c149 f86 b58 b171; omega
      have f88 : (x 0 6).toNat = 1 := by clear * - c172 f72 b172 b82; omega
      have f89 : (x 1 4).toNat = 0 := by clear * - c175 f87 b178 b171 b83 b109 b79; omega
      have f90 : (x (-1) 2).toNat = 0 := by clear * - c175 f87 b178 b171 b83 b109 b79; omega
      have f91 : (x (-2) 3).toNat = 0 := by clear * - c175 f87 b178 b171 b83 b109 b79; omega
      have f92 : (e 5).toNat = 0 := by clear * - c175 f87 b178 b171 b83 b109 b79; omega
      have f93 : (x 1 4 && x 1 5).toNat = 0 := by clear * - c47 f89 b65 b178; omega
      have f94 : (x (-1) 0 && x (-1) 2).toNat = 0 := by clear * - c55 f90 b0 b83; omega
      have f95 : (x (-2) 1 && x (-2) 3).toNat = 0 := by clear * - c57 f91 b13 b109; omega
      have f96 : (x (-2) 0 && x (-2) 3).toNat = 0 := by clear * - c81 f91 b11 b109; omega
      have f97 : (x (-1) 2 && x (-1) 5).toNat = 0 := by clear * - c106 f90 b5 b83; omega
      have f98 : (x (-2) 3 && x (-2) 6).toNat = 0 := by clear * - c108 f91 b18 b109; omega
      have f99 : (x (-1) 2 && x (-1) 7).toNat = 0 := by clear * - c159 f90 b6 b83; omega
      have f100 : (x (-1) 5).toNat = 0 := by clear * - c223 f72 b85 b82; omega
      have f101 : (x (-1) 0 && x (-1) 5).toNat = 0 := by clear * - c114 f100 b1 b85; omega
      have f102 : (x (-2) 1 && x (-2) 6).toNat = 1 := by clear * - c112 f101 f67 b1 b14 b23; omega
      have f103 : (x (-2) 1).toNat = 1 := by clear * - c115 f102 b14 b107; omega
      have f104 : (x (-2) 6).toNat = 1 := by clear * - c116 f102 b14 b111; omega
      have f105 : (x (-1) 6).toNat = 0 := by clear * - c168 f103 b86 b107; omega
      have f106 : (x (-1) 6 && x (-1) 7).toNat = 0 := by clear * - c51 f105 b7 b86; omega
      have f107 : (x 0 1).toNat = 1 := by clear * - c227 f87 b171 b167; omega
      have f108 : (x (-3) 4).toNat = 0 := by clear * - c4 f27 f107 f90 f91 f58 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f109 : (e 1).toNat = 0 := by clear * - c4 f27 f107 f90 f91 f58 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f110 : (x (-3) 1 && x (-3) 4).toNat = 0 := by clear * - c83 f108 b20 b117; omega
      have f111 : (x (-3) 4 && x (-3) 7).toNat = 0 := by clear * - c110 f108 b26 b117; omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b170 with f112 | f112
      · have f113 : (x 0 1 && x 0 4).toNat = 0 := by clear * - c105 f112 b59 b170; omega
        have f114 : (x 1 0 && x 1 3).toNat = 1 := by clear * - c101 f113 f97 f98 f111 b62 b59 b5 b18 b26; omega
        have f115 : (x 1 3).toNat = 1 := by clear * - c103 f114 b62 b177; omega
        have f116 : (x 3 1).toNat = 0 := by clear * - c6 f33 f115 f112 f100 f104 f20 b197 b191 b184 b177 b170 b85 b111 b120 b78; omega
        have f117 : (x 2 2).toNat = 0 := by clear * - c6 f33 f115 f112 f100 f104 f20 b197 b191 b184 b177 b170 b85 b111 b120 b78; omega
        have f118 : (e 4).toNat = 0 := by clear * - c6 f33 f115 f112 f100 f104 f20 b197 b191 b184 b177 b170 b85 b111 b120 b78; omega
        have f119 : (x 3 5).toNat = 0 := by clear * - c239 f116 b194 b191; omega
        have f120 : (x 3 0 && x 3 5).toNat = 0 := by clear * - c163 f119 b68 b194; omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b176 with f121 | f121
        · have f122 : (x 1 2 && x 1 7).toNat = 0 := by clear * - c166 f121 b64 b176; omega
          have f123 : (x 2 1 && x 2 6).toNat = 1 := by clear * - c161 f120 f122 b68 b66 b64; omega
          have f124 : (x 2 1).toNat = 1 := by clear * - c164 f123 b66 b183; omega
          have f125 : (x (-1) 4).toNat = 0 := by clear * - c5 f31 f124 f121 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f126 : (x (-2) 5).toNat = 0 := by clear * - c5 f31 f124 f121 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f127 : (e 3).toNat = 0 := by clear * - c5 f31 f124 f121 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f128 : (x (-2) 0 && x (-2) 5).toNat = 0 := by clear * - c121 f126 b12 b110; omega
          have f129 : (x (-4) 2 && x (-4) 7).toNat = 1 := by clear * - c119 f128 f64 b12 b21 b30; omega
          have f130 : (x (-4) 2).toNat = 1 := by clear * - c124 f129 b30 b123; omega
          have f131 : (x 2 6).toNat = 1 := by clear * - c165 f123 b66 b188; omega
          have f132 : (x (-4) 3).toNat = 1 := by clear * - c173 f125 f126 f65 f127 b84 b110 b115 b124 b77; omega
          have f133 : (x (-5) 4).toNat = 0 := by clear * - c0 f23 f103 f65 f132 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f134 : (x (-6) 5).toNat = 0 := by clear * - c0 f23 f103 f65 f132 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f135 : (x (-7) 6).toNat = 0 := by clear * - c0 f23 f103 f65 f132 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f136 : (e (-1)).toNat = 0 := by clear * - c0 f23 f103 f65 f132 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f137 : (x (-6) 5 && x (-6) 7).toNat = 0 := by clear * - c64 f134 b47 b141; omega
          have f138 : (x (-4) 3 && x (-4) 5).toNat = 1 := by clear * - c53 f94 f95 f66 f54 f137 b0 b13 b22 b31 b39 b47; omega
          have f139 : (x (-6) 0 && x (-6) 5).toNat = 0 := by clear * - c142 f134 b41 b141; omega
          have f140 : (x (-7) 1 && x (-7) 6).toNat = 0 := by clear * - c144 f135 b49 b149; omega
          have f141 : (x (-8) 2 && x (-8) 7).toNat = 1 := by clear * - c140 f139 f140 b41 b49 b53; omega
          have f142 : (x (-8) 2).toNat = 1 := by clear * - c145 f141 b53 b153; omega
          have f143 : (x (-8) 6).toNat = 1 := by clear * - c194 f142 b153 b157; omega
          have f144 : (x (-3) 1).toNat = 0 := by clear * - c1 f21 f130 f143 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f145 : (x (-5) 3).toNat = 0 := by clear * - c1 f21 f130 f143 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f146 : (x (-6) 4).toNat = 0 := by clear * - c1 f21 f130 f143 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f147 : (x (-7) 5).toNat = 0 := by clear * - c1 f21 f130 f143 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f148 : (e (-2)).toNat = 0 := by clear * - c1 f21 f130 f143 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f149 : (x (-6) 4 && x (-6) 6).toNat = 0 := by clear * - c75 f146 b45 b140; omega
          have f150 : (x (-7) 5 && x (-7) 7).toNat = 1 := by clear * - c66 f78 f79 f48 f49 f149 b10 b19 b28 b37 b45 b52; omega
          clear * - c77 f150 f147 b52 b148; omega
        · have f151 : (x 2 1).toNat = 0 := by clear * - c5 f31 f121 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f152 : (x (-1) 4).toNat = 0 := by clear * - c5 f31 f121 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f153 : (x (-2) 5).toNat = 0 := by clear * - c5 f31 f121 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f154 : (e 3).toNat = 0 := by clear * - c5 f31 f121 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f155 : (x (-2) 0 && x (-2) 5).toNat = 0 := by clear * - c121 f153 b12 b110; omega
          have f156 : (x (-4) 2 && x (-4) 7).toNat = 1 := by clear * - c119 f155 f64 b12 b21 b30; omega
          have f157 : (x (-4) 2).toNat = 1 := by clear * - c124 f156 b30 b123; omega
          have f158 : (x 2 1 && x 2 6).toNat = 0 := by clear * - c164 f151 b66 b183; omega
          have f159 : (x 1 2 && x 1 7).toNat = 1 := by clear * - c161 f120 f158 b68 b66 b64; omega
          have f160 : (x (-4) 3).toNat = 1 := by clear * - c173 f152 f153 f65 f154 b84 b110 b115 b124 b77; omega
          have f161 : (x (-5) 4).toNat = 0 := by clear * - c0 f23 f103 f65 f160 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f162 : (x (-6) 5).toNat = 0 := by clear * - c0 f23 f103 f65 f160 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f163 : (x (-7) 6).toNat = 0 := by clear * - c0 f23 f103 f65 f160 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f164 : (e (-1)).toNat = 0 := by clear * - c0 f23 f103 f65 f160 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f165 : (x (-6) 5 && x (-6) 7).toNat = 0 := by clear * - c64 f162 b47 b141; omega
          have f166 : (x (-4) 3 && x (-4) 5).toNat = 1 := by clear * - c53 f94 f95 f66 f54 f165 b0 b13 b22 b31 b39 b47; omega
          have f167 : (x (-6) 0 && x (-6) 5).toNat = 0 := by clear * - c142 f162 b41 b141; omega
          have f168 : (x (-7) 1 && x (-7) 6).toNat = 0 := by clear * - c144 f163 b49 b149; omega
          have f169 : (x (-8) 2 && x (-8) 7).toNat = 1 := by clear * - c140 f167 f168 b41 b49 b53; omega
          have f170 : (x (-8) 2).toNat = 1 := by clear * - c145 f169 b53 b153; omega
          have f171 : (x (-8) 6).toNat = 1 := by clear * - c194 f170 b153 b157; omega
          have f172 : (x (-3) 1).toNat = 0 := by clear * - c1 f21 f157 f171 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f173 : (x (-5) 3).toNat = 0 := by clear * - c1 f21 f157 f171 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f174 : (x (-6) 4).toNat = 0 := by clear * - c1 f21 f157 f171 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f175 : (x (-7) 5).toNat = 0 := by clear * - c1 f21 f157 f171 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f176 : (e (-2)).toNat = 0 := by clear * - c1 f21 f157 f171 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f177 : (x (-6) 4 && x (-6) 6).toNat = 0 := by clear * - c75 f174 b45 b140; omega
          have f178 : (x (-7) 5 && x (-7) 7).toNat = 1 := by clear * - c66 f78 f79 f48 f49 f177 b10 b19 b28 b37 b45 b52; omega
          clear * - c77 f178 f175 b52 b148; omega
      · have f179 : (x 3 1).toNat = 0 := by clear * - c6 f33 f112 f100 f104 f20 b197 b191 b184 b177 b170 b85 b111 b120 b78; omega
        have f180 : (x 2 2).toNat = 0 := by clear * - c6 f33 f112 f100 f104 f20 b197 b191 b184 b177 b170 b85 b111 b120 b78; omega
        have f181 : (x 1 3).toNat = 0 := by clear * - c6 f33 f112 f100 f104 f20 b197 b191 b184 b177 b170 b85 b111 b120 b78; omega
        have f182 : (e 4).toNat = 0 := by clear * - c6 f33 f112 f100 f104 f20 b197 b191 b184 b177 b170 b85 b111 b120 b78; omega
        have f183 : (x 1 0 && x 1 3).toNat = 0 := by clear * - c103 f181 b62 b177; omega
        have f184 : (x 0 1 && x 0 4).toNat = 1 := by clear * - c101 f183 f97 f98 f111 b62 b59 b5 b18 b26; omega
        have f185 : (x 3 5).toNat = 0 := by clear * - c239 f179 b194 b191; omega
        have f186 : (x 3 0 && x 3 5).toNat = 0 := by clear * - c163 f185 b68 b194; omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b176 with f187 | f187
        · have f188 : (x 1 2 && x 1 7).toNat = 0 := by clear * - c166 f187 b64 b176; omega
          have f189 : (x 2 1 && x 2 6).toNat = 1 := by clear * - c161 f186 f188 b68 b66 b64; omega
          have f190 : (x 2 1).toNat = 1 := by clear * - c164 f189 b66 b183; omega
          have f191 : (x (-1) 4).toNat = 0 := by clear * - c5 f31 f190 f187 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f192 : (x (-2) 5).toNat = 0 := by clear * - c5 f31 f190 f187 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f193 : (e 3).toNat = 0 := by clear * - c5 f31 f190 f187 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f194 : (x (-2) 0 && x (-2) 5).toNat = 0 := by clear * - c121 f192 b12 b110; omega
          have f195 : (x (-4) 2 && x (-4) 7).toNat = 1 := by clear * - c119 f194 f64 b12 b21 b30; omega
          have f196 : (x (-4) 2).toNat = 1 := by clear * - c124 f195 b30 b123; omega
          have f197 : (x 2 6).toNat = 1 := by clear * - c165 f189 b66 b188; omega
          have f198 : (x (-4) 3).toNat = 1 := by clear * - c173 f191 f192 f65 f193 b84 b110 b115 b124 b77; omega
          have f199 : (x (-5) 4).toNat = 0 := by clear * - c0 f23 f103 f65 f198 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f200 : (x (-6) 5).toNat = 0 := by clear * - c0 f23 f103 f65 f198 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f201 : (x (-7) 6).toNat = 0 := by clear * - c0 f23 f103 f65 f198 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f202 : (e (-1)).toNat = 0 := by clear * - c0 f23 f103 f65 f198 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f203 : (x (-6) 5 && x (-6) 7).toNat = 0 := by clear * - c64 f200 b47 b141; omega
          have f204 : (x (-4) 3 && x (-4) 5).toNat = 1 := by clear * - c53 f94 f95 f66 f54 f203 b0 b13 b22 b31 b39 b47; omega
          have f205 : (x (-6) 0 && x (-6) 5).toNat = 0 := by clear * - c142 f200 b41 b141; omega
          have f206 : (x (-7) 1 && x (-7) 6).toNat = 0 := by clear * - c144 f201 b49 b149; omega
          have f207 : (x (-8) 2 && x (-8) 7).toNat = 1 := by clear * - c140 f205 f206 b41 b49 b53; omega
          have f208 : (x (-8) 2).toNat = 1 := by clear * - c145 f207 b53 b153; omega
          have f209 : (x (-8) 6).toNat = 1 := by clear * - c194 f208 b153 b157; omega
          have f210 : (x (-3) 1).toNat = 0 := by clear * - c1 f21 f196 f209 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f211 : (x (-5) 3).toNat = 0 := by clear * - c1 f21 f196 f209 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f212 : (x (-6) 4).toNat = 0 := by clear * - c1 f21 f196 f209 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f213 : (x (-7) 5).toNat = 0 := by clear * - c1 f21 f196 f209 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f214 : (e (-2)).toNat = 0 := by clear * - c1 f21 f196 f209 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f215 : (x (-6) 4 && x (-6) 6).toNat = 0 := by clear * - c75 f212 b45 b140; omega
          have f216 : (x (-7) 5 && x (-7) 7).toNat = 1 := by clear * - c66 f78 f79 f48 f49 f215 b10 b19 b28 b37 b45 b52; omega
          clear * - c77 f216 f213 b52 b148; omega
        · have f217 : (x 2 1).toNat = 0 := by clear * - c5 f31 f187 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f218 : (x (-1) 4).toNat = 0 := by clear * - c5 f31 f187 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f219 : (x (-2) 5).toNat = 0 := by clear * - c5 f31 f187 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f220 : (e 3).toNat = 0 := by clear * - c5 f31 f187 f83 f62 f18 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
          have f221 : (x (-2) 0 && x (-2) 5).toNat = 0 := by clear * - c121 f219 b12 b110; omega
          have f222 : (x (-4) 2 && x (-4) 7).toNat = 1 := by clear * - c119 f221 f64 b12 b21 b30; omega
          have f223 : (x (-4) 2).toNat = 1 := by clear * - c124 f222 b30 b123; omega
          have f224 : (x 2 1 && x 2 6).toNat = 0 := by clear * - c164 f217 b66 b183; omega
          have f225 : (x 1 2 && x 1 7).toNat = 1 := by clear * - c161 f186 f224 b68 b66 b64; omega
          have f226 : (x (-4) 3).toNat = 1 := by clear * - c173 f218 f219 f65 f220 b84 b110 b115 b124 b77; omega
          have f227 : (x (-5) 4).toNat = 0 := by clear * - c0 f23 f103 f65 f226 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f228 : (x (-6) 5).toNat = 0 := by clear * - c0 f23 f103 f65 f226 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f229 : (x (-7) 6).toNat = 0 := by clear * - c0 f23 f103 f65 f226 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f230 : (e (-1)).toNat = 0 := by clear * - c0 f23 f103 f65 f226 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f231 : (x (-6) 5 && x (-6) 7).toNat = 0 := by clear * - c64 f228 b47 b141; omega
          have f232 : (x (-4) 3 && x (-4) 5).toNat = 1 := by clear * - c53 f94 f95 f66 f54 f231 b0 b13 b22 b31 b39 b47; omega
          have f233 : (x (-6) 0 && x (-6) 5).toNat = 0 := by clear * - c142 f228 b41 b141; omega
          have f234 : (x (-7) 1 && x (-7) 6).toNat = 0 := by clear * - c144 f229 b49 b149; omega
          have f235 : (x (-8) 2 && x (-8) 7).toNat = 1 := by clear * - c140 f233 f234 b41 b49 b53; omega
          have f236 : (x (-8) 2).toNat = 1 := by clear * - c145 f235 b53 b153; omega
          have f237 : (x (-8) 6).toNat = 1 := by clear * - c194 f236 b153 b157; omega
          have f238 : (x (-3) 1).toNat = 0 := by clear * - c1 f21 f223 f237 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f239 : (x (-5) 3).toNat = 0 := by clear * - c1 f21 f223 f237 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f240 : (x (-6) 4).toNat = 0 := by clear * - c1 f21 f223 f237 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f241 : (x (-7) 5).toNat = 0 := by clear * - c1 f21 f223 f237 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f242 : (e (-2)).toNat = 0 := by clear * - c1 f21 f223 f237 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f243 : (x (-6) 4 && x (-6) 6).toNat = 0 := by clear * - c75 f240 b45 b140; omega
          have f244 : (x (-7) 5 && x (-7) 7).toNat = 1 := by clear * - c66 f78 f79 f48 f49 f243 b10 b19 b28 b37 b45 b52; omega
          clear * - c77 f244 f241 b52 b148; omega
    · have f245 : (x (-8) 3).toNat = 0 := by clear * - c2 f15 f59 f68 f2 b129 b138 b146 b154 b162 b91 b98 b105 b74; omega
      have f246 : (x (-9) 4).toNat = 0 := by clear * - c2 f15 f59 f68 f2 b129 b138 b146 b154 b162 b91 b98 b105 b74; omega
      have f247 : (x (-10) 5).toNat = 0 := by clear * - c2 f15 f59 f68 f2 b129 b138 b146 b154 b162 b91 b98 b105 b74; omega
      have f248 : (x (-11) 6).toNat = 0 := by clear * - c2 f15 f59 f68 f2 b129 b138 b146 b154 b162 b91 b98 b105 b74; omega
      have f249 : (e (-5)).toNat = 0 := by clear * - c2 f15 f59 f68 f2 b129 b138 b146 b154 b162 b91 b98 b105 b74; omega
      have f250 : (x (-8) 3 && x (-8) 4).toNat = 0 := by clear * - c15 f245 b54 b154; omega
      have f251 : (x (-9) 4 && x (-9) 5).toNat = 0 := by clear * - c17 f246 b55 b162; omega
      have f252 : (x (-10) 5 && x (-10) 6).toNat = 0 := by clear * - c19 f247 b8 b91; omega
      have f253 : (x (-11) 6 && x (-11) 7).toNat = 0 := by clear * - c21 f248 b9 b98; omega
      have f254 : (x (-5) 0 && x (-5) 1).toNat = 1 := by clear * - c8 f44 f45 f250 f251 f252 f253 b34 b42 b50 b54 b55 b8 b9; omega
      have f255 : (x (-5) 1).toNat = 1 := by clear * - c10 f254 b34 b130; omega
      have f256 : (x (-4) 6).toNat = 0 := by clear * - c170 f255 b127 b130; omega
      have f257 : (x (-11) 2).toNat = 0 := by clear * - c182 f248 b96 b98; omega
      have f258 : (x (-7) 6).toNat = 1 := by clear * - c198 f68 b146 b149; omega
      have f259 : (x (-4) 2).toNat = 0 := by clear * - c210 f256 b123 b127; omega
      have f260 : (x (-4) 2 && x (-4) 5).toNat = 0 := by clear * - c84 f259 b29 b123; omega
      have f261 : (x (-4) 2 && x (-4) 7).toNat = 0 := by clear * - c124 f259 b30 b123; omega
      have f262 : (x (-2) 0 && x (-2) 5).toNat = 1 := by clear * - c119 f64 f261 b12 b21 b30; omega
      have f263 : (x (-2) 5).toNat = 1 := by clear * - c121 f262 b12 b110; omega
      have f264 : (x (-1) 4).toNat = 0 := by clear * - c173 f263 f65 b84 b110 b115 b124 b77; omega
      have f265 : (x (-4) 3).toNat = 0 := by clear * - c173 f263 f65 b84 b110 b115 b124 b77; omega
      have f266 : (e 3).toNat = 0 := by clear * - c173 f263 f65 b84 b110 b115 b124 b77; omega
      have f267 : (x (-4) 3 && x (-4) 5).toNat = 0 := by clear * - c60 f265 b31 b124; omega
      have f268 : (x (-1) 1 && x (-1) 4).toNat = 0 := by clear * - c94 f264 b3 b84; omega
      have f269 : (x (-2) 1).toNat = 1 := by clear * - c219 f263 b110 b107; omega
      have f270 : (x (-5) 4).toNat = 0 := by clear * - c0 f23 f269 f65 f265 f258 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
      have f271 : (x (-6) 5).toNat = 0 := by clear * - c0 f23 f269 f65 f265 f258 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
      have f272 : (e (-1)).toNat = 0 := by clear * - c0 f23 f269 f65 f265 f258 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
      have f273 : (x (-6) 5 && x (-6) 7).toNat = 0 := by clear * - c64 f271 b47 b141; omega
      have f274 : (x (-6) 0 && x (-6) 5).toNat = 0 := by clear * - c142 f271 b41 b141; omega
      have f275 : (x (-1) 6).toNat = 0 := by clear * - c168 f269 b86 b107; omega
      have f276 : (x (-1) 6 && x (-1) 7).toNat = 0 := by clear * - c51 f275 b7 b86; omega
      have f277 : (x (-1) 1 && x (-1) 6).toNat = 0 := by clear * - c151 f275 b4 b86; omega
      have f278 : (x (-1) 2).toNat = 0 := by clear * - c222 f275 b83 b86; omega
      have f279 : (x (-1) 1 && x (-1) 2).toNat = 0 := by clear * - c27 f278 b2 b83; omega
      have f280 : (x (-1) 0 && x (-1) 2).toNat = 0 := by clear * - c55 f278 b0 b83; omega
      have f281 : (x (-2) 1 && x (-2) 3).toNat = 1 := by clear * - c53 f280 f66 f267 f54 f273 b0 b13 b22 b31 b39 b47; omega
      have f282 : (x (-2) 3).toNat = 1 := by clear * - c57 f281 b13 b109; omega
      have f283 : (x 0 1).toNat = 0 := by clear * - c4 f27 f278 f282 f58 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f284 : (x (-3) 4).toNat = 0 := by clear * - c4 f27 f278 f282 f58 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f285 : (e 1).toNat = 0 := by clear * - c4 f27 f278 f282 f58 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f286 : (x 0 0 && x 0 1).toNat = 0 := by clear * - c25 f283 b56 b167; omega
      have f287 : (x (-3) 3 && x (-3) 4).toNat = 0 := by clear * - c31 f284 b24 b117; omega
      have f288 : (x (-3) 1 && x (-3) 4).toNat = 0 := by clear * - c83 f284 b20 b117; omega
      have f289 : (x 0 1 && x 0 4).toNat = 0 := by clear * - c104 f283 b59 b167; omega
      have f290 : (x (-1) 2 && x (-1) 5).toNat = 0 := by clear * - c106 f278 b5 b83; omega
      have f291 : (x (-3) 4 && x (-3) 7).toNat = 0 := by clear * - c110 f284 b26 b117; omega
      have f292 : (x 0 1 && x 0 6).toNat = 0 := by clear * - c157 f283 b60 b167; omega
      have f293 : (x (-1) 2 && x (-1) 7).toNat = 0 := by clear * - c159 f278 b6 b83; omega
      have f294 : (x 1 0 && x 1 5).toNat = 1 := by clear * - c154 f292 f293 b63 b60 b6; omega
      have f295 : (x 1 5).toNat = 1 := by clear * - c156 f294 b63 b179; omega
      have f296 : (x 1 4).toNat = 0 := by clear * - c175 f278 f282 b178 b171 b83 b109 b79; omega
      have f297 : (x 0 5).toNat = 0 := by clear * - c175 f278 f282 b178 b171 b83 b109 b79; omega
      have f298 : (e 5).toNat = 0 := by clear * - c175 f278 f282 b178 b171 b83 b109 b79; omega
      have f299 : (x 1 4 && x 1 5).toNat = 0 := by clear * - c47 f296 b65 b178; omega
      have f300 : (x 0 5 && x 0 6).toNat = 0 := by clear * - c49 f297 b61 b171; omega
      have f301 : (x 0 0 && x 0 5).toNat = 0 := by clear * - c149 f297 b58 b171; omega
      have f302 : (x (-2) 2 && x (-2) 7).toNat = 1 := by clear * - c147 f301 f277 b58 b4 b17; omega
      have f303 : (x (-2) 2).toNat = 1 := by clear * - c152 f302 b17 b108; omega
      have f304 : (x (-1) 1).toNat = 0 := by clear * - c3 f25 f303 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f305 : (x (-3) 3).toNat = 0 := by clear * - c3 f25 f303 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f306 : (x (-6) 6).toNat = 0 := by clear * - c3 f25 f303 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f307 : (x (-6) 6 && x (-6) 7).toNat = 0 := by clear * - c36 f306 b48 b142; omega
      have f308 : (x (-2) 2 && x (-2) 3).toNat = 1 := by clear * - c23 f286 f279 f287 f46 f47 f307 b56 b2 b15 b24 b32 b40 b48; omega
      have f309 : (x (-3) 1 && x (-3) 3).toNat = 0 := by clear * - c70 f305 b19 b116; omega
      have f310 : (x (-6) 4 && x (-6) 6).toNat = 0 := by clear * - c76 f306 b45 b142; omega
      have f311 : (x (-6) 1 && x (-6) 6).toNat = 0 := by clear * - c137 f306 b43 b142; omega
      have f312 : (x (-7) 2 && x (-7) 7).toNat = 1 := by clear * - c133 f52 f311 b35 b43 b51; omega
      have f313 : (x 0 6).toNat = 1 := by clear * - c172 f304 b172 b82; omega
      have f314 : (x 5 1).toNat = 0 := by clear * - c7 f37 f295 f313 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f315 : (x 4 2).toNat = 0 := by clear * - c7 f37 f295 f313 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f316 : (x 3 3).toNat = 0 := by clear * - c7 f37 f295 f313 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f317 : (x 2 4).toNat = 0 := by clear * - c7 f37 f295 f313 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f318 : (e 6).toNat = 0 := by clear * - c7 f37 f295 f313 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f319 : (x 5 0 && x 5 1).toNat = 0 := by clear * - c40 f314 b71 b204; omega
      have f320 : (x 4 1 && x 4 2).toNat = 0 := by clear * - c42 f315 b70 b199; omega
      have f321 : (x 3 2 && x 3 3).toNat = 0 := by clear * - c44 f316 b69 b193; omega
      have f322 : (x 2 3 && x 2 4).toNat = 1 := by clear * - c38 f319 f320 f321 f299 f300 f276 b71 b70 b69 b67 b65 b61 b7; omega
      have f323 : (x 2 3).toNat = 1 := by clear * - c45 f322 b67 b185; omega
      clear * - c46 f322 f317 b67 b186; omega
  · have f324 : (x (-6) 1).toNat = 0 := by clear * - c171 f53 b135 b138; omega
    have f325 : (x (-6) 1 && x (-6) 6).toNat = 0 := by clear * - c136 f324 b43 b138; omega
    have f326 : (x (-7) 2 && x (-7) 7).toNat = 1 := by clear * - c133 f52 f325 b35 b43 b51; omega
    have f327 : (x (-7) 2).toNat = 1 := by clear * - c138 f326 b51 b146; omega
    have f328 : (x (-7) 6).toNat = 1 := by clear * - c198 f327 b146 b149; omega
    have f329 : (x (-6) 5).toNat = 0 := by clear * - c203 f324 b141 b138; omega
    have f330 : (x (-6) 5 && x (-6) 7).toNat = 0 := by clear * - c64 f329 b47 b141; omega
    have f331 : (x (-6) 0 && x (-6) 5).toNat = 0 := by clear * - c142 f329 b41 b141; omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b126 with f332 | f332
    · have f333 : (x (-4) 3 && x (-4) 5).toNat = 0 := by clear * - c61 f332 b31 b126; omega
      have f334 : (x (-4) 2 && x (-4) 5).toNat = 0 := by clear * - c85 f332 b29 b126; omega
      have f335 : (x (-4) 0 && x (-4) 5).toNat = 0 := by clear * - c128 f332 b27 b126; omega
      have f336 : (x (-5) 1 && x (-5) 6).toNat = 1 := by clear * - c126 f335 f51 b27 b36 b44; omega
      have f337 : (x (-5) 1).toNat = 1 := by clear * - c129 f336 b36 b130; omega
      have f338 : (x (-4) 6).toNat = 0 := by clear * - c170 f337 b127 b130; omega
      have f339 : (x (-4) 2).toNat = 0 := by clear * - c210 f338 b123 b127; omega
      have f340 : (x (-4) 2 && x (-4) 7).toNat = 0 := by clear * - c124 f339 b30 b123; omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b86 with f341 | f341
      · have f342 : (x (-1) 6 && x (-1) 7).toNat = 0 := by clear * - c51 f341 b7 b86; omega
        have f343 : (x (-1) 1 && x (-1) 6).toNat = 0 := by clear * - c151 f341 b4 b86; omega
        have f344 : (x (-2) 1).toNat = 1 := by clear * - c168 f341 b86 b107; omega
        have f345 : (x (-3) 2).toNat = 0 := by clear * - c0 f23 f344 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
        have f346 : (x (-4) 3).toNat = 0 := by clear * - c0 f23 f344 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
        have f347 : (x (-5) 4).toNat = 0 := by clear * - c0 f23 f344 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
        have f348 : (e (-1)).toNat = 0 := by clear * - c0 f23 f344 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
        have f349 : (x (-3) 2 && x (-3) 4).toNat = 0 := by clear * - c58 f345 b22 b115; omega
        have f350 : (x (-5) 4 && x (-5) 6).toNat = 0 := by clear * - c62 f347 b39 b133; omega
        have f351 : (x (-3) 2 && x (-3) 7).toNat = 0 := by clear * - c117 f345 b23 b115; omega
        have f352 : (x (-1) 2).toNat = 0 := by clear * - c222 f341 b83 b86; omega
        have f353 : (x (-1) 1 && x (-1) 2).toNat = 0 := by clear * - c27 f352 b2 b83; omega
        have f354 : (x (-1) 0 && x (-1) 2).toNat = 0 := by clear * - c55 f352 b0 b83; omega
        have f355 : (x (-2) 1 && x (-2) 3).toNat = 1 := by clear * - c53 f354 f349 f333 f350 f330 b0 b13 b22 b31 b39 b47; omega
        have f356 : (x (-2) 3).toNat = 1 := by clear * - c57 f355 b13 b109; omega
        have f357 : (x 0 1).toNat = 0 := by clear * - c4 f27 f352 f356 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
        have f358 : (x (-3) 4).toNat = 0 := by clear * - c4 f27 f352 f356 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
        have f359 : (e 1).toNat = 0 := by clear * - c4 f27 f352 f356 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
        have f360 : (x 0 0 && x 0 1).toNat = 0 := by clear * - c25 f357 b56 b167; omega
        have f361 : (x (-3) 3 && x (-3) 4).toNat = 0 := by clear * - c31 f358 b24 b117; omega
        have f362 : (x (-3) 1 && x (-3) 4).toNat = 0 := by clear * - c83 f358 b20 b117; omega
        have f363 : (x 0 1 && x 0 4).toNat = 0 := by clear * - c104 f357 b59 b167; omega
        have f364 : (x (-1) 2 && x (-1) 5).toNat = 0 := by clear * - c106 f352 b5 b83; omega
        have f365 : (x (-3) 4 && x (-3) 7).toNat = 0 := by clear * - c110 f358 b26 b117; omega
        have f366 : (x 0 1 && x 0 6).toNat = 0 := by clear * - c157 f357 b60 b167; omega
        have f367 : (x (-1) 2 && x (-1) 7).toNat = 0 := by clear * - c159 f352 b6 b83; omega
        have f368 : (x 1 0 && x 1 5).toNat = 1 := by clear * - c154 f366 f367 b63 b60 b6; omega
        have f369 : (x 1 5).toNat = 1 := by clear * - c156 f368 b63 b179; omega
        have f370 : (x 1 4).toNat = 0 := by clear * - c175 f352 f356 b178 b171 b83 b109 b79; omega
        have f371 : (x 0 5).toNat = 0 := by clear * - c175 f352 f356 b178 b171 b83 b109 b79; omega
        have f372 : (e 5).toNat = 0 := by clear * - c175 f352 f356 b178 b171 b83 b109 b79; omega
        have f373 : (x 1 4 && x 1 5).toNat = 0 := by clear * - c47 f370 b65 b178; omega
        have f374 : (x 0 5 && x 0 6).toNat = 0 := by clear * - c49 f371 b61 b171; omega
        have f375 : (x 0 0 && x 0 5).toNat = 0 := by clear * - c149 f371 b58 b171; omega
        have f376 : (x (-2) 2 && x (-2) 7).toNat = 1 := by clear * - c147 f375 f343 b58 b4 b17; omega
        have f377 : (x (-2) 2).toNat = 1 := by clear * - c152 f376 b17 b108; omega
        have f378 : (x (-1) 1).toNat = 0 := by clear * - c3 f25 f377 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
        have f379 : (x (-3) 3).toNat = 0 := by clear * - c3 f25 f377 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
        have f380 : (x (-6) 6).toNat = 0 := by clear * - c3 f25 f377 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
        have f381 : (x (-6) 6 && x (-6) 7).toNat = 0 := by clear * - c36 f380 b48 b142; omega
        have f382 : (x (-2) 2 && x (-2) 3).toNat = 1 := by clear * - c23 f360 f353 f361 f46 f47 f381 b56 b2 b15 b24 b32 b40 b48; omega
        have f383 : (x (-3) 1 && x (-3) 3).toNat = 0 := by clear * - c70 f379 b19 b116; omega
        have f384 : (x (-6) 4 && x (-6) 6).toNat = 0 := by clear * - c76 f380 b45 b142; omega
        have f385 : (x (-1) 1 && x (-1) 4).toNat = 0 := by clear * - c93 f378 b3 b82; omega
        have f386 : (x (-3) 3 && x (-3) 6).toNat = 0 := by clear * - c97 f379 b25 b116; omega
        have f387 : (x 0 6).toNat = 1 := by clear * - c172 f378 b172 b82; omega
        have f388 : (x 5 1).toNat = 0 := by clear * - c7 f37 f369 f387 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
        have f389 : (x 4 2).toNat = 0 := by clear * - c7 f37 f369 f387 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
        have f390 : (x 3 3).toNat = 0 := by clear * - c7 f37 f369 f387 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
        have f391 : (x 2 4).toNat = 0 := by clear * - c7 f37 f369 f387 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
        have f392 : (e 6).toNat = 0 := by clear * - c7 f37 f369 f387 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
        have f393 : (x 5 0 && x 5 1).toNat = 0 := by clear * - c40 f388 b71 b204; omega
        have f394 : (x 4 1 && x 4 2).toNat = 0 := by clear * - c42 f389 b70 b199; omega
        have f395 : (x 3 2 && x 3 3).toNat = 0 := by clear * - c44 f390 b69 b193; omega
        have f396 : (x 2 3 && x 2 4).toNat = 1 := by clear * - c38 f393 f394 f395 f373 f374 f342 b71 b70 b69 b67 b65 b61 b7; omega
        have f397 : (x 2 3).toNat = 1 := by clear * - c45 f396 b67 b185; omega
        clear * - c46 f396 f391 b67 b186; omega
      · have f398 : (x (-2) 1).toNat = 0 := by clear * - c168 f341 b86 b107; omega
        have f399 : (x (-2) 1 && x (-2) 3).toNat = 0 := by clear * - c56 f398 b13 b107; omega
        have f400 : (x (-2) 1 && x (-2) 6).toNat = 0 := by clear * - c115 f398 b14 b107; omega
        have f401 : (x (-2) 5).toNat = 0 := by clear * - c219 f398 b110 b107; omega
        have f402 : (x (-2) 2 && x (-2) 5).toNat = 0 := by clear * - c96 f401 b16 b110; omega
        have f403 : (x (-2) 0 && x (-2) 5).toNat = 0 := by clear * - c121 f401 b12 b110; omega
        have f404 : (x (-3) 1 && x (-3) 6).toNat = 1 := by clear * - c119 f403 f340 b12 b21 b30; omega
        have f405 : (x (-3) 1).toNat = 1 := by clear * - c122 f404 b21 b114; omega
        have f406 : (x (-3) 6).toNat = 1 := by clear * - c123 f404 b21 b119; omega
        have f407 : (x (-4) 1).toNat = 0 := by clear * - c169 f406 b119 b122; omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b82 with f408 | f408
        · have f409 : (x (-1) 1 && x (-1) 2).toNat = 0 := by clear * - c26 f408 b2 b82; omega
          have f410 : (x (-1) 1 && x (-1) 4).toNat = 0 := by clear * - c93 f408 b3 b82; omega
          have f411 : (x (-1) 1 && x (-1) 6).toNat = 0 := by clear * - c150 f408 b4 b82; omega
          have f412 : (x 0 6).toNat = 1 := by clear * - c172 f408 b172 b82; omega
          have f413 : (x (-1) 5).toNat = 0 := by clear * - c223 f408 b85 b82; omega
          have f414 : (x (-1) 2 && x (-1) 5).toNat = 0 := by clear * - c107 f413 b5 b85; omega
          have f415 : (x (-1) 0 && x (-1) 5).toNat = 0 := by clear * - c114 f413 b1 b85; omega
          have f416 : (x (-3) 2 && x (-3) 7).toNat = 1 := by clear * - c112 f415 f400 b1 b14 b23; omega
          have f417 : (x (-3) 2).toNat = 1 := by clear * - c117 f416 b23 b115; omega
          have f418 : (x (-4) 3).toNat = 0 := by clear * - c0 f23 f398 f417 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f419 : (x (-5) 4).toNat = 0 := by clear * - c0 f23 f398 f417 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f420 : (e (-1)).toNat = 0 := by clear * - c0 f23 f398 f417 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
          have f421 : (x (-5) 4 && x (-5) 6).toNat = 0 := by clear * - c62 f419 b39 b133; omega
          have f422 : (x (-1) 4).toNat = 0 := by clear * - c173 f401 f417 f418 b84 b110 b115 b124 b77; omega
          have f423 : (e 3).toNat = 0 := by clear * - c173 f401 f417 f418 b84 b110 b115 b124 b77; omega
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b83 with f424 | f424
          · have f425 : (x (-1) 0 && x (-1) 2).toNat = 0 := by clear * - c55 f424 b0 b83; omega
            have f426 : (x (-3) 2 && x (-3) 4).toNat = 1 := by clear * - c53 f425 f399 f333 f421 f330 b0 b13 b22 b31 b39 b47; omega
            have f427 : (x (-3) 4).toNat = 1 := by clear * - c59 f426 b22 b117; omega
            have f428 : (x 0 1).toNat = 0 := by clear * - c4 f27 f424 f427 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f429 : (x (-2) 3).toNat = 0 := by clear * - c4 f27 f424 f427 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f430 : (e 1).toNat = 0 := by clear * - c4 f27 f424 f427 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f431 : (x 0 0 && x 0 1).toNat = 0 := by clear * - c25 f428 b56 b167; omega
            have f432 : (x (-2) 2 && x (-2) 3).toNat = 0 := by clear * - c29 f429 b15 b109; omega
            have f433 : (x (-2) 0 && x (-2) 3).toNat = 0 := by clear * - c81 f429 b11 b109; omega
            have f434 : (x 0 1 && x 0 4).toNat = 0 := by clear * - c104 f428 b59 b167; omega
            have f435 : (x (-2) 3 && x (-2) 6).toNat = 0 := by clear * - c108 f429 b18 b109; omega
            have f436 : (x 0 1 && x 0 6).toNat = 0 := by clear * - c157 f428 b60 b167; omega
            have f437 : (x (-1) 2 && x (-1) 7).toNat = 0 := by clear * - c159 f424 b6 b83; omega
            have f438 : (x 1 0 && x 1 5).toNat = 1 := by clear * - c154 f436 f437 b63 b60 b6; omega
            have f439 : (x 1 5).toNat = 1 := by clear * - c156 f438 b63 b179; omega
            have f440 : (x 5 1).toNat = 0 := by clear * - c7 f37 f439 f412 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
            have f441 : (x 4 2).toNat = 0 := by clear * - c7 f37 f439 f412 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
            have f442 : (x 3 3).toNat = 0 := by clear * - c7 f37 f439 f412 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
            have f443 : (x 2 4).toNat = 0 := by clear * - c7 f37 f439 f412 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
            have f444 : (e 6).toNat = 0 := by clear * - c7 f37 f439 f412 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
            have f445 : (x 5 0 && x 5 1).toNat = 0 := by clear * - c40 f440 b71 b204; omega
            have f446 : (x 4 1 && x 4 2).toNat = 0 := by clear * - c42 f441 b70 b199; omega
            have f447 : (x 3 2 && x 3 3).toNat = 0 := by clear * - c44 f442 b69 b193; omega
            have f448 : (x 2 3 && x 2 4).toNat = 0 := by clear * - c46 f443 b67 b186; omega
            have f449 : (x 0 5).toNat = 0 := by clear * - c227 f428 b171 b167; omega
            have f450 : (x 0 5 && x 0 6).toNat = 0 := by clear * - c49 f449 b61 b171; omega
            have f451 : (x 0 0 && x 0 5).toNat = 0 := by clear * - c149 f449 b58 b171; omega
            have f452 : (x (-2) 2 && x (-2) 7).toNat = 1 := by clear * - c147 f451 f411 b58 b4 b17; omega
            have f453 : (x (-2) 2).toNat = 1 := by clear * - c152 f452 b17 b108; omega
            have f454 : (x (-3) 3).toNat = 0 := by clear * - c3 f25 f408 f453 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
            have f455 : (x (-6) 6).toNat = 0 := by clear * - c3 f25 f408 f453 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
            have f456 : (x (-3) 3 && x (-3) 4).toNat = 0 := by clear * - c30 f454 b24 b116; omega
            have f457 : (x (-6) 6 && x (-6) 7).toNat = 1 := by clear * - c23 f431 f409 f432 f456 f46 f47 b56 b2 b15 b24 b32 b40 b48; omega
            clear * - c36 f457 f455 b48 b142; omega
          · have f458 : (x 0 1).toNat = 0 := by clear * - c4 f27 f424 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f459 : (x (-2) 3).toNat = 0 := by clear * - c4 f27 f424 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f460 : (x (-3) 4).toNat = 0 := by clear * - c4 f27 f424 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f461 : (e 1).toNat = 0 := by clear * - c4 f27 f424 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f462 : (x 0 0 && x 0 1).toNat = 0 := by clear * - c25 f458 b56 b167; omega
            have f463 : (x (-2) 2 && x (-2) 3).toNat = 0 := by clear * - c29 f459 b15 b109; omega
            have f464 : (x (-3) 3 && x (-3) 4).toNat = 0 := by clear * - c31 f460 b24 b117; omega
            have f465 : (x (-6) 6 && x (-6) 7).toNat = 1 := by clear * - c23 f462 f409 f463 f464 f46 f47 b56 b2 b15 b24 b32 b40 b48; omega
            have f466 : (x (-6) 6).toNat = 1 := by clear * - c36 f465 b48 b142; omega
            have f467 : (x (-2) 2).toNat = 0 := by clear * - c3 f25 f408 f40 f41 f466 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
            have f468 : (x (-3) 3).toNat = 0 := by clear * - c3 f25 f408 f40 f41 f466 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
            have f469 : (x (-3) 2 && x (-3) 4).toNat = 0 := by clear * - c59 f460 b22 b117; omega
            have f470 : (x (-1) 0 && x (-1) 2).toNat = 1 := by clear * - c53 f399 f469 f333 f421 f330 b0 b13 b22 b31 b39 b47; omega
            have f471 : (x (-2) 0 && x (-2) 2).toNat = 0 := by clear * - c68 f467 b10 b108; omega
            have f472 : (x (-3) 1 && x (-3) 3).toNat = 0 := by clear * - c70 f468 b19 b116; omega
            have f473 : (x (-2) 0 && x (-2) 3).toNat = 0 := by clear * - c81 f459 b11 b109; omega
            have f474 : (x (-3) 1 && x (-3) 4).toNat = 0 := by clear * - c83 f460 b20 b117; omega
            have f475 : (x (-3) 3 && x (-3) 6).toNat = 0 := by clear * - c97 f468 b25 b116; omega
            have f476 : (x 0 0 && x 0 3).toNat = 1 := by clear * - c90 f410 f402 f475 f50 b57 b3 b16 b25 b33; omega
            have f477 : (x 0 3).toNat = 1 := by clear * - c92 f476 b57 b169; omega
            have f478 : (x 2 1).toNat = 0 := by clear * - c5 f31 f477 f422 f401 f406 f18 f423 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
            have f479 : (x 1 2).toNat = 0 := by clear * - c5 f31 f477 f422 f401 f406 f18 f423 b190 b183 b176 b169 b84 b110 b119 b128 b77; omega
            have f480 : (x 0 1 && x 0 4).toNat = 0 := by clear * - c104 f458 b59 b167; omega
            have f481 : (x (-2) 3 && x (-2) 6).toNat = 0 := by clear * - c108 f459 b18 b109; omega
            have f482 : (x (-3) 4 && x (-3) 7).toNat = 0 := by clear * - c110 f460 b26 b117; omega
            have f483 : (x 1 0 && x 1 3).toNat = 1 := by clear * - c101 f480 f414 f481 f482 b62 b59 b5 b18 b26; omega
            have f484 : (x 1 3).toNat = 1 := by clear * - c103 f483 b62 b177; omega
            have f485 : (x (-2) 2 && x (-2) 7).toNat = 0 := by clear * - c152 f467 b17 b108; omega
            have f486 : (x 0 0 && x 0 5).toNat = 1 := by clear * - c147 f411 f485 b58 b4 b17; omega
            have f487 : (x 0 5).toNat = 1 := by clear * - c149 f486 b58 b171; omega
            have f488 : (x 0 1 && x 0 6).toNat = 0 := by clear * - c157 f458 b60 b167; omega
            have f489 : (x 2 1 && x 2 6).toNat = 0 := by clear * - c164 f478 b66 b183; omega
            have f490 : (x 1 2 && x 1 7).toNat = 0 := by clear * - c166 f479 b64 b176; omega
            have f491 : (x 3 0 && x 3 5).toNat = 1 := by clear * - c161 f489 f490 b68 b66 b64; omega
            have f492 : (x 3 5).toNat = 1 := by clear * - c163 f491 b68 b194; omega
            clear * - c175 f487 f424 f459 b178 b171 b83 b109 b79; omega
        · have f493 : (x (-2) 2).toNat = 0 := by clear * - c3 f25 f408 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
          have f494 : (x (-3) 3).toNat = 0 := by clear * - c3 f25 f408 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
          have f495 : (x (-6) 6).toNat = 0 := by clear * - c3 f25 f408 f40 f41 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
          have f496 : (x (-2) 2 && x (-2) 3).toNat = 0 := by clear * - c28 f493 b15 b108; omega
          have f497 : (x (-3) 3 && x (-3) 4).toNat = 0 := by clear * - c30 f494 b24 b116; omega
          have f498 : (x (-6) 6 && x (-6) 7).toNat = 0 := by clear * - c36 f495 b48 b142; omega
          have f499 : (x (-2) 0 && x (-2) 2).toNat = 0 := by clear * - c68 f493 b10 b108; omega
          have f500 : (x (-3) 1 && x (-3) 3).toNat = 0 := by clear * - c70 f494 b19 b116; omega
          have f501 : (x (-6) 4 && x (-6) 6).toNat = 0 := by clear * - c76 f495 b45 b142; omega
          have f502 : (x (-7) 5 && x (-7) 7).toNat = 1 := by clear * - c66 f499 f500 f48 f49 f501 b10 b19 b28 b37 b45 b52; omega
          have f503 : (x (-7) 5).toNat = 1 := by clear * - c77 f502 b52 b148; omega
          have f504 : (x (-5) 3).toNat = 0 := by clear * - c1 f21 f405 f339 f503 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f505 : (x (-6) 4).toNat = 0 := by clear * - c1 f21 f405 f339 f503 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f506 : (x (-8) 6).toNat = 0 := by clear * - c1 f21 f405 f339 f503 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f507 : (e (-2)).toNat = 0 := by clear * - c1 f21 f405 f339 f503 f8 b106 b114 b123 b132 b140 b148 b157 b165 b73; omega
          have f508 : (x (-5) 3 && x (-5) 6).toNat = 0 := by clear * - c86 f504 b38 b132; omega
          have f509 : (x (-6) 4 && x (-6) 7).toNat = 0 := by clear * - c88 f505 b46 b140; omega
          have f510 : (x (-3) 3 && x (-3) 6).toNat = 0 := by clear * - c97 f494 b25 b116; omega
          have f511 : (x (-2) 2 && x (-2) 7).toNat = 0 := by clear * - c152 f493 b17 b108; omega
          have f512 : (x 0 6).toNat = 0 := by clear * - c172 f408 b172 b82; omega
          have f513 : (x 0 5 && x 0 6).toNat = 0 := by clear * - c50 f512 b61 b172; omega
          have f514 : (x 0 1 && x 0 6).toNat = 0 := by clear * - c158 f512 b60 b172; omega
          have f515 : (x (-8) 2).toNat = 0 := by clear * - c194 f506 b153 b157; omega
          have f516 : (x (-8) 2 && x (-8) 7).toNat = 0 := by clear * - c145 f515 b53 b153; omega
          have f517 : (x (-7) 1 && x (-7) 6).toNat = 1 := by clear * - c140 f331 f516 b41 b49 b53; omega
          have f518 : (x (-7) 1).toNat = 1 := by clear * - c143 f517 b49 b145; omega
          have f519 : (x 0 2).toNat = 0 := by clear * - c226 f512 b168 b172; omega
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b83 with f520 | f520
          · have f521 : (x (-1) 1 && x (-1) 2).toNat = 0 := by clear * - c27 f520 b2 b83; omega
            have f522 : (x 0 0 && x 0 1).toNat = 1 := by clear * - c23 f521 f496 f497 f46 f47 f498 b56 b2 b15 b24 b32 b40 b48; omega
            have f523 : (x 0 1).toNat = 1 := by clear * - c25 f522 b56 b167; omega
            have f524 : (x (-2) 3).toNat = 0 := by clear * - c4 f27 f523 f520 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f525 : (x (-3) 4).toNat = 0 := by clear * - c4 f27 f523 f520 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f526 : (e 1).toNat = 0 := by clear * - c4 f27 f523 f520 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f527 : (x (-1) 0 && x (-1) 2).toNat = 0 := by clear * - c55 f520 b0 b83; omega
            have f528 : (x (-3) 2 && x (-3) 4).toNat = 0 := by clear * - c59 f525 b22 b117; omega
            have f529 : (x (-5) 4 && x (-5) 6).toNat = 1 := by clear * - c53 f527 f399 f528 f333 f330 b0 b13 b22 b31 b39 b47; omega
            have f530 : (x (-5) 4).toNat = 1 := by clear * - c62 f529 b39 b133; omega
            have f531 : (x (-3) 2).toNat = 0 := by clear * - c0 f23 f398 f530 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
            have f532 : (x (-4) 3).toNat = 0 := by clear * - c0 f23 f398 f530 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
            have f533 : (e (-1)).toNat = 0 := by clear * - c0 f23 f398 f530 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
            have f534 : (x (-2) 0 && x (-2) 3).toNat = 0 := by clear * - c81 f524 b11 b109; omega
            have f535 : (x (-3) 1 && x (-3) 4).toNat = 1 := by clear * - c79 f534 f334 f508 f509 b11 b20 b29 b38 b46; omega
            clear * - c83 f535 f525 b20 b117; omega
          · have f536 : (x 0 1).toNat = 0 := by clear * - c4 f27 f520 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f537 : (x (-2) 3).toNat = 0 := by clear * - c4 f27 f520 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f538 : (x (-3) 4).toNat = 0 := by clear * - c4 f27 f520 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f539 : (e 1).toNat = 0 := by clear * - c4 f27 f520 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
            have f540 : (x 0 0 && x 0 1).toNat = 0 := by clear * - c25 f536 b56 b167; omega
            have f541 : (x (-1) 1 && x (-1) 2).toNat = 1 := by clear * - c23 f540 f496 f497 f46 f47 f498 b56 b2 b15 b24 b32 b40 b48; omega
            have f542 : (x (-3) 2 && x (-3) 4).toNat = 0 := by clear * - c59 f538 b22 b117; omega
            have f543 : (x (-2) 0 && x (-2) 3).toNat = 0 := by clear * - c81 f537 b11 b109; omega
            have f544 : (x (-3) 1 && x (-3) 4).toNat = 1 := by clear * - c79 f543 f334 f508 f509 b11 b20 b29 b38 b46; omega
            clear * - c83 f544 f538 b20 b117; omega
    · have f545 : (x 0 1).toNat = 0 := by clear * - c4 f27 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f546 : (x (-1) 2).toNat = 0 := by clear * - c4 f27 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f547 : (x (-2) 3).toNat = 0 := by clear * - c4 f27 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f548 : (x (-3) 4).toNat = 0 := by clear * - c4 f27 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f549 : (e 1).toNat = 0 := by clear * - c4 f27 f332 f53 f14 b174 b167 b83 b109 b117 b126 b135 b143 b76; omega
      have f550 : (x 0 0 && x 0 1).toNat = 0 := by clear * - c25 f545 b56 b167; omega
      have f551 : (x (-1) 1 && x (-1) 2).toNat = 0 := by clear * - c27 f546 b2 b83; omega
      have f552 : (x (-2) 2 && x (-2) 3).toNat = 0 := by clear * - c29 f547 b15 b109; omega
      have f553 : (x (-3) 3 && x (-3) 4).toNat = 0 := by clear * - c31 f548 b24 b117; omega
      have f554 : (x (-6) 6 && x (-6) 7).toNat = 1 := by clear * - c23 f550 f551 f552 f553 f46 f47 b56 b2 b15 b24 b32 b40 b48; omega
      have f555 : (x (-6) 6).toNat = 1 := by clear * - c36 f554 b48 b142; omega
      have f556 : (x (-1) 1).toNat = 0 := by clear * - c3 f25 f40 f41 f555 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f557 : (x (-2) 2).toNat = 0 := by clear * - c3 f25 f40 f41 f555 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f558 : (x (-3) 3).toNat = 0 := by clear * - c3 f25 f40 f41 f555 f12 f39 b166 b82 b108 b116 b125 b134 b142 b150 b75; omega
      have f559 : (x (-1) 0 && x (-1) 2).toNat = 0 := by clear * - c55 f546 b0 b83; omega
      have f560 : (x (-2) 1 && x (-2) 3).toNat = 0 := by clear * - c57 f547 b13 b109; omega
      have f561 : (x (-3) 2 && x (-3) 4).toNat = 0 := by clear * - c59 f548 b22 b117; omega
      have f562 : (x (-2) 0 && x (-2) 2).toNat = 0 := by clear * - c68 f557 b10 b108; omega
      have f563 : (x (-3) 1 && x (-3) 3).toNat = 0 := by clear * - c70 f558 b19 b116; omega
      have f564 : (x (-2) 0 && x (-2) 3).toNat = 0 := by clear * - c81 f547 b11 b109; omega
      have f565 : (x (-3) 1 && x (-3) 4).toNat = 0 := by clear * - c83 f548 b20 b117; omega
      have f566 : (x (-1) 1 && x (-1) 4).toNat = 0 := by clear * - c93 f556 b3 b82; omega
      have f567 : (x (-2) 2 && x (-2) 5).toNat = 0 := by clear * - c95 f557 b16 b108; omega
      have f568 : (x (-3) 3 && x (-3) 6).toNat = 0 := by clear * - c97 f558 b25 b116; omega
      have f569 : (x 0 0 && x 0 3).toNat = 1 := by clear * - c90 f566 f567 f568 f50 b57 b3 b16 b25 b33; omega
      have f570 : (x 0 3).toNat = 1 := by clear * - c92 f569 b57 b169; omega
      have f571 : (x 0 1 && x 0 4).toNat = 0 := by clear * - c104 f545 b59 b167; omega
      have f572 : (x (-1) 2 && x (-1) 5).toNat = 0 := by clear * - c106 f546 b5 b83; omega
      have f573 : (x (-2) 3 && x (-2) 6).toNat = 0 := by clear * - c108 f547 b18 b109; omega
      have f574 : (x (-3) 4 && x (-3) 7).toNat = 0 := by clear * - c110 f548 b26 b117; omega
      have f575 : (x 1 0 && x 1 3).toNat = 1 := by clear * - c101 f571 f572 f573 f574 b62 b59 b5 b18 b26; omega
      have f576 : (x 1 3).toNat = 1 := by clear * - c103 f575 b62 b177; omega
      have f577 : (x (-1) 1 && x (-1) 6).toNat = 0 := by clear * - c150 f556 b4 b82; omega
      have f578 : (x (-2) 2 && x (-2) 7).toNat = 0 := by clear * - c152 f557 b17 b108; omega
      have f579 : (x 0 0 && x 0 5).toNat = 1 := by clear * - c147 f577 f578 b58 b4 b17; omega
      have f580 : (x 0 5).toNat = 1 := by clear * - c149 f579 b58 b171; omega
      have f581 : (x 0 1 && x 0 6).toNat = 0 := by clear * - c157 f545 b60 b167; omega
      have f582 : (x (-1) 2 && x (-1) 7).toNat = 0 := by clear * - c159 f546 b6 b83; omega
      have f583 : (x 1 0 && x 1 5).toNat = 1 := by clear * - c154 f581 f582 b63 b60 b6; omega
      have f584 : (x 1 5).toNat = 1 := by clear * - c156 f583 b63 b179; omega
      have f585 : (x 0 6).toNat = 1 := by clear * - c172 f556 b172 b82; omega
      have f586 : (x 5 1).toNat = 0 := by clear * - c7 f37 f584 f585 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f587 : (x 4 2).toNat = 0 := by clear * - c7 f37 f584 f585 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f588 : (x 3 3).toNat = 0 := by clear * - c7 f37 f584 f585 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f589 : (x 2 4).toNat = 0 := by clear * - c7 f37 f584 f585 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f590 : (e 6).toNat = 0 := by clear * - c7 f37 f584 f585 f24 b209 b204 b199 b193 b186 b179 b172 b87 b80; omega
      have f591 : (x 5 0 && x 5 1).toNat = 0 := by clear * - c40 f586 b71 b204; omega
      have f592 : (x 4 1 && x 4 2).toNat = 0 := by clear * - c42 f587 b70 b199; omega
      have f593 : (x 3 2 && x 3 3).toNat = 0 := by clear * - c44 f588 b69 b193; omega
      have f594 : (x 2 3 && x 2 4).toNat = 0 := by clear * - c46 f589 b67 b186; omega
      have f595 : (x 1 4).toNat = 0 := by clear * - c175 f580 f546 f547 b178 b171 b83 b109 b79; omega
      have f596 : (e 5).toNat = 0 := by clear * - c175 f580 f546 f547 b178 b171 b83 b109 b79; omega
      have f597 : (x 1 4 && x 1 5).toNat = 0 := by clear * - c47 f595 b65 b178; omega
      have f598 : (x (-4) 1).toNat = 1 := by clear * - c211 f332 b126 b122; omega
      have f599 : (x (-3) 6).toNat = 0 := by clear * - c169 f598 b119 b122; omega
      have f600 : (x (-3) 1 && x (-3) 6).toNat = 0 := by clear * - c123 f599 b21 b119; omega
      have f601 : (x (-3) 2).toNat = 0 := by clear * - c214 f599 b115 b119; omega
      have f602 : (x (-3) 2 && x (-3) 7).toNat = 0 := by clear * - c117 f601 b23 b115; omega
      have f603 : (x (-1) 5).toNat = 0 := by clear * - c223 f556 b85 b82; omega
      have f604 : (x (-1) 0 && x (-1) 5).toNat = 0 := by clear * - c114 f603 b1 b85; omega
      have f605 : (x (-2) 1 && x (-2) 6).toNat = 1 := by clear * - c112 f604 f602 b1 b14 b23; omega
      have f606 : (x (-2) 1).toNat = 1 := by clear * - c115 f605 b14 b107; omega
      have f607 : (x (-4) 3).toNat = 0 := by clear * - c0 f23 f606 f601 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
      have f608 : (x (-5) 4).toNat = 0 := by clear * - c0 f23 f606 f601 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
      have f609 : (e (-1)).toNat = 0 := by clear * - c0 f23 f606 f601 f329 f328 f10 b81 b107 b115 b124 b133 b141 b149 b158 b72; omega
      have f610 : (x (-4) 3 && x (-4) 5).toNat = 0 := by clear * - c60 f607 b31 b124; omega
      have f611 : (x (-5) 4 && x (-5) 6).toNat = 1 := by clear * - c53 f559 f560 f561 f610 f330 b0 b13 b22 b31 b39 b47; omega
      clear * - c62 f611 f608 b39 b133; omega

theorem half1119h (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 4) : ∀ p : ℤ, e p = false := by
  intro p
  cases he : e p with
  | false => rfl
  | true =>
    exact False.elim (origin1119h _ _ (shift1119h x e 4 hm p) (by simpa using he))

end RT1Half1119

theorem cycle_power_eight_half_phase_half_no_defects (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 4) : ∀ p : ℤ, e p = false := by
  exact RT1Half1119.half1119h x e hm
