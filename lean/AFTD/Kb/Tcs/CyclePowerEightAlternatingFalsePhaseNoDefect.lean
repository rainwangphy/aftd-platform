import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.G

/-!
# cycle_power_eight_alternating_false_phase_no_defect

Topic: combinatorics   Node: 96cc3622724f

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635; finite computations 29006, 29007 and 29023.

If the first inner bit alternates in a zero-phase defective exponent-three model, no defect can occur at a root where that bit is false.
-/

namespace RT1False942
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
theorem rt1_bridge_base895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0) :
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

private theorem bool_parent_and (a b : Bool) (h : a = true → b = true) : (a && b) = a := by
  cases a <;> cases b <;> simp_all

theorem rt1_false_semantics939 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) :
    (∀ v : ℤ, (x v 6).toNat + (x (v-1) 1).toNat = 1) ∧
    (∀ v : ℤ, (x v 4).toNat + (x (v-1) 5).toNat + (x (v-2) 2).toNat +
       (x (v-3) 3).toNat + (e v).toNat = 1) ∧
    (∀ v : ℤ, (x v 0).toNat + (x (v-1) 1).toNat + (x (v-2) 2).toNat +
       (x (v-3) 3).toNat + (x (v-4) 4).toNat + (x (v-5) 5).toNat +
       (x (v-6) 6).toNat + (x (v-7) 7).toNat + (e v).toNat = 4) := by
  obtain ⟨hend, hp⟩ := rt1_bridge_base895 x e h
  have hpa (p : ℤ) : (x p 1 && x p 5) = x p 5 := by
    rw [Bool.and_comm]; exact bool_parent_and _ _ (hp p).2.2.2.2.1
  have hpb (p : ℤ) : (x p 2 && x p 6) = x p 2 :=
    bool_parent_and _ _ (hp p).2.1
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

theorem rt1_false_arithmetic942
    (bm2 cm3 dm4 hm5 fm6 d0 hm1 fm2 bm3 fm3 : ℕ)
    (c0 dm1 a2 b1 hm2 e3 h3 a3 b2 c1 d4 e4 : ℕ)
    (htop0 : d0 + hm1 + bm2 + cm3 + 1 = 1)
    (hcount0 : bm2 + cm3 + dm4 + hm5 + fm6 + 4 = 4)
    (hrank : fm2 + 1 = 1)
    (hcov5m1 : 1 ≤ hm1 + fm2 + bm3)
    (hparentb : bm3 ≤ fm3) (hbm : bm3 ≤ 1) (hfm : fm3 ≤ 1)
    (hcov30 : 1 ≤ c0 + dm1 + bm2 + cm3 + dm4)
    (hcount3 : a2 + b1 + c0 + dm1 + hm2 + e3 + fm3 + 2 = 4)
    (hcov53 : 1 ≤ h3 + a2 + b1)
    (hparenth : h3 ≤ a3) (ha3 : a3 ≤ 1) (hh3 : h3 ≤ 1)
    (htop4 : d4 + h3 + b2 + c1 + e4 = 1)
    (hcount4 : a3 + b2 + c1 + d0 + hm1 + fm2 + e4 + 2 = 4) : False := by
  omega

theorem rt1_cover_five_upper942 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v : ℤ) :
    1 ≤ (x v 5).toNat + (x (v-1) 6).toNat + (x (v-2) 2).toNat := by
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 5 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2
  all_goals simp_all <;> omega

theorem rt1_cover_five_first_upper942 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) (v : ℤ) :
    1 ≤ (x v 5).toNat + (x (v-1) 1).toNat + (x (v-2) 2).toNat := by
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 5 (by decide) (by decide) (by decide) v
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2
  all_goals simp_all <;> omega

theorem rt1_cover_three_upper942 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0) :
    1 ≤ (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 2).toNat +
      (x (-3) 3).toNat + (x (-4) 4).toNat := by
  obtain ⟨a, ha, h1, h2⟩ := h.2.2.2.1 3 (by decide) (by decide) (by decide) 0
  norm_num at ha
  interval_cases a <;> norm_num at h1 h2
  all_goals simp_all <;> omega

private theorem rt1_bool_toNat_le942 (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
private theorem rt1_bool_imp_toNat942 (a b : Bool) (h : a = true → b = true) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all

theorem rt1_false_origin_short942 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 x e 0)
    (ha1 : x (-1) 1 = true) (ha3 : x (-3) 1 = true) (he0 : e 0 = true) : False := by
  obtain ⟨hend, hp⟩ := rt1_bridge_base895 x e h
  obtain ⟨hrank, htop, hcount⟩ := rt1_false_semantics939 x e h
  have htop0 := htop 0
  have hcount0 := hcount 0
  have hrankm2 := hrank (-2)
  have hcount3 := hcount 3
  have htop4 := htop 4
  have hcount4 := hcount 4
  have hc5m1 := rt1_cover_five_upper942 x e h (-1)
  have hc53 := rt1_cover_five_first_upper942 x e h 3
  have hc30 := rt1_cover_three_upper942 x e h
  have hp_b := rt1_bool_imp_toNat942 _ _ (hp (-3)).2.1
  have hp_h := rt1_bool_imp_toNat942 _ _ (hp 3).2.2.2.2.1
  have hbm := rt1_bool_toNat_le942 (x (-3) 2)
  have hfm := rt1_bool_toNat_le942 (x (-3) 6)
  have ha3b := rt1_bool_toNat_le942 (x 3 1)
  have hh3b := rt1_bool_toNat_le942 (x 3 5)
  have he0n : (e 0).toNat = 1 := by simp [he0]
  have ha1n : (x (-1) 1).toNat = 1 := by simp [ha1]
  have ha3n : (x (-3) 1).toNat = 1 := by simp [ha3]
  have ends0 := hend 0
  have endsm7 := hend (-7)
  have ends3 := hend 3
  have endsm4 := hend (-4)
  have ends4 := hend 4
  have endsm3 := hend (-3)
  norm_num only [Bool.toNat_true, ends0.1, endsm7.2, ends3.1, endsm4.2, ends4.1, endsm3.2,
    he0, ha1, ha3] at htop0 hcount0 hrankm2 hcount3 htop4 hcount4 hc5m1 hc53 hc30
  exact rt1_false_arithmetic942
    (x (-2) 2).toNat (x (-3) 3).toNat (x (-4) 4).toNat (x (-5) 5).toNat
    (x (-6) 6).toNat (x 0 4).toNat (x (-1) 5).toNat (x (-2) 6).toNat
    (x (-3) 2).toNat (x (-3) 6).toNat (x 0 3).toNat (x (-1) 4).toNat
    (x 2 1).toNat (x 1 2).toNat (x (-2) 5).toNat (e 3).toNat
    (x 3 5).toNat (x 3 1).toNat (x 2 2).toNat (x 1 3).toNat
    (x 4 4).toNat (e 4).toNat
    (by omega) (by omega) (by omega) (by omega) hp_b hbm hfm (by omega)
    (by omega) (by omega) hp_h ha3b hh3b (by omega) (by omega)
theorem rt1_model_shift_upper895 (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (h : cycle_power_dyadic_defective_half_model 3 y e 0) (v : ℤ) :
    cycle_power_dyadic_defective_half_model 3 (fun p a => y (v+p) a) (fun p => e (v+p)) 0 := by
  rcases h with ⟨hw, hl, ht, hc, hn⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hw (v+p)
  · intro j hj p
    simpa only [add_sub_assoc] using hl j hj (v+p)
  · intro p
    simpa only [add_sub_assoc, add_zero] using ht (v+p)
  · intro d hd hd8 hd4 p
    obtain ⟨a,ha,ha1,ha2⟩ := hc d hd hd8 hd4 (v+p)
    refine ⟨a, ha, ?_, ?_⟩
    · simpa only [add_sub_assoc] using ha1
    · simpa only [add_sub_assoc] using ha2
  · intro p
    simpa only [add_sub_assoc] using hn (v+p)


theorem rt1_false_phase942 (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0)
    (halt : ∀ p : ℤ, x (p + 1) 1 = !(x p 1)) :
    ∀ p : ℤ, x p 1 = false → e p = false := by
  intro p hp
  have a1 : x (p-1) 1 = true := by
    have hh := halt (p-1)
    have hi : p-1+1 = p := by omega
    rw [hi, hp] at hh
    cases hbit : x (p-1) 1 <;> simp [hbit] at hh ⊢
  have a2 : x (p-2) 1 = false := by
    have hh := halt (p-2)
    have hi : p-2+1 = p-1 := by omega
    rw [hi, a1] at hh
    cases hbit : x (p-2) 1 <;> simp [hbit] at hh ⊢
  have a3 : x (p-3) 1 = true := by
    have hh := halt (p-3)
    have hi : p-3+1 = p-2 := by omega
    rw [hi, a2] at hh
    cases hbit : x (p-3) 1 <;> simp [hbit] at hh ⊢
  cases he : e p with
  | false => rfl
  | true =>
    have hs := rt1_model_shift_upper895 x e hm p
    have he0 : (fun q => e (p+q)) 0 = true := by simpa using he
    have ha1 : (fun q a => x (p+q) a) (-1) 1 = true := by simpa only [sub_eq_add_neg] using a1
    have ha3 : (fun q a => x (p+q) a) (-3) 1 = true := by simpa only [sub_eq_add_neg] using a3
    exact False.elim (rt1_false_origin_short942 _ _ hs ha1 ha3 he0)

end RT1False942

theorem cycle_power_eight_alternating_false_phase_no_defect (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0)
    (halt : ∀ p : ℤ, x (p + 1) 1 = !(x p 1)) :
    ∀ p : ℤ, x p 1 = false → e p = false := by
  exact RT1False942.rt1_false_phase942 x e hm halt
