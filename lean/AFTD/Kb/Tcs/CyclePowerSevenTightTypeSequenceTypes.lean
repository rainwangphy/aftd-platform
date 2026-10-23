import AFTD.Prelude

/-!
# cycle_power_seven_tight_type_sequence_types

Topic: graphs   Node: 8f9600b618db

Provenance: helper lemma. step for simple_graph_cycle_power_seven_cover_four_tight_dvd (research thread RT-1, open case k = 7 of OP-205, arXiv:2610.15635)

Layer-free type classification for tight 4-covers of C_n^7. Let x p j say that the class starting at p (the class of the distance-7 pair (p, p+7)) contains p + j. Assume the counting system of cycle_power_seven_tight_type_sequence_one_iff_six together with its conclusion x p 1 = x p 6. Then the classes alternate around the cycle. A class without p+1 is just {p, p+7}. A class with p+1 is {p, p+1, p+6, p+7}, plus {p+2, p+3} exactly when the class two steps back lacks p+4 and p+5, plus {p+4, p+5} otherwise. Its bit for p+2 has period 4.
-/

theorem cycle_power_seven_tight_type_cov_forms (y : ℤ → Fin 8 → Bool)
    (hcov : ∀ (d : ℕ) (o : ℤ), d ∈ ({1, 2, 3, 5} : Finset ℕ) →
      ∃ j : Fin 8, ∃ hj : j.val + d ≤ 7, y (o - j.val) j = true ∧
        y (o - j.val) ⟨j.val + d, by omega⟩ = true) :
    (∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true) ∧
    (∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true) ∧
    (∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true) ∧
    (∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro o _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    obtain ⟨j, hj, h1, h2⟩ := hcov 1 o (by decide)
    clear hcov
    fin_cases j <;> (try simp at hj) <;> simp_all
  · rintro o _ _ _ _ _ rfl rfl rfl rfl rfl
    obtain ⟨j, hj, h1, h2⟩ := hcov 2 o (by decide)
    clear hcov
    fin_cases j <;> (try simp at hj) <;> simp_all
  · rintro o _ _ _ _ rfl rfl rfl rfl
    obtain ⟨j, hj, h1, h2⟩ := hcov 3 o (by decide)
    clear hcov
    fin_cases j <;> (try simp at hj) <;> simp_all
  · rintro o _ _ rfl rfl
    obtain ⟨j, hj, h1, h2⟩ := hcov 5 o (by decide)
    clear hcov
    fin_cases j <;> (try simp at hj) <;> simp_all

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_p2 (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = false) (H1 : y 0 2 = true) : False := by
  have c_t16_0 := h16 0
  have c_t26_0 := h26 0
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y 0 1 = v0_1 at *
  generalize y 0 2 = v0_2 at *
  generalize y 0 6 = v0_6 at *
  subst H0
  subst H1
  have e : v0_6 = true := by clear * - c_t26_0; revert c_t26_0; revert v0_6; decide
  subst e
  clear * - c_t16_0; revert c_t16_0; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_p3 (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = false) (H1 : y 0 3 = true) : False := by
  have c_count_1 := hcount 1 0 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_3 := hcount 3 2 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_5 := hcount 5 4 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_1 := cov2 1 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_3 := cov2 3 2 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov5_3 := cov5 3 2 1 (by norm_num) (by norm_num)
  have c_d4_1 := hd4 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_0 := hd6 0 (-1) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_d6_2 := hd6 2 1 (by norm_num)
  have c_d6_4 := hd6 4 3 (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_t16_0 := h16 0
  have c_t16_1 := h16 1
  have c_t16_2 := h16 2
  have c_t16_4 := h16 4
  have c_t16_m1 := h16 (-1)
  have c_t16_m2 := h16 (-2)
  have c_t16_m3 := h16 (-3)
  have c_t16_m4 := h16 (-4)
  have c_t16_m5 := h16 (-5)
  have c_t51_0 := h51 0
  have c_t51_3 := h51 3
  have c_t51_m2 := h51 (-2)
  have c_t51_m4 := h51 (-4)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 5 = vm4_5 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 4 = vm3_4 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 3 = vm2_3 at *
  generalize y (-2) 5 = vm2_5 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 2 = vm1_2 at *
  generalize y (-1) 4 = vm1_4 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 3 = v0_3 at *
  generalize y 0 5 = v0_5 at *
  generalize y 0 6 = v0_6 at *
  generalize y 1 1 = v1_1 at *
  generalize y 1 2 = v1_2 at *
  generalize y 1 4 = v1_4 at *
  generalize y 1 6 = v1_6 at *
  generalize y 2 1 = v2_1 at *
  generalize y 2 3 = v2_3 at *
  generalize y 2 6 = v2_6 at *
  generalize y 3 1 = v3_1 at *
  generalize y 3 2 = v3_2 at *
  generalize y 3 5 = v3_5 at *
  generalize y 4 1 = v4_1 at *
  generalize y 4 6 = v4_6 at *
  subst H0
  subst H1
  have e : v0_5 = false := by clear * - c_t51_0; revert c_t51_0; revert v0_5; decide
  subst e
  have e : v0_6 = false := by clear * - c_t16_0; revert c_t16_0; revert v0_6; decide
  subst e
  have e : vm1_1 = true := by clear * - c_d6_0; revert c_d6_0; revert vm1_1; decide
  subst e
  have e : vm1_6 = true := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_6; decide
  subst e
  have e : vm2_1 = false := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
  subst e
  have e : vm2_5 = false := by clear * - c_t51_m2; revert c_t51_m2; revert vm2_5; decide
  subst e
  have e : vm2_6 = false := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_6; decide
  subst e
  have e : vm3_1 = true := by clear * - c_d6_m2; revert c_d6_m2; revert vm3_1; decide
  subst e
  have e : vm3_6 = true := by clear * - c_t16_m3; revert c_t16_m3; revert vm3_6; decide
  subst e
  have e : vm4_1 = false := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
  subst e
  have e : vm4_5 = false := by clear * - c_t51_m4; revert c_t51_m4; revert vm4_5; decide
  subst e
  have e : vm4_6 = false := by clear * - c_t16_m4; revert c_t16_m4; revert vm4_6; decide
  subst e
  have e : vm5_1 = true := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
  subst e
  have e : vm5_6 = true := by clear * - c_t16_m5; revert c_t16_m5; revert vm5_6; decide
  subst e
  have e : v1_6 = true := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
  subst e
  have e : v1_1 = true := by clear * - c_t16_1; revert c_t16_1; revert v1_1; decide
  subst e
  have e : v2_6 = false := by clear * - c_d6_2; revert c_d6_2; revert v2_6; decide
  subst e
  have e : v2_1 = false := by clear * - c_t16_2; revert c_t16_2; revert v2_1; decide
  subst e
  have e : v1_2 = false := by clear * - c_count_3; revert c_count_3; revert v1_2 vm1_4; decide
  subst e
  have e : vm1_4 = false := by clear * - c_count_3; revert c_count_3; revert vm1_4; decide
  subst e
  have e : vm3_4 = true := by clear * - c_cov2_1; revert c_cov2_1; revert vm3_4 vm2_3 vm1_2; decide
  subst e
  have e : vm1_2 = false := by clear * - c_count_1; revert c_count_1; revert vm1_2 vm2_3; decide
  subst e
  have e : vm2_3 = false := by clear * - c_count_1; revert c_count_1; revert vm2_3; decide
  subst e
  have e : v1_4 = true := by clear * - c_d4_1; revert c_d4_1; revert v1_4; decide
  subst e
  have e : v3_2 = true := by clear * - c_cov2_3; revert c_cov2_3; revert v2_3 v3_2; decide
  subst e
  have e : v3_5 = true := by clear * - c_cov5_3; revert c_cov5_3; revert v3_5; decide
  subst e
  have e : v3_1 = true := by clear * - c_t51_3; revert c_t51_3; revert v3_1; decide
  subst e
  have e : v4_6 = false := by clear * - c_d6_4; revert c_d6_4; revert v4_6; decide
  subst e
  have e : v4_1 = false := by clear * - c_t16_4; revert c_t16_4; revert v4_1; decide
  subst e
  clear * - c_count_5; revert c_count_5; revert v2_3; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_p4 (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = false) (H1 : y 0 4 = true) : False := by
  have c_count_1 := hcount 1 0 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_4 := hcount 4 3 2 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m1 := hcount (-1) (-2) (-3) (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m3 := hcount (-3) (-4) (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_0 := cov1 0 (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_m4 := cov1 (-4) (-5) (-6) (-7) (-8) (-9) (-10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_1 := cov3 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m4 := cov3 (-4) (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov5_m1 := cov5 (-1) (-2) (-3) (by norm_num) (by norm_num)
  have c_d4_0 := hd4 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m3 := hd4 (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m4 := hd4 (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m8 := hd4 (-8) (-9) (-10) (-11) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_0 := hd6 0 (-1) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_d6_2 := hd6 2 1 (by norm_num)
  have c_d6_3 := hd6 3 2 (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_d6_m5 := hd6 (-5) (-6) (by norm_num)
  have c_d6_m6 := hd6 (-6) (-7) (by norm_num)
  have c_d6_m7 := hd6 (-7) (-8) (by norm_num)
  have c_d6_m8 := hd6 (-8) (-9) (by norm_num)
  have c_d6_m9 := hd6 (-9) (-10) (by norm_num)
  have c_t16_0 := h16 0
  have c_t16_1 := h16 1
  have c_t16_2 := h16 2
  have c_t16_3 := h16 3
  have c_t16_m1 := h16 (-1)
  have c_t16_m10 := h16 (-10)
  have c_t16_m2 := h16 (-2)
  have c_t16_m3 := h16 (-3)
  have c_t16_m4 := h16 (-4)
  have c_t16_m5 := h16 (-5)
  have c_t16_m6 := h16 (-6)
  have c_t16_m7 := h16 (-7)
  have c_t16_m8 := h16 (-8)
  have c_t16_m9 := h16 (-9)
  have c_t26_2 := h26 2
  have c_t26_m10 := h26 (-10)
  have c_t26_m2 := h26 (-2)
  have c_t26_m6 := h26 (-6)
  have c_t51_m4 := h51 (-4)
  have c_t51_m6 := h51 (-6)
  have c_t51_m8 := h51 (-8)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-11) 3 = vm11_3 at *
  generalize y (-10) 1 = vm10_1 at *
  generalize y (-10) 2 = vm10_2 at *
  generalize y (-10) 6 = vm10_6 at *
  generalize y (-9) 1 = vm9_1 at *
  generalize y (-9) 5 = vm9_5 at *
  generalize y (-9) 6 = vm9_6 at *
  generalize y (-8) 1 = vm8_1 at *
  generalize y (-8) 4 = vm8_4 at *
  generalize y (-8) 5 = vm8_5 at *
  generalize y (-8) 6 = vm8_6 at *
  generalize y (-7) 1 = vm7_1 at *
  generalize y (-7) 3 = vm7_3 at *
  generalize y (-7) 4 = vm7_4 at *
  generalize y (-7) 6 = vm7_6 at *
  generalize y (-6) 1 = vm6_1 at *
  generalize y (-6) 2 = vm6_2 at *
  generalize y (-6) 3 = vm6_3 at *
  generalize y (-6) 5 = vm6_5 at *
  generalize y (-6) 6 = vm6_6 at *
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 2 = vm5_2 at *
  generalize y (-5) 4 = vm5_4 at *
  generalize y (-5) 5 = vm5_5 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 3 = vm4_3 at *
  generalize y (-4) 4 = vm4_4 at *
  generalize y (-4) 5 = vm4_5 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 2 = vm3_2 at *
  generalize y (-3) 3 = vm3_3 at *
  generalize y (-3) 4 = vm3_4 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 2 = vm2_2 at *
  generalize y (-2) 3 = vm2_3 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 2 = vm1_2 at *
  generalize y (-1) 5 = vm1_5 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 4 = v0_4 at *
  generalize y 0 6 = v0_6 at *
  generalize y 1 1 = v1_1 at *
  generalize y 1 3 = v1_3 at *
  generalize y 1 6 = v1_6 at *
  generalize y 2 1 = v2_1 at *
  generalize y 2 2 = v2_2 at *
  generalize y 2 6 = v2_6 at *
  generalize y 3 1 = v3_1 at *
  generalize y 3 6 = v3_6 at *
  subst H0
  subst H1
  have e : vm3_3 = false := by clear * - c_d4_0; revert c_d4_0; revert vm1_1 vm1_5 vm2_2 vm2_6 vm3_3; decide
  subst e
  have e : v0_6 = false := by clear * - c_t16_0; revert c_t16_0; revert v0_6; decide
  subst e
  have e : vm1_1 = true := by clear * - c_d6_0; revert c_d6_0; revert vm1_1; decide
  subst e
  have e : vm1_6 = true := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_6; decide
  subst e
  have e : vm2_1 = false := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
  subst e
  have e : vm2_6 = false := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_6; decide
  subst e
  have e : vm3_1 = true := by clear * - c_d6_m2; revert c_d6_m2; revert vm3_1; decide
  subst e
  have e : vm3_6 = true := by clear * - c_t16_m3; revert c_t16_m3; revert vm3_6; decide
  subst e
  have e : vm4_1 = false := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
  subst e
  have e : vm4_5 = false := by clear * - c_t51_m4; revert c_t51_m4; revert vm4_5; decide
  subst e
  have e : vm4_6 = false := by clear * - c_t16_m4; revert c_t16_m4; revert vm4_6; decide
  subst e
  have e : vm5_1 = true := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
  subst e
  have e : vm5_6 = true := by clear * - c_t16_m5; revert c_t16_m5; revert vm5_6; decide
  subst e
  have e : vm6_1 = false := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
  subst e
  have e : vm6_5 = false := by clear * - c_t51_m6; revert c_t51_m6; revert vm6_5; decide
  subst e
  have e : vm6_6 = false := by clear * - c_t16_m6; revert c_t16_m6; revert vm6_6; decide
  subst e
  have e : vm7_1 = true := by clear * - c_d6_m6; revert c_d6_m6; revert vm7_1; decide
  subst e
  have e : vm7_6 = true := by clear * - c_t16_m7; revert c_t16_m7; revert vm7_6; decide
  subst e
  have e : vm8_1 = false := by clear * - c_d6_m7; revert c_d6_m7; revert vm8_1; decide
  subst e
  have e : vm8_5 = false := by clear * - c_t51_m8; revert c_t51_m8; revert vm8_5; decide
  subst e
  have e : vm8_6 = false := by clear * - c_t16_m8; revert c_t16_m8; revert vm8_6; decide
  subst e
  have e : vm9_1 = true := by clear * - c_d6_m8; revert c_d6_m8; revert vm9_1; decide
  subst e
  have e : vm9_6 = true := by clear * - c_t16_m9; revert c_t16_m9; revert vm9_6; decide
  subst e
  have e : vm10_1 = false := by clear * - c_d6_m9; revert c_d6_m9; revert vm10_1; decide
  subst e
  have e : vm10_6 = false := by clear * - c_t16_m10; revert c_t16_m10; revert vm10_6; decide
  subst e
  have e : vm10_2 = false := by clear * - c_t26_m10; revert c_t26_m10; revert vm10_2; decide
  subst e
  have e : vm6_2 = false := by clear * - c_t26_m6; revert c_t26_m6; revert vm6_2; decide
  subst e
  have e : vm2_2 = false := by clear * - c_t26_m2; revert c_t26_m2; revert vm2_2; decide
  subst e
  have e : vm1_5 = false := by clear * - c_d4_0; revert c_d4_0; revert vm1_5; decide
  subst e
  have e : vm3_2 = true := by clear * - c_cov5_m1; revert c_cov5_m1; revert vm3_2; decide
  subst e
  have e : vm4_3 = false := by clear * - c_count_m1; revert c_count_m1; revert vm4_3 vm5_4; decide
  subst e
  have e : vm5_4 = false := by clear * - c_count_m1; revert c_count_m1; revert vm5_4; decide
  subst e
  have e : v1_6 = true := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
  subst e
  have e : v1_1 = true := by clear * - c_t16_1; revert c_t16_1; revert v1_1; decide
  subst e
  have e : v2_6 = false := by clear * - c_d6_2; revert c_d6_2; revert v2_6; decide
  subst e
  have e : v2_2 = false := by clear * - c_t26_2; revert c_t26_2; revert v2_2; decide
  subst e
  have e : v2_1 = false := by clear * - c_t16_2; revert c_t16_2; revert v2_1; decide
  subst e
  have e : v3_6 = true := by clear * - c_d6_3; revert c_d6_3; revert v3_6; decide
  subst e
  have e : v3_1 = true := by clear * - c_t16_3; revert c_t16_3; revert v3_1; decide
  subst e
  have e : v1_3 = false := by clear * - c_count_4; revert c_count_4; revert v1_3; decide
  subst e
  have e : vm3_4 = true := by clear * - c_cov3_1; revert c_cov3_1; revert vm3_4 vm2_3 vm1_2; decide
  subst e
  have e : vm5_2 = false := by clear * - c_d4_m3; revert c_d4_m3; revert vm5_2 vm6_3; decide
  subst e
  have e : vm6_3 = false := by clear * - c_d4_m3; revert c_d4_m3; revert vm6_3; decide
  subst e
  have e : vm7_4 = true := by clear * - c_count_m3; revert c_count_m3; revert vm7_4; decide
  subst e
  have e : vm1_2 = false := by clear * - c_count_1; revert c_count_1; revert vm1_2 vm2_3; decide
  subst e
  have e : vm5_5 = true := by clear * - c_cov1_0; revert c_cov1_0; revert vm5_5 vm4_4 vm2_3; decide
  subst e
  have e : vm4_4 = false := by clear * - c_d4_m4; revert c_d4_m4; revert vm4_4 vm7_3; decide
  subst e
  have e : vm7_3 = false := by clear * - c_d4_m4; revert c_d4_m4; revert vm7_3; decide
  subst e
  have e : vm9_5 = true := by clear * - c_cov1_m4; revert c_cov1_m4; revert vm9_5 vm8_4; decide
  subst e
  have e : vm8_4 = false := by clear * - c_d4_m8; revert c_d4_m8; revert vm8_4 vm11_3; decide
  subst e
  clear * - c_cov3_m4; revert c_cov3_m4; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_p5 (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = false) (H1 : y 0 5 = true) : False := by
  have c_t51_0 := h51 0
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y 0 1 = v0_1 at *
  generalize y 0 5 = v0_5 at *
  subst H0
  subst H1
  clear * - c_t51_0; revert c_t51_0; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_n23a (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = true) (H1 : y 0 2 = true) (H2 : y 0 3 = false) : False := by
  have c_count_0 := hcount 0 (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_2 := hcount 2 1 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_4 := hcount 4 3 2 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_6 := hcount 6 5 4 3 2 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m10 := hcount (-10) (-11) (-12) (-13) (-14) (-15) (-16) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m11 := hcount (-11) (-12) (-13) (-14) (-15) (-16) (-17) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m13 := hcount (-13) (-14) (-15) (-16) (-17) (-18) (-19) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m2 := hcount (-2) (-3) (-4) (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m6 := hcount (-6) (-7) (-8) (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_3 := cov1 3 2 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_m1 := cov1 (-1) (-2) (-3) (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_2 := cov2 2 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_4 := cov2 4 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_m11 := cov2 (-11) (-12) (-13) (-14) (-15) (-16) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_m13 := cov2 (-13) (-14) (-15) (-16) (-17) (-18) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_3 := cov3 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m1 := cov3 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m13 := cov3 (-13) (-14) (-15) (-16) (-17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m5 := cov3 (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m9 := cov3 (-9) (-10) (-11) (-12) (-13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov5_m10 := cov5 (-10) (-11) (-12) (by norm_num) (by norm_num)
  have c_cov5_m2 := cov5 (-2) (-3) (-4) (by norm_num) (by norm_num)
  have c_cov5_m6 := cov5 (-6) (-7) (-8) (by norm_num) (by norm_num)
  have c_d4_0 := hd4 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_2 := hd4 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m1 := hd4 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m13 := hd4 (-13) (-14) (-15) (-16) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m15 := hd4 (-15) (-16) (-17) (-18) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m5 := hd4 (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m9 := hd4 (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_0 := hd6 0 (-1) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_d6_10 := hd6 10 9 (by norm_num)
  have c_d6_11 := hd6 11 10 (by norm_num)
  have c_d6_12 := hd6 12 11 (by norm_num)
  have c_d6_13 := hd6 13 12 (by norm_num)
  have c_d6_14 := hd6 14 13 (by norm_num)
  have c_d6_15 := hd6 15 14 (by norm_num)
  have c_d6_16 := hd6 16 15 (by norm_num)
  have c_d6_2 := hd6 2 1 (by norm_num)
  have c_d6_3 := hd6 3 2 (by norm_num)
  have c_d6_4 := hd6 4 3 (by norm_num)
  have c_d6_5 := hd6 5 4 (by norm_num)
  have c_d6_6 := hd6 6 5 (by norm_num)
  have c_d6_7 := hd6 7 6 (by norm_num)
  have c_d6_8 := hd6 8 7 (by norm_num)
  have c_d6_9 := hd6 9 8 (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m10 := hd6 (-10) (-11) (by norm_num)
  have c_d6_m11 := hd6 (-11) (-12) (by norm_num)
  have c_d6_m12 := hd6 (-12) (-13) (by norm_num)
  have c_d6_m13 := hd6 (-13) (-14) (by norm_num)
  have c_d6_m14 := hd6 (-14) (-15) (by norm_num)
  have c_d6_m15 := hd6 (-15) (-16) (by norm_num)
  have c_d6_m16 := hd6 (-16) (-17) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_d6_m5 := hd6 (-5) (-6) (by norm_num)
  have c_d6_m6 := hd6 (-6) (-7) (by norm_num)
  have c_d6_m7 := hd6 (-7) (-8) (by norm_num)
  have c_d6_m8 := hd6 (-8) (-9) (by norm_num)
  have c_d6_m9 := hd6 (-9) (-10) (by norm_num)
  have c_t16_1 := h16 1
  have c_t16_10 := h16 10
  have c_t16_11 := h16 11
  have c_t16_12 := h16 12
  have c_t16_13 := h16 13
  have c_t16_14 := h16 14
  have c_t16_15 := h16 15
  have c_t16_16 := h16 16
  have c_t16_2 := h16 2
  have c_t16_3 := h16 3
  have c_t16_4 := h16 4
  have c_t16_5 := h16 5
  have c_t16_6 := h16 6
  have c_t16_7 := h16 7
  have c_t16_8 := h16 8
  have c_t16_9 := h16 9
  have c_t16_m1 := h16 (-1)
  have c_t16_m10 := h16 (-10)
  have c_t16_m11 := h16 (-11)
  have c_t16_m12 := h16 (-12)
  have c_t16_m13 := h16 (-13)
  have c_t16_m14 := h16 (-14)
  have c_t16_m15 := h16 (-15)
  have c_t16_m16 := h16 (-16)
  have c_t16_m2 := h16 (-2)
  have c_t16_m3 := h16 (-3)
  have c_t16_m4 := h16 (-4)
  have c_t16_m5 := h16 (-5)
  have c_t16_m6 := h16 (-6)
  have c_t16_m7 := h16 (-7)
  have c_t16_m8 := h16 (-8)
  have c_t16_m9 := h16 (-9)
  have c_t26_0 := h26 0
  have c_t26_1 := h26 1
  have c_t26_11 := h26 11
  have c_t26_13 := h26 13
  have c_t26_15 := h26 15
  have c_t26_3 := h26 3
  have c_t26_5 := h26 5
  have c_t26_7 := h26 7
  have c_t26_9 := h26 9
  have c_t26_m1 := h26 (-1)
  have c_t26_m11 := h26 (-11)
  have c_t26_m13 := h26 (-13)
  have c_t26_m15 := h26 (-15)
  have c_t26_m3 := h26 (-3)
  have c_t26_m5 := h26 (-5)
  have c_t26_m7 := h26 (-7)
  have c_t26_m9 := h26 (-9)
  have c_t51_1 := h51 1
  have c_t51_11 := h51 11
  have c_t51_13 := h51 13
  have c_t51_15 := h51 15
  have c_t51_3 := h51 3
  have c_t51_5 := h51 5
  have c_t51_7 := h51 7
  have c_t51_9 := h51 9
  have c_t51_m1 := h51 (-1)
  have c_t51_m11 := h51 (-11)
  have c_t51_m13 := h51 (-13)
  have c_t51_m15 := h51 (-15)
  have c_t51_m3 := h51 (-3)
  have c_t51_m5 := h51 (-5)
  have c_t51_m7 := h51 (-7)
  have c_t51_m9 := h51 (-9)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-19) 6 = vm19_6 at *
  generalize y (-18) 3 = vm18_3 at *
  generalize y (-18) 5 = vm18_5 at *
  generalize y (-17) 1 = vm17_1 at *
  generalize y (-17) 2 = vm17_2 at *
  generalize y (-17) 4 = vm17_4 at *
  generalize y (-17) 6 = vm17_6 at *
  generalize y (-16) 1 = vm16_1 at *
  generalize y (-16) 3 = vm16_3 at *
  generalize y (-16) 5 = vm16_5 at *
  generalize y (-16) 6 = vm16_6 at *
  generalize y (-15) 1 = vm15_1 at *
  generalize y (-15) 2 = vm15_2 at *
  generalize y (-15) 4 = vm15_4 at *
  generalize y (-15) 5 = vm15_5 at *
  generalize y (-15) 6 = vm15_6 at *
  generalize y (-14) 1 = vm14_1 at *
  generalize y (-14) 3 = vm14_3 at *
  generalize y (-14) 4 = vm14_4 at *
  generalize y (-14) 5 = vm14_5 at *
  generalize y (-14) 6 = vm14_6 at *
  generalize y (-13) 1 = vm13_1 at *
  generalize y (-13) 2 = vm13_2 at *
  generalize y (-13) 3 = vm13_3 at *
  generalize y (-13) 4 = vm13_4 at *
  generalize y (-13) 5 = vm13_5 at *
  generalize y (-13) 6 = vm13_6 at *
  generalize y (-12) 1 = vm12_1 at *
  generalize y (-12) 2 = vm12_2 at *
  generalize y (-12) 3 = vm12_3 at *
  generalize y (-12) 6 = vm12_6 at *
  generalize y (-11) 1 = vm11_1 at *
  generalize y (-11) 2 = vm11_2 at *
  generalize y (-11) 5 = vm11_5 at *
  generalize y (-11) 6 = vm11_6 at *
  generalize y (-10) 1 = vm10_1 at *
  generalize y (-10) 4 = vm10_4 at *
  generalize y (-10) 5 = vm10_5 at *
  generalize y (-10) 6 = vm10_6 at *
  generalize y (-9) 1 = vm9_1 at *
  generalize y (-9) 2 = vm9_2 at *
  generalize y (-9) 3 = vm9_3 at *
  generalize y (-9) 4 = vm9_4 at *
  generalize y (-9) 5 = vm9_5 at *
  generalize y (-9) 6 = vm9_6 at *
  generalize y (-8) 1 = vm8_1 at *
  generalize y (-8) 2 = vm8_2 at *
  generalize y (-8) 3 = vm8_3 at *
  generalize y (-8) 6 = vm8_6 at *
  generalize y (-7) 1 = vm7_1 at *
  generalize y (-7) 2 = vm7_2 at *
  generalize y (-7) 5 = vm7_5 at *
  generalize y (-7) 6 = vm7_6 at *
  generalize y (-6) 1 = vm6_1 at *
  generalize y (-6) 4 = vm6_4 at *
  generalize y (-6) 5 = vm6_5 at *
  generalize y (-6) 6 = vm6_6 at *
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 2 = vm5_2 at *
  generalize y (-5) 3 = vm5_3 at *
  generalize y (-5) 4 = vm5_4 at *
  generalize y (-5) 5 = vm5_5 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 2 = vm4_2 at *
  generalize y (-4) 3 = vm4_3 at *
  generalize y (-4) 4 = vm4_4 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 2 = vm3_2 at *
  generalize y (-3) 3 = vm3_3 at *
  generalize y (-3) 5 = vm3_5 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 2 = vm2_2 at *
  generalize y (-2) 4 = vm2_4 at *
  generalize y (-2) 5 = vm2_5 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 2 = vm1_2 at *
  generalize y (-1) 3 = vm1_3 at *
  generalize y (-1) 4 = vm1_4 at *
  generalize y (-1) 5 = vm1_5 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 2 = v0_2 at *
  generalize y 0 3 = v0_3 at *
  generalize y 0 4 = v0_4 at *
  generalize y 0 6 = v0_6 at *
  generalize y 1 1 = v1_1 at *
  generalize y 1 2 = v1_2 at *
  generalize y 1 3 = v1_3 at *
  generalize y 1 5 = v1_5 at *
  generalize y 1 6 = v1_6 at *
  generalize y 2 1 = v2_1 at *
  generalize y 2 2 = v2_2 at *
  generalize y 2 4 = v2_4 at *
  generalize y 2 6 = v2_6 at *
  generalize y 3 1 = v3_1 at *
  generalize y 3 2 = v3_2 at *
  generalize y 3 3 = v3_3 at *
  generalize y 3 5 = v3_5 at *
  generalize y 3 6 = v3_6 at *
  generalize y 4 1 = v4_1 at *
  generalize y 4 2 = v4_2 at *
  generalize y 4 6 = v4_6 at *
  generalize y 5 1 = v5_1 at *
  generalize y 5 2 = v5_2 at *
  generalize y 5 5 = v5_5 at *
  generalize y 5 6 = v5_6 at *
  generalize y 6 1 = v6_1 at *
  generalize y 6 6 = v6_6 at *
  generalize y 7 1 = v7_1 at *
  generalize y 7 2 = v7_2 at *
  generalize y 7 5 = v7_5 at *
  generalize y 7 6 = v7_6 at *
  generalize y 8 1 = v8_1 at *
  generalize y 8 6 = v8_6 at *
  generalize y 9 1 = v9_1 at *
  generalize y 9 2 = v9_2 at *
  generalize y 9 5 = v9_5 at *
  generalize y 9 6 = v9_6 at *
  generalize y 10 1 = v10_1 at *
  generalize y 10 6 = v10_6 at *
  generalize y 11 1 = v11_1 at *
  generalize y 11 2 = v11_2 at *
  generalize y 11 5 = v11_5 at *
  generalize y 11 6 = v11_6 at *
  generalize y 12 1 = v12_1 at *
  generalize y 12 6 = v12_6 at *
  generalize y 13 1 = v13_1 at *
  generalize y 13 2 = v13_2 at *
  generalize y 13 5 = v13_5 at *
  generalize y 13 6 = v13_6 at *
  generalize y 14 1 = v14_1 at *
  generalize y 14 6 = v14_6 at *
  generalize y 15 1 = v15_1 at *
  generalize y 15 2 = v15_2 at *
  generalize y 15 5 = v15_5 at *
  generalize y 15 6 = v15_6 at *
  generalize y 16 1 = v16_1 at *
  generalize y 16 6 = v16_6 at *
  subst H0
  subst H1
  subst H2
  have e : v0_6 = true := by clear * - c_t26_0; revert c_t26_0; revert v0_6; decide
  subst e
  have e : vm1_1 = false := by clear * - c_d6_0; revert c_d6_0; revert vm1_1; decide
  subst e
  have e : vm1_5 = false := by clear * - c_t51_m1; revert c_t51_m1; revert vm1_5; decide
  subst e
  have e : vm1_6 = false := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_6; decide
  subst e
  have e : vm2_1 = true := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
  subst e
  have e : vm2_6 = true := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_6; decide
  subst e
  have e : vm3_1 = false := by clear * - c_d6_m2; revert c_d6_m2; revert vm3_1; decide
  subst e
  have e : vm3_5 = false := by clear * - c_t51_m3; revert c_t51_m3; revert vm3_5; decide
  subst e
  have e : vm3_6 = false := by clear * - c_t16_m3; revert c_t16_m3; revert vm3_6; decide
  subst e
  have e : vm4_1 = true := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
  subst e
  have e : vm4_6 = true := by clear * - c_t16_m4; revert c_t16_m4; revert vm4_6; decide
  subst e
  have e : vm5_1 = false := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
  subst e
  have e : vm5_5 = false := by clear * - c_t51_m5; revert c_t51_m5; revert vm5_5; decide
  subst e
  have e : vm5_6 = false := by clear * - c_t16_m5; revert c_t16_m5; revert vm5_6; decide
  subst e
  have e : vm6_1 = true := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
  subst e
  have e : vm6_6 = true := by clear * - c_t16_m6; revert c_t16_m6; revert vm6_6; decide
  subst e
  have e : vm7_1 = false := by clear * - c_d6_m6; revert c_d6_m6; revert vm7_1; decide
  subst e
  have e : vm7_5 = false := by clear * - c_t51_m7; revert c_t51_m7; revert vm7_5; decide
  subst e
  have e : vm7_6 = false := by clear * - c_t16_m7; revert c_t16_m7; revert vm7_6; decide
  subst e
  have e : vm8_1 = true := by clear * - c_d6_m7; revert c_d6_m7; revert vm8_1; decide
  subst e
  have e : vm8_6 = true := by clear * - c_t16_m8; revert c_t16_m8; revert vm8_6; decide
  subst e
  have e : vm9_1 = false := by clear * - c_d6_m8; revert c_d6_m8; revert vm9_1; decide
  subst e
  have e : vm9_5 = false := by clear * - c_t51_m9; revert c_t51_m9; revert vm9_5; decide
  subst e
  have e : vm9_6 = false := by clear * - c_t16_m9; revert c_t16_m9; revert vm9_6; decide
  subst e
  have e : vm10_1 = true := by clear * - c_d6_m9; revert c_d6_m9; revert vm10_1; decide
  subst e
  have e : vm10_6 = true := by clear * - c_t16_m10; revert c_t16_m10; revert vm10_6; decide
  subst e
  have e : vm11_1 = false := by clear * - c_d6_m10; revert c_d6_m10; revert vm11_1; decide
  subst e
  have e : vm11_5 = false := by clear * - c_t51_m11; revert c_t51_m11; revert vm11_5; decide
  subst e
  have e : vm11_6 = false := by clear * - c_t16_m11; revert c_t16_m11; revert vm11_6; decide
  subst e
  have e : vm12_1 = true := by clear * - c_d6_m11; revert c_d6_m11; revert vm12_1; decide
  subst e
  have e : vm12_6 = true := by clear * - c_t16_m12; revert c_t16_m12; revert vm12_6; decide
  subst e
  have e : vm13_1 = false := by clear * - c_d6_m12; revert c_d6_m12; revert vm13_1; decide
  subst e
  have e : vm13_5 = false := by clear * - c_t51_m13; revert c_t51_m13; revert vm13_5; decide
  subst e
  have e : vm13_6 = false := by clear * - c_t16_m13; revert c_t16_m13; revert vm13_6; decide
  subst e
  have e : vm14_1 = true := by clear * - c_d6_m13; revert c_d6_m13; revert vm14_1; decide
  subst e
  have e : vm14_6 = true := by clear * - c_t16_m14; revert c_t16_m14; revert vm14_6; decide
  subst e
  have e : vm15_1 = false := by clear * - c_d6_m14; revert c_d6_m14; revert vm15_1; decide
  subst e
  have e : vm15_5 = false := by clear * - c_t51_m15; revert c_t51_m15; revert vm15_5; decide
  subst e
  have e : vm15_6 = false := by clear * - c_t16_m15; revert c_t16_m15; revert vm15_6; decide
  subst e
  have e : vm16_1 = true := by clear * - c_d6_m15; revert c_d6_m15; revert vm16_1; decide
  subst e
  have e : vm16_6 = true := by clear * - c_t16_m16; revert c_t16_m16; revert vm16_6; decide
  subst e
  have e : vm17_1 = false := by clear * - c_d6_m16; revert c_d6_m16; revert vm17_1; decide
  subst e
  have e : vm15_2 = false := by clear * - c_t26_m15; revert c_t26_m15; revert vm15_2; decide
  subst e
  have e : vm13_2 = false := by clear * - c_t26_m13; revert c_t26_m13; revert vm13_2; decide
  subst e
  have e : vm11_2 = false := by clear * - c_t26_m11; revert c_t26_m11; revert vm11_2; decide
  subst e
  have e : vm9_2 = false := by clear * - c_t26_m9; revert c_t26_m9; revert vm9_2; decide
  subst e
  have e : vm7_2 = false := by clear * - c_t26_m7; revert c_t26_m7; revert vm7_2; decide
  subst e
  have e : vm5_2 = false := by clear * - c_t26_m5; revert c_t26_m5; revert vm5_2; decide
  subst e
  have e : vm3_2 = false := by clear * - c_t26_m3; revert c_t26_m3; revert vm3_2; decide
  subst e
  have e : vm1_2 = false := by clear * - c_t26_m1; revert c_t26_m1; revert vm1_2; decide
  subst e
  have e : v1_6 = false := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
  subst e
  have e : v1_2 = false := by clear * - c_t26_1; revert c_t26_1; revert v1_2; decide
  subst e
  have e : v1_1 = false := by clear * - c_t16_1; revert c_t16_1; revert v1_1; decide
  subst e
  have e : v1_5 = false := by clear * - c_t51_1; revert c_t51_1; revert v1_5; decide
  subst e
  have e : vm1_3 = false := by clear * - c_count_2; revert c_count_2; revert vm1_3 vm2_4; decide
  subst e
  have e : vm2_4 = false := by clear * - c_count_2; revert c_count_2; revert vm2_4; decide
  subst e
  have e : v2_4 = false := by clear * - c_d4_2; revert c_d4_2; revert v2_4; decide
  subst e
  have e : v2_6 = true := by clear * - c_d6_2; revert c_d6_2; revert v2_6; decide
  subst e
  have e : v2_1 = true := by clear * - c_t16_2; revert c_t16_2; revert v2_1; decide
  subst e
  have e : v3_6 = false := by clear * - c_d6_3; revert c_d6_3; revert v3_6; decide
  subst e
  have e : v3_2 = false := by clear * - c_t26_3; revert c_t26_3; revert v3_2; decide
  subst e
  have e : v3_1 = false := by clear * - c_t16_3; revert c_t16_3; revert v3_1; decide
  subst e
  have e : v3_5 = false := by clear * - c_t51_3; revert c_t51_3; revert v3_5; decide
  subst e
  have e : v4_6 = true := by clear * - c_d6_4; revert c_d6_4; revert v4_6; decide
  subst e
  have e : v4_1 = true := by clear * - c_t16_4; revert c_t16_4; revert v4_1; decide
  subst e
  have e : v5_6 = false := by clear * - c_d6_5; revert c_d6_5; revert v5_6; decide
  subst e
  have e : v5_2 = false := by clear * - c_t26_5; revert c_t26_5; revert v5_2; decide
  subst e
  have e : v5_1 = false := by clear * - c_t16_5; revert c_t16_5; revert v5_1; decide
  subst e
  have e : v5_5 = false := by clear * - c_t51_5; revert c_t51_5; revert v5_5; decide
  subst e
  have e : v6_6 = true := by clear * - c_d6_6; revert c_d6_6; revert v6_6; decide
  subst e
  have e : v6_1 = true := by clear * - c_t16_6; revert c_t16_6; revert v6_1; decide
  subst e
  have e : v7_6 = false := by clear * - c_d6_7; revert c_d6_7; revert v7_6; decide
  subst e
  have e : v7_2 = false := by clear * - c_t26_7; revert c_t26_7; revert v7_2; decide
  subst e
  have e : v7_1 = false := by clear * - c_t16_7; revert c_t16_7; revert v7_1; decide
  subst e
  have e : v7_5 = false := by clear * - c_t51_7; revert c_t51_7; revert v7_5; decide
  subst e
  have e : v8_6 = true := by clear * - c_d6_8; revert c_d6_8; revert v8_6; decide
  subst e
  have e : v8_1 = true := by clear * - c_t16_8; revert c_t16_8; revert v8_1; decide
  subst e
  have e : v9_6 = false := by clear * - c_d6_9; revert c_d6_9; revert v9_6; decide
  subst e
  have e : v9_2 = false := by clear * - c_t26_9; revert c_t26_9; revert v9_2; decide
  subst e
  have e : v9_1 = false := by clear * - c_t16_9; revert c_t16_9; revert v9_1; decide
  subst e
  have e : v9_5 = false := by clear * - c_t51_9; revert c_t51_9; revert v9_5; decide
  subst e
  have e : v10_6 = true := by clear * - c_d6_10; revert c_d6_10; revert v10_6; decide
  subst e
  have e : v10_1 = true := by clear * - c_t16_10; revert c_t16_10; revert v10_1; decide
  subst e
  have e : v11_6 = false := by clear * - c_d6_11; revert c_d6_11; revert v11_6; decide
  subst e
  have e : v11_2 = false := by clear * - c_t26_11; revert c_t26_11; revert v11_2; decide
  subst e
  have e : v11_1 = false := by clear * - c_t16_11; revert c_t16_11; revert v11_1; decide
  subst e
  have e : v11_5 = false := by clear * - c_t51_11; revert c_t51_11; revert v11_5; decide
  subst e
  have e : v12_6 = true := by clear * - c_d6_12; revert c_d6_12; revert v12_6; decide
  subst e
  have e : v12_1 = true := by clear * - c_t16_12; revert c_t16_12; revert v12_1; decide
  subst e
  have e : v13_6 = false := by clear * - c_d6_13; revert c_d6_13; revert v13_6; decide
  subst e
  have e : v13_2 = false := by clear * - c_t26_13; revert c_t26_13; revert v13_2; decide
  subst e
  have e : v13_1 = false := by clear * - c_t16_13; revert c_t16_13; revert v13_1; decide
  subst e
  have e : v13_5 = false := by clear * - c_t51_13; revert c_t51_13; revert v13_5; decide
  subst e
  have e : v14_6 = true := by clear * - c_d6_14; revert c_d6_14; revert v14_6; decide
  subst e
  have e : v14_1 = true := by clear * - c_t16_14; revert c_t16_14; revert v14_1; decide
  subst e
  have e : v15_6 = false := by clear * - c_d6_15; revert c_d6_15; revert v15_6; decide
  subst e
  have e : v15_2 = false := by clear * - c_t26_15; revert c_t26_15; revert v15_2; decide
  subst e
  have e : v15_1 = false := by clear * - c_t16_15; revert c_t16_15; revert v15_1; decide
  subst e
  have e : v15_5 = false := by clear * - c_t51_15; revert c_t51_15; revert v15_5; decide
  subst e
  have e : v16_6 = true := by clear * - c_d6_16; revert c_d6_16; revert v16_6; decide
  subst e
  have e : v16_1 = true := by clear * - c_t16_16; revert c_t16_16; revert v16_1; decide
  subst e
  cases v0_4
  · have e : v2_2 = true := by clear * - c_cov2_2; revert c_cov2_2; revert v1_3 v2_2; decide
    subst e
    have e : v1_3 = false := by clear * - c_count_4; revert c_count_4; revert v1_3; decide
    subst e
    have e : v4_2 = true := by clear * - c_cov2_4; revert c_cov2_4; revert v3_3 v4_2; decide
    subst e
    have e : v3_3 = false := by clear * - c_count_6; revert c_count_6; revert v3_3; decide
    subst e
    have e : vm1_4 = true := by clear * - c_cov3_3; revert c_cov3_3; revert vm1_4; decide
    subst e
    have e : vm2_5 = false := by clear * - c_d4_m1; revert c_d4_m1; revert vm2_5 vm4_3; decide
    subst e
    have e : vm4_2 = true := by clear * - c_cov5_m2; revert c_cov5_m2; revert vm4_2; decide
    subst e
    have e : vm5_3 = false := by clear * - c_count_m2; revert c_count_m2; revert vm5_3 vm6_4; decide
    subst e
    have e : vm6_4 = false := by clear * - c_count_m2; revert c_count_m2; revert vm6_4; decide
    subst e
    have e : vm4_3 = false := by clear * - c_d4_m1; revert c_d4_m1; revert vm4_3; decide
    subst e
    have e : vm5_4 = true := by clear * - c_cov3_m1; revert c_cov3_m1; revert vm5_4; decide
    subst e
    have e : vm6_5 = false := by clear * - c_d4_m5; revert c_d4_m5; revert vm6_5 vm8_3; decide
    subst e
    have e : vm8_2 = true := by clear * - c_cov5_m6; revert c_cov5_m6; revert vm8_2; decide
    subst e
    have e : vm9_3 = false := by clear * - c_count_m6; revert c_count_m6; revert vm9_3 vm10_4; decide
    subst e
    have e : vm10_4 = false := by clear * - c_count_m6; revert c_count_m6; revert vm10_4; decide
    subst e
    have e : vm8_3 = false := by clear * - c_d4_m5; revert c_d4_m5; revert vm8_3; decide
    subst e
    have e : vm9_4 = true := by clear * - c_cov3_m5; revert c_cov3_m5; revert vm9_4; decide
    subst e
    have e : vm10_5 = false := by clear * - c_d4_m9; revert c_d4_m9; revert vm10_5 vm12_3; decide
    subst e
    have e : vm12_2 = true := by clear * - c_cov5_m10; revert c_cov5_m10; revert vm12_2; decide
    subst e
    have e : vm13_3 = false := by clear * - c_count_m10; revert c_count_m10; revert vm13_3 vm14_4; decide
    subst e
    have e : vm14_4 = false := by clear * - c_count_m10; revert c_count_m10; revert vm14_4; decide
    subst e
    have e : vm12_3 = false := by clear * - c_d4_m9; revert c_d4_m9; revert vm12_3; decide
    subst e
    have e : vm13_4 = true := by clear * - c_cov3_m9; revert c_cov3_m9; revert vm13_4; decide
    subst e
    have e : vm14_5 = false := by clear * - c_d4_m13; revert c_d4_m13; revert vm14_5 vm16_3; decide
    subst e
    have e : vm16_3 = false := by clear * - c_d4_m13; revert c_d4_m13; revert vm16_3; decide
    subst e
    have e : vm17_4 = true := by clear * - c_cov3_m13; revert c_cov3_m13; revert vm17_4; decide
    subst e
    have e : vm18_5 = false := by clear * - c_count_m13; revert c_count_m13; revert vm18_5 vm19_6; decide
    subst e
    have e : vm16_5 = true := by clear * - c_cov2_m11; revert c_cov2_m11; revert vm16_5 vm15_4 vm14_3; decide
    subst e
    have e : vm15_4 = false := by clear * - c_d4_m15; revert c_d4_m15; revert vm15_4 vm17_2 vm17_6 vm18_3; decide
    subst e
    have e : vm14_3 = false := by clear * - c_count_m11; revert c_count_m11; revert vm14_3 vm17_6; decide
    subst e
    have e : vm17_6 = true := by clear * - c_cov2_m13; revert c_cov2_m13; revert vm17_6; decide
    subst e
    clear * - c_count_m11; revert c_count_m11; decide
  · have e : vm2_2 = false := by clear * - c_d4_0; revert c_d4_0; revert vm2_2 vm3_3; decide
    subst e
    have e : vm3_3 = false := by clear * - c_d4_0; revert c_d4_0; revert vm3_3; decide
    subst e
    have e : vm4_4 = true := by clear * - c_count_0; revert c_count_0; revert vm4_4; decide
    subst e
    have e : v2_2 = false := by clear * - c_count_4; revert c_count_4; revert v2_2 v1_3; decide
    subst e
    have e : vm2_5 = true := by clear * - c_cov1_3; revert c_cov1_3; revert vm2_5 vm1_4 v1_3; decide
    subst e
    have e : vm1_4 = false := by clear * - c_d4_m1; revert c_d4_m1; revert vm1_4 vm4_3; decide
    subst e
    have e : vm4_3 = false := by clear * - c_d4_m1; revert c_d4_m1; revert vm4_3; decide
    subst e
    have e : vm6_5 = true := by clear * - c_cov1_m1; revert c_cov1_m1; revert vm6_5 vm5_4; decide
    subst e
    have e : vm5_4 = false := by clear * - c_d4_m5; revert c_d4_m5; revert vm5_4 vm8_3; decide
    subst e
    clear * - c_cov3_m1; revert c_cov3_m1; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_n23b (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = true) (H1 : y 0 2 = false) (H2 : y 0 3 = true) : False := by
  have c_cov5_2 := cov5 2 1 0 (by norm_num) (by norm_num)
  have c_d4_3 := hd4 3 2 1 0 (by norm_num) (by norm_num) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_t16_1 := h16 1
  have c_t26_1 := h26 1
  have c_t51_2 := h51 2
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y 0 1 = v0_1 at *
  generalize y 0 2 = v0_2 at *
  generalize y 0 3 = v0_3 at *
  generalize y 1 1 = v1_1 at *
  generalize y 1 2 = v1_2 at *
  generalize y 1 6 = v1_6 at *
  generalize y 2 1 = v2_1 at *
  generalize y 2 5 = v2_5 at *
  generalize y 3 4 = v3_4 at *
  subst H0
  subst H1
  subst H2
  have e : v1_6 = false := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
  subst e
  have e : v1_2 = false := by clear * - c_t26_1; revert c_t26_1; revert v1_2; decide
  subst e
  have e : v1_1 = false := by clear * - c_t16_1; revert c_t16_1; revert v1_1; decide
  subst e
  have e : v2_5 = true := by clear * - c_cov5_2; revert c_cov5_2; revert v2_5; decide
  subst e
  have e : v2_1 = true := by clear * - c_t51_2; revert c_t51_2; revert v2_1; decide
  subst e
  clear * - c_d4_3; revert c_d4_3; revert v3_4; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_n45a (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = true) (H1 : y 0 4 = true) (H2 : y 0 5 = false) : False := by
  have c_cov5_0 := cov5 0 (-1) (-2) (by norm_num) (by norm_num)
  have c_d4_0 := hd4 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_0 := hd6 0 (-1) (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_t16_0 := h16 0
  have c_t16_m1 := h16 (-1)
  have c_t16_m2 := h16 (-2)
  have c_t51_m1 := h51 (-1)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-3) 3 = vm3_3 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 2 = vm2_2 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 5 = vm1_5 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 4 = v0_4 at *
  generalize y 0 5 = v0_5 at *
  generalize y 0 6 = v0_6 at *
  subst H0
  subst H1
  subst H2
  have e : vm3_3 = false := by clear * - c_d4_0; revert c_d4_0; revert vm1_1 vm1_5 vm2_2 vm2_6 vm3_3; decide
  subst e
  have e : v0_6 = true := by clear * - c_t16_0; revert c_t16_0; revert v0_6; decide
  subst e
  have e : vm1_1 = false := by clear * - c_d6_0; revert c_d6_0; revert vm1_1; decide
  subst e
  have e : vm1_5 = false := by clear * - c_t51_m1; revert c_t51_m1; revert vm1_5; decide
  subst e
  have e : vm1_6 = false := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_6; decide
  subst e
  have e : vm2_1 = true := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
  subst e
  have e : vm2_6 = true := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_6; decide
  subst e
  have e : vm2_2 = false := by clear * - c_d4_0; revert c_d4_0; revert vm2_2; decide
  subst e
  clear * - c_cov5_0; revert c_cov5_0; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_n45b (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = true) (H1 : y 0 4 = false) (H2 : y 0 5 = true) : False := by
  have c_count_2 := hcount 2 1 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_4 := hcount 4 3 2 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_5 := hcount 5 4 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_6 := hcount 6 5 4 3 2 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m2 := hcount (-2) (-3) (-4) (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m4 := hcount (-4) (-5) (-6) (-7) (-8) (-9) (-10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m6 := hcount (-6) (-7) (-8) (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_1 := cov1 1 0 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_m3 := cov1 (-3) (-4) (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_m7 := cov1 (-7) (-8) (-9) (-10) (-11) (-12) (-13) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_2 := cov2 2 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_4 := cov2 4 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_1 := cov3 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_2 := cov3 2 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m2 := cov3 (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m7 := cov3 (-7) (-8) (-9) (-10) (-11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov5_m4 := cov5 (-4) (-5) (-6) (by norm_num) (by norm_num)
  have c_d4_1 := hd4 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_2 := hd4 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m11 := hd4 (-11) (-12) (-13) (-14) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m3 := hd4 (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m6 := hd4 (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m7 := hd4 (-7) (-8) (-9) (-10) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_0 := hd6 0 (-1) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_d6_10 := hd6 10 9 (by norm_num)
  have c_d6_11 := hd6 11 10 (by norm_num)
  have c_d6_12 := hd6 12 11 (by norm_num)
  have c_d6_13 := hd6 13 12 (by norm_num)
  have c_d6_14 := hd6 14 13 (by norm_num)
  have c_d6_15 := hd6 15 14 (by norm_num)
  have c_d6_16 := hd6 16 15 (by norm_num)
  have c_d6_2 := hd6 2 1 (by norm_num)
  have c_d6_3 := hd6 3 2 (by norm_num)
  have c_d6_4 := hd6 4 3 (by norm_num)
  have c_d6_5 := hd6 5 4 (by norm_num)
  have c_d6_6 := hd6 6 5 (by norm_num)
  have c_d6_7 := hd6 7 6 (by norm_num)
  have c_d6_8 := hd6 8 7 (by norm_num)
  have c_d6_9 := hd6 9 8 (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m10 := hd6 (-10) (-11) (by norm_num)
  have c_d6_m11 := hd6 (-11) (-12) (by norm_num)
  have c_d6_m12 := hd6 (-12) (-13) (by norm_num)
  have c_d6_m13 := hd6 (-13) (-14) (by norm_num)
  have c_d6_m14 := hd6 (-14) (-15) (by norm_num)
  have c_d6_m15 := hd6 (-15) (-16) (by norm_num)
  have c_d6_m16 := hd6 (-16) (-17) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_d6_m5 := hd6 (-5) (-6) (by norm_num)
  have c_d6_m6 := hd6 (-6) (-7) (by norm_num)
  have c_d6_m7 := hd6 (-7) (-8) (by norm_num)
  have c_d6_m8 := hd6 (-8) (-9) (by norm_num)
  have c_d6_m9 := hd6 (-9) (-10) (by norm_num)
  have c_t16_0 := h16 0
  have c_t16_1 := h16 1
  have c_t16_10 := h16 10
  have c_t16_11 := h16 11
  have c_t16_12 := h16 12
  have c_t16_13 := h16 13
  have c_t16_14 := h16 14
  have c_t16_15 := h16 15
  have c_t16_16 := h16 16
  have c_t16_2 := h16 2
  have c_t16_3 := h16 3
  have c_t16_4 := h16 4
  have c_t16_5 := h16 5
  have c_t16_6 := h16 6
  have c_t16_7 := h16 7
  have c_t16_8 := h16 8
  have c_t16_9 := h16 9
  have c_t16_m1 := h16 (-1)
  have c_t16_m10 := h16 (-10)
  have c_t16_m11 := h16 (-11)
  have c_t16_m12 := h16 (-12)
  have c_t16_m13 := h16 (-13)
  have c_t16_m14 := h16 (-14)
  have c_t16_m15 := h16 (-15)
  have c_t16_m16 := h16 (-16)
  have c_t16_m2 := h16 (-2)
  have c_t16_m3 := h16 (-3)
  have c_t16_m4 := h16 (-4)
  have c_t16_m5 := h16 (-5)
  have c_t16_m6 := h16 (-6)
  have c_t16_m7 := h16 (-7)
  have c_t16_m8 := h16 (-8)
  have c_t16_m9 := h16 (-9)
  have c_t26_1 := h26 1
  have c_t26_11 := h26 11
  have c_t26_13 := h26 13
  have c_t26_15 := h26 15
  have c_t26_3 := h26 3
  have c_t26_5 := h26 5
  have c_t26_7 := h26 7
  have c_t26_9 := h26 9
  have c_t26_m1 := h26 (-1)
  have c_t26_m11 := h26 (-11)
  have c_t26_m13 := h26 (-13)
  have c_t26_m15 := h26 (-15)
  have c_t26_m3 := h26 (-3)
  have c_t26_m5 := h26 (-5)
  have c_t26_m7 := h26 (-7)
  have c_t26_m9 := h26 (-9)
  have c_t51_1 := h51 1
  have c_t51_11 := h51 11
  have c_t51_13 := h51 13
  have c_t51_15 := h51 15
  have c_t51_3 := h51 3
  have c_t51_5 := h51 5
  have c_t51_7 := h51 7
  have c_t51_9 := h51 9
  have c_t51_m1 := h51 (-1)
  have c_t51_m11 := h51 (-11)
  have c_t51_m13 := h51 (-13)
  have c_t51_m15 := h51 (-15)
  have c_t51_m3 := h51 (-3)
  have c_t51_m5 := h51 (-5)
  have c_t51_m7 := h51 (-7)
  have c_t51_m9 := h51 (-9)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-17) 1 = vm17_1 at *
  generalize y (-16) 1 = vm16_1 at *
  generalize y (-16) 6 = vm16_6 at *
  generalize y (-15) 1 = vm15_1 at *
  generalize y (-15) 2 = vm15_2 at *
  generalize y (-15) 5 = vm15_5 at *
  generalize y (-15) 6 = vm15_6 at *
  generalize y (-14) 1 = vm14_1 at *
  generalize y (-14) 3 = vm14_3 at *
  generalize y (-14) 6 = vm14_6 at *
  generalize y (-13) 1 = vm13_1 at *
  generalize y (-13) 2 = vm13_2 at *
  generalize y (-13) 5 = vm13_5 at *
  generalize y (-13) 6 = vm13_6 at *
  generalize y (-12) 1 = vm12_1 at *
  generalize y (-12) 5 = vm12_5 at *
  generalize y (-12) 6 = vm12_6 at *
  generalize y (-11) 1 = vm11_1 at *
  generalize y (-11) 2 = vm11_2 at *
  generalize y (-11) 4 = vm11_4 at *
  generalize y (-11) 5 = vm11_5 at *
  generalize y (-11) 6 = vm11_6 at *
  generalize y (-10) 1 = vm10_1 at *
  generalize y (-10) 3 = vm10_3 at *
  generalize y (-10) 4 = vm10_4 at *
  generalize y (-10) 6 = vm10_6 at *
  generalize y (-9) 1 = vm9_1 at *
  generalize y (-9) 2 = vm9_2 at *
  generalize y (-9) 3 = vm9_3 at *
  generalize y (-9) 5 = vm9_5 at *
  generalize y (-9) 6 = vm9_6 at *
  generalize y (-8) 1 = vm8_1 at *
  generalize y (-8) 2 = vm8_2 at *
  generalize y (-8) 4 = vm8_4 at *
  generalize y (-8) 5 = vm8_5 at *
  generalize y (-8) 6 = vm8_6 at *
  generalize y (-7) 1 = vm7_1 at *
  generalize y (-7) 2 = vm7_2 at *
  generalize y (-7) 3 = vm7_3 at *
  generalize y (-7) 4 = vm7_4 at *
  generalize y (-7) 5 = vm7_5 at *
  generalize y (-7) 6 = vm7_6 at *
  generalize y (-6) 1 = vm6_1 at *
  generalize y (-6) 2 = vm6_2 at *
  generalize y (-6) 3 = vm6_3 at *
  generalize y (-6) 4 = vm6_4 at *
  generalize y (-6) 6 = vm6_6 at *
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 2 = vm5_2 at *
  generalize y (-5) 3 = vm5_3 at *
  generalize y (-5) 5 = vm5_5 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 2 = vm4_2 at *
  generalize y (-4) 5 = vm4_5 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 2 = vm3_2 at *
  generalize y (-3) 4 = vm3_4 at *
  generalize y (-3) 5 = vm3_5 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 3 = vm2_3 at *
  generalize y (-2) 4 = vm2_4 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 2 = vm1_2 at *
  generalize y (-1) 3 = vm1_3 at *
  generalize y (-1) 5 = vm1_5 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 2 = v0_2 at *
  generalize y 0 4 = v0_4 at *
  generalize y 0 5 = v0_5 at *
  generalize y 0 6 = v0_6 at *
  generalize y 1 1 = v1_1 at *
  generalize y 1 2 = v1_2 at *
  generalize y 1 3 = v1_3 at *
  generalize y 1 4 = v1_4 at *
  generalize y 1 5 = v1_5 at *
  generalize y 1 6 = v1_6 at *
  generalize y 2 1 = v2_1 at *
  generalize y 2 2 = v2_2 at *
  generalize y 2 3 = v2_3 at *
  generalize y 2 4 = v2_4 at *
  generalize y 2 6 = v2_6 at *
  generalize y 3 1 = v3_1 at *
  generalize y 3 2 = v3_2 at *
  generalize y 3 3 = v3_3 at *
  generalize y 3 5 = v3_5 at *
  generalize y 3 6 = v3_6 at *
  generalize y 4 1 = v4_1 at *
  generalize y 4 2 = v4_2 at *
  generalize y 4 6 = v4_6 at *
  generalize y 5 1 = v5_1 at *
  generalize y 5 2 = v5_2 at *
  generalize y 5 5 = v5_5 at *
  generalize y 5 6 = v5_6 at *
  generalize y 6 1 = v6_1 at *
  generalize y 6 6 = v6_6 at *
  generalize y 7 1 = v7_1 at *
  generalize y 7 2 = v7_2 at *
  generalize y 7 5 = v7_5 at *
  generalize y 7 6 = v7_6 at *
  generalize y 8 1 = v8_1 at *
  generalize y 8 6 = v8_6 at *
  generalize y 9 1 = v9_1 at *
  generalize y 9 2 = v9_2 at *
  generalize y 9 5 = v9_5 at *
  generalize y 9 6 = v9_6 at *
  generalize y 10 1 = v10_1 at *
  generalize y 10 6 = v10_6 at *
  generalize y 11 1 = v11_1 at *
  generalize y 11 2 = v11_2 at *
  generalize y 11 5 = v11_5 at *
  generalize y 11 6 = v11_6 at *
  generalize y 12 1 = v12_1 at *
  generalize y 12 6 = v12_6 at *
  generalize y 13 1 = v13_1 at *
  generalize y 13 2 = v13_2 at *
  generalize y 13 5 = v13_5 at *
  generalize y 13 6 = v13_6 at *
  generalize y 14 1 = v14_1 at *
  generalize y 14 6 = v14_6 at *
  generalize y 15 1 = v15_1 at *
  generalize y 15 2 = v15_2 at *
  generalize y 15 5 = v15_5 at *
  generalize y 15 6 = v15_6 at *
  generalize y 16 1 = v16_1 at *
  generalize y 16 6 = v16_6 at *
  subst H0
  subst H1
  subst H2
  have e : v0_6 = true := by clear * - c_t16_0; revert c_t16_0; revert v0_6; decide
  subst e
  have e : vm1_1 = false := by clear * - c_d6_0; revert c_d6_0; revert vm1_1; decide
  subst e
  have e : vm1_5 = false := by clear * - c_t51_m1; revert c_t51_m1; revert vm1_5; decide
  subst e
  have e : vm1_6 = false := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_6; decide
  subst e
  have e : vm2_1 = true := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
  subst e
  have e : vm2_6 = true := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_6; decide
  subst e
  have e : vm3_1 = false := by clear * - c_d6_m2; revert c_d6_m2; revert vm3_1; decide
  subst e
  have e : vm3_5 = false := by clear * - c_t51_m3; revert c_t51_m3; revert vm3_5; decide
  subst e
  have e : vm3_6 = false := by clear * - c_t16_m3; revert c_t16_m3; revert vm3_6; decide
  subst e
  have e : vm4_1 = true := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
  subst e
  have e : vm4_6 = true := by clear * - c_t16_m4; revert c_t16_m4; revert vm4_6; decide
  subst e
  have e : vm5_1 = false := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
  subst e
  have e : vm5_5 = false := by clear * - c_t51_m5; revert c_t51_m5; revert vm5_5; decide
  subst e
  have e : vm5_6 = false := by clear * - c_t16_m5; revert c_t16_m5; revert vm5_6; decide
  subst e
  have e : vm6_1 = true := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
  subst e
  have e : vm6_6 = true := by clear * - c_t16_m6; revert c_t16_m6; revert vm6_6; decide
  subst e
  have e : vm7_1 = false := by clear * - c_d6_m6; revert c_d6_m6; revert vm7_1; decide
  subst e
  have e : vm7_5 = false := by clear * - c_t51_m7; revert c_t51_m7; revert vm7_5; decide
  subst e
  have e : vm7_6 = false := by clear * - c_t16_m7; revert c_t16_m7; revert vm7_6; decide
  subst e
  have e : vm8_1 = true := by clear * - c_d6_m7; revert c_d6_m7; revert vm8_1; decide
  subst e
  have e : vm8_6 = true := by clear * - c_t16_m8; revert c_t16_m8; revert vm8_6; decide
  subst e
  have e : vm9_1 = false := by clear * - c_d6_m8; revert c_d6_m8; revert vm9_1; decide
  subst e
  have e : vm9_5 = false := by clear * - c_t51_m9; revert c_t51_m9; revert vm9_5; decide
  subst e
  have e : vm9_6 = false := by clear * - c_t16_m9; revert c_t16_m9; revert vm9_6; decide
  subst e
  have e : vm10_1 = true := by clear * - c_d6_m9; revert c_d6_m9; revert vm10_1; decide
  subst e
  have e : vm10_6 = true := by clear * - c_t16_m10; revert c_t16_m10; revert vm10_6; decide
  subst e
  have e : vm11_1 = false := by clear * - c_d6_m10; revert c_d6_m10; revert vm11_1; decide
  subst e
  have e : vm11_5 = false := by clear * - c_t51_m11; revert c_t51_m11; revert vm11_5; decide
  subst e
  have e : vm11_6 = false := by clear * - c_t16_m11; revert c_t16_m11; revert vm11_6; decide
  subst e
  have e : vm12_1 = true := by clear * - c_d6_m11; revert c_d6_m11; revert vm12_1; decide
  subst e
  have e : vm12_6 = true := by clear * - c_t16_m12; revert c_t16_m12; revert vm12_6; decide
  subst e
  have e : vm13_1 = false := by clear * - c_d6_m12; revert c_d6_m12; revert vm13_1; decide
  subst e
  have e : vm13_5 = false := by clear * - c_t51_m13; revert c_t51_m13; revert vm13_5; decide
  subst e
  have e : vm13_6 = false := by clear * - c_t16_m13; revert c_t16_m13; revert vm13_6; decide
  subst e
  have e : vm14_1 = true := by clear * - c_d6_m13; revert c_d6_m13; revert vm14_1; decide
  subst e
  have e : vm14_6 = true := by clear * - c_t16_m14; revert c_t16_m14; revert vm14_6; decide
  subst e
  have e : vm15_1 = false := by clear * - c_d6_m14; revert c_d6_m14; revert vm15_1; decide
  subst e
  have e : vm15_5 = false := by clear * - c_t51_m15; revert c_t51_m15; revert vm15_5; decide
  subst e
  have e : vm15_6 = false := by clear * - c_t16_m15; revert c_t16_m15; revert vm15_6; decide
  subst e
  have e : vm16_1 = true := by clear * - c_d6_m15; revert c_d6_m15; revert vm16_1; decide
  subst e
  have e : vm16_6 = true := by clear * - c_t16_m16; revert c_t16_m16; revert vm16_6; decide
  subst e
  have e : vm17_1 = false := by clear * - c_d6_m16; revert c_d6_m16; revert vm17_1; decide
  subst e
  have e : vm15_2 = false := by clear * - c_t26_m15; revert c_t26_m15; revert vm15_2; decide
  subst e
  have e : vm13_2 = false := by clear * - c_t26_m13; revert c_t26_m13; revert vm13_2; decide
  subst e
  have e : vm11_2 = false := by clear * - c_t26_m11; revert c_t26_m11; revert vm11_2; decide
  subst e
  have e : vm9_2 = false := by clear * - c_t26_m9; revert c_t26_m9; revert vm9_2; decide
  subst e
  have e : vm7_2 = false := by clear * - c_t26_m7; revert c_t26_m7; revert vm7_2; decide
  subst e
  have e : vm5_2 = false := by clear * - c_t26_m5; revert c_t26_m5; revert vm5_2; decide
  subst e
  have e : vm3_2 = false := by clear * - c_t26_m3; revert c_t26_m3; revert vm3_2; decide
  subst e
  have e : vm1_2 = false := by clear * - c_t26_m1; revert c_t26_m1; revert vm1_2; decide
  subst e
  have e : v1_4 = false := by clear * - c_d4_1; revert c_d4_1; revert v1_4 vm2_3; decide
  subst e
  have e : vm2_3 = false := by clear * - c_d4_1; revert c_d4_1; revert vm2_3; decide
  subst e
  have e : v1_6 = false := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
  subst e
  have e : v1_2 = false := by clear * - c_t26_1; revert c_t26_1; revert v1_2; decide
  subst e
  have e : v1_1 = false := by clear * - c_t16_1; revert c_t16_1; revert v1_1; decide
  subst e
  have e : v1_5 = false := by clear * - c_t51_1; revert c_t51_1; revert v1_5; decide
  subst e
  have e : v2_6 = true := by clear * - c_d6_2; revert c_d6_2; revert v2_6; decide
  subst e
  have e : v2_1 = true := by clear * - c_t16_2; revert c_t16_2; revert v2_1; decide
  subst e
  have e : v3_6 = false := by clear * - c_d6_3; revert c_d6_3; revert v3_6; decide
  subst e
  have e : v3_2 = false := by clear * - c_t26_3; revert c_t26_3; revert v3_2; decide
  subst e
  have e : v3_1 = false := by clear * - c_t16_3; revert c_t16_3; revert v3_1; decide
  subst e
  have e : v3_5 = false := by clear * - c_t51_3; revert c_t51_3; revert v3_5; decide
  subst e
  have e : v4_6 = true := by clear * - c_d6_4; revert c_d6_4; revert v4_6; decide
  subst e
  have e : v4_1 = true := by clear * - c_t16_4; revert c_t16_4; revert v4_1; decide
  subst e
  have e : v2_3 = false := by clear * - c_count_5; revert c_count_5; revert v2_3; decide
  subst e
  have e : v5_6 = false := by clear * - c_d6_5; revert c_d6_5; revert v5_6; decide
  subst e
  have e : v5_2 = false := by clear * - c_t26_5; revert c_t26_5; revert v5_2; decide
  subst e
  have e : v5_1 = false := by clear * - c_t16_5; revert c_t16_5; revert v5_1; decide
  subst e
  have e : v5_5 = false := by clear * - c_t51_5; revert c_t51_5; revert v5_5; decide
  subst e
  have e : v6_6 = true := by clear * - c_d6_6; revert c_d6_6; revert v6_6; decide
  subst e
  have e : v6_1 = true := by clear * - c_t16_6; revert c_t16_6; revert v6_1; decide
  subst e
  have e : v7_6 = false := by clear * - c_d6_7; revert c_d6_7; revert v7_6; decide
  subst e
  have e : v7_2 = false := by clear * - c_t26_7; revert c_t26_7; revert v7_2; decide
  subst e
  have e : v7_1 = false := by clear * - c_t16_7; revert c_t16_7; revert v7_1; decide
  subst e
  have e : v7_5 = false := by clear * - c_t51_7; revert c_t51_7; revert v7_5; decide
  subst e
  have e : v8_6 = true := by clear * - c_d6_8; revert c_d6_8; revert v8_6; decide
  subst e
  have e : v8_1 = true := by clear * - c_t16_8; revert c_t16_8; revert v8_1; decide
  subst e
  have e : v9_6 = false := by clear * - c_d6_9; revert c_d6_9; revert v9_6; decide
  subst e
  have e : v9_2 = false := by clear * - c_t26_9; revert c_t26_9; revert v9_2; decide
  subst e
  have e : v9_1 = false := by clear * - c_t16_9; revert c_t16_9; revert v9_1; decide
  subst e
  have e : v9_5 = false := by clear * - c_t51_9; revert c_t51_9; revert v9_5; decide
  subst e
  have e : v10_6 = true := by clear * - c_d6_10; revert c_d6_10; revert v10_6; decide
  subst e
  have e : v10_1 = true := by clear * - c_t16_10; revert c_t16_10; revert v10_1; decide
  subst e
  have e : v11_6 = false := by clear * - c_d6_11; revert c_d6_11; revert v11_6; decide
  subst e
  have e : v11_2 = false := by clear * - c_t26_11; revert c_t26_11; revert v11_2; decide
  subst e
  have e : v11_1 = false := by clear * - c_t16_11; revert c_t16_11; revert v11_1; decide
  subst e
  have e : v11_5 = false := by clear * - c_t51_11; revert c_t51_11; revert v11_5; decide
  subst e
  have e : v12_6 = true := by clear * - c_d6_12; revert c_d6_12; revert v12_6; decide
  subst e
  have e : v12_1 = true := by clear * - c_t16_12; revert c_t16_12; revert v12_1; decide
  subst e
  have e : v13_6 = false := by clear * - c_d6_13; revert c_d6_13; revert v13_6; decide
  subst e
  have e : v13_2 = false := by clear * - c_t26_13; revert c_t26_13; revert v13_2; decide
  subst e
  have e : v13_1 = false := by clear * - c_t16_13; revert c_t16_13; revert v13_1; decide
  subst e
  have e : v13_5 = false := by clear * - c_t51_13; revert c_t51_13; revert v13_5; decide
  subst e
  have e : v14_6 = true := by clear * - c_d6_14; revert c_d6_14; revert v14_6; decide
  subst e
  have e : v14_1 = true := by clear * - c_t16_14; revert c_t16_14; revert v14_1; decide
  subst e
  have e : v15_6 = false := by clear * - c_d6_15; revert c_d6_15; revert v15_6; decide
  subst e
  have e : v15_2 = false := by clear * - c_t26_15; revert c_t26_15; revert v15_2; decide
  subst e
  have e : v15_1 = false := by clear * - c_t16_15; revert c_t16_15; revert v15_1; decide
  subst e
  have e : v15_5 = false := by clear * - c_t51_15; revert c_t51_15; revert v15_5; decide
  subst e
  have e : v16_6 = true := by clear * - c_d6_16; revert c_d6_16; revert v16_6; decide
  subst e
  have e : v16_1 = true := by clear * - c_t16_16; revert c_t16_16; revert v16_1; decide
  subst e
  cases v0_2
  · have e : vm4_5 = true := by clear * - c_cov1_1; revert c_cov1_1; revert vm4_5 vm3_4 vm2_4 vm1_3; decide
    subst e
    have e : vm3_4 = false := by clear * - c_d4_m3; revert c_d4_m3; revert vm3_4 vm6_3; decide
    subst e
    have e : v1_3 = true := by clear * - c_cov3_1; revert c_cov3_1; revert v1_3; decide
    subst e
    have e : vm2_4 = true := by clear * - c_cov3_2; revert c_cov3_2; revert vm2_4 vm1_3; decide
    subst e
    have e : vm1_3 = false := by clear * - c_count_2; revert c_count_2; revert vm1_3; decide
    subst e
    have e : v2_4 = true := by clear * - c_d4_2; revert c_d4_2; revert v2_4; decide
    subst e
    have e : v2_2 = false := by clear * - c_count_4; revert c_count_4; revert v2_2; decide
    subst e
    have e : v4_2 = true := by clear * - c_cov2_4; revert c_cov2_4; revert v3_3 v4_2; decide
    subst e
    clear * - c_count_6; revert c_count_6; revert v3_3; decide
  · have e : vm1_3 = false := by clear * - c_count_2; revert c_count_2; revert vm1_3 vm2_4; decide
    subst e
    have e : vm2_4 = false := by clear * - c_count_2; revert c_count_2; revert vm2_4; decide
    subst e
    have e : v2_2 = true := by clear * - c_cov2_2; revert c_cov2_2; revert v1_3 v2_2; decide
    subst e
    have e : v1_3 = false := by clear * - c_count_4; revert c_count_4; revert v1_3; decide
    subst e
    have e : vm3_4 = true := by clear * - c_cov3_1; revert c_cov3_1; revert vm3_4; decide
    subst e
    have e : vm4_5 = false := by clear * - c_d4_m3; revert c_d4_m3; revert vm4_5 vm6_3; decide
    subst e
    have e : vm6_2 = true := by clear * - c_cov5_m4; revert c_cov5_m4; revert vm6_2; decide
    subst e
    have e : vm7_3 = false := by clear * - c_count_m4; revert c_count_m4; revert vm7_3 vm8_4; decide
    subst e
    have e : vm8_4 = false := by clear * - c_count_m4; revert c_count_m4; revert vm8_4; decide
    subst e
    have e : vm6_3 = false := by clear * - c_d4_m3; revert c_d4_m3; revert vm6_3; decide
    subst e
    have e : vm6_4 = true := by clear * - c_cov3_m2; revert c_cov3_m2; revert vm6_4 vm5_3 vm4_2; decide
    subst e
    have e : vm8_2 = false := by clear * - c_d4_m6; revert c_d4_m6; revert vm8_2 vm9_3; decide
    subst e
    have e : vm9_3 = false := by clear * - c_d4_m6; revert c_d4_m6; revert vm9_3; decide
    subst e
    have e : vm10_4 = true := by clear * - c_count_m6; revert c_count_m6; revert vm10_4; decide
    subst e
    have e : vm4_2 = false := by clear * - c_count_m2; revert c_count_m2; revert vm4_2 vm5_3; decide
    subst e
    have e : vm8_5 = true := by clear * - c_cov1_m3; revert c_cov1_m3; revert vm8_5 vm7_4 vm5_3; decide
    subst e
    have e : vm7_4 = false := by clear * - c_d4_m7; revert c_d4_m7; revert vm7_4 vm10_3; decide
    subst e
    have e : vm10_3 = false := by clear * - c_d4_m7; revert c_d4_m7; revert vm10_3; decide
    subst e
    have e : vm12_5 = true := by clear * - c_cov1_m7; revert c_cov1_m7; revert vm12_5 vm11_4; decide
    subst e
    have e : vm11_4 = false := by clear * - c_d4_m11; revert c_d4_m11; revert vm11_4 vm14_3; decide
    subst e
    clear * - c_cov3_m7; revert c_cov3_m7; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_n4a (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = true) (H1 : y 0 4 = true) (H2 : y (-2) 2 = true) : False := by
  have c_count_0 := hcount 0 (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_0 := hd4 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_d6_m5 := hd6 (-5) (-6) (by norm_num)
  have c_t16_m1 := h16 (-1)
  have c_t16_m2 := h16 (-2)
  have c_t16_m3 := h16 (-3)
  have c_t16_m4 := h16 (-4)
  have c_t16_m5 := h16 (-5)
  have c_t16_m6 := h16 (-6)
  have c_t26_m2 := h26 (-2)
  have c_t51_m1 := h51 (-1)
  have c_t51_m5 := h51 (-5)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-6) 1 = vm6_1 at *
  generalize y (-6) 6 = vm6_6 at *
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 5 = vm5_5 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 4 = vm4_4 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 3 = vm3_3 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 2 = vm2_2 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 5 = vm1_5 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 4 = v0_4 at *
  subst H0
  subst H1
  subst H2
  have e : vm2_6 = true := by clear * - c_t26_m2; revert c_t26_m2; revert vm2_6; decide
  subst e
  have e : vm3_1 = false := by clear * - c_d6_m2; revert c_d6_m2; revert vm3_1; decide
  subst e
  have e : vm3_6 = false := by clear * - c_t16_m3; revert c_t16_m3; revert vm3_6; decide
  subst e
  have e : vm4_1 = true := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
  subst e
  have e : vm4_6 = true := by clear * - c_t16_m4; revert c_t16_m4; revert vm4_6; decide
  subst e
  have e : vm5_1 = false := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
  subst e
  have e : vm5_5 = false := by clear * - c_t51_m5; revert c_t51_m5; revert vm5_5; decide
  subst e
  have e : vm5_6 = false := by clear * - c_t16_m5; revert c_t16_m5; revert vm5_6; decide
  subst e
  have e : vm6_1 = true := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
  subst e
  have e : vm6_6 = true := by clear * - c_t16_m6; revert c_t16_m6; revert vm6_6; decide
  subst e
  have e : vm2_1 = true := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_1; decide
  subst e
  have e : vm1_6 = false := by clear * - c_d6_m1; revert c_d6_m1; revert vm1_6; decide
  subst e
  have e : vm1_1 = false := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_1; decide
  subst e
  have e : vm1_5 = false := by clear * - c_t51_m1; revert c_t51_m1; revert vm1_5; decide
  subst e
  have e : vm3_3 = false := by clear * - c_count_0; revert c_count_0; revert vm3_3 vm4_4; decide
  subst e
  clear * - c_d4_0; revert c_d4_0; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_n4b (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = true) (H1 : y 0 4 = false) (H2 : y (-2) 2 = false) : False := by
  have c_count_0 := hcount 0 (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_2 := hcount 2 1 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m2 := hcount (-2) (-3) (-4) (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_0 := cov2 0 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_m2 := cov2 (-2) (-3) (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_0 := hd4 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m2 := hd4 (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_0 := hd6 0 (-1) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_d6_m5 := hd6 (-5) (-6) (by norm_num)
  have c_d6_m6 := hd6 (-6) (-7) (by norm_num)
  have c_d6_m7 := hd6 (-7) (-8) (by norm_num)
  have c_t16_0 := h16 0
  have c_t16_1 := h16 1
  have c_t16_m1 := h16 (-1)
  have c_t16_m2 := h16 (-2)
  have c_t16_m3 := h16 (-3)
  have c_t16_m4 := h16 (-4)
  have c_t16_m5 := h16 (-5)
  have c_t16_m6 := h16 (-6)
  have c_t16_m7 := h16 (-7)
  have c_t16_m8 := h16 (-8)
  have c_t51_m1 := h51 (-1)
  have c_t51_m3 := h51 (-3)
  have c_t51_m5 := h51 (-5)
  have c_t51_m7 := h51 (-7)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-8) 1 = vm8_1 at *
  generalize y (-8) 6 = vm8_6 at *
  generalize y (-7) 1 = vm7_1 at *
  generalize y (-7) 5 = vm7_5 at *
  generalize y (-7) 6 = vm7_6 at *
  generalize y (-6) 1 = vm6_1 at *
  generalize y (-6) 4 = vm6_4 at *
  generalize y (-6) 6 = vm6_6 at *
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 3 = vm5_3 at *
  generalize y (-5) 5 = vm5_5 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 2 = vm4_2 at *
  generalize y (-4) 4 = vm4_4 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 3 = vm3_3 at *
  generalize y (-3) 5 = vm3_5 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 2 = vm2_2 at *
  generalize y (-2) 4 = vm2_4 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 3 = vm1_3 at *
  generalize y (-1) 5 = vm1_5 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 2 = v0_2 at *
  generalize y 0 4 = v0_4 at *
  generalize y 0 6 = v0_6 at *
  generalize y 1 1 = v1_1 at *
  generalize y 1 6 = v1_6 at *
  subst H0
  subst H1
  subst H2
  have e : v0_6 = true := by clear * - c_t16_0; revert c_t16_0; revert v0_6; decide
  subst e
  have e : vm1_1 = false := by clear * - c_d6_0; revert c_d6_0; revert vm1_1; decide
  subst e
  have e : vm1_5 = false := by clear * - c_t51_m1; revert c_t51_m1; revert vm1_5; decide
  subst e
  have e : vm1_6 = false := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_6; decide
  subst e
  have e : vm2_1 = true := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
  subst e
  have e : vm2_6 = true := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_6; decide
  subst e
  have e : vm3_1 = false := by clear * - c_d6_m2; revert c_d6_m2; revert vm3_1; decide
  subst e
  have e : vm3_5 = false := by clear * - c_t51_m3; revert c_t51_m3; revert vm3_5; decide
  subst e
  have e : vm3_6 = false := by clear * - c_t16_m3; revert c_t16_m3; revert vm3_6; decide
  subst e
  have e : vm4_1 = true := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
  subst e
  have e : vm4_6 = true := by clear * - c_t16_m4; revert c_t16_m4; revert vm4_6; decide
  subst e
  have e : vm5_1 = false := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
  subst e
  have e : vm5_5 = false := by clear * - c_t51_m5; revert c_t51_m5; revert vm5_5; decide
  subst e
  have e : vm5_6 = false := by clear * - c_t16_m5; revert c_t16_m5; revert vm5_6; decide
  subst e
  have e : vm6_1 = true := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
  subst e
  have e : vm6_6 = true := by clear * - c_t16_m6; revert c_t16_m6; revert vm6_6; decide
  subst e
  have e : vm7_1 = false := by clear * - c_d6_m6; revert c_d6_m6; revert vm7_1; decide
  subst e
  have e : vm7_5 = false := by clear * - c_t51_m7; revert c_t51_m7; revert vm7_5; decide
  subst e
  have e : vm7_6 = false := by clear * - c_t16_m7; revert c_t16_m7; revert vm7_6; decide
  subst e
  have e : vm8_1 = true := by clear * - c_d6_m7; revert c_d6_m7; revert vm8_1; decide
  subst e
  have e : vm8_6 = true := by clear * - c_t16_m8; revert c_t16_m8; revert vm8_6; decide
  subst e
  have e : vm3_3 = true := by clear * - c_d4_0; revert c_d4_0; revert vm3_3; decide
  subst e
  have e : vm4_4 = false := by clear * - c_count_0; revert c_count_0; revert vm4_4; decide
  subst e
  have e : vm6_4 = true := by clear * - c_cov2_m2; revert c_cov2_m2; revert vm6_4 vm5_3 vm4_2; decide
  subst e
  have e : vm4_2 = false := by clear * - c_count_m2; revert c_count_m2; revert vm4_2 vm5_3; decide
  subst e
  have e : vm5_3 = false := by clear * - c_count_m2; revert c_count_m2; revert vm5_3; decide
  subst e
  have e : vm2_4 = true := by clear * - c_d4_m2; revert c_d4_m2; revert vm2_4; decide
  subst e
  have e : v0_2 = true := by clear * - c_cov2_0; revert c_cov2_0; revert vm1_3 v0_2; decide
  subst e
  have e : v1_6 = false := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
  subst e
  have e : v1_1 = false := by clear * - c_t16_1; revert c_t16_1; revert v1_1; decide
  subst e
  clear * - c_count_2; revert c_count_2; revert vm1_3; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_n2a (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = true) (H1 : y 0 2 = true) (H2 : y (-4) 2 = false) : False := by
  have c_count_2 := hcount 2 1 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m2 := hcount (-2) (-3) (-4) (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m4 := hcount (-4) (-5) (-6) (-7) (-8) (-9) (-10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m6 := hcount (-6) (-7) (-8) (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m8 := hcount (-8) (-9) (-10) (-11) (-12) (-13) (-14) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_m5 := cov1 (-5) (-6) (-7) (-8) (-9) (-10) (-11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov1_m9 := cov1 (-9) (-10) (-11) (-12) (-13) (-14) (-15) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_m4 := cov2 (-4) (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m1 := cov3 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m9 := cov3 (-9) (-10) (-11) (-12) (-13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov5_m2 := cov5 (-2) (-3) (-4) (by norm_num) (by norm_num)
  have c_cov5_m6 := cov5 (-6) (-7) (-8) (by norm_num) (by norm_num)
  have c_d4_m1 := hd4 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m13 := hd4 (-13) (-14) (-15) (-16) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m2 := hd4 (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m5 := hd4 (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m8 := hd4 (-8) (-9) (-10) (-11) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m9 := hd4 (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_0 := hd6 0 (-1) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m10 := hd6 (-10) (-11) (by norm_num)
  have c_d6_m11 := hd6 (-11) (-12) (by norm_num)
  have c_d6_m12 := hd6 (-12) (-13) (by norm_num)
  have c_d6_m13 := hd6 (-13) (-14) (by norm_num)
  have c_d6_m14 := hd6 (-14) (-15) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_d6_m5 := hd6 (-5) (-6) (by norm_num)
  have c_d6_m6 := hd6 (-6) (-7) (by norm_num)
  have c_d6_m7 := hd6 (-7) (-8) (by norm_num)
  have c_d6_m8 := hd6 (-8) (-9) (by norm_num)
  have c_d6_m9 := hd6 (-9) (-10) (by norm_num)
  have c_t16_1 := h16 1
  have c_t16_m1 := h16 (-1)
  have c_t16_m10 := h16 (-10)
  have c_t16_m11 := h16 (-11)
  have c_t16_m12 := h16 (-12)
  have c_t16_m13 := h16 (-13)
  have c_t16_m14 := h16 (-14)
  have c_t16_m15 := h16 (-15)
  have c_t16_m2 := h16 (-2)
  have c_t16_m3 := h16 (-3)
  have c_t16_m4 := h16 (-4)
  have c_t16_m5 := h16 (-5)
  have c_t16_m6 := h16 (-6)
  have c_t16_m7 := h16 (-7)
  have c_t16_m8 := h16 (-8)
  have c_t16_m9 := h16 (-9)
  have c_t26_0 := h26 0
  have c_t26_m11 := h26 (-11)
  have c_t26_m15 := h26 (-15)
  have c_t26_m3 := h26 (-3)
  have c_t26_m7 := h26 (-7)
  have c_t51_m11 := h51 (-11)
  have c_t51_m13 := h51 (-13)
  have c_t51_m3 := h51 (-3)
  have c_t51_m7 := h51 (-7)
  have c_t51_m9 := h51 (-9)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-16) 3 = vm16_3 at *
  generalize y (-15) 1 = vm15_1 at *
  generalize y (-15) 2 = vm15_2 at *
  generalize y (-15) 6 = vm15_6 at *
  generalize y (-14) 1 = vm14_1 at *
  generalize y (-14) 5 = vm14_5 at *
  generalize y (-14) 6 = vm14_6 at *
  generalize y (-13) 1 = vm13_1 at *
  generalize y (-13) 4 = vm13_4 at *
  generalize y (-13) 5 = vm13_5 at *
  generalize y (-13) 6 = vm13_6 at *
  generalize y (-12) 1 = vm12_1 at *
  generalize y (-12) 3 = vm12_3 at *
  generalize y (-12) 4 = vm12_4 at *
  generalize y (-12) 6 = vm12_6 at *
  generalize y (-11) 1 = vm11_1 at *
  generalize y (-11) 2 = vm11_2 at *
  generalize y (-11) 3 = vm11_3 at *
  generalize y (-11) 5 = vm11_5 at *
  generalize y (-11) 6 = vm11_6 at *
  generalize y (-10) 1 = vm10_1 at *
  generalize y (-10) 2 = vm10_2 at *
  generalize y (-10) 4 = vm10_4 at *
  generalize y (-10) 5 = vm10_5 at *
  generalize y (-10) 6 = vm10_6 at *
  generalize y (-9) 1 = vm9_1 at *
  generalize y (-9) 3 = vm9_3 at *
  generalize y (-9) 4 = vm9_4 at *
  generalize y (-9) 5 = vm9_5 at *
  generalize y (-9) 6 = vm9_6 at *
  generalize y (-8) 1 = vm8_1 at *
  generalize y (-8) 2 = vm8_2 at *
  generalize y (-8) 3 = vm8_3 at *
  generalize y (-8) 4 = vm8_4 at *
  generalize y (-8) 6 = vm8_6 at *
  generalize y (-7) 1 = vm7_1 at *
  generalize y (-7) 2 = vm7_2 at *
  generalize y (-7) 3 = vm7_3 at *
  generalize y (-7) 5 = vm7_5 at *
  generalize y (-7) 6 = vm7_6 at *
  generalize y (-6) 1 = vm6_1 at *
  generalize y (-6) 2 = vm6_2 at *
  generalize y (-6) 4 = vm6_4 at *
  generalize y (-6) 5 = vm6_5 at *
  generalize y (-6) 6 = vm6_6 at *
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 3 = vm5_3 at *
  generalize y (-5) 4 = vm5_4 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 2 = vm4_2 at *
  generalize y (-4) 3 = vm4_3 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 2 = vm3_2 at *
  generalize y (-3) 5 = vm3_5 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 4 = vm2_4 at *
  generalize y (-2) 5 = vm2_5 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 3 = vm1_3 at *
  generalize y (-1) 4 = vm1_4 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 2 = v0_2 at *
  generalize y 0 6 = v0_6 at *
  generalize y 1 1 = v1_1 at *
  generalize y 1 6 = v1_6 at *
  subst H0
  subst H1
  subst H2
  have e : v0_6 = true := by clear * - c_t26_0; revert c_t26_0; revert v0_6; decide
  subst e
  have e : vm1_1 = false := by clear * - c_d6_0; revert c_d6_0; revert vm1_1; decide
  subst e
  have e : vm1_6 = false := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_6; decide
  subst e
  have e : vm2_1 = true := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
  subst e
  have e : vm2_6 = true := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_6; decide
  subst e
  have e : vm3_1 = false := by clear * - c_d6_m2; revert c_d6_m2; revert vm3_1; decide
  subst e
  have e : vm3_5 = false := by clear * - c_t51_m3; revert c_t51_m3; revert vm3_5; decide
  subst e
  have e : vm3_6 = false := by clear * - c_t16_m3; revert c_t16_m3; revert vm3_6; decide
  subst e
  have e : vm4_1 = true := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
  subst e
  have e : vm4_6 = true := by clear * - c_t16_m4; revert c_t16_m4; revert vm4_6; decide
  subst e
  have e : vm5_1 = false := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
  subst e
  have e : vm5_6 = false := by clear * - c_t16_m5; revert c_t16_m5; revert vm5_6; decide
  subst e
  have e : vm6_1 = true := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
  subst e
  have e : vm6_6 = true := by clear * - c_t16_m6; revert c_t16_m6; revert vm6_6; decide
  subst e
  have e : vm7_1 = false := by clear * - c_d6_m6; revert c_d6_m6; revert vm7_1; decide
  subst e
  have e : vm7_5 = false := by clear * - c_t51_m7; revert c_t51_m7; revert vm7_5; decide
  subst e
  have e : vm7_6 = false := by clear * - c_t16_m7; revert c_t16_m7; revert vm7_6; decide
  subst e
  have e : vm8_1 = true := by clear * - c_d6_m7; revert c_d6_m7; revert vm8_1; decide
  subst e
  have e : vm8_6 = true := by clear * - c_t16_m8; revert c_t16_m8; revert vm8_6; decide
  subst e
  have e : vm9_1 = false := by clear * - c_d6_m8; revert c_d6_m8; revert vm9_1; decide
  subst e
  have e : vm9_5 = false := by clear * - c_t51_m9; revert c_t51_m9; revert vm9_5; decide
  subst e
  have e : vm9_6 = false := by clear * - c_t16_m9; revert c_t16_m9; revert vm9_6; decide
  subst e
  have e : vm10_1 = true := by clear * - c_d6_m9; revert c_d6_m9; revert vm10_1; decide
  subst e
  have e : vm10_6 = true := by clear * - c_t16_m10; revert c_t16_m10; revert vm10_6; decide
  subst e
  have e : vm11_1 = false := by clear * - c_d6_m10; revert c_d6_m10; revert vm11_1; decide
  subst e
  have e : vm11_5 = false := by clear * - c_t51_m11; revert c_t51_m11; revert vm11_5; decide
  subst e
  have e : vm11_6 = false := by clear * - c_t16_m11; revert c_t16_m11; revert vm11_6; decide
  subst e
  have e : vm12_1 = true := by clear * - c_d6_m11; revert c_d6_m11; revert vm12_1; decide
  subst e
  have e : vm12_6 = true := by clear * - c_t16_m12; revert c_t16_m12; revert vm12_6; decide
  subst e
  have e : vm13_1 = false := by clear * - c_d6_m12; revert c_d6_m12; revert vm13_1; decide
  subst e
  have e : vm13_5 = false := by clear * - c_t51_m13; revert c_t51_m13; revert vm13_5; decide
  subst e
  have e : vm13_6 = false := by clear * - c_t16_m13; revert c_t16_m13; revert vm13_6; decide
  subst e
  have e : vm14_1 = true := by clear * - c_d6_m13; revert c_d6_m13; revert vm14_1; decide
  subst e
  have e : vm14_6 = true := by clear * - c_t16_m14; revert c_t16_m14; revert vm14_6; decide
  subst e
  have e : vm15_1 = false := by clear * - c_d6_m14; revert c_d6_m14; revert vm15_1; decide
  subst e
  have e : vm15_6 = false := by clear * - c_t16_m15; revert c_t16_m15; revert vm15_6; decide
  subst e
  have e : vm15_2 = false := by clear * - c_t26_m15; revert c_t26_m15; revert vm15_2; decide
  subst e
  have e : vm11_2 = false := by clear * - c_t26_m11; revert c_t26_m11; revert vm11_2; decide
  subst e
  have e : vm7_2 = false := by clear * - c_t26_m7; revert c_t26_m7; revert vm7_2; decide
  subst e
  have e : vm3_2 = false := by clear * - c_t26_m3; revert c_t26_m3; revert vm3_2; decide
  subst e
  have e : vm2_5 = true := by clear * - c_cov5_m2; revert c_cov5_m2; revert vm2_5; decide
  subst e
  have e : vm1_4 = false := by clear * - c_d4_m1; revert c_d4_m1; revert vm1_4 vm4_3; decide
  subst e
  have e : vm4_3 = false := by clear * - c_d4_m1; revert c_d4_m1; revert vm4_3; decide
  subst e
  have e : v1_6 = false := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
  subst e
  have e : v1_1 = false := by clear * - c_t16_1; revert c_t16_1; revert v1_1; decide
  subst e
  have e : vm1_3 = false := by clear * - c_count_2; revert c_count_2; revert vm1_3 vm2_4; decide
  subst e
  have e : vm2_4 = false := by clear * - c_count_2; revert c_count_2; revert vm2_4; decide
  subst e
  have e : vm5_3 = true := by clear * - c_d4_m2; revert c_d4_m2; revert vm5_3; decide
  subst e
  have e : vm6_4 = false := by clear * - c_count_m2; revert c_count_m2; revert vm6_4; decide
  subst e
  have e : vm8_4 = true := by clear * - c_cov2_m4; revert c_cov2_m4; revert vm8_4 vm7_3 vm6_2; decide
  subst e
  have e : vm10_2 = false := by clear * - c_d4_m8; revert c_d4_m8; revert vm10_2 vm11_3; decide
  subst e
  have e : vm11_3 = false := by clear * - c_d4_m8; revert c_d4_m8; revert vm11_3; decide
  subst e
  have e : vm12_4 = true := by clear * - c_count_m8; revert c_count_m8; revert vm12_4; decide
  subst e
  have e : vm6_2 = false := by clear * - c_count_m4; revert c_count_m4; revert vm6_2 vm7_3; decide
  subst e
  have e : vm7_3 = false := by clear * - c_count_m4; revert c_count_m4; revert vm7_3; decide
  subst e
  have e : vm5_4 = true := by clear * - c_cov3_m1; revert c_cov3_m1; revert vm5_4; decide
  subst e
  have e : vm6_5 = false := by clear * - c_d4_m5; revert c_d4_m5; revert vm6_5 vm8_3; decide
  subst e
  have e : vm8_2 = true := by clear * - c_cov5_m6; revert c_cov5_m6; revert vm8_2; decide
  subst e
  have e : vm9_3 = false := by clear * - c_count_m6; revert c_count_m6; revert vm9_3 vm10_4; decide
  subst e
  have e : vm10_4 = false := by clear * - c_count_m6; revert c_count_m6; revert vm10_4; decide
  subst e
  have e : vm8_3 = false := by clear * - c_d4_m5; revert c_d4_m5; revert vm8_3; decide
  subst e
  have e : vm10_5 = true := by clear * - c_cov1_m5; revert c_cov1_m5; revert vm10_5 vm9_4; decide
  subst e
  have e : vm9_4 = false := by clear * - c_d4_m9; revert c_d4_m9; revert vm9_4 vm12_3; decide
  subst e
  have e : vm12_3 = false := by clear * - c_d4_m9; revert c_d4_m9; revert vm12_3; decide
  subst e
  have e : vm14_5 = true := by clear * - c_cov1_m9; revert c_cov1_m9; revert vm14_5 vm13_4; decide
  subst e
  have e : vm13_4 = false := by clear * - c_d4_m13; revert c_d4_m13; revert vm13_4 vm16_3; decide
  subst e
  clear * - c_cov3_m9; revert c_cov3_m9; decide

set_option maxHeartbeats 4000000 in
theorem cycle_power_seven_tight_type_core_n2b (y : ℤ → Fin 8 → Bool)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true)
    (cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true)
    (cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true)
    (cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 → (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true)
    (h16 : ∀ a, y a 1 = y a 6)
    (H0 : y 0 1 = true) (H1 : y 0 2 = false) (H2 : y (-4) 2 = true) : False := by
  have c_count_0 := hcount 0 (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_2 := hcount 2 1 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_4 := hcount 4 3 2 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m2 := hcount (-2) (-3) (-4) (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_0 := cov2 0 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_2 := cov2 2 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov5_2 := cov5 2 1 0 (by norm_num) (by norm_num)
  have c_d4_0 := hd4 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m2 := hd4 (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_d6_3 := hd6 3 2 (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_d6_m5 := hd6 (-5) (-6) (by norm_num)
  have c_d6_m6 := hd6 (-6) (-7) (by norm_num)
  have c_d6_m7 := hd6 (-7) (-8) (by norm_num)
  have c_t16_1 := h16 1
  have c_t16_3 := h16 3
  have c_t16_m1 := h16 (-1)
  have c_t16_m2 := h16 (-2)
  have c_t16_m3 := h16 (-3)
  have c_t16_m4 := h16 (-4)
  have c_t16_m5 := h16 (-5)
  have c_t16_m6 := h16 (-6)
  have c_t16_m7 := h16 (-7)
  have c_t16_m8 := h16 (-8)
  have c_t26_m4 := h26 (-4)
  have c_t51_2 := h51 2
  have c_t51_m1 := h51 (-1)
  have c_t51_m3 := h51 (-3)
  have c_t51_m5 := h51 (-5)
  have c_t51_m7 := h51 (-7)
  clear hcount hd4 hd6 h51 h26 h16 cov1 cov2 cov3 cov5
  generalize y (-8) 1 = vm8_1 at *
  generalize y (-8) 6 = vm8_6 at *
  generalize y (-7) 1 = vm7_1 at *
  generalize y (-7) 5 = vm7_5 at *
  generalize y (-7) 6 = vm7_6 at *
  generalize y (-6) 1 = vm6_1 at *
  generalize y (-6) 4 = vm6_4 at *
  generalize y (-6) 6 = vm6_6 at *
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 3 = vm5_3 at *
  generalize y (-5) 5 = vm5_5 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 2 = vm4_2 at *
  generalize y (-4) 4 = vm4_4 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 3 = vm3_3 at *
  generalize y (-3) 5 = vm3_5 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 2 = vm2_2 at *
  generalize y (-2) 4 = vm2_4 at *
  generalize y (-2) 6 = vm2_6 at *
  generalize y (-1) 1 = vm1_1 at *
  generalize y (-1) 3 = vm1_3 at *
  generalize y (-1) 5 = vm1_5 at *
  generalize y (-1) 6 = vm1_6 at *
  generalize y 0 1 = v0_1 at *
  generalize y 0 2 = v0_2 at *
  generalize y 0 4 = v0_4 at *
  generalize y 1 1 = v1_1 at *
  generalize y 1 3 = v1_3 at *
  generalize y 1 6 = v1_6 at *
  generalize y 2 1 = v2_1 at *
  generalize y 2 2 = v2_2 at *
  generalize y 2 5 = v2_5 at *
  generalize y 3 1 = v3_1 at *
  generalize y 3 6 = v3_6 at *
  subst H0
  subst H1
  subst H2
  have e : vm4_6 = true := by clear * - c_t26_m4; revert c_t26_m4; revert vm4_6; decide
  subst e
  have e : vm5_1 = false := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
  subst e
  have e : vm5_5 = false := by clear * - c_t51_m5; revert c_t51_m5; revert vm5_5; decide
  subst e
  have e : vm5_6 = false := by clear * - c_t16_m5; revert c_t16_m5; revert vm5_6; decide
  subst e
  have e : vm6_1 = true := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
  subst e
  have e : vm6_6 = true := by clear * - c_t16_m6; revert c_t16_m6; revert vm6_6; decide
  subst e
  have e : vm7_1 = false := by clear * - c_d6_m6; revert c_d6_m6; revert vm7_1; decide
  subst e
  have e : vm7_5 = false := by clear * - c_t51_m7; revert c_t51_m7; revert vm7_5; decide
  subst e
  have e : vm7_6 = false := by clear * - c_t16_m7; revert c_t16_m7; revert vm7_6; decide
  subst e
  have e : vm8_1 = true := by clear * - c_d6_m7; revert c_d6_m7; revert vm8_1; decide
  subst e
  have e : vm8_6 = true := by clear * - c_t16_m8; revert c_t16_m8; revert vm8_6; decide
  subst e
  have e : vm4_1 = true := by clear * - c_t16_m4; revert c_t16_m4; revert vm4_1; decide
  subst e
  have e : vm3_6 = false := by clear * - c_d6_m3; revert c_d6_m3; revert vm3_6; decide
  subst e
  have e : vm3_1 = false := by clear * - c_t16_m3; revert c_t16_m3; revert vm3_1; decide
  subst e
  have e : vm3_5 = false := by clear * - c_t51_m3; revert c_t51_m3; revert vm3_5; decide
  subst e
  have e : vm5_3 = false := by clear * - c_count_m2; revert c_count_m2; revert vm5_3 vm6_4; decide
  subst e
  have e : vm2_4 = false := by clear * - c_d4_m2; revert c_d4_m2; revert vm2_4; decide
  subst e
  have e : vm2_6 = true := by clear * - c_d6_m2; revert c_d6_m2; revert vm2_6; decide
  subst e
  have e : vm2_1 = true := by clear * - c_t16_m2; revert c_t16_m2; revert vm2_1; decide
  subst e
  have e : vm1_6 = false := by clear * - c_d6_m1; revert c_d6_m1; revert vm1_6; decide
  subst e
  have e : vm1_1 = false := by clear * - c_t16_m1; revert c_t16_m1; revert vm1_1; decide
  subst e
  have e : vm1_5 = false := by clear * - c_t51_m1; revert c_t51_m1; revert vm1_5; decide
  subst e
  have e : vm4_4 = true := by clear * - c_cov2_0; revert c_cov2_0; revert vm4_4 vm3_3 vm2_2 vm1_3; decide
  subst e
  have e : vm2_2 = false := by clear * - c_count_0; revert c_count_0; revert vm2_2 vm3_3; decide
  subst e
  have e : vm3_3 = false := by clear * - c_count_0; revert c_count_0; revert vm3_3; decide
  subst e
  have e : v0_4 = true := by clear * - c_d4_0; revert c_d4_0; revert v0_4; decide
  subst e
  have e : v1_6 = false := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
  subst e
  have e : v1_1 = false := by clear * - c_t16_1; revert c_t16_1; revert v1_1; decide
  subst e
  have e : vm1_3 = true := by clear * - c_count_2; revert c_count_2; revert vm1_3; decide
  subst e
  have e : v2_2 = true := by clear * - c_cov2_2; revert c_cov2_2; revert v1_3 v2_2; decide
  subst e
  have e : v2_5 = true := by clear * - c_cov5_2; revert c_cov5_2; revert v2_5; decide
  subst e
  have e : v2_1 = true := by clear * - c_t51_2; revert c_t51_2; revert v2_1; decide
  subst e
  have e : v3_6 = false := by clear * - c_d6_3; revert c_d6_3; revert v3_6; decide
  subst e
  have e : v3_1 = false := by clear * - c_t16_3; revert c_t16_3; revert v3_1; decide
  subst e
  clear * - c_count_4; revert c_count_4; revert v1_3; decide

theorem cycle_power_seven_tight_type_sequence_types (n : ℕ) [NeZero n]
    (x : ZMod n → Fin 8 → Bool)
    (hcount : ∀ u, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat +
      (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat = 2)
    (hd4 : ∀ u, (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat +
      (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3).toNat = 1)
    (hd6 : ∀ u, (x (u - 1) 1).toNat + (x u 6).toNat = 1)
    (hcov : ∀ (d : ℕ) (u : ZMod n), d ∈ ({1, 2, 3, 5} : Finset ℕ) →
      ∃ j : Fin 8, ∃ hj : j.val + d ≤ 7, x (u - j.val) j = true ∧
        x (u - j.val) ⟨j.val + d, by omega⟩ = true)
    (h51 : ∀ p, x p 5 = true → x p 1 = true) (h26 : ∀ p, x p 2 = true → x p 6 = true)
    (h16 : ∀ p, x p 1 = x p 6) (p : ZMod n) :
    x (p + 1) 1 = !x p 1 ∧
      (x p 1 = false → x p 2 = false ∧ x p 3 = false ∧ x p 4 = false ∧ x p 5 = false) ∧
      (x p 1 = true → x p 3 = x p 2 ∧ x p 5 = x p 4 ∧ x p 4 = !x (p - 2) 2 ∧
        x p 2 = x (p - 4) 2) := by
  have Hc : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 →
      (x (p + (a1 : ZMod n)) 1).toNat + (x (p + (a2 : ZMod n)) 2).toNat +
        (x (p + (a3 : ZMod n)) 3).toNat + (x (p + (a4 : ZMod n)) 4).toNat +
        (x (p + (a5 : ZMod n)) 5).toNat + (x (p + (a6 : ZMod n)) 6).toNat = 2 := by
    rintro o _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    have h := hcount (p + (o : ZMod n))
    simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_one]
    simpa only [add_sub_assoc] using h
  have Hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (x (p + (o : ZMod n)) 4).toNat + (x (p + (a1 : ZMod n)) 1 && x (p + (a1 : ZMod n)) 5).toNat +
        (x (p + (a2 : ZMod n)) 2 && x (p + (a2 : ZMod n)) 6).toNat +
        (x (p + (a3 : ZMod n)) 3).toNat = 1 := by
    rintro o _ _ _ rfl rfl rfl
    have h := hd4 (p + (o : ZMod n))
    simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_one]
    simpa only [add_sub_assoc] using h
  have Hd6 : ∀ o a1 : ℤ, a1 = o - 1 →
      (x (p + (a1 : ZMod n)) 1).toNat + (x (p + (o : ZMod n)) 6).toNat = 1 := by
    rintro o _ rfl
    have h := hd6 (p + (o : ZMod n))
    simp only [Int.cast_sub, Int.cast_one]
    simpa only [add_sub_assoc] using h
  have Hcov : ∀ (d : ℕ) (o : ℤ), d ∈ ({1, 2, 3, 5} : Finset ℕ) →
      ∃ j : Fin 8, ∃ hj : j.val + d ≤ 7, x (p + ((o - j.val : ℤ) : ZMod n)) j = true ∧
        x (p + ((o - j.val : ℤ) : ZMod n)) ⟨j.val + d, by omega⟩ = true := by
    intro d o hd
    obtain ⟨j, hj, h1, h2⟩ := hcov d (p + (o : ZMod n)) hd
    refine ⟨j, hj, ?_, ?_⟩
    · simp only [Int.cast_sub, Int.cast_natCast]
      simpa only [add_sub_assoc] using h1
    · simp only [Int.cast_sub, Int.cast_natCast]
      simpa only [add_sub_assoc] using h2
  obtain ⟨C1, C2, C3, C5⟩ := cycle_power_seven_tight_type_cov_forms (fun a j => x (p + (a : ZMod n)) j) Hcov
  have y0 : ∀ j, x (p + ((0 : ℤ) : ZMod n)) j = x p j := by intro j; simp
  have ym2 : x (p + ((-2 : ℤ) : ZMod n)) 2 = x (p - 2) 2 := by
    congr 1; push_cast; ring
  have ym4 : x (p + ((-4 : ℤ) : ZMod n)) 2 = x (p - 4) 2 := by
    congr 1; push_cast; ring
  have e0 : ∀ j b, x p j = b → x (p + ((0 : ℤ) : ZMod n)) j = b := fun j b h => by rw [y0]; exact h
  have e2 : ∀ b, x (p - 2) 2 = b → x (p + ((-2 : ℤ) : ZMod n)) 2 = b := fun b h => by rw [ym2]; exact h
  have e4 : ∀ b, x (p - 4) 2 = b → x (p + ((-4 : ℤ) : ZMod n)) 2 = b := fun b h => by rw [ym4]; exact h
  have alt : x (p + 1) 1 = !x p 1 := by
    have h := hd6 (p + 1)
    rw [add_sub_cancel_right, ← h16 (p + 1)] at h
    revert h; cases x p 1 <;> cases x (p + 1) 1 <;> decide
  refine ⟨alt, fun hP => ⟨?_, ?_, ?_, ?_⟩, fun hN => ⟨?_, ?_, ?_, ?_⟩⟩
  · cases h : x p 2
    · rfl
    · exact (cycle_power_seven_tight_type_core_p2 (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hP) (e0 _ _ h)).elim
  · cases h : x p 3
    · rfl
    · exact (cycle_power_seven_tight_type_core_p3 (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hP) (e0 _ _ h)).elim
  · cases h : x p 4
    · rfl
    · exact (cycle_power_seven_tight_type_core_p4 (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hP) (e0 _ _ h)).elim
  · cases h : x p 5
    · rfl
    · exact (cycle_power_seven_tight_type_core_p5 (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hP) (e0 _ _ h)).elim
  · cases ha : x p 2 <;> cases hb : x p 3
    · rfl
    · exact (cycle_power_seven_tight_type_core_n23b (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hN) (e0 _ _ ha) (e0 _ _ hb)).elim
    · exact (cycle_power_seven_tight_type_core_n23a (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hN) (e0 _ _ ha) (e0 _ _ hb)).elim
    · rfl
  · cases ha : x p 4 <;> cases hb : x p 5
    · rfl
    · exact (cycle_power_seven_tight_type_core_n45b (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hN) (e0 _ _ ha) (e0 _ _ hb)).elim
    · exact (cycle_power_seven_tight_type_core_n45a (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hN) (e0 _ _ ha) (e0 _ _ hb)).elim
    · rfl
  · cases ha : x p 4 <;> cases hb : x (p - 2) 2
    · exact (cycle_power_seven_tight_type_core_n4b (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hN) (e0 _ _ ha) (e2 _ hb)).elim
    · rfl
    · rfl
    · exact (cycle_power_seven_tight_type_core_n4a (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hN) (e0 _ _ ha) (e2 _ hb)).elim
  · cases ha : x p 2 <;> cases hb : x (p - 4) 2
    · rfl
    · exact (cycle_power_seven_tight_type_core_n2b (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hN) (e0 _ _ ha) (e4 _ hb)).elim
    · exact (cycle_power_seven_tight_type_core_n2a (fun a j => x (p + (a : ZMod n)) j) Hc Hd4 Hd6 C1 C2 C3 C5 (fun a => h51 _) (fun a => h26 _) (fun a => h16 _) (e0 _ _ hN) (e0 _ _ ha) (e4 _ hb)).elim
    · rfl
