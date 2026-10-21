import AFTD.Prelude

/-!
# cycle_power_seven_tight_type_sequence_one_iff_six

Topic: graphs   Node: 3ab8ad577477

Provenance: helper lemma. step for simple_graph_cycle_power_seven_cover_four_tight_dvd (research thread RT-1, open case k = 7 of OP-205, arXiv:2610.15635)

Layer-free form of h16. Let x p j say that the class starting at p (the class of the distance-7 pair (p, p+7)) contains p + j. If, around the cycle: every vertex is an inner element (offsets 1..6) of exactly two such classes; every distance-4 and distance-6 pair is covered exactly once; every pair at distance 1, 2, 3, 5 is covered; and every class satisfies 5 ∈ T → 1 ∈ T and 2 ∈ T → 6 ∈ T (the classes of weight |T|); then every class contains p+1 exactly when it contains p+6.
-/

set_option maxHeartbeats 10000000 in
theorem cycle_power_seven_tight_type_sequence_core (y : ℤ → Fin 8 → Bool) (h0 : ∀ a, y a 0 = true) (h7 : ∀ a, y a 7 = true)
    (hcount : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      a5 = o - 5 → a6 = o - 6 → (y a1 1).toNat + (y a2 2).toNat + (y a3 3).toNat +
        (y a4 4).toNat + (y a5 5).toNat + (y a6 6).toNat = 2)
    (hd4 : ∀ o a1 a2 a3 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 →
      (y o 4).toNat + (y a1 1 && y a1 5).toNat + (y a2 2 && y a2 6).toNat + (y a3 3).toNat = 1)
    (hd6 : ∀ o a1 : ℤ, a1 = o - 1 → (y a1 1).toNat + (y o 6).toNat = 1)
    (hcov : ∀ (d : ℕ) (o : ℤ), d ∈ ({1, 2, 3, 5} : Finset ℕ) →
      ∃ j : Fin 8, ∃ hj : j.val + d ≤ 7, y (o - j.val) j = true ∧
        y (o - j.val) ⟨j.val + d, by omega⟩ = true)
    (h51 : ∀ a, y a 5 = true → y a 1 = true) (h26 : ∀ a, y a 2 = true → y a 6 = true) :
    y 0 1 = y 0 6 := by
  have cov1 : ∀ o a1 a2 a3 a4 a5 a6 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 → a6 = o - 6 →
      (y o 1 || (y a1 1 && y a1 2) || (y a2 2 && y a2 3) || (y a3 3 && y a3 4) || (y a4 4 && y a4 5) || (y a5 5 && y a5 6) || y a6 6) = true := by
    rintro o _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    obtain ⟨j, hj, h1, h2⟩ := hcov 1 o (by decide)
    clear hcov hcount hd4 hd6 h51 h26
    fin_cases j <;> (try simp at hj) <;> simp_all
  have cov2 : ∀ o a1 a2 a3 a4 a5 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 → a5 = o - 5 →
      (y o 2 || (y a1 1 && y a1 3) || (y a2 2 && y a2 4) || (y a3 3 && y a3 5) || (y a4 4 && y a4 6) || y a5 5) = true := by
    rintro o _ _ _ _ _ rfl rfl rfl rfl rfl
    obtain ⟨j, hj, h1, h2⟩ := hcov 2 o (by decide)
    clear hcov hcount hd4 hd6 h51 h26
    fin_cases j <;> (try simp at hj) <;> simp_all
  have cov3 : ∀ o a1 a2 a3 a4 : ℤ, a1 = o - 1 → a2 = o - 2 → a3 = o - 3 → a4 = o - 4 →
      (y o 3 || (y a1 1 && y a1 4) || (y a2 2 && y a2 5) || (y a3 3 && y a3 6) || y a4 4) = true := by
    rintro o _ _ _ _ rfl rfl rfl rfl
    obtain ⟨j, hj, h1, h2⟩ := hcov 3 o (by decide)
    clear hcov hcount hd4 hd6 h51 h26
    fin_cases j <;> (try simp at hj) <;> simp_all
  have cov5 : ∀ o a1 a2 : ℤ, a1 = o - 1 → a2 = o - 2 →
      (y o 5 || (y a1 1 && y a1 6) || y a2 2) = true := by
    rintro o _ _ rfl rfl
    obtain ⟨j, hj, h1, h2⟩ := hcov 5 o (by decide)
    clear hcov hcount hd4 hd6 h51 h26
    fin_cases j <;> (try simp at hj) <;> simp_all
  have c_count_m1 := hcount (-1) (-2) (-3) (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m3 := hcount (-3) (-4) (-5) (-6) (-7) (-8) (-9) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m4 := hcount (-4) (-5) (-6) (-7) (-8) (-9) (-10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m5 := hcount (-5) (-6) (-7) (-8) (-9) (-10) (-11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m8 := hcount (-8) (-9) (-10) (-11) (-12) (-13) (-14) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_m9 := hcount (-9) (-10) (-11) (-12) (-13) (-14) (-15) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_0 := hcount 0 (-1) (-2) (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_1 := hcount 1 0 (-1) (-2) (-3) (-4) (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_10 := hcount 10 9 8 7 6 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_3 := hcount 3 2 1 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_4 := hcount 4 3 2 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_5 := hcount 5 4 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_6 := hcount 6 5 4 3 2 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_7 := hcount 7 6 5 4 3 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_count_9 := hcount 9 8 7 6 5 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_1 := cov2 1 0 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_4 := cov2 4 3 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov2_5 := cov2 5 4 3 2 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m4 := cov3 (-4) (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_m8 := cov3 (-8) (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_6 := cov3 6 5 4 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov3_7 := cov3 7 6 5 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_cov5_m1 := cov5 (-1) (-2) (-3) (by norm_num) (by norm_num)
  have c_cov5_m10 := cov5 (-10) (-11) (-12) (by norm_num) (by norm_num)
  have c_cov5_m11 := cov5 (-11) (-12) (-13) (by norm_num) (by norm_num)
  have c_cov5_m12 := cov5 (-12) (-13) (-14) (by norm_num) (by norm_num)
  have c_cov5_m13 := cov5 (-13) (-14) (-15) (by norm_num) (by norm_num)
  have c_cov5_m2 := cov5 (-2) (-3) (-4) (by norm_num) (by norm_num)
  have c_cov5_m3 := cov5 (-3) (-4) (-5) (by norm_num) (by norm_num)
  have c_cov5_m4 := cov5 (-4) (-5) (-6) (by norm_num) (by norm_num)
  have c_cov5_m5 := cov5 (-5) (-6) (-7) (by norm_num) (by norm_num)
  have c_cov5_m6 := cov5 (-6) (-7) (-8) (by norm_num) (by norm_num)
  have c_cov5_m7 := cov5 (-7) (-8) (-9) (by norm_num) (by norm_num)
  have c_cov5_m8 := cov5 (-8) (-9) (-10) (by norm_num) (by norm_num)
  have c_cov5_m9 := cov5 (-9) (-10) (-11) (by norm_num) (by norm_num)
  have c_cov5_0 := cov5 0 (-1) (-2) (by norm_num) (by norm_num)
  have c_cov5_1 := cov5 1 0 (-1) (by norm_num) (by norm_num)
  have c_cov5_2 := cov5 2 1 0 (by norm_num) (by norm_num)
  have c_cov5_3 := cov5 3 2 1 (by norm_num) (by norm_num)
  have c_cov5_4 := cov5 4 3 2 (by norm_num) (by norm_num)
  have c_cov5_5 := cov5 5 4 3 (by norm_num) (by norm_num)
  have c_cov5_6 := cov5 6 5 4 (by norm_num) (by norm_num)
  have c_cov5_7 := cov5 7 6 5 (by norm_num) (by norm_num)
  have c_cov5_8 := cov5 8 7 6 (by norm_num) (by norm_num)
  have c_cov5_9 := cov5 9 8 7 (by norm_num) (by norm_num)
  have c_d4_m1 := hd4 (-1) (-2) (-3) (-4) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m13 := hd4 (-13) (-14) (-15) (-16) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m3 := hd4 (-3) (-4) (-5) (-6) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m4 := hd4 (-4) (-5) (-6) (-7) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m5 := hd4 (-5) (-6) (-7) (-8) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m8 := hd4 (-8) (-9) (-10) (-11) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_m9 := hd4 (-9) (-10) (-11) (-12) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_0 := hd4 0 (-1) (-2) (-3) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_1 := hd4 1 0 (-1) (-2) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_2 := hd4 2 1 0 (-1) (by norm_num) (by norm_num) (by norm_num)
  have c_d4_3 := hd4 3 2 1 0 (by norm_num) (by norm_num) (by norm_num)
  have c_d4_5 := hd4 5 4 3 2 (by norm_num) (by norm_num) (by norm_num)
  have c_d4_6 := hd4 6 5 4 3 (by norm_num) (by norm_num) (by norm_num)
  have c_d4_7 := hd4 7 6 5 4 (by norm_num) (by norm_num) (by norm_num)
  have c_d6_m1 := hd6 (-1) (-2) (by norm_num)
  have c_d6_m10 := hd6 (-10) (-11) (by norm_num)
  have c_d6_m11 := hd6 (-11) (-12) (by norm_num)
  have c_d6_m12 := hd6 (-12) (-13) (by norm_num)
  have c_d6_m13 := hd6 (-13) (-14) (by norm_num)
  have c_d6_m2 := hd6 (-2) (-3) (by norm_num)
  have c_d6_m3 := hd6 (-3) (-4) (by norm_num)
  have c_d6_m4 := hd6 (-4) (-5) (by norm_num)
  have c_d6_m5 := hd6 (-5) (-6) (by norm_num)
  have c_d6_m6 := hd6 (-6) (-7) (by norm_num)
  have c_d6_m7 := hd6 (-7) (-8) (by norm_num)
  have c_d6_m8 := hd6 (-8) (-9) (by norm_num)
  have c_d6_m9 := hd6 (-9) (-10) (by norm_num)
  have c_d6_0 := hd6 0 (-1) (by norm_num)
  have c_d6_1 := hd6 1 0 (by norm_num)
  have c_d6_2 := hd6 2 1 (by norm_num)
  have c_d6_3 := hd6 3 2 (by norm_num)
  have c_d6_4 := hd6 4 3 (by norm_num)
  have c_d6_5 := hd6 5 4 (by norm_num)
  have c_d6_6 := hd6 6 5 (by norm_num)
  have c_d6_7 := hd6 7 6 (by norm_num)
  have c_d6_8 := hd6 8 7 (by norm_num)
  have c_t26_m1 := h26 (-1)
  have c_t26_m10 := h26 (-10)
  have c_t26_m11 := h26 (-11)
  have c_t26_m12 := h26 (-12)
  have c_t26_m13 := h26 (-13)
  have c_t26_m14 := h26 (-14)
  have c_t26_m15 := h26 (-15)
  have c_t26_m2 := h26 (-2)
  have c_t26_m3 := h26 (-3)
  have c_t26_m4 := h26 (-4)
  have c_t26_m5 := h26 (-5)
  have c_t26_m6 := h26 (-6)
  have c_t26_m7 := h26 (-7)
  have c_t26_m8 := h26 (-8)
  have c_t26_m9 := h26 (-9)
  have c_t26_0 := h26 0
  have c_t26_1 := h26 1
  have c_t26_2 := h26 2
  have c_t26_3 := h26 3
  have c_t26_4 := h26 4
  have c_t26_5 := h26 5
  have c_t26_6 := h26 6
  have c_t26_7 := h26 7
  have c_t26_8 := h26 8
  have c_t51_m1 := h51 (-1)
  have c_t51_m10 := h51 (-10)
  have c_t51_m11 := h51 (-11)
  have c_t51_m12 := h51 (-12)
  have c_t51_m13 := h51 (-13)
  have c_t51_m14 := h51 (-14)
  have c_t51_m2 := h51 (-2)
  have c_t51_m3 := h51 (-3)
  have c_t51_m4 := h51 (-4)
  have c_t51_m5 := h51 (-5)
  have c_t51_m6 := h51 (-6)
  have c_t51_m7 := h51 (-7)
  have c_t51_m8 := h51 (-8)
  have c_t51_m9 := h51 (-9)
  have c_t51_0 := h51 0
  have c_t51_1 := h51 1
  have c_t51_2 := h51 2
  have c_t51_3 := h51 3
  have c_t51_4 := h51 4
  have c_t51_5 := h51 5
  have c_t51_6 := h51 6
  have c_t51_7 := h51 7
  have c_t51_8 := h51 8
  have c_t51_9 := h51 9
  clear hcount hd4 hd6 hcov h51 h26 cov1 cov2 cov3 cov5 h0 h7
  generalize y (-16) 3 = vm16_3 at *
  generalize y (-15) 2 = vm15_2 at *
  generalize y (-15) 6 = vm15_6 at *
  generalize y (-14) 1 = vm14_1 at *
  generalize y (-14) 2 = vm14_2 at *
  generalize y (-14) 5 = vm14_5 at *
  generalize y (-14) 6 = vm14_6 at *
  generalize y (-13) 1 = vm13_1 at *
  generalize y (-13) 2 = vm13_2 at *
  generalize y (-13) 4 = vm13_4 at *
  generalize y (-13) 5 = vm13_5 at *
  generalize y (-13) 6 = vm13_6 at *
  generalize y (-12) 1 = vm12_1 at *
  generalize y (-12) 2 = vm12_2 at *
  generalize y (-12) 3 = vm12_3 at *
  generalize y (-12) 4 = vm12_4 at *
  generalize y (-12) 5 = vm12_5 at *
  generalize y (-12) 6 = vm12_6 at *
  generalize y (-11) 1 = vm11_1 at *
  generalize y (-11) 2 = vm11_2 at *
  generalize y (-11) 3 = vm11_3 at *
  generalize y (-11) 5 = vm11_5 at *
  generalize y (-11) 6 = vm11_6 at *
  generalize y (-10) 1 = vm10_1 at *
  generalize y (-10) 2 = vm10_2 at *
  generalize y (-10) 5 = vm10_5 at *
  generalize y (-10) 6 = vm10_6 at *
  generalize y (-9) 1 = vm9_1 at *
  generalize y (-9) 2 = vm9_2 at *
  generalize y (-9) 4 = vm9_4 at *
  generalize y (-9) 5 = vm9_5 at *
  generalize y (-9) 6 = vm9_6 at *
  generalize y (-8) 1 = vm8_1 at *
  generalize y (-8) 2 = vm8_2 at *
  generalize y (-8) 3 = vm8_3 at *
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
  generalize y (-6) 5 = vm6_5 at *
  generalize y (-6) 6 = vm6_6 at *
  generalize y (-5) 1 = vm5_1 at *
  generalize y (-5) 2 = vm5_2 at *
  generalize y (-5) 4 = vm5_4 at *
  generalize y (-5) 5 = vm5_5 at *
  generalize y (-5) 6 = vm5_6 at *
  generalize y (-4) 1 = vm4_1 at *
  generalize y (-4) 2 = vm4_2 at *
  generalize y (-4) 3 = vm4_3 at *
  generalize y (-4) 4 = vm4_4 at *
  generalize y (-4) 5 = vm4_5 at *
  generalize y (-4) 6 = vm4_6 at *
  generalize y (-3) 1 = vm3_1 at *
  generalize y (-3) 2 = vm3_2 at *
  generalize y (-3) 3 = vm3_3 at *
  generalize y (-3) 4 = vm3_4 at *
  generalize y (-3) 5 = vm3_5 at *
  generalize y (-3) 6 = vm3_6 at *
  generalize y (-2) 1 = vm2_1 at *
  generalize y (-2) 2 = vm2_2 at *
  generalize y (-2) 3 = vm2_3 at *
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
  generalize y 2 5 = v2_5 at *
  generalize y 2 6 = v2_6 at *
  generalize y 3 1 = v3_1 at *
  generalize y 3 2 = v3_2 at *
  generalize y 3 3 = v3_3 at *
  generalize y 3 4 = v3_4 at *
  generalize y 3 5 = v3_5 at *
  generalize y 3 6 = v3_6 at *
  generalize y 4 1 = v4_1 at *
  generalize y 4 2 = v4_2 at *
  generalize y 4 3 = v4_3 at *
  generalize y 4 5 = v4_5 at *
  generalize y 4 6 = v4_6 at *
  generalize y 5 1 = v5_1 at *
  generalize y 5 2 = v5_2 at *
  generalize y 5 4 = v5_4 at *
  generalize y 5 5 = v5_5 at *
  generalize y 5 6 = v5_6 at *
  generalize y 6 1 = v6_1 at *
  generalize y 6 2 = v6_2 at *
  generalize y 6 3 = v6_3 at *
  generalize y 6 4 = v6_4 at *
  generalize y 6 5 = v6_5 at *
  generalize y 6 6 = v6_6 at *
  generalize y 7 1 = v7_1 at *
  generalize y 7 2 = v7_2 at *
  generalize y 7 3 = v7_3 at *
  generalize y 7 4 = v7_4 at *
  generalize y 7 5 = v7_5 at *
  generalize y 7 6 = v7_6 at *
  generalize y 8 1 = v8_1 at *
  generalize y 8 2 = v8_2 at *
  generalize y 8 5 = v8_5 at *
  generalize y 8 6 = v8_6 at *
  generalize y 9 1 = v9_1 at *
  generalize y 9 5 = v9_5 at *
  clear y
  cases v0_1 <;> cases v0_6
  · rfl
  · exfalso
    have e : vm1_1 = false := by clear * - c_d6_0; revert c_d6_0; revert vm1_1; decide
    subst e
    have e : vm1_5 = false := by clear * - c_t51_m1; revert c_t51_m1; revert vm1_5; decide
    subst e
    have e : v0_5 = false := by clear * - c_t51_0; revert c_t51_0; revert v0_5; decide
    subst e
    have e : v1_6 = true := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
    subst e
    have e : vm2_2 = true := by clear * - c_cov5_0; revert c_cov5_0; revert vm2_2 vm1_6; decide
    subst e
    have e : vm2_6 = true := by clear * - c_t26_m2; revert c_t26_m2; revert vm2_6; decide
    subst e
    have e : vm3_1 = false := by clear * - c_d6_m2; revert c_d6_m2; revert vm3_1; decide
    subst e
    have e : vm3_5 = false := by clear * - c_t51_m3; revert c_t51_m3; revert vm3_5; decide
    subst e
    have e : vm3_3 = false := by clear * - c_d4_0; revert c_d4_0; revert vm3_3 v0_4; decide
    subst e
    have e : v0_4 = false := by clear * - c_d4_0; revert c_d4_0; revert v0_4; decide
    subst e
    cases vm1_2
    · -- vm1_2 = False
      have e : v1_5 = true := by clear * - c_cov5_1; revert c_cov5_1; revert v1_5; decide
      subst e
      have e : v1_1 = true := by clear * - c_t51_1; revert c_t51_1; revert v1_1; decide
      subst e
      have e : v2_6 = false := by clear * - c_d6_2; revert c_d6_2; revert v2_6; decide
      subst e
      have e : v2_2 = false := by clear * - c_t26_2; revert c_t26_2; revert v2_2; decide
      subst e
      have e : vm1_3 = false := by clear * - c_d4_2; revert c_d4_2; revert vm1_3 v0_2 v2_4; decide
      subst e
      have e : v0_2 = false := by clear * - c_d4_2; revert c_d4_2; revert v0_2 v2_4; decide
      subst e
      have e : v2_4 = false := by clear * - c_d4_2; revert c_d4_2; revert v2_4; decide
      subst e
      have e : v3_3 = false := by clear * - c_count_6; revert c_count_6; revert v3_3 v4_2 v5_1; decide
      subst e
      have e : v4_2 = false := by clear * - c_count_6; revert c_count_6; revert v4_2 v5_1; decide
      subst e
      have e : v5_1 = false := by clear * - c_count_6; revert c_count_6; revert v5_1; decide
      subst e
      have e : v5_5 = false := by clear * - c_t51_5; revert c_t51_5; revert v5_5; decide
      subst e
      have e : v1_3 = true := by clear * - c_cov2_4; revert c_cov2_4; revert v1_3 v3_1; decide
      subst e
      have e : v3_1 = false := by clear * - c_count_4; revert c_count_4; revert v3_1; decide
      subst e
      have e : v4_6 = true := by clear * - c_d6_4; revert c_d6_4; revert v4_6; decide
      subst e
      have e : v6_4 = true := by clear * - c_d4_6; revert c_d4_6; revert v6_4; decide
      subst e
      have e : v4_5 = true := by clear * - c_cov5_4; revert c_cov5_4; revert v3_6 v4_5; decide
      subst e
      have e : v4_1 = true := by clear * - c_t51_4; revert c_t51_4; revert v4_1; decide
      subst e
      have e : v5_6 = false := by clear * - c_d6_5; revert c_d6_5; revert v5_6; decide
      subst e
      have e : v5_2 = false := by clear * - c_t26_5; revert c_t26_5; revert v5_2; decide
      subst e
      have e : v6_5 = true := by clear * - c_cov5_6; revert c_cov5_6; revert v6_5; decide
      subst e
      have e : v6_1 = true := by clear * - c_t51_6; revert c_t51_6; revert v6_1; decide
      subst e
      have e : v7_6 = false := by clear * - c_d6_7; revert c_d6_7; revert v7_6; decide
      subst e
      have e : v7_2 = false := by clear * - c_t26_7; revert c_t26_7; revert v7_2; decide
      subst e
      have e : v4_3 = false := by clear * - c_d4_7; revert c_d4_7; revert v4_3 v7_4; decide
      subst e
      have e : v2_5 = false := by clear * - c_count_7; revert c_count_7; revert v2_5 v3_4; decide
      subst e
      have e : v3_4 = false := by clear * - c_count_7; revert c_count_7; revert v3_4; decide
      subst e
      have e : v1_4 = true := by clear * - c_cov2_5; revert c_cov2_5; revert v1_4 v2_3 v3_2; decide
      subst e
      have e : vm1_6 = false := by clear * - c_count_5; revert c_count_5; revert vm1_6 v2_3 v3_2; decide
      subst e
      have e : v2_3 = false := by clear * - c_count_5; revert c_count_5; revert v2_3 v3_2; decide
      subst e
      have e : v3_2 = false := by clear * - c_count_5; revert c_count_5; revert v3_2; decide
      subst e
      have e : v5_4 = false := by clear * - c_d4_5; revert c_d4_5; revert v3_6 v5_4; decide
      subst e
      have e : v6_3 = true := by clear * - c_cov3_6; revert c_cov3_6; revert v3_6 v6_3; decide
      subst e
      have e : v3_6 = false := by clear * - c_count_9; revert c_count_9; revert v3_6 v8_1; decide
      subst e
      have e : v8_1 = false := by clear * - c_count_9; revert c_count_9; revert v8_1; decide
      subst e
      have e : v9_5 = true := by clear * - c_cov5_9; revert c_cov5_9; revert v8_6 v9_5; decide
      subst e
      have e : v9_1 = true := by clear * - c_t51_9; revert c_t51_9; revert v9_1; decide
      subst e
      clear * - c_count_10; revert c_count_10; revert v7_3 v8_2; decide
    · -- vm1_2 = True
      have e : vm1_6 = true := by clear * - c_t26_m1; revert c_t26_m1; revert vm1_6; decide
      subst e
      have e : vm2_1 = false := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
      subst e
      have e : vm2_5 = false := by clear * - c_t51_m2; revert c_t51_m2; revert vm2_5; decide
      subst e
      have e : vm3_2 = true := by clear * - c_cov5_m1; revert c_cov5_m1; revert vm3_2; decide
      subst e
      have e : vm3_6 = true := by clear * - c_t26_m3; revert c_t26_m3; revert vm3_6; decide
      subst e
      have e : vm4_1 = false := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
      subst e
      have e : vm4_5 = false := by clear * - c_t51_m4; revert c_t51_m4; revert vm4_5; decide
      subst e
      have e : vm4_2 = true := by clear * - c_cov5_m2; revert c_cov5_m2; revert vm4_2; decide
      subst e
      have e : vm4_6 = true := by clear * - c_t26_m4; revert c_t26_m4; revert vm4_6; decide
      subst e
      have e : vm5_1 = false := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
      subst e
      have e : vm5_5 = false := by clear * - c_t51_m5; revert c_t51_m5; revert vm5_5; decide
      subst e
      have e : vm5_2 = true := by clear * - c_cov5_m3; revert c_cov5_m3; revert vm5_2; decide
      subst e
      have e : vm5_6 = true := by clear * - c_t26_m5; revert c_t26_m5; revert vm5_6; decide
      subst e
      have e : vm6_1 = false := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
      subst e
      have e : vm6_5 = false := by clear * - c_t51_m6; revert c_t51_m6; revert vm6_5; decide
      subst e
      have e : vm6_2 = true := by clear * - c_cov5_m4; revert c_cov5_m4; revert vm6_2; decide
      subst e
      have e : vm6_6 = true := by clear * - c_t26_m6; revert c_t26_m6; revert vm6_6; decide
      subst e
      have e : vm7_1 = false := by clear * - c_d6_m6; revert c_d6_m6; revert vm7_1; decide
      subst e
      have e : vm7_5 = false := by clear * - c_t51_m7; revert c_t51_m7; revert vm7_5; decide
      subst e
      have e : vm7_2 = true := by clear * - c_cov5_m5; revert c_cov5_m5; revert vm7_2; decide
      subst e
      have e : vm7_6 = true := by clear * - c_t26_m7; revert c_t26_m7; revert vm7_6; decide
      subst e
      have e : vm8_1 = false := by clear * - c_d6_m7; revert c_d6_m7; revert vm8_1; decide
      subst e
      have e : vm8_5 = false := by clear * - c_t51_m8; revert c_t51_m8; revert vm8_5; decide
      subst e
      have e : vm8_2 = true := by clear * - c_cov5_m6; revert c_cov5_m6; revert vm8_2; decide
      subst e
      have e : vm8_6 = true := by clear * - c_t26_m8; revert c_t26_m8; revert vm8_6; decide
      subst e
      have e : vm9_1 = false := by clear * - c_d6_m8; revert c_d6_m8; revert vm9_1; decide
      subst e
      have e : vm9_5 = false := by clear * - c_t51_m9; revert c_t51_m9; revert vm9_5; decide
      subst e
      have e : vm9_2 = true := by clear * - c_cov5_m7; revert c_cov5_m7; revert vm9_2; decide
      subst e
      have e : vm9_6 = true := by clear * - c_t26_m9; revert c_t26_m9; revert vm9_6; decide
      subst e
      have e : vm10_1 = false := by clear * - c_d6_m9; revert c_d6_m9; revert vm10_1; decide
      subst e
      have e : vm10_5 = false := by clear * - c_t51_m10; revert c_t51_m10; revert vm10_5; decide
      subst e
      have e : vm10_2 = true := by clear * - c_cov5_m8; revert c_cov5_m8; revert vm10_2; decide
      subst e
      have e : vm10_6 = true := by clear * - c_t26_m10; revert c_t26_m10; revert vm10_6; decide
      subst e
      have e : vm11_1 = false := by clear * - c_d6_m10; revert c_d6_m10; revert vm11_1; decide
      subst e
      have e : vm11_5 = false := by clear * - c_t51_m11; revert c_t51_m11; revert vm11_5; decide
      subst e
      have e : vm11_2 = true := by clear * - c_cov5_m9; revert c_cov5_m9; revert vm11_2; decide
      subst e
      have e : vm11_6 = true := by clear * - c_t26_m11; revert c_t26_m11; revert vm11_6; decide
      subst e
      have e : vm12_1 = false := by clear * - c_d6_m11; revert c_d6_m11; revert vm12_1; decide
      subst e
      have e : vm12_5 = false := by clear * - c_t51_m12; revert c_t51_m12; revert vm12_5; decide
      subst e
      have e : vm12_2 = true := by clear * - c_cov5_m10; revert c_cov5_m10; revert vm12_2; decide
      subst e
      have e : vm12_6 = true := by clear * - c_t26_m12; revert c_t26_m12; revert vm12_6; decide
      subst e
      have e : vm13_1 = false := by clear * - c_d6_m12; revert c_d6_m12; revert vm13_1; decide
      subst e
      have e : vm13_5 = false := by clear * - c_t51_m13; revert c_t51_m13; revert vm13_5; decide
      subst e
      have e : vm13_2 = true := by clear * - c_cov5_m11; revert c_cov5_m11; revert vm13_2; decide
      subst e
      have e : vm13_6 = true := by clear * - c_t26_m13; revert c_t26_m13; revert vm13_6; decide
      subst e
      have e : vm14_1 = false := by clear * - c_d6_m13; revert c_d6_m13; revert vm14_1; decide
      subst e
      have e : vm14_5 = false := by clear * - c_t51_m14; revert c_t51_m14; revert vm14_5; decide
      subst e
      have e : vm14_2 = true := by clear * - c_cov5_m12; revert c_cov5_m12; revert vm14_2; decide
      subst e
      have e : vm14_6 = true := by clear * - c_t26_m14; revert c_t26_m14; revert vm14_6; decide
      subst e
      have e : vm15_2 = true := by clear * - c_cov5_m13; revert c_cov5_m13; revert vm15_2; decide
      subst e
      have e : vm15_6 = true := by clear * - c_t26_m15; revert c_t26_m15; revert vm15_6; decide
      subst e
      have e : vm4_4 = false := by clear * - c_count_0; revert c_count_0; revert vm4_4; decide
      subst e
      have e : vm7_3 = false := by clear * - c_d4_m4; revert c_d4_m4; revert vm7_3; decide
      subst e
      have e : vm8_4 = false := by clear * - c_count_m4; revert c_count_m4; revert vm8_4; decide
      subst e
      have e : vm11_3 = false := by clear * - c_d4_m8; revert c_d4_m8; revert vm11_3; decide
      subst e
      have e : vm12_4 = false := by clear * - c_count_m8; revert c_count_m8; revert vm12_4; decide
      subst e
      have e : vm16_3 = false := by clear * - c_d4_m13; revert c_d4_m13; revert vm16_3 vm13_4; decide
      subst e
      have e : vm13_4 = false := by clear * - c_d4_m13; revert c_d4_m13; revert vm13_4; decide
      subst e
      have e : vm12_3 = false := by clear * - c_count_m9; revert c_count_m9; revert vm12_3; decide
      subst e
      have e : vm9_4 = false := by clear * - c_d4_m9; revert c_d4_m9; revert vm9_4; decide
      subst e
      have e : vm8_3 = true := by clear * - c_cov3_m8; revert c_cov3_m8; revert vm8_3; decide
      subst e
      clear * - c_count_m5; revert c_count_m5; decide
  · exfalso
    have e : v0_2 = false := by clear * - c_t26_0; revert c_t26_0; revert v0_2; decide
    subst e
    have e : v1_6 = false := by clear * - c_d6_1; revert c_d6_1; revert v1_6; decide
    subst e
    have e : v1_2 = false := by clear * - c_t26_1; revert c_t26_1; revert v1_2; decide
    subst e
    have e : v2_5 = true := by clear * - c_cov5_2; revert c_cov5_2; revert v1_1 v2_5; decide
    subst e
    have e : v2_1 = true := by clear * - c_t51_2; revert c_t51_2; revert v2_1; decide
    subst e
    have e : v3_6 = false := by clear * - c_d6_3; revert c_d6_3; revert v3_6; decide
    subst e
    have e : v3_2 = false := by clear * - c_t26_3; revert c_t26_3; revert v3_2; decide
    subst e
    have e : v0_3 = false := by clear * - c_d4_3; revert c_d4_3; revert v0_3 v3_4; decide
    subst e
    have e : v3_4 = false := by clear * - c_d4_3; revert c_d4_3; revert v3_4; decide
    subst e
    cases vm1_2
    · -- vm1_2 = False
      have e : v1_5 = true := by clear * - c_cov5_1; revert c_cov5_1; revert v1_5; decide
      subst e
      have e : v1_1 = true := by clear * - c_t51_1; revert c_t51_1; revert v1_1; decide
      subst e
      have e : v2_6 = false := by clear * - c_d6_2; revert c_d6_2; revert v2_6; decide
      subst e
      have e : v2_2 = false := by clear * - c_t26_2; revert c_t26_2; revert v2_2; decide
      subst e
      have e : v3_5 = true := by clear * - c_cov5_3; revert c_cov5_3; revert v3_5; decide
      subst e
      have e : v3_1 = true := by clear * - c_t51_3; revert c_t51_3; revert v3_1; decide
      subst e
      have e : v4_6 = false := by clear * - c_d6_4; revert c_d6_4; revert v4_6; decide
      subst e
      have e : v4_5 = true := by clear * - c_cov5_4; revert c_cov5_4; revert v4_5; decide
      subst e
      have e : v4_1 = true := by clear * - c_t51_4; revert c_t51_4; revert v4_1; decide
      subst e
      have e : v4_2 = false := by clear * - c_t26_4; revert c_t26_4; revert v4_2; decide
      subst e
      have e : v5_6 = false := by clear * - c_d6_5; revert c_d6_5; revert v5_6; decide
      subst e
      have e : v5_5 = true := by clear * - c_cov5_5; revert c_cov5_5; revert v5_5; decide
      subst e
      have e : v5_1 = true := by clear * - c_t51_5; revert c_t51_5; revert v5_1; decide
      subst e
      have e : v5_2 = false := by clear * - c_t26_5; revert c_t26_5; revert v5_2; decide
      subst e
      have e : v6_6 = false := by clear * - c_d6_6; revert c_d6_6; revert v6_6; decide
      subst e
      have e : v6_5 = true := by clear * - c_cov5_6; revert c_cov5_6; revert v6_5; decide
      subst e
      have e : v6_1 = true := by clear * - c_t51_6; revert c_t51_6; revert v6_1; decide
      subst e
      have e : v6_2 = false := by clear * - c_t26_6; revert c_t26_6; revert v6_2; decide
      subst e
      have e : v4_3 = false := by clear * - c_count_7; revert c_count_7; revert v4_3; decide
      subst e
      have e : v7_6 = false := by clear * - c_d6_7; revert c_d6_7; revert v7_6; decide
      subst e
      have e : v7_5 = true := by clear * - c_cov5_7; revert c_cov5_7; revert v7_5; decide
      subst e
      have e : v7_1 = true := by clear * - c_t51_7; revert c_t51_7; revert v7_1; decide
      subst e
      have e : v7_2 = false := by clear * - c_t26_7; revert c_t26_7; revert v7_2; decide
      subst e
      have e : v8_6 = false := by clear * - c_d6_8; revert c_d6_8; revert v8_6; decide
      subst e
      have e : v8_5 = true := by clear * - c_cov5_8; revert c_cov5_8; revert v8_5; decide
      subst e
      have e : v8_1 = true := by clear * - c_t51_8; revert c_t51_8; revert v8_1; decide
      subst e
      have e : v8_2 = false := by clear * - c_t26_8; revert c_t26_8; revert v8_2; decide
      subst e
      have e : v9_5 = true := by clear * - c_cov5_9; revert c_cov5_9; revert v9_5; decide
      subst e
      have e : v9_1 = true := by clear * - c_t51_9; revert c_t51_9; revert v9_1; decide
      subst e
      have e : vm1_3 = false := by clear * - c_d4_2; revert c_d4_2; revert vm1_3 v2_4; decide
      subst e
      have e : v2_4 = false := by clear * - c_d4_2; revert c_d4_2; revert v2_4; decide
      subst e
      have e : v3_3 = false := by clear * - c_count_6; revert c_count_6; revert v3_3; decide
      subst e
      have e : v6_4 = false := by clear * - c_d4_6; revert c_d4_6; revert v6_4; decide
      subst e
      have e : v7_3 = true := by clear * - c_cov3_7; revert c_cov3_7; revert v7_3; decide
      subst e
      clear * - c_count_10; revert c_count_10; decide
    · -- vm1_2 = True
      have e : vm1_6 = true := by clear * - c_t26_m1; revert c_t26_m1; revert vm1_6; decide
      subst e
      have e : vm2_1 = false := by clear * - c_d6_m1; revert c_d6_m1; revert vm2_1; decide
      subst e
      have e : vm2_5 = false := by clear * - c_t51_m2; revert c_t51_m2; revert vm2_5; decide
      subst e
      have e : vm2_3 = false := by clear * - c_d4_1; revert c_d4_1; revert vm2_3 v0_5 v1_4; decide
      subst e
      have e : vm5_6 = false := by clear * - c_count_1; revert c_count_1; revert vm5_6 vm4_5 vm3_4; decide
      subst e
      have e : vm6_1 = true := by clear * - c_d6_m5; revert c_d6_m5; revert vm6_1; decide
      subst e
      have e : vm5_2 = false := by clear * - c_t26_m5; revert c_t26_m5; revert vm5_2; decide
      subst e
      have e : vm4_5 = false := by clear * - c_count_1; revert c_count_1; revert vm4_5 vm3_4; decide
      subst e
      have e : vm3_4 = false := by clear * - c_count_1; revert c_count_1; revert vm3_4; decide
      subst e
      have e : vm6_2 = true := by clear * - c_cov5_m4; revert c_cov5_m4; revert vm6_2 vm5_1; decide
      subst e
      have e : vm6_6 = true := by clear * - c_t26_m6; revert c_t26_m6; revert vm6_6; decide
      subst e
      have e : vm7_1 = false := by clear * - c_d6_m6; revert c_d6_m6; revert vm7_1; decide
      subst e
      have e : vm7_5 = false := by clear * - c_t51_m7; revert c_t51_m7; revert vm7_5; decide
      subst e
      have e : vm6_3 = true := by clear * - c_d4_m3; revert c_d4_m3; revert vm6_3 vm4_1; decide
      subst e
      have e : vm1_4 = true := by clear * - c_cov2_1; revert c_cov2_1; revert vm3_6 vm1_4; decide
      subst e
      have e : vm3_6 = false := by clear * - c_count_3; revert c_count_3; revert vm3_6; decide
      subst e
      have e : vm4_1 = true := by clear * - c_d6_m3; revert c_d6_m3; revert vm4_1; decide
      subst e
      have e : vm3_2 = false := by clear * - c_t26_m3; revert c_t26_m3; revert vm3_2; decide
      subst e
      have e : vm4_3 = false := by clear * - c_d4_m1; revert c_d4_m1; revert vm4_3; decide
      subst e
      have e : vm4_2 = true := by clear * - c_cov5_m2; revert c_cov5_m2; revert vm4_2 vm3_1; decide
      subst e
      have e : vm4_6 = true := by clear * - c_t26_m4; revert c_t26_m4; revert vm4_6; decide
      subst e
      have e : vm5_1 = false := by clear * - c_d6_m4; revert c_d6_m4; revert vm5_1; decide
      subst e
      have e : vm5_5 = false := by clear * - c_t51_m5; revert c_t51_m5; revert vm5_5; decide
      subst e
      have e : vm7_3 = false := by clear * - c_d4_m4; revert c_d4_m4; revert vm7_3 vm4_4; decide
      subst e
      have e : vm9_6 = false := by clear * - c_count_m3; revert c_count_m3; revert vm9_6 vm8_5 vm7_4; decide
      subst e
      have e : vm9_2 = false := by clear * - c_t26_m9; revert c_t26_m9; revert vm9_2; decide
      subst e
      have e : vm8_1 = true := by clear * - c_cov5_m7; revert c_cov5_m7; revert vm8_1 vm8_6; decide
      subst e
      have e : vm7_6 = false := by clear * - c_d6_m7; revert c_d6_m7; revert vm7_6; decide
      subst e
      have e : vm8_6 = true := by clear * - c_cov5_m7; revert c_cov5_m7; revert vm8_6; decide
      subst e
      have e : vm9_1 = false := by clear * - c_d6_m8; revert c_d6_m8; revert vm9_1; decide
      subst e
      have e : vm9_5 = false := by clear * - c_t51_m9; revert c_t51_m9; revert vm9_5; decide
      subst e
      have e : vm7_2 = false := by clear * - c_t26_m7; revert c_t26_m7; revert vm7_2; decide
      subst e
      have e : vm8_5 = false := by clear * - c_count_m3; revert c_count_m3; revert vm8_5 vm7_4; decide
      subst e
      have e : vm10_2 = true := by clear * - c_cov5_m8; revert c_cov5_m8; revert vm10_2; decide
      subst e
      have e : vm10_6 = true := by clear * - c_t26_m10; revert c_t26_m10; revert vm10_6; decide
      subst e
      have e : vm8_4 = false := by clear * - c_count_m4; revert c_count_m4; revert vm8_4; decide
      subst e
      have e : vm6_5 = true := by clear * - c_cov3_m4; revert c_cov3_m4; revert vm6_5 vm5_4; decide
      subst e
      have e : vm5_4 = true := by clear * - c_count_m1; revert c_count_m1; revert vm5_4; decide
      subst e
      clear * - c_d4_m5; revert c_d4_m5; revert vm8_3; decide
  · rfl

theorem cycle_power_seven_tight_type_sequence_one_iff_six (n : ℕ) [NeZero n]
    (x : ZMod n → Fin 8 → Bool) (h0 : ∀ p, x p 0 = true) (h7 : ∀ p, x p 7 = true)
    (hcount : ∀ u, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat +
      (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat = 2)
    (hd4 : ∀ u, (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat +
      (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3).toNat = 1)
    (hd6 : ∀ u, (x (u - 1) 1).toNat + (x u 6).toNat = 1)
    (hcov : ∀ (d : ℕ) (u : ZMod n), d ∈ ({1, 2, 3, 5} : Finset ℕ) →
      ∃ j : Fin 8, ∃ hj : j.val + d ≤ 7, x (u - j.val) j = true ∧
        x (u - j.val) ⟨j.val + d, by omega⟩ = true)
    (h51 : ∀ p, x p 5 = true → x p 1 = true) (h26 : ∀ p, x p 2 = true → x p 6 = true)
    (i : ZMod n) : x i 1 = x i 6 := by
  have key := cycle_power_seven_tight_type_sequence_core (fun a j => x (i + (a : ZMod n)) j) (fun a => h0 _) (fun a => h7 _)
    (by
      rintro o _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
      have h := hcount (i + (o : ZMod n))
      simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_one]
      simpa only [add_sub_assoc] using h)
    (by
      rintro o _ _ _ rfl rfl rfl
      have h := hd4 (i + (o : ZMod n))
      simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_one]
      simpa only [add_sub_assoc] using h)
    (by
      rintro o _ rfl
      have h := hd6 (i + (o : ZMod n))
      simp only [Int.cast_sub, Int.cast_one]
      simpa only [add_sub_assoc] using h)
    (by
      intro d o hd
      obtain ⟨j, hj, h1, h2⟩ := hcov d (i + (o : ZMod n)) hd
      refine ⟨j, hj, ?_, ?_⟩
      · simp only [Int.cast_sub, Int.cast_natCast]
        simpa only [add_sub_assoc] using h1
      · simp only [Int.cast_sub, Int.cast_natCast]
        simpa only [add_sub_assoc] using h2)
    (fun a => h51 _) (fun a => h26 _)
  simpa using key
