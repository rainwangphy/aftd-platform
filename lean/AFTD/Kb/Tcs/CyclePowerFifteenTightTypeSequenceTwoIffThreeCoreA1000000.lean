import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000000

Topic: combinatorics   Node: d158809993f6

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 90 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000000_aux (x : ℤ → Fin 16 → Bool)
    (hcount : ∀ u : ℤ, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat + (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat + (x (u - 7) 7).toNat + (x (u - 8) 8).toNat + (x (u - 9) 9).toNat + (x (u - 10) 10).toNat + (x (u - 11) 11).toNat + (x (u - 12) 12).toNat + (x (u - 13) 13).toNat + (x (u - 14) 14).toNat = 3)
    (hd14 : ∀ u : ℤ, (x u 14).toNat + (x (u - 1) 1).toNat = 1)
    (hd12 : ∀ u : ℤ, (x u 12).toNat + (x (u - 1) 1 && x (u - 1) 13).toNat + (x (u - 2) 2 && x (u - 2) 14).toNat + (x (u - 3) 3).toNat = 1)
    (hd8 : ∀ u : ℤ, (x u 8).toNat + (x (u - 1) 1 && x (u - 1) 9).toNat + (x (u - 2) 2 && x (u - 2) 10).toNat + (x (u - 3) 3 && x (u - 3) 11).toNat + (x (u - 4) 4 && x (u - 4) 12).toNat + (x (u - 5) 5 && x (u - 5) 13).toNat + (x (u - 6) 6 && x (u - 6) 14).toNat + (x (u - 7) 7).toNat = 1)
    (hcov1 : ∀ u : ℤ, 1 ≤ (x u 1).toNat + (x (u - 1) 1 && x (u - 1) 2).toNat + (x (u - 2) 2 && x (u - 2) 3).toNat + (x (u - 3) 3 && x (u - 3) 4).toNat + (x (u - 4) 4 && x (u - 4) 5).toNat + (x (u - 5) 5 && x (u - 5) 6).toNat + (x (u - 6) 6 && x (u - 6) 7).toNat + (x (u - 7) 7 && x (u - 7) 8).toNat + (x (u - 8) 8 && x (u - 8) 9).toNat + (x (u - 9) 9 && x (u - 9) 10).toNat + (x (u - 10) 10 && x (u - 10) 11).toNat + (x (u - 11) 11 && x (u - 11) 12).toNat + (x (u - 12) 12 && x (u - 12) 13).toNat + (x (u - 13) 13 && x (u - 13) 14).toNat + (x (u - 14) 14).toNat)
    (hcov2 : ∀ u : ℤ, 1 ≤ (x u 2).toNat + (x (u - 1) 1 && x (u - 1) 3).toNat + (x (u - 2) 2 && x (u - 2) 4).toNat + (x (u - 3) 3 && x (u - 3) 5).toNat + (x (u - 4) 4 && x (u - 4) 6).toNat + (x (u - 5) 5 && x (u - 5) 7).toNat + (x (u - 6) 6 && x (u - 6) 8).toNat + (x (u - 7) 7 && x (u - 7) 9).toNat + (x (u - 8) 8 && x (u - 8) 10).toNat + (x (u - 9) 9 && x (u - 9) 11).toNat + (x (u - 10) 10 && x (u - 10) 12).toNat + (x (u - 11) 11 && x (u - 11) 13).toNat + (x (u - 12) 12 && x (u - 12) 14).toNat + (x (u - 13) 13).toNat)
    (hcov3 : ∀ u : ℤ, 1 ≤ (x u 3).toNat + (x (u - 1) 1 && x (u - 1) 4).toNat + (x (u - 2) 2 && x (u - 2) 5).toNat + (x (u - 3) 3 && x (u - 3) 6).toNat + (x (u - 4) 4 && x (u - 4) 7).toNat + (x (u - 5) 5 && x (u - 5) 8).toNat + (x (u - 6) 6 && x (u - 6) 9).toNat + (x (u - 7) 7 && x (u - 7) 10).toNat + (x (u - 8) 8 && x (u - 8) 11).toNat + (x (u - 9) 9 && x (u - 9) 12).toNat + (x (u - 10) 10 && x (u - 10) 13).toNat + (x (u - 11) 11 && x (u - 11) 14).toNat + (x (u - 12) 12).toNat)
    (hcov4 : ∀ u : ℤ, 1 ≤ (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat + (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3 && x (u - 3) 7).toNat + (x (u - 4) 4 && x (u - 4) 8).toNat + (x (u - 5) 5 && x (u - 5) 9).toNat + (x (u - 6) 6 && x (u - 6) 10).toNat + (x (u - 7) 7 && x (u - 7) 11).toNat + (x (u - 8) 8 && x (u - 8) 12).toNat + (x (u - 9) 9 && x (u - 9) 13).toNat + (x (u - 10) 10 && x (u - 10) 14).toNat + (x (u - 11) 11).toNat)
    (hcov5 : ∀ u : ℤ, 1 ≤ (x u 5).toNat + (x (u - 1) 1 && x (u - 1) 6).toNat + (x (u - 2) 2 && x (u - 2) 7).toNat + (x (u - 3) 3 && x (u - 3) 8).toNat + (x (u - 4) 4 && x (u - 4) 9).toNat + (x (u - 5) 5 && x (u - 5) 10).toNat + (x (u - 6) 6 && x (u - 6) 11).toNat + (x (u - 7) 7 && x (u - 7) 12).toNat + (x (u - 8) 8 && x (u - 8) 13).toNat + (x (u - 9) 9 && x (u - 9) 14).toNat + (x (u - 10) 10).toNat)
    (hcov6 : ∀ u : ℤ, 1 ≤ (x u 6).toNat + (x (u - 1) 1 && x (u - 1) 7).toNat + (x (u - 2) 2 && x (u - 2) 8).toNat + (x (u - 3) 3 && x (u - 3) 9).toNat + (x (u - 4) 4 && x (u - 4) 10).toNat + (x (u - 5) 5 && x (u - 5) 11).toNat + (x (u - 6) 6 && x (u - 6) 12).toNat + (x (u - 7) 7 && x (u - 7) 13).toNat + (x (u - 8) 8 && x (u - 8) 14).toNat + (x (u - 9) 9).toNat)
    (hcov7 : ∀ u : ℤ, 1 ≤ (x u 7).toNat + (x (u - 1) 1 && x (u - 1) 8).toNat + (x (u - 2) 2 && x (u - 2) 9).toNat + (x (u - 3) 3 && x (u - 3) 10).toNat + (x (u - 4) 4 && x (u - 4) 11).toNat + (x (u - 5) 5 && x (u - 5) 12).toNat + (x (u - 6) 6 && x (u - 6) 13).toNat + (x (u - 7) 7 && x (u - 7) 14).toNat + (x (u - 8) 8).toNat)
    (hcov9 : ∀ u : ℤ, 1 ≤ (x u 9).toNat + (x (u - 1) 1 && x (u - 1) 10).toNat + (x (u - 2) 2 && x (u - 2) 11).toNat + (x (u - 3) 3 && x (u - 3) 12).toNat + (x (u - 4) 4 && x (u - 4) 13).toNat + (x (u - 5) 5 && x (u - 5) 14).toNat + (x (u - 6) 6).toNat)
    (hcov10 : ∀ u : ℤ, 1 ≤ (x u 10).toNat + (x (u - 1) 1 && x (u - 1) 11).toNat + (x (u - 2) 2 && x (u - 2) 12).toNat + (x (u - 3) 3 && x (u - 3) 13).toNat + (x (u - 4) 4 && x (u - 4) 14).toNat + (x (u - 5) 5).toNat)
    (hcov11 : ∀ u : ℤ, 1 ≤ (x u 11).toNat + (x (u - 1) 1 && x (u - 1) 12).toNat + (x (u - 2) 2 && x (u - 2) 13).toNat + (x (u - 3) 3 && x (u - 3) 14).toNat + (x (u - 4) 4).toNat)
    (hcov13 : ∀ u : ℤ, 1 ≤ (x u 13).toNat + (x (u - 1) 1 && x (u - 1) 14).toNat + (x (u - 2) 2).toNat)
    (hp2 : ∀ p, x p 2 = true → x p 14 = true)
    (hp4 : ∀ p, x p 4 = true → x p 12 = true)
    (hp5 : ∀ p, x p 5 = true → x p 13 = true)
    (hp6 : ∀ p, x p 6 = true → x p 14 = true)
    (hp9 : ∀ p, x p 9 = true → x p 1 = true)
    (hp10 : ∀ p, x p 10 = true → x p 2 = true)
    (hp11 : ∀ p, x p 11 = true → x p 3 = true)
    (hp13 : ∀ p, x p 13 = true → x p 1 = true)
    (g0 : (x (-2) 3).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-1) 2).toNat = 0)
    (g3 : (x (-1) 3).toNat = 0)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 10).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x (-1) 13).toNat = 0)
    (g9 : (x 0 1).toNat = 1)
    (g10 : (x 0 2).toNat = 1)
    (g11 : (x 0 3).toNat = 0)
    (g12 : (x 0 4).toNat = 0)
    (g13 : (x 0 5).toNat = 0)
    (g14 : (x 0 6).toNat = 0)
    (g15 : (x 0 7).toNat = 0)
    (g16 : (x 0 8).toNat = 0)
    (g17 : (x 0 9).toNat = 0)
    (g18 : (x 0 11).toNat = 0)
    (g19 : (x 0 12).toNat = 0)
    (g20 : (x 0 13).toNat = 1)
    (g21 : (x 0 14).toNat = 1)
    (g22 : (x 1 2).toNat = 0)
    (g23 : (x 1 4).toNat = 0)
    (g24 : (x 1 5).toNat = 0)
    (g25 : (x 1 6).toNat = 0)
    (g26 : (x 1 10).toNat = 0)
    (g27 : (x 1 12).toNat = 0)
    (g28 : (x 1 13).toNat = 0)
    (g29 : (x 2 4).toNat = 0)
    (g30 : (x 2 12).toNat = 0)
    (g31 : (x 0 2 && x 0 4).toNat = 0)
    (g32 : (x (-1) 3 && x (-1) 5).toNat = 0)
    (g33 : (x 1 10 && x 1 12).toNat = 0)
    (g34 : (x 0 11 && x 0 13).toNat = 0)
    (g35 : (x 0 1 && x 0 4).toNat = 0)
    (g36 : (x (-1) 2 && x (-1) 5).toNat = 0)
    (g37 : (x (-2) 3 && x (-2) 6).toNat = 0)
    (g38 : (x 2 9 && x 2 12).toNat = 0)
    (g39 : (x 1 10 && x 1 13).toNat = 0)
    (g40 : (x 0 11 && x 0 14).toNat = 0)
    (g41 : (x 0 2 && x 0 6).toNat = 0)
    (g42 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g43 : (x 1 8 && x 1 12).toNat = 0)
    (g44 : (x 0 1 && x 0 6).toNat = 0)
    (g45 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g46 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g47 : (x 1 1 && x 1 6).toNat = 0)
    (g48 : (x 0 2 && x 0 7).toNat = 0)
    (g49 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g50 : (x 1 7 && x 1 12).toNat = 0)
    (g51 : (x 0 8 && x 0 13).toNat = 0)
    (g52 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g53 : (x 2 7 && x 2 12).toNat = 0)
    (g54 : (x 1 8 && x 1 13).toNat = 0)
    (g55 : (x 0 1 && x 0 7).toNat = 0)
    (g56 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g57 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g58 : (x 0 2 && x 0 8).toNat = 0)
    (g59 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g60 : (x 1 6 && x 1 12).toNat = 0)
    (g61 : (x 0 7 && x 0 13).toNat = 0)
    (g62 : (x 2 6 && x 2 12).toNat = 0)
    (g63 : (x 1 7 && x 1 13).toNat = 0)
    (g64 : (x 0 8 && x 0 14).toNat = 0)
    (g65 : (x 2 5 && x 2 12).toNat = 0)
    (g66 : (x 1 6 && x 1 13).toNat = 0)
    (g67 : (x 0 7 && x 0 14).toNat = 0)
    (g68 : (x 1 1 && x 1 10).toNat = 0)
    (g69 : (x 0 2 && x 0 11).toNat = 0)
    (g70 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g71 : (x 1 2 && x 1 11).toNat = 0)
    (g72 : (x 0 3 && x 0 12).toNat = 0)
    (g73 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g74 : (x 0 1 && x 0 11).toNat = 0)
    (g75 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g76 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g77 : (x 0 2 && x 0 12).toNat = 0)
    (g78 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g79 : (x 1 2 && x 1 12).toNat = 0)
    (g80 : (x 0 3 && x 0 13).toNat = 0)
    (g81 : (x 2 2 && x 2 12).toNat = 0)
    (g82 : (x 1 3 && x 1 13).toNat = 0)
    (g83 : (x 0 4 && x 0 14).toNat = 0)
    (g84 : (x 0 1 && x 0 12).toNat = 0)
    (g85 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g86 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g87 : (x 2 1 && x 2 12).toNat = 0)
    (g88 : (x 1 2 && x 1 13).toNat = 0)
    (g89 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d9303 : (x 0 9 && x 0 14).toNat = 0 := by
    have r9304 := hand1 (x 0 9) (x 0 14)
    have b9305 := hb (x 0 9)
    have b9306 := hb (x 0 9 && x 0 14)
    clear * - r9304 b9305 b9306 g17
    omega
  have d9307 : (x 0 9 && x 0 13).toNat = 0 := by
    have r9308 := hand1 (x 0 9) (x 0 13)
    have b9309 := hb (x 0 9)
    have b9310 := hb (x 0 9 && x 0 13)
    clear * - r9308 b9309 b9310 g17
    omega
  cases h9311 : x 0 10
  · have f9312 : (x 0 10).toNat = 0 := by rw [h9311]; rfl
    cases h9313 : x 1 1
    · have f9314 : (x 1 1).toNat = 0 := by rw [h9313]; rfl
      have d9315 : (x 1 1 && x 1 11).toNat = 0 := by
        have r9316 := hand1 (x 1 1) (x 1 11)
        have b9317 := hb (x 1 1)
        have b9318 := hb (x 1 1 && x 1 11)
        clear * - r9316 b9317 b9318 f9314
        omega
      have d9319 : (x 1 1 && x 1 7).toNat = 0 := by
        have r9320 := hand1 (x 1 1) (x 1 7)
        have b9321 := hb (x 1 1)
        have b9322 := hb (x 1 1 && x 1 7)
        clear * - r9320 b9321 b9322 f9314
        omega
      have d9323 : (x 1 1 && x 1 3).toNat = 0 := by
        have r9324 := hand1 (x 1 1) (x 1 3)
        have b9325 := hb (x 1 1)
        have b9326 := hb (x 1 1 && x 1 3)
        clear * - r9324 b9325 b9326 f9314
        omega
      have d9327 : (x 1 9).toNat = 0 := by
        have r9328 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
        have b9329 := hb (x 1 1)
        have b9330 := hb (x 1 9)
        clear * - r9328 b9329 b9330 f9314
        omega
      have d9331 : (x 2 14).toNat = 1 := by
        have r9332 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9333 := hb (x 1 1)
        have b9334 := hb (x 2 14)
        clear * - r9332 b9333 b9334 f9314
        omega
      cases h9335 : x 1 3
      · have f9336 : (x 1 3).toNat = 0 := by rw [h9335]; rfl
        have d9337 : (x 1 11).toNat = 0 := by
          have r9338 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b9339 := hb (x 1 3)
          have b9340 := hb (x 1 11)
          clear * - r9338 b9339 b9340 f9336
          omega
        have d9341 : (x (-3) 4).toNat = 1 := by
          have r9342 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9343 := hb (x (-3) 4)
          have b9344 := hb (x 1 11)
          have b9345 := hb (x 0 1 && x 0 12)
          have b9346 := hb (x (-1) 2 && x (-1) 13)
          have b9347 := hb (x (-2) 3 && x (-2) 14)
          clear * - r9342 b9343 b9344 b9345 b9346 b9347 d9337 g84 g85 g86
          omega
        have d9348 : (x (-3) 12).toNat = 1 := by
          have r9349 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b9350 := hb (x (-3) 4)
          have b9351 := hb (x (-3) 12)
          clear * - r9349 b9350 b9351 d9341
          omega
        have d9352 : (x (-4) 13).toNat = 0 := by
          have r9353 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9354 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e9355 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b9356 := hb (x (-6) 3)
          have b9357 := hb (x (-5) 2)
          have b9358 := hb (x (-4) 13)
          have b9359 := hb (x (-3) 12)
          clear * - r9353 e9354 e9355 b9356 b9357 b9358 b9359 d9348
          omega
        have d9360 : (x (-4) 5).toNat = 0 := by
          have r9361 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
          have b9362 := hb (x (-4) 5)
          have b9363 := hb (x (-4) 13)
          clear * - r9361 b9362 b9363 d9352
          omega
        have d9364 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
          have r9365 := hand1 (x (-4) 5) (x (-4) 11)
          have b9366 := hb (x (-4) 5)
          have b9367 := hb (x (-4) 5 && x (-4) 11)
          clear * - r9365 b9366 b9367 d9360
          omega
        have d9368 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
          have r9369 := hand1 (x (-4) 5) (x (-4) 10)
          have b9370 := hb (x (-4) 5)
          have b9371 := hb (x (-4) 5 && x (-4) 10)
          clear * - r9369 b9370 b9371 d9360
          omega
        have d9372 : (x (-4) 5 && x (-4) 8).toNat = 0 := by
          have r9373 := hand1 (x (-4) 5) (x (-4) 8)
          have b9374 := hb (x (-4) 5)
          have b9375 := hb (x (-4) 5 && x (-4) 8)
          clear * - r9373 b9374 b9375 d9360
          omega
        have d9376 : (x (-5) 2).toNat = 0 := by
          have r9377 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9378 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e9379 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b9380 := hb (x (-6) 3)
          have b9381 := hb (x (-5) 2)
          have b9382 := hb (x (-4) 13)
          have b9383 := hb (x (-3) 12)
          clear * - r9377 e9378 e9379 b9380 b9381 b9382 b9383 d9348 d9352
          omega
        have d9384 : (x (-5) 10).toNat = 0 := by
          have r9385 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
          have b9386 := hb (x (-5) 2)
          have b9387 := hb (x (-5) 10)
          clear * - r9385 b9386 b9387 d9376
          omega
        have d9388 : (x (-6) 3).toNat = 0 := by
          have r9389 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9390 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e9391 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b9392 := hb (x (-6) 3)
          have b9393 := hb (x (-5) 2)
          have b9394 := hb (x (-4) 13)
          have b9395 := hb (x (-3) 12)
          clear * - r9389 e9390 e9391 b9392 b9393 b9394 b9395 d9348 d9352 d9376
          omega
        have d9396 : (x (-6) 11).toNat = 0 := by
          have r9397 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
          have b9398 := hb (x (-6) 3)
          have b9399 := hb (x (-6) 11)
          clear * - r9397 b9398 b9399 d9388
          omega
        have d9400 : (x (-6) 1 && x (-6) 11).toNat = 0 := by
          have r9401 := hand2 (x (-6) 1) (x (-6) 11)
          have b9402 := hb (x (-6) 11)
          have b9403 := hb (x (-6) 1 && x (-6) 11)
          clear * - r9401 b9402 b9403 d9396
          omega
        have d9404 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
          have r9405 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9406 := hb (x (-4) 5)
          have b9407 := hb (x 1 10)
          have b9408 := hb (x 0 1 && x 0 11)
          have b9409 := hb (x (-1) 2 && x (-1) 12)
          have b9410 := hb (x (-2) 3 && x (-2) 13)
          have b9411 := hb (x (-3) 4 && x (-3) 14)
          clear * - r9405 b9406 b9407 b9408 b9409 b9410 b9411 g26 g74 g75 g76 d9360
          omega
        have d9412 : (x (-3) 14).toNat = 1 := by
          have r9413 := hand2 (x (-3) 4) (x (-3) 14)
          have b9414 := hb (x (-3) 14)
          have b9415 := hb (x (-3) 4 && x (-3) 14)
          clear * - r9413 b9414 b9415 d9404
          omega
        have d9416 : (x (-4) 1).toNat = 0 := by
          have r9417 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9418 := hb (x (-4) 1)
          have b9419 := hb (x (-3) 14)
          clear * - r9417 b9418 b9419 d9412
          omega
        have d9420 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
          have r9421 := hand1 (x (-4) 1) (x (-4) 14)
          have b9422 := hb (x (-4) 1)
          have b9423 := hb (x (-4) 1 && x (-4) 14)
          clear * - r9421 b9422 b9423 d9416
          omega
        have d9424 : (x (-3) 13).toNat = 1 := by
          have r9425 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9426 := hb (x (-5) 2)
          have b9427 := hb (x (-3) 13)
          have b9428 := hb (x (-4) 1 && x (-4) 14)
          clear * - r9425 b9426 b9427 b9428 d9420 d9376
          omega
        have d9429 : (x (-3) 1).toNat = 1 := by
          have r9430 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b9431 := hb (x (-3) 1)
          have b9432 := hb (x (-3) 13)
          clear * - r9430 b9431 b9432 d9424
          omega
        have d9433 : (x (-2) 14).toNat = 0 := by
          have r9434 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9435 := hb (x (-3) 1)
          have b9436 := hb (x (-2) 14)
          clear * - r9434 b9435 b9436 d9429
          omega
        have d9437 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r9438 := hand2 (x (-2) 1) (x (-2) 14)
          have b9439 := hb (x (-2) 14)
          have b9440 := hb (x (-2) 1 && x (-2) 14)
          clear * - r9438 b9439 b9440 d9433
          omega
        have d9441 : (x (-3) 2).toNat = 1 := by
          have r9442 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9443 := hb (x (-3) 2)
          have b9444 := hb (x (-1) 13)
          have b9445 := hb (x (-2) 1 && x (-2) 14)
          clear * - r9442 b9443 b9444 b9445 g8 d9437
          omega
        have d9446 : (x (-1) 12).toNat = 0 := by
          have r9447 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9448 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e9449 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b9450 := hb (x (-4) 3)
          have b9451 := hb (x (-3) 2)
          have b9452 := hb (x (-2) 13)
          have b9453 := hb (x (-1) 12)
          clear * - r9447 e9448 e9449 b9450 b9451 b9452 b9453 d9441
          omega
        have d9454 : (x (-1) 12 && x (-1) 14).toNat = 0 := by
          have r9455 := hand1 (x (-1) 12) (x (-1) 14)
          have b9456 := hb (x (-1) 12)
          have b9457 := hb (x (-1) 12 && x (-1) 14)
          clear * - r9455 b9456 b9457 d9446
          omega
        have d9458 : (x (-1) 4).toNat = 0 := by
          have r9459 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b9460 := hb (x (-1) 4)
          have b9461 := hb (x (-1) 12)
          clear * - r9459 b9460 b9461 d9446
          omega
        have d9462 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
          have r9463 := hand1 (x (-1) 4) (x (-1) 14)
          have b9464 := hb (x (-1) 4)
          have b9465 := hb (x (-1) 4 && x (-1) 14)
          clear * - r9463 b9464 b9465 d9458
          omega
        have d9466 : (x 3 11).toNat = 1 := by
          have r9467 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9468 := hb (x (-1) 4)
          have b9469 := hb (x 3 11)
          have b9470 := hb (x 2 1 && x 2 12)
          have b9471 := hb (x 1 2 && x 1 13)
          have b9472 := hb (x 0 3 && x 0 14)
          clear * - r9467 b9468 b9469 b9470 b9471 b9472 g87 g88 g89 d9458
          omega
        have d9473 : (x 3 3).toNat = 1 := by
          have r9474 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b9475 := hb (x 3 3)
          have b9476 := hb (x 3 11)
          clear * - r9474 b9475 b9476 d9466
          omega
        have d9477 : (x 6 12).toNat = 0 := by
          have r9478 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9479 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e9480 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b9481 := hb (x 3 3)
          have b9482 := hb (x 4 2)
          have b9483 := hb (x 5 13)
          have b9484 := hb (x 6 12)
          clear * - r9478 e9479 e9480 b9481 b9482 b9483 b9484 d9473
          omega
        have d9485 : (x 6 1 && x 6 12).toNat = 0 := by
          have r9486 := hand2 (x 6 1) (x 6 12)
          have b9487 := hb (x 6 12)
          have b9488 := hb (x 6 1 && x 6 12)
          clear * - r9486 b9487 b9488 d9477
          omega
        have d9489 : (x 6 2 && x 6 12).toNat = 0 := by
          have r9490 := hand2 (x 6 2) (x 6 12)
          have b9491 := hb (x 6 12)
          have b9492 := hb (x 6 2 && x 6 12)
          clear * - r9490 b9491 b9492 d9477
          omega
        have d9493 : (x 6 4).toNat = 0 := by
          have r9494 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b9495 := hb (x 6 4)
          have b9496 := hb (x 6 12)
          clear * - r9494 b9495 b9496 d9477
          omega
        have d9497 : (x 6 4 && x 6 10).toNat = 0 := by
          have r9498 := hand1 (x 6 4) (x 6 10)
          have b9499 := hb (x 6 4)
          have b9500 := hb (x 6 4 && x 6 10)
          clear * - r9498 b9499 b9500 d9493
          omega
        have d9501 : (x 5 13).toNat = 0 := by
          have r9502 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9503 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e9504 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b9505 := hb (x 3 3)
          have b9506 := hb (x 4 2)
          have b9507 := hb (x 5 13)
          have b9508 := hb (x 6 12)
          clear * - r9502 e9503 e9504 b9505 b9506 b9507 b9508 d9477 d9473
          omega
        have d9509 : (x 5 2 && x 5 13).toNat = 0 := by
          have r9510 := hand2 (x 5 2) (x 5 13)
          have b9511 := hb (x 5 13)
          have b9512 := hb (x 5 2 && x 5 13)
          clear * - r9510 b9511 b9512 d9501
          omega
        have d9513 : (x 5 3 && x 5 13).toNat = 0 := by
          have r9514 := hand2 (x 5 3) (x 5 13)
          have b9515 := hb (x 5 13)
          have b9516 := hb (x 5 3 && x 5 13)
          clear * - r9514 b9515 b9516 d9501
          omega
        have d9517 : (x 5 5).toNat = 0 := by
          have r9518 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
          have b9519 := hb (x 5 5)
          have b9520 := hb (x 5 13)
          clear * - r9518 b9519 b9520 d9501
          omega
        have d9521 : (x 5 5 && x 5 11).toNat = 0 := by
          have r9522 := hand1 (x 5 5) (x 5 11)
          have b9523 := hb (x 5 5)
          have b9524 := hb (x 5 5 && x 5 11)
          clear * - r9522 b9523 b9524 d9517
          omega
        have d9525 : (x 4 2).toNat = 0 := by
          have r9526 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9527 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e9528 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b9529 := hb (x 3 3)
          have b9530 := hb (x 4 2)
          have b9531 := hb (x 5 13)
          have b9532 := hb (x 6 12)
          clear * - r9526 e9527 e9528 b9529 b9530 b9531 b9532 d9477 d9501 d9473
          omega
        have d9533 : (x 4 10).toNat = 0 := by
          have r9534 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
          have b9535 := hb (x 4 2)
          have b9536 := hb (x 4 10)
          clear * - r9534 b9535 b9536 d9525
          omega
        have d9537 : (x 4 3 && x 4 10).toNat = 0 := by
          have r9538 := hand2 (x 4 3) (x 4 10)
          have b9539 := hb (x 4 10)
          have b9540 := hb (x 4 3 && x 4 10)
          clear * - r9538 b9539 b9540 d9533
          omega
        have d9541 : (x 4 4 && x 4 10).toNat = 0 := by
          have r9542 := hand2 (x 4 4) (x 4 10)
          have b9543 := hb (x 4 10)
          have b9544 := hb (x 4 4 && x 4 10)
          clear * - r9542 b9543 b9544 d9533
          omega
        have d9545 : (x 4 5 && x 4 10).toNat = 0 := by
          have r9546 := hand2 (x 4 5) (x 4 10)
          have b9547 := hb (x 4 10)
          have b9548 := hb (x 4 5 && x 4 10)
          clear * - r9546 b9547 b9548 d9533
          omega
        have d9549 : (x 4 7 && x 4 10).toNat = 0 := by
          have r9550 := hand2 (x 4 7) (x 4 10)
          have b9551 := hb (x 4 10)
          have b9552 := hb (x 4 7 && x 4 10)
          clear * - r9550 b9551 b9552 d9533
          omega
        have d9553 : (x 3 1 && x 3 11).toNat = 1 := by
          have r9554 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9555 := hb (x (-1) 5)
          have b9556 := hb (x 4 10)
          have b9557 := hb (x 3 1 && x 3 11)
          have b9558 := hb (x 2 2 && x 2 12)
          have b9559 := hb (x 1 3 && x 1 13)
          have b9560 := hb (x 0 4 && x 0 14)
          clear * - r9554 b9555 b9556 b9557 b9558 b9559 b9560 d9533 g81 g82 g83 g4
          omega
        have d9561 : (x 3 1).toNat = 1 := by
          have r9562 := hand1 (x 3 1) (x 3 11)
          have b9563 := hb (x 3 1)
          have b9564 := hb (x 3 1 && x 3 11)
          clear * - r9562 b9563 b9564 d9553
          omega
        have d9565 : (x 4 14).toNat = 0 := by
          have r9566 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9567 := hb (x 3 1)
          have b9568 := hb (x 4 14)
          clear * - r9566 b9567 b9568 d9561
          omega
        have d9569 : (x 4 1 && x 4 14).toNat = 0 := by
          have r9570 := hand2 (x 4 1) (x 4 14)
          have b9571 := hb (x 4 14)
          have b9572 := hb (x 4 1 && x 4 14)
          clear * - r9570 b9571 b9572 d9565
          omega
        have d9573 : (x 3 2).toNat = 1 := by
          have r9574 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9575 := hb (x 3 2)
          have b9576 := hb (x 5 13)
          have b9577 := hb (x 4 1 && x 4 14)
          clear * - r9574 b9575 b9576 b9577 d9501 d9569
          omega
        have d9578 : (x 3 14).toNat = 1 := by
          have r9579 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
          have b9580 := hb (x 3 2)
          have b9581 := hb (x 3 14)
          clear * - r9579 b9580 b9581 d9573
          omega
        have d9582 : (x 2 1).toNat = 0 := by
          have r9583 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9584 := hb (x 2 1)
          have b9585 := hb (x 3 14)
          clear * - r9583 b9584 b9585 d9578
          omega
        have d9586 : (x 2 1 && x 2 14).toNat = 0 := by
          have r9587 := hand1 (x 2 1) (x 2 14)
          have b9588 := hb (x 2 1)
          have b9589 := hb (x 2 1 && x 2 14)
          clear * - r9587 b9588 b9589 d9582
          omega
        have d9590 : (x 3 13).toNat = 1 := by
          have r9591 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9592 := hb (x 1 2)
          have b9593 := hb (x 3 13)
          have b9594 := hb (x 2 1 && x 2 14)
          clear * - r9591 b9592 b9593 b9594 d9586 g22
          omega
        have d9595 : (x 4 12).toNat = 0 := by
          have r9596 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9597 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e9598 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b9599 := hb (x 1 3)
          have b9600 := hb (x 2 2)
          have b9601 := hb (x 3 13)
          have b9602 := hb (x 4 12)
          clear * - r9596 e9597 e9598 b9599 b9600 b9601 b9602 d9590 f9336
          omega
        have d9603 : (x 4 6 && x 4 12).toNat = 0 := by
          have r9604 := hand2 (x 4 6) (x 4 12)
          have b9605 := hb (x 4 12)
          have b9606 := hb (x 4 6 && x 4 12)
          clear * - r9604 b9605 b9606 d9595
          omega
        have d9607 : (x 4 7 && x 4 12).toNat = 0 := by
          have r9608 := hand2 (x 4 7) (x 4 12)
          have b9609 := hb (x 4 12)
          have b9610 := hb (x 4 7 && x 4 12)
          clear * - r9608 b9609 b9610 d9595
          omega
        have d9611 : (x 4 4).toNat = 0 := by
          have r9612 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b9613 := hb (x 4 4)
          have b9614 := hb (x 4 12)
          clear * - r9612 b9613 b9614 d9595
          omega
        have d9615 : (x 4 4 && x 4 14).toNat = 0 := by
          have r9616 := hand1 (x 4 4) (x 4 14)
          have b9617 := hb (x 4 4)
          have b9618 := hb (x 4 4 && x 4 14)
          clear * - r9616 b9617 b9618 d9611
          omega
        have d9619 : (x 4 4 && x 4 9).toNat = 0 := by
          have r9620 := hand1 (x 4 4) (x 4 9)
          have b9621 := hb (x 4 4)
          have b9622 := hb (x 4 4 && x 4 9)
          clear * - r9620 b9621 b9622 d9611
          omega
        have d9623 : (x 2 2).toNat = 0 := by
          have r9624 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9625 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e9626 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b9627 := hb (x 1 3)
          have b9628 := hb (x 2 2)
          have b9629 := hb (x 3 13)
          have b9630 := hb (x 4 12)
          clear * - r9624 e9625 e9626 b9627 b9628 b9629 b9630 d9595 d9590 f9336
          omega
        have d9631 : (x 2 10).toNat = 0 := by
          have r9632 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
          have b9633 := hb (x 2 2)
          have b9634 := hb (x 2 10)
          clear * - r9632 b9633 b9634 d9623
          omega
        have d9635 : (x 2 1 && x 2 10).toNat = 0 := by
          have r9636 := hand2 (x 2 1) (x 2 10)
          have b9637 := hb (x 2 10)
          have b9638 := hb (x 2 1 && x 2 10)
          clear * - r9636 b9637 b9638 d9631
          omega
        have d9639 : (x 2 1 && x 2 11).toNat = 0 := by
          have r9640 := hand1 (x 2 1) (x 2 11)
          have b9641 := hb (x 2 1)
          have b9642 := hb (x 2 1 && x 2 11)
          clear * - r9640 b9641 b9642 d9582
          omega
        have d9643 : (x 2 13).toNat = 0 := by
          have r9644 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
          have b9645 := hb (x 2 1)
          have b9646 := hb (x 2 13)
          clear * - r9644 b9645 b9646 d9582
          omega
        have d9647 : (x 2 9 && x 2 13).toNat = 0 := by
          have r9648 := hand2 (x 2 9) (x 2 13)
          have b9649 := hb (x 2 13)
          have b9650 := hb (x 2 9 && x 2 13)
          clear * - r9648 b9649 b9650 d9643
          omega
        have d9651 : (x 2 5).toNat = 0 := by
          have r9652 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
          have b9653 := hb (x 2 5)
          have b9654 := hb (x 2 13)
          clear * - r9652 b9653 b9654 d9643
          omega
        have d9655 : (x 2 5 && x 2 11).toNat = 0 := by
          have r9656 := hand1 (x 2 5) (x 2 11)
          have b9657 := hb (x 2 5)
          have b9658 := hb (x 2 5 && x 2 11)
          clear * - r9656 b9657 b9658 d9651
          omega
        have d9659 : (x 2 9).toNat = 0 := by
          have r9660 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
          have b9661 := hb (x 2 1)
          have b9662 := hb (x 2 9)
          clear * - r9660 b9661 b9662 d9582
          omega
        have d9663 : (x 2 9 && x 2 14).toNat = 0 := by
          have r9664 := hand1 (x 2 9) (x 2 14)
          have b9665 := hb (x 2 9)
          have b9666 := hb (x 2 9 && x 2 14)
          clear * - r9664 b9665 b9666 d9659
          omega
        have d9667 : (x 2 9 && x 2 11).toNat = 0 := by
          have r9668 := hand1 (x 2 9) (x 2 11)
          have b9669 := hb (x 2 9)
          have b9670 := hb (x 2 9 && x 2 11)
          clear * - r9668 b9669 b9670 d9659
          omega
        have d9671 : (x 5 12).toNat = 0 := by
          have r9672 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9673 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e9674 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b9675 := hb (x 2 3)
          have b9676 := hb (x 3 2)
          have b9677 := hb (x 4 13)
          have b9678 := hb (x 5 12)
          clear * - r9672 e9673 e9674 b9675 b9676 b9677 b9678 d9573
          omega
        have d9679 : (x 5 4).toNat = 0 := by
          have r9680 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b9681 := hb (x 5 4)
          have b9682 := hb (x 5 12)
          clear * - r9680 b9681 b9682 d9671
          omega
        have d9683 : (x 5 4 && x 5 9).toNat = 0 := by
          have r9684 := hand1 (x 5 4) (x 5 9)
          have b9685 := hb (x 5 4)
          have b9686 := hb (x 5 4 && x 5 9)
          clear * - r9684 b9685 b9686 d9679
          omega
        have d9687 : (x 5 4 && x 5 8).toNat = 0 := by
          have r9688 := hand1 (x 5 4) (x 5 8)
          have b9689 := hb (x 5 4)
          have b9690 := hb (x 5 4 && x 5 8)
          clear * - r9688 b9689 b9690 d9679
          omega
        have d9691 : (x 4 13).toNat = 0 := by
          have r9692 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9693 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e9694 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b9695 := hb (x 2 3)
          have b9696 := hb (x 3 2)
          have b9697 := hb (x 4 13)
          have b9698 := hb (x 5 12)
          clear * - r9692 e9693 e9694 b9695 b9696 b9697 b9698 d9671 d9573
          omega
        have d9699 : (x 4 5).toNat = 0 := by
          have r9700 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
          have b9701 := hb (x 4 5)
          have b9702 := hb (x 4 13)
          clear * - r9700 b9701 b9702 d9691
          omega
        have d9703 : (x 4 5 && x 4 9).toNat = 0 := by
          have r9704 := hand1 (x 4 5) (x 4 9)
          have b9705 := hb (x 4 5)
          have b9706 := hb (x 4 5 && x 4 9)
          clear * - r9704 b9705 b9706 d9699
          omega
        have d9707 : (x 2 3).toNat = 0 := by
          have r9708 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9709 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e9710 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b9711 := hb (x 2 3)
          have b9712 := hb (x 3 2)
          have b9713 := hb (x 4 13)
          have b9714 := hb (x 5 12)
          clear * - r9708 e9709 e9710 b9711 b9712 b9713 b9714 d9671 d9691 d9573
          omega
        have d9715 : (x 2 11).toNat = 0 := by
          have r9716 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
          have b9717 := hb (x 2 3)
          have b9718 := hb (x 2 11)
          clear * - r9716 b9717 b9718 d9707
          omega
        have d9719 : (x 2 6 && x 2 11).toNat = 0 := by
          have r9720 := hand2 (x 2 6) (x 2 11)
          have b9721 := hb (x 2 11)
          have b9722 := hb (x 2 6 && x 2 11)
          clear * - r9720 b9721 b9722 d9715
          omega
        have d9723 : (x 2 7 && x 2 11).toNat = 0 := by
          have r9724 := hand2 (x 2 7) (x 2 11)
          have b9725 := hb (x 2 11)
          have b9726 := hb (x 2 7 && x 2 11)
          clear * - r9724 b9725 b9726 d9715
          omega
        have d9727 : (x 4 3 && x 4 14).toNat = 0 := by
          have r9728 := hand2 (x 4 3) (x 4 14)
          have b9729 := hb (x 4 14)
          have b9730 := hb (x 4 3 && x 4 14)
          clear * - r9728 b9729 b9730 d9565
          omega
        have d9731 : (x 4 6).toNat = 0 := by
          have r9732 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
          have b9733 := hb (x 4 6)
          have b9734 := hb (x 4 14)
          clear * - r9732 b9733 b9734 d9565
          omega
        have d9735 : (x (-2) 13).toNat = 0 := by
          have r9736 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9737 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e9738 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b9739 := hb (x (-4) 3)
          have b9740 := hb (x (-3) 2)
          have b9741 := hb (x (-2) 13)
          have b9742 := hb (x (-1) 12)
          clear * - r9736 e9737 e9738 b9739 b9740 b9741 b9742 d9446 d9441
          omega
        have d9743 : (x (-2) 5).toNat = 0 := by
          have r9744 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b9745 := hb (x (-2) 5)
          have b9746 := hb (x (-2) 13)
          clear * - r9744 b9745 b9746 d9735
          omega
        have d9747 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
          have r9748 := hand1 (x (-2) 5) (x (-2) 14)
          have b9749 := hb (x (-2) 5)
          have b9750 := hb (x (-2) 5 && x (-2) 14)
          clear * - r9748 b9749 b9750 d9743
          omega
        have d9751 : (x 3 10).toNat = 1 := by
          have r9752 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9753 := hb (x (-2) 5)
          have b9754 := hb (x 3 10)
          have b9755 := hb (x 2 1 && x 2 11)
          have b9756 := hb (x 1 2 && x 1 12)
          have b9757 := hb (x 0 3 && x 0 13)
          have b9758 := hb (x (-1) 4 && x (-1) 14)
          clear * - r9752 b9753 b9754 b9755 b9756 b9757 b9758 d9639 g79 g80 d9462 d9743
          omega
        have d9759 : (x (-4) 3).toNat = 0 := by
          have r9760 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9761 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e9762 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b9763 := hb (x (-4) 3)
          have b9764 := hb (x (-3) 2)
          have b9765 := hb (x (-2) 13)
          have b9766 := hb (x (-1) 12)
          clear * - r9760 e9761 e9762 b9763 b9764 b9765 b9766 d9446 d9735 d9441
          omega
        have d9767 : (x (-4) 11).toNat = 0 := by
          have r9768 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b9769 := hb (x (-4) 3)
          have b9770 := hb (x (-4) 11)
          clear * - r9768 b9769 b9770 d9759
          omega
        have d9771 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
          have r9772 := hand2 (x (-4) 6) (x (-4) 11)
          have b9773 := hb (x (-4) 11)
          have b9774 := hb (x (-4) 6 && x (-4) 11)
          clear * - r9772 b9773 b9774 d9767
          omega
        have d9775 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
          have r9776 := hand2 (x (-2) 4) (x (-2) 14)
          have b9777 := hb (x (-2) 14)
          have b9778 := hb (x (-2) 4 && x (-2) 14)
          clear * - r9776 b9777 b9778 d9433
          omega
        have d9779 : (x (-3) 5).toNat = 1 := by
          have r9780 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b9781 := hb (x (-3) 5)
          have b9782 := hb (x 2 10)
          have b9783 := hb (x 1 1 && x 1 11)
          have b9784 := hb (x 0 2 && x 0 12)
          have b9785 := hb (x (-1) 3 && x (-1) 13)
          have b9786 := hb (x (-2) 4 && x (-2) 14)
          clear * - r9780 b9781 b9782 b9783 b9784 b9785 b9786 d9631 d9315 g77 g78 d9775
          omega
        have d9787 : (x (-2) 6).toNat = 0 := by
          have r9788 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
          have b9789 := hb (x (-2) 6)
          have b9790 := hb (x (-2) 14)
          clear * - r9788 b9789 b9790 d9433
          omega
        have d9791 : (x (-2) 2 && x (-2) 6).toNat = 0 := by
          have r9792 := hand2 (x (-2) 2) (x (-2) 6)
          have b9793 := hb (x (-2) 6)
          have b9794 := hb (x (-2) 2 && x (-2) 6)
          clear * - r9792 b9793 b9794 d9787
          omega
        have d9795 : (x (-2) 4 && x (-2) 6).toNat = 0 := by
          have r9796 := hand2 (x (-2) 4) (x (-2) 6)
          have b9797 := hb (x (-2) 6)
          have b9798 := hb (x (-2) 4 && x (-2) 6)
          clear * - r9796 b9797 b9798 d9787
          omega
        have d9799 : (x (-2) 2).toNat = 0 := by
          have r9800 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
          have b9801 := hb (x (-2) 2)
          have b9802 := hb (x (-2) 14)
          clear * - r9800 b9801 b9802 d9433
          omega
        have d9803 : (x (-2) 10).toNat = 0 := by
          have r9804 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
          have b9805 := hb (x (-2) 2)
          have b9806 := hb (x (-2) 10)
          clear * - r9804 b9805 b9806 d9799
          omega
        have d9807 : (x (-2) 4 && x (-2) 10).toNat = 0 := by
          have r9808 := hand2 (x (-2) 4) (x (-2) 10)
          have b9809 := hb (x (-2) 10)
          have b9810 := hb (x (-2) 4 && x (-2) 10)
          clear * - r9808 b9809 b9810 d9803
          omega
        have d9811 : (x (-2) 12).toNat = 0 := by
          have r9812 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9813 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e9814 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b9815 := hb (x (-5) 3)
          have b9816 := hb (x (-4) 2)
          have b9817 := hb (x (-3) 13)
          have b9818 := hb (x (-2) 12)
          clear * - r9812 e9813 e9814 b9815 b9816 b9817 b9818 d9424
          omega
        have d9819 : (x (-2) 4).toNat = 0 := by
          have r9820 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
          have b9821 := hb (x (-2) 4)
          have b9822 := hb (x (-2) 12)
          clear * - r9820 b9821 b9822 d9811
          omega
        have d9823 : (x (-2) 4 && x (-2) 9).toNat = 0 := by
          have r9824 := hand1 (x (-2) 4) (x (-2) 9)
          have b9825 := hb (x (-2) 4)
          have b9826 := hb (x (-2) 4 && x (-2) 9)
          clear * - r9824 b9825 b9826 d9819
          omega
        have d9827 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
          have r9828 := hand1 (x (-2) 4) (x (-2) 8)
          have b9829 := hb (x (-2) 4)
          have b9830 := hb (x (-2) 4 && x (-2) 8)
          clear * - r9828 b9829 b9830 d9819
          omega
        have d9831 : (x (-4) 2).toNat = 0 := by
          have r9832 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9833 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e9834 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b9835 := hb (x (-5) 3)
          have b9836 := hb (x (-4) 2)
          have b9837 := hb (x (-3) 13)
          have b9838 := hb (x (-2) 12)
          clear * - r9832 e9833 e9834 b9835 b9836 b9837 b9838 d9811 d9424
          omega
        have d9839 : (x (-4) 10).toNat = 0 := by
          have r9840 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
          have b9841 := hb (x (-4) 2)
          have b9842 := hb (x (-4) 10)
          clear * - r9840 b9841 b9842 d9831
          omega
        have d9843 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
          have r9844 := hand2 (x (-4) 6) (x (-4) 10)
          have b9845 := hb (x (-4) 10)
          have b9846 := hb (x (-4) 6 && x (-4) 10)
          clear * - r9844 b9845 b9846 d9839
          omega
        have d9847 : (x (-5) 3).toNat = 0 := by
          have r9848 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9849 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e9850 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b9851 := hb (x (-5) 3)
          have b9852 := hb (x (-4) 2)
          have b9853 := hb (x (-3) 13)
          have b9854 := hb (x (-2) 12)
          clear * - r9848 e9849 e9850 b9851 b9852 b9853 b9854 d9811 d9424 d9831
          omega
        have d9855 : (x (-5) 11).toNat = 0 := by
          have r9856 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
          have b9857 := hb (x (-5) 3)
          have b9858 := hb (x (-5) 11)
          clear * - r9856 b9857 b9858 d9847
          omega
        have d9859 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
          have r9860 := hand2 (x (-5) 6) (x (-5) 11)
          have b9861 := hb (x (-5) 11)
          have b9862 := hb (x (-5) 6 && x (-5) 11)
          clear * - r9860 b9861 b9862 d9855
          omega
        have d9863 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
          have r9864 := hand2 (x (-5) 7) (x (-5) 11)
          have b9865 := hb (x (-5) 11)
          have b9866 := hb (x (-5) 7 && x (-5) 11)
          clear * - r9864 b9865 b9866 d9855
          omega
        have d9867 : (x 6 8).toNat = 0 := by
          have r9868 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9869 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e9870 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e9871 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e9872 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e9873 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e9874 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b9875 := hb (x (-1) 7)
          have b9876 := hb (x 0 6)
          have b9877 := hb (x 1 5)
          have b9878 := hb (x 2 4)
          have b9879 := hb (x 3 11)
          have b9880 := hb (x 4 10)
          have b9881 := hb (x 5 9)
          have b9882 := hb (x 6 8)
          clear * - r9868 e9869 e9870 e9871 e9872 e9873 e9874 b9875 b9876 b9877 b9878 b9879 b9880 b9881 b9882 d9533 d9466 g29 g24 g14
          omega
        have d9883 : (x 6 1 && x 6 8).toNat = 0 := by
          have r9884 := hand2 (x 6 1) (x 6 8)
          have b9885 := hb (x 6 8)
          have b9886 := hb (x 6 1 && x 6 8)
          clear * - r9884 b9885 b9886 d9867
          omega
        have d9887 : (x 6 2 && x 6 8).toNat = 0 := by
          have r9888 := hand2 (x 6 2) (x 6 8)
          have b9889 := hb (x 6 8)
          have b9890 := hb (x 6 2 && x 6 8)
          clear * - r9888 b9889 b9890 d9867
          omega
        have d9891 : (x 6 3 && x 6 8).toNat = 0 := by
          have r9892 := hand2 (x 6 3) (x 6 8)
          have b9893 := hb (x 6 8)
          have b9894 := hb (x 6 3 && x 6 8)
          clear * - r9892 b9893 b9894 d9867
          omega
        have d9895 : (x 6 5 && x 6 8).toNat = 0 := by
          have r9896 := hand2 (x 6 5) (x 6 8)
          have b9897 := hb (x 6 8)
          have b9898 := hb (x 6 5 && x 6 8)
          clear * - r9896 b9897 b9898 d9867
          omega
        have d9899 : (x 5 9).toNat = 0 := by
          have r9900 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9901 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e9902 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e9903 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e9904 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e9905 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e9906 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b9907 := hb (x (-1) 7)
          have b9908 := hb (x 0 6)
          have b9909 := hb (x 1 5)
          have b9910 := hb (x 2 4)
          have b9911 := hb (x 3 11)
          have b9912 := hb (x 4 10)
          have b9913 := hb (x 5 9)
          have b9914 := hb (x 6 8)
          clear * - r9900 e9901 e9902 e9903 e9904 e9905 e9906 b9907 b9908 b9909 b9910 b9911 b9912 b9913 b9914 d9867 d9533 d9466 g29 g24 g14
          omega
        have d9915 : (x 5 2 && x 5 9).toNat = 0 := by
          have r9916 := hand2 (x 5 2) (x 5 9)
          have b9917 := hb (x 5 9)
          have b9918 := hb (x 5 2 && x 5 9)
          clear * - r9916 b9917 b9918 d9899
          omega
        have d9919 : (x 5 3 && x 5 9).toNat = 0 := by
          have r9920 := hand2 (x 5 3) (x 5 9)
          have b9921 := hb (x 5 9)
          have b9922 := hb (x 5 3 && x 5 9)
          clear * - r9920 b9921 b9922 d9899
          omega
        have d9923 : (x 5 6 && x 5 9).toNat = 0 := by
          have r9924 := hand2 (x 5 6) (x 5 9)
          have b9925 := hb (x 5 9)
          have b9926 := hb (x 5 6 && x 5 9)
          clear * - r9924 b9925 b9926 d9899
          omega
        have d9927 : (x 5 8).toNat = 0 := by
          have r9928 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9929 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e9930 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e9931 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e9932 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e9933 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e9934 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b9935 := hb (x (-2) 7)
          have b9936 := hb (x (-1) 6)
          have b9937 := hb (x 0 5)
          have b9938 := hb (x 1 4)
          have b9939 := hb (x 2 11)
          have b9940 := hb (x 3 10)
          have b9941 := hb (x 4 9)
          have b9942 := hb (x 5 8)
          clear * - r9928 e9929 e9930 e9931 e9932 e9933 e9934 b9935 b9936 b9937 b9938 b9939 b9940 b9941 b9942 d9751 d9715 g23 g13
          omega
        have d9943 : (x 5 2 && x 5 8).toNat = 0 := by
          have r9944 := hand2 (x 5 2) (x 5 8)
          have b9945 := hb (x 5 8)
          have b9946 := hb (x 5 2 && x 5 8)
          clear * - r9944 b9945 b9946 d9927
          omega
        have d9947 : (x 5 3 && x 5 8).toNat = 0 := by
          have r9948 := hand2 (x 5 3) (x 5 8)
          have b9949 := hb (x 5 8)
          have b9950 := hb (x 5 3 && x 5 8)
          clear * - r9948 b9949 b9950 d9927
          omega
        have d9951 : (x 5 6 && x 5 8).toNat = 0 := by
          have r9952 := hand2 (x 5 6) (x 5 8)
          have b9953 := hb (x 5 8)
          have b9954 := hb (x 5 6 && x 5 8)
          clear * - r9952 b9953 b9954 d9927
          omega
        have d9955 : (x 4 9).toNat = 0 := by
          have r9956 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9957 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e9958 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e9959 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e9960 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e9961 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e9962 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b9963 := hb (x (-2) 7)
          have b9964 := hb (x (-1) 6)
          have b9965 := hb (x 0 5)
          have b9966 := hb (x 1 4)
          have b9967 := hb (x 2 11)
          have b9968 := hb (x 3 10)
          have b9969 := hb (x 4 9)
          have b9970 := hb (x 5 8)
          clear * - r9956 e9957 e9958 e9959 e9960 e9961 e9962 b9963 b9964 b9965 b9966 b9967 b9968 b9969 b9970 d9927 d9751 d9715 g23 g13
          omega
        have d9971 : (x 4 3 && x 4 9).toNat = 0 := by
          have r9972 := hand2 (x 4 3) (x 4 9)
          have b9973 := hb (x 4 9)
          have b9974 := hb (x 4 3 && x 4 9)
          clear * - r9972 b9973 b9974 d9955
          omega
        have d9975 : (x 4 7 && x 4 9).toNat = 0 := by
          have r9976 := hand2 (x 4 7) (x 4 9)
          have b9977 := hb (x 4 9)
          have b9978 := hb (x 4 7 && x 4 9)
          clear * - r9976 b9977 b9978 d9955
          omega
        have d9979 : (x 2 8).toNat = 0 := by
          have r9980 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e9981 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e9982 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e9983 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e9984 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e9985 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e9986 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b9987 := hb (x (-5) 7)
          have b9988 := hb (x (-4) 6)
          have b9989 := hb (x (-3) 5)
          have b9990 := hb (x (-2) 4)
          have b9991 := hb (x (-1) 11)
          have b9992 := hb (x 0 10)
          have b9993 := hb (x 1 9)
          have b9994 := hb (x 2 8)
          clear * - r9980 e9981 e9982 e9983 e9984 e9985 e9986 b9987 b9988 b9989 b9990 b9991 b9992 b9993 b9994 d9327 f9312 g7 d9819 d9779
          omega
        have d9995 : (x 2 8 && x 2 14).toNat = 0 := by
          have r9996 := hand1 (x 2 8) (x 2 14)
          have b9997 := hb (x 2 8)
          have b9998 := hb (x 2 8 && x 2 14)
          clear * - r9996 b9997 b9998 d9979
          omega
        have d9999 : (x (-4) 6).toNat = 0 := by
          have r10000 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e10001 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e10002 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e10003 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e10004 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e10005 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e10006 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b10007 := hb (x (-5) 7)
          have b10008 := hb (x (-4) 6)
          have b10009 := hb (x (-3) 5)
          have b10010 := hb (x (-2) 4)
          have b10011 := hb (x (-1) 11)
          have b10012 := hb (x 0 10)
          have b10013 := hb (x 1 9)
          have b10014 := hb (x 2 8)
          clear * - r10000 e10001 e10002 e10003 e10004 e10005 e10006 b10007 b10008 b10009 b10010 b10011 b10012 b10013 b10014 d9979 d9327 f9312 g7 d9819 d9779
          omega
        have d10015 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
          have r10016 := hand1 (x (-4) 6) (x (-4) 12)
          have b10017 := hb (x (-4) 6)
          have b10018 := hb (x (-4) 6 && x (-4) 12)
          clear * - r10016 b10017 b10018 d9999
          omega
        have d10019 : (x (-4) 6 && x (-4) 8).toNat = 0 := by
          have r10020 := hand1 (x (-4) 6) (x (-4) 8)
          have b10021 := hb (x (-4) 6)
          have b10022 := hb (x (-4) 6 && x (-4) 8)
          clear * - r10020 b10021 b10022 d9999
          omega
        have d10023 : (x (-5) 7).toNat = 0 := by
          have r10024 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e10025 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e10026 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e10027 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e10028 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e10029 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e10030 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have b10031 := hb (x (-5) 7)
          have b10032 := hb (x (-4) 6)
          have b10033 := hb (x (-3) 5)
          have b10034 := hb (x (-2) 4)
          have b10035 := hb (x (-1) 11)
          have b10036 := hb (x 0 10)
          have b10037 := hb (x 1 9)
          have b10038 := hb (x 2 8)
          clear * - r10024 e10025 e10026 e10027 e10028 e10029 e10030 b10031 b10032 b10033 b10034 b10035 b10036 b10037 b10038 d9979 d9327 f9312 g7 d9819 d9779 d9999
          omega
        have d10039 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
          have r10040 := hand1 (x (-5) 7) (x (-5) 13)
          have b10041 := hb (x (-5) 7)
          have b10042 := hb (x (-5) 7 && x (-5) 13)
          clear * - r10040 b10041 b10042 d10023
          omega
        have d10043 : (x (-5) 7 && x (-5) 12).toNat = 0 := by
          have r10044 := hand1 (x (-5) 7) (x (-5) 12)
          have b10045 := hb (x (-5) 7)
          have b10046 := hb (x (-5) 7 && x (-5) 12)
          clear * - r10044 b10045 b10046 d10023
          omega
        have d10047 : (x (-5) 7 && x (-5) 9).toNat = 0 := by
          have r10048 := hand1 (x (-5) 7) (x (-5) 9)
          have b10049 := hb (x (-5) 7)
          have b10050 := hb (x (-5) 7 && x (-5) 9)
          clear * - r10048 b10049 b10050 d10023
          omega
        have d10051 : (x 1 8).toNat = 0 := by
          have r10052 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e10053 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e10054 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e10055 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e10056 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e10057 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e10058 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b10059 := hb (x (-6) 7)
          have b10060 := hb (x (-5) 6)
          have b10061 := hb (x (-4) 5)
          have b10062 := hb (x (-3) 4)
          have b10063 := hb (x (-2) 11)
          have b10064 := hb (x (-1) 10)
          have b10065 := hb (x 0 9)
          have b10066 := hb (x 1 8)
          clear * - r10052 e10053 e10054 e10055 e10056 e10057 e10058 b10059 b10060 b10061 b10062 b10063 b10064 b10065 b10066 g17 g6 g1 d9341 d9360
          omega
        have d10067 : (x (-5) 6).toNat = 0 := by
          have r10068 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e10069 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e10070 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e10071 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e10072 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e10073 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e10074 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b10075 := hb (x (-6) 7)
          have b10076 := hb (x (-5) 6)
          have b10077 := hb (x (-4) 5)
          have b10078 := hb (x (-3) 4)
          have b10079 := hb (x (-2) 11)
          have b10080 := hb (x (-1) 10)
          have b10081 := hb (x 0 9)
          have b10082 := hb (x 1 8)
          clear * - r10068 e10069 e10070 e10071 e10072 e10073 e10074 b10075 b10076 b10077 b10078 b10079 b10080 b10081 b10082 d10051 g17 g6 g1 d9341 d9360
          omega
        have d10083 : (x (-5) 6 && x (-5) 12).toNat = 0 := by
          have r10084 := hand1 (x (-5) 6) (x (-5) 12)
          have b10085 := hb (x (-5) 6)
          have b10086 := hb (x (-5) 6 && x (-5) 12)
          clear * - r10084 b10085 b10086 d10067
          omega
        have d10087 : (x (-5) 6 && x (-5) 9).toNat = 0 := by
          have r10088 := hand1 (x (-5) 6) (x (-5) 9)
          have b10089 := hb (x (-5) 6)
          have b10090 := hb (x (-5) 6 && x (-5) 9)
          clear * - r10088 b10089 b10090 d10067
          omega
        have d10091 : (x (-6) 7).toNat = 0 := by
          have r10092 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e10093 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e10094 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e10095 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e10096 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e10097 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e10098 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b10099 := hb (x (-6) 7)
          have b10100 := hb (x (-5) 6)
          have b10101 := hb (x (-4) 5)
          have b10102 := hb (x (-3) 4)
          have b10103 := hb (x (-2) 11)
          have b10104 := hb (x (-1) 10)
          have b10105 := hb (x 0 9)
          have b10106 := hb (x 1 8)
          clear * - r10092 e10093 e10094 e10095 e10096 e10097 e10098 b10099 b10100 b10101 b10102 b10103 b10104 b10105 b10106 d10051 g17 g6 g1 d9341 d9360 d10067
          omega
        have d10107 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
          have r10108 := hand1 (x (-6) 7) (x (-6) 13)
          have b10109 := hb (x (-6) 7)
          have b10110 := hb (x (-6) 7 && x (-6) 13)
          clear * - r10108 b10109 b10110 d10091
          omega
        have d10111 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
          have r10112 := hand1 (x (-6) 7) (x (-6) 12)
          have b10113 := hb (x (-6) 7)
          have b10114 := hb (x (-6) 7 && x (-6) 12)
          clear * - r10112 b10113 b10114 d10091
          omega
        have d10115 : (x (-6) 7 && x (-6) 10).toNat = 0 := by
          have r10116 := hand1 (x (-6) 7) (x (-6) 10)
          have b10117 := hb (x (-6) 7)
          have b10118 := hb (x (-6) 7 && x (-6) 10)
          clear * - r10116 b10117 b10118 d10091
          omega
        cases h10119 : x 1 7
        · have f10120 : (x 1 7).toNat = 0 := by rw [h10119]; rfl
          cases h10121 : x (-1) 8
          · have f10122 : (x (-1) 8).toNat = 0 := by rw [h10121]; rfl
            have d10123 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
              have r10124 := hand1 (x (-1) 8) (x (-1) 14)
              have b10125 := hb (x (-1) 8)
              have b10126 := hb (x (-1) 8 && x (-1) 14)
              clear * - r10124 b10125 b10126 f10122
              omega
            cases h10127 : x (-1) 14
            · have f10128 : (x (-1) 14).toNat = 0 := by rw [h10127]; rfl
              cases h10129 : x 2 6
              · have f10130 : (x 2 6).toNat = 0 := by rw [h10129]; rfl
                cases h10131 : x 2 7
                · have f10132 : (x 2 7).toNat = 0 := by rw [h10131]; rfl
                  cases h10133 : x (-2) 8
                  · have f10134 : (x (-2) 8).toNat = 0 := by rw [h10133]; rfl
                    cases h10135 : x (-2) 9
                    · have f10136 : (x (-2) 9).toNat = 0 := by rw [h10135]; rfl
                      cases h10137 : x 3 4
                      · have f10138 : (x 3 4).toNat = 0 := by rw [h10137]; rfl
                        have d10139 : (x 3 4 && x 3 11).toNat = 0 := by
                          have r10140 := hand1 (x 3 4) (x 3 11)
                          have b10141 := hb (x 3 4)
                          have b10142 := hb (x 3 4 && x 3 11)
                          clear * - r10140 b10141 b10142 f10138
                          omega
                        have d10143 : (x 3 4 && x 3 10).toNat = 0 := by
                          have r10144 := hand1 (x 3 4) (x 3 10)
                          have b10145 := hb (x 3 4)
                          have b10146 := hb (x 3 4 && x 3 10)
                          clear * - r10144 b10145 b10146 f10138
                          omega
                        have d10147 : (x 7 11).toNat = 1 := by
                          have r10148 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10149 := hb (x 3 4)
                          have b10150 := hb (x 7 11)
                          have b10151 := hb (x 6 1 && x 6 12)
                          have b10152 := hb (x 5 2 && x 5 13)
                          have b10153 := hb (x 4 3 && x 4 14)
                          clear * - r10148 b10149 b10150 b10151 b10152 b10153 d9485 d9509 d9727 f10138
                          omega
                        have d10154 : (x 7 3).toNat = 1 := by
                          have r10155 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                          have b10156 := hb (x 7 3)
                          have b10157 := hb (x 7 11)
                          clear * - r10155 b10156 b10157 d10147
                          omega
                        have d10158 : (x 10 12).toNat = 0 := by
                          have r10159 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10160 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                          have e10161 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                          have b10162 := hb (x 7 3)
                          have b10163 := hb (x 8 2)
                          have b10164 := hb (x 9 13)
                          have b10165 := hb (x 10 12)
                          clear * - r10159 e10160 e10161 b10162 b10163 b10164 b10165 d10154
                          omega
                        have d10166 : (x 10 4).toNat = 0 := by
                          have r10167 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                          have b10168 := hb (x 10 4)
                          have b10169 := hb (x 10 12)
                          clear * - r10167 b10168 b10169 d10158
                          omega
                        have d10170 : (x 9 13).toNat = 0 := by
                          have r10171 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10172 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                          have e10173 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                          have b10174 := hb (x 7 3)
                          have b10175 := hb (x 8 2)
                          have b10176 := hb (x 9 13)
                          have b10177 := hb (x 10 12)
                          clear * - r10171 e10172 e10173 b10174 b10175 b10176 b10177 d10158 d10154
                          omega
                        have d10178 : (x 9 5).toNat = 0 := by
                          have r10179 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
                          have b10180 := hb (x 9 5)
                          have b10181 := hb (x 9 13)
                          clear * - r10179 b10180 b10181 d10170
                          omega
                        have d10182 : (x 8 2).toNat = 0 := by
                          have r10183 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10184 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                          have e10185 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                          have b10186 := hb (x 7 3)
                          have b10187 := hb (x 8 2)
                          have b10188 := hb (x 9 13)
                          have b10189 := hb (x 10 12)
                          clear * - r10183 e10184 e10185 b10186 b10187 b10188 b10189 d10158 d10170 d10154
                          omega
                        have d10190 : (x 8 2 && x 8 8).toNat = 0 := by
                          have r10191 := hand1 (x 8 2) (x 8 8)
                          have b10192 := hb (x 8 2)
                          have b10193 := hb (x 8 2 && x 8 8)
                          clear * - r10191 b10192 b10193 d10182
                          omega
                        have d10194 : (x 8 10).toNat = 0 := by
                          have r10195 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                          have b10196 := hb (x 8 2)
                          have b10197 := hb (x 8 10)
                          clear * - r10195 b10196 b10197 d10182
                          omega
                        have d10198 : (x 10 8).toNat = 0 := by
                          have r10199 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10200 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                          have e10201 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                          have e10202 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                          have e10203 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                          have e10204 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                          have e10205 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                          have b10206 := hb (x 3 7)
                          have b10207 := hb (x 4 6)
                          have b10208 := hb (x 5 5)
                          have b10209 := hb (x 6 4)
                          have b10210 := hb (x 7 11)
                          have b10211 := hb (x 8 10)
                          have b10212 := hb (x 9 9)
                          have b10213 := hb (x 10 8)
                          clear * - r10199 e10200 e10201 e10202 e10203 e10204 e10205 b10206 b10207 b10208 b10209 b10210 b10211 b10212 b10213 d10194 d10147 d9493 d9517 d9731
                          omega
                        have d10214 : (x 9 9).toNat = 0 := by
                          have r10215 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10216 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                          have e10217 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                          have e10218 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                          have e10219 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                          have e10220 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                          have e10221 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                          have b10222 := hb (x 3 7)
                          have b10223 := hb (x 4 6)
                          have b10224 := hb (x 5 5)
                          have b10225 := hb (x 6 4)
                          have b10226 := hb (x 7 11)
                          have b10227 := hb (x 8 10)
                          have b10228 := hb (x 9 9)
                          have b10229 := hb (x 10 8)
                          clear * - r10215 e10216 e10217 e10218 e10219 e10220 e10221 b10222 b10223 b10224 b10225 b10226 b10227 b10228 b10229 d10198 d10194 d10147 d9493 d9517 d9731
                          omega
                        have d10230 : (x 3 7).toNat = 0 := by
                          have r10231 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10232 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                          have e10233 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                          have e10234 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                          have e10235 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                          have e10236 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                          have e10237 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                          have b10238 := hb (x 3 7)
                          have b10239 := hb (x 4 6)
                          have b10240 := hb (x 5 5)
                          have b10241 := hb (x 6 4)
                          have b10242 := hb (x 7 11)
                          have b10243 := hb (x 8 10)
                          have b10244 := hb (x 9 9)
                          have b10245 := hb (x 10 8)
                          clear * - r10231 e10232 e10233 e10234 e10235 e10236 e10237 b10238 b10239 b10240 b10241 b10242 b10243 b10244 b10245 d10198 d10214 d10194 d10147 d9493 d9517 d9731
                          omega
                        have d10246 : (x 3 7 && x 3 13).toNat = 0 := by
                          have r10247 := hand1 (x 3 7) (x 3 13)
                          have b10248 := hb (x 3 7)
                          have b10249 := hb (x 3 7 && x 3 13)
                          clear * - r10247 b10248 b10249 d10230
                          omega
                        have d10250 : (x 7 7).toNat = 1 := by
                          have r10251 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10252 := hb (x (-1) 8)
                          have b10253 := hb (x 7 7)
                          have b10254 := hb (x 6 1 && x 6 8)
                          have b10255 := hb (x 5 2 && x 5 9)
                          have b10256 := hb (x 4 3 && x 4 10)
                          have b10257 := hb (x 3 4 && x 3 11)
                          have b10258 := hb (x 2 5 && x 2 12)
                          have b10259 := hb (x 1 6 && x 1 13)
                          have b10260 := hb (x 0 7 && x 0 14)
                          clear * - r10251 b10252 b10253 b10254 b10255 b10256 b10257 b10258 b10259 b10260 d9883 d9915 d9537 d10139 g65 g66 g67 f10122
                          omega
                        have d10261 : (x 14 8).toNat = 0 := by
                          have r10262 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10263 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                          have e10264 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                          have e10265 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                          have e10266 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                          have e10267 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                          have e10268 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                          have b10269 := hb (x 7 7)
                          have b10270 := hb (x 8 6)
                          have b10271 := hb (x 9 5)
                          have b10272 := hb (x 10 4)
                          have b10273 := hb (x 11 11)
                          have b10274 := hb (x 12 10)
                          have b10275 := hb (x 13 9)
                          have b10276 := hb (x 14 8)
                          clear * - r10262 e10263 e10264 e10265 e10266 e10267 e10268 b10269 b10270 b10271 b10272 b10273 b10274 b10275 b10276 d10166 d10178 d10250
                          omega
                        have d10277 : (x 13 9).toNat = 0 := by
                          have r10278 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10279 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                          have e10280 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                          have e10281 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                          have e10282 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                          have e10283 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                          have e10284 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                          have b10285 := hb (x 7 7)
                          have b10286 := hb (x 8 6)
                          have b10287 := hb (x 9 5)
                          have b10288 := hb (x 10 4)
                          have b10289 := hb (x 11 11)
                          have b10290 := hb (x 12 10)
                          have b10291 := hb (x 13 9)
                          have b10292 := hb (x 14 8)
                          clear * - r10278 e10279 e10280 e10281 e10282 e10283 e10284 b10285 b10286 b10287 b10288 b10289 b10290 b10291 b10292 d10261 d10166 d10178 d10250
                          omega
                        have d10293 : (x 12 10).toNat = 0 := by
                          have r10294 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10295 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                          have e10296 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                          have e10297 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                          have e10298 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                          have e10299 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                          have e10300 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                          have b10301 := hb (x 7 7)
                          have b10302 := hb (x 8 6)
                          have b10303 := hb (x 9 5)
                          have b10304 := hb (x 10 4)
                          have b10305 := hb (x 11 11)
                          have b10306 := hb (x 12 10)
                          have b10307 := hb (x 13 9)
                          have b10308 := hb (x 14 8)
                          clear * - r10294 e10295 e10296 e10297 e10298 e10299 e10300 b10301 b10302 b10303 b10304 b10305 b10306 b10307 b10308 d10261 d10277 d10166 d10178 d10250
                          omega
                        have d10309 : (x 11 11).toNat = 0 := by
                          have r10310 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10311 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                          have e10312 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                          have e10313 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                          have e10314 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                          have e10315 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                          have e10316 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                          have b10317 := hb (x 7 7)
                          have b10318 := hb (x 8 6)
                          have b10319 := hb (x 9 5)
                          have b10320 := hb (x 10 4)
                          have b10321 := hb (x 11 11)
                          have b10322 := hb (x 12 10)
                          have b10323 := hb (x 13 9)
                          have b10324 := hb (x 14 8)
                          clear * - r10310 e10311 e10312 e10313 e10314 e10315 e10316 b10317 b10318 b10319 b10320 b10321 b10322 b10323 b10324 d10261 d10277 d10293 d10166 d10178 d10250
                          omega
                        have d10325 : (x 8 6).toNat = 0 := by
                          have r10326 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10327 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                          have e10328 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                          have e10329 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                          have e10330 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                          have e10331 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                          have e10332 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                          have b10333 := hb (x 7 7)
                          have b10334 := hb (x 8 6)
                          have b10335 := hb (x 9 5)
                          have b10336 := hb (x 10 4)
                          have b10337 := hb (x 11 11)
                          have b10338 := hb (x 12 10)
                          have b10339 := hb (x 13 9)
                          have b10340 := hb (x 14 8)
                          clear * - r10326 e10327 e10328 e10329 e10330 e10331 e10332 b10333 b10334 b10335 b10336 b10337 b10338 b10339 b10340 d10261 d10277 d10293 d10309 d10166 d10178 d10250
                          omega
                        have d10341 : (x 13 1).toNat = 0 := by
                          have r10342 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10343 := hb (x 0 14)
                          have b10344 := hb (x 1 13)
                          have b10345 := hb (x 2 12)
                          have b10346 := hb (x 3 11)
                          have b10347 := hb (x 4 10)
                          have b10348 := hb (x 5 9)
                          have b10349 := hb (x 6 8)
                          have b10350 := hb (x 7 7)
                          have b10351 := hb (x 8 6)
                          have b10352 := hb (x 9 5)
                          have b10353 := hb (x 10 4)
                          have b10354 := hb (x 11 3)
                          have b10355 := hb (x 12 2)
                          have b10356 := hb (x 13 1)
                          clear * - r10342 b10343 b10344 b10345 b10346 b10347 b10348 b10349 b10350 b10351 b10352 b10353 b10354 b10355 b10356 d10166 d10178 d10325 d10250 d9867 d9899 d9533 d9466 g30 g28 g21
                          omega
                        have d10357 : (x 13 1 && x 13 14).toNat = 0 := by
                          have r10358 := hand1 (x 13 1) (x 13 14)
                          have b10359 := hb (x 13 1)
                          have b10360 := hb (x 13 1 && x 13 14)
                          clear * - r10358 b10359 b10360 d10341
                          omega
                        have d10361 : (x 13 1 && x 13 12).toNat = 0 := by
                          have r10362 := hand1 (x 13 1) (x 13 12)
                          have b10363 := hb (x 13 1)
                          have b10364 := hb (x 13 1 && x 13 12)
                          clear * - r10362 b10363 b10364 d10341
                          omega
                        have d10365 : (x 12 2).toNat = 0 := by
                          have r10366 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10367 := hb (x 0 14)
                          have b10368 := hb (x 1 13)
                          have b10369 := hb (x 2 12)
                          have b10370 := hb (x 3 11)
                          have b10371 := hb (x 4 10)
                          have b10372 := hb (x 5 9)
                          have b10373 := hb (x 6 8)
                          have b10374 := hb (x 7 7)
                          have b10375 := hb (x 8 6)
                          have b10376 := hb (x 9 5)
                          have b10377 := hb (x 10 4)
                          have b10378 := hb (x 11 3)
                          have b10379 := hb (x 12 2)
                          have b10380 := hb (x 13 1)
                          clear * - r10366 b10367 b10368 b10369 b10370 b10371 b10372 b10373 b10374 b10375 b10376 b10377 b10378 b10379 b10380 d10341 d10166 d10178 d10325 d10250 d9867 d9899 d9533 d9466 g30 g28 g21
                          omega
                        have d10381 : (x 12 2 && x 12 13).toNat = 0 := by
                          have r10382 := hand1 (x 12 2) (x 12 13)
                          have b10383 := hb (x 12 2)
                          have b10384 := hb (x 12 2 && x 12 13)
                          clear * - r10382 b10383 b10384 d10365
                          omega
                        have d10385 : (x 14 13).toNat = 1 := by
                          have r10386 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10387 := hb (x 12 2)
                          have b10388 := hb (x 14 13)
                          have b10389 := hb (x 13 1 && x 13 14)
                          clear * - r10386 b10387 b10388 b10389 d10357 d10365
                          omega
                        have d10390 : (x 14 1).toNat = 1 := by
                          have r10391 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
                          have b10392 := hb (x 14 1)
                          have b10393 := hb (x 14 13)
                          clear * - r10391 b10392 b10393 d10385
                          omega
                        have d10394 : (x 15 14).toNat = 0 := by
                          have r10395 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10396 := hb (x 14 1)
                          have b10397 := hb (x 15 14)
                          clear * - r10395 b10396 b10397 d10390
                          omega
                        have d10398 : (x 15 1 && x 15 14).toNat = 0 := by
                          have r10399 := hand2 (x 15 1) (x 15 14)
                          have b10400 := hb (x 15 14)
                          have b10401 := hb (x 15 1 && x 15 14)
                          clear * - r10399 b10400 b10401 d10394
                          omega
                        have d10402 : (x 15 2).toNat = 0 := by
                          have r10403 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                          have b10404 := hb (x 15 2)
                          have b10405 := hb (x 15 14)
                          clear * - r10403 b10404 b10405 d10394
                          omega
                        have d10406 : (x 11 3).toNat = 0 := by
                          have r10407 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10408 := hb (x 0 14)
                          have b10409 := hb (x 1 13)
                          have b10410 := hb (x 2 12)
                          have b10411 := hb (x 3 11)
                          have b10412 := hb (x 4 10)
                          have b10413 := hb (x 5 9)
                          have b10414 := hb (x 6 8)
                          have b10415 := hb (x 7 7)
                          have b10416 := hb (x 8 6)
                          have b10417 := hb (x 9 5)
                          have b10418 := hb (x 10 4)
                          have b10419 := hb (x 11 3)
                          have b10420 := hb (x 12 2)
                          have b10421 := hb (x 13 1)
                          clear * - r10407 b10408 b10409 b10410 b10411 b10412 b10413 b10414 b10415 b10416 b10417 b10418 b10419 b10420 b10421 d10341 d10365 d10166 d10178 d10325 d10250 d9867 d9899 d9533 d9466 g30 g28 g21
                          omega
                        have d10422 : (x 11 3 && x 11 14).toNat = 0 := by
                          have r10423 := hand1 (x 11 3) (x 11 14)
                          have b10424 := hb (x 11 3)
                          have b10425 := hb (x 11 3 && x 11 14)
                          clear * - r10423 b10424 b10425 d10406
                          omega
                        have d10426 : (x 14 11).toNat = 1 := by
                          have r10427 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10428 := hb (x 10 4)
                          have b10429 := hb (x 14 11)
                          have b10430 := hb (x 13 1 && x 13 12)
                          have b10431 := hb (x 12 2 && x 12 13)
                          have b10432 := hb (x 11 3 && x 11 14)
                          clear * - r10427 b10428 b10429 b10430 b10431 b10432 d10361 d10381 d10422 d10166
                          omega
                        have d10433 : (x 14 3).toNat = 1 := by
                          have r10434 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                          have b10435 := hb (x 14 3)
                          have b10436 := hb (x 14 11)
                          clear * - r10434 b10435 b10436 d10426
                          omega
                        have d10437 : (x 17 12).toNat = 0 := by
                          have r10438 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10439 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                          have e10440 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                          have b10441 := hb (x 14 3)
                          have b10442 := hb (x 15 2)
                          have b10443 := hb (x 16 13)
                          have b10444 := hb (x 17 12)
                          clear * - r10438 e10439 e10440 b10441 b10442 b10443 b10444 d10402 d10433
                          omega
                        have d10445 : (x 16 13).toNat = 0 := by
                          have r10446 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10447 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                          have e10448 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                          have b10449 := hb (x 14 3)
                          have b10450 := hb (x 15 2)
                          have b10451 := hb (x 16 13)
                          have b10452 := hb (x 17 12)
                          clear * - r10446 e10447 e10448 b10449 b10450 b10451 b10452 d10437 d10402 d10433
                          omega
                        have d10453 : (x 14 2).toNat = 1 := by
                          have r10454 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10455 := hb (x 14 2)
                          have b10456 := hb (x 16 13)
                          have b10457 := hb (x 15 1 && x 15 14)
                          clear * - r10454 b10455 b10456 b10457 d10445 d10398
                          omega
                        have d10458 : (x 16 12).toNat = 0 := by
                          have r10459 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10460 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                          have e10461 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                          have b10462 := hb (x 13 3)
                          have b10463 := hb (x 14 2)
                          have b10464 := hb (x 15 13)
                          have b10465 := hb (x 16 12)
                          clear * - r10459 e10460 e10461 b10462 b10463 b10464 b10465 d10453
                          omega
                        have d10466 : (x 15 13).toNat = 0 := by
                          have r10467 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10468 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                          have e10469 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                          have b10470 := hb (x 13 3)
                          have b10471 := hb (x 14 2)
                          have b10472 := hb (x 15 13)
                          have b10473 := hb (x 16 12)
                          clear * - r10467 e10468 e10469 b10470 b10471 b10472 b10473 d10458 d10453
                          omega
                        have d10474 : (x 13 3).toNat = 0 := by
                          have r10475 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10476 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                          have e10477 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                          have b10478 := hb (x 13 3)
                          have b10479 := hb (x 14 2)
                          have b10480 := hb (x 15 13)
                          have b10481 := hb (x 16 12)
                          clear * - r10475 e10476 e10477 b10478 b10479 b10480 b10481 d10458 d10466 d10453
                          omega
                        have d10482 : (x 15 1).toNat = 0 := by
                          have r10483 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10484 := hb (x 2 14)
                          have b10485 := hb (x 3 13)
                          have b10486 := hb (x 4 12)
                          have b10487 := hb (x 5 11)
                          have b10488 := hb (x 6 10)
                          have b10489 := hb (x 7 9)
                          have b10490 := hb (x 8 8)
                          have b10491 := hb (x 9 7)
                          have b10492 := hb (x 10 6)
                          have b10493 := hb (x 11 5)
                          have b10494 := hb (x 12 4)
                          have b10495 := hb (x 13 3)
                          have b10496 := hb (x 14 2)
                          have b10497 := hb (x 15 1)
                          clear * - r10483 b10484 b10485 b10486 b10487 b10488 b10489 b10490 b10491 b10492 b10493 b10494 b10495 b10496 b10497 d10453 d10474 d9595 d9590 d9331
                          omega
                        have d10498 : (x 12 4).toNat = 0 := by
                          have r10499 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10500 := hb (x 2 14)
                          have b10501 := hb (x 3 13)
                          have b10502 := hb (x 4 12)
                          have b10503 := hb (x 5 11)
                          have b10504 := hb (x 6 10)
                          have b10505 := hb (x 7 9)
                          have b10506 := hb (x 8 8)
                          have b10507 := hb (x 9 7)
                          have b10508 := hb (x 10 6)
                          have b10509 := hb (x 11 5)
                          have b10510 := hb (x 12 4)
                          have b10511 := hb (x 13 3)
                          have b10512 := hb (x 14 2)
                          have b10513 := hb (x 15 1)
                          clear * - r10499 b10500 b10501 b10502 b10503 b10504 b10505 b10506 b10507 b10508 b10509 b10510 b10511 b10512 b10513 d10482 d10453 d10474 d9595 d9590 d9331
                          omega
                        have d10514 : (x 11 5).toNat = 0 := by
                          have r10515 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10516 := hb (x 2 14)
                          have b10517 := hb (x 3 13)
                          have b10518 := hb (x 4 12)
                          have b10519 := hb (x 5 11)
                          have b10520 := hb (x 6 10)
                          have b10521 := hb (x 7 9)
                          have b10522 := hb (x 8 8)
                          have b10523 := hb (x 9 7)
                          have b10524 := hb (x 10 6)
                          have b10525 := hb (x 11 5)
                          have b10526 := hb (x 12 4)
                          have b10527 := hb (x 13 3)
                          have b10528 := hb (x 14 2)
                          have b10529 := hb (x 15 1)
                          clear * - r10515 b10516 b10517 b10518 b10519 b10520 b10521 b10522 b10523 b10524 b10525 b10526 b10527 b10528 b10529 d10482 d10453 d10474 d10498 d9595 d9590 d9331
                          omega
                        have d10530 : (x 10 6).toNat = 0 := by
                          have r10531 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10532 := hb (x 2 14)
                          have b10533 := hb (x 3 13)
                          have b10534 := hb (x 4 12)
                          have b10535 := hb (x 5 11)
                          have b10536 := hb (x 6 10)
                          have b10537 := hb (x 7 9)
                          have b10538 := hb (x 8 8)
                          have b10539 := hb (x 9 7)
                          have b10540 := hb (x 10 6)
                          have b10541 := hb (x 11 5)
                          have b10542 := hb (x 12 4)
                          have b10543 := hb (x 13 3)
                          have b10544 := hb (x 14 2)
                          have b10545 := hb (x 15 1)
                          clear * - r10531 b10532 b10533 b10534 b10535 b10536 b10537 b10538 b10539 b10540 b10541 b10542 b10543 b10544 b10545 d10482 d10453 d10474 d10498 d10514 d9595 d9590 d9331
                          omega
                        have d10546 : (x 9 7).toNat = 0 := by
                          have r10547 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10548 := hb (x 2 14)
                          have b10549 := hb (x 3 13)
                          have b10550 := hb (x 4 12)
                          have b10551 := hb (x 5 11)
                          have b10552 := hb (x 6 10)
                          have b10553 := hb (x 7 9)
                          have b10554 := hb (x 8 8)
                          have b10555 := hb (x 9 7)
                          have b10556 := hb (x 10 6)
                          have b10557 := hb (x 11 5)
                          have b10558 := hb (x 12 4)
                          have b10559 := hb (x 13 3)
                          have b10560 := hb (x 14 2)
                          have b10561 := hb (x 15 1)
                          clear * - r10547 b10548 b10549 b10550 b10551 b10552 b10553 b10554 b10555 b10556 b10557 b10558 b10559 b10560 b10561 d10482 d10453 d10474 d10498 d10514 d10530 d9595 d9590 d9331
                          omega
                        have d10562 : (x 9 1 && x 9 7).toNat = 0 := by
                          have r10563 := hand2 (x 9 1) (x 9 7)
                          have b10564 := hb (x 9 7)
                          have b10565 := hb (x 9 1 && x 9 7)
                          clear * - r10563 b10564 b10565 d10546
                          omega
                        have d10566 : (x 7 3 && x 7 9).toNat = 1 := by
                          have r10567 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10568 := hb (x 1 9)
                          have b10569 := hb (x 10 6)
                          have b10570 := hb (x 9 1 && x 9 7)
                          have b10571 := hb (x 8 2 && x 8 8)
                          have b10572 := hb (x 7 3 && x 7 9)
                          have b10573 := hb (x 6 4 && x 6 10)
                          have b10574 := hb (x 5 5 && x 5 11)
                          have b10575 := hb (x 4 6 && x 4 12)
                          have b10576 := hb (x 3 7 && x 3 13)
                          have b10577 := hb (x 2 8 && x 2 14)
                          clear * - r10567 b10568 b10569 b10570 b10571 b10572 b10573 b10574 b10575 b10576 b10577 d10530 d10562 d10190 d9497 d9521 d9603 d10246 d9995 d9327
                          omega
                        have d10578 : (x 7 9).toNat = 1 := by
                          have r10579 := hand2 (x 7 3) (x 7 9)
                          have b10580 := hb (x 7 9)
                          have b10581 := hb (x 7 3 && x 7 9)
                          clear * - r10579 b10580 b10581 d10566
                          omega
                        have d10582 : (x 7 1).toNat = 1 := by
                          have r10583 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
                          have b10584 := hb (x 7 1)
                          have b10585 := hb (x 7 9)
                          clear * - r10583 b10584 b10585 d10578
                          omega
                        have d10586 : (x 8 14).toNat = 0 := by
                          have r10587 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10588 := hb (x 7 1)
                          have b10589 := hb (x 8 14)
                          clear * - r10587 b10588 b10589 d10582
                          omega
                        have d10590 : (x 8 1 && x 8 14).toNat = 0 := by
                          have r10591 := hand2 (x 8 1) (x 8 14)
                          have b10592 := hb (x 8 14)
                          have b10593 := hb (x 8 1 && x 8 14)
                          clear * - r10591 b10592 b10593 d10586
                          omega
                        have d10594 : (x 7 2).toNat = 1 := by
                          have r10595 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10596 := hb (x 7 2)
                          have b10597 := hb (x 9 13)
                          have b10598 := hb (x 8 1 && x 8 14)
                          clear * - r10595 b10596 b10597 b10598 d10170 d10590
                          omega
                        have d10599 : (x 7 14).toNat = 1 := by
                          have r10600 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                          have b10601 := hb (x 7 2)
                          have b10602 := hb (x 7 14)
                          clear * - r10600 b10601 b10602 d10594
                          omega
                        have d10603 : (x 6 1).toNat = 0 := by
                          have r10604 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10605 := hb (x 6 1)
                          have b10606 := hb (x 7 14)
                          clear * - r10604 b10605 b10606 d10599
                          omega
                        have d10607 : (x 6 1 && x 6 14).toNat = 0 := by
                          have r10608 := hand1 (x 6 1) (x 6 14)
                          have b10609 := hb (x 6 1)
                          have b10610 := hb (x 6 1 && x 6 14)
                          clear * - r10608 b10609 b10610 d10603
                          omega
                        have d10611 : (x 6 1 && x 6 7).toNat = 0 := by
                          have r10612 := hand1 (x 6 1) (x 6 7)
                          have b10613 := hb (x 6 1)
                          have b10614 := hb (x 6 1 && x 6 7)
                          clear * - r10612 b10613 b10614 d10603
                          omega
                        have d10615 : (x 7 6).toNat = 1 := by
                          have r10616 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10617 := hb (x (-2) 9)
                          have b10618 := hb (x 7 6)
                          have b10619 := hb (x 6 1 && x 6 7)
                          have b10620 := hb (x 5 2 && x 5 8)
                          have b10621 := hb (x 4 3 && x 4 9)
                          have b10622 := hb (x 3 4 && x 3 10)
                          have b10623 := hb (x 2 5 && x 2 11)
                          have b10624 := hb (x 1 6 && x 1 12)
                          have b10625 := hb (x 0 7 && x 0 13)
                          have b10626 := hb (x (-1) 8 && x (-1) 14)
                          clear * - r10616 b10617 b10618 b10619 b10620 b10621 b10622 b10623 b10624 b10625 b10626 d10611 d9943 d9971 d10143 d9655 g60 g61 d10123 f10136
                          omega
                        have d10627 : (x 13 8).toNat = 0 := by
                          have r10628 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10629 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                          have e10630 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                          have e10631 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                          have e10632 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                          have e10633 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                          have e10634 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                          have b10635 := hb (x 6 7)
                          have b10636 := hb (x 7 6)
                          have b10637 := hb (x 8 5)
                          have b10638 := hb (x 9 4)
                          have b10639 := hb (x 10 11)
                          have b10640 := hb (x 11 10)
                          have b10641 := hb (x 12 9)
                          have b10642 := hb (x 13 8)
                          clear * - r10628 e10629 e10630 e10631 e10632 e10633 e10634 b10635 b10636 b10637 b10638 b10639 b10640 b10641 b10642 d10615
                          omega
                        have d10643 : (x 12 9).toNat = 0 := by
                          have r10644 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10645 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                          have e10646 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                          have e10647 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                          have e10648 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                          have e10649 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                          have e10650 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                          have b10651 := hb (x 6 7)
                          have b10652 := hb (x 7 6)
                          have b10653 := hb (x 8 5)
                          have b10654 := hb (x 9 4)
                          have b10655 := hb (x 10 11)
                          have b10656 := hb (x 11 10)
                          have b10657 := hb (x 12 9)
                          have b10658 := hb (x 13 8)
                          clear * - r10644 e10645 e10646 e10647 e10648 e10649 e10650 b10651 b10652 b10653 b10654 b10655 b10656 b10657 b10658 d10627 d10615
                          omega
                        have d10659 : (x 11 10).toNat = 0 := by
                          have r10660 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10661 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                          have e10662 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                          have e10663 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                          have e10664 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                          have e10665 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                          have e10666 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                          have b10667 := hb (x 6 7)
                          have b10668 := hb (x 7 6)
                          have b10669 := hb (x 8 5)
                          have b10670 := hb (x 9 4)
                          have b10671 := hb (x 10 11)
                          have b10672 := hb (x 11 10)
                          have b10673 := hb (x 12 9)
                          have b10674 := hb (x 13 8)
                          clear * - r10660 e10661 e10662 e10663 e10664 e10665 e10666 b10667 b10668 b10669 b10670 b10671 b10672 b10673 b10674 d10627 d10643 d10615
                          omega
                        have d10675 : (x 10 11).toNat = 0 := by
                          have r10676 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10677 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                          have e10678 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                          have e10679 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                          have e10680 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                          have e10681 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                          have e10682 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                          have b10683 := hb (x 6 7)
                          have b10684 := hb (x 7 6)
                          have b10685 := hb (x 8 5)
                          have b10686 := hb (x 9 4)
                          have b10687 := hb (x 10 11)
                          have b10688 := hb (x 11 10)
                          have b10689 := hb (x 12 9)
                          have b10690 := hb (x 13 8)
                          clear * - r10676 e10677 e10678 e10679 e10680 e10681 e10682 b10683 b10684 b10685 b10686 b10687 b10688 b10689 b10690 d10627 d10643 d10659 d10615
                          omega
                        have d10691 : (x 10 1 && x 10 11).toNat = 0 := by
                          have r10692 := hand2 (x 10 1) (x 10 11)
                          have b10693 := hb (x 10 11)
                          have b10694 := hb (x 10 1 && x 10 11)
                          clear * - r10692 b10693 b10694 d10675
                          omega
                        have d10695 : (x 6 13).toNat = 0 := by
                          have r10696 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                          have b10697 := hb (x 6 1)
                          have b10698 := hb (x 6 13)
                          clear * - r10696 b10697 b10698 d10603
                          omega
                        have d10699 : (x 6 5).toNat = 0 := by
                          have r10700 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                          have b10701 := hb (x 6 5)
                          have b10702 := hb (x 6 13)
                          clear * - r10700 b10701 b10702 d10695
                          omega
                        have d10703 : (x 5 1 && x 5 14).toNat = 1 := by
                          have r10704 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10705 := hb (x 4 2)
                          have b10706 := hb (x 6 13)
                          have b10707 := hb (x 5 1 && x 5 14)
                          clear * - r10704 b10705 b10706 b10707 d10695 d9525
                          omega
                        have d10708 : (x 5 1).toNat = 1 := by
                          have r10709 := hand1 (x 5 1) (x 5 14)
                          have b10710 := hb (x 5 1)
                          have b10711 := hb (x 5 1 && x 5 14)
                          clear * - r10709 b10710 b10711 d10703
                          omega
                        have d10712 : (x 6 14).toNat = 0 := by
                          have r10713 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10714 := hb (x 5 1)
                          have b10715 := hb (x 6 14)
                          clear * - r10713 b10714 b10715 d10708
                          omega
                        have d10716 : (x 6 2).toNat = 0 := by
                          have r10717 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                          have b10718 := hb (x 6 2)
                          have b10719 := hb (x 6 14)
                          clear * - r10717 b10718 b10719 d10712
                          omega
                        have d10720 : (x 6 10).toNat = 0 := by
                          have r10721 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
                          have b10722 := hb (x 6 2)
                          have b10723 := hb (x 6 10)
                          clear * - r10721 b10722 b10723 d10716
                          omega
                        have d10724 : (x 9 12).toNat = 0 := by
                          have r10725 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10726 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                          have e10727 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                          have b10728 := hb (x 6 3)
                          have b10729 := hb (x 7 2)
                          have b10730 := hb (x 8 13)
                          have b10731 := hb (x 9 12)
                          clear * - r10725 e10726 e10727 b10728 b10729 b10730 b10731 d10594
                          omega
                        have d10732 : (x 9 2 && x 9 12).toNat = 0 := by
                          have r10733 := hand2 (x 9 2) (x 9 12)
                          have b10734 := hb (x 9 12)
                          have b10735 := hb (x 9 2 && x 9 12)
                          clear * - r10733 b10734 b10735 d10724
                          omega
                        have d10736 : (x 8 13).toNat = 0 := by
                          have r10737 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10738 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                          have e10739 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                          have b10740 := hb (x 6 3)
                          have b10741 := hb (x 7 2)
                          have b10742 := hb (x 8 13)
                          have b10743 := hb (x 9 12)
                          clear * - r10737 e10738 e10739 b10740 b10741 b10742 b10743 d10724 d10594
                          omega
                        have d10744 : (x 8 3 && x 8 13).toNat = 0 := by
                          have r10745 := hand2 (x 8 3) (x 8 13)
                          have b10746 := hb (x 8 13)
                          have b10747 := hb (x 8 3 && x 8 13)
                          clear * - r10745 b10746 b10747 d10736
                          omega
                        have d10748 : (x 7 4 && x 7 14).toNat = 1 := by
                          have r10749 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10750 := hb (x 6 5)
                          have b10751 := hb (x 11 10)
                          have b10752 := hb (x 10 1 && x 10 11)
                          have b10753 := hb (x 9 2 && x 9 12)
                          have b10754 := hb (x 8 3 && x 8 13)
                          have b10755 := hb (x 7 4 && x 7 14)
                          clear * - r10749 b10750 b10751 b10752 b10753 b10754 b10755 d10659 d10691 d10732 d10744 d10699
                          omega
                        have d10756 : (x 7 4).toNat = 1 := by
                          have r10757 := hand1 (x 7 4) (x 7 14)
                          have b10758 := hb (x 7 4)
                          have b10759 := hb (x 7 4 && x 7 14)
                          clear * - r10757 b10758 b10759 d10748
                          omega
                        have d10760 : (x 7 12).toNat = 1 := by
                          have r10761 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                          have b10762 := hb (x 7 4)
                          have b10763 := hb (x 7 12)
                          clear * - r10761 b10762 b10763 d10756
                          omega
                        have d10764 : (x 5 2).toNat = 0 := by
                          have r10765 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10766 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                          have e10767 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                          have b10768 := hb (x 4 3)
                          have b10769 := hb (x 5 2)
                          have b10770 := hb (x 6 13)
                          have b10771 := hb (x 7 12)
                          clear * - r10765 e10766 e10767 b10768 b10769 b10770 b10771 d10760 d10695
                          omega
                        have d10772 : (x 7 13).toNat = 1 := by
                          have r10773 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b10774 := hb (x 5 2)
                          have b10775 := hb (x 7 13)
                          have b10776 := hb (x 6 1 && x 6 14)
                          clear * - r10773 b10774 b10775 b10776 d10607 d10764
                          omega
                        have d10777 : (x 8 12).toNat = 0 := by
                          have r10778 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10779 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                          have e10780 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                          have b10781 := hb (x 5 3)
                          have b10782 := hb (x 6 2)
                          have b10783 := hb (x 7 13)
                          have b10784 := hb (x 8 12)
                          clear * - r10778 e10779 e10780 b10781 b10782 b10783 b10784 d10772 d10716
                          omega
                        have d10785 : (x 5 3).toNat = 0 := by
                          have r10786 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10787 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                          have e10788 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                          have b10789 := hb (x 5 3)
                          have b10790 := hb (x 6 2)
                          have b10791 := hb (x 7 13)
                          have b10792 := hb (x 8 12)
                          clear * - r10786 e10787 e10788 b10789 b10790 b10791 b10792 d10777 d10772 d10716
                          omega
                        have d10793 : (x 5 11).toNat = 0 := by
                          have r10794 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                          have b10795 := hb (x 5 3)
                          have b10796 := hb (x 5 11)
                          clear * - r10794 b10795 b10796 d10785
                          omega
                        have d10797 : (x 8 8).toNat = 0 := by
                          have r10798 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10799 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e10800 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e10801 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e10802 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e10803 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e10804 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have b10805 := hb (x 1 7)
                          have b10806 := hb (x 2 6)
                          have b10807 := hb (x 3 5)
                          have b10808 := hb (x 4 4)
                          have b10809 := hb (x 5 11)
                          have b10810 := hb (x 6 10)
                          have b10811 := hb (x 7 9)
                          have b10812 := hb (x 8 8)
                          clear * - r10798 e10799 e10800 e10801 e10802 e10803 e10804 b10805 b10806 b10807 b10808 b10809 b10810 b10811 b10812 d10578 d10720 d10793 d9611 f10130 f10120
                          omega
                        have r10813 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b10814 := hb (x 2 14)
                        have b10815 := hb (x 3 13)
                        have b10816 := hb (x 4 12)
                        have b10817 := hb (x 5 11)
                        have b10818 := hb (x 6 10)
                        have b10819 := hb (x 7 9)
                        have b10820 := hb (x 8 8)
                        have b10821 := hb (x 9 7)
                        have b10822 := hb (x 10 6)
                        have b10823 := hb (x 11 5)
                        have b10824 := hb (x 12 4)
                        have b10825 := hb (x 13 3)
                        have b10826 := hb (x 14 2)
                        have b10827 := hb (x 15 1)
                        linarith only [r10813, b10814, b10815, b10816, b10817, b10818, b10819, b10820, b10821, b10822, b10823, b10824, b10825, b10826, b10827, d10482, d10453, d10474, d10498, d10514, d10530, d10546, d10797, d10578, d10720, d10793, d9595, d9590, d9331]
                      · have f10828 : (x 3 4).toNat = 1 := by rw [h10137]; rfl
                        have d10829 : (x 7 8).toNat = 0 := by
                          have r10830 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10831 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                          have e10832 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                          have e10833 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                          have e10834 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                          have e10835 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                          have e10836 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                          have b10837 := hb (x 0 7)
                          have b10838 := hb (x 1 6)
                          have b10839 := hb (x 2 5)
                          have b10840 := hb (x 3 4)
                          have b10841 := hb (x 4 11)
                          have b10842 := hb (x 5 10)
                          have b10843 := hb (x 6 9)
                          have b10844 := hb (x 7 8)
                          clear * - r10830 e10831 e10832 e10833 e10834 e10835 e10836 b10837 b10838 b10839 b10840 b10841 b10842 b10843 b10844 f10828 d9651 g25 g15
                          omega
                        have d10845 : (x 7 4 && x 7 8).toNat = 0 := by
                          have r10846 := hand2 (x 7 4) (x 7 8)
                          have b10847 := hb (x 7 8)
                          have b10848 := hb (x 7 4 && x 7 8)
                          clear * - r10846 b10847 b10848 d10829
                          omega
                        have d10849 : (x 6 9).toNat = 0 := by
                          have r10850 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10851 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                          have e10852 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                          have e10853 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                          have e10854 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                          have e10855 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                          have e10856 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                          have b10857 := hb (x 0 7)
                          have b10858 := hb (x 1 6)
                          have b10859 := hb (x 2 5)
                          have b10860 := hb (x 3 4)
                          have b10861 := hb (x 4 11)
                          have b10862 := hb (x 5 10)
                          have b10863 := hb (x 6 9)
                          have b10864 := hb (x 7 8)
                          clear * - r10850 e10851 e10852 e10853 e10854 e10855 e10856 b10857 b10858 b10859 b10860 b10861 b10862 b10863 b10864 d10829 f10828 d9651 g25 g15
                          omega
                        have d10865 : (x 6 5 && x 6 9).toNat = 0 := by
                          have r10866 := hand2 (x 6 5) (x 6 9)
                          have b10867 := hb (x 6 9)
                          have b10868 := hb (x 6 5 && x 6 9)
                          clear * - r10866 b10867 b10868 d10849
                          omega
                        have d10869 : (x 5 10).toNat = 0 := by
                          have r10870 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10871 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                          have e10872 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                          have e10873 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                          have e10874 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                          have e10875 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                          have e10876 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                          have b10877 := hb (x 0 7)
                          have b10878 := hb (x 1 6)
                          have b10879 := hb (x 2 5)
                          have b10880 := hb (x 3 4)
                          have b10881 := hb (x 4 11)
                          have b10882 := hb (x 5 10)
                          have b10883 := hb (x 6 9)
                          have b10884 := hb (x 7 8)
                          clear * - r10870 e10871 e10872 e10873 e10874 e10875 e10876 b10877 b10878 b10879 b10880 b10881 b10882 b10883 b10884 d10829 d10849 f10828 d9651 g25 g15
                          omega
                        have d10885 : (x 5 6 && x 5 10).toNat = 0 := by
                          have r10886 := hand2 (x 5 6) (x 5 10)
                          have b10887 := hb (x 5 10)
                          have b10888 := hb (x 5 6 && x 5 10)
                          clear * - r10886 b10887 b10888 d10869
                          omega
                        have d10889 : (x 4 11).toNat = 0 := by
                          have r10890 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10891 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                          have e10892 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                          have e10893 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                          have e10894 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                          have e10895 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                          have e10896 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                          have b10897 := hb (x 0 7)
                          have b10898 := hb (x 1 6)
                          have b10899 := hb (x 2 5)
                          have b10900 := hb (x 3 4)
                          have b10901 := hb (x 4 11)
                          have b10902 := hb (x 5 10)
                          have b10903 := hb (x 6 9)
                          have b10904 := hb (x 7 8)
                          clear * - r10890 e10891 e10892 e10893 e10894 e10895 e10896 b10897 b10898 b10899 b10900 b10901 b10902 b10903 b10904 d10829 d10849 d10869 f10828 d9651 g25 g15
                          omega
                        have d10905 : (x 4 7 && x 4 11).toNat = 0 := by
                          have r10906 := hand2 (x 4 7) (x 4 11)
                          have b10907 := hb (x 4 11)
                          have b10908 := hb (x 4 7 && x 4 11)
                          clear * - r10906 b10907 b10908 d10889
                          omega
                        cases h10909 : x 3 5
                        · have f10910 : (x 3 5).toNat = 0 := by rw [h10909]; rfl
                          have d10911 : (x 3 5 && x 3 11).toNat = 0 := by
                            have r10912 := hand1 (x 3 5) (x 3 11)
                            have b10913 := hb (x 3 5)
                            have b10914 := hb (x 3 5 && x 3 11)
                            clear * - r10912 b10913 b10914 f10910
                            omega
                          have r10915 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r10916 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r10917 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e10918 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e10919 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e10920 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e10921 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e10922 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e10923 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have r10924 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r10925 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r10926 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                          have r10927 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
                          have r10928 := hand2 (x 7 1) (x 7 7)
                          have r10929 := hand2 (x 13 1) (x 13 11)
                          have r10930 := hand1 (x 12 2) (x 12 12)
                          have r10931 := hand1 (x 11 3) (x 11 13)
                          have r10932 := hand1 (x 10 4) (x 10 14)
                          linarith only [r10915, r10916, r10917, e10918, e10919, e10920, e10921, e10922, e10923, r10924, r10925, r10926, r10927, r10928, r10929, r10930, r10931, r10932, g5, g21, f10120, g28, f10130, g30, d9331, f10910, d9466, d9590, d9611, d9533, d9595, d9899, d9867, d9887, d9919, d9541, d10911, g62, g63, g64]
                        · have f10980 : (x 3 5).toNat = 1 := by rw [h10909]; rfl
                          cases h10981 : x (-3) 6
                          · have f10982 : (x (-3) 6).toNat = 0 := by rw [h10981]; rfl
                            have d10983 : (x 3 9).toNat = 1 := by
                              have r10984 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b10985 := hb (x (-3) 6)
                              have b10986 := hb (x 3 9)
                              have b10987 := hb (x 2 1 && x 2 10)
                              have b10988 := hb (x 1 2 && x 1 11)
                              have b10989 := hb (x 0 3 && x 0 12)
                              have b10990 := hb (x (-1) 4 && x (-1) 13)
                              have b10991 := hb (x (-2) 5 && x (-2) 14)
                              clear * - r10984 b10985 b10986 b10987 b10988 b10989 b10990 b10991 d9635 g71 g72 g73 d9747 f10982
                              omega
                            have d10992 : (x 4 8).toNat = 0 := by
                              have r10993 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e10994 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                              have e10995 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                              have e10996 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                              have e10997 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                              have e10998 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                              have e10999 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                              have b11000 := hb (x (-3) 7)
                              have b11001 := hb (x (-2) 6)
                              have b11002 := hb (x (-1) 5)
                              have b11003 := hb (x 0 4)
                              have b11004 := hb (x 1 11)
                              have b11005 := hb (x 2 10)
                              have b11006 := hb (x 3 9)
                              have b11007 := hb (x 4 8)
                              clear * - r10993 e10994 e10995 e10996 e10997 e10998 e10999 b11000 b11001 b11002 b11003 b11004 b11005 b11006 b11007 d10983 d9631 d9337 g12 g4 d9787
                              omega
                            have d11008 : (x (-3) 7).toNat = 0 := by
                              have r11009 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e11010 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                              have e11011 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                              have e11012 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                              have e11013 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                              have e11014 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                              have e11015 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                              have b11016 := hb (x (-3) 7)
                              have b11017 := hb (x (-2) 6)
                              have b11018 := hb (x (-1) 5)
                              have b11019 := hb (x 0 4)
                              have b11020 := hb (x 1 11)
                              have b11021 := hb (x 2 10)
                              have b11022 := hb (x 3 9)
                              have b11023 := hb (x 4 8)
                              clear * - r11009 e11010 e11011 e11012 e11013 e11014 e11015 b11016 b11017 b11018 b11019 b11020 b11021 b11022 b11023 d10992 d10983 d9631 d9337 g12 g4 d9787
                              omega
                            have d11024 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
                              have r11025 := hand2 (x (-3) 3) (x (-3) 7)
                              have b11026 := hb (x (-3) 7)
                              have b11027 := hb (x (-3) 3 && x (-3) 7)
                              clear * - r11025 b11026 b11027 d11008
                              omega
                            have d11028 : (x (-3) 4 && x (-3) 7).toNat = 0 := by
                              have r11029 := hand2 (x (-3) 4) (x (-3) 7)
                              have b11030 := hb (x (-3) 7)
                              have b11031 := hb (x (-3) 4 && x (-3) 7)
                              clear * - r11029 b11030 b11031 d11008
                              omega
                            have d11032 : (x (-3) 5 && x (-3) 7).toNat = 0 := by
                              have r11033 := hand2 (x (-3) 5) (x (-3) 7)
                              have b11034 := hb (x (-3) 7)
                              have b11035 := hb (x (-3) 5 && x (-3) 7)
                              clear * - r11033 b11034 b11035 d11008
                              omega
                            have r11036 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11037 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11038 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11039 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11040 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                            have e11041 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                            have e11042 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                            have e11043 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                            have e11044 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                            have e11045 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                            have r11046 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11047 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                            have e11048 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                            have e11049 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                            have e11050 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                            have e11051 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                            have e11052 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                            have r11053 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11054 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                            have e11055 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                            have e11056 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                            have e11057 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                            have e11058 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                            have e11059 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                            have r11060 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11061 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                            have e11062 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                            have r11063 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11064 : 1 ≤ (x 2 2).toNat + (x 1 1 && x 1 3).toNat + (x 0 2 && x 0 4).toNat + (x (-1) 3 && x (-1) 5).toNat + (x (-2) 4 && x (-2) 6).toNat + (x (-3) 5 && x (-3) 7).toNat + (x (-4) 6 && x (-4) 8).toNat + (x (-5) 7 && x (-5) 9).toNat + (x (-6) 8 && x (-6) 10).toNat + (x (-7) 9 && x (-7) 11).toNat + (x (-8) 10 && x (-8) 12).toNat + (x (-9) 11 && x (-9) 13).toNat + (x (-10) 12 && x (-10) 14).toNat + (x (-11) 13).toNat := by have q := hcov2 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11065 : 1 ≤ (x 1 3).toNat + (x 0 1 && x 0 4).toNat + (x (-1) 2 && x (-1) 5).toNat + (x (-2) 3 && x (-2) 6).toNat + (x (-3) 4 && x (-3) 7).toNat + (x (-4) 5 && x (-4) 8).toNat + (x (-5) 6 && x (-5) 9).toNat + (x (-6) 7 && x (-6) 10).toNat + (x (-7) 8 && x (-7) 11).toNat + (x (-8) 9 && x (-8) 12).toNat + (x (-9) 10 && x (-9) 13).toNat + (x (-10) 11 && x (-10) 14).toNat + (x (-11) 12).toNat := by have q := hcov3 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11066 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11067 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
                            have e11068 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
                            have r11069 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11070 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11071 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11072 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                            have r11073 : (x (-11) 13).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp13 (-11))
                            have r11074 := hand1 (x (-6) 8) (x (-6) 10)
                            have r11075 := hand1 (x (-7) 9) (x (-7) 11)
                            have r11076 := hand1 (x (-8) 10) (x (-8) 12)
                            have r11077 := hand1 (x (-9) 11) (x (-9) 13)
                            have r11078 := hand1 (x (-10) 12) (x (-10) 14)
                            have r11079 := hand1 (x (-7) 8) (x (-7) 11)
                            have r11080 := hand1 (x (-8) 9) (x (-8) 12)
                            have r11081 := hand1 (x (-9) 10) (x (-9) 13)
                            have r11082 := hand1 (x (-10) 11) (x (-10) 14)
                            have r11083 := hand1 (x (-4) 4) (x (-4) 8)
                            have r11084 := hand1 (x (-5) 5) (x (-5) 9)
                            have r11085 := hand1 (x (-6) 6) (x (-6) 10)
                            have r11086 := hand1 (x (-7) 7) (x (-7) 11)
                            have r11087 := hand1 (x (-8) 8) (x (-8) 12)
                            have r11088 := hand1 (x (-9) 9) (x (-9) 13)
                            have r11089 := hand2 (x (-3) 5) (x (-3) 11)
                            have r11090 := hand1 (x (-6) 8) (x (-6) 14)
                            have r11091 := hand2 (x (-9) 1) (x (-9) 11)
                            have r11092 := hand2 (x (-10) 2) (x (-10) 12)
                            have r11093 := hand1 (x (-11) 3) (x (-11) 13)
                            have r11094 := hand1 (x (-12) 4) (x (-12) 14)
                            have r11095 := hand2 (x (-12) 1) (x (-12) 14)
                            linarith only [r11036, r11037, r11038, r11039, e11040, e11041, e11042, e11043, e11044, e11045, r11046, e11047, e11048, e11049, e11050, e11051, e11052, r11053, e11054, e11055, e11056, e11057, e11058, e11059, r11060, e11061, e11062, r11063, r11064, r11065, r11066, e11067, e11068, r11069, r11070, r11071, r11072, r11073, r11074, r11075, r11076, r11077, r11078, r11079, r11080, r11081, r11082, r11083, r11084, r11085, r11086, r11087, r11088, r11089, r11090, r11091, r11092, r11093, r11094, r11095, d10091, d10067, d10023, d9360, d9999, d9341, d9779, d11008, g0, d9819, d9787, d9803, g2, g3, g4, g5, g9, g10, g12, g16, f9314, f9336, d9623, f10130, d9561, d9323, g31, g32, d9795, d11032, d10019, d10047, g35, g36, g37, d11028, d9372, d10087, d10115, d9791, d11024, d9319, g58, g59, d9807, d10015, d10039]
                          · have f11207 : (x (-3) 6).toNat = 1 := by rw [h10981]; rfl
                            have d11208 : (x 3 8).toNat = 0 := by
                              have r11209 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e11210 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                              have e11211 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                              have e11212 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                              have e11213 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                              have e11214 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                              have e11215 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                              have b11216 := hb (x (-4) 7)
                              have b11217 := hb (x (-3) 6)
                              have b11218 := hb (x (-2) 5)
                              have b11219 := hb (x (-1) 4)
                              have b11220 := hb (x 0 11)
                              have b11221 := hb (x 1 10)
                              have b11222 := hb (x 2 9)
                              have b11223 := hb (x 3 8)
                              clear * - r11209 e11210 e11211 e11212 e11213 e11214 e11215 b11216 b11217 b11218 b11219 b11220 b11221 b11222 b11223 d9659 g26 g18 d9458 d9743 f11207
                              omega
                            have d11224 : (x 3 8 && x 3 12).toNat = 0 := by
                              have r11225 := hand1 (x 3 8) (x 3 12)
                              have b11226 := hb (x 3 8)
                              have b11227 := hb (x 3 8 && x 3 12)
                              clear * - r11225 b11226 b11227 d11208
                              omega
                            have d11228 : (x 3 8 && x 3 11).toNat = 0 := by
                              have r11229 := hand1 (x 3 8) (x 3 11)
                              have b11230 := hb (x 3 8)
                              have b11231 := hb (x 3 8 && x 3 11)
                              clear * - r11229 b11230 b11231 d11208
                              omega
                            have d11232 : (x 3 8 && x 3 10).toNat = 0 := by
                              have r11233 := hand1 (x 3 8) (x 3 10)
                              have b11234 := hb (x 3 8)
                              have b11235 := hb (x 3 8 && x 3 10)
                              clear * - r11233 b11234 b11235 d11208
                              omega
                            have r11236 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11237 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11238 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11239 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11240 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                            have e11241 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                            have e11242 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                            have e11243 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                            have e11244 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                            have e11245 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                            have r11246 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11247 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                            have e11248 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                            have e11249 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                            have e11250 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                            have e11251 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                            have e11252 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                            have r11253 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11254 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                            have e11255 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                            have r11256 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11257 : 1 ≤ (x 11 2).toNat + (x 10 1 && x 10 3).toNat + (x 9 2 && x 9 4).toNat + (x 8 3 && x 8 5).toNat + (x 7 4 && x 7 6).toNat + (x 6 5 && x 6 7).toNat + (x 5 6 && x 5 8).toNat + (x 4 7 && x 4 9).toNat + (x 3 8 && x 3 10).toNat + (x 2 9 && x 2 11).toNat + (x 1 10 && x 1 12).toNat + (x 0 11 && x 0 13).toNat + (x (-1) 12 && x (-1) 14).toNat + (x (-2) 13).toNat := by have q := hcov2 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11258 : 1 ≤ (x 11 3).toNat + (x 10 1 && x 10 4).toNat + (x 9 2 && x 9 5).toNat + (x 8 3 && x 8 6).toNat + (x 7 4 && x 7 7).toNat + (x 6 5 && x 6 8).toNat + (x 5 6 && x 5 9).toNat + (x 4 7 && x 4 10).toNat + (x 3 8 && x 3 11).toNat + (x 2 9 && x 2 12).toNat + (x 1 10 && x 1 13).toNat + (x 0 11 && x 0 14).toNat + (x (-1) 12).toNat := by have q := hcov3 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11259 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e11260 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
                            have e11261 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
                            have r11262 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11263 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have r11264 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                            have r11265 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                            have r11266 := hand2 (x 10 1) (x 10 3)
                            have r11267 := hand2 (x 9 2) (x 9 4)
                            have r11268 := hand2 (x 8 3) (x 8 5)
                            have r11269 := hand2 (x 7 4) (x 7 6)
                            have r11270 := hand2 (x 6 5) (x 6 7)
                            have r11271 := hand2 (x 10 1) (x 10 4)
                            have r11272 := hand2 (x 9 2) (x 9 5)
                            have r11273 := hand2 (x 8 3) (x 8 6)
                            have r11274 := hand2 (x 7 4) (x 7 7)
                            have r11275 := hand2 (x 9 2) (x 9 6)
                            have r11276 := hand2 (x 8 3) (x 8 7)
                            have r11277 := hand2 (x 12 1) (x 12 11)
                            have r11278 := hand2 (x 11 2) (x 11 12)
                            have r11279 := hand1 (x 10 3) (x 10 13)
                            have r11280 := hand1 (x 9 4) (x 9 14)
                            have r11281 := hand1 (x 12 1) (x 12 14)
                            linarith only [r11236, r11237, r11238, r11239, e11240, e11241, e11242, e11243, e11244, e11245, r11246, e11247, e11248, e11249, e11250, e11251, e11252, r11253, e11254, e11255, r11256, r11257, r11258, r11259, e11260, e11261, r11262, r11263, r11264, r11265, r11266, r11267, r11268, r11269, r11270, r11271, r11272, r11273, r11274, r11275, r11276, r11277, r11278, r11279, r11280, r11281, d9412, d9735, d9446, f10128, g18, g20, g21, g26, g27, g28, d9659, d9715, g30, d11208, d9751, d9466, d9955, d9533, d9927, d9899, d9867, d9951, d9975, d11232, d9667, g33, g34, d9454, d9895, d9923, d9549, d11228, g38, g39, g40, d10845, d10865, d10885, d10905, d11224, d9647]
                    · have f11376 : (x (-2) 9).toNat = 1 := by rw [h10135]; rfl
                      have d11377 : (x (-3) 10).toNat = 0 := by
                        have r11378 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e11379 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e11380 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e11381 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e11382 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e11383 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e11384 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b11385 := hb (x (-8) 7)
                        have b11386 := hb (x (-7) 6)
                        have b11387 := hb (x (-6) 5)
                        have b11388 := hb (x (-5) 4)
                        have b11389 := hb (x (-4) 11)
                        have b11390 := hb (x (-3) 10)
                        have b11391 := hb (x (-2) 9)
                        have b11392 := hb (x (-1) 8)
                        clear * - r11378 e11379 e11380 e11381 e11382 e11383 e11384 b11385 b11386 b11387 b11388 b11389 b11390 b11391 b11392 f10122 f11376 d9767
                        omega
                      have d11393 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
                        have r11394 := hand2 (x (-3) 4) (x (-3) 10)
                        have b11395 := hb (x (-3) 10)
                        have b11396 := hb (x (-3) 4 && x (-3) 10)
                        clear * - r11394 b11395 b11396 d11377
                        omega
                      have d11397 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
                        have r11398 := hand2 (x (-3) 5) (x (-3) 10)
                        have b11399 := hb (x (-3) 10)
                        have b11400 := hb (x (-3) 5 && x (-3) 10)
                        clear * - r11398 b11399 b11400 d11377
                        omega
                      have r11401 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r11402 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r11403 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r11404 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r11405 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r11406 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                      have r11407 := hand1 (x (-6) 8) (x (-6) 13)
                      have r11408 := hand1 (x (-7) 9) (x (-7) 14)
                      have r11409 := hand1 (x (-7) 8) (x (-7) 14)
                      have r11410 := hand2 (x (-12) 1) (x (-12) 14)
                      linarith only [r11401, r11402, r11403, r11404, r11405, r11406, r11407, r11408, r11409, r11410, d10091, d10067, d10023, d9360, d9999, d9341, d9779, g0, d9819, g2, g3, g9, g10, f9314, g25, d9651, g47, g48, g49, d9823, d11397, d9771, d10043, g55, g56, g57, d11393, d9364, d10083, d10107]
                  · have f11460 : (x (-2) 8).toNat = 1 := by rw [h10133]; rfl
                    have d11461 : (x (-3) 9).toNat = 0 := by
                      have r11462 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11463 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                      have e11464 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                      have e11465 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                      have e11466 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                      have e11467 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                      have e11468 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                      have b11469 := hb (x (-9) 7)
                      have b11470 := hb (x (-8) 6)
                      have b11471 := hb (x (-7) 5)
                      have b11472 := hb (x (-6) 4)
                      have b11473 := hb (x (-5) 11)
                      have b11474 := hb (x (-4) 10)
                      have b11475 := hb (x (-3) 9)
                      have b11476 := hb (x (-2) 8)
                      clear * - r11462 e11463 e11464 e11465 e11466 e11467 e11468 b11469 b11470 b11471 b11472 b11473 b11474 b11475 b11476 f11460 d9839 d9855
                      omega
                    have d11477 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
                      have r11478 := hand2 (x (-3) 4) (x (-3) 9)
                      have b11479 := hb (x (-3) 9)
                      have b11480 := hb (x (-3) 4 && x (-3) 9)
                      clear * - r11478 b11479 b11480 d11461
                      omega
                    have d11481 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
                      have r11482 := hand2 (x (-3) 5) (x (-3) 9)
                      have b11483 := hb (x (-3) 9)
                      have b11484 := hb (x (-3) 5 && x (-3) 9)
                      clear * - r11482 b11483 b11484 d11461
                      omega
                    have r11485 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11486 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11487 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11488 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
                    have e11489 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
                    have r11490 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11491 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11492 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                    have r11493 := hand1 (x (-6) 8) (x (-6) 12)
                    have r11494 := hand1 (x (-7) 9) (x (-7) 13)
                    have r11495 := hand1 (x (-7) 8) (x (-7) 13)
                    have r11496 := hand1 (x (-8) 9) (x (-8) 14)
                    have r11497 := hand2 (x (-12) 1) (x (-12) 14)
                    linarith only [r11485, r11486, r11487, e11488, e11489, r11490, r11491, r11492, r11493, r11494, r11495, r11496, r11497, d10091, d10067, d10023, d9360, d9999, d9341, d9779, g0, d9819, g2, g3, g9, g10, f9314, g24, g29, g41, g42, d9827, d11481, d9843, d9863, g44, g45, g46, d11477, d9368, d9859, d10111]
                · have f11547 : (x 2 7).toNat = 1 := by rw [h10131]; rfl
                  have d11548 : (x 9 8).toNat = 0 := by
                    have r11549 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11550 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e11551 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e11552 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e11553 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e11554 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e11555 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b11556 := hb (x 2 7)
                    have b11557 := hb (x 3 6)
                    have b11558 := hb (x 4 5)
                    have b11559 := hb (x 5 4)
                    have b11560 := hb (x 6 11)
                    have b11561 := hb (x 7 10)
                    have b11562 := hb (x 8 9)
                    have b11563 := hb (x 9 8)
                    clear * - r11549 e11550 e11551 e11552 e11553 e11554 e11555 b11556 b11557 b11558 b11559 b11560 b11561 b11562 b11563 d9679 d9699 f11547
                    omega
                  have d11564 : (x 8 9).toNat = 0 := by
                    have r11565 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11566 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e11567 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e11568 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e11569 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e11570 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e11571 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b11572 := hb (x 2 7)
                    have b11573 := hb (x 3 6)
                    have b11574 := hb (x 4 5)
                    have b11575 := hb (x 5 4)
                    have b11576 := hb (x 6 11)
                    have b11577 := hb (x 7 10)
                    have b11578 := hb (x 8 9)
                    have b11579 := hb (x 9 8)
                    clear * - r11565 e11566 e11567 e11568 e11569 e11570 e11571 b11572 b11573 b11574 b11575 b11576 b11577 b11578 b11579 d11548 d9679 d9699 f11547
                    omega
                  have d11580 : (x 7 10).toNat = 0 := by
                    have r11581 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11582 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e11583 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e11584 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e11585 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e11586 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e11587 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b11588 := hb (x 2 7)
                    have b11589 := hb (x 3 6)
                    have b11590 := hb (x 4 5)
                    have b11591 := hb (x 5 4)
                    have b11592 := hb (x 6 11)
                    have b11593 := hb (x 7 10)
                    have b11594 := hb (x 8 9)
                    have b11595 := hb (x 9 8)
                    clear * - r11581 e11582 e11583 e11584 e11585 e11586 e11587 b11588 b11589 b11590 b11591 b11592 b11593 b11594 b11595 d11548 d11564 d9679 d9699 f11547
                    omega
                  have d11596 : (x 6 11).toNat = 0 := by
                    have r11597 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11598 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e11599 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e11600 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e11601 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e11602 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e11603 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b11604 := hb (x 2 7)
                    have b11605 := hb (x 3 6)
                    have b11606 := hb (x 4 5)
                    have b11607 := hb (x 5 4)
                    have b11608 := hb (x 6 11)
                    have b11609 := hb (x 7 10)
                    have b11610 := hb (x 8 9)
                    have b11611 := hb (x 9 8)
                    clear * - r11597 e11598 e11599 e11600 e11601 e11602 e11603 b11604 b11605 b11606 b11607 b11608 b11609 b11610 b11611 d11548 d11564 d11580 d9679 d9699 f11547
                    omega
                  have d11612 : (x 3 6).toNat = 0 := by
                    have r11613 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11614 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                    have e11615 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                    have e11616 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                    have e11617 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                    have e11618 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                    have e11619 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                    have b11620 := hb (x 2 7)
                    have b11621 := hb (x 3 6)
                    have b11622 := hb (x 4 5)
                    have b11623 := hb (x 5 4)
                    have b11624 := hb (x 6 11)
                    have b11625 := hb (x 7 10)
                    have b11626 := hb (x 8 9)
                    have b11627 := hb (x 9 8)
                    clear * - r11613 e11614 e11615 e11616 e11617 e11618 e11619 b11620 b11621 b11622 b11623 b11624 b11625 b11626 b11627 d11548 d11564 d11580 d11596 d9679 d9699 f11547
                    omega
                  have d11628 : (x 3 6 && x 3 11).toNat = 0 := by
                    have r11629 := hand1 (x 3 6) (x 3 11)
                    have b11630 := hb (x 3 6)
                    have b11631 := hb (x 3 6 && x 3 11)
                    clear * - r11629 b11630 b11631 d11612
                    omega
                  have d11632 : (x 3 6 && x 3 10).toNat = 0 := by
                    have r11633 := hand1 (x 3 6) (x 3 10)
                    have b11634 := hb (x 3 6)
                    have b11635 := hb (x 3 6 && x 3 10)
                    clear * - r11633 b11634 b11635 d11612
                    omega
                  have r11636 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11637 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11638 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11639 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
                  have e11640 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
                  have r11641 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11642 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11643 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                  have r11644 := hand2 (x 7 2) (x 7 6)
                  have r11645 := hand2 (x 6 3) (x 6 7)
                  have r11646 := hand2 (x 8 1) (x 8 6)
                  have r11647 := hand2 (x 7 2) (x 7 7)
                  have r11648 := hand1 (x 12 1) (x 12 14)
                  linarith only [r11636, r11637, r11638, e11639, e11640, r11641, r11642, r11643, r11644, r11645, r11646, r11647, r11648, g1, g6, f10128, g20, g21, g27, g28, d9715, g30, d9751, d9466, d9955, d9533, d9927, d9899, d9867, d9687, d9703, d11632, d9723, g43, d9307, d9891, d9683, d9545, d11628, g53, g54, d9303]
              · have f11698 : (x 2 6).toNat = 1 := by rw [h10129]; rfl
                have d11699 : (x 8 8).toNat = 0 := by
                  have r11700 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11701 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e11702 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e11703 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e11704 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e11705 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e11706 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b11707 := hb (x 1 7)
                  have b11708 := hb (x 2 6)
                  have b11709 := hb (x 3 5)
                  have b11710 := hb (x 4 4)
                  have b11711 := hb (x 5 11)
                  have b11712 := hb (x 6 10)
                  have b11713 := hb (x 7 9)
                  have b11714 := hb (x 8 8)
                  clear * - r11700 e11701 e11702 e11703 e11704 e11705 e11706 b11707 b11708 b11709 b11710 b11711 b11712 b11713 b11714 d9611 f11698 f10120
                  omega
                have d11715 : (x 7 9).toNat = 0 := by
                  have r11716 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11717 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e11718 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e11719 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e11720 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e11721 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e11722 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b11723 := hb (x 1 7)
                  have b11724 := hb (x 2 6)
                  have b11725 := hb (x 3 5)
                  have b11726 := hb (x 4 4)
                  have b11727 := hb (x 5 11)
                  have b11728 := hb (x 6 10)
                  have b11729 := hb (x 7 9)
                  have b11730 := hb (x 8 8)
                  clear * - r11716 e11717 e11718 e11719 e11720 e11721 e11722 b11723 b11724 b11725 b11726 b11727 b11728 b11729 b11730 d11699 d9611 f11698 f10120
                  omega
                have d11731 : (x 6 10).toNat = 0 := by
                  have r11732 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11733 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e11734 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e11735 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e11736 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e11737 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e11738 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b11739 := hb (x 1 7)
                  have b11740 := hb (x 2 6)
                  have b11741 := hb (x 3 5)
                  have b11742 := hb (x 4 4)
                  have b11743 := hb (x 5 11)
                  have b11744 := hb (x 6 10)
                  have b11745 := hb (x 7 9)
                  have b11746 := hb (x 8 8)
                  clear * - r11732 e11733 e11734 e11735 e11736 e11737 e11738 b11739 b11740 b11741 b11742 b11743 b11744 b11745 b11746 d11699 d11715 d9611 f11698 f10120
                  omega
                have d11747 : (x 5 11).toNat = 0 := by
                  have r11748 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11749 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e11750 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e11751 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e11752 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e11753 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e11754 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b11755 := hb (x 1 7)
                  have b11756 := hb (x 2 6)
                  have b11757 := hb (x 3 5)
                  have b11758 := hb (x 4 4)
                  have b11759 := hb (x 5 11)
                  have b11760 := hb (x 6 10)
                  have b11761 := hb (x 7 9)
                  have b11762 := hb (x 8 8)
                  clear * - r11748 e11749 e11750 e11751 e11752 e11753 e11754 b11755 b11756 b11757 b11758 b11759 b11760 b11761 b11762 d11699 d11715 d11731 d9611 f11698 f10120
                  omega
                have d11763 : (x 3 5).toNat = 0 := by
                  have r11764 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11765 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e11766 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e11767 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e11768 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e11769 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e11770 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b11771 := hb (x 1 7)
                  have b11772 := hb (x 2 6)
                  have b11773 := hb (x 3 5)
                  have b11774 := hb (x 4 4)
                  have b11775 := hb (x 5 11)
                  have b11776 := hb (x 6 10)
                  have b11777 := hb (x 7 9)
                  have b11778 := hb (x 8 8)
                  clear * - r11764 e11765 e11766 e11767 e11768 e11769 e11770 b11771 b11772 b11773 b11774 b11775 b11776 b11777 b11778 d11699 d11715 d11731 d11747 d9611 f11698 f10120
                  omega
                have d11779 : (x 3 5 && x 3 11).toNat = 0 := by
                  have r11780 := hand1 (x 3 5) (x 3 11)
                  have b11781 := hb (x 3 5)
                  have b11782 := hb (x 3 5 && x 3 11)
                  clear * - r11780 b11781 b11782 d11763
                  omega
                have d11783 : (x 3 5 && x 3 10).toNat = 0 := by
                  have r11784 := hand1 (x 3 5) (x 3 10)
                  have b11785 := hb (x 3 5)
                  have b11786 := hb (x 3 5 && x 3 10)
                  clear * - r11784 b11785 b11786 d11763
                  omega
                have r11787 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r11788 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r11789 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r11790 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r11791 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r11792 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have r11793 := hand2 (x 7 1) (x 7 6)
                have r11794 := hand2 (x 6 2) (x 6 7)
                have r11795 := hand2 (x 7 1) (x 7 7)
                have r11796 := hand1 (x 12 1) (x 12 14)
                linarith only [r11787, r11788, r11789, r11790, r11791, r11792, r11793, r11794, r11795, r11796, d9803, g5, f10128, g20, g21, g27, g28, d9715, g30, d9751, d9466, d9955, d9533, d9927, d9899, d9867, d9947, d9619, d11783, d9719, g50, g51, g52, d9887, d9919, d9541, d11779, g62, g63, g64]
            · have f11846 : (x (-1) 14).toNat = 1 := by rw [h10127]; rfl
              have d11847 : (x 12 1).toNat = 0 := by
                have r11848 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11849 := hb (x (-1) 14)
                have b11850 := hb (x 0 13)
                have b11851 := hb (x 1 12)
                have b11852 := hb (x 2 11)
                have b11853 := hb (x 3 10)
                have b11854 := hb (x 4 9)
                have b11855 := hb (x 5 8)
                have b11856 := hb (x 6 7)
                have b11857 := hb (x 7 6)
                have b11858 := hb (x 8 5)
                have b11859 := hb (x 9 4)
                have b11860 := hb (x 10 3)
                have b11861 := hb (x 11 2)
                have b11862 := hb (x 12 1)
                clear * - r11848 b11849 b11850 b11851 b11852 b11853 b11854 b11855 b11856 b11857 b11858 b11859 b11860 b11861 b11862 d9927 d9955 d9751 d9715 g27 g20 f11846
                omega
              have d11863 : (x 12 1 && x 12 14).toNat = 0 := by
                have r11864 := hand1 (x 12 1) (x 12 14)
                have b11865 := hb (x 12 1)
                have b11866 := hb (x 12 1 && x 12 14)
                clear * - r11864 b11865 b11866 d11847
                omega
              have d11867 : (x 11 2).toNat = 0 := by
                have r11868 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11869 := hb (x (-1) 14)
                have b11870 := hb (x 0 13)
                have b11871 := hb (x 1 12)
                have b11872 := hb (x 2 11)
                have b11873 := hb (x 3 10)
                have b11874 := hb (x 4 9)
                have b11875 := hb (x 5 8)
                have b11876 := hb (x 6 7)
                have b11877 := hb (x 7 6)
                have b11878 := hb (x 8 5)
                have b11879 := hb (x 9 4)
                have b11880 := hb (x 10 3)
                have b11881 := hb (x 11 2)
                have b11882 := hb (x 12 1)
                clear * - r11868 b11869 b11870 b11871 b11872 b11873 b11874 b11875 b11876 b11877 b11878 b11879 b11880 b11881 b11882 d11847 d9927 d9955 d9751 d9715 g27 g20 f11846
                omega
              have d11883 : (x 13 13).toNat = 1 := by
                have r11884 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11885 := hb (x 11 2)
                have b11886 := hb (x 13 13)
                have b11887 := hb (x 12 1 && x 12 14)
                clear * - r11884 b11885 b11886 b11887 d11863 d11867
                omega
              have d11888 : (x 13 1).toNat = 1 := by
                have r11889 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have b11890 := hb (x 13 1)
                have b11891 := hb (x 13 13)
                clear * - r11889 b11890 b11891 d11883
                omega
              have d11892 : (x 14 14).toNat = 0 := by
                have r11893 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11894 := hb (x 13 1)
                have b11895 := hb (x 14 14)
                clear * - r11893 b11894 b11895 d11888
                omega
              have d11896 : (x 14 2).toNat = 0 := by
                have r11897 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
                have b11898 := hb (x 14 2)
                have b11899 := hb (x 14 14)
                clear * - r11897 b11898 b11899 d11892
                omega
              have d11900 : (x 14 10).toNat = 0 := by
                have r11901 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
                have b11902 := hb (x 14 2)
                have b11903 := hb (x 14 10)
                clear * - r11901 b11902 b11903 d11896
                omega
              have d11904 : (x 12 2).toNat = 0 := by
                have r11905 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11906 := hb (x 0 14)
                have b11907 := hb (x 1 13)
                have b11908 := hb (x 2 12)
                have b11909 := hb (x 3 11)
                have b11910 := hb (x 4 10)
                have b11911 := hb (x 5 9)
                have b11912 := hb (x 6 8)
                have b11913 := hb (x 7 7)
                have b11914 := hb (x 8 6)
                have b11915 := hb (x 9 5)
                have b11916 := hb (x 10 4)
                have b11917 := hb (x 11 3)
                have b11918 := hb (x 12 2)
                have b11919 := hb (x 13 1)
                clear * - r11905 b11906 b11907 b11908 b11909 b11910 b11911 b11912 b11913 b11914 b11915 b11916 b11917 b11918 b11919 d11888 d9867 d9899 d9533 d9466 g30 g28 g21
                omega
              have d11920 : (x 12 2 && x 12 12).toNat = 0 := by
                have r11921 := hand1 (x 12 2) (x 12 12)
                have b11922 := hb (x 12 2)
                have b11923 := hb (x 12 2 && x 12 12)
                clear * - r11921 b11922 b11923 d11904
                omega
              have d11924 : (x 11 3).toNat = 0 := by
                have r11925 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11926 := hb (x 0 14)
                have b11927 := hb (x 1 13)
                have b11928 := hb (x 2 12)
                have b11929 := hb (x 3 11)
                have b11930 := hb (x 4 10)
                have b11931 := hb (x 5 9)
                have b11932 := hb (x 6 8)
                have b11933 := hb (x 7 7)
                have b11934 := hb (x 8 6)
                have b11935 := hb (x 9 5)
                have b11936 := hb (x 10 4)
                have b11937 := hb (x 11 3)
                have b11938 := hb (x 12 2)
                have b11939 := hb (x 13 1)
                clear * - r11925 b11926 b11927 b11928 b11929 b11930 b11931 b11932 b11933 b11934 b11935 b11936 b11937 b11938 b11939 d11888 d11904 d9867 d9899 d9533 d9466 g30 g28 g21
                omega
              have d11940 : (x 11 3 && x 11 13).toNat = 0 := by
                have r11941 := hand1 (x 11 3) (x 11 13)
                have b11942 := hb (x 11 3)
                have b11943 := hb (x 11 3 && x 11 13)
                clear * - r11941 b11942 b11943 d11924
                omega
              have d11944 : (x 10 4).toNat = 0 := by
                have r11945 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11946 := hb (x 0 14)
                have b11947 := hb (x 1 13)
                have b11948 := hb (x 2 12)
                have b11949 := hb (x 3 11)
                have b11950 := hb (x 4 10)
                have b11951 := hb (x 5 9)
                have b11952 := hb (x 6 8)
                have b11953 := hb (x 7 7)
                have b11954 := hb (x 8 6)
                have b11955 := hb (x 9 5)
                have b11956 := hb (x 10 4)
                have b11957 := hb (x 11 3)
                have b11958 := hb (x 12 2)
                have b11959 := hb (x 13 1)
                clear * - r11945 b11946 b11947 b11948 b11949 b11950 b11951 b11952 b11953 b11954 b11955 b11956 b11957 b11958 b11959 d11888 d11904 d11924 d9867 d9899 d9533 d9466 g30 g28 g21
                omega
              have d11960 : (x 10 4 && x 10 14).toNat = 0 := by
                have r11961 := hand1 (x 10 4) (x 10 14)
                have b11962 := hb (x 10 4)
                have b11963 := hb (x 10 4 && x 10 14)
                clear * - r11961 b11962 b11963 d11944
                omega
              have d11964 : (x 9 5).toNat = 0 := by
                have r11965 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11966 := hb (x 0 14)
                have b11967 := hb (x 1 13)
                have b11968 := hb (x 2 12)
                have b11969 := hb (x 3 11)
                have b11970 := hb (x 4 10)
                have b11971 := hb (x 5 9)
                have b11972 := hb (x 6 8)
                have b11973 := hb (x 7 7)
                have b11974 := hb (x 8 6)
                have b11975 := hb (x 9 5)
                have b11976 := hb (x 10 4)
                have b11977 := hb (x 11 3)
                have b11978 := hb (x 12 2)
                have b11979 := hb (x 13 1)
                clear * - r11965 b11966 b11967 b11968 b11969 b11970 b11971 b11972 b11973 b11974 b11975 b11976 b11977 b11978 b11979 d11888 d11904 d11924 d11944 d9867 d9899 d9533 d9466 g30 g28 g21
                omega
              have d11980 : (x 13 1 && x 13 11).toNat = 1 := by
                have r11981 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11982 := hb (x 9 5)
                have b11983 := hb (x 14 10)
                have b11984 := hb (x 13 1 && x 13 11)
                have b11985 := hb (x 12 2 && x 12 12)
                have b11986 := hb (x 11 3 && x 11 13)
                have b11987 := hb (x 10 4 && x 10 14)
                clear * - r11981 b11982 b11983 b11984 b11985 b11986 b11987 d11900 d11920 d11940 d11960 d11964
                omega
              have d11988 : (x 13 11).toNat = 1 := by
                have r11989 := hand2 (x 13 1) (x 13 11)
                have b11990 := hb (x 13 11)
                have b11991 := hb (x 13 1 && x 13 11)
                clear * - r11989 b11990 b11991 d11980
                omega
              have d11992 : (x 13 3).toNat = 1 := by
                have r11993 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have b11994 := hb (x 13 3)
                have b11995 := hb (x 13 11)
                clear * - r11993 b11994 b11995 d11988
                omega
              have d11996 : (x 15 1).toNat = 0 := by
                have r11997 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b11998 := hb (x 2 14)
                have b11999 := hb (x 3 13)
                have b12000 := hb (x 4 12)
                have b12001 := hb (x 5 11)
                have b12002 := hb (x 6 10)
                have b12003 := hb (x 7 9)
                have b12004 := hb (x 8 8)
                have b12005 := hb (x 9 7)
                have b12006 := hb (x 10 6)
                have b12007 := hb (x 11 5)
                have b12008 := hb (x 12 4)
                have b12009 := hb (x 13 3)
                have b12010 := hb (x 14 2)
                have b12011 := hb (x 15 1)
                clear * - r11997 b11998 b11999 b12000 b12001 b12002 b12003 b12004 b12005 b12006 b12007 b12008 b12009 b12010 b12011 d11896 d11992 d9595 d9590 d9331
                omega
              have d12012 : (x 12 4).toNat = 0 := by
                have r12013 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12014 := hb (x 2 14)
                have b12015 := hb (x 3 13)
                have b12016 := hb (x 4 12)
                have b12017 := hb (x 5 11)
                have b12018 := hb (x 6 10)
                have b12019 := hb (x 7 9)
                have b12020 := hb (x 8 8)
                have b12021 := hb (x 9 7)
                have b12022 := hb (x 10 6)
                have b12023 := hb (x 11 5)
                have b12024 := hb (x 12 4)
                have b12025 := hb (x 13 3)
                have b12026 := hb (x 14 2)
                have b12027 := hb (x 15 1)
                clear * - r12013 b12014 b12015 b12016 b12017 b12018 b12019 b12020 b12021 b12022 b12023 b12024 b12025 b12026 b12027 d11996 d11896 d11992 d9595 d9590 d9331
                omega
              have d12028 : (x 11 5).toNat = 0 := by
                have r12029 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12030 := hb (x 2 14)
                have b12031 := hb (x 3 13)
                have b12032 := hb (x 4 12)
                have b12033 := hb (x 5 11)
                have b12034 := hb (x 6 10)
                have b12035 := hb (x 7 9)
                have b12036 := hb (x 8 8)
                have b12037 := hb (x 9 7)
                have b12038 := hb (x 10 6)
                have b12039 := hb (x 11 5)
                have b12040 := hb (x 12 4)
                have b12041 := hb (x 13 3)
                have b12042 := hb (x 14 2)
                have b12043 := hb (x 15 1)
                clear * - r12029 b12030 b12031 b12032 b12033 b12034 b12035 b12036 b12037 b12038 b12039 b12040 b12041 b12042 b12043 d11996 d11896 d11992 d12012 d9595 d9590 d9331
                omega
              have d12044 : (x 10 6).toNat = 0 := by
                have r12045 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12046 := hb (x 2 14)
                have b12047 := hb (x 3 13)
                have b12048 := hb (x 4 12)
                have b12049 := hb (x 5 11)
                have b12050 := hb (x 6 10)
                have b12051 := hb (x 7 9)
                have b12052 := hb (x 8 8)
                have b12053 := hb (x 9 7)
                have b12054 := hb (x 10 6)
                have b12055 := hb (x 11 5)
                have b12056 := hb (x 12 4)
                have b12057 := hb (x 13 3)
                have b12058 := hb (x 14 2)
                have b12059 := hb (x 15 1)
                clear * - r12045 b12046 b12047 b12048 b12049 b12050 b12051 b12052 b12053 b12054 b12055 b12056 b12057 b12058 b12059 d11996 d11896 d11992 d12012 d12028 d9595 d9590 d9331
                omega
              have d12060 : (x 10 1 && x 10 6).toNat = 0 := by
                have r12061 := hand2 (x 10 1) (x 10 6)
                have b12062 := hb (x 10 6)
                have b12063 := hb (x 10 1 && x 10 6)
                clear * - r12061 b12062 b12063 d12044
                omega
              have d12064 : (x 9 7).toNat = 0 := by
                have r12065 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12066 := hb (x 2 14)
                have b12067 := hb (x 3 13)
                have b12068 := hb (x 4 12)
                have b12069 := hb (x 5 11)
                have b12070 := hb (x 6 10)
                have b12071 := hb (x 7 9)
                have b12072 := hb (x 8 8)
                have b12073 := hb (x 9 7)
                have b12074 := hb (x 10 6)
                have b12075 := hb (x 11 5)
                have b12076 := hb (x 12 4)
                have b12077 := hb (x 13 3)
                have b12078 := hb (x 14 2)
                have b12079 := hb (x 15 1)
                clear * - r12065 b12066 b12067 b12068 b12069 b12070 b12071 b12072 b12073 b12074 b12075 b12076 b12077 b12078 b12079 d11996 d11896 d11992 d12012 d12028 d12044 d9595 d9590 d9331
                omega
              have d12080 : (x 9 1 && x 9 7).toNat = 0 := by
                have r12081 := hand2 (x 9 1) (x 9 7)
                have b12082 := hb (x 9 7)
                have b12083 := hb (x 9 1 && x 9 7)
                clear * - r12081 b12082 b12083 d12064
                omega
              have d12084 : (x 9 2 && x 9 7).toNat = 0 := by
                have r12085 := hand2 (x 9 2) (x 9 7)
                have b12086 := hb (x 9 7)
                have b12087 := hb (x 9 2 && x 9 7)
                clear * - r12085 b12086 b12087 d12064
                omega
              have d12088 : (x 8 8).toNat = 0 := by
                have r12089 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12090 := hb (x 2 14)
                have b12091 := hb (x 3 13)
                have b12092 := hb (x 4 12)
                have b12093 := hb (x 5 11)
                have b12094 := hb (x 6 10)
                have b12095 := hb (x 7 9)
                have b12096 := hb (x 8 8)
                have b12097 := hb (x 9 7)
                have b12098 := hb (x 10 6)
                have b12099 := hb (x 11 5)
                have b12100 := hb (x 12 4)
                have b12101 := hb (x 13 3)
                have b12102 := hb (x 14 2)
                have b12103 := hb (x 15 1)
                clear * - r12089 b12090 b12091 b12092 b12093 b12094 b12095 b12096 b12097 b12098 b12099 b12100 b12101 b12102 b12103 d11996 d11896 d11992 d12012 d12028 d12044 d12064 d9595 d9590 d9331
                omega
              have d12104 : (x 8 2 && x 8 8).toNat = 0 := by
                have r12105 := hand2 (x 8 2) (x 8 8)
                have b12106 := hb (x 8 8)
                have b12107 := hb (x 8 2 && x 8 8)
                clear * - r12105 b12106 b12107 d12088
                omega
              have d12108 : (x 8 3 && x 8 8).toNat = 0 := by
                have r12109 := hand2 (x 8 3) (x 8 8)
                have b12110 := hb (x 8 8)
                have b12111 := hb (x 8 3 && x 8 8)
                clear * - r12109 b12110 b12111 d12088
                omega
              have d12112 : (x 7 9).toNat = 0 := by
                have r12113 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12114 := hb (x 2 14)
                have b12115 := hb (x 3 13)
                have b12116 := hb (x 4 12)
                have b12117 := hb (x 5 11)
                have b12118 := hb (x 6 10)
                have b12119 := hb (x 7 9)
                have b12120 := hb (x 8 8)
                have b12121 := hb (x 9 7)
                have b12122 := hb (x 10 6)
                have b12123 := hb (x 11 5)
                have b12124 := hb (x 12 4)
                have b12125 := hb (x 13 3)
                have b12126 := hb (x 14 2)
                have b12127 := hb (x 15 1)
                clear * - r12113 b12114 b12115 b12116 b12117 b12118 b12119 b12120 b12121 b12122 b12123 b12124 b12125 b12126 b12127 d11996 d11896 d11992 d12012 d12028 d12044 d12064 d12088 d9595 d9590 d9331
                omega
              have d12128 : (x 7 3 && x 7 9).toNat = 0 := by
                have r12129 := hand2 (x 7 3) (x 7 9)
                have b12130 := hb (x 7 9)
                have b12131 := hb (x 7 3 && x 7 9)
                clear * - r12129 b12130 b12131 d12112
                omega
              have d12132 : (x 3 7 && x 3 13).toNat = 1 := by
                have r12133 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12134 := hb (x 1 9)
                have b12135 := hb (x 10 6)
                have b12136 := hb (x 9 1 && x 9 7)
                have b12137 := hb (x 8 2 && x 8 8)
                have b12138 := hb (x 7 3 && x 7 9)
                have b12139 := hb (x 6 4 && x 6 10)
                have b12140 := hb (x 5 5 && x 5 11)
                have b12141 := hb (x 4 6 && x 4 12)
                have b12142 := hb (x 3 7 && x 3 13)
                have b12143 := hb (x 2 8 && x 2 14)
                clear * - r12133 b12134 b12135 b12136 b12137 b12138 b12139 b12140 b12141 b12142 b12143 d12044 d12080 d12104 d12128 d9497 d9521 d9603 d9995 d9327
                omega
              have d12144 : (x 3 7).toNat = 1 := by
                have r12145 := hand1 (x 3 7) (x 3 13)
                have b12146 := hb (x 3 7)
                have b12147 := hb (x 3 7 && x 3 13)
                clear * - r12145 b12146 b12147 d12132
                omega
              have d12148 : (x 10 8).toNat = 0 := by
                have r12149 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12150 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e12151 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e12152 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e12153 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e12154 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e12155 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b12156 := hb (x 3 7)
                have b12157 := hb (x 4 6)
                have b12158 := hb (x 5 5)
                have b12159 := hb (x 6 4)
                have b12160 := hb (x 7 11)
                have b12161 := hb (x 8 10)
                have b12162 := hb (x 9 9)
                have b12163 := hb (x 10 8)
                clear * - r12149 e12150 e12151 e12152 e12153 e12154 e12155 b12156 b12157 b12158 b12159 b12160 b12161 b12162 b12163 d9493 d9517 d9731 d12144
                omega
              have d12164 : (x 9 9).toNat = 0 := by
                have r12165 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12166 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e12167 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e12168 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e12169 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e12170 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e12171 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b12172 := hb (x 3 7)
                have b12173 := hb (x 4 6)
                have b12174 := hb (x 5 5)
                have b12175 := hb (x 6 4)
                have b12176 := hb (x 7 11)
                have b12177 := hb (x 8 10)
                have b12178 := hb (x 9 9)
                have b12179 := hb (x 10 8)
                clear * - r12165 e12166 e12167 e12168 e12169 e12170 e12171 b12172 b12173 b12174 b12175 b12176 b12177 b12178 b12179 d12148 d9493 d9517 d9731 d12144
                omega
              have d12180 : (x 8 10).toNat = 0 := by
                have r12181 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12182 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e12183 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e12184 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e12185 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e12186 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e12187 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b12188 := hb (x 3 7)
                have b12189 := hb (x 4 6)
                have b12190 := hb (x 5 5)
                have b12191 := hb (x 6 4)
                have b12192 := hb (x 7 11)
                have b12193 := hb (x 8 10)
                have b12194 := hb (x 9 9)
                have b12195 := hb (x 10 8)
                clear * - r12181 e12182 e12183 e12184 e12185 e12186 e12187 b12188 b12189 b12190 b12191 b12192 b12193 b12194 b12195 d12148 d12164 d9493 d9517 d9731 d12144
                omega
              have d12196 : (x 7 11).toNat = 0 := by
                have r12197 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12198 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e12199 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e12200 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e12201 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e12202 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e12203 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b12204 := hb (x 3 7)
                have b12205 := hb (x 4 6)
                have b12206 := hb (x 5 5)
                have b12207 := hb (x 6 4)
                have b12208 := hb (x 7 11)
                have b12209 := hb (x 8 10)
                have b12210 := hb (x 9 9)
                have b12211 := hb (x 10 8)
                clear * - r12197 e12198 e12199 e12200 e12201 e12202 e12203 b12204 b12205 b12206 b12207 b12208 b12209 b12210 b12211 d12148 d12164 d12180 d9493 d9517 d9731 d12144
                omega
              have d12212 : (x 7 1 && x 7 11).toNat = 0 := by
                have r12213 := hand2 (x 7 1) (x 7 11)
                have b12214 := hb (x 7 11)
                have b12215 := hb (x 7 1 && x 7 11)
                clear * - r12213 b12214 b12215 d12196
                omega
              have d12216 : (x 3 5).toNat = 1 := by
                have r12217 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12218 := hb (x 3 5)
                have b12219 := hb (x 8 10)
                have b12220 := hb (x 7 1 && x 7 11)
                have b12221 := hb (x 6 2 && x 6 12)
                have b12222 := hb (x 5 3 && x 5 13)
                have b12223 := hb (x 4 4 && x 4 14)
                clear * - r12217 b12218 b12219 b12220 b12221 b12222 b12223 d12180 d12212 d9489 d9513 d9615
                omega
              have d12224 : (x 7 4 && x 7 9).toNat = 0 := by
                have r12225 := hand2 (x 7 4) (x 7 9)
                have b12226 := hb (x 7 9)
                have b12227 := hb (x 7 4 && x 7 9)
                clear * - r12225 b12226 b12227 d12112
                omega
              have d12228 : (x 6 10).toNat = 0 := by
                have r12229 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12230 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e12231 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e12232 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e12233 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e12234 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e12235 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b12236 := hb (x 1 7)
                have b12237 := hb (x 2 6)
                have b12238 := hb (x 3 5)
                have b12239 := hb (x 4 4)
                have b12240 := hb (x 5 11)
                have b12241 := hb (x 6 10)
                have b12242 := hb (x 7 9)
                have b12243 := hb (x 8 8)
                clear * - r12229 e12230 e12231 e12232 e12233 e12234 e12235 b12236 b12237 b12238 b12239 b12240 b12241 b12242 b12243 d12088 d12112 d9611 d12216 f10120
                omega
              have d12244 : (x 6 5 && x 6 10).toNat = 0 := by
                have r12245 := hand2 (x 6 5) (x 6 10)
                have b12246 := hb (x 6 10)
                have b12247 := hb (x 6 5 && x 6 10)
                clear * - r12245 b12246 b12247 d12228
                omega
              have d12248 : (x 5 11).toNat = 0 := by
                have r12249 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12250 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e12251 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e12252 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e12253 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e12254 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e12255 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b12256 := hb (x 1 7)
                have b12257 := hb (x 2 6)
                have b12258 := hb (x 3 5)
                have b12259 := hb (x 4 4)
                have b12260 := hb (x 5 11)
                have b12261 := hb (x 6 10)
                have b12262 := hb (x 7 9)
                have b12263 := hb (x 8 8)
                clear * - r12249 e12250 e12251 e12252 e12253 e12254 e12255 b12256 b12257 b12258 b12259 b12260 b12261 b12262 b12263 d12088 d12112 d12228 d9611 d12216 f10120
                omega
              have d12264 : (x 5 6 && x 5 11).toNat = 0 := by
                have r12265 := hand2 (x 5 6) (x 5 11)
                have b12266 := hb (x 5 11)
                have b12267 := hb (x 5 6 && x 5 11)
                clear * - r12265 b12266 b12267 d12248
                omega
              have d12268 : (x 3 8 && x 3 13).toNat = 1 := by
                have r12269 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12270 := hb (x 1 10)
                have b12271 := hb (x 11 5)
                have b12272 := hb (x 10 1 && x 10 6)
                have b12273 := hb (x 9 2 && x 9 7)
                have b12274 := hb (x 8 3 && x 8 8)
                have b12275 := hb (x 7 4 && x 7 9)
                have b12276 := hb (x 6 5 && x 6 10)
                have b12277 := hb (x 5 6 && x 5 11)
                have b12278 := hb (x 4 7 && x 4 12)
                have b12279 := hb (x 3 8 && x 3 13)
                have b12280 := hb (x 2 9 && x 2 14)
                clear * - r12269 b12270 b12271 b12272 b12273 b12274 b12275 b12276 b12277 b12278 b12279 b12280 d12028 d12060 d12084 d12108 d12224 d12244 d12264 d9607 d9663 g26
                omega
              have d12281 : (x 3 8).toNat = 1 := by
                have r12282 := hand1 (x 3 8) (x 3 13)
                have b12283 := hb (x 3 8)
                have b12284 := hb (x 3 8 && x 3 13)
                clear * - r12282 b12283 b12284 d12268
                omega
              have d12285 : (x (-3) 6).toNat = 0 := by
                have r12286 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12287 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e12288 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e12289 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e12290 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e12291 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e12292 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b12293 := hb (x (-4) 7)
                have b12294 := hb (x (-3) 6)
                have b12295 := hb (x (-2) 5)
                have b12296 := hb (x (-1) 4)
                have b12297 := hb (x 0 11)
                have b12298 := hb (x 1 10)
                have b12299 := hb (x 2 9)
                have b12300 := hb (x 3 8)
                clear * - r12286 e12287 e12288 e12289 e12290 e12291 e12292 b12293 b12294 b12295 b12296 b12297 b12298 b12299 b12300 d12281 d9659 g26 g18 d9458 d9743
                omega
              have d12301 : (x 3 9).toNat = 1 := by
                have r12302 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b12303 := hb (x (-3) 6)
                have b12304 := hb (x 3 9)
                have b12305 := hb (x 2 1 && x 2 10)
                have b12306 := hb (x 1 2 && x 1 11)
                have b12307 := hb (x 0 3 && x 0 12)
                have b12308 := hb (x (-1) 4 && x (-1) 13)
                have b12309 := hb (x (-2) 5 && x (-2) 14)
                clear * - r12302 b12303 b12304 b12305 b12306 b12307 b12308 b12309 d9635 g71 g72 g73 d9747 d12285
                omega
              have d12310 : (x 4 8).toNat = 0 := by
                have r12311 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12312 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                have e12313 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                have e12314 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                have e12315 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                have e12316 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                have e12317 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                have b12318 := hb (x (-3) 7)
                have b12319 := hb (x (-2) 6)
                have b12320 := hb (x (-1) 5)
                have b12321 := hb (x 0 4)
                have b12322 := hb (x 1 11)
                have b12323 := hb (x 2 10)
                have b12324 := hb (x 3 9)
                have b12325 := hb (x 4 8)
                clear * - r12311 e12312 e12313 e12314 e12315 e12316 e12317 b12318 b12319 b12320 b12321 b12322 b12323 b12324 b12325 d12301 d9631 d9337 g12 g4 d9787
                omega
              have d12326 : (x (-3) 7).toNat = 0 := by
                have r12327 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12328 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                have e12329 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                have e12330 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                have e12331 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                have e12332 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                have e12333 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                have b12334 := hb (x (-3) 7)
                have b12335 := hb (x (-2) 6)
                have b12336 := hb (x (-1) 5)
                have b12337 := hb (x 0 4)
                have b12338 := hb (x 1 11)
                have b12339 := hb (x 2 10)
                have b12340 := hb (x 3 9)
                have b12341 := hb (x 4 8)
                clear * - r12327 e12328 e12329 e12330 e12331 e12332 e12333 b12334 b12335 b12336 b12337 b12338 b12339 b12340 b12341 d12310 d12301 d9631 d9337 g12 g4 d9787
                omega
              have d12342 : (x (-3) 4 && x (-3) 7).toNat = 0 := by
                have r12343 := hand2 (x (-3) 4) (x (-3) 7)
                have b12344 := hb (x (-3) 7)
                have b12345 := hb (x (-3) 4 && x (-3) 7)
                clear * - r12343 b12344 b12345 d12326
                omega
              have d12346 : (x (-4) 7).toNat = 0 := by
                have r12347 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e12348 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e12349 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e12350 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e12351 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e12352 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e12353 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b12354 := hb (x (-4) 7)
                have b12355 := hb (x (-3) 6)
                have b12356 := hb (x (-2) 5)
                have b12357 := hb (x (-1) 4)
                have b12358 := hb (x 0 11)
                have b12359 := hb (x 1 10)
                have b12360 := hb (x 2 9)
                have b12361 := hb (x 3 8)
                clear * - r12347 e12348 e12349 e12350 e12351 e12352 e12353 b12354 b12355 b12356 b12357 b12358 b12359 b12360 b12361 d12281 d9659 g26 g18 d9458 d9743 d12285
                omega
              have r12362 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r12363 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r12364 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r12365 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12366 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
              have e12367 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
              have e12368 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
              have e12369 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
              have e12370 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
              have e12371 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
              have r12372 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12373 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
              have e12374 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
              have e12375 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
              have e12376 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
              have e12377 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
              have e12378 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
              have r12379 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12380 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
              have e12381 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
              have r12382 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12383 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e12384 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have r12385 : 1 ≤ (x 1 3).toNat + (x 0 1 && x 0 4).toNat + (x (-1) 2 && x (-1) 5).toNat + (x (-2) 3 && x (-2) 6).toNat + (x (-3) 4 && x (-3) 7).toNat + (x (-4) 5 && x (-4) 8).toNat + (x (-5) 6 && x (-5) 9).toNat + (x (-6) 7 && x (-6) 10).toNat + (x (-7) 8 && x (-7) 11).toNat + (x (-8) 9 && x (-8) 12).toNat + (x (-9) 10 && x (-9) 13).toNat + (x (-10) 11 && x (-10) 14).toNat + (x (-11) 12).toNat := by have q := hcov3 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r12386 : 1 ≤ (x (-9) 10).toNat + (x (-10) 1 && x (-10) 11).toNat + (x (-11) 2 && x (-11) 12).toNat + (x (-12) 3 && x (-12) 13).toNat + (x (-13) 4 && x (-13) 14).toNat + (x (-14) 5).toNat := by have q := hcov10 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r12387 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r12388 : 1 ≤ (x (-9) 11).toNat + (x (-10) 1 && x (-10) 12).toNat + (x (-11) 2 && x (-11) 13).toNat + (x (-12) 3 && x (-12) 14).toNat + (x (-13) 4).toNat := by have q := hcov11 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r12389 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r12390 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
              have r12391 : (x (-10) 11).toNat ≤ (x (-10) 3).toNat := himp _ _ (hp11 (-10))
              have r12392 : (x (-9) 10).toNat ≤ (x (-9) 2).toNat := himp _ _ (hp10 (-9))
              have r12393 := hand1 (x (-7) 8) (x (-7) 11)
              have r12394 := hand1 (x (-8) 9) (x (-8) 12)
              have r12395 := hand1 (x (-9) 10) (x (-9) 13)
              have r12396 := hand1 (x (-10) 11) (x (-10) 14)
              have r12397 := hand2 (x (-10) 1) (x (-10) 11)
              have r12398 := hand1 (x (-11) 2) (x (-11) 12)
              have r12399 := hand1 (x (-12) 3) (x (-12) 13)
              have r12400 := hand2 (x (-13) 4) (x (-13) 14)
              have r12401 := hand2 (x (-7) 2) (x (-7) 12)
              have r12402 := hand2 (x (-8) 3) (x (-8) 13)
              have r12403 := hand1 (x (-9) 4) (x (-9) 14)
              have r12404 := hand2 (x (-10) 1) (x (-10) 12)
              have r12405 := hand1 (x (-11) 2) (x (-11) 13)
              have r12406 := hand1 (x (-12) 3) (x (-12) 14)
              have r12407 := hand2 (x (-12) 1) (x (-12) 14)
              have b12424 := hb (x (-11) 14)
              linarith only [r12362, r12363, r12364, r12365, e12366, e12367, e12368, e12369, e12370, e12371, r12372, e12373, e12374, e12375, e12376, e12377, e12378, r12379, e12380, e12381, r12382, e12383, e12384, r12385, r12386, r12387, r12388, r12389, r12390, r12391, r12392, r12393, r12394, r12395, r12396, r12397, r12398, r12399, r12400, r12401, r12402, r12403, r12404, r12405, r12406, r12407, b12424, d10091, d10067, d10023, d9384, d9360, d9999, d12346, d9341, d9779, d12285, g0, d9819, d9743, g2, g3, d9458, g9, g10, g11, f9314, g22, f9336, d9582, g35, g36, g37, d12342, d9372, d10087, d10115, d9400]
          · have f12494 : (x (-1) 8).toNat = 1 := by rw [h10121]; rfl
            have d12495 : (x (-2) 9).toNat = 0 := by
              have r12496 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12497 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e12498 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e12499 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e12500 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e12501 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e12502 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b12503 := hb (x (-8) 7)
              have b12504 := hb (x (-7) 6)
              have b12505 := hb (x (-6) 5)
              have b12506 := hb (x (-5) 4)
              have b12507 := hb (x (-4) 11)
              have b12508 := hb (x (-3) 10)
              have b12509 := hb (x (-2) 9)
              have b12510 := hb (x (-1) 8)
              clear * - r12496 e12497 e12498 e12499 e12500 e12501 e12502 b12503 b12504 b12505 b12506 b12507 b12508 b12509 b12510 f12494 d9767
              omega
            have d12511 : (x (-3) 10).toNat = 0 := by
              have r12512 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12513 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e12514 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e12515 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e12516 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e12517 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e12518 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b12519 := hb (x (-8) 7)
              have b12520 := hb (x (-7) 6)
              have b12521 := hb (x (-6) 5)
              have b12522 := hb (x (-5) 4)
              have b12523 := hb (x (-4) 11)
              have b12524 := hb (x (-3) 10)
              have b12525 := hb (x (-2) 9)
              have b12526 := hb (x (-1) 8)
              clear * - r12512 e12513 e12514 e12515 e12516 e12517 e12518 b12519 b12520 b12521 b12522 b12523 b12524 b12525 b12526 f12494 d12495 d9767
              omega
            have d12527 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
              have r12528 := hand2 (x (-3) 4) (x (-3) 10)
              have b12529 := hb (x (-3) 10)
              have b12530 := hb (x (-3) 4 && x (-3) 10)
              clear * - r12528 b12529 b12530 d12511
              omega
            have d12531 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
              have r12532 := hand2 (x (-3) 5) (x (-3) 10)
              have b12533 := hb (x (-3) 10)
              have b12534 := hb (x (-3) 5 && x (-3) 10)
              clear * - r12532 b12533 b12534 d12511
              omega
            have r12535 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12536 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12537 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12538 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12539 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12540 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
            have r12541 := hand1 (x (-6) 8) (x (-6) 13)
            have r12542 := hand1 (x (-7) 9) (x (-7) 14)
            have r12543 := hand1 (x (-7) 8) (x (-7) 14)
            have r12544 := hand2 (x (-12) 1) (x (-12) 14)
            linarith only [r12535, r12536, r12537, r12538, r12539, r12540, r12541, r12542, r12543, r12544, d10091, d10067, d10023, d9360, d9999, d9341, d9779, g0, d9819, g2, g3, g9, g10, f9314, g25, d9651, g47, g48, g49, d9823, d12531, d9771, d10043, g55, g56, g57, d12527, d9364, d10083, d10107]
        · have f12594 : (x 1 7).toNat = 1 := by rw [h10119]; rfl
          have d12595 : (x 8 8).toNat = 0 := by
            have r12596 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12597 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e12598 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e12599 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e12600 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e12601 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e12602 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b12603 := hb (x 1 7)
            have b12604 := hb (x 2 6)
            have b12605 := hb (x 3 5)
            have b12606 := hb (x 4 4)
            have b12607 := hb (x 5 11)
            have b12608 := hb (x 6 10)
            have b12609 := hb (x 7 9)
            have b12610 := hb (x 8 8)
            clear * - r12596 e12597 e12598 e12599 e12600 e12601 e12602 b12603 b12604 b12605 b12606 b12607 b12608 b12609 b12610 d9611 f12594
            omega
          have d12611 : (x 7 9).toNat = 0 := by
            have r12612 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12613 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e12614 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e12615 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e12616 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e12617 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e12618 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b12619 := hb (x 1 7)
            have b12620 := hb (x 2 6)
            have b12621 := hb (x 3 5)
            have b12622 := hb (x 4 4)
            have b12623 := hb (x 5 11)
            have b12624 := hb (x 6 10)
            have b12625 := hb (x 7 9)
            have b12626 := hb (x 8 8)
            clear * - r12612 e12613 e12614 e12615 e12616 e12617 e12618 b12619 b12620 b12621 b12622 b12623 b12624 b12625 b12626 d12595 d9611 f12594
            omega
          have d12627 : (x 6 10).toNat = 0 := by
            have r12628 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12629 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e12630 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e12631 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e12632 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e12633 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e12634 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b12635 := hb (x 1 7)
            have b12636 := hb (x 2 6)
            have b12637 := hb (x 3 5)
            have b12638 := hb (x 4 4)
            have b12639 := hb (x 5 11)
            have b12640 := hb (x 6 10)
            have b12641 := hb (x 7 9)
            have b12642 := hb (x 8 8)
            clear * - r12628 e12629 e12630 e12631 e12632 e12633 e12634 b12635 b12636 b12637 b12638 b12639 b12640 b12641 b12642 d12595 d12611 d9611 f12594
            omega
          have d12643 : (x 5 11).toNat = 0 := by
            have r12644 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12645 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e12646 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e12647 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e12648 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e12649 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e12650 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b12651 := hb (x 1 7)
            have b12652 := hb (x 2 6)
            have b12653 := hb (x 3 5)
            have b12654 := hb (x 4 4)
            have b12655 := hb (x 5 11)
            have b12656 := hb (x 6 10)
            have b12657 := hb (x 7 9)
            have b12658 := hb (x 8 8)
            clear * - r12644 e12645 e12646 e12647 e12648 e12649 e12650 b12651 b12652 b12653 b12654 b12655 b12656 b12657 b12658 d12595 d12611 d12627 d9611 f12594
            omega
          have d12659 : (x 3 5).toNat = 0 := by
            have r12660 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12661 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e12662 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e12663 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e12664 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e12665 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e12666 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b12667 := hb (x 1 7)
            have b12668 := hb (x 2 6)
            have b12669 := hb (x 3 5)
            have b12670 := hb (x 4 4)
            have b12671 := hb (x 5 11)
            have b12672 := hb (x 6 10)
            have b12673 := hb (x 7 9)
            have b12674 := hb (x 8 8)
            clear * - r12660 e12661 e12662 e12663 e12664 e12665 e12666 b12667 b12668 b12669 b12670 b12671 b12672 b12673 b12674 d12595 d12611 d12627 d12643 d9611 f12594
            omega
          have d12675 : (x 3 5 && x 3 11).toNat = 0 := by
            have r12676 := hand1 (x 3 5) (x 3 11)
            have b12677 := hb (x 3 5)
            have b12678 := hb (x 3 5 && x 3 11)
            clear * - r12676 b12677 b12678 d12659
            omega
          have d12679 : (x 3 5 && x 3 10).toNat = 0 := by
            have r12680 := hand1 (x 3 5) (x 3 10)
            have b12681 := hb (x 3 5)
            have b12682 := hb (x 3 5 && x 3 10)
            clear * - r12680 b12681 b12682 d12659
            omega
          have r12683 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r12684 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r12685 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r12686 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r12687 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r12688 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have r12689 := hand2 (x 7 1) (x 7 6)
          have r12690 := hand2 (x 6 2) (x 6 7)
          have r12691 := hand2 (x 7 1) (x 7 7)
          have r12692 := hand1 (x 12 1) (x 12 14)
          linarith only [r12683, r12684, r12685, r12686, r12687, r12688, r12689, r12690, r12691, r12692, d9803, g5, g20, g21, g27, g28, d9715, g30, d9751, d9466, d9955, d9533, d9927, d9899, d9867, d9947, d9619, d12679, d9719, g50, g51, g52, d9887, d9919, d9541, d12675, g62, g63, g64]
      · have f12742 : (x 1 3).toNat = 1 := by rw [h9335]; rfl
        have d12743 : (x 4 12).toNat = 0 := by
          have r12744 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12745 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e12746 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b12747 := hb (x 1 3)
          have b12748 := hb (x 2 2)
          have b12749 := hb (x 3 13)
          have b12750 := hb (x 4 12)
          clear * - r12744 e12745 e12746 b12747 b12748 b12749 b12750 f12742
          omega
        have d12751 : (x 4 1 && x 4 12).toNat = 0 := by
          have r12752 := hand2 (x 4 1) (x 4 12)
          have b12753 := hb (x 4 12)
          have b12754 := hb (x 4 1 && x 4 12)
          clear * - r12752 b12753 b12754 d12743
          omega
        have d12755 : (x 4 4).toNat = 0 := by
          have r12756 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b12757 := hb (x 4 4)
          have b12758 := hb (x 4 12)
          clear * - r12756 b12757 b12758 d12743
          omega
        have d12759 : (x 3 13).toNat = 0 := by
          have r12760 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12761 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e12762 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b12763 := hb (x 1 3)
          have b12764 := hb (x 2 2)
          have b12765 := hb (x 3 13)
          have b12766 := hb (x 4 12)
          clear * - r12760 e12761 e12762 b12763 b12764 b12765 b12766 d12743 f12742
          omega
        have d12767 : (x 3 2 && x 3 13).toNat = 0 := by
          have r12768 := hand2 (x 3 2) (x 3 13)
          have b12769 := hb (x 3 13)
          have b12770 := hb (x 3 2 && x 3 13)
          clear * - r12768 b12769 b12770 d12759
          omega
        have d12771 : (x 2 1 && x 2 14).toNat = 1 := by
          have r12772 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12773 := hb (x 1 2)
          have b12774 := hb (x 3 13)
          have b12775 := hb (x 2 1 && x 2 14)
          clear * - r12772 b12773 b12774 b12775 d12759 g22
          omega
        have d12776 : (x 2 1).toNat = 1 := by
          have r12777 := hand1 (x 2 1) (x 2 14)
          have b12778 := hb (x 2 1)
          have b12779 := hb (x 2 1 && x 2 14)
          clear * - r12777 b12778 b12779 d12771
          omega
        have d12780 : (x 3 14).toNat = 0 := by
          have r12781 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12782 := hb (x 2 1)
          have b12783 := hb (x 3 14)
          clear * - r12781 b12782 b12783 d12776
          omega
        have d12784 : (x 3 1 && x 3 14).toNat = 0 := by
          have r12785 := hand2 (x 3 1) (x 3 14)
          have b12786 := hb (x 3 14)
          have b12787 := hb (x 3 1 && x 3 14)
          clear * - r12785 b12786 b12787 d12780
          omega
        have d12788 : (x 3 2).toNat = 0 := by
          have r12789 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
          have b12790 := hb (x 3 2)
          have b12791 := hb (x 3 14)
          clear * - r12789 b12790 b12791 d12780
          omega
        have d12792 : (x 2 2).toNat = 0 := by
          have r12793 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12794 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e12795 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b12796 := hb (x 1 3)
          have b12797 := hb (x 2 2)
          have b12798 := hb (x 3 13)
          have b12799 := hb (x 4 12)
          clear * - r12793 e12794 e12795 b12796 b12797 b12798 b12799 d12743 d12759 f12742
          omega
        have d12800 : (x 4 13).toNat = 1 := by
          have r12801 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12802 := hb (x 2 2)
          have b12803 := hb (x 4 13)
          have b12804 := hb (x 3 1 && x 3 14)
          clear * - r12801 b12802 b12803 b12804 d12784 d12792
          omega
        have d12805 : (x 4 1).toNat = 1 := by
          have r12806 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b12807 := hb (x 4 1)
          have b12808 := hb (x 4 13)
          clear * - r12806 b12807 b12808 d12800
          omega
        have d12809 : (x 5 14).toNat = 0 := by
          have r12810 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12811 := hb (x 4 1)
          have b12812 := hb (x 5 14)
          clear * - r12810 b12811 b12812 d12805
          omega
        have d12813 : (x 5 3 && x 5 14).toNat = 0 := by
          have r12814 := hand2 (x 5 3) (x 5 14)
          have b12815 := hb (x 5 14)
          have b12816 := hb (x 5 3 && x 5 14)
          clear * - r12814 b12815 b12816 d12809
          omega
        have d12817 : (x 5 2).toNat = 0 := by
          have r12818 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b12819 := hb (x 5 2)
          have b12820 := hb (x 5 14)
          clear * - r12818 b12819 b12820 d12809
          omega
        have d12821 : (x 5 12).toNat = 0 := by
          have r12822 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12823 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e12824 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b12825 := hb (x 2 3)
          have b12826 := hb (x 3 2)
          have b12827 := hb (x 4 13)
          have b12828 := hb (x 5 12)
          clear * - r12822 e12823 e12824 b12825 b12826 b12827 b12828 d12800 d12788
          omega
        have d12829 : (x 5 4).toNat = 0 := by
          have r12830 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b12831 := hb (x 5 4)
          have b12832 := hb (x 5 12)
          clear * - r12830 b12831 b12832 d12821
          omega
        have d12833 : (x 2 3).toNat = 0 := by
          have r12834 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12835 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e12836 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b12837 := hb (x 2 3)
          have b12838 := hb (x 3 2)
          have b12839 := hb (x 4 13)
          have b12840 := hb (x 5 12)
          clear * - r12834 e12835 e12836 b12837 b12838 b12839 b12840 d12821 d12800 d12788
          omega
        have d12841 : (x 2 3 && x 2 14).toNat = 0 := by
          have r12842 := hand1 (x 2 3) (x 2 14)
          have b12843 := hb (x 2 3)
          have b12844 := hb (x 2 3 && x 2 14)
          clear * - r12842 b12843 b12844 d12833
          omega
        have d12845 : (x 5 11).toNat = 1 := by
          have r12846 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12847 := hb (x 1 4)
          have b12848 := hb (x 5 11)
          have b12849 := hb (x 4 1 && x 4 12)
          have b12850 := hb (x 3 2 && x 3 13)
          have b12851 := hb (x 2 3 && x 2 14)
          clear * - r12846 b12847 b12848 b12849 b12850 b12851 d12751 d12767 d12841 g23
          omega
        have d12852 : (x 5 3).toNat = 1 := by
          have r12853 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b12854 := hb (x 5 3)
          have b12855 := hb (x 5 11)
          clear * - r12853 b12854 b12855 d12845
          omega
        have d12856 : (x 8 12).toNat = 0 := by
          have r12857 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12858 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e12859 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b12860 := hb (x 5 3)
          have b12861 := hb (x 6 2)
          have b12862 := hb (x 7 13)
          have b12863 := hb (x 8 12)
          clear * - r12857 e12858 e12859 b12860 b12861 b12862 b12863 d12852
          omega
        have d12864 : (x 8 1 && x 8 12).toNat = 0 := by
          have r12865 := hand2 (x 8 1) (x 8 12)
          have b12866 := hb (x 8 12)
          have b12867 := hb (x 8 1 && x 8 12)
          clear * - r12865 b12866 b12867 d12856
          omega
        have d12868 : (x 8 4).toNat = 0 := by
          have r12869 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
          have b12870 := hb (x 8 4)
          have b12871 := hb (x 8 12)
          clear * - r12869 b12870 b12871 d12856
          omega
        have d12872 : (x 7 13).toNat = 0 := by
          have r12873 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12874 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e12875 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b12876 := hb (x 5 3)
          have b12877 := hb (x 6 2)
          have b12878 := hb (x 7 13)
          have b12879 := hb (x 8 12)
          clear * - r12873 e12874 e12875 b12876 b12877 b12878 b12879 d12856 d12852
          omega
        have d12880 : (x 7 2 && x 7 13).toNat = 0 := by
          have r12881 := hand2 (x 7 2) (x 7 13)
          have b12882 := hb (x 7 13)
          have b12883 := hb (x 7 2 && x 7 13)
          clear * - r12881 b12882 b12883 d12872
          omega
        have d12884 : (x 6 1 && x 6 14).toNat = 1 := by
          have r12885 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12886 := hb (x 5 2)
          have b12887 := hb (x 7 13)
          have b12888 := hb (x 6 1 && x 6 14)
          clear * - r12885 b12886 b12887 b12888 d12872 d12817
          omega
        have d12889 : (x 6 1).toNat = 1 := by
          have r12890 := hand1 (x 6 1) (x 6 14)
          have b12891 := hb (x 6 1)
          have b12892 := hb (x 6 1 && x 6 14)
          clear * - r12890 b12891 b12892 d12884
          omega
        have d12893 : (x 7 14).toNat = 0 := by
          have r12894 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12895 := hb (x 6 1)
          have b12896 := hb (x 7 14)
          clear * - r12894 b12895 b12896 d12889
          omega
        have d12897 : (x 7 1 && x 7 14).toNat = 0 := by
          have r12898 := hand2 (x 7 1) (x 7 14)
          have b12899 := hb (x 7 14)
          have b12900 := hb (x 7 1 && x 7 14)
          clear * - r12898 b12899 b12900 d12893
          omega
        have d12901 : (x 7 2).toNat = 0 := by
          have r12902 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b12903 := hb (x 7 2)
          have b12904 := hb (x 7 14)
          clear * - r12902 b12903 b12904 d12893
          omega
        have d12905 : (x 6 2).toNat = 0 := by
          have r12906 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12907 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e12908 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b12909 := hb (x 5 3)
          have b12910 := hb (x 6 2)
          have b12911 := hb (x 7 13)
          have b12912 := hb (x 8 12)
          clear * - r12906 e12907 e12908 b12909 b12910 b12911 b12912 d12856 d12872 d12852
          omega
        have d12913 : (x 6 2 && x 6 13).toNat = 0 := by
          have r12914 := hand1 (x 6 2) (x 6 13)
          have b12915 := hb (x 6 2)
          have b12916 := hb (x 6 2 && x 6 13)
          clear * - r12914 b12915 b12916 d12905
          omega
        have d12917 : (x 8 13).toNat = 1 := by
          have r12918 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12919 := hb (x 6 2)
          have b12920 := hb (x 8 13)
          have b12921 := hb (x 7 1 && x 7 14)
          clear * - r12918 b12919 b12920 b12921 d12897 d12905
          omega
        have d12922 : (x 8 1).toNat = 1 := by
          have r12923 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b12924 := hb (x 8 1)
          have b12925 := hb (x 8 13)
          clear * - r12923 b12924 b12925 d12917
          omega
        have d12926 : (x 9 14).toNat = 0 := by
          have r12927 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12928 := hb (x 8 1)
          have b12929 := hb (x 9 14)
          clear * - r12927 b12928 b12929 d12922
          omega
        have d12930 : (x 9 3 && x 9 14).toNat = 0 := by
          have r12931 := hand2 (x 9 3) (x 9 14)
          have b12932 := hb (x 9 14)
          have b12933 := hb (x 9 3 && x 9 14)
          clear * - r12931 b12932 b12933 d12926
          omega
        have d12934 : (x 9 2).toNat = 0 := by
          have r12935 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b12936 := hb (x 9 2)
          have b12937 := hb (x 9 14)
          clear * - r12935 b12936 b12937 d12926
          omega
        have d12938 : (x 9 12).toNat = 0 := by
          have r12939 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12940 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e12941 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b12942 := hb (x 6 3)
          have b12943 := hb (x 7 2)
          have b12944 := hb (x 8 13)
          have b12945 := hb (x 9 12)
          clear * - r12939 e12940 e12941 b12942 b12943 b12944 b12945 d12917 d12901
          omega
        have d12946 : (x 9 4).toNat = 0 := by
          have r12947 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
          have b12948 := hb (x 9 4)
          have b12949 := hb (x 9 12)
          clear * - r12947 b12948 b12949 d12938
          omega
        have d12950 : (x 6 3).toNat = 0 := by
          have r12951 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12952 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e12953 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b12954 := hb (x 6 3)
          have b12955 := hb (x 7 2)
          have b12956 := hb (x 8 13)
          have b12957 := hb (x 9 12)
          clear * - r12951 e12952 e12953 b12954 b12955 b12956 b12957 d12938 d12917 d12901
          omega
        have d12958 : (x 6 3 && x 6 14).toNat = 0 := by
          have r12959 := hand1 (x 6 3) (x 6 14)
          have b12960 := hb (x 6 3)
          have b12961 := hb (x 6 3 && x 6 14)
          clear * - r12959 b12960 b12961 d12950
          omega
        have d12962 : (x 9 11).toNat = 1 := by
          have r12963 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12964 := hb (x 5 4)
          have b12965 := hb (x 9 11)
          have b12966 := hb (x 8 1 && x 8 12)
          have b12967 := hb (x 7 2 && x 7 13)
          have b12968 := hb (x 6 3 && x 6 14)
          clear * - r12963 b12964 b12965 b12966 b12967 b12968 d12864 d12880 d12958 d12829
          omega
        have d12969 : (x 9 3).toNat = 1 := by
          have r12970 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
          have b12971 := hb (x 9 3)
          have b12972 := hb (x 9 11)
          clear * - r12970 b12971 b12972 d12962
          omega
        have d12973 : (x 12 12).toNat = 0 := by
          have r12974 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12975 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e12976 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b12977 := hb (x 9 3)
          have b12978 := hb (x 10 2)
          have b12979 := hb (x 11 13)
          have b12980 := hb (x 12 12)
          clear * - r12974 e12975 e12976 b12977 b12978 b12979 b12980 d12969
          omega
        have d12981 : (x 12 1 && x 12 12).toNat = 0 := by
          have r12982 := hand2 (x 12 1) (x 12 12)
          have b12983 := hb (x 12 12)
          have b12984 := hb (x 12 1 && x 12 12)
          clear * - r12982 b12983 b12984 d12973
          omega
        have d12985 : (x 12 4).toNat = 0 := by
          have r12986 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
          have b12987 := hb (x 12 4)
          have b12988 := hb (x 12 12)
          clear * - r12986 b12987 b12988 d12973
          omega
        have d12989 : (x 11 13).toNat = 0 := by
          have r12990 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12991 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e12992 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b12993 := hb (x 9 3)
          have b12994 := hb (x 10 2)
          have b12995 := hb (x 11 13)
          have b12996 := hb (x 12 12)
          clear * - r12990 e12991 e12992 b12993 b12994 b12995 b12996 d12973 d12969
          omega
        have d12997 : (x 11 2 && x 11 13).toNat = 0 := by
          have r12998 := hand2 (x 11 2) (x 11 13)
          have b12999 := hb (x 11 13)
          have b13000 := hb (x 11 2 && x 11 13)
          clear * - r12998 b12999 b13000 d12989
          omega
        have d13001 : (x 10 1 && x 10 14).toNat = 1 := by
          have r13002 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13003 := hb (x 9 2)
          have b13004 := hb (x 11 13)
          have b13005 := hb (x 10 1 && x 10 14)
          clear * - r13002 b13003 b13004 b13005 d12989 d12934
          omega
        have d13006 : (x 10 14).toNat = 1 := by
          have r13007 := hand2 (x 10 1) (x 10 14)
          have b13008 := hb (x 10 14)
          have b13009 := hb (x 10 1 && x 10 14)
          clear * - r13007 b13008 b13009 d13001
          omega
        have d13010 : (x 9 1).toNat = 0 := by
          have r13011 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13012 := hb (x 9 1)
          have b13013 := hb (x 10 14)
          clear * - r13011 b13012 b13013 d13006
          omega
        have d13014 : (x 9 13).toNat = 0 := by
          have r13015 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b13016 := hb (x 9 1)
          have b13017 := hb (x 9 13)
          clear * - r13015 b13016 b13017 d13010
          omega
        have d13018 : (x 8 1 && x 8 14).toNat = 1 := by
          have r13019 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13020 := hb (x 7 2)
          have b13021 := hb (x 9 13)
          have b13022 := hb (x 8 1 && x 8 14)
          clear * - r13019 b13020 b13021 b13022 d13014 d12901
          omega
        have d13023 : (x 8 14).toNat = 1 := by
          have r13024 := hand2 (x 8 1) (x 8 14)
          have b13025 := hb (x 8 14)
          have b13026 := hb (x 8 1 && x 8 14)
          clear * - r13024 b13025 b13026 d13018
          omega
        have d13027 : (x 7 1).toNat = 0 := by
          have r13028 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13029 := hb (x 7 1)
          have b13030 := hb (x 8 14)
          clear * - r13028 b13029 b13030 d13023
          omega
        have d13031 : (x 7 1 && x 7 12).toNat = 0 := by
          have r13032 := hand1 (x 7 1) (x 7 12)
          have b13033 := hb (x 7 1)
          have b13034 := hb (x 7 1 && x 7 12)
          clear * - r13032 b13033 b13034 d13027
          omega
        have d13035 : (x 8 11).toNat = 1 := by
          have r13036 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13037 := hb (x 4 4)
          have b13038 := hb (x 8 11)
          have b13039 := hb (x 7 1 && x 7 12)
          have b13040 := hb (x 6 2 && x 6 13)
          have b13041 := hb (x 5 3 && x 5 14)
          clear * - r13036 b13037 b13038 b13039 b13040 b13041 d13031 d12913 d12813 d12755
          omega
        have d13042 : (x 8 3).toNat = 1 := by
          have r13043 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b13044 := hb (x 8 3)
          have b13045 := hb (x 8 11)
          clear * - r13043 b13044 b13045 d13035
          omega
        have d13046 : (x 11 12).toNat = 0 := by
          have r13047 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13048 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e13049 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b13050 := hb (x 8 3)
          have b13051 := hb (x 9 2)
          have b13052 := hb (x 10 13)
          have b13053 := hb (x 11 12)
          clear * - r13047 e13048 e13049 b13050 b13051 b13052 b13053 d12934 d13042
          omega
        have d13054 : (x 11 1 && x 11 12).toNat = 0 := by
          have r13055 := hand2 (x 11 1) (x 11 12)
          have b13056 := hb (x 11 12)
          have b13057 := hb (x 11 1 && x 11 12)
          clear * - r13055 b13056 b13057 d13046
          omega
        have d13058 : (x 10 13).toNat = 0 := by
          have r13059 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13060 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e13061 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b13062 := hb (x 8 3)
          have b13063 := hb (x 9 2)
          have b13064 := hb (x 10 13)
          have b13065 := hb (x 11 12)
          clear * - r13059 e13060 e13061 b13062 b13063 b13064 b13065 d13046 d12934 d13042
          omega
        have d13066 : (x 10 2 && x 10 13).toNat = 0 := by
          have r13067 := hand2 (x 10 2) (x 10 13)
          have b13068 := hb (x 10 13)
          have b13069 := hb (x 10 2 && x 10 13)
          clear * - r13067 b13068 b13069 d13058
          omega
        have d13070 : (x 12 11).toNat = 1 := by
          have r13071 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13072 := hb (x 8 4)
          have b13073 := hb (x 12 11)
          have b13074 := hb (x 11 1 && x 11 12)
          have b13075 := hb (x 10 2 && x 10 13)
          have b13076 := hb (x 9 3 && x 9 14)
          clear * - r13071 b13072 b13073 b13074 b13075 b13076 d13054 d13066 d12930 d12868
          omega
        have d13077 : (x 12 3).toNat = 1 := by
          have r13078 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
          have b13079 := hb (x 12 3)
          have b13080 := hb (x 12 11)
          clear * - r13078 b13079 b13080 d13070
          omega
        have d13081 : (x 15 12).toNat = 0 := by
          have r13082 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13083 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e13084 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b13085 := hb (x 12 3)
          have b13086 := hb (x 13 2)
          have b13087 := hb (x 14 13)
          have b13088 := hb (x 15 12)
          clear * - r13082 e13083 e13084 b13085 b13086 b13087 b13088 d13077
          omega
        have d13089 : (x 15 1 && x 15 12).toNat = 0 := by
          have r13090 := hand2 (x 15 1) (x 15 12)
          have b13091 := hb (x 15 12)
          have b13092 := hb (x 15 1 && x 15 12)
          clear * - r13090 b13091 b13092 d13081
          omega
        have d13093 : (x 14 13).toNat = 0 := by
          have r13094 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13095 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e13096 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b13097 := hb (x 12 3)
          have b13098 := hb (x 13 2)
          have b13099 := hb (x 14 13)
          have b13100 := hb (x 15 12)
          clear * - r13094 e13095 e13096 b13097 b13098 b13099 b13100 d13081 d13077
          omega
        have d13101 : (x 14 2 && x 14 13).toNat = 0 := by
          have r13102 := hand2 (x 14 2) (x 14 13)
          have b13103 := hb (x 14 13)
          have b13104 := hb (x 14 2 && x 14 13)
          clear * - r13102 b13103 b13104 d13093
          omega
        have d13105 : (x 13 2).toNat = 0 := by
          have r13106 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13107 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e13108 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b13109 := hb (x 12 3)
          have b13110 := hb (x 13 2)
          have b13111 := hb (x 14 13)
          have b13112 := hb (x 15 12)
          clear * - r13106 e13107 e13108 b13109 b13110 b13111 b13112 d13081 d13093 d13077
          omega
        have d13113 : (x 10 1).toNat = 1 := by
          have r13114 := hand1 (x 10 1) (x 10 14)
          have b13115 := hb (x 10 1)
          have b13116 := hb (x 10 1 && x 10 14)
          clear * - r13114 b13115 b13116 d13001
          omega
        have d13117 : (x 11 14).toNat = 0 := by
          have r13118 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13119 := hb (x 10 1)
          have b13120 := hb (x 11 14)
          clear * - r13118 b13119 b13120 d13113
          omega
        have d13121 : (x 11 1 && x 11 14).toNat = 0 := by
          have r13122 := hand2 (x 11 1) (x 11 14)
          have b13123 := hb (x 11 14)
          have b13124 := hb (x 11 1 && x 11 14)
          clear * - r13122 b13123 b13124 d13117
          omega
        have d13125 : (x 11 2).toNat = 0 := by
          have r13126 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b13127 := hb (x 11 2)
          have b13128 := hb (x 11 14)
          clear * - r13126 b13127 b13128 d13117
          omega
        have d13129 : (x 10 2).toNat = 0 := by
          have r13130 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13131 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e13132 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b13133 := hb (x 9 3)
          have b13134 := hb (x 10 2)
          have b13135 := hb (x 11 13)
          have b13136 := hb (x 12 12)
          clear * - r13130 e13131 e13132 b13133 b13134 b13135 b13136 d12973 d12989 d12969
          omega
        have d13137 : (x 12 13).toNat = 1 := by
          have r13138 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13139 := hb (x 10 2)
          have b13140 := hb (x 12 13)
          have b13141 := hb (x 11 1 && x 11 14)
          clear * - r13138 b13139 b13140 b13141 d13121 d13129
          omega
        have d13142 : (x 12 1).toNat = 1 := by
          have r13143 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b13144 := hb (x 12 1)
          have b13145 := hb (x 12 13)
          clear * - r13143 b13144 b13145 d13137
          omega
        have d13146 : (x 13 14).toNat = 0 := by
          have r13147 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13148 := hb (x 12 1)
          have b13149 := hb (x 13 14)
          clear * - r13147 b13148 b13149 d13142
          omega
        have d13150 : (x 13 1 && x 13 14).toNat = 0 := by
          have r13151 := hand2 (x 13 1) (x 13 14)
          have b13152 := hb (x 13 14)
          have b13153 := hb (x 13 1 && x 13 14)
          clear * - r13151 b13152 b13153 d13146
          omega
        have d13154 : (x 12 2).toNat = 1 := by
          have r13155 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13156 := hb (x 12 2)
          have b13157 := hb (x 14 13)
          have b13158 := hb (x 13 1 && x 13 14)
          clear * - r13155 b13156 b13157 b13158 d13093 d13150
          omega
        have d13159 : (x 14 12).toNat = 0 := by
          have r13160 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13161 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e13162 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b13163 := hb (x 11 3)
          have b13164 := hb (x 12 2)
          have b13165 := hb (x 13 13)
          have b13166 := hb (x 14 12)
          clear * - r13160 e13161 e13162 b13163 b13164 b13165 b13166 d13154
          omega
        have d13167 : (x 14 4).toNat = 0 := by
          have r13168 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
          have b13169 := hb (x 14 4)
          have b13170 := hb (x 14 12)
          clear * - r13168 b13169 b13170 d13159
          omega
        have d13171 : (x 14 4 && x 14 14).toNat = 0 := by
          have r13172 := hand1 (x 14 4) (x 14 14)
          have b13173 := hb (x 14 4)
          have b13174 := hb (x 14 4 && x 14 14)
          clear * - r13172 b13173 b13174 d13167
          omega
        have d13175 : (x 13 13).toNat = 0 := by
          have r13176 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13177 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e13178 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b13179 := hb (x 11 3)
          have b13180 := hb (x 12 2)
          have b13181 := hb (x 13 13)
          have b13182 := hb (x 14 12)
          clear * - r13176 e13177 e13178 b13179 b13180 b13181 b13182 d13159 d13154
          omega
        have d13183 : (x 13 5).toNat = 0 := by
          have r13184 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
          have b13185 := hb (x 13 5)
          have b13186 := hb (x 13 13)
          clear * - r13184 b13185 b13186 d13175
          omega
        have d13187 : (x 13 3 && x 13 14).toNat = 0 := by
          have r13188 := hand2 (x 13 3) (x 13 14)
          have b13189 := hb (x 13 14)
          have b13190 := hb (x 13 3 && x 13 14)
          clear * - r13188 b13189 b13190 d13146
          omega
        have d13191 : (x 16 11).toNat = 1 := by
          have r13192 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13193 := hb (x 12 4)
          have b13194 := hb (x 16 11)
          have b13195 := hb (x 15 1 && x 15 12)
          have b13196 := hb (x 14 2 && x 14 13)
          have b13197 := hb (x 13 3 && x 13 14)
          clear * - r13192 b13193 b13194 b13195 b13196 b13197 d13089 d13101 d13187 d12985
          omega
        have d13198 : (x 16 3).toNat = 1 := by
          have r13199 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
          have b13200 := hb (x 16 3)
          have b13201 := hb (x 16 11)
          clear * - r13199 b13200 b13201 d13191
          omega
        have d13202 : (x 19 12).toNat = 0 := by
          have r13203 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13204 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e13205 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b13206 := hb (x 16 3)
          have b13207 := hb (x 17 2)
          have b13208 := hb (x 18 13)
          have b13209 := hb (x 19 12)
          clear * - r13203 e13204 e13205 b13206 b13207 b13208 b13209 d13198
          omega
        have d13210 : (x 18 13).toNat = 0 := by
          have r13211 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13212 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e13213 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b13214 := hb (x 16 3)
          have b13215 := hb (x 17 2)
          have b13216 := hb (x 18 13)
          have b13217 := hb (x 19 12)
          clear * - r13211 e13212 e13213 b13214 b13215 b13216 b13217 d13202 d13198
          omega
        have d13218 : (x 17 2).toNat = 0 := by
          have r13219 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13220 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e13221 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b13222 := hb (x 16 3)
          have b13223 := hb (x 17 2)
          have b13224 := hb (x 18 13)
          have b13225 := hb (x 19 12)
          clear * - r13219 e13220 e13221 b13222 b13223 b13224 b13225 d13202 d13210 d13198
          omega
        have d13226 : (x 13 12).toNat = 0 := by
          have r13227 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13228 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e13229 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b13230 := hb (x 10 3)
          have b13231 := hb (x 11 2)
          have b13232 := hb (x 12 13)
          have b13233 := hb (x 13 12)
          clear * - r13227 e13228 e13229 b13230 b13231 b13232 b13233 d13137 d13125
          omega
        have d13234 : (x 13 4).toNat = 0 := by
          have r13235 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b13236 := hb (x 13 4)
          have b13237 := hb (x 13 12)
          clear * - r13235 b13236 b13237 d13226
          omega
        have d13238 : (x 10 3).toNat = 0 := by
          have r13239 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13240 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e13241 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b13242 := hb (x 10 3)
          have b13243 := hb (x 11 2)
          have b13244 := hb (x 12 13)
          have b13245 := hb (x 13 12)
          clear * - r13239 e13240 e13241 b13242 b13243 b13244 b13245 d13226 d13137 d13125
          omega
        have d13246 : (x 10 3 && x 10 14).toNat = 0 := by
          have r13247 := hand1 (x 10 3) (x 10 14)
          have b13248 := hb (x 10 3)
          have b13249 := hb (x 10 3 && x 10 14)
          clear * - r13247 b13248 b13249 d13238
          omega
        have d13250 : (x 13 11).toNat = 1 := by
          have r13251 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13252 := hb (x 9 4)
          have b13253 := hb (x 13 11)
          have b13254 := hb (x 12 1 && x 12 12)
          have b13255 := hb (x 11 2 && x 11 13)
          have b13256 := hb (x 10 3 && x 10 14)
          clear * - r13251 b13252 b13253 b13254 b13255 b13256 d12981 d12997 d13246 d12946
          omega
        have d13257 : (x 13 3).toNat = 1 := by
          have r13258 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
          have b13259 := hb (x 13 3)
          have b13260 := hb (x 13 11)
          clear * - r13258 b13259 b13260 d13250
          omega
        have d13261 : (x 16 12).toNat = 0 := by
          have r13262 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13263 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e13264 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b13265 := hb (x 13 3)
          have b13266 := hb (x 14 2)
          have b13267 := hb (x 15 13)
          have b13268 := hb (x 16 12)
          clear * - r13262 e13263 e13264 b13265 b13266 b13267 b13268 d13257
          omega
        have d13269 : (x 16 1 && x 16 12).toNat = 0 := by
          have r13270 := hand2 (x 16 1) (x 16 12)
          have b13271 := hb (x 16 12)
          have b13272 := hb (x 16 1 && x 16 12)
          clear * - r13270 b13271 b13272 d13261
          omega
        have d13273 : (x 16 2 && x 16 12).toNat = 0 := by
          have r13274 := hand2 (x 16 2) (x 16 12)
          have b13275 := hb (x 16 12)
          have b13276 := hb (x 16 2 && x 16 12)
          clear * - r13274 b13275 b13276 d13261
          omega
        have d13277 : (x 15 13).toNat = 0 := by
          have r13278 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13279 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e13280 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b13281 := hb (x 13 3)
          have b13282 := hb (x 14 2)
          have b13283 := hb (x 15 13)
          have b13284 := hb (x 16 12)
          clear * - r13278 e13279 e13280 b13281 b13282 b13283 b13284 d13261 d13257
          omega
        have d13285 : (x 15 2 && x 15 13).toNat = 0 := by
          have r13286 := hand2 (x 15 2) (x 15 13)
          have b13287 := hb (x 15 13)
          have b13288 := hb (x 15 2 && x 15 13)
          clear * - r13286 b13287 b13288 d13277
          omega
        have d13289 : (x 15 3 && x 15 13).toNat = 0 := by
          have r13290 := hand2 (x 15 3) (x 15 13)
          have b13291 := hb (x 15 13)
          have b13292 := hb (x 15 3 && x 15 13)
          clear * - r13290 b13291 b13292 d13277
          omega
        have d13293 : (x 14 1 && x 14 14).toNat = 1 := by
          have r13294 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13295 := hb (x 13 2)
          have b13296 := hb (x 15 13)
          have b13297 := hb (x 14 1 && x 14 14)
          clear * - r13294 b13295 b13296 b13297 d13277 d13105
          omega
        have d13298 : (x 14 1).toNat = 1 := by
          have r13299 := hand1 (x 14 1) (x 14 14)
          have b13300 := hb (x 14 1)
          have b13301 := hb (x 14 1 && x 14 14)
          clear * - r13299 b13300 b13301 d13293
          omega
        have d13302 : (x 15 14).toNat = 0 := by
          have r13303 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13304 := hb (x 14 1)
          have b13305 := hb (x 15 14)
          clear * - r13303 b13304 b13305 d13298
          omega
        have d13306 : (x 15 1 && x 15 14).toNat = 0 := by
          have r13307 := hand2 (x 15 1) (x 15 14)
          have b13308 := hb (x 15 14)
          have b13309 := hb (x 15 1 && x 15 14)
          clear * - r13307 b13308 b13309 d13302
          omega
        have d13310 : (x 15 2).toNat = 0 := by
          have r13311 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b13312 := hb (x 15 2)
          have b13313 := hb (x 15 14)
          clear * - r13311 b13312 b13313 d13302
          omega
        have d13314 : (x 14 2).toNat = 0 := by
          have r13315 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13316 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e13317 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b13318 := hb (x 13 3)
          have b13319 := hb (x 14 2)
          have b13320 := hb (x 15 13)
          have b13321 := hb (x 16 12)
          clear * - r13315 e13316 e13317 b13318 b13319 b13320 b13321 d13261 d13277 d13257
          omega
        have d13322 : (x 16 13).toNat = 1 := by
          have r13323 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13324 := hb (x 14 2)
          have b13325 := hb (x 16 13)
          have b13326 := hb (x 15 1 && x 15 14)
          clear * - r13323 b13324 b13325 b13326 d13306 d13314
          omega
        have d13327 : (x 17 12).toNat = 0 := by
          have r13328 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13329 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e13330 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b13331 := hb (x 14 3)
          have b13332 := hb (x 15 2)
          have b13333 := hb (x 16 13)
          have b13334 := hb (x 17 12)
          clear * - r13328 e13329 e13330 b13331 b13332 b13333 b13334 d13322 d13310
          omega
        have d13335 : (x 14 3).toNat = 0 := by
          have r13336 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13337 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e13338 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b13339 := hb (x 14 3)
          have b13340 := hb (x 15 2)
          have b13341 := hb (x 16 13)
          have b13342 := hb (x 17 12)
          clear * - r13336 e13337 e13338 b13339 b13340 b13341 b13342 d13327 d13322 d13310
          omega
        have d13343 : (x 14 3 && x 14 14).toNat = 0 := by
          have r13344 := hand1 (x 14 3) (x 14 14)
          have b13345 := hb (x 14 3)
          have b13346 := hb (x 14 3 && x 14 14)
          clear * - r13344 b13345 b13346 d13335
          omega
        have d13347 : (x 17 11).toNat = 1 := by
          have r13348 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13349 := hb (x 13 4)
          have b13350 := hb (x 17 11)
          have b13351 := hb (x 16 1 && x 16 12)
          have b13352 := hb (x 15 2 && x 15 13)
          have b13353 := hb (x 14 3 && x 14 14)
          clear * - r13348 b13349 b13350 b13351 b13352 b13353 d13269 d13285 d13343 d13234
          omega
        have d13354 : (x 17 3).toNat = 1 := by
          have r13355 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b13356 := hb (x 17 3)
          have b13357 := hb (x 17 11)
          clear * - r13355 b13356 b13357 d13347
          omega
        have d13358 : (x 20 12).toNat = 0 := by
          have r13359 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13360 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e13361 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b13362 := hb (x 17 3)
          have b13363 := hb (x 18 2)
          have b13364 := hb (x 19 13)
          have b13365 := hb (x 20 12)
          clear * - r13359 e13360 e13361 b13362 b13363 b13364 b13365 d13354
          omega
        have d13366 : (x 19 13).toNat = 0 := by
          have r13367 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13368 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e13369 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b13370 := hb (x 17 3)
          have b13371 := hb (x 18 2)
          have b13372 := hb (x 19 13)
          have b13373 := hb (x 20 12)
          clear * - r13367 e13368 e13369 b13370 b13371 b13372 b13373 d13358 d13354
          omega
        have d13374 : (x 18 1 && x 18 14).toNat = 1 := by
          have r13375 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13376 := hb (x 17 2)
          have b13377 := hb (x 19 13)
          have b13378 := hb (x 18 1 && x 18 14)
          clear * - r13375 b13376 b13377 b13378 d13366 d13218
          omega
        have d13379 : (x 18 14).toNat = 1 := by
          have r13380 := hand2 (x 18 1) (x 18 14)
          have b13381 := hb (x 18 14)
          have b13382 := hb (x 18 1 && x 18 14)
          clear * - r13380 b13381 b13382 d13374
          omega
        have d13383 : (x 17 1).toNat = 0 := by
          have r13384 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b13385 := hb (x 17 1)
          have b13386 := hb (x 18 14)
          clear * - r13384 b13385 b13386 d13379
          omega
        have d13387 : (x 17 1 && x 17 11).toNat = 0 := by
          have r13388 := hand1 (x 17 1) (x 17 11)
          have b13389 := hb (x 17 1)
          have b13390 := hb (x 17 1 && x 17 11)
          clear * - r13388 b13389 b13390 d13383
          omega
        have d13391 : (x 18 2).toNat = 0 := by
          have r13392 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e13393 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e13394 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b13395 := hb (x 17 3)
          have b13396 := hb (x 18 2)
          have b13397 := hb (x 19 13)
          have b13398 := hb (x 20 12)
          clear * - r13392 e13393 e13394 b13395 b13396 b13397 b13398 d13358 d13366 d13354
          omega
        have d13399 : (x 18 10).toNat = 0 := by
          have r13400 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
          have b13401 := hb (x 18 2)
          have b13402 := hb (x 18 10)
          clear * - r13400 b13401 b13402 d13391
          omega
        have r13403 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13404 := hb (x 13 5)
        have b13405 := hb (x 18 10)
        have b13406 := hb (x 17 1 && x 17 11)
        have b13407 := hb (x 16 2 && x 16 12)
        have b13408 := hb (x 15 3 && x 15 13)
        have b13409 := hb (x 14 4 && x 14 14)
        linarith only [r13403, b13404, b13405, b13406, b13407, b13408, b13409, d13399, d13387, d13273, d13289, d13171, d13183]
    · have f13410 : (x 1 1).toNat = 1 := by rw [h9313]; rfl
      have d13411 : (x 2 14).toNat = 0 := by
        have r13412 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13413 := hb (x 1 1)
        have b13414 := hb (x 2 14)
        clear * - r13412 b13413 b13414 f13410
        omega
      have d13415 : (x 2 1 && x 2 14).toNat = 0 := by
        have r13416 := hand2 (x 2 1) (x 2 14)
        have b13417 := hb (x 2 14)
        have b13418 := hb (x 2 1 && x 2 14)
        clear * - r13416 b13417 b13418 d13411
        omega
      have d13419 : (x 2 2).toNat = 0 := by
        have r13420 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b13421 := hb (x 2 2)
        have b13422 := hb (x 2 14)
        clear * - r13420 b13421 b13422 d13411
        omega
      have d13423 : (x 2 10).toNat = 0 := by
        have r13424 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
        have b13425 := hb (x 2 2)
        have b13426 := hb (x 2 10)
        clear * - r13424 b13425 b13426 d13419
        omega
      have d13427 : (x 2 1 && x 2 10).toNat = 0 := by
        have r13428 := hand2 (x 2 1) (x 2 10)
        have b13429 := hb (x 2 10)
        have b13430 := hb (x 2 1 && x 2 10)
        clear * - r13428 b13429 b13430 d13423
        omega
      have d13431 : (x 3 13).toNat = 1 := by
        have r13432 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13433 := hb (x 1 2)
        have b13434 := hb (x 3 13)
        have b13435 := hb (x 2 1 && x 2 14)
        clear * - r13432 b13433 b13434 b13435 d13415 g22
        omega
      have d13436 : (x 3 1).toNat = 1 := by
        have r13437 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b13438 := hb (x 3 1)
        have b13439 := hb (x 3 13)
        clear * - r13437 b13438 b13439 d13431
        omega
      have d13440 : (x 4 14).toNat = 0 := by
        have r13441 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13442 := hb (x 3 1)
        have b13443 := hb (x 4 14)
        clear * - r13441 b13442 b13443 d13436
        omega
      have d13444 : (x 4 1 && x 4 14).toNat = 0 := by
        have r13445 := hand2 (x 4 1) (x 4 14)
        have b13446 := hb (x 4 14)
        have b13447 := hb (x 4 1 && x 4 14)
        clear * - r13445 b13446 b13447 d13440
        omega
      have d13448 : (x 4 2).toNat = 0 := by
        have r13449 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
        have b13450 := hb (x 4 2)
        have b13451 := hb (x 4 14)
        clear * - r13449 b13450 b13451 d13440
        omega
      have d13452 : (x 4 10).toNat = 0 := by
        have r13453 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
        have b13454 := hb (x 4 2)
        have b13455 := hb (x 4 10)
        clear * - r13453 b13454 b13455 d13448
        omega
      have d13456 : (x 4 7 && x 4 10).toNat = 0 := by
        have r13457 := hand2 (x 4 7) (x 4 10)
        have b13458 := hb (x 4 10)
        have b13459 := hb (x 4 7 && x 4 10)
        clear * - r13457 b13458 b13459 d13452
        omega
      have d13460 : (x 4 12).toNat = 0 := by
        have r13461 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13462 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e13463 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b13464 := hb (x 1 3)
        have b13465 := hb (x 2 2)
        have b13466 := hb (x 3 13)
        have b13467 := hb (x 4 12)
        clear * - r13461 e13462 e13463 b13464 b13465 b13466 b13467 d13431 d13419
        omega
      have d13468 : (x 1 3).toNat = 0 := by
        have r13469 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13470 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e13471 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b13472 := hb (x 1 3)
        have b13473 := hb (x 2 2)
        have b13474 := hb (x 3 13)
        have b13475 := hb (x 4 12)
        clear * - r13469 e13470 e13471 b13472 b13473 b13474 b13475 d13460 d13431 d13419
        omega
      have d13476 : (x 1 1 && x 1 3).toNat = 0 := by
        have r13477 := hand2 (x 1 1) (x 1 3)
        have b13478 := hb (x 1 3)
        have b13479 := hb (x 1 1 && x 1 3)
        clear * - r13477 b13478 b13479 d13468
        omega
      have d13480 : (x 1 11).toNat = 0 := by
        have r13481 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b13482 := hb (x 1 3)
        have b13483 := hb (x 1 11)
        clear * - r13481 b13482 b13483 d13468
        omega
      have d13484 : (x 1 1 && x 1 11).toNat = 0 := by
        have r13485 := hand2 (x 1 1) (x 1 11)
        have b13486 := hb (x 1 11)
        have b13487 := hb (x 1 1 && x 1 11)
        clear * - r13485 b13486 b13487 d13480
        omega
      have d13488 : (x (-3) 4).toNat = 1 := by
        have r13489 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13490 := hb (x (-3) 4)
        have b13491 := hb (x 1 11)
        have b13492 := hb (x 0 1 && x 0 12)
        have b13493 := hb (x (-1) 2 && x (-1) 13)
        have b13494 := hb (x (-2) 3 && x (-2) 14)
        clear * - r13489 b13490 b13491 b13492 b13493 b13494 d13480 g84 g85 g86
        omega
      have d13495 : (x (-3) 12).toNat = 1 := by
        have r13496 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b13497 := hb (x (-3) 4)
        have b13498 := hb (x (-3) 12)
        clear * - r13496 b13497 b13498 d13488
        omega
      have d13499 : (x (-4) 13).toNat = 0 := by
        have r13500 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13501 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e13502 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b13503 := hb (x (-6) 3)
        have b13504 := hb (x (-5) 2)
        have b13505 := hb (x (-4) 13)
        have b13506 := hb (x (-3) 12)
        clear * - r13500 e13501 e13502 b13503 b13504 b13505 b13506 d13495
        omega
      have d13507 : (x (-4) 5).toNat = 0 := by
        have r13508 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
        have b13509 := hb (x (-4) 5)
        have b13510 := hb (x (-4) 13)
        clear * - r13508 b13509 b13510 d13499
        omega
      have d13511 : (x (-5) 2).toNat = 0 := by
        have r13512 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13513 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e13514 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b13515 := hb (x (-6) 3)
        have b13516 := hb (x (-5) 2)
        have b13517 := hb (x (-4) 13)
        have b13518 := hb (x (-3) 12)
        clear * - r13512 e13513 e13514 b13515 b13516 b13517 b13518 d13495 d13499
        omega
      have d13519 : (x 3 1 && x 3 11).toNat = 1 := by
        have r13520 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13521 := hb (x (-1) 5)
        have b13522 := hb (x 4 10)
        have b13523 := hb (x 3 1 && x 3 11)
        have b13524 := hb (x 2 2 && x 2 12)
        have b13525 := hb (x 1 3 && x 1 13)
        have b13526 := hb (x 0 4 && x 0 14)
        clear * - r13520 b13521 b13522 b13523 b13524 b13525 b13526 d13452 g81 g82 g83 g4
        omega
      have d13527 : (x 3 11).toNat = 1 := by
        have r13528 := hand2 (x 3 1) (x 3 11)
        have b13529 := hb (x 3 11)
        have b13530 := hb (x 3 1 && x 3 11)
        clear * - r13528 b13529 b13530 d13519
        omega
      have d13531 : (x 3 3).toNat = 1 := by
        have r13532 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
        have b13533 := hb (x 3 3)
        have b13534 := hb (x 3 11)
        clear * - r13532 b13533 b13534 d13527
        omega
      have d13535 : (x 6 12).toNat = 0 := by
        have r13536 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13537 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e13538 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b13539 := hb (x 3 3)
        have b13540 := hb (x 4 2)
        have b13541 := hb (x 5 13)
        have b13542 := hb (x 6 12)
        clear * - r13536 e13537 e13538 b13539 b13540 b13541 b13542 d13448 d13531
        omega
      have d13543 : (x 6 4).toNat = 0 := by
        have r13544 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
        have b13545 := hb (x 6 4)
        have b13546 := hb (x 6 12)
        clear * - r13544 b13545 b13546 d13535
        omega
      have d13547 : (x 6 4 && x 6 14).toNat = 0 := by
        have r13548 := hand1 (x 6 4) (x 6 14)
        have b13549 := hb (x 6 4)
        have b13550 := hb (x 6 4 && x 6 14)
        clear * - r13548 b13549 b13550 d13543
        omega
      have d13551 : (x 5 13).toNat = 0 := by
        have r13552 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13553 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e13554 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b13555 := hb (x 3 3)
        have b13556 := hb (x 4 2)
        have b13557 := hb (x 5 13)
        have b13558 := hb (x 6 12)
        clear * - r13552 e13553 e13554 b13555 b13556 b13557 b13558 d13535 d13448 d13531
        omega
      have d13559 : (x 5 5).toNat = 0 := by
        have r13560 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
        have b13561 := hb (x 5 5)
        have b13562 := hb (x 5 13)
        clear * - r13560 b13561 b13562 d13551
        omega
      have d13563 : (x 3 2).toNat = 1 := by
        have r13564 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13565 := hb (x 3 2)
        have b13566 := hb (x 5 13)
        have b13567 := hb (x 4 1 && x 4 14)
        clear * - r13564 b13565 b13566 b13567 d13551 d13444
        omega
      have d13568 : (x 3 14).toNat = 1 := by
        have r13569 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b13570 := hb (x 3 2)
        have b13571 := hb (x 3 14)
        clear * - r13569 b13570 b13571 d13563
        omega
      have d13572 : (x 2 1).toNat = 0 := by
        have r13573 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13574 := hb (x 2 1)
        have b13575 := hb (x 3 14)
        clear * - r13573 b13574 b13575 d13568
        omega
      have d13576 : (x 2 1 && x 2 11).toNat = 0 := by
        have r13577 := hand1 (x 2 1) (x 2 11)
        have b13578 := hb (x 2 1)
        have b13579 := hb (x 2 1 && x 2 11)
        clear * - r13577 b13578 b13579 d13572
        omega
      have d13580 : (x 2 9).toNat = 0 := by
        have r13581 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
        have b13582 := hb (x 2 1)
        have b13583 := hb (x 2 9)
        clear * - r13581 b13582 b13583 d13572
        omega
      have d13584 : (x 5 12).toNat = 0 := by
        have r13585 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13586 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e13587 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b13588 := hb (x 2 3)
        have b13589 := hb (x 3 2)
        have b13590 := hb (x 4 13)
        have b13591 := hb (x 5 12)
        clear * - r13585 e13586 e13587 b13588 b13589 b13590 b13591 d13563
        omega
      have d13592 : (x 4 13).toNat = 0 := by
        have r13593 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13594 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e13595 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b13596 := hb (x 2 3)
        have b13597 := hb (x 3 2)
        have b13598 := hb (x 4 13)
        have b13599 := hb (x 5 12)
        clear * - r13593 e13594 e13595 b13596 b13597 b13598 b13599 d13584 d13563
        omega
      have d13600 : (x 2 3).toNat = 0 := by
        have r13601 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13602 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e13603 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b13604 := hb (x 2 3)
        have b13605 := hb (x 3 2)
        have b13606 := hb (x 4 13)
        have b13607 := hb (x 5 12)
        clear * - r13601 e13602 e13603 b13604 b13605 b13606 b13607 d13584 d13592 d13563
        omega
      have d13608 : (x 2 11).toNat = 0 := by
        have r13609 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
        have b13610 := hb (x 2 3)
        have b13611 := hb (x 2 11)
        clear * - r13609 b13610 b13611 d13600
        omega
      have d13612 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
        have r13613 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13614 := hb (x (-4) 5)
        have b13615 := hb (x 1 10)
        have b13616 := hb (x 0 1 && x 0 11)
        have b13617 := hb (x (-1) 2 && x (-1) 12)
        have b13618 := hb (x (-2) 3 && x (-2) 13)
        have b13619 := hb (x (-3) 4 && x (-3) 14)
        clear * - r13613 b13614 b13615 b13616 b13617 b13618 b13619 g26 g74 g75 g76 d13507
        omega
      have d13620 : (x (-3) 14).toNat = 1 := by
        have r13621 := hand2 (x (-3) 4) (x (-3) 14)
        have b13622 := hb (x (-3) 14)
        have b13623 := hb (x (-3) 4 && x (-3) 14)
        clear * - r13621 b13622 b13623 d13612
        omega
      have d13624 : (x (-4) 1).toNat = 0 := by
        have r13625 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13626 := hb (x (-4) 1)
        have b13627 := hb (x (-3) 14)
        clear * - r13625 b13626 b13627 d13620
        omega
      have d13628 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
        have r13629 := hand1 (x (-4) 1) (x (-4) 14)
        have b13630 := hb (x (-4) 1)
        have b13631 := hb (x (-4) 1 && x (-4) 14)
        clear * - r13629 b13630 b13631 d13624
        omega
      have d13632 : (x (-3) 13).toNat = 1 := by
        have r13633 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13634 := hb (x (-5) 2)
        have b13635 := hb (x (-3) 13)
        have b13636 := hb (x (-4) 1 && x (-4) 14)
        clear * - r13633 b13634 b13635 b13636 d13628 d13511
        omega
      have d13637 : (x (-3) 1).toNat = 1 := by
        have r13638 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
        have b13639 := hb (x (-3) 1)
        have b13640 := hb (x (-3) 13)
        clear * - r13638 b13639 b13640 d13632
        omega
      have d13641 : (x (-2) 14).toNat = 0 := by
        have r13642 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13643 := hb (x (-3) 1)
        have b13644 := hb (x (-2) 14)
        clear * - r13642 b13643 b13644 d13637
        omega
      have d13645 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r13646 := hand2 (x (-2) 1) (x (-2) 14)
        have b13647 := hb (x (-2) 14)
        have b13648 := hb (x (-2) 1 && x (-2) 14)
        clear * - r13646 b13647 b13648 d13641
        omega
      have d13649 : (x (-3) 2).toNat = 1 := by
        have r13650 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13651 := hb (x (-3) 2)
        have b13652 := hb (x (-1) 13)
        have b13653 := hb (x (-2) 1 && x (-2) 14)
        clear * - r13650 b13651 b13652 b13653 g8 d13645
        omega
      have d13654 : (x (-1) 12).toNat = 0 := by
        have r13655 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13656 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e13657 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b13658 := hb (x (-4) 3)
        have b13659 := hb (x (-3) 2)
        have b13660 := hb (x (-2) 13)
        have b13661 := hb (x (-1) 12)
        clear * - r13655 e13656 e13657 b13658 b13659 b13660 b13661 d13649
        omega
      have d13662 : (x (-1) 4).toNat = 0 := by
        have r13663 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b13664 := hb (x (-1) 4)
        have b13665 := hb (x (-1) 12)
        clear * - r13663 b13664 b13665 d13654
        omega
      have d13666 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
        have r13667 := hand1 (x (-1) 4) (x (-1) 14)
        have b13668 := hb (x (-1) 4)
        have b13669 := hb (x (-1) 4 && x (-1) 14)
        clear * - r13667 b13668 b13669 d13662
        omega
      have d13670 : (x (-2) 13).toNat = 0 := by
        have r13671 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13672 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e13673 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b13674 := hb (x (-4) 3)
        have b13675 := hb (x (-3) 2)
        have b13676 := hb (x (-2) 13)
        have b13677 := hb (x (-1) 12)
        clear * - r13671 e13672 e13673 b13674 b13675 b13676 b13677 d13654 d13649
        omega
      have d13678 : (x (-2) 5).toNat = 0 := by
        have r13679 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
        have b13680 := hb (x (-2) 5)
        have b13681 := hb (x (-2) 13)
        clear * - r13679 b13680 b13681 d13670
        omega
      have d13682 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
        have r13683 := hand1 (x (-2) 5) (x (-2) 14)
        have b13684 := hb (x (-2) 5)
        have b13685 := hb (x (-2) 5 && x (-2) 14)
        clear * - r13683 b13684 b13685 d13678
        omega
      have d13686 : (x 3 10).toNat = 1 := by
        have r13687 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13688 := hb (x (-2) 5)
        have b13689 := hb (x 3 10)
        have b13690 := hb (x 2 1 && x 2 11)
        have b13691 := hb (x 1 2 && x 1 12)
        have b13692 := hb (x 0 3 && x 0 13)
        have b13693 := hb (x (-1) 4 && x (-1) 14)
        clear * - r13687 b13688 b13689 b13690 b13691 b13692 b13693 d13576 g79 g80 d13666 d13678
        omega
      have d13694 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
        have r13695 := hand2 (x (-2) 4) (x (-2) 14)
        have b13696 := hb (x (-2) 14)
        have b13697 := hb (x (-2) 4 && x (-2) 14)
        clear * - r13695 b13696 b13697 d13641
        omega
      have d13698 : (x (-3) 5).toNat = 1 := by
        have r13699 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13700 := hb (x (-3) 5)
        have b13701 := hb (x 2 10)
        have b13702 := hb (x 1 1 && x 1 11)
        have b13703 := hb (x 0 2 && x 0 12)
        have b13704 := hb (x (-1) 3 && x (-1) 13)
        have b13705 := hb (x (-2) 4 && x (-2) 14)
        clear * - r13699 b13700 b13701 b13702 b13703 b13704 b13705 d13423 d13484 g77 g78 d13694
        omega
      have d13706 : (x (-2) 6).toNat = 0 := by
        have r13707 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
        have b13708 := hb (x (-2) 6)
        have b13709 := hb (x (-2) 14)
        clear * - r13707 b13708 b13709 d13641
        omega
      have d13710 : (x (-2) 4 && x (-2) 6).toNat = 0 := by
        have r13711 := hand2 (x (-2) 4) (x (-2) 6)
        have b13712 := hb (x (-2) 6)
        have b13713 := hb (x (-2) 4 && x (-2) 6)
        clear * - r13711 b13712 b13713 d13706
        omega
      have d13714 : (x (-2) 12).toNat = 0 := by
        have r13715 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13716 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e13717 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b13718 := hb (x (-5) 3)
        have b13719 := hb (x (-4) 2)
        have b13720 := hb (x (-3) 13)
        have b13721 := hb (x (-2) 12)
        clear * - r13715 e13716 e13717 b13718 b13719 b13720 b13721 d13632
        omega
      have d13722 : (x (-2) 4).toNat = 0 := by
        have r13723 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have b13724 := hb (x (-2) 4)
        have b13725 := hb (x (-2) 12)
        clear * - r13723 b13724 b13725 d13714
        omega
      have d13726 : (x 6 8).toNat = 0 := by
        have r13727 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13728 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e13729 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e13730 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e13731 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e13732 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e13733 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b13734 := hb (x (-1) 7)
        have b13735 := hb (x 0 6)
        have b13736 := hb (x 1 5)
        have b13737 := hb (x 2 4)
        have b13738 := hb (x 3 11)
        have b13739 := hb (x 4 10)
        have b13740 := hb (x 5 9)
        have b13741 := hb (x 6 8)
        clear * - r13727 e13728 e13729 e13730 e13731 e13732 e13733 b13734 b13735 b13736 b13737 b13738 b13739 b13740 b13741 d13452 d13527 g29 g24 g14
        omega
      have d13742 : (x 6 5 && x 6 8).toNat = 0 := by
        have r13743 := hand2 (x 6 5) (x 6 8)
        have b13744 := hb (x 6 8)
        have b13745 := hb (x 6 5 && x 6 8)
        clear * - r13743 b13744 b13745 d13726
        omega
      have d13746 : (x 5 9).toNat = 0 := by
        have r13747 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13748 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e13749 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e13750 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e13751 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e13752 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e13753 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b13754 := hb (x (-1) 7)
        have b13755 := hb (x 0 6)
        have b13756 := hb (x 1 5)
        have b13757 := hb (x 2 4)
        have b13758 := hb (x 3 11)
        have b13759 := hb (x 4 10)
        have b13760 := hb (x 5 9)
        have b13761 := hb (x 6 8)
        clear * - r13747 e13748 e13749 e13750 e13751 e13752 e13753 b13754 b13755 b13756 b13757 b13758 b13759 b13760 b13761 d13726 d13452 d13527 g29 g24 g14
        omega
      have d13762 : (x 5 6 && x 5 9).toNat = 0 := by
        have r13763 := hand2 (x 5 6) (x 5 9)
        have b13764 := hb (x 5 9)
        have b13765 := hb (x 5 6 && x 5 9)
        clear * - r13763 b13764 b13765 d13746
        omega
      have d13766 : (x 5 8).toNat = 0 := by
        have r13767 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13768 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e13769 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e13770 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e13771 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e13772 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e13773 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b13774 := hb (x (-2) 7)
        have b13775 := hb (x (-1) 6)
        have b13776 := hb (x 0 5)
        have b13777 := hb (x 1 4)
        have b13778 := hb (x 2 11)
        have b13779 := hb (x 3 10)
        have b13780 := hb (x 4 9)
        have b13781 := hb (x 5 8)
        clear * - r13767 e13768 e13769 e13770 e13771 e13772 e13773 b13774 b13775 b13776 b13777 b13778 b13779 b13780 b13781 d13686 d13608 g23 g13
        omega
      have d13782 : (x 4 9).toNat = 0 := by
        have r13783 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13784 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e13785 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e13786 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e13787 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e13788 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e13789 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b13790 := hb (x (-2) 7)
        have b13791 := hb (x (-1) 6)
        have b13792 := hb (x 0 5)
        have b13793 := hb (x 1 4)
        have b13794 := hb (x 2 11)
        have b13795 := hb (x 3 10)
        have b13796 := hb (x 4 9)
        have b13797 := hb (x 5 8)
        clear * - r13783 e13784 e13785 e13786 e13787 e13788 e13789 b13790 b13791 b13792 b13793 b13794 b13795 b13796 b13797 d13766 d13686 d13608 g23 g13
        omega
      have d13798 : (x 2 8).toNat = 0 := by
        have r13799 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13800 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e13801 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e13802 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e13803 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e13804 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e13805 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b13806 := hb (x (-5) 7)
        have b13807 := hb (x (-4) 6)
        have b13808 := hb (x (-3) 5)
        have b13809 := hb (x (-2) 4)
        have b13810 := hb (x (-1) 11)
        have b13811 := hb (x 0 10)
        have b13812 := hb (x 1 9)
        have b13813 := hb (x 2 8)
        clear * - r13799 e13800 e13801 e13802 e13803 e13804 e13805 b13806 b13807 b13808 b13809 b13810 b13811 b13812 b13813 f9312 g7 d13722 d13698
        omega
      have d13814 : (x 1 9).toNat = 0 := by
        have r13815 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13816 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e13817 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e13818 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e13819 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e13820 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e13821 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b13822 := hb (x (-5) 7)
        have b13823 := hb (x (-4) 6)
        have b13824 := hb (x (-3) 5)
        have b13825 := hb (x (-2) 4)
        have b13826 := hb (x (-1) 11)
        have b13827 := hb (x 0 10)
        have b13828 := hb (x 1 9)
        have b13829 := hb (x 2 8)
        clear * - r13815 e13816 e13817 e13818 e13819 e13820 e13821 b13822 b13823 b13824 b13825 b13826 b13827 b13828 b13829 d13798 f9312 g7 d13722 d13698
        omega
      have d13830 : (x (-4) 6).toNat = 0 := by
        have r13831 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13832 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e13833 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e13834 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e13835 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e13836 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e13837 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b13838 := hb (x (-5) 7)
        have b13839 := hb (x (-4) 6)
        have b13840 := hb (x (-3) 5)
        have b13841 := hb (x (-2) 4)
        have b13842 := hb (x (-1) 11)
        have b13843 := hb (x 0 10)
        have b13844 := hb (x 1 9)
        have b13845 := hb (x 2 8)
        clear * - r13831 e13832 e13833 e13834 e13835 e13836 e13837 b13838 b13839 b13840 b13841 b13842 b13843 b13844 b13845 d13798 d13814 f9312 g7 d13722 d13698
        omega
      have d13846 : (x (-4) 6 && x (-4) 8).toNat = 0 := by
        have r13847 := hand1 (x (-4) 6) (x (-4) 8)
        have b13848 := hb (x (-4) 6)
        have b13849 := hb (x (-4) 6 && x (-4) 8)
        clear * - r13847 b13848 b13849 d13830
        omega
      have d13850 : (x (-5) 7).toNat = 0 := by
        have r13851 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13852 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e13853 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e13854 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e13855 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e13856 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e13857 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b13858 := hb (x (-5) 7)
        have b13859 := hb (x (-4) 6)
        have b13860 := hb (x (-3) 5)
        have b13861 := hb (x (-2) 4)
        have b13862 := hb (x (-1) 11)
        have b13863 := hb (x 0 10)
        have b13864 := hb (x 1 9)
        have b13865 := hb (x 2 8)
        clear * - r13851 e13852 e13853 e13854 e13855 e13856 e13857 b13858 b13859 b13860 b13861 b13862 b13863 b13864 b13865 d13798 d13814 f9312 g7 d13722 d13698 d13830
        omega
      have d13866 : (x (-5) 7 && x (-5) 9).toNat = 0 := by
        have r13867 := hand1 (x (-5) 7) (x (-5) 9)
        have b13868 := hb (x (-5) 7)
        have b13869 := hb (x (-5) 7 && x (-5) 9)
        clear * - r13867 b13868 b13869 d13850
        omega
      have d13870 : (x (-6) 8).toNat = 0 := by
        have r13871 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13872 := hb (x (-12) 14)
        have b13873 := hb (x (-11) 13)
        have b13874 := hb (x (-10) 12)
        have b13875 := hb (x (-9) 11)
        have b13876 := hb (x (-8) 10)
        have b13877 := hb (x (-7) 9)
        have b13878 := hb (x (-6) 8)
        have b13879 := hb (x (-5) 7)
        have b13880 := hb (x (-4) 6)
        have b13881 := hb (x (-3) 5)
        have b13882 := hb (x (-2) 4)
        have b13883 := hb (x (-1) 3)
        have b13884 := hb (x 0 2)
        have b13885 := hb (x 1 1)
        clear * - r13871 b13872 b13873 b13874 b13875 b13876 b13877 b13878 b13879 b13880 b13881 b13882 b13883 b13884 b13885 f13410 g10 g3 d13722 d13698 d13830 d13850
        omega
      have d13886 : (x (-6) 8 && x (-6) 10).toNat = 0 := by
        have r13887 := hand1 (x (-6) 8) (x (-6) 10)
        have b13888 := hb (x (-6) 8)
        have b13889 := hb (x (-6) 8 && x (-6) 10)
        clear * - r13887 b13888 b13889 d13870
        omega
      have d13890 : (x (-7) 9).toNat = 0 := by
        have r13891 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13892 := hb (x (-12) 14)
        have b13893 := hb (x (-11) 13)
        have b13894 := hb (x (-10) 12)
        have b13895 := hb (x (-9) 11)
        have b13896 := hb (x (-8) 10)
        have b13897 := hb (x (-7) 9)
        have b13898 := hb (x (-6) 8)
        have b13899 := hb (x (-5) 7)
        have b13900 := hb (x (-4) 6)
        have b13901 := hb (x (-3) 5)
        have b13902 := hb (x (-2) 4)
        have b13903 := hb (x (-1) 3)
        have b13904 := hb (x 0 2)
        have b13905 := hb (x 1 1)
        clear * - r13891 b13892 b13893 b13894 b13895 b13896 b13897 b13898 b13899 b13900 b13901 b13902 b13903 b13904 b13905 f13410 g10 g3 d13722 d13698 d13830 d13850 d13870
        omega
      have d13906 : (x (-7) 9 && x (-7) 11).toNat = 0 := by
        have r13907 := hand1 (x (-7) 9) (x (-7) 11)
        have b13908 := hb (x (-7) 9)
        have b13909 := hb (x (-7) 9 && x (-7) 11)
        clear * - r13907 b13908 b13909 d13890
        omega
      have d13910 : (x (-8) 10).toNat = 0 := by
        have r13911 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13912 := hb (x (-12) 14)
        have b13913 := hb (x (-11) 13)
        have b13914 := hb (x (-10) 12)
        have b13915 := hb (x (-9) 11)
        have b13916 := hb (x (-8) 10)
        have b13917 := hb (x (-7) 9)
        have b13918 := hb (x (-6) 8)
        have b13919 := hb (x (-5) 7)
        have b13920 := hb (x (-4) 6)
        have b13921 := hb (x (-3) 5)
        have b13922 := hb (x (-2) 4)
        have b13923 := hb (x (-1) 3)
        have b13924 := hb (x 0 2)
        have b13925 := hb (x 1 1)
        clear * - r13911 b13912 b13913 b13914 b13915 b13916 b13917 b13918 b13919 b13920 b13921 b13922 b13923 b13924 b13925 f13410 g10 g3 d13722 d13698 d13830 d13850 d13870 d13890
        omega
      have d13926 : (x (-8) 10 && x (-8) 12).toNat = 0 := by
        have r13927 := hand1 (x (-8) 10) (x (-8) 12)
        have b13928 := hb (x (-8) 10)
        have b13929 := hb (x (-8) 10 && x (-8) 12)
        clear * - r13927 b13928 b13929 d13910
        omega
      have d13930 : (x (-9) 11).toNat = 0 := by
        have r13931 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13932 := hb (x (-12) 14)
        have b13933 := hb (x (-11) 13)
        have b13934 := hb (x (-10) 12)
        have b13935 := hb (x (-9) 11)
        have b13936 := hb (x (-8) 10)
        have b13937 := hb (x (-7) 9)
        have b13938 := hb (x (-6) 8)
        have b13939 := hb (x (-5) 7)
        have b13940 := hb (x (-4) 6)
        have b13941 := hb (x (-3) 5)
        have b13942 := hb (x (-2) 4)
        have b13943 := hb (x (-1) 3)
        have b13944 := hb (x 0 2)
        have b13945 := hb (x 1 1)
        clear * - r13931 b13932 b13933 b13934 b13935 b13936 b13937 b13938 b13939 b13940 b13941 b13942 b13943 b13944 b13945 f13410 g10 g3 d13722 d13698 d13830 d13850 d13870 d13890 d13910
        omega
      have d13946 : (x (-9) 11 && x (-9) 13).toNat = 0 := by
        have r13947 := hand1 (x (-9) 11) (x (-9) 13)
        have b13948 := hb (x (-9) 11)
        have b13949 := hb (x (-9) 11 && x (-9) 13)
        clear * - r13947 b13948 b13949 d13930
        omega
      have d13950 : (x (-10) 12).toNat = 0 := by
        have r13951 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13952 := hb (x (-12) 14)
        have b13953 := hb (x (-11) 13)
        have b13954 := hb (x (-10) 12)
        have b13955 := hb (x (-9) 11)
        have b13956 := hb (x (-8) 10)
        have b13957 := hb (x (-7) 9)
        have b13958 := hb (x (-6) 8)
        have b13959 := hb (x (-5) 7)
        have b13960 := hb (x (-4) 6)
        have b13961 := hb (x (-3) 5)
        have b13962 := hb (x (-2) 4)
        have b13963 := hb (x (-1) 3)
        have b13964 := hb (x 0 2)
        have b13965 := hb (x 1 1)
        clear * - r13951 b13952 b13953 b13954 b13955 b13956 b13957 b13958 b13959 b13960 b13961 b13962 b13963 b13964 b13965 f13410 g10 g3 d13722 d13698 d13830 d13850 d13870 d13890 d13910 d13930
        omega
      have d13966 : (x (-10) 12 && x (-10) 14).toNat = 0 := by
        have r13967 := hand1 (x (-10) 12) (x (-10) 14)
        have b13968 := hb (x (-10) 12)
        have b13969 := hb (x (-10) 12 && x (-10) 14)
        clear * - r13967 b13968 b13969 d13950
        omega
      have d13970 : (x (-11) 13).toNat = 0 := by
        have r13971 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13972 := hb (x (-12) 14)
        have b13973 := hb (x (-11) 13)
        have b13974 := hb (x (-10) 12)
        have b13975 := hb (x (-9) 11)
        have b13976 := hb (x (-8) 10)
        have b13977 := hb (x (-7) 9)
        have b13978 := hb (x (-6) 8)
        have b13979 := hb (x (-5) 7)
        have b13980 := hb (x (-4) 6)
        have b13981 := hb (x (-3) 5)
        have b13982 := hb (x (-2) 4)
        have b13983 := hb (x (-1) 3)
        have b13984 := hb (x 0 2)
        have b13985 := hb (x 1 1)
        clear * - r13971 b13972 b13973 b13974 b13975 b13976 b13977 b13978 b13979 b13980 b13981 b13982 b13983 b13984 b13985 f13410 g10 g3 d13722 d13698 d13830 d13850 d13870 d13890 d13910 d13930 d13950
        omega
      have d13986 : (x (-3) 5 && x (-3) 7).toNat = 1 := by
        have r13987 : 1 ≤ (x 2 2).toNat + (x 1 1 && x 1 3).toNat + (x 0 2 && x 0 4).toNat + (x (-1) 3 && x (-1) 5).toNat + (x (-2) 4 && x (-2) 6).toNat + (x (-3) 5 && x (-3) 7).toNat + (x (-4) 6 && x (-4) 8).toNat + (x (-5) 7 && x (-5) 9).toNat + (x (-6) 8 && x (-6) 10).toNat + (x (-7) 9 && x (-7) 11).toNat + (x (-8) 10 && x (-8) 12).toNat + (x (-9) 11 && x (-9) 13).toNat + (x (-10) 12 && x (-10) 14).toNat + (x (-11) 13).toNat := by have q := hcov2 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13988 := hb (x (-11) 13)
        have b13989 := hb (x 2 2)
        have b13990 := hb (x 1 1 && x 1 3)
        have b13991 := hb (x 0 2 && x 0 4)
        have b13992 := hb (x (-1) 3 && x (-1) 5)
        have b13993 := hb (x (-2) 4 && x (-2) 6)
        have b13994 := hb (x (-3) 5 && x (-3) 7)
        have b13995 := hb (x (-4) 6 && x (-4) 8)
        have b13996 := hb (x (-5) 7 && x (-5) 9)
        have b13997 := hb (x (-6) 8 && x (-6) 10)
        have b13998 := hb (x (-7) 9 && x (-7) 11)
        have b13999 := hb (x (-8) 10 && x (-8) 12)
        have b14000 := hb (x (-9) 11 && x (-9) 13)
        have b14001 := hb (x (-10) 12 && x (-10) 14)
        clear * - r13987 b13988 b13989 b13990 b13991 b13992 b13993 b13994 b13995 b13996 b13997 b13998 b13999 b14000 b14001 d13419 d13476 g31 g32 d13710 d13846 d13866 d13886 d13906 d13926 d13946 d13966 d13970
        omega
      have d14002 : (x (-3) 7).toNat = 1 := by
        have r14003 := hand2 (x (-3) 5) (x (-3) 7)
        have b14004 := hb (x (-3) 7)
        have b14005 := hb (x (-3) 5 && x (-3) 7)
        clear * - r14003 b14004 b14005 d13986
        omega
      have d14006 : (x 4 8).toNat = 0 := by
        have r14007 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e14008 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e14009 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e14010 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e14011 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e14012 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e14013 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b14014 := hb (x (-3) 7)
        have b14015 := hb (x (-2) 6)
        have b14016 := hb (x (-1) 5)
        have b14017 := hb (x 0 4)
        have b14018 := hb (x 1 11)
        have b14019 := hb (x 2 10)
        have b14020 := hb (x 3 9)
        have b14021 := hb (x 4 8)
        clear * - r14007 e14008 e14009 e14010 e14011 e14012 e14013 b14014 b14015 b14016 b14017 b14018 b14019 b14020 b14021 d13423 d13480 g12 g4 d13706 d14002
        omega
      have d14022 : (x 3 9).toNat = 0 := by
        have r14023 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e14024 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e14025 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e14026 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e14027 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e14028 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e14029 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b14030 := hb (x (-3) 7)
        have b14031 := hb (x (-2) 6)
        have b14032 := hb (x (-1) 5)
        have b14033 := hb (x 0 4)
        have b14034 := hb (x 1 11)
        have b14035 := hb (x 2 10)
        have b14036 := hb (x 3 9)
        have b14037 := hb (x 4 8)
        clear * - r14023 e14024 e14025 e14026 e14027 e14028 e14029 b14030 b14031 b14032 b14033 b14034 b14035 b14036 b14037 d14006 d13423 d13480 g12 g4 d13706 d14002
        omega
      have d14038 : (x (-3) 6).toNat = 1 := by
        have r14039 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b14040 := hb (x (-3) 6)
        have b14041 := hb (x 3 9)
        have b14042 := hb (x 2 1 && x 2 10)
        have b14043 := hb (x 1 2 && x 1 11)
        have b14044 := hb (x 0 3 && x 0 12)
        have b14045 := hb (x (-1) 4 && x (-1) 13)
        have b14046 := hb (x (-2) 5 && x (-2) 14)
        clear * - r14039 b14040 b14041 b14042 b14043 b14044 b14045 b14046 d14022 d13427 g71 g72 g73 d13682
        omega
      have d14047 : (x 3 8).toNat = 0 := by
        have r14048 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e14049 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e14050 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e14051 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e14052 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e14053 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e14054 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b14055 := hb (x (-4) 7)
        have b14056 := hb (x (-3) 6)
        have b14057 := hb (x (-2) 5)
        have b14058 := hb (x (-1) 4)
        have b14059 := hb (x 0 11)
        have b14060 := hb (x 1 10)
        have b14061 := hb (x 2 9)
        have b14062 := hb (x 3 8)
        clear * - r14048 e14049 e14050 e14051 e14052 e14053 e14054 b14055 b14056 b14057 b14058 b14059 b14060 b14061 b14062 d13580 g26 g18 d13662 d13678 d14038
        omega
      have d14063 : (x 3 8 && x 3 11).toNat = 0 := by
        have r14064 := hand1 (x 3 8) (x 3 11)
        have b14065 := hb (x 3 8)
        have b14066 := hb (x 3 8 && x 3 11)
        clear * - r14064 b14065 b14066 d14047
        omega
      have r14067 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r14068 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r14069 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r14070 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14071 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e14072 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e14073 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e14074 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e14075 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e14076 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have r14077 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14078 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
      have e14079 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
      have e14080 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
      have e14081 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
      have e14082 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
      have e14083 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
      have r14084 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14085 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e14086 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have r14087 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14088 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e14089 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have r14090 : 1 ≤ (x 11 3).toNat + (x 10 1 && x 10 4).toNat + (x 9 2 && x 9 5).toNat + (x 8 3 && x 8 6).toNat + (x 7 4 && x 7 7).toNat + (x 6 5 && x 6 8).toNat + (x 5 6 && x 5 9).toNat + (x 4 7 && x 4 10).toNat + (x 3 8 && x 3 11).toNat + (x 2 9 && x 2 12).toNat + (x 1 10 && x 1 13).toNat + (x 0 11 && x 0 14).toNat + (x (-1) 12).toNat := by have q := hcov3 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r14091 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r14092 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r14093 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r14094 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r14095 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
      have r14096 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
      have r14097 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
      have r14098 := hand2 (x 10 1) (x 10 4)
      have r14099 := hand2 (x 9 2) (x 9 5)
      have r14100 := hand2 (x 8 3) (x 8 6)
      have r14101 := hand2 (x 7 4) (x 7 7)
      have r14102 := hand2 (x 9 1) (x 9 11)
      have r14103 := hand1 (x 8 2) (x 8 12)
      have r14104 := hand1 (x 7 3) (x 7 13)
      have r14105 := hand1 (x 13 1) (x 13 11)
      have r14106 := hand1 (x 12 2) (x 12 12)
      have r14107 := hand2 (x 11 3) (x 11 13)
      have r14108 := hand1 (x 10 4) (x 10 14)
      have r14109 := hand2 (x 12 1) (x 12 12)
      have r14110 := hand2 (x 11 2) (x 11 13)
      have r14111 := hand1 (x 10 3) (x 10 14)
      have r14112 := hand1 (x 12 1) (x 12 14)
      have b14159 := hb (x 11 1)
      linarith only [r14067, r14068, r14069, r14070, e14071, e14072, e14073, e14074, e14075, e14076, r14077, e14078, e14079, e14080, e14081, e14082, e14083, r14084, e14085, e14086, r14087, e14088, e14089, r14090, r14091, r14092, r14093, r14094, r14095, r14096, r14097, r14098, r14099, r14100, r14101, r14102, r14103, r14104, r14105, r14106, r14107, r14108, r14109, r14110, r14111, r14112, b14159, d13641, d13654, g8, g19, g20, g21, d13480, g27, g28, d13423, d13608, g30, d14022, d13686, d13527, d14006, d13782, d13452, d13559, d13766, d13746, d13726, d13742, d13762, d13456, d14063, g38, g39, g40, d13547]
  · have f14199 : (x 0 10).toNat = 1 := by rw [h9311]; rfl
    have d14200 : (x 2 8).toNat = 0 := by
      have r14201 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14202 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e14203 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e14204 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e14205 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e14206 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e14207 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b14208 := hb (x (-5) 7)
      have b14209 := hb (x (-4) 6)
      have b14210 := hb (x (-3) 5)
      have b14211 := hb (x (-2) 4)
      have b14212 := hb (x (-1) 11)
      have b14213 := hb (x 0 10)
      have b14214 := hb (x 1 9)
      have b14215 := hb (x 2 8)
      clear * - r14201 e14202 e14203 e14204 e14205 e14206 e14207 b14208 b14209 b14210 b14211 b14212 b14213 b14214 b14215 f14199 g7
      omega
    have d14216 : (x 1 9).toNat = 0 := by
      have r14217 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14218 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e14219 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e14220 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e14221 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e14222 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e14223 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b14224 := hb (x (-5) 7)
      have b14225 := hb (x (-4) 6)
      have b14226 := hb (x (-3) 5)
      have b14227 := hb (x (-2) 4)
      have b14228 := hb (x (-1) 11)
      have b14229 := hb (x 0 10)
      have b14230 := hb (x 1 9)
      have b14231 := hb (x 2 8)
      clear * - r14217 e14218 e14219 e14220 e14221 e14222 e14223 b14224 b14225 b14226 b14227 b14228 b14229 b14230 b14231 d14200 f14199 g7
      omega
    have d14232 : (x (-2) 4).toNat = 0 := by
      have r14233 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14234 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e14235 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e14236 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e14237 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e14238 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e14239 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b14240 := hb (x (-5) 7)
      have b14241 := hb (x (-4) 6)
      have b14242 := hb (x (-3) 5)
      have b14243 := hb (x (-2) 4)
      have b14244 := hb (x (-1) 11)
      have b14245 := hb (x 0 10)
      have b14246 := hb (x 1 9)
      have b14247 := hb (x 2 8)
      clear * - r14233 e14234 e14235 e14236 e14237 e14238 e14239 b14240 b14241 b14242 b14243 b14244 b14245 b14246 b14247 d14200 d14216 f14199 g7
      omega
    have d14248 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
      have r14249 := hand1 (x (-2) 4) (x (-2) 13)
      have b14250 := hb (x (-2) 4)
      have b14251 := hb (x (-2) 4 && x (-2) 13)
      clear * - r14249 b14250 b14251 d14232
      omega
    have d14252 : (x (-3) 5).toNat = 0 := by
      have r14253 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14254 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e14255 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e14256 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e14257 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e14258 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e14259 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b14260 := hb (x (-5) 7)
      have b14261 := hb (x (-4) 6)
      have b14262 := hb (x (-3) 5)
      have b14263 := hb (x (-2) 4)
      have b14264 := hb (x (-1) 11)
      have b14265 := hb (x 0 10)
      have b14266 := hb (x 1 9)
      have b14267 := hb (x 2 8)
      clear * - r14253 e14254 e14255 e14256 e14257 e14258 e14259 b14260 b14261 b14262 b14263 b14264 b14265 b14266 b14267 d14200 d14216 f14199 g7 d14232
      omega
    have d14268 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
      have r14269 := hand1 (x (-3) 5) (x (-3) 14)
      have b14270 := hb (x (-3) 5)
      have b14271 := hb (x (-3) 5 && x (-3) 14)
      clear * - r14269 b14270 b14271 d14252
      omega
    have d14272 : (x (-4) 6).toNat = 0 := by
      have r14273 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14274 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e14275 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e14276 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e14277 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e14278 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e14279 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b14280 := hb (x (-5) 7)
      have b14281 := hb (x (-4) 6)
      have b14282 := hb (x (-3) 5)
      have b14283 := hb (x (-2) 4)
      have b14284 := hb (x (-1) 11)
      have b14285 := hb (x 0 10)
      have b14286 := hb (x 1 9)
      have b14287 := hb (x 2 8)
      clear * - r14273 e14274 e14275 e14276 e14277 e14278 e14279 b14280 b14281 b14282 b14283 b14284 b14285 b14286 b14287 d14200 d14216 f14199 g7 d14232 d14252
      omega
    have d14288 : (x 2 9).toNat = 1 := by
      have r14289 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14290 := hb (x (-4) 6)
      have b14291 := hb (x 2 9)
      have b14292 := hb (x 1 1 && x 1 10)
      have b14293 := hb (x 0 2 && x 0 11)
      have b14294 := hb (x (-1) 3 && x (-1) 12)
      have b14295 := hb (x (-2) 4 && x (-2) 13)
      have b14296 := hb (x (-3) 5 && x (-3) 14)
      clear * - r14289 b14290 b14291 b14292 b14293 b14294 b14295 b14296 g68 g69 g70 d14248 d14268 d14272
      omega
    have d14297 : (x 2 1).toNat = 1 := by
      have r14298 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
      have b14299 := hb (x 2 1)
      have b14300 := hb (x 2 9)
      clear * - r14298 b14299 b14300 d14288
      omega
    have d14301 : (x 3 14).toNat = 0 := by
      have r14302 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14303 := hb (x 2 1)
      have b14304 := hb (x 3 14)
      clear * - r14302 b14303 b14304 d14297
      omega
    have d14305 : (x 3 2).toNat = 0 := by
      have r14306 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b14307 := hb (x 3 2)
      have b14308 := hb (x 3 14)
      clear * - r14306 b14307 b14308 d14301
      omega
    have d14309 : (x 3 8).toNat = 0 := by
      have r14310 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14311 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e14312 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e14313 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e14314 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e14315 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e14316 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b14317 := hb (x (-4) 7)
      have b14318 := hb (x (-3) 6)
      have b14319 := hb (x (-2) 5)
      have b14320 := hb (x (-1) 4)
      have b14321 := hb (x 0 11)
      have b14322 := hb (x 1 10)
      have b14323 := hb (x 2 9)
      have b14324 := hb (x 3 8)
      clear * - r14310 e14311 e14312 e14313 e14314 e14315 e14316 b14317 b14318 b14319 b14320 b14321 b14322 b14323 b14324 d14288 g26 g18
      omega
    have d14325 : (x (-1) 4).toNat = 0 := by
      have r14326 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14327 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e14328 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e14329 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e14330 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e14331 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e14332 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b14333 := hb (x (-4) 7)
      have b14334 := hb (x (-3) 6)
      have b14335 := hb (x (-2) 5)
      have b14336 := hb (x (-1) 4)
      have b14337 := hb (x 0 11)
      have b14338 := hb (x 1 10)
      have b14339 := hb (x 2 9)
      have b14340 := hb (x 3 8)
      clear * - r14326 e14327 e14328 e14329 e14330 e14331 e14332 b14333 b14334 b14335 b14336 b14337 b14338 b14339 b14340 d14309 d14288 g26 g18
      omega
    have d14341 : (x 3 11).toNat = 1 := by
      have r14342 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14343 := hb (x (-1) 4)
      have b14344 := hb (x 3 11)
      have b14345 := hb (x 2 1 && x 2 12)
      have b14346 := hb (x 1 2 && x 1 13)
      have b14347 := hb (x 0 3 && x 0 14)
      clear * - r14342 b14343 b14344 b14345 b14346 b14347 g87 g88 g89 d14325
      omega
    have d14348 : (x 3 3).toNat = 1 := by
      have r14349 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b14350 := hb (x 3 3)
      have b14351 := hb (x 3 11)
      clear * - r14349 b14350 b14351 d14341
      omega
    have d14352 : (x 6 12).toNat = 0 := by
      have r14353 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14354 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e14355 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b14356 := hb (x 3 3)
      have b14357 := hb (x 4 2)
      have b14358 := hb (x 5 13)
      have b14359 := hb (x 6 12)
      clear * - r14353 e14354 e14355 b14356 b14357 b14358 b14359 d14348
      omega
    have d14360 : (x 5 13).toNat = 0 := by
      have r14361 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14362 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e14363 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b14364 := hb (x 3 3)
      have b14365 := hb (x 4 2)
      have b14366 := hb (x 5 13)
      have b14367 := hb (x 6 12)
      clear * - r14361 e14362 e14363 b14364 b14365 b14366 b14367 d14352 d14348
      omega
    have d14368 : (x 4 1 && x 4 14).toNat = 1 := by
      have r14369 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14370 := hb (x 3 2)
      have b14371 := hb (x 5 13)
      have b14372 := hb (x 4 1 && x 4 14)
      clear * - r14369 b14370 b14371 b14372 d14360 d14305
      omega
    have d14373 : (x 4 14).toNat = 1 := by
      have r14374 := hand2 (x 4 1) (x 4 14)
      have b14375 := hb (x 4 14)
      have b14376 := hb (x 4 1 && x 4 14)
      clear * - r14374 b14375 b14376 d14368
      omega
    have d14377 : (x 3 1).toNat = 0 := by
      have r14378 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14379 := hb (x 3 1)
      have b14380 := hb (x 4 14)
      clear * - r14378 b14379 b14380 d14373
      omega
    have d14381 : (x 3 1 && x 3 11).toNat = 0 := by
      have r14382 := hand1 (x 3 1) (x 3 11)
      have b14383 := hb (x 3 1)
      have b14384 := hb (x 3 1 && x 3 11)
      clear * - r14382 b14383 b14384 d14377
      omega
    have d14385 : (x 4 10).toNat = 1 := by
      have r14386 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b14387 := hb (x (-1) 5)
      have b14388 := hb (x 4 10)
      have b14389 := hb (x 3 1 && x 3 11)
      have b14390 := hb (x 2 2 && x 2 12)
      have b14391 := hb (x 1 3 && x 1 13)
      have b14392 := hb (x 0 4 && x 0 14)
      clear * - r14386 b14387 b14388 b14389 b14390 b14391 b14392 d14381 g81 g82 g83 g4
      omega
    have d14393 : (x 4 2).toNat = 1 := by
      have r14394 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
      have b14395 := hb (x 4 2)
      have b14396 := hb (x 4 10)
      clear * - r14394 b14395 b14396 d14385
      omega
    have r14397 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14398 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e14399 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b14400 := hb (x 3 3)
    have b14401 := hb (x 4 2)
    have b14402 := hb (x 5 13)
    have b14403 := hb (x 6 12)
    linarith only [r14397, e14398, e14399, b14400, b14401, b14402, b14403, d14352, d14360, d14393, d14348]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000000 (x : ℤ → Fin 16 → Bool)
    (hcount : ∀ u : ℤ, (x (u - 1) 1).toNat + (x (u - 2) 2).toNat + (x (u - 3) 3).toNat + (x (u - 4) 4).toNat + (x (u - 5) 5).toNat + (x (u - 6) 6).toNat + (x (u - 7) 7).toNat + (x (u - 8) 8).toNat + (x (u - 9) 9).toNat + (x (u - 10) 10).toNat + (x (u - 11) 11).toNat + (x (u - 12) 12).toNat + (x (u - 13) 13).toNat + (x (u - 14) 14).toNat = 3)
    (hd14 : ∀ u : ℤ, (x u 14).toNat + (x (u - 1) 1).toNat = 1)
    (hd12 : ∀ u : ℤ, (x u 12).toNat + (x (u - 1) 1 && x (u - 1) 13).toNat + (x (u - 2) 2 && x (u - 2) 14).toNat + (x (u - 3) 3).toNat = 1)
    (hd8 : ∀ u : ℤ, (x u 8).toNat + (x (u - 1) 1 && x (u - 1) 9).toNat + (x (u - 2) 2 && x (u - 2) 10).toNat + (x (u - 3) 3 && x (u - 3) 11).toNat + (x (u - 4) 4 && x (u - 4) 12).toNat + (x (u - 5) 5 && x (u - 5) 13).toNat + (x (u - 6) 6 && x (u - 6) 14).toNat + (x (u - 7) 7).toNat = 1)
    (hcov1 : ∀ u : ℤ, 1 ≤ (x u 1).toNat + (x (u - 1) 1 && x (u - 1) 2).toNat + (x (u - 2) 2 && x (u - 2) 3).toNat + (x (u - 3) 3 && x (u - 3) 4).toNat + (x (u - 4) 4 && x (u - 4) 5).toNat + (x (u - 5) 5 && x (u - 5) 6).toNat + (x (u - 6) 6 && x (u - 6) 7).toNat + (x (u - 7) 7 && x (u - 7) 8).toNat + (x (u - 8) 8 && x (u - 8) 9).toNat + (x (u - 9) 9 && x (u - 9) 10).toNat + (x (u - 10) 10 && x (u - 10) 11).toNat + (x (u - 11) 11 && x (u - 11) 12).toNat + (x (u - 12) 12 && x (u - 12) 13).toNat + (x (u - 13) 13 && x (u - 13) 14).toNat + (x (u - 14) 14).toNat)
    (hcov2 : ∀ u : ℤ, 1 ≤ (x u 2).toNat + (x (u - 1) 1 && x (u - 1) 3).toNat + (x (u - 2) 2 && x (u - 2) 4).toNat + (x (u - 3) 3 && x (u - 3) 5).toNat + (x (u - 4) 4 && x (u - 4) 6).toNat + (x (u - 5) 5 && x (u - 5) 7).toNat + (x (u - 6) 6 && x (u - 6) 8).toNat + (x (u - 7) 7 && x (u - 7) 9).toNat + (x (u - 8) 8 && x (u - 8) 10).toNat + (x (u - 9) 9 && x (u - 9) 11).toNat + (x (u - 10) 10 && x (u - 10) 12).toNat + (x (u - 11) 11 && x (u - 11) 13).toNat + (x (u - 12) 12 && x (u - 12) 14).toNat + (x (u - 13) 13).toNat)
    (hcov3 : ∀ u : ℤ, 1 ≤ (x u 3).toNat + (x (u - 1) 1 && x (u - 1) 4).toNat + (x (u - 2) 2 && x (u - 2) 5).toNat + (x (u - 3) 3 && x (u - 3) 6).toNat + (x (u - 4) 4 && x (u - 4) 7).toNat + (x (u - 5) 5 && x (u - 5) 8).toNat + (x (u - 6) 6 && x (u - 6) 9).toNat + (x (u - 7) 7 && x (u - 7) 10).toNat + (x (u - 8) 8 && x (u - 8) 11).toNat + (x (u - 9) 9 && x (u - 9) 12).toNat + (x (u - 10) 10 && x (u - 10) 13).toNat + (x (u - 11) 11 && x (u - 11) 14).toNat + (x (u - 12) 12).toNat)
    (hcov4 : ∀ u : ℤ, 1 ≤ (x u 4).toNat + (x (u - 1) 1 && x (u - 1) 5).toNat + (x (u - 2) 2 && x (u - 2) 6).toNat + (x (u - 3) 3 && x (u - 3) 7).toNat + (x (u - 4) 4 && x (u - 4) 8).toNat + (x (u - 5) 5 && x (u - 5) 9).toNat + (x (u - 6) 6 && x (u - 6) 10).toNat + (x (u - 7) 7 && x (u - 7) 11).toNat + (x (u - 8) 8 && x (u - 8) 12).toNat + (x (u - 9) 9 && x (u - 9) 13).toNat + (x (u - 10) 10 && x (u - 10) 14).toNat + (x (u - 11) 11).toNat)
    (hcov5 : ∀ u : ℤ, 1 ≤ (x u 5).toNat + (x (u - 1) 1 && x (u - 1) 6).toNat + (x (u - 2) 2 && x (u - 2) 7).toNat + (x (u - 3) 3 && x (u - 3) 8).toNat + (x (u - 4) 4 && x (u - 4) 9).toNat + (x (u - 5) 5 && x (u - 5) 10).toNat + (x (u - 6) 6 && x (u - 6) 11).toNat + (x (u - 7) 7 && x (u - 7) 12).toNat + (x (u - 8) 8 && x (u - 8) 13).toNat + (x (u - 9) 9 && x (u - 9) 14).toNat + (x (u - 10) 10).toNat)
    (hcov6 : ∀ u : ℤ, 1 ≤ (x u 6).toNat + (x (u - 1) 1 && x (u - 1) 7).toNat + (x (u - 2) 2 && x (u - 2) 8).toNat + (x (u - 3) 3 && x (u - 3) 9).toNat + (x (u - 4) 4 && x (u - 4) 10).toNat + (x (u - 5) 5 && x (u - 5) 11).toNat + (x (u - 6) 6 && x (u - 6) 12).toNat + (x (u - 7) 7 && x (u - 7) 13).toNat + (x (u - 8) 8 && x (u - 8) 14).toNat + (x (u - 9) 9).toNat)
    (hcov7 : ∀ u : ℤ, 1 ≤ (x u 7).toNat + (x (u - 1) 1 && x (u - 1) 8).toNat + (x (u - 2) 2 && x (u - 2) 9).toNat + (x (u - 3) 3 && x (u - 3) 10).toNat + (x (u - 4) 4 && x (u - 4) 11).toNat + (x (u - 5) 5 && x (u - 5) 12).toNat + (x (u - 6) 6 && x (u - 6) 13).toNat + (x (u - 7) 7 && x (u - 7) 14).toNat + (x (u - 8) 8).toNat)
    (hcov9 : ∀ u : ℤ, 1 ≤ (x u 9).toNat + (x (u - 1) 1 && x (u - 1) 10).toNat + (x (u - 2) 2 && x (u - 2) 11).toNat + (x (u - 3) 3 && x (u - 3) 12).toNat + (x (u - 4) 4 && x (u - 4) 13).toNat + (x (u - 5) 5 && x (u - 5) 14).toNat + (x (u - 6) 6).toNat)
    (hcov10 : ∀ u : ℤ, 1 ≤ (x u 10).toNat + (x (u - 1) 1 && x (u - 1) 11).toNat + (x (u - 2) 2 && x (u - 2) 12).toNat + (x (u - 3) 3 && x (u - 3) 13).toNat + (x (u - 4) 4 && x (u - 4) 14).toNat + (x (u - 5) 5).toNat)
    (hcov11 : ∀ u : ℤ, 1 ≤ (x u 11).toNat + (x (u - 1) 1 && x (u - 1) 12).toNat + (x (u - 2) 2 && x (u - 2) 13).toNat + (x (u - 3) 3 && x (u - 3) 14).toNat + (x (u - 4) 4).toNat)
    (hcov13 : ∀ u : ℤ, 1 ≤ (x u 13).toNat + (x (u - 1) 1 && x (u - 1) 14).toNat + (x (u - 2) 2).toNat)
    (hp2 : ∀ p, x p 2 = true → x p 14 = true)
    (hp4 : ∀ p, x p 4 = true → x p 12 = true)
    (hp5 : ∀ p, x p 5 = true → x p 13 = true)
    (hp6 : ∀ p, x p 6 = true → x p 14 = true)
    (hp9 : ∀ p, x p 9 = true → x p 1 = true)
    (hp10 : ∀ p, x p 10 = true → x p 2 = true)
    (hp11 : ∀ p, x p 11 = true → x p 3 = true)
    (hp13 : ∀ p, x p 13 = true → x p 1 = true)
    (g0 : (x (-2) 3).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-1) 2).toNat = 0)
    (g3 : (x (-1) 3).toNat = 0)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 10).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x (-1) 13).toNat = 0)
    (g9 : (x 0 1).toNat = 1)
    (g10 : (x 0 2).toNat = 1)
    (g11 : (x 0 3).toNat = 0)
    (g12 : (x 0 4).toNat = 0)
    (g13 : (x 0 5).toNat = 0)
    (g14 : (x 0 6).toNat = 0)
    (g15 : (x 0 7).toNat = 0)
    (g16 : (x 0 8).toNat = 0)
    (g17 : (x 0 9).toNat = 0)
    (g18 : (x 0 11).toNat = 0)
    (g19 : (x 0 12).toNat = 0)
    (g20 : (x 0 13).toNat = 1)
    (g21 : (x 0 14).toNat = 1)
    (g22 : (x 1 2).toNat = 0)
    (g23 : (x 1 4).toNat = 0)
    (g24 : (x 1 5).toNat = 0)
    (g25 : (x 1 6).toNat = 0)
    (g26 : (x 1 10).toNat = 0)
    (g27 : (x 1 12).toNat = 0)
    (g28 : (x 1 13).toNat = 0)
    (g29 : (x 2 4).toNat = 0)
    (g30 : (x 2 12).toNat = 0)
    (g31 : (x 0 2 && x 0 4).toNat = 0)
    (g32 : (x (-1) 3 && x (-1) 5).toNat = 0)
    (g33 : (x 1 10 && x 1 12).toNat = 0)
    (g34 : (x 0 11 && x 0 13).toNat = 0)
    (g35 : (x 0 1 && x 0 4).toNat = 0)
    (g36 : (x (-1) 2 && x (-1) 5).toNat = 0)
    (g37 : (x (-2) 3 && x (-2) 6).toNat = 0)
    (g38 : (x 2 9 && x 2 12).toNat = 0)
    (g39 : (x 1 10 && x 1 13).toNat = 0)
    (g40 : (x 0 11 && x 0 14).toNat = 0)
    (g41 : (x 0 2 && x 0 6).toNat = 0)
    (g42 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g43 : (x 1 8 && x 1 12).toNat = 0)
    (g44 : (x 0 1 && x 0 6).toNat = 0)
    (g45 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g46 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g47 : (x 1 1 && x 1 6).toNat = 0)
    (g48 : (x 0 2 && x 0 7).toNat = 0)
    (g49 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g50 : (x 1 7 && x 1 12).toNat = 0)
    (g51 : (x 0 8 && x 0 13).toNat = 0)
    (g52 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g53 : (x 2 7 && x 2 12).toNat = 0)
    (g54 : (x 1 8 && x 1 13).toNat = 0)
    (g55 : (x 0 1 && x 0 7).toNat = 0)
    (g56 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g57 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g58 : (x 0 2 && x 0 8).toNat = 0)
    (g59 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g60 : (x 1 6 && x 1 12).toNat = 0)
    (g61 : (x 0 7 && x 0 13).toNat = 0)
    (g62 : (x 2 6 && x 2 12).toNat = 0)
    (g63 : (x 1 7 && x 1 13).toNat = 0)
    (g64 : (x 0 8 && x 0 14).toNat = 0)
    (g65 : (x 2 5 && x 2 12).toNat = 0)
    (g66 : (x 1 6 && x 1 13).toNat = 0)
    (g67 : (x 0 7 && x 0 14).toNat = 0)
    (g68 : (x 1 1 && x 1 10).toNat = 0)
    (g69 : (x 0 2 && x 0 11).toNat = 0)
    (g70 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g71 : (x 1 2 && x 1 11).toNat = 0)
    (g72 : (x 0 3 && x 0 12).toNat = 0)
    (g73 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g74 : (x 0 1 && x 0 11).toNat = 0)
    (g75 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g76 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g77 : (x 0 2 && x 0 12).toNat = 0)
    (g78 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g79 : (x 1 2 && x 1 12).toNat = 0)
    (g80 : (x 0 3 && x 0 13).toNat = 0)
    (g81 : (x 2 2 && x 2 12).toNat = 0)
    (g82 : (x 1 3 && x 1 13).toNat = 0)
    (g83 : (x 0 4 && x 0 14).toNat = 0)
    (g84 : (x 0 1 && x 0 12).toNat = 0)
    (g85 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g86 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g87 : (x 2 1 && x 2 12).toNat = 0)
    (g88 : (x 1 2 && x 1 13).toNat = 0)
    (g89 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89
