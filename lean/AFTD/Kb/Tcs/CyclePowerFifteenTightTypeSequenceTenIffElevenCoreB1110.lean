import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b1110

Topic: combinatorics   Node: f3bf879945d2

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 88 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b1110_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-2) 7).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-1) 3).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 6).toNat = 0)
    (g9 : (x (-1) 7).toNat = 0)
    (g10 : (x (-1) 9).toNat = 0)
    (g11 : (x (-1) 10).toNat = 0)
    (g12 : (x (-1) 11).toNat = 0)
    (g13 : (x (-1) 13).toNat = 0)
    (g14 : (x 0 2).toNat = 1)
    (g15 : (x 0 4).toNat = 1)
    (g16 : (x 0 5).toNat = 1)
    (g17 : (x 0 6).toNat = 1)
    (g18 : (x 0 7).toNat = 0)
    (g19 : (x 0 10).toNat = 0)
    (g20 : (x 1 2).toNat = 0)
    (g21 : (x 1 4).toNat = 0)
    (g22 : (x 1 5).toNat = 0)
    (g23 : (x 1 6).toNat = 0)
    (g24 : (x 2 4).toNat = 0)
    (g25 : (x 2 5).toNat = 0)
    (g26 : (x 3 4).toNat = 0)
    (g27 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g28 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g29 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g30 : (x 1 4 && x 1 8).toNat = 0)
    (g31 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g32 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g33 : (x 2 4 && x 2 8).toNat = 0)
    (g34 : (x 1 5 && x 1 9).toNat = 0)
    (g35 : (x 0 6 && x 0 10).toNat = 0)
    (g36 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g37 : (x 3 4 && x 3 8).toNat = 0)
    (g38 : (x 2 5 && x 2 9).toNat = 0)
    (g39 : (x 1 6 && x 1 10).toNat = 0)
    (g40 : (x 6 4 && x 6 8).toNat = 0)
    (g41 : (x 5 5 && x 5 9).toNat = 0)
    (g42 : (x 4 6 && x 4 10).toNat = 0)
    (g43 : (x 3 7 && x 3 11).toNat = 0)
    (g44 : (x 2 8 && x 2 12).toNat = 0)
    (g45 : (x 1 9 && x 1 13).toNat = 0)
    (g46 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g47 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g48 : (x 6 3 && x 6 8).toNat = 0)
    (g49 : (x 5 4 && x 5 9).toNat = 0)
    (g50 : (x 4 5 && x 4 10).toNat = 0)
    (g51 : (x 3 6 && x 3 11).toNat = 0)
    (g52 : (x 2 7 && x 2 12).toNat = 0)
    (g53 : (x 1 8 && x 1 13).toNat = 0)
    (g54 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g55 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g56 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g57 : (x 6 2 && x 6 8).toNat = 0)
    (g58 : (x 5 3 && x 5 9).toNat = 0)
    (g59 : (x 4 4 && x 4 10).toNat = 0)
    (g60 : (x 3 5 && x 3 11).toNat = 0)
    (g61 : (x 2 6 && x 2 12).toNat = 0)
    (g62 : (x 1 7 && x 1 13).toNat = 0)
    (g63 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g64 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g65 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g66 : (x 6 1 && x 6 8).toNat = 0)
    (g67 : (x 5 2 && x 5 9).toNat = 0)
    (g68 : (x 4 3 && x 4 10).toNat = 0)
    (g69 : (x 3 4 && x 3 11).toNat = 0)
    (g70 : (x 2 5 && x 2 12).toNat = 0)
    (g71 : (x 1 6 && x 1 13).toNat = 0)
    (g72 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g73 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g74 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g75 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g76 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g77 : (x 0 1 && x 0 10).toNat = 0)
    (g78 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g79 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g80 : (x 3 4 && x 3 13).toNat = 0)
    (g81 : (x 2 5 && x 2 14).toNat = 0)
    (g82 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g83 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g84 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g85 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g86 : (x 2 4 && x 2 14).toNat = 0)
    (g87 : (x 3 4 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d22346 : (x 0 7 && x 0 14).toNat = 0 := by
    have r22347 := hand1 (x 0 7) (x 0 14)
    have b22348 := hb (x 0 7)
    have b22349 := hb (x 0 7 && x 0 14)
    clear * - r22347 b22348 b22349 g18
    omega
  have d22350 : (x 0 7 && x 0 11).toNat = 0 := by
    have r22351 := hand1 (x 0 7) (x 0 11)
    have b22352 := hb (x 0 7)
    have b22353 := hb (x 0 7 && x 0 11)
    clear * - r22351 b22352 b22353 g18
    omega
  cases h22354 : x 0 8
  · have f22355 : (x 0 8).toNat = 0 := by rw [h22354]; rfl
    have d22356 : (x 0 1 && x 0 8).toNat = 0 := by
      have r22357 := hand2 (x 0 1) (x 0 8)
      have b22358 := hb (x 0 8)
      have b22359 := hb (x 0 1 && x 0 8)
      clear * - r22357 b22358 b22359 f22355
      omega
    have d22360 : (x 0 8 && x 0 14).toNat = 0 := by
      have r22361 := hand1 (x 0 8) (x 0 14)
      have b22362 := hb (x 0 8)
      have b22363 := hb (x 0 8 && x 0 14)
      clear * - r22361 b22362 b22363 f22355
      omega
    have d22364 : (x 0 2 && x 0 8).toNat = 0 := by
      have r22365 := hand2 (x 0 2) (x 0 8)
      have b22366 := hb (x 0 8)
      have b22367 := hb (x 0 2 && x 0 8)
      clear * - r22365 b22366 b22367 f22355
      omega
    have d22368 : (x 0 4 && x 0 8).toNat = 0 := by
      have r22369 := hand2 (x 0 4) (x 0 8)
      have b22370 := hb (x 0 8)
      have b22371 := hb (x 0 4 && x 0 8)
      clear * - r22369 b22370 b22371 f22355
      omega
    cases h22372 : x 0 9
    · have f22373 : (x 0 9).toNat = 0 := by rw [h22372]; rfl
      have d22374 : (x 0 9 && x 0 14).toNat = 0 := by
        have r22375 := hand1 (x 0 9) (x 0 14)
        have b22376 := hb (x 0 9)
        have b22377 := hb (x 0 9 && x 0 14)
        clear * - r22375 b22376 b22377 f22373
        omega
      have d22378 : (x 0 5 && x 0 9).toNat = 0 := by
        have r22379 := hand2 (x 0 5) (x 0 9)
        have b22380 := hb (x 0 9)
        have b22381 := hb (x 0 5 && x 0 9)
        clear * - r22379 b22380 b22381 f22373
        omega
      cases h22382 : x 1 1
      · have f22383 : (x 1 1).toNat = 0 := by rw [h22382]; rfl
        cases h22384 : x 1 3
        · have f22385 : (x 1 3).toNat = 0 := by rw [h22384]; rfl
          cases h22386 : x 1 7
          · have f22387 : (x 1 7).toNat = 0 := by rw [h22386]; rfl
            cases h22388 : x (-1) 8
            · have f22389 : (x (-1) 8).toNat = 0 := by rw [h22388]; rfl
              have d22390 : (x 7 7).toNat = 1 := by
                have r22391 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22392 := hb (x (-1) 8)
                have b22393 := hb (x 7 7)
                have b22394 := hb (x 6 1 && x 6 8)
                have b22395 := hb (x 5 2 && x 5 9)
                have b22396 := hb (x 4 3 && x 4 10)
                have b22397 := hb (x 3 4 && x 3 11)
                have b22398 := hb (x 2 5 && x 2 12)
                have b22399 := hb (x 1 6 && x 1 13)
                have b22400 := hb (x 0 7 && x 0 14)
                clear * - r22391 b22392 b22393 b22394 b22395 b22396 b22397 b22398 b22399 b22400 g66 g67 g68 g69 g70 g71 d22346 f22389
                omega
              have d22401 : (x 14 8).toNat = 0 := by
                have r22402 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22403 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e22404 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e22405 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e22406 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e22407 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e22408 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b22409 := hb (x 7 7)
                have b22410 := hb (x 8 6)
                have b22411 := hb (x 9 5)
                have b22412 := hb (x 10 4)
                have b22413 := hb (x 11 11)
                have b22414 := hb (x 12 10)
                have b22415 := hb (x 13 9)
                have b22416 := hb (x 14 8)
                clear * - r22402 e22403 e22404 e22405 e22406 e22407 e22408 b22409 b22410 b22411 b22412 b22413 b22414 b22415 b22416 d22390
                omega
              have d22417 : (x 13 9).toNat = 0 := by
                have r22418 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22419 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e22420 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e22421 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e22422 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e22423 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e22424 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b22425 := hb (x 7 7)
                have b22426 := hb (x 8 6)
                have b22427 := hb (x 9 5)
                have b22428 := hb (x 10 4)
                have b22429 := hb (x 11 11)
                have b22430 := hb (x 12 10)
                have b22431 := hb (x 13 9)
                have b22432 := hb (x 14 8)
                clear * - r22418 e22419 e22420 e22421 e22422 e22423 e22424 b22425 b22426 b22427 b22428 b22429 b22430 b22431 b22432 d22401 d22390
                omega
              have d22433 : (x 12 10).toNat = 0 := by
                have r22434 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22435 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e22436 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e22437 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e22438 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e22439 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e22440 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b22441 := hb (x 7 7)
                have b22442 := hb (x 8 6)
                have b22443 := hb (x 9 5)
                have b22444 := hb (x 10 4)
                have b22445 := hb (x 11 11)
                have b22446 := hb (x 12 10)
                have b22447 := hb (x 13 9)
                have b22448 := hb (x 14 8)
                clear * - r22434 e22435 e22436 e22437 e22438 e22439 e22440 b22441 b22442 b22443 b22444 b22445 b22446 b22447 b22448 d22401 d22417 d22390
                omega
              have d22449 : (x 12 1 && x 12 10).toNat = 0 := by
                have r22450 := hand2 (x 12 1) (x 12 10)
                have b22451 := hb (x 12 10)
                have b22452 := hb (x 12 1 && x 12 10)
                clear * - r22450 b22451 b22452 d22433
                omega
              have d22453 : (x 11 11).toNat = 0 := by
                have r22454 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22455 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e22456 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e22457 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e22458 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e22459 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e22460 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b22461 := hb (x 7 7)
                have b22462 := hb (x 8 6)
                have b22463 := hb (x 9 5)
                have b22464 := hb (x 10 4)
                have b22465 := hb (x 11 11)
                have b22466 := hb (x 12 10)
                have b22467 := hb (x 13 9)
                have b22468 := hb (x 14 8)
                clear * - r22454 e22455 e22456 e22457 e22458 e22459 e22460 b22461 b22462 b22463 b22464 b22465 b22466 b22467 b22468 d22401 d22417 d22433 d22390
                omega
              have d22469 : (x 11 2 && x 11 11).toNat = 0 := by
                have r22470 := hand2 (x 11 2) (x 11 11)
                have b22471 := hb (x 11 11)
                have b22472 := hb (x 11 2 && x 11 11)
                clear * - r22470 b22471 b22472 d22453
                omega
              have d22473 : (x 10 4).toNat = 0 := by
                have r22474 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22475 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e22476 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e22477 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e22478 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e22479 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e22480 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b22481 := hb (x 7 7)
                have b22482 := hb (x 8 6)
                have b22483 := hb (x 9 5)
                have b22484 := hb (x 10 4)
                have b22485 := hb (x 11 11)
                have b22486 := hb (x 12 10)
                have b22487 := hb (x 13 9)
                have b22488 := hb (x 14 8)
                clear * - r22474 e22475 e22476 e22477 e22478 e22479 e22480 b22481 b22482 b22483 b22484 b22485 b22486 b22487 b22488 d22401 d22417 d22433 d22453 d22390
                omega
              have d22489 : (x 9 5).toNat = 0 := by
                have r22490 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22491 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e22492 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e22493 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e22494 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e22495 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e22496 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b22497 := hb (x 7 7)
                have b22498 := hb (x 8 6)
                have b22499 := hb (x 9 5)
                have b22500 := hb (x 10 4)
                have b22501 := hb (x 11 11)
                have b22502 := hb (x 12 10)
                have b22503 := hb (x 13 9)
                have b22504 := hb (x 14 8)
                clear * - r22490 e22491 e22492 e22493 e22494 e22495 e22496 b22497 b22498 b22499 b22500 b22501 b22502 b22503 b22504 d22401 d22417 d22433 d22453 d22473 d22390
                omega
              have d22505 : (x 8 6).toNat = 0 := by
                have r22506 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22507 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e22508 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e22509 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e22510 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e22511 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e22512 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b22513 := hb (x 7 7)
                have b22514 := hb (x 8 6)
                have b22515 := hb (x 9 5)
                have b22516 := hb (x 10 4)
                have b22517 := hb (x 11 11)
                have b22518 := hb (x 12 10)
                have b22519 := hb (x 13 9)
                have b22520 := hb (x 14 8)
                clear * - r22506 e22507 e22508 e22509 e22510 e22511 e22512 b22513 b22514 b22515 b22516 b22517 b22518 b22519 b22520 d22401 d22417 d22433 d22453 d22473 d22489 d22390
                omega
              have d22521 : (x 8 1 && x 8 6).toNat = 0 := by
                have r22522 := hand2 (x 8 1) (x 8 6)
                have b22523 := hb (x 8 6)
                have b22524 := hb (x 8 1 && x 8 6)
                clear * - r22522 b22523 b22524 d22505
                omega
              have d22525 : (x 8 2 && x 8 6).toNat = 0 := by
                have r22526 := hand2 (x 8 2) (x 8 6)
                have b22527 := hb (x 8 6)
                have b22528 := hb (x 8 2 && x 8 6)
                clear * - r22526 b22527 b22528 d22505
                omega
              have d22529 : (x 7 1 && x 7 7).toNat = 1 := by
                have r22530 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22531 := hb (x (-1) 9)
                have b22532 := hb (x 8 6)
                have b22533 := hb (x 7 1 && x 7 7)
                have b22534 := hb (x 6 2 && x 6 8)
                have b22535 := hb (x 5 3 && x 5 9)
                have b22536 := hb (x 4 4 && x 4 10)
                have b22537 := hb (x 3 5 && x 3 11)
                have b22538 := hb (x 2 6 && x 2 12)
                have b22539 := hb (x 1 7 && x 1 13)
                have b22540 := hb (x 0 8 && x 0 14)
                clear * - r22530 b22531 b22532 b22533 b22534 b22535 b22536 b22537 b22538 b22539 b22540 d22505 g57 g58 g59 g60 g61 g62 d22360 g10
                omega
              have d22541 : (x 7 1).toNat = 1 := by
                have r22542 := hand1 (x 7 1) (x 7 7)
                have b22543 := hb (x 7 1)
                have b22544 := hb (x 7 1 && x 7 7)
                clear * - r22542 b22543 b22544 d22529
                omega
              have d22545 : (x 8 14).toNat = 0 := by
                have r22546 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22547 := hb (x 7 1)
                have b22548 := hb (x 8 14)
                clear * - r22546 b22547 b22548 d22541
                omega
              have d22549 : (x 8 5 && x 8 14).toNat = 0 := by
                have r22550 := hand2 (x 8 5) (x 8 14)
                have b22551 := hb (x 8 14)
                have b22552 := hb (x 8 5 && x 8 14)
                clear * - r22550 b22551 b22552 d22545
                omega
              have d22553 : (x 8 2).toNat = 0 := by
                have r22554 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                have b22555 := hb (x 8 2)
                have b22556 := hb (x 8 14)
                clear * - r22554 b22555 b22556 d22545
                omega
              have d22557 : (x 8 10).toNat = 0 := by
                have r22558 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                have b22559 := hb (x 8 2)
                have b22560 := hb (x 8 10)
                clear * - r22558 b22559 b22560 d22553
                omega
              have d22561 : (x 7 2 && x 7 7).toNat = 1 := by
                have r22562 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22563 := hb (x (-1) 10)
                have b22564 := hb (x 9 5)
                have b22565 := hb (x 8 1 && x 8 6)
                have b22566 := hb (x 7 2 && x 7 7)
                have b22567 := hb (x 6 3 && x 6 8)
                have b22568 := hb (x 5 4 && x 5 9)
                have b22569 := hb (x 4 5 && x 4 10)
                have b22570 := hb (x 3 6 && x 3 11)
                have b22571 := hb (x 2 7 && x 2 12)
                have b22572 := hb (x 1 8 && x 1 13)
                have b22573 := hb (x 0 9 && x 0 14)
                clear * - r22562 b22563 b22564 b22565 b22566 b22567 b22568 b22569 b22570 b22571 b22572 b22573 d22489 d22521 g48 g49 g50 g51 g52 g53 d22374 g11
                omega
              have d22574 : (x 7 2).toNat = 1 := by
                have r22575 := hand1 (x 7 2) (x 7 7)
                have b22576 := hb (x 7 2)
                have b22577 := hb (x 7 2 && x 7 7)
                clear * - r22575 b22576 b22577 d22561
                omega
              have d22578 : (x 7 14).toNat = 1 := by
                have r22579 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b22580 := hb (x 7 2)
                have b22581 := hb (x 7 14)
                clear * - r22579 b22580 b22581 d22574
                omega
              have d22582 : (x 6 1).toNat = 0 := by
                have r22583 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22584 := hb (x 6 1)
                have b22585 := hb (x 7 14)
                clear * - r22583 b22584 b22585 d22578
                omega
              have d22586 : (x 6 1 && x 6 14).toNat = 0 := by
                have r22587 := hand1 (x 6 1) (x 6 14)
                have b22588 := hb (x 6 1)
                have b22589 := hb (x 6 1 && x 6 14)
                clear * - r22587 b22588 b22589 d22582
                omega
              have d22590 : (x 6 1 && x 6 12).toNat = 0 := by
                have r22591 := hand1 (x 6 1) (x 6 12)
                have b22592 := hb (x 6 1)
                have b22593 := hb (x 6 1 && x 6 12)
                clear * - r22591 b22592 b22593 d22582
                omega
              have d22594 : (x 6 1 && x 6 11).toNat = 0 := by
                have r22595 := hand1 (x 6 1) (x 6 11)
                have b22596 := hb (x 6 1)
                have b22597 := hb (x 6 1 && x 6 11)
                clear * - r22595 b22596 b22597 d22582
                omega
              have d22598 : (x 6 13).toNat = 0 := by
                have r22599 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                have b22600 := hb (x 6 1)
                have b22601 := hb (x 6 13)
                clear * - r22599 b22600 b22601 d22582
                omega
              have d22602 : (x 6 5).toNat = 0 := by
                have r22603 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                have b22604 := hb (x 6 5)
                have b22605 := hb (x 6 13)
                clear * - r22603 b22604 b22605 d22598
                omega
              have d22606 : (x 9 12).toNat = 0 := by
                have r22607 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22608 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e22609 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b22610 := hb (x 6 3)
                have b22611 := hb (x 7 2)
                have b22612 := hb (x 8 13)
                have b22613 := hb (x 9 12)
                clear * - r22607 e22608 e22609 b22610 b22611 b22612 b22613 d22574
                omega
              have d22614 : (x 9 2 && x 9 12).toNat = 0 := by
                have r22615 := hand2 (x 9 2) (x 9 12)
                have b22616 := hb (x 9 12)
                have b22617 := hb (x 9 2 && x 9 12)
                clear * - r22615 b22616 b22617 d22606
                omega
              have d22618 : (x 9 4).toNat = 0 := by
                have r22619 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have b22620 := hb (x 9 4)
                have b22621 := hb (x 9 12)
                clear * - r22619 b22620 b22621 d22606
                omega
              have d22622 : (x 9 4 && x 9 13).toNat = 0 := by
                have r22623 := hand1 (x 9 4) (x 9 13)
                have b22624 := hb (x 9 4)
                have b22625 := hb (x 9 4 && x 9 13)
                clear * - r22623 b22624 b22625 d22618
                omega
              have d22626 : (x 8 13).toNat = 0 := by
                have r22627 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22628 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e22629 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b22630 := hb (x 6 3)
                have b22631 := hb (x 7 2)
                have b22632 := hb (x 8 13)
                have b22633 := hb (x 9 12)
                clear * - r22627 e22628 e22629 b22630 b22631 b22632 b22633 d22606 d22574
                omega
              have d22634 : (x 8 3 && x 8 13).toNat = 0 := by
                have r22635 := hand2 (x 8 3) (x 8 13)
                have b22636 := hb (x 8 13)
                have b22637 := hb (x 8 3 && x 8 13)
                clear * - r22635 b22636 b22637 d22626
                omega
              have d22638 : (x 8 5).toNat = 0 := by
                have r22639 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                have b22640 := hb (x 8 5)
                have b22641 := hb (x 8 13)
                clear * - r22639 b22640 b22641 d22626
                omega
              have d22642 : (x 6 3).toNat = 0 := by
                have r22643 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22644 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e22645 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b22646 := hb (x 6 3)
                have b22647 := hb (x 7 2)
                have b22648 := hb (x 8 13)
                have b22649 := hb (x 9 12)
                clear * - r22643 e22644 e22645 b22646 b22647 b22648 b22649 d22606 d22626 d22574
                omega
              have d22650 : (x 6 11).toNat = 0 := by
                have r22651 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                have b22652 := hb (x 6 3)
                have b22653 := hb (x 6 11)
                clear * - r22651 b22652 b22653 d22642
                omega
              have d22654 : (x 7 3 && x 7 7).toNat = 1 := by
                have r22655 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22656 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
                have e22657 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
                have b22658 := hb (x (-1) 11)
                have b22659 := hb (x 0 10)
                have b22660 := hb (x 9 5)
                have b22661 := hb (x 10 4)
                have b22662 := hb (x 8 2 && x 8 6)
                have b22663 := hb (x 7 3 && x 7 7)
                have b22664 := hb (x 6 4 && x 6 8)
                have b22665 := hb (x 5 5 && x 5 9)
                have b22666 := hb (x 4 6 && x 4 10)
                have b22667 := hb (x 3 7 && x 3 11)
                have b22668 := hb (x 2 8 && x 2 12)
                have b22669 := hb (x 1 9 && x 1 13)
                clear * - r22655 e22656 e22657 b22658 b22659 b22660 b22661 b22662 b22663 b22664 b22665 b22666 b22667 b22668 b22669 d22473 d22489 d22525 g40 g41 g42 g43 g44 g45 g19 g12
                omega
              have d22670 : (x 7 3).toNat = 1 := by
                have r22671 := hand1 (x 7 3) (x 7 7)
                have b22672 := hb (x 7 3)
                have b22673 := hb (x 7 3 && x 7 7)
                clear * - r22671 b22672 b22673 d22654
                omega
              have d22674 : (x 10 12).toNat = 0 := by
                have r22675 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22676 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e22677 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b22678 := hb (x 7 3)
                have b22679 := hb (x 8 2)
                have b22680 := hb (x 9 13)
                have b22681 := hb (x 10 12)
                clear * - r22675 e22676 e22677 b22678 b22679 b22680 b22681 d22553 d22670
                omega
              have d22682 : (x 10 3 && x 10 12).toNat = 0 := by
                have r22683 := hand2 (x 10 3) (x 10 12)
                have b22684 := hb (x 10 12)
                have b22685 := hb (x 10 3 && x 10 12)
                clear * - r22683 b22684 b22685 d22674
                omega
              have d22686 : (x 7 6).toNat = 1 := by
                have r22687 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22688 := hb (x 7 6)
                have b22689 := hb (x 13 9)
                have b22690 := hb (x 12 1 && x 12 10)
                have b22691 := hb (x 11 2 && x 11 11)
                have b22692 := hb (x 10 3 && x 10 12)
                have b22693 := hb (x 9 4 && x 9 13)
                have b22694 := hb (x 8 5 && x 8 14)
                clear * - r22687 b22688 b22689 b22690 b22691 b22692 b22693 b22694 d22417 d22449 d22469 d22682 d22622 d22549
                omega
              have d22695 : (x 13 8).toNat = 0 := by
                have r22696 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22697 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e22698 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e22699 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e22700 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e22701 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e22702 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b22703 := hb (x 6 7)
                have b22704 := hb (x 7 6)
                have b22705 := hb (x 8 5)
                have b22706 := hb (x 9 4)
                have b22707 := hb (x 10 11)
                have b22708 := hb (x 11 10)
                have b22709 := hb (x 12 9)
                have b22710 := hb (x 13 8)
                clear * - r22696 e22697 e22698 e22699 e22700 e22701 e22702 b22703 b22704 b22705 b22706 b22707 b22708 b22709 b22710 d22618 d22638 d22686
                omega
              have d22711 : (x 12 9).toNat = 0 := by
                have r22712 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22713 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e22714 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e22715 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e22716 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e22717 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e22718 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b22719 := hb (x 6 7)
                have b22720 := hb (x 7 6)
                have b22721 := hb (x 8 5)
                have b22722 := hb (x 9 4)
                have b22723 := hb (x 10 11)
                have b22724 := hb (x 11 10)
                have b22725 := hb (x 12 9)
                have b22726 := hb (x 13 8)
                clear * - r22712 e22713 e22714 e22715 e22716 e22717 e22718 b22719 b22720 b22721 b22722 b22723 b22724 b22725 b22726 d22695 d22618 d22638 d22686
                omega
              have d22727 : (x 11 10).toNat = 0 := by
                have r22728 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22729 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e22730 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e22731 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e22732 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e22733 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e22734 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b22735 := hb (x 6 7)
                have b22736 := hb (x 7 6)
                have b22737 := hb (x 8 5)
                have b22738 := hb (x 9 4)
                have b22739 := hb (x 10 11)
                have b22740 := hb (x 11 10)
                have b22741 := hb (x 12 9)
                have b22742 := hb (x 13 8)
                clear * - r22728 e22729 e22730 e22731 e22732 e22733 e22734 b22735 b22736 b22737 b22738 b22739 b22740 b22741 b22742 d22695 d22711 d22618 d22638 d22686
                omega
              have d22743 : (x 10 11).toNat = 0 := by
                have r22744 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22745 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e22746 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e22747 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e22748 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e22749 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e22750 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b22751 := hb (x 6 7)
                have b22752 := hb (x 7 6)
                have b22753 := hb (x 8 5)
                have b22754 := hb (x 9 4)
                have b22755 := hb (x 10 11)
                have b22756 := hb (x 11 10)
                have b22757 := hb (x 12 9)
                have b22758 := hb (x 13 8)
                clear * - r22744 e22745 e22746 e22747 e22748 e22749 e22750 b22751 b22752 b22753 b22754 b22755 b22756 b22757 b22758 d22695 d22711 d22727 d22618 d22638 d22686
                omega
              have d22759 : (x 10 1 && x 10 11).toNat = 0 := by
                have r22760 := hand2 (x 10 1) (x 10 11)
                have b22761 := hb (x 10 11)
                have b22762 := hb (x 10 1 && x 10 11)
                clear * - r22760 b22761 b22762 d22743
                omega
              have d22763 : (x 7 4 && x 7 14).toNat = 1 := by
                have r22764 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22765 := hb (x 6 5)
                have b22766 := hb (x 11 10)
                have b22767 := hb (x 10 1 && x 10 11)
                have b22768 := hb (x 9 2 && x 9 12)
                have b22769 := hb (x 8 3 && x 8 13)
                have b22770 := hb (x 7 4 && x 7 14)
                clear * - r22764 b22765 b22766 b22767 b22768 b22769 b22770 d22727 d22759 d22614 d22634 d22602
                omega
              have d22771 : (x 7 4).toNat = 1 := by
                have r22772 := hand1 (x 7 4) (x 7 14)
                have b22773 := hb (x 7 4)
                have b22774 := hb (x 7 4 && x 7 14)
                clear * - r22772 b22773 b22774 d22763
                omega
              have d22775 : (x 7 12).toNat = 1 := by
                have r22776 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have b22777 := hb (x 7 4)
                have b22778 := hb (x 7 12)
                clear * - r22776 b22777 b22778 d22771
                omega
              have d22779 : (x 5 2).toNat = 0 := by
                have r22780 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22781 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e22782 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b22783 := hb (x 4 3)
                have b22784 := hb (x 5 2)
                have b22785 := hb (x 6 13)
                have b22786 := hb (x 7 12)
                clear * - r22780 e22781 e22782 b22783 b22784 b22785 b22786 d22775 d22598
                omega
              have d22787 : (x 5 2 && x 5 13).toNat = 0 := by
                have r22788 := hand1 (x 5 2) (x 5 13)
                have b22789 := hb (x 5 2)
                have b22790 := hb (x 5 2 && x 5 13)
                clear * - r22788 b22789 b22790 d22779
                omega
              have d22791 : (x 5 2 && x 5 12).toNat = 0 := by
                have r22792 := hand1 (x 5 2) (x 5 12)
                have b22793 := hb (x 5 2)
                have b22794 := hb (x 5 2 && x 5 12)
                clear * - r22792 b22793 b22794 d22779
                omega
              have d22795 : (x 7 13).toNat = 1 := by
                have r22796 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22797 := hb (x 5 2)
                have b22798 := hb (x 7 13)
                have b22799 := hb (x 6 1 && x 6 14)
                clear * - r22796 b22797 b22798 b22799 d22586 d22779
                omega
              have d22800 : (x 8 12).toNat = 0 := by
                have r22801 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22802 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e22803 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b22804 := hb (x 5 3)
                have b22805 := hb (x 6 2)
                have b22806 := hb (x 7 13)
                have b22807 := hb (x 8 12)
                clear * - r22801 e22802 e22803 b22804 b22805 b22806 b22807 d22795
                omega
              have d22808 : (x 6 2).toNat = 0 := by
                have r22809 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22810 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e22811 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b22812 := hb (x 5 3)
                have b22813 := hb (x 6 2)
                have b22814 := hb (x 7 13)
                have b22815 := hb (x 8 12)
                clear * - r22809 e22810 e22811 b22812 b22813 b22814 b22815 d22800 d22795
                omega
              have d22816 : (x 6 10).toNat = 0 := by
                have r22817 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
                have b22818 := hb (x 6 2)
                have b22819 := hb (x 6 10)
                clear * - r22817 b22818 b22819 d22808
                omega
              have d22820 : (x 5 3).toNat = 0 := by
                have r22821 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22822 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e22823 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b22824 := hb (x 5 3)
                have b22825 := hb (x 6 2)
                have b22826 := hb (x 7 13)
                have b22827 := hb (x 8 12)
                clear * - r22821 e22822 e22823 b22824 b22825 b22826 b22827 d22800 d22795 d22808
                omega
              have d22828 : (x 5 11).toNat = 0 := by
                have r22829 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                have b22830 := hb (x 5 3)
                have b22831 := hb (x 5 11)
                clear * - r22829 b22830 b22831 d22820
                omega
              have d22832 : (x 5 1 && x 5 11).toNat = 0 := by
                have r22833 := hand2 (x 5 1) (x 5 11)
                have b22834 := hb (x 5 11)
                have b22835 := hb (x 5 1 && x 5 11)
                clear * - r22833 b22834 b22835 d22828
                omega
              have d22836 : (x 4 3).toNat = 0 := by
                have r22837 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22838 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e22839 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b22840 := hb (x 4 3)
                have b22841 := hb (x 5 2)
                have b22842 := hb (x 6 13)
                have b22843 := hb (x 7 12)
                clear * - r22837 e22838 e22839 b22840 b22841 b22842 b22843 d22775 d22598 d22779
                omega
              have d22844 : (x 4 3 && x 4 14).toNat = 0 := by
                have r22845 := hand1 (x 4 3) (x 4 14)
                have b22846 := hb (x 4 3)
                have b22847 := hb (x 4 3 && x 4 14)
                clear * - r22845 b22846 b22847 d22836
                omega
              have d22848 : (x 7 11).toNat = 1 := by
                have r22849 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22850 := hb (x 3 4)
                have b22851 := hb (x 7 11)
                have b22852 := hb (x 6 1 && x 6 12)
                have b22853 := hb (x 5 2 && x 5 13)
                have b22854 := hb (x 4 3 && x 4 14)
                clear * - r22849 b22850 b22851 b22852 b22853 b22854 d22590 d22787 d22844 g26
                omega
              have d22855 : (x 10 8).toNat = 0 := by
                have r22856 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22857 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e22858 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e22859 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e22860 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e22861 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e22862 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b22863 := hb (x 3 7)
                have b22864 := hb (x 4 6)
                have b22865 := hb (x 5 5)
                have b22866 := hb (x 6 4)
                have b22867 := hb (x 7 11)
                have b22868 := hb (x 8 10)
                have b22869 := hb (x 9 9)
                have b22870 := hb (x 10 8)
                clear * - r22856 e22857 e22858 e22859 e22860 e22861 e22862 b22863 b22864 b22865 b22866 b22867 b22868 b22869 b22870 d22557 d22848
                omega
              have d22871 : (x 9 9).toNat = 0 := by
                have r22872 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22873 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e22874 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e22875 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e22876 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e22877 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e22878 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b22879 := hb (x 3 7)
                have b22880 := hb (x 4 6)
                have b22881 := hb (x 5 5)
                have b22882 := hb (x 6 4)
                have b22883 := hb (x 7 11)
                have b22884 := hb (x 8 10)
                have b22885 := hb (x 9 9)
                have b22886 := hb (x 10 8)
                clear * - r22872 e22873 e22874 e22875 e22876 e22877 e22878 b22879 b22880 b22881 b22882 b22883 b22884 b22885 b22886 d22855 d22557 d22848
                omega
              have d22887 : (x 6 4).toNat = 0 := by
                have r22888 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22889 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e22890 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e22891 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e22892 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e22893 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e22894 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b22895 := hb (x 3 7)
                have b22896 := hb (x 4 6)
                have b22897 := hb (x 5 5)
                have b22898 := hb (x 6 4)
                have b22899 := hb (x 7 11)
                have b22900 := hb (x 8 10)
                have b22901 := hb (x 9 9)
                have b22902 := hb (x 10 8)
                clear * - r22888 e22889 e22890 e22891 e22892 e22893 e22894 b22895 b22896 b22897 b22898 b22899 b22900 b22901 b22902 d22855 d22871 d22557 d22848
                omega
              have d22903 : (x 5 5).toNat = 0 := by
                have r22904 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22905 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e22906 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e22907 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e22908 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e22909 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e22910 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b22911 := hb (x 3 7)
                have b22912 := hb (x 4 6)
                have b22913 := hb (x 5 5)
                have b22914 := hb (x 6 4)
                have b22915 := hb (x 7 11)
                have b22916 := hb (x 8 10)
                have b22917 := hb (x 9 9)
                have b22918 := hb (x 10 8)
                clear * - r22904 e22905 e22906 e22907 e22908 e22909 e22910 b22911 b22912 b22913 b22914 b22915 b22916 b22917 b22918 d22855 d22871 d22557 d22848 d22887
                omega
              have d22919 : (x 4 6).toNat = 0 := by
                have r22920 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22921 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e22922 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e22923 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e22924 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e22925 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e22926 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b22927 := hb (x 3 7)
                have b22928 := hb (x 4 6)
                have b22929 := hb (x 5 5)
                have b22930 := hb (x 6 4)
                have b22931 := hb (x 7 11)
                have b22932 := hb (x 8 10)
                have b22933 := hb (x 9 9)
                have b22934 := hb (x 10 8)
                clear * - r22920 e22921 e22922 e22923 e22924 e22925 e22926 b22927 b22928 b22929 b22930 b22931 b22932 b22933 b22934 d22855 d22871 d22557 d22848 d22887 d22903
                omega
              have d22935 : (x 4 2 && x 4 6).toNat = 0 := by
                have r22936 := hand2 (x 4 2) (x 4 6)
                have b22937 := hb (x 4 6)
                have b22938 := hb (x 4 2 && x 4 6)
                clear * - r22936 b22937 b22938 d22919
                omega
              have d22939 : (x 3 7).toNat = 0 := by
                have r22940 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22941 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e22942 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e22943 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e22944 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e22945 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e22946 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b22947 := hb (x 3 7)
                have b22948 := hb (x 4 6)
                have b22949 := hb (x 5 5)
                have b22950 := hb (x 6 4)
                have b22951 := hb (x 7 11)
                have b22952 := hb (x 8 10)
                have b22953 := hb (x 9 9)
                have b22954 := hb (x 10 8)
                clear * - r22940 e22941 e22942 e22943 e22944 e22945 e22946 b22947 b22948 b22949 b22950 b22951 b22952 b22953 b22954 d22855 d22871 d22557 d22848 d22887 d22903 d22919
                omega
              have d22955 : (x 3 3 && x 3 7).toNat = 0 := by
                have r22956 := hand2 (x 3 3) (x 3 7)
                have b22957 := hb (x 3 7)
                have b22958 := hb (x 3 3 && x 3 7)
                clear * - r22956 b22957 b22958 d22939
                omega
              have d22959 : (x 4 3 && x 4 13).toNat = 0 := by
                have r22960 := hand1 (x 4 3) (x 4 13)
                have b22961 := hb (x 4 3)
                have b22962 := hb (x 4 3 && x 4 13)
                clear * - r22960 b22961 b22962 d22836
                omega
              have d22963 : (x 7 10).toNat = 1 := by
                have r22964 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22965 := hb (x 2 5)
                have b22966 := hb (x 7 10)
                have b22967 := hb (x 6 1 && x 6 11)
                have b22968 := hb (x 5 2 && x 5 12)
                have b22969 := hb (x 4 3 && x 4 13)
                have b22970 := hb (x 3 4 && x 3 14)
                clear * - r22964 b22965 b22966 b22967 b22968 b22969 b22970 d22594 d22791 d22959 g87 g25
                omega
              have d22971 : (x 9 8).toNat = 0 := by
                have r22972 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22973 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e22974 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e22975 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e22976 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e22977 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e22978 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b22979 := hb (x 2 7)
                have b22980 := hb (x 3 6)
                have b22981 := hb (x 4 5)
                have b22982 := hb (x 5 4)
                have b22983 := hb (x 6 11)
                have b22984 := hb (x 7 10)
                have b22985 := hb (x 8 9)
                have b22986 := hb (x 9 8)
                clear * - r22972 e22973 e22974 e22975 e22976 e22977 e22978 b22979 b22980 b22981 b22982 b22983 b22984 b22985 b22986 d22963 d22650
                omega
              have d22987 : (x 8 9).toNat = 0 := by
                have r22988 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22989 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e22990 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e22991 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e22992 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e22993 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e22994 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b22995 := hb (x 2 7)
                have b22996 := hb (x 3 6)
                have b22997 := hb (x 4 5)
                have b22998 := hb (x 5 4)
                have b22999 := hb (x 6 11)
                have b23000 := hb (x 7 10)
                have b23001 := hb (x 8 9)
                have b23002 := hb (x 9 8)
                clear * - r22988 e22989 e22990 e22991 e22992 e22993 e22994 b22995 b22996 b22997 b22998 b22999 b23000 b23001 b23002 d22971 d22963 d22650
                omega
              have d23003 : (x 5 4).toNat = 0 := by
                have r23004 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23005 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23006 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23007 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23008 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23009 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23010 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b23011 := hb (x 2 7)
                have b23012 := hb (x 3 6)
                have b23013 := hb (x 4 5)
                have b23014 := hb (x 5 4)
                have b23015 := hb (x 6 11)
                have b23016 := hb (x 7 10)
                have b23017 := hb (x 8 9)
                have b23018 := hb (x 9 8)
                clear * - r23004 e23005 e23006 e23007 e23008 e23009 e23010 b23011 b23012 b23013 b23014 b23015 b23016 b23017 b23018 d22971 d22987 d22963 d22650
                omega
              have d23019 : (x 4 5).toNat = 0 := by
                have r23020 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23021 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23022 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23023 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23024 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23025 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23026 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b23027 := hb (x 2 7)
                have b23028 := hb (x 3 6)
                have b23029 := hb (x 4 5)
                have b23030 := hb (x 5 4)
                have b23031 := hb (x 6 11)
                have b23032 := hb (x 7 10)
                have b23033 := hb (x 8 9)
                have b23034 := hb (x 9 8)
                clear * - r23020 e23021 e23022 e23023 e23024 e23025 e23026 b23027 b23028 b23029 b23030 b23031 b23032 b23033 b23034 d22971 d22987 d22963 d22650 d23003
                omega
              have d23035 : (x 3 6).toNat = 0 := by
                have r23036 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23037 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23038 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23039 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23040 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23041 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23042 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b23043 := hb (x 2 7)
                have b23044 := hb (x 3 6)
                have b23045 := hb (x 4 5)
                have b23046 := hb (x 5 4)
                have b23047 := hb (x 6 11)
                have b23048 := hb (x 7 10)
                have b23049 := hb (x 8 9)
                have b23050 := hb (x 9 8)
                clear * - r23036 e23037 e23038 e23039 e23040 e23041 e23042 b23043 b23044 b23045 b23046 b23047 b23048 b23049 b23050 d22971 d22987 d22963 d22650 d23003 d23019
                omega
              have d23051 : (x 3 2 && x 3 6).toNat = 0 := by
                have r23052 := hand2 (x 3 2) (x 3 6)
                have b23053 := hb (x 3 6)
                have b23054 := hb (x 3 2 && x 3 6)
                clear * - r23052 b23053 b23054 d23035
                omega
              have d23055 : (x 2 7).toNat = 0 := by
                have r23056 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23057 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23058 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23059 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23060 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23061 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23062 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b23063 := hb (x 2 7)
                have b23064 := hb (x 3 6)
                have b23065 := hb (x 4 5)
                have b23066 := hb (x 5 4)
                have b23067 := hb (x 6 11)
                have b23068 := hb (x 7 10)
                have b23069 := hb (x 8 9)
                have b23070 := hb (x 9 8)
                clear * - r23056 e23057 e23058 e23059 e23060 e23061 e23062 b23063 b23064 b23065 b23066 b23067 b23068 b23069 b23070 d22971 d22987 d22963 d22650 d23003 d23019 d23035
                omega
              have d23071 : (x 2 3 && x 2 7).toNat = 0 := by
                have r23072 := hand2 (x 2 3) (x 2 7)
                have b23073 := hb (x 2 7)
                have b23074 := hb (x 2 3 && x 2 7)
                clear * - r23072 b23073 b23074 d23055
                omega
              have r23075 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r23076 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r23077 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23078 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
              have e23079 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
              have r23080 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23081 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
              have e23082 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
              have r23083 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r23084 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r23085 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r23086 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
              have r23087 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
              have r23088 := hand1 (x (-3) 8) (x (-3) 12)
              have r23089 := hand1 (x (-4) 9) (x (-4) 13)
              have r23090 := hand1 (x (-2) 8) (x (-2) 12)
              have r23091 := hand1 (x (-3) 9) (x (-3) 13)
              have r23092 := hand1 (x 4 2) (x 4 12)
              have r23093 := hand1 (x 3 3) (x 3 13)
              have r23094 := hand2 (x (-8) 1) (x (-8) 14)
              have r23095 := hand1 (x 4 1) (x 4 14)
              linarith only [r23075, r23076, r23077, e23078, e23079, r23080, e23081, e23082, r23083, r23084, r23085, r23086, r23087, r23088, r23089, r23090, r23091, r23092, r23093, r23094, r23095, g3, g8, g9, g16, g17, g21, g22, g24, d23019, d23003, d22903, d22887, d22816, d23051, d23071, g30, d22378, g31, g32, d22935, d22955, g33, g34, g35, g36, d22832, g86]
            · have f23153 : (x (-1) 8).toNat = 1 := by rw [h22388]; rfl
              have d23154 : (x (-2) 9).toNat = 0 := by
                have r23155 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23156 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e23157 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e23158 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e23159 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e23160 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e23161 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b23162 := hb (x (-8) 7)
                have b23163 := hb (x (-7) 6)
                have b23164 := hb (x (-6) 5)
                have b23165 := hb (x (-5) 4)
                have b23166 := hb (x (-4) 11)
                have b23167 := hb (x (-3) 10)
                have b23168 := hb (x (-2) 9)
                have b23169 := hb (x (-1) 8)
                clear * - r23155 e23156 e23157 e23158 e23159 e23160 e23161 b23162 b23163 b23164 b23165 b23166 b23167 b23168 b23169 f23153
                omega
              have d23170 : (x (-3) 10).toNat = 0 := by
                have r23171 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23172 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e23173 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e23174 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e23175 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e23176 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e23177 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b23178 := hb (x (-8) 7)
                have b23179 := hb (x (-7) 6)
                have b23180 := hb (x (-6) 5)
                have b23181 := hb (x (-5) 4)
                have b23182 := hb (x (-4) 11)
                have b23183 := hb (x (-3) 10)
                have b23184 := hb (x (-2) 9)
                have b23185 := hb (x (-1) 8)
                clear * - r23171 e23172 e23173 e23174 e23175 e23176 e23177 b23178 b23179 b23180 b23181 b23182 b23183 b23184 b23185 f23153 d23154
                omega
              have d23186 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
                have r23187 := hand2 (x (-3) 1) (x (-3) 10)
                have b23188 := hb (x (-3) 10)
                have b23189 := hb (x (-3) 1 && x (-3) 10)
                clear * - r23187 b23188 b23189 d23170
                omega
              have d23190 : (x (-4) 11).toNat = 0 := by
                have r23191 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23192 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e23193 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e23194 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e23195 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e23196 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e23197 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b23198 := hb (x (-8) 7)
                have b23199 := hb (x (-7) 6)
                have b23200 := hb (x (-6) 5)
                have b23201 := hb (x (-5) 4)
                have b23202 := hb (x (-4) 11)
                have b23203 := hb (x (-3) 10)
                have b23204 := hb (x (-2) 9)
                have b23205 := hb (x (-1) 8)
                clear * - r23191 e23192 e23193 e23194 e23195 e23196 e23197 b23198 b23199 b23200 b23201 b23202 b23203 b23204 b23205 f23153 d23154 d23170
                omega
              have d23206 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
                have r23207 := hand2 (x (-4) 2) (x (-4) 11)
                have b23208 := hb (x (-4) 11)
                have b23209 := hb (x (-4) 2 && x (-4) 11)
                clear * - r23207 b23208 b23209 d23190
                omega
              have d23210 : (x (-5) 4).toNat = 0 := by
                have r23211 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23212 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e23213 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e23214 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e23215 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e23216 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e23217 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b23218 := hb (x (-8) 7)
                have b23219 := hb (x (-7) 6)
                have b23220 := hb (x (-6) 5)
                have b23221 := hb (x (-5) 4)
                have b23222 := hb (x (-4) 11)
                have b23223 := hb (x (-3) 10)
                have b23224 := hb (x (-2) 9)
                have b23225 := hb (x (-1) 8)
                clear * - r23211 e23212 e23213 e23214 e23215 e23216 e23217 b23218 b23219 b23220 b23221 b23222 b23223 b23224 b23225 f23153 d23154 d23170 d23190
                omega
              have d23226 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                have r23227 := hand1 (x (-5) 4) (x (-5) 14)
                have b23228 := hb (x (-5) 4)
                have b23229 := hb (x (-5) 4 && x (-5) 14)
                clear * - r23227 b23228 b23229 d23210
                omega
              have d23230 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                have r23231 := hand1 (x (-5) 4) (x (-5) 13)
                have b23232 := hb (x (-5) 4)
                have b23233 := hb (x (-5) 4 && x (-5) 13)
                clear * - r23231 b23232 b23233 d23210
                omega
              have d23234 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
                have r23235 := hand1 (x (-5) 4) (x (-5) 11)
                have b23236 := hb (x (-5) 4)
                have b23237 := hb (x (-5) 4 && x (-5) 11)
                clear * - r23235 b23236 b23237 d23210
                omega
              have d23238 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
                have r23239 := hand1 (x (-5) 4) (x (-5) 9)
                have b23240 := hb (x (-5) 4)
                have b23241 := hb (x (-5) 4 && x (-5) 9)
                clear * - r23239 b23240 b23241 d23210
                omega
              have d23242 : (x (-6) 5).toNat = 0 := by
                have r23243 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23244 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e23245 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e23246 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e23247 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e23248 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e23249 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b23250 := hb (x (-8) 7)
                have b23251 := hb (x (-7) 6)
                have b23252 := hb (x (-6) 5)
                have b23253 := hb (x (-5) 4)
                have b23254 := hb (x (-4) 11)
                have b23255 := hb (x (-3) 10)
                have b23256 := hb (x (-2) 9)
                have b23257 := hb (x (-1) 8)
                clear * - r23243 e23244 e23245 e23246 e23247 e23248 e23249 b23250 b23251 b23252 b23253 b23254 b23255 b23256 b23257 f23153 d23154 d23170 d23190 d23210
                omega
              have d23258 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                have r23259 := hand1 (x (-6) 5) (x (-6) 14)
                have b23260 := hb (x (-6) 5)
                have b23261 := hb (x (-6) 5 && x (-6) 14)
                clear * - r23259 b23260 b23261 d23242
                omega
              have d23262 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
                have r23263 := hand1 (x (-6) 5) (x (-6) 12)
                have b23264 := hb (x (-6) 5)
                have b23265 := hb (x (-6) 5 && x (-6) 12)
                clear * - r23263 b23264 b23265 d23242
                omega
              have d23266 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
                have r23267 := hand1 (x (-6) 5) (x (-6) 10)
                have b23268 := hb (x (-6) 5)
                have b23269 := hb (x (-6) 5 && x (-6) 10)
                clear * - r23267 b23268 b23269 d23242
                omega
              have d23270 : (x (-7) 6).toNat = 0 := by
                have r23271 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23272 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e23273 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e23274 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e23275 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e23276 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e23277 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b23278 := hb (x (-8) 7)
                have b23279 := hb (x (-7) 6)
                have b23280 := hb (x (-6) 5)
                have b23281 := hb (x (-5) 4)
                have b23282 := hb (x (-4) 11)
                have b23283 := hb (x (-3) 10)
                have b23284 := hb (x (-2) 9)
                have b23285 := hb (x (-1) 8)
                clear * - r23271 e23272 e23273 e23274 e23275 e23276 e23277 b23278 b23279 b23280 b23281 b23282 b23283 b23284 b23285 f23153 d23154 d23170 d23190 d23210 d23242
                omega
              have d23286 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
                have r23287 := hand1 (x (-7) 6) (x (-7) 13)
                have b23288 := hb (x (-7) 6)
                have b23289 := hb (x (-7) 6 && x (-7) 13)
                clear * - r23287 b23288 b23289 d23270
                omega
              have d23290 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
                have r23291 := hand1 (x (-7) 6) (x (-7) 11)
                have b23292 := hb (x (-7) 6)
                have b23293 := hb (x (-7) 6 && x (-7) 11)
                clear * - r23291 b23292 b23293 d23270
                omega
              have d23294 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
                have r23295 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23296 := hb (x (-7) 6)
                have b23297 := hb (x (-1) 9)
                have b23298 := hb (x (-2) 1 && x (-2) 10)
                have b23299 := hb (x (-3) 2 && x (-3) 11)
                have b23300 := hb (x (-4) 3 && x (-4) 12)
                have b23301 := hb (x (-5) 4 && x (-5) 13)
                have b23302 := hb (x (-6) 5 && x (-6) 14)
                clear * - r23295 b23296 b23297 b23298 b23299 b23300 b23301 b23302 g10 g72 g73 d23230 d23258 d23270
                omega
              have d23303 : (x (-4) 12).toNat = 1 := by
                have r23304 := hand2 (x (-4) 3) (x (-4) 12)
                have b23305 := hb (x (-4) 12)
                have b23306 := hb (x (-4) 3 && x (-4) 12)
                clear * - r23304 b23305 b23306 d23294
                omega
              have d23307 : (x (-5) 13).toNat = 0 := by
                have r23308 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23309 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e23310 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b23311 := hb (x (-7) 3)
                have b23312 := hb (x (-6) 2)
                have b23313 := hb (x (-5) 13)
                have b23314 := hb (x (-4) 12)
                clear * - r23308 e23309 e23310 b23311 b23312 b23313 b23314 d23303
                omega
              have d23315 : (x (-5) 5).toNat = 0 := by
                have r23316 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
                have b23317 := hb (x (-5) 5)
                have b23318 := hb (x (-5) 13)
                clear * - r23316 b23317 b23318 d23307
                omega
              have d23319 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
                have r23320 := hand1 (x (-5) 5) (x (-5) 14)
                have b23321 := hb (x (-5) 5)
                have b23322 := hb (x (-5) 5 && x (-5) 14)
                clear * - r23320 b23321 b23322 d23315
                omega
              have d23323 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
                have r23324 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23325 := hb (x (-5) 5)
                have b23326 := hb (x 0 10)
                have b23327 := hb (x (-1) 1 && x (-1) 11)
                have b23328 := hb (x (-2) 2 && x (-2) 12)
                have b23329 := hb (x (-3) 3 && x (-3) 13)
                have b23330 := hb (x (-4) 4 && x (-4) 14)
                clear * - r23324 b23325 b23326 b23327 b23328 b23329 b23330 g19 g83 g84 g85 d23315
                omega
              have d23331 : (x (-4) 14).toNat = 1 := by
                have r23332 := hand2 (x (-4) 4) (x (-4) 14)
                have b23333 := hb (x (-4) 14)
                have b23334 := hb (x (-4) 4 && x (-4) 14)
                clear * - r23332 b23333 b23334 d23323
                omega
              have d23335 : (x (-5) 1).toNat = 0 := by
                have r23336 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23337 := hb (x (-5) 1)
                have b23338 := hb (x (-4) 14)
                clear * - r23336 b23337 b23338 d23331
                omega
              have d23339 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
                have r23340 := hand1 (x (-5) 1) (x (-5) 12)
                have b23341 := hb (x (-5) 1)
                have b23342 := hb (x (-5) 1 && x (-5) 12)
                clear * - r23340 b23341 b23342 d23335
                omega
              have d23343 : (x (-5) 9).toNat = 0 := by
                have r23344 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
                have b23345 := hb (x (-5) 1)
                have b23346 := hb (x (-5) 9)
                clear * - r23344 b23345 b23346 d23335
                omega
              have d23347 : (x (-4) 4).toNat = 1 := by
                have r23348 := hand1 (x (-4) 4) (x (-4) 14)
                have b23349 := hb (x (-4) 4)
                have b23350 := hb (x (-4) 4 && x (-4) 14)
                clear * - r23348 b23349 b23350 d23323
                omega
              have d23351 : (x (-6) 6).toNat = 0 := by
                have r23352 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23353 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                have e23354 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                have e23355 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                have e23356 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                have e23357 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                have e23358 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                have b23359 := hb (x (-7) 7)
                have b23360 := hb (x (-6) 6)
                have b23361 := hb (x (-5) 5)
                have b23362 := hb (x (-4) 4)
                have b23363 := hb (x (-3) 11)
                have b23364 := hb (x (-2) 10)
                have b23365 := hb (x (-1) 9)
                have b23366 := hb (x 0 8)
                clear * - r23352 e23353 e23354 e23355 e23356 e23357 e23358 b23359 b23360 b23361 b23362 b23363 b23364 b23365 b23366 f22355 g10 g4 g1 d23347 d23315
                omega
              have d23367 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
                have r23368 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23369 := hb (x (-6) 6)
                have b23370 := hb (x 0 9)
                have b23371 := hb (x (-1) 1 && x (-1) 10)
                have b23372 := hb (x (-2) 2 && x (-2) 11)
                have b23373 := hb (x (-3) 3 && x (-3) 12)
                have b23374 := hb (x (-4) 4 && x (-4) 13)
                have b23375 := hb (x (-5) 5 && x (-5) 14)
                clear * - r23368 b23369 b23370 b23371 b23372 b23373 b23374 b23375 f22373 g74 g75 g76 d23319 d23351
                omega
              have d23376 : (x (-4) 13).toNat = 1 := by
                have r23377 := hand2 (x (-4) 4) (x (-4) 13)
                have b23378 := hb (x (-4) 13)
                have b23379 := hb (x (-4) 4 && x (-4) 13)
                clear * - r23377 b23378 b23379 d23367
                omega
              have d23380 : (x (-4) 1).toNat = 1 := by
                have r23381 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                have b23382 := hb (x (-4) 1)
                have b23383 := hb (x (-4) 13)
                clear * - r23381 b23382 b23383 d23376
                omega
              have d23384 : (x (-3) 14).toNat = 0 := by
                have r23385 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23386 := hb (x (-4) 1)
                have b23387 := hb (x (-3) 14)
                clear * - r23385 b23386 b23387 d23380
                omega
              have d23388 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                have r23389 := hand2 (x (-3) 1) (x (-3) 14)
                have b23390 := hb (x (-3) 14)
                have b23391 := hb (x (-3) 1 && x (-3) 14)
                clear * - r23389 b23390 b23391 d23384
                omega
              have d23392 : (x (-3) 2).toNat = 0 := by
                have r23393 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                have b23394 := hb (x (-3) 2)
                have b23395 := hb (x (-3) 14)
                clear * - r23393 b23394 b23395 d23384
                omega
              have d23396 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                have r23397 := hand1 (x (-3) 2) (x (-3) 12)
                have b23398 := hb (x (-3) 2)
                have b23399 := hb (x (-3) 2 && x (-3) 12)
                clear * - r23397 b23398 b23399 d23392
                omega
              have d23400 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
                have r23401 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23402 := hb (x (-6) 5)
                have b23403 := hb (x (-1) 10)
                have b23404 := hb (x (-2) 1 && x (-2) 11)
                have b23405 := hb (x (-3) 2 && x (-3) 12)
                have b23406 := hb (x (-4) 3 && x (-4) 13)
                have b23407 := hb (x (-5) 4 && x (-5) 14)
                clear * - r23401 b23402 b23403 b23404 b23405 b23406 b23407 g11 g82 d23396 d23226 d23242
                omega
              have d23408 : (x (-4) 3).toNat = 1 := by
                have r23409 := hand1 (x (-4) 3) (x (-4) 13)
                have b23410 := hb (x (-4) 3)
                have b23411 := hb (x (-4) 3 && x (-4) 13)
                clear * - r23409 b23410 b23411 d23400
                omega
              have d23412 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
                have r23413 := hand1 (x (-3) 2) (x (-3) 9)
                have b23414 := hb (x (-3) 2)
                have b23415 := hb (x (-3) 2 && x (-3) 9)
                clear * - r23413 b23414 b23415 d23392
                omega
              have d23416 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                have r23417 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23418 := hb (x (-3) 2)
                have b23419 := hb (x (-1) 13)
                have b23420 := hb (x (-2) 1 && x (-2) 14)
                clear * - r23417 b23418 b23419 b23420 g13 d23392
                omega
              have d23421 : (x (-2) 14).toNat = 1 := by
                have r23422 := hand2 (x (-2) 1) (x (-2) 14)
                have b23423 := hb (x (-2) 14)
                have b23424 := hb (x (-2) 1 && x (-2) 14)
                clear * - r23422 b23423 b23424 d23416
                omega
              have d23425 : (x (-3) 1).toNat = 0 := by
                have r23426 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23427 := hb (x (-3) 1)
                have b23428 := hb (x (-2) 14)
                clear * - r23426 b23427 b23428 d23421
                omega
              have d23429 : (x (-3) 13).toNat = 0 := by
                have r23430 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                have b23431 := hb (x (-3) 1)
                have b23432 := hb (x (-3) 13)
                clear * - r23430 b23431 b23432 d23425
                omega
              have d23433 : (x (-3) 9).toNat = 0 := by
                have r23434 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
                have b23435 := hb (x (-3) 1)
                have b23436 := hb (x (-3) 9)
                clear * - r23434 b23435 b23436 d23425
                omega
              have d23437 : (x (-1) 12).toNat = 0 := by
                have r23438 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23439 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e23440 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b23441 := hb (x (-4) 3)
                have b23442 := hb (x (-3) 2)
                have b23443 := hb (x (-2) 13)
                have b23444 := hb (x (-1) 12)
                clear * - r23438 e23439 e23440 b23441 b23442 b23443 b23444 d23392 d23408
                omega
              have d23445 : (x (-2) 13).toNat = 0 := by
                have r23446 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23447 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e23448 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b23449 := hb (x (-4) 3)
                have b23450 := hb (x (-3) 2)
                have b23451 := hb (x (-2) 13)
                have b23452 := hb (x (-1) 12)
                clear * - r23446 e23447 e23448 b23449 b23450 b23451 b23452 d23437 d23392 d23408
                omega
              have d23453 : (x (-4) 2).toNat = 1 := by
                have r23454 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23455 := hb (x (-4) 2)
                have b23456 := hb (x (-2) 13)
                have b23457 := hb (x (-3) 1 && x (-3) 14)
                clear * - r23454 b23455 b23456 b23457 d23445 d23388
                omega
              have d23458 : (x (-2) 12).toNat = 0 := by
                have r23459 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23460 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e23461 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b23462 := hb (x (-5) 3)
                have b23463 := hb (x (-4) 2)
                have b23464 := hb (x (-3) 13)
                have b23465 := hb (x (-2) 12)
                clear * - r23459 e23460 e23461 b23462 b23463 b23464 b23465 d23429 d23453
                omega
              have d23466 : (x (-5) 3).toNat = 0 := by
                have r23467 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23468 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e23469 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b23470 := hb (x (-5) 3)
                have b23471 := hb (x (-4) 2)
                have b23472 := hb (x (-3) 13)
                have b23473 := hb (x (-2) 12)
                clear * - r23467 e23468 e23469 b23470 b23471 b23472 b23473 d23458 d23429 d23453
                omega
              have d23474 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
                have r23475 := hand1 (x (-5) 3) (x (-5) 12)
                have b23476 := hb (x (-5) 3)
                have b23477 := hb (x (-5) 3 && x (-5) 12)
                clear * - r23475 b23476 b23477 d23466
                omega
              have d23478 : (x (-5) 11).toNat = 0 := by
                have r23479 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                have b23480 := hb (x (-5) 3)
                have b23481 := hb (x (-5) 11)
                clear * - r23479 b23480 b23481 d23466
                omega
              have d23482 : (x (-6) 2).toNat = 0 := by
                have r23483 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23484 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e23485 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b23486 := hb (x (-7) 3)
                have b23487 := hb (x (-6) 2)
                have b23488 := hb (x (-5) 13)
                have b23489 := hb (x (-4) 12)
                clear * - r23483 e23484 e23485 b23486 b23487 b23488 b23489 d23303 d23307
                omega
              have d23490 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
                have r23491 := hand1 (x (-6) 2) (x (-6) 13)
                have b23492 := hb (x (-6) 2)
                have b23493 := hb (x (-6) 2 && x (-6) 13)
                clear * - r23491 b23492 b23493 d23482
                omega
              have d23494 : (x (-6) 10).toNat = 0 := by
                have r23495 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                have b23496 := hb (x (-6) 2)
                have b23497 := hb (x (-6) 10)
                clear * - r23495 b23496 b23497 d23482
                omega
              have d23498 : (x (-7) 3).toNat = 0 := by
                have r23499 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23500 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e23501 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b23502 := hb (x (-7) 3)
                have b23503 := hb (x (-6) 2)
                have b23504 := hb (x (-5) 13)
                have b23505 := hb (x (-4) 12)
                clear * - r23499 e23500 e23501 b23502 b23503 b23504 b23505 d23303 d23307 d23482
                omega
              have d23506 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
                have r23507 := hand1 (x (-7) 3) (x (-7) 14)
                have b23508 := hb (x (-7) 3)
                have b23509 := hb (x (-7) 3 && x (-7) 14)
                clear * - r23507 b23508 b23509 d23498
                omega
              have d23510 : (x (-8) 4).toNat = 1 := by
                have r23511 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23512 := hb (x (-8) 4)
                have b23513 := hb (x (-4) 11)
                have b23514 := hb (x (-5) 1 && x (-5) 12)
                have b23515 := hb (x (-6) 2 && x (-6) 13)
                have b23516 := hb (x (-7) 3 && x (-7) 14)
                clear * - r23511 b23512 b23513 b23514 b23515 b23516 d23190 d23339 d23490 d23506
                omega
              have d23517 : (x (-8) 12).toNat = 1 := by
                have r23518 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                have b23519 := hb (x (-8) 4)
                have b23520 := hb (x (-8) 12)
                clear * - r23518 b23519 b23520 d23510
                omega
              have d23521 : (x (-9) 13).toNat = 0 := by
                have r23522 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23523 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                have e23524 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                have b23525 := hb (x (-11) 3)
                have b23526 := hb (x (-10) 2)
                have b23527 := hb (x (-9) 13)
                have b23528 := hb (x (-8) 12)
                clear * - r23522 e23523 e23524 b23525 b23526 b23527 b23528 d23517
                omega
              have d23529 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
                have r23530 := hand2 (x (-9) 8) (x (-9) 13)
                have b23531 := hb (x (-9) 13)
                have b23532 := hb (x (-9) 8 && x (-9) 13)
                clear * - r23530 b23531 b23532 d23521
                omega
              have d23533 : (x (-9) 5).toNat = 0 := by
                have r23534 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
                have b23535 := hb (x (-9) 5)
                have b23536 := hb (x (-9) 13)
                clear * - r23534 b23535 b23536 d23521
                omega
              have d23537 : (x (-7) 11).toNat = 0 := by
                have r23538 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                have b23539 := hb (x (-7) 3)
                have b23540 := hb (x (-7) 11)
                clear * - r23538 b23539 b23540 d23498
                omega
              have d23541 : (x (-8) 7).toNat = 0 := by
                have r23542 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23543 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e23544 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e23545 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e23546 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e23547 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e23548 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have b23549 := hb (x (-8) 7)
                have b23550 := hb (x (-7) 6)
                have b23551 := hb (x (-6) 5)
                have b23552 := hb (x (-5) 4)
                have b23553 := hb (x (-4) 11)
                have b23554 := hb (x (-3) 10)
                have b23555 := hb (x (-2) 9)
                have b23556 := hb (x (-1) 8)
                clear * - r23542 e23543 e23544 e23545 e23546 e23547 e23548 b23549 b23550 b23551 b23552 b23553 b23554 b23555 b23556 f23153 d23154 d23170 d23190 d23210 d23242 d23270
                omega
              have d23557 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
                have r23558 := hand1 (x (-8) 7) (x (-8) 14)
                have b23559 := hb (x (-8) 7)
                have b23560 := hb (x (-8) 7 && x (-8) 14)
                clear * - r23558 b23559 b23560 d23541
                omega
              have d23561 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
                have r23562 := hand1 (x (-8) 7) (x (-8) 12)
                have b23563 := hb (x (-8) 7)
                have b23564 := hb (x (-8) 7 && x (-8) 12)
                clear * - r23562 b23563 b23564 d23541
                omega
              have d23565 : (x (-4) 8).toNat = 0 := by
                have r23566 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23567 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                have e23568 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                have e23569 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                have e23570 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                have e23571 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                have e23572 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                have b23573 := hb (x (-11) 7)
                have b23574 := hb (x (-10) 6)
                have b23575 := hb (x (-9) 5)
                have b23576 := hb (x (-8) 4)
                have b23577 := hb (x (-7) 11)
                have b23578 := hb (x (-6) 10)
                have b23579 := hb (x (-5) 9)
                have b23580 := hb (x (-4) 8)
                clear * - r23566 e23567 e23568 e23569 e23570 e23571 e23572 b23573 b23574 b23575 b23576 b23577 b23578 b23579 b23580 d23343 d23494 d23537 d23510 d23533
                omega
              have d23581 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
                have r23582 := hand2 (x (-4) 3) (x (-4) 8)
                have b23583 := hb (x (-4) 8)
                have b23584 := hb (x (-4) 3 && x (-4) 8)
                clear * - r23582 b23583 b23584 d23565
                omega
              have r23585 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23586 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
              have e23587 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
              have e23588 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
              have e23589 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
              have e23590 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
              have e23591 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
              have r23592 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23593 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e23594 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e23595 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e23596 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e23597 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e23598 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have r23599 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r23600 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r23601 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r23602 := hand1 (x (-10) 9) (x (-10) 14)
              have r23603 := hand2 (x (-2) 1) (x (-2) 8)
              have r23604 := hand2 (x (-4) 3) (x (-4) 10)
              have r23605 := hand1 (x (-6) 4) (x (-6) 13)
              have r23606 := hand1 (x (-7) 5) (x (-7) 14)
              linarith only [r23585, e23586, e23587, e23588, e23589, e23590, e23591, r23592, e23593, e23594, e23595, e23596, e23597, e23598, r23599, r23600, r23601, r23602, r23603, r23604, r23605, r23606, d23478, d23433, d23154, g7, g9, g46, g47, d23581, d23238, d23266, d23290, d23561, d23529, d23412, d23234, d23262, d23286, d23557, d23186, d23206, d23474]
          · have f23647 : (x 1 7).toNat = 1 := by rw [h22386]; rfl
            have d23648 : (x 8 8).toNat = 0 := by
              have r23649 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23650 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e23651 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e23652 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e23653 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e23654 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e23655 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b23656 := hb (x 1 7)
              have b23657 := hb (x 2 6)
              have b23658 := hb (x 3 5)
              have b23659 := hb (x 4 4)
              have b23660 := hb (x 5 11)
              have b23661 := hb (x 6 10)
              have b23662 := hb (x 7 9)
              have b23663 := hb (x 8 8)
              clear * - r23649 e23650 e23651 e23652 e23653 e23654 e23655 b23656 b23657 b23658 b23659 b23660 b23661 b23662 b23663 f23647
              omega
            have d23664 : (x 7 9).toNat = 0 := by
              have r23665 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23666 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e23667 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e23668 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e23669 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e23670 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e23671 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b23672 := hb (x 1 7)
              have b23673 := hb (x 2 6)
              have b23674 := hb (x 3 5)
              have b23675 := hb (x 4 4)
              have b23676 := hb (x 5 11)
              have b23677 := hb (x 6 10)
              have b23678 := hb (x 7 9)
              have b23679 := hb (x 8 8)
              clear * - r23665 e23666 e23667 e23668 e23669 e23670 e23671 b23672 b23673 b23674 b23675 b23676 b23677 b23678 b23679 d23648 f23647
              omega
            have d23680 : (x 6 10).toNat = 0 := by
              have r23681 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23682 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e23683 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e23684 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e23685 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e23686 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e23687 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b23688 := hb (x 1 7)
              have b23689 := hb (x 2 6)
              have b23690 := hb (x 3 5)
              have b23691 := hb (x 4 4)
              have b23692 := hb (x 5 11)
              have b23693 := hb (x 6 10)
              have b23694 := hb (x 7 9)
              have b23695 := hb (x 8 8)
              clear * - r23681 e23682 e23683 e23684 e23685 e23686 e23687 b23688 b23689 b23690 b23691 b23692 b23693 b23694 b23695 d23648 d23664 f23647
              omega
            have d23696 : (x 6 1 && x 6 10).toNat = 0 := by
              have r23697 := hand2 (x 6 1) (x 6 10)
              have b23698 := hb (x 6 10)
              have b23699 := hb (x 6 1 && x 6 10)
              clear * - r23697 b23698 b23699 d23680
              omega
            have d23700 : (x 5 11).toNat = 0 := by
              have r23701 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23702 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e23703 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e23704 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e23705 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e23706 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e23707 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b23708 := hb (x 1 7)
              have b23709 := hb (x 2 6)
              have b23710 := hb (x 3 5)
              have b23711 := hb (x 4 4)
              have b23712 := hb (x 5 11)
              have b23713 := hb (x 6 10)
              have b23714 := hb (x 7 9)
              have b23715 := hb (x 8 8)
              clear * - r23701 e23702 e23703 e23704 e23705 e23706 e23707 b23708 b23709 b23710 b23711 b23712 b23713 b23714 b23715 d23648 d23664 d23680 f23647
              omega
            have d23716 : (x 5 1 && x 5 11).toNat = 0 := by
              have r23717 := hand2 (x 5 1) (x 5 11)
              have b23718 := hb (x 5 11)
              have b23719 := hb (x 5 1 && x 5 11)
              clear * - r23717 b23718 b23719 d23700
              omega
            have d23720 : (x 5 2 && x 5 11).toNat = 0 := by
              have r23721 := hand2 (x 5 2) (x 5 11)
              have b23722 := hb (x 5 11)
              have b23723 := hb (x 5 2 && x 5 11)
              clear * - r23721 b23722 b23723 d23700
              omega
            have d23724 : (x 4 3 && x 4 12).toNat = 1 := by
              have r23725 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b23726 := hb (x 1 6)
              have b23727 := hb (x 7 9)
              have b23728 := hb (x 6 1 && x 6 10)
              have b23729 := hb (x 5 2 && x 5 11)
              have b23730 := hb (x 4 3 && x 4 12)
              have b23731 := hb (x 3 4 && x 3 13)
              have b23732 := hb (x 2 5 && x 2 14)
              clear * - r23725 b23726 b23727 b23728 b23729 b23730 b23731 b23732 d23664 d23696 d23720 g80 g81 g23
              omega
            have d23733 : (x 4 12).toNat = 1 := by
              have r23734 := hand2 (x 4 3) (x 4 12)
              have b23735 := hb (x 4 12)
              have b23736 := hb (x 4 3 && x 4 12)
              clear * - r23734 b23735 b23736 d23724
              omega
            have d23737 : (x 3 13).toNat = 0 := by
              have r23738 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23739 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e23740 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b23741 := hb (x 1 3)
              have b23742 := hb (x 2 2)
              have b23743 := hb (x 3 13)
              have b23744 := hb (x 4 12)
              clear * - r23738 e23739 e23740 b23741 b23742 b23743 b23744 d23733 f22385
              omega
            have d23745 : (x 3 3 && x 3 13).toNat = 0 := by
              have r23746 := hand2 (x 3 3) (x 3 13)
              have b23747 := hb (x 3 13)
              have b23748 := hb (x 3 3 && x 3 13)
              clear * - r23746 b23747 b23748 d23737
              omega
            have d23749 : (x 4 2 && x 4 12).toNat = 1 := by
              have r23750 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b23751 := hb (x 1 5)
              have b23752 := hb (x 6 10)
              have b23753 := hb (x 5 1 && x 5 11)
              have b23754 := hb (x 4 2 && x 4 12)
              have b23755 := hb (x 3 3 && x 3 13)
              have b23756 := hb (x 2 4 && x 2 14)
              clear * - r23750 b23751 b23752 b23753 b23754 b23755 b23756 d23680 d23716 d23745 g86 g22
              omega
            have d23757 : (x 4 2).toNat = 1 := by
              have r23758 := hand1 (x 4 2) (x 4 12)
              have b23759 := hb (x 4 2)
              have b23760 := hb (x 4 2 && x 4 12)
              clear * - r23758 b23759 b23760 d23749
              omega
            have d23761 : (x 6 12).toNat = 0 := by
              have r23762 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23763 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e23764 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b23765 := hb (x 3 3)
              have b23766 := hb (x 4 2)
              have b23767 := hb (x 5 13)
              have b23768 := hb (x 6 12)
              clear * - r23762 e23763 e23764 b23765 b23766 b23767 b23768 d23757
              omega
            have d23769 : (x 5 13).toNat = 0 := by
              have r23770 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23771 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e23772 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b23773 := hb (x 3 3)
              have b23774 := hb (x 4 2)
              have b23775 := hb (x 5 13)
              have b23776 := hb (x 6 12)
              clear * - r23770 e23771 e23772 b23773 b23774 b23775 b23776 d23761 d23757
              omega
            have d23777 : (x 3 5).toNat = 0 := by
              have r23778 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
              have b23779 := hb (x 3 5)
              have b23780 := hb (x 3 13)
              clear * - r23778 b23779 b23780 d23737
              omega
            have d23781 : (x 2 1 && x 2 14).toNat = 1 := by
              have r23782 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b23783 := hb (x 1 2)
              have b23784 := hb (x 3 13)
              have b23785 := hb (x 2 1 && x 2 14)
              clear * - r23782 b23783 b23784 b23785 d23737 g20
              omega
            have d23786 : (x 2 1).toNat = 1 := by
              have r23787 := hand1 (x 2 1) (x 2 14)
              have b23788 := hb (x 2 1)
              have b23789 := hb (x 2 1 && x 2 14)
              clear * - r23787 b23788 b23789 d23781
              omega
            have d23790 : (x 3 14).toNat = 0 := by
              have r23791 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b23792 := hb (x 2 1)
              have b23793 := hb (x 3 14)
              clear * - r23791 b23792 b23793 d23786
              omega
            have d23794 : (x 3 2).toNat = 0 := by
              have r23795 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
              have b23796 := hb (x 3 2)
              have b23797 := hb (x 3 14)
              clear * - r23795 b23796 b23797 d23790
              omega
            have d23798 : (x 4 1 && x 4 14).toNat = 1 := by
              have r23799 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b23800 := hb (x 3 2)
              have b23801 := hb (x 5 13)
              have b23802 := hb (x 4 1 && x 4 14)
              clear * - r23799 b23800 b23801 b23802 d23769 d23794
              omega
            have d23803 : (x 4 1).toNat = 1 := by
              have r23804 := hand1 (x 4 1) (x 4 14)
              have b23805 := hb (x 4 1)
              have b23806 := hb (x 4 1 && x 4 14)
              clear * - r23804 b23805 b23806 d23798
              omega
            have d23807 : (x 5 14).toNat = 0 := by
              have r23808 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b23809 := hb (x 4 1)
              have b23810 := hb (x 5 14)
              clear * - r23808 b23809 b23810 d23803
              omega
            have d23811 : (x 5 3 && x 5 14).toNat = 0 := by
              have r23812 := hand2 (x 5 3) (x 5 14)
              have b23813 := hb (x 5 14)
              have b23814 := hb (x 5 3 && x 5 14)
              clear * - r23812 b23813 b23814 d23807
              omega
            have d23815 : (x 5 6).toNat = 0 := by
              have r23816 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
              have b23817 := hb (x 5 6)
              have b23818 := hb (x 5 14)
              clear * - r23816 b23817 b23818 d23807
              omega
            have d23819 : (x 5 2 && x 5 6).toNat = 0 := by
              have r23820 := hand2 (x 5 2) (x 5 6)
              have b23821 := hb (x 5 6)
              have b23822 := hb (x 5 2 && x 5 6)
              clear * - r23820 b23821 b23822 d23815
              omega
            have d23823 : (x 5 2).toNat = 0 := by
              have r23824 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b23825 := hb (x 5 2)
              have b23826 := hb (x 5 14)
              clear * - r23824 b23825 b23826 d23807
              omega
            have d23827 : (x 4 3).toNat = 1 := by
              have r23828 := hand1 (x 4 3) (x 4 12)
              have b23829 := hb (x 4 3)
              have b23830 := hb (x 4 3 && x 4 12)
              clear * - r23828 b23829 b23830 d23724
              omega
            have d23831 : (x 7 12).toNat = 0 := by
              have r23832 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23833 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e23834 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b23835 := hb (x 4 3)
              have b23836 := hb (x 5 2)
              have b23837 := hb (x 6 13)
              have b23838 := hb (x 7 12)
              clear * - r23832 e23833 e23834 b23835 b23836 b23837 b23838 d23823 d23827
              omega
            have d23839 : (x 7 1 && x 7 12).toNat = 0 := by
              have r23840 := hand2 (x 7 1) (x 7 12)
              have b23841 := hb (x 7 12)
              have b23842 := hb (x 7 1 && x 7 12)
              clear * - r23840 b23841 b23842 d23831
              omega
            have d23843 : (x 7 4).toNat = 0 := by
              have r23844 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
              have b23845 := hb (x 7 4)
              have b23846 := hb (x 7 12)
              clear * - r23844 b23845 b23846 d23831
              omega
            have d23847 : (x 6 13).toNat = 0 := by
              have r23848 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23849 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e23850 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b23851 := hb (x 4 3)
              have b23852 := hb (x 5 2)
              have b23853 := hb (x 6 13)
              have b23854 := hb (x 7 12)
              clear * - r23848 e23849 e23850 b23851 b23852 b23853 b23854 d23831 d23823 d23827
              omega
            have d23855 : (x 6 2 && x 6 13).toNat = 0 := by
              have r23856 := hand2 (x 6 2) (x 6 13)
              have b23857 := hb (x 6 13)
              have b23858 := hb (x 6 2 && x 6 13)
              clear * - r23856 b23857 b23858 d23847
              omega
            have d23859 : (x 6 5).toNat = 0 := by
              have r23860 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
              have b23861 := hb (x 6 5)
              have b23862 := hb (x 6 13)
              clear * - r23860 b23861 b23862 d23847
              omega
            have d23863 : (x 4 4).toNat = 0 := by
              have r23864 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23865 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e23866 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e23867 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e23868 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e23869 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e23870 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b23871 := hb (x 1 7)
              have b23872 := hb (x 2 6)
              have b23873 := hb (x 3 5)
              have b23874 := hb (x 4 4)
              have b23875 := hb (x 5 11)
              have b23876 := hb (x 6 10)
              have b23877 := hb (x 7 9)
              have b23878 := hb (x 8 8)
              clear * - r23864 e23865 e23866 e23867 e23868 e23869 e23870 b23871 b23872 b23873 b23874 b23875 b23876 b23877 b23878 d23648 d23664 d23680 d23700 d23777 f23647
              omega
            have d23879 : (x 8 11).toNat = 1 := by
              have r23880 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b23881 := hb (x 4 4)
              have b23882 := hb (x 8 11)
              have b23883 := hb (x 7 1 && x 7 12)
              have b23884 := hb (x 6 2 && x 6 13)
              have b23885 := hb (x 5 3 && x 5 14)
              clear * - r23880 b23881 b23882 b23883 b23884 b23885 d23839 d23855 d23811 d23863
              omega
            have d23886 : (x 8 3).toNat = 1 := by
              have r23887 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
              have b23888 := hb (x 8 3)
              have b23889 := hb (x 8 11)
              clear * - r23887 b23888 b23889 d23879
              omega
            have d23890 : (x 11 12).toNat = 0 := by
              have r23891 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23892 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e23893 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b23894 := hb (x 8 3)
              have b23895 := hb (x 9 2)
              have b23896 := hb (x 10 13)
              have b23897 := hb (x 11 12)
              clear * - r23891 e23892 e23893 b23894 b23895 b23896 b23897 d23886
              omega
            have d23898 : (x 10 13).toNat = 0 := by
              have r23899 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23900 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e23901 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b23902 := hb (x 8 3)
              have b23903 := hb (x 9 2)
              have b23904 := hb (x 10 13)
              have b23905 := hb (x 11 12)
              clear * - r23899 e23900 e23901 b23902 b23903 b23904 b23905 d23890 d23886
              omega
            have d23906 : (x 9 2).toNat = 0 := by
              have r23907 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23908 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e23909 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b23910 := hb (x 8 3)
              have b23911 := hb (x 9 2)
              have b23912 := hb (x 10 13)
              have b23913 := hb (x 11 12)
              clear * - r23907 e23908 e23909 b23910 b23911 b23912 b23913 d23890 d23898 d23886
              omega
            have d23914 : (x 9 2 && x 9 13).toNat = 0 := by
              have r23915 := hand1 (x 9 2) (x 9 13)
              have b23916 := hb (x 9 2)
              have b23917 := hb (x 9 2 && x 9 13)
              clear * - r23915 b23916 b23917 d23906
              omega
            have d23918 : (x 9 10).toNat = 0 := by
              have r23919 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
              have b23920 := hb (x 9 2)
              have b23921 := hb (x 9 10)
              clear * - r23919 b23920 b23921 d23906
              omega
            have d23922 : (x 11 8).toNat = 0 := by
              have r23923 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23924 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e23925 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e23926 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e23927 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e23928 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e23929 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b23930 := hb (x 4 7)
              have b23931 := hb (x 5 6)
              have b23932 := hb (x 6 5)
              have b23933 := hb (x 7 4)
              have b23934 := hb (x 8 11)
              have b23935 := hb (x 9 10)
              have b23936 := hb (x 10 9)
              have b23937 := hb (x 11 8)
              clear * - r23923 e23924 e23925 e23926 e23927 e23928 e23929 b23930 b23931 b23932 b23933 b23934 b23935 b23936 b23937 d23918 d23879 d23843 d23859 d23815
              omega
            have d23938 : (x 10 9).toNat = 0 := by
              have r23939 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23940 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e23941 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e23942 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e23943 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e23944 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e23945 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b23946 := hb (x 4 7)
              have b23947 := hb (x 5 6)
              have b23948 := hb (x 6 5)
              have b23949 := hb (x 7 4)
              have b23950 := hb (x 8 11)
              have b23951 := hb (x 9 10)
              have b23952 := hb (x 10 9)
              have b23953 := hb (x 11 8)
              clear * - r23939 e23940 e23941 e23942 e23943 e23944 e23945 b23946 b23947 b23948 b23949 b23950 b23951 b23952 b23953 d23922 d23918 d23879 d23843 d23859 d23815
              omega
            have d23954 : (x 4 7).toNat = 0 := by
              have r23955 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e23956 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e23957 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e23958 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e23959 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e23960 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e23961 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b23962 := hb (x 4 7)
              have b23963 := hb (x 5 6)
              have b23964 := hb (x 6 5)
              have b23965 := hb (x 7 4)
              have b23966 := hb (x 8 11)
              have b23967 := hb (x 9 10)
              have b23968 := hb (x 10 9)
              have b23969 := hb (x 11 8)
              clear * - r23955 e23956 e23957 e23958 e23959 e23960 e23961 b23962 b23963 b23964 b23965 b23966 b23967 b23968 b23969 d23922 d23938 d23918 d23879 d23843 d23859 d23815
              omega
            have d23970 : (x 4 3 && x 4 7).toNat = 0 := by
              have r23971 := hand2 (x 4 3) (x 4 7)
              have b23972 := hb (x 4 7)
              have b23973 := hb (x 4 3 && x 4 7)
              clear * - r23971 b23972 b23973 d23954
              omega
            have r23974 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e23975 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e23976 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e23977 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e23978 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e23979 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e23980 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have r23981 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e23982 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e23983 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e23984 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e23985 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e23986 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e23987 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have r23988 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e23989 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e23990 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have r23991 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e23992 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e23993 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have r23994 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r23995 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e23996 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
            have e23997 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
            have r23998 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e23999 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
            have e24000 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
            have r24001 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r24002 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r24003 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r24004 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r24005 := hand2 (x (-1) 8) (x (-1) 12)
            have r24006 := hand2 (x (-2) 9) (x (-2) 13)
            have r24007 := hand2 (x 8 2) (x 8 6)
            have r24008 := hand1 (x 7 3) (x 7 7)
            have r24009 := hand1 (x 7 1) (x 7 7)
            have r24010 := hand1 (x (-4) 3) (x (-4) 12)
            have r24011 := hand1 (x (-5) 4) (x (-5) 13)
            have r24012 := hand1 (x (-6) 5) (x (-6) 14)
            have r24013 := hand2 (x 10 1) (x 10 12)
            have r24014 := hand2 (x 8 3) (x 8 14)
            linarith only [r23974, e23975, e23976, e23977, e23978, e23979, e23980, r23981, e23982, e23983, e23984, e23985, e23986, e23987, r23988, e23989, e23990, r23991, e23992, e23993, r23994, r23995, e23996, e23997, r23998, e23999, e24000, r24001, r24002, r24003, r24004, r24005, r24006, r24007, r24008, r24009, r24010, r24011, r24012, r24013, r24014, g10, g12, g19, d23859, d23843, d23819, d23970, g37, g38, g39, d22350, g40, g41, g42, g43, g44, g45, g57, g58, g59, g60, g61, g62, d22360, g66, g67, g68, g69, g70, g71, d22346, g72, g73, d23914]
        · have f24085 : (x 1 3).toNat = 1 := by rw [h22384]; rfl
          have d24086 : (x 4 12).toNat = 0 := by
            have r24087 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24088 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e24089 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b24090 := hb (x 1 3)
            have b24091 := hb (x 2 2)
            have b24092 := hb (x 3 13)
            have b24093 := hb (x 4 12)
            clear * - r24087 e24088 e24089 b24090 b24091 b24092 b24093 f24085
            omega
          have d24094 : (x 4 1 && x 4 12).toNat = 0 := by
            have r24095 := hand2 (x 4 1) (x 4 12)
            have b24096 := hb (x 4 12)
            have b24097 := hb (x 4 1 && x 4 12)
            clear * - r24095 b24096 b24097 d24086
            omega
          have d24098 : (x 4 4).toNat = 0 := by
            have r24099 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b24100 := hb (x 4 4)
            have b24101 := hb (x 4 12)
            clear * - r24099 b24100 b24101 d24086
            omega
          have d24102 : (x 3 13).toNat = 0 := by
            have r24103 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24104 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e24105 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b24106 := hb (x 1 3)
            have b24107 := hb (x 2 2)
            have b24108 := hb (x 3 13)
            have b24109 := hb (x 4 12)
            clear * - r24103 e24104 e24105 b24106 b24107 b24108 b24109 d24086 f24085
            omega
          have d24110 : (x 3 2 && x 3 13).toNat = 0 := by
            have r24111 := hand2 (x 3 2) (x 3 13)
            have b24112 := hb (x 3 13)
            have b24113 := hb (x 3 2 && x 3 13)
            clear * - r24111 b24112 b24113 d24102
            omega
          have d24114 : (x 2 1 && x 2 14).toNat = 1 := by
            have r24115 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24116 := hb (x 1 2)
            have b24117 := hb (x 3 13)
            have b24118 := hb (x 2 1 && x 2 14)
            clear * - r24115 b24116 b24117 b24118 d24102 g20
            omega
          have d24119 : (x 2 1).toNat = 1 := by
            have r24120 := hand1 (x 2 1) (x 2 14)
            have b24121 := hb (x 2 1)
            have b24122 := hb (x 2 1 && x 2 14)
            clear * - r24120 b24121 b24122 d24114
            omega
          have d24123 : (x 3 14).toNat = 0 := by
            have r24124 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24125 := hb (x 2 1)
            have b24126 := hb (x 3 14)
            clear * - r24124 b24125 b24126 d24119
            omega
          have d24127 : (x 3 1 && x 3 14).toNat = 0 := by
            have r24128 := hand2 (x 3 1) (x 3 14)
            have b24129 := hb (x 3 14)
            have b24130 := hb (x 3 1 && x 3 14)
            clear * - r24128 b24129 b24130 d24123
            omega
          have d24131 : (x 3 2).toNat = 0 := by
            have r24132 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b24133 := hb (x 3 2)
            have b24134 := hb (x 3 14)
            clear * - r24132 b24133 b24134 d24123
            omega
          have d24135 : (x 2 2).toNat = 0 := by
            have r24136 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24137 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e24138 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b24139 := hb (x 1 3)
            have b24140 := hb (x 2 2)
            have b24141 := hb (x 3 13)
            have b24142 := hb (x 4 12)
            clear * - r24136 e24137 e24138 b24139 b24140 b24141 b24142 d24086 d24102 f24085
            omega
          have d24143 : (x 4 13).toNat = 1 := by
            have r24144 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24145 := hb (x 2 2)
            have b24146 := hb (x 4 13)
            have b24147 := hb (x 3 1 && x 3 14)
            clear * - r24144 b24145 b24146 b24147 d24127 d24135
            omega
          have d24148 : (x 4 1).toNat = 1 := by
            have r24149 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
            have b24150 := hb (x 4 1)
            have b24151 := hb (x 4 13)
            clear * - r24149 b24150 b24151 d24143
            omega
          have d24152 : (x 5 14).toNat = 0 := by
            have r24153 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24154 := hb (x 4 1)
            have b24155 := hb (x 5 14)
            clear * - r24153 b24154 b24155 d24148
            omega
          have d24156 : (x 5 3 && x 5 14).toNat = 0 := by
            have r24157 := hand2 (x 5 3) (x 5 14)
            have b24158 := hb (x 5 14)
            have b24159 := hb (x 5 3 && x 5 14)
            clear * - r24157 b24158 b24159 d24152
            omega
          have d24160 : (x 5 2).toNat = 0 := by
            have r24161 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b24162 := hb (x 5 2)
            have b24163 := hb (x 5 14)
            clear * - r24161 b24162 b24163 d24152
            omega
          have d24164 : (x 5 12).toNat = 0 := by
            have r24165 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24166 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e24167 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b24168 := hb (x 2 3)
            have b24169 := hb (x 3 2)
            have b24170 := hb (x 4 13)
            have b24171 := hb (x 5 12)
            clear * - r24165 e24166 e24167 b24168 b24169 b24170 b24171 d24143 d24131
            omega
          have d24172 : (x 5 4).toNat = 0 := by
            have r24173 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b24174 := hb (x 5 4)
            have b24175 := hb (x 5 12)
            clear * - r24173 b24174 b24175 d24164
            omega
          have d24176 : (x 2 3).toNat = 0 := by
            have r24177 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24178 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e24179 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b24180 := hb (x 2 3)
            have b24181 := hb (x 3 2)
            have b24182 := hb (x 4 13)
            have b24183 := hb (x 5 12)
            clear * - r24177 e24178 e24179 b24180 b24181 b24182 b24183 d24164 d24143 d24131
            omega
          have d24184 : (x 2 3 && x 2 14).toNat = 0 := by
            have r24185 := hand1 (x 2 3) (x 2 14)
            have b24186 := hb (x 2 3)
            have b24187 := hb (x 2 3 && x 2 14)
            clear * - r24185 b24186 b24187 d24176
            omega
          have d24188 : (x 5 11).toNat = 1 := by
            have r24189 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24190 := hb (x 1 4)
            have b24191 := hb (x 5 11)
            have b24192 := hb (x 4 1 && x 4 12)
            have b24193 := hb (x 3 2 && x 3 13)
            have b24194 := hb (x 2 3 && x 2 14)
            clear * - r24189 b24190 b24191 b24192 b24193 b24194 d24094 d24110 d24184 g21
            omega
          have d24195 : (x 5 3).toNat = 1 := by
            have r24196 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
            have b24197 := hb (x 5 3)
            have b24198 := hb (x 5 11)
            clear * - r24196 b24197 b24198 d24188
            omega
          have d24199 : (x 8 12).toNat = 0 := by
            have r24200 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24201 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e24202 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b24203 := hb (x 5 3)
            have b24204 := hb (x 6 2)
            have b24205 := hb (x 7 13)
            have b24206 := hb (x 8 12)
            clear * - r24200 e24201 e24202 b24203 b24204 b24205 b24206 d24195
            omega
          have d24207 : (x 8 1 && x 8 12).toNat = 0 := by
            have r24208 := hand2 (x 8 1) (x 8 12)
            have b24209 := hb (x 8 12)
            have b24210 := hb (x 8 1 && x 8 12)
            clear * - r24208 b24209 b24210 d24199
            omega
          have d24211 : (x 8 4).toNat = 0 := by
            have r24212 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
            have b24213 := hb (x 8 4)
            have b24214 := hb (x 8 12)
            clear * - r24212 b24213 b24214 d24199
            omega
          have d24215 : (x 7 13).toNat = 0 := by
            have r24216 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24217 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e24218 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b24219 := hb (x 5 3)
            have b24220 := hb (x 6 2)
            have b24221 := hb (x 7 13)
            have b24222 := hb (x 8 12)
            clear * - r24216 e24217 e24218 b24219 b24220 b24221 b24222 d24199 d24195
            omega
          have d24223 : (x 7 2 && x 7 13).toNat = 0 := by
            have r24224 := hand2 (x 7 2) (x 7 13)
            have b24225 := hb (x 7 13)
            have b24226 := hb (x 7 2 && x 7 13)
            clear * - r24224 b24225 b24226 d24215
            omega
          have d24227 : (x 6 1 && x 6 14).toNat = 1 := by
            have r24228 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24229 := hb (x 5 2)
            have b24230 := hb (x 7 13)
            have b24231 := hb (x 6 1 && x 6 14)
            clear * - r24228 b24229 b24230 b24231 d24215 d24160
            omega
          have d24232 : (x 6 1).toNat = 1 := by
            have r24233 := hand1 (x 6 1) (x 6 14)
            have b24234 := hb (x 6 1)
            have b24235 := hb (x 6 1 && x 6 14)
            clear * - r24233 b24234 b24235 d24227
            omega
          have d24236 : (x 7 14).toNat = 0 := by
            have r24237 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24238 := hb (x 6 1)
            have b24239 := hb (x 7 14)
            clear * - r24237 b24238 b24239 d24232
            omega
          have d24240 : (x 7 1 && x 7 14).toNat = 0 := by
            have r24241 := hand2 (x 7 1) (x 7 14)
            have b24242 := hb (x 7 14)
            have b24243 := hb (x 7 1 && x 7 14)
            clear * - r24241 b24242 b24243 d24236
            omega
          have d24244 : (x 7 2).toNat = 0 := by
            have r24245 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b24246 := hb (x 7 2)
            have b24247 := hb (x 7 14)
            clear * - r24245 b24246 b24247 d24236
            omega
          have d24248 : (x 6 2).toNat = 0 := by
            have r24249 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24250 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e24251 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b24252 := hb (x 5 3)
            have b24253 := hb (x 6 2)
            have b24254 := hb (x 7 13)
            have b24255 := hb (x 8 12)
            clear * - r24249 e24250 e24251 b24252 b24253 b24254 b24255 d24199 d24215 d24195
            omega
          have d24256 : (x 6 2 && x 6 13).toNat = 0 := by
            have r24257 := hand1 (x 6 2) (x 6 13)
            have b24258 := hb (x 6 2)
            have b24259 := hb (x 6 2 && x 6 13)
            clear * - r24257 b24258 b24259 d24248
            omega
          have d24260 : (x 8 13).toNat = 1 := by
            have r24261 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24262 := hb (x 6 2)
            have b24263 := hb (x 8 13)
            have b24264 := hb (x 7 1 && x 7 14)
            clear * - r24261 b24262 b24263 b24264 d24240 d24248
            omega
          have d24265 : (x 8 1).toNat = 1 := by
            have r24266 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
            have b24267 := hb (x 8 1)
            have b24268 := hb (x 8 13)
            clear * - r24266 b24267 b24268 d24260
            omega
          have d24269 : (x 9 14).toNat = 0 := by
            have r24270 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24271 := hb (x 8 1)
            have b24272 := hb (x 9 14)
            clear * - r24270 b24271 b24272 d24265
            omega
          have d24273 : (x 9 3 && x 9 14).toNat = 0 := by
            have r24274 := hand2 (x 9 3) (x 9 14)
            have b24275 := hb (x 9 14)
            have b24276 := hb (x 9 3 && x 9 14)
            clear * - r24274 b24275 b24276 d24269
            omega
          have d24277 : (x 9 2).toNat = 0 := by
            have r24278 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
            have b24279 := hb (x 9 2)
            have b24280 := hb (x 9 14)
            clear * - r24278 b24279 b24280 d24269
            omega
          have d24281 : (x 9 12).toNat = 0 := by
            have r24282 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24283 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e24284 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b24285 := hb (x 6 3)
            have b24286 := hb (x 7 2)
            have b24287 := hb (x 8 13)
            have b24288 := hb (x 9 12)
            clear * - r24282 e24283 e24284 b24285 b24286 b24287 b24288 d24260 d24244
            omega
          have d24289 : (x 9 4).toNat = 0 := by
            have r24290 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
            have b24291 := hb (x 9 4)
            have b24292 := hb (x 9 12)
            clear * - r24290 b24291 b24292 d24281
            omega
          have d24293 : (x 6 3).toNat = 0 := by
            have r24294 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24295 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e24296 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b24297 := hb (x 6 3)
            have b24298 := hb (x 7 2)
            have b24299 := hb (x 8 13)
            have b24300 := hb (x 9 12)
            clear * - r24294 e24295 e24296 b24297 b24298 b24299 b24300 d24281 d24260 d24244
            omega
          have d24301 : (x 6 3 && x 6 14).toNat = 0 := by
            have r24302 := hand1 (x 6 3) (x 6 14)
            have b24303 := hb (x 6 3)
            have b24304 := hb (x 6 3 && x 6 14)
            clear * - r24302 b24303 b24304 d24293
            omega
          have d24305 : (x 9 11).toNat = 1 := by
            have r24306 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24307 := hb (x 5 4)
            have b24308 := hb (x 9 11)
            have b24309 := hb (x 8 1 && x 8 12)
            have b24310 := hb (x 7 2 && x 7 13)
            have b24311 := hb (x 6 3 && x 6 14)
            clear * - r24306 b24307 b24308 b24309 b24310 b24311 d24207 d24223 d24301 d24172
            omega
          have d24312 : (x 9 3).toNat = 1 := by
            have r24313 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
            have b24314 := hb (x 9 3)
            have b24315 := hb (x 9 11)
            clear * - r24313 b24314 b24315 d24305
            omega
          have d24316 : (x 12 12).toNat = 0 := by
            have r24317 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24318 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e24319 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b24320 := hb (x 9 3)
            have b24321 := hb (x 10 2)
            have b24322 := hb (x 11 13)
            have b24323 := hb (x 12 12)
            clear * - r24317 e24318 e24319 b24320 b24321 b24322 b24323 d24312
            omega
          have d24324 : (x 12 1 && x 12 12).toNat = 0 := by
            have r24325 := hand2 (x 12 1) (x 12 12)
            have b24326 := hb (x 12 12)
            have b24327 := hb (x 12 1 && x 12 12)
            clear * - r24325 b24326 b24327 d24316
            omega
          have d24328 : (x 12 4).toNat = 0 := by
            have r24329 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
            have b24330 := hb (x 12 4)
            have b24331 := hb (x 12 12)
            clear * - r24329 b24330 b24331 d24316
            omega
          have d24332 : (x 11 13).toNat = 0 := by
            have r24333 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24334 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e24335 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b24336 := hb (x 9 3)
            have b24337 := hb (x 10 2)
            have b24338 := hb (x 11 13)
            have b24339 := hb (x 12 12)
            clear * - r24333 e24334 e24335 b24336 b24337 b24338 b24339 d24316 d24312
            omega
          have d24340 : (x 11 2 && x 11 13).toNat = 0 := by
            have r24341 := hand2 (x 11 2) (x 11 13)
            have b24342 := hb (x 11 13)
            have b24343 := hb (x 11 2 && x 11 13)
            clear * - r24341 b24342 b24343 d24332
            omega
          have d24344 : (x 10 1 && x 10 14).toNat = 1 := by
            have r24345 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24346 := hb (x 9 2)
            have b24347 := hb (x 11 13)
            have b24348 := hb (x 10 1 && x 10 14)
            clear * - r24345 b24346 b24347 b24348 d24332 d24277
            omega
          have d24349 : (x 10 14).toNat = 1 := by
            have r24350 := hand2 (x 10 1) (x 10 14)
            have b24351 := hb (x 10 14)
            have b24352 := hb (x 10 1 && x 10 14)
            clear * - r24350 b24351 b24352 d24344
            omega
          have d24353 : (x 9 1).toNat = 0 := by
            have r24354 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24355 := hb (x 9 1)
            have b24356 := hb (x 10 14)
            clear * - r24354 b24355 b24356 d24349
            omega
          have d24357 : (x 9 13).toNat = 0 := by
            have r24358 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
            have b24359 := hb (x 9 1)
            have b24360 := hb (x 9 13)
            clear * - r24358 b24359 b24360 d24353
            omega
          have d24361 : (x 8 1 && x 8 14).toNat = 1 := by
            have r24362 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24363 := hb (x 7 2)
            have b24364 := hb (x 9 13)
            have b24365 := hb (x 8 1 && x 8 14)
            clear * - r24362 b24363 b24364 b24365 d24357 d24244
            omega
          have d24366 : (x 8 14).toNat = 1 := by
            have r24367 := hand2 (x 8 1) (x 8 14)
            have b24368 := hb (x 8 14)
            have b24369 := hb (x 8 1 && x 8 14)
            clear * - r24367 b24368 b24369 d24361
            omega
          have d24370 : (x 7 1).toNat = 0 := by
            have r24371 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24372 := hb (x 7 1)
            have b24373 := hb (x 8 14)
            clear * - r24371 b24372 b24373 d24366
            omega
          have d24374 : (x 7 1 && x 7 12).toNat = 0 := by
            have r24375 := hand1 (x 7 1) (x 7 12)
            have b24376 := hb (x 7 1)
            have b24377 := hb (x 7 1 && x 7 12)
            clear * - r24375 b24376 b24377 d24370
            omega
          have d24378 : (x 8 11).toNat = 1 := by
            have r24379 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24380 := hb (x 4 4)
            have b24381 := hb (x 8 11)
            have b24382 := hb (x 7 1 && x 7 12)
            have b24383 := hb (x 6 2 && x 6 13)
            have b24384 := hb (x 5 3 && x 5 14)
            clear * - r24379 b24380 b24381 b24382 b24383 b24384 d24374 d24256 d24156 d24098
            omega
          have d24385 : (x 8 3).toNat = 1 := by
            have r24386 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
            have b24387 := hb (x 8 3)
            have b24388 := hb (x 8 11)
            clear * - r24386 b24387 b24388 d24378
            omega
          have d24389 : (x 11 12).toNat = 0 := by
            have r24390 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24391 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e24392 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b24393 := hb (x 8 3)
            have b24394 := hb (x 9 2)
            have b24395 := hb (x 10 13)
            have b24396 := hb (x 11 12)
            clear * - r24390 e24391 e24392 b24393 b24394 b24395 b24396 d24277 d24385
            omega
          have d24397 : (x 11 1 && x 11 12).toNat = 0 := by
            have r24398 := hand2 (x 11 1) (x 11 12)
            have b24399 := hb (x 11 12)
            have b24400 := hb (x 11 1 && x 11 12)
            clear * - r24398 b24399 b24400 d24389
            omega
          have d24401 : (x 10 13).toNat = 0 := by
            have r24402 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24403 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e24404 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b24405 := hb (x 8 3)
            have b24406 := hb (x 9 2)
            have b24407 := hb (x 10 13)
            have b24408 := hb (x 11 12)
            clear * - r24402 e24403 e24404 b24405 b24406 b24407 b24408 d24389 d24277 d24385
            omega
          have d24409 : (x 10 2 && x 10 13).toNat = 0 := by
            have r24410 := hand2 (x 10 2) (x 10 13)
            have b24411 := hb (x 10 13)
            have b24412 := hb (x 10 2 && x 10 13)
            clear * - r24410 b24411 b24412 d24401
            omega
          have d24413 : (x 12 11).toNat = 1 := by
            have r24414 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24415 := hb (x 8 4)
            have b24416 := hb (x 12 11)
            have b24417 := hb (x 11 1 && x 11 12)
            have b24418 := hb (x 10 2 && x 10 13)
            have b24419 := hb (x 9 3 && x 9 14)
            clear * - r24414 b24415 b24416 b24417 b24418 b24419 d24397 d24409 d24273 d24211
            omega
          have d24420 : (x 12 3).toNat = 1 := by
            have r24421 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
            have b24422 := hb (x 12 3)
            have b24423 := hb (x 12 11)
            clear * - r24421 b24422 b24423 d24413
            omega
          have d24424 : (x 15 12).toNat = 0 := by
            have r24425 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24426 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e24427 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b24428 := hb (x 12 3)
            have b24429 := hb (x 13 2)
            have b24430 := hb (x 14 13)
            have b24431 := hb (x 15 12)
            clear * - r24425 e24426 e24427 b24428 b24429 b24430 b24431 d24420
            omega
          have d24432 : (x 15 1 && x 15 12).toNat = 0 := by
            have r24433 := hand2 (x 15 1) (x 15 12)
            have b24434 := hb (x 15 12)
            have b24435 := hb (x 15 1 && x 15 12)
            clear * - r24433 b24434 b24435 d24424
            omega
          have d24436 : (x 14 13).toNat = 0 := by
            have r24437 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24438 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e24439 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b24440 := hb (x 12 3)
            have b24441 := hb (x 13 2)
            have b24442 := hb (x 14 13)
            have b24443 := hb (x 15 12)
            clear * - r24437 e24438 e24439 b24440 b24441 b24442 b24443 d24424 d24420
            omega
          have d24444 : (x 14 2 && x 14 13).toNat = 0 := by
            have r24445 := hand2 (x 14 2) (x 14 13)
            have b24446 := hb (x 14 13)
            have b24447 := hb (x 14 2 && x 14 13)
            clear * - r24445 b24446 b24447 d24436
            omega
          have d24448 : (x 13 2).toNat = 0 := by
            have r24449 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24450 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e24451 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b24452 := hb (x 12 3)
            have b24453 := hb (x 13 2)
            have b24454 := hb (x 14 13)
            have b24455 := hb (x 15 12)
            clear * - r24449 e24450 e24451 b24452 b24453 b24454 b24455 d24424 d24436 d24420
            omega
          have d24456 : (x 10 1).toNat = 1 := by
            have r24457 := hand1 (x 10 1) (x 10 14)
            have b24458 := hb (x 10 1)
            have b24459 := hb (x 10 1 && x 10 14)
            clear * - r24457 b24458 b24459 d24344
            omega
          have d24460 : (x 11 14).toNat = 0 := by
            have r24461 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24462 := hb (x 10 1)
            have b24463 := hb (x 11 14)
            clear * - r24461 b24462 b24463 d24456
            omega
          have d24464 : (x 11 1 && x 11 14).toNat = 0 := by
            have r24465 := hand2 (x 11 1) (x 11 14)
            have b24466 := hb (x 11 14)
            have b24467 := hb (x 11 1 && x 11 14)
            clear * - r24465 b24466 b24467 d24460
            omega
          have d24468 : (x 11 2).toNat = 0 := by
            have r24469 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
            have b24470 := hb (x 11 2)
            have b24471 := hb (x 11 14)
            clear * - r24469 b24470 b24471 d24460
            omega
          have d24472 : (x 10 2).toNat = 0 := by
            have r24473 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24474 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e24475 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b24476 := hb (x 9 3)
            have b24477 := hb (x 10 2)
            have b24478 := hb (x 11 13)
            have b24479 := hb (x 12 12)
            clear * - r24473 e24474 e24475 b24476 b24477 b24478 b24479 d24316 d24332 d24312
            omega
          have d24480 : (x 12 13).toNat = 1 := by
            have r24481 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24482 := hb (x 10 2)
            have b24483 := hb (x 12 13)
            have b24484 := hb (x 11 1 && x 11 14)
            clear * - r24481 b24482 b24483 b24484 d24464 d24472
            omega
          have d24485 : (x 12 1).toNat = 1 := by
            have r24486 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
            have b24487 := hb (x 12 1)
            have b24488 := hb (x 12 13)
            clear * - r24486 b24487 b24488 d24480
            omega
          have d24489 : (x 13 14).toNat = 0 := by
            have r24490 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24491 := hb (x 12 1)
            have b24492 := hb (x 13 14)
            clear * - r24490 b24491 b24492 d24485
            omega
          have d24493 : (x 13 1 && x 13 14).toNat = 0 := by
            have r24494 := hand2 (x 13 1) (x 13 14)
            have b24495 := hb (x 13 14)
            have b24496 := hb (x 13 1 && x 13 14)
            clear * - r24494 b24495 b24496 d24489
            omega
          have d24497 : (x 12 2).toNat = 1 := by
            have r24498 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24499 := hb (x 12 2)
            have b24500 := hb (x 14 13)
            have b24501 := hb (x 13 1 && x 13 14)
            clear * - r24498 b24499 b24500 b24501 d24436 d24493
            omega
          have d24502 : (x 14 12).toNat = 0 := by
            have r24503 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24504 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e24505 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b24506 := hb (x 11 3)
            have b24507 := hb (x 12 2)
            have b24508 := hb (x 13 13)
            have b24509 := hb (x 14 12)
            clear * - r24503 e24504 e24505 b24506 b24507 b24508 b24509 d24497
            omega
          have d24510 : (x 14 4).toNat = 0 := by
            have r24511 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
            have b24512 := hb (x 14 4)
            have b24513 := hb (x 14 12)
            clear * - r24511 b24512 b24513 d24502
            omega
          have d24514 : (x 14 4 && x 14 14).toNat = 0 := by
            have r24515 := hand1 (x 14 4) (x 14 14)
            have b24516 := hb (x 14 4)
            have b24517 := hb (x 14 4 && x 14 14)
            clear * - r24515 b24516 b24517 d24510
            omega
          have d24518 : (x 13 13).toNat = 0 := by
            have r24519 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24520 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e24521 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b24522 := hb (x 11 3)
            have b24523 := hb (x 12 2)
            have b24524 := hb (x 13 13)
            have b24525 := hb (x 14 12)
            clear * - r24519 e24520 e24521 b24522 b24523 b24524 b24525 d24502 d24497
            omega
          have d24526 : (x 13 5).toNat = 0 := by
            have r24527 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
            have b24528 := hb (x 13 5)
            have b24529 := hb (x 13 13)
            clear * - r24527 b24528 b24529 d24518
            omega
          have d24530 : (x 13 3 && x 13 14).toNat = 0 := by
            have r24531 := hand2 (x 13 3) (x 13 14)
            have b24532 := hb (x 13 14)
            have b24533 := hb (x 13 3 && x 13 14)
            clear * - r24531 b24532 b24533 d24489
            omega
          have d24534 : (x 16 11).toNat = 1 := by
            have r24535 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24536 := hb (x 12 4)
            have b24537 := hb (x 16 11)
            have b24538 := hb (x 15 1 && x 15 12)
            have b24539 := hb (x 14 2 && x 14 13)
            have b24540 := hb (x 13 3 && x 13 14)
            clear * - r24535 b24536 b24537 b24538 b24539 b24540 d24432 d24444 d24530 d24328
            omega
          have d24541 : (x 16 3).toNat = 1 := by
            have r24542 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
            have b24543 := hb (x 16 3)
            have b24544 := hb (x 16 11)
            clear * - r24542 b24543 b24544 d24534
            omega
          have d24545 : (x 19 12).toNat = 0 := by
            have r24546 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24547 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e24548 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b24549 := hb (x 16 3)
            have b24550 := hb (x 17 2)
            have b24551 := hb (x 18 13)
            have b24552 := hb (x 19 12)
            clear * - r24546 e24547 e24548 b24549 b24550 b24551 b24552 d24541
            omega
          have d24553 : (x 18 13).toNat = 0 := by
            have r24554 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24555 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e24556 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b24557 := hb (x 16 3)
            have b24558 := hb (x 17 2)
            have b24559 := hb (x 18 13)
            have b24560 := hb (x 19 12)
            clear * - r24554 e24555 e24556 b24557 b24558 b24559 b24560 d24545 d24541
            omega
          have d24561 : (x 17 2).toNat = 0 := by
            have r24562 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24563 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e24564 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b24565 := hb (x 16 3)
            have b24566 := hb (x 17 2)
            have b24567 := hb (x 18 13)
            have b24568 := hb (x 19 12)
            clear * - r24562 e24563 e24564 b24565 b24566 b24567 b24568 d24545 d24553 d24541
            omega
          have d24569 : (x 13 12).toNat = 0 := by
            have r24570 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24571 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e24572 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b24573 := hb (x 10 3)
            have b24574 := hb (x 11 2)
            have b24575 := hb (x 12 13)
            have b24576 := hb (x 13 12)
            clear * - r24570 e24571 e24572 b24573 b24574 b24575 b24576 d24480 d24468
            omega
          have d24577 : (x 13 4).toNat = 0 := by
            have r24578 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
            have b24579 := hb (x 13 4)
            have b24580 := hb (x 13 12)
            clear * - r24578 b24579 b24580 d24569
            omega
          have d24581 : (x 10 3).toNat = 0 := by
            have r24582 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24583 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e24584 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b24585 := hb (x 10 3)
            have b24586 := hb (x 11 2)
            have b24587 := hb (x 12 13)
            have b24588 := hb (x 13 12)
            clear * - r24582 e24583 e24584 b24585 b24586 b24587 b24588 d24569 d24480 d24468
            omega
          have d24589 : (x 10 3 && x 10 14).toNat = 0 := by
            have r24590 := hand1 (x 10 3) (x 10 14)
            have b24591 := hb (x 10 3)
            have b24592 := hb (x 10 3 && x 10 14)
            clear * - r24590 b24591 b24592 d24581
            omega
          have d24593 : (x 13 11).toNat = 1 := by
            have r24594 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24595 := hb (x 9 4)
            have b24596 := hb (x 13 11)
            have b24597 := hb (x 12 1 && x 12 12)
            have b24598 := hb (x 11 2 && x 11 13)
            have b24599 := hb (x 10 3 && x 10 14)
            clear * - r24594 b24595 b24596 b24597 b24598 b24599 d24324 d24340 d24589 d24289
            omega
          have d24600 : (x 13 3).toNat = 1 := by
            have r24601 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
            have b24602 := hb (x 13 3)
            have b24603 := hb (x 13 11)
            clear * - r24601 b24602 b24603 d24593
            omega
          have d24604 : (x 16 12).toNat = 0 := by
            have r24605 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24606 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e24607 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b24608 := hb (x 13 3)
            have b24609 := hb (x 14 2)
            have b24610 := hb (x 15 13)
            have b24611 := hb (x 16 12)
            clear * - r24605 e24606 e24607 b24608 b24609 b24610 b24611 d24600
            omega
          have d24612 : (x 16 1 && x 16 12).toNat = 0 := by
            have r24613 := hand2 (x 16 1) (x 16 12)
            have b24614 := hb (x 16 12)
            have b24615 := hb (x 16 1 && x 16 12)
            clear * - r24613 b24614 b24615 d24604
            omega
          have d24616 : (x 16 2 && x 16 12).toNat = 0 := by
            have r24617 := hand2 (x 16 2) (x 16 12)
            have b24618 := hb (x 16 12)
            have b24619 := hb (x 16 2 && x 16 12)
            clear * - r24617 b24618 b24619 d24604
            omega
          have d24620 : (x 15 13).toNat = 0 := by
            have r24621 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24622 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e24623 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b24624 := hb (x 13 3)
            have b24625 := hb (x 14 2)
            have b24626 := hb (x 15 13)
            have b24627 := hb (x 16 12)
            clear * - r24621 e24622 e24623 b24624 b24625 b24626 b24627 d24604 d24600
            omega
          have d24628 : (x 15 2 && x 15 13).toNat = 0 := by
            have r24629 := hand2 (x 15 2) (x 15 13)
            have b24630 := hb (x 15 13)
            have b24631 := hb (x 15 2 && x 15 13)
            clear * - r24629 b24630 b24631 d24620
            omega
          have d24632 : (x 15 3 && x 15 13).toNat = 0 := by
            have r24633 := hand2 (x 15 3) (x 15 13)
            have b24634 := hb (x 15 13)
            have b24635 := hb (x 15 3 && x 15 13)
            clear * - r24633 b24634 b24635 d24620
            omega
          have d24636 : (x 14 1 && x 14 14).toNat = 1 := by
            have r24637 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24638 := hb (x 13 2)
            have b24639 := hb (x 15 13)
            have b24640 := hb (x 14 1 && x 14 14)
            clear * - r24637 b24638 b24639 b24640 d24620 d24448
            omega
          have d24641 : (x 14 1).toNat = 1 := by
            have r24642 := hand1 (x 14 1) (x 14 14)
            have b24643 := hb (x 14 1)
            have b24644 := hb (x 14 1 && x 14 14)
            clear * - r24642 b24643 b24644 d24636
            omega
          have d24645 : (x 15 14).toNat = 0 := by
            have r24646 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24647 := hb (x 14 1)
            have b24648 := hb (x 15 14)
            clear * - r24646 b24647 b24648 d24641
            omega
          have d24649 : (x 15 1 && x 15 14).toNat = 0 := by
            have r24650 := hand2 (x 15 1) (x 15 14)
            have b24651 := hb (x 15 14)
            have b24652 := hb (x 15 1 && x 15 14)
            clear * - r24650 b24651 b24652 d24645
            omega
          have d24653 : (x 15 2).toNat = 0 := by
            have r24654 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
            have b24655 := hb (x 15 2)
            have b24656 := hb (x 15 14)
            clear * - r24654 b24655 b24656 d24645
            omega
          have d24657 : (x 14 2).toNat = 0 := by
            have r24658 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24659 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e24660 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b24661 := hb (x 13 3)
            have b24662 := hb (x 14 2)
            have b24663 := hb (x 15 13)
            have b24664 := hb (x 16 12)
            clear * - r24658 e24659 e24660 b24661 b24662 b24663 b24664 d24604 d24620 d24600
            omega
          have d24665 : (x 16 13).toNat = 1 := by
            have r24666 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24667 := hb (x 14 2)
            have b24668 := hb (x 16 13)
            have b24669 := hb (x 15 1 && x 15 14)
            clear * - r24666 b24667 b24668 b24669 d24649 d24657
            omega
          have d24670 : (x 17 12).toNat = 0 := by
            have r24671 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24672 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e24673 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b24674 := hb (x 14 3)
            have b24675 := hb (x 15 2)
            have b24676 := hb (x 16 13)
            have b24677 := hb (x 17 12)
            clear * - r24671 e24672 e24673 b24674 b24675 b24676 b24677 d24665 d24653
            omega
          have d24678 : (x 14 3).toNat = 0 := by
            have r24679 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24680 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e24681 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b24682 := hb (x 14 3)
            have b24683 := hb (x 15 2)
            have b24684 := hb (x 16 13)
            have b24685 := hb (x 17 12)
            clear * - r24679 e24680 e24681 b24682 b24683 b24684 b24685 d24670 d24665 d24653
            omega
          have d24686 : (x 14 3 && x 14 14).toNat = 0 := by
            have r24687 := hand1 (x 14 3) (x 14 14)
            have b24688 := hb (x 14 3)
            have b24689 := hb (x 14 3 && x 14 14)
            clear * - r24687 b24688 b24689 d24678
            omega
          have d24690 : (x 17 11).toNat = 1 := by
            have r24691 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24692 := hb (x 13 4)
            have b24693 := hb (x 17 11)
            have b24694 := hb (x 16 1 && x 16 12)
            have b24695 := hb (x 15 2 && x 15 13)
            have b24696 := hb (x 14 3 && x 14 14)
            clear * - r24691 b24692 b24693 b24694 b24695 b24696 d24612 d24628 d24686 d24577
            omega
          have d24697 : (x 17 3).toNat = 1 := by
            have r24698 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
            have b24699 := hb (x 17 3)
            have b24700 := hb (x 17 11)
            clear * - r24698 b24699 b24700 d24690
            omega
          have d24701 : (x 20 12).toNat = 0 := by
            have r24702 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24703 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e24704 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b24705 := hb (x 17 3)
            have b24706 := hb (x 18 2)
            have b24707 := hb (x 19 13)
            have b24708 := hb (x 20 12)
            clear * - r24702 e24703 e24704 b24705 b24706 b24707 b24708 d24697
            omega
          have d24709 : (x 19 13).toNat = 0 := by
            have r24710 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24711 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e24712 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b24713 := hb (x 17 3)
            have b24714 := hb (x 18 2)
            have b24715 := hb (x 19 13)
            have b24716 := hb (x 20 12)
            clear * - r24710 e24711 e24712 b24713 b24714 b24715 b24716 d24701 d24697
            omega
          have d24717 : (x 18 1 && x 18 14).toNat = 1 := by
            have r24718 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24719 := hb (x 17 2)
            have b24720 := hb (x 19 13)
            have b24721 := hb (x 18 1 && x 18 14)
            clear * - r24718 b24719 b24720 b24721 d24709 d24561
            omega
          have d24722 : (x 18 14).toNat = 1 := by
            have r24723 := hand2 (x 18 1) (x 18 14)
            have b24724 := hb (x 18 14)
            have b24725 := hb (x 18 1 && x 18 14)
            clear * - r24723 b24724 b24725 d24717
            omega
          have d24726 : (x 17 1).toNat = 0 := by
            have r24727 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24728 := hb (x 17 1)
            have b24729 := hb (x 18 14)
            clear * - r24727 b24728 b24729 d24722
            omega
          have d24730 : (x 17 1 && x 17 11).toNat = 0 := by
            have r24731 := hand1 (x 17 1) (x 17 11)
            have b24732 := hb (x 17 1)
            have b24733 := hb (x 17 1 && x 17 11)
            clear * - r24731 b24732 b24733 d24726
            omega
          have d24734 : (x 18 2).toNat = 0 := by
            have r24735 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24736 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e24737 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b24738 := hb (x 17 3)
            have b24739 := hb (x 18 2)
            have b24740 := hb (x 19 13)
            have b24741 := hb (x 20 12)
            clear * - r24735 e24736 e24737 b24738 b24739 b24740 b24741 d24701 d24709 d24697
            omega
          have d24742 : (x 18 10).toNat = 0 := by
            have r24743 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
            have b24744 := hb (x 18 2)
            have b24745 := hb (x 18 10)
            clear * - r24743 b24744 b24745 d24734
            omega
          have r24746 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b24747 := hb (x 13 5)
          have b24748 := hb (x 18 10)
          have b24749 := hb (x 17 1 && x 17 11)
          have b24750 := hb (x 16 2 && x 16 12)
          have b24751 := hb (x 15 3 && x 15 13)
          have b24752 := hb (x 14 4 && x 14 14)
          linarith only [r24746, b24747, b24748, b24749, b24750, b24751, b24752, d24742, d24730, d24616, d24632, d24514, d24526]
      · have f24753 : (x 1 1).toNat = 1 := by rw [h22382]; rfl
        have d24754 : (x 2 14).toNat = 0 := by
          have r24755 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b24756 := hb (x 1 1)
          have b24757 := hb (x 2 14)
          clear * - r24755 b24756 b24757 f24753
          omega
        have d24758 : (x 2 1 && x 2 14).toNat = 0 := by
          have r24759 := hand2 (x 2 1) (x 2 14)
          have b24760 := hb (x 2 14)
          have b24761 := hb (x 2 1 && x 2 14)
          clear * - r24759 b24760 b24761 d24754
          omega
        have d24762 : (x 2 6).toNat = 0 := by
          have r24763 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
          have b24764 := hb (x 2 6)
          have b24765 := hb (x 2 14)
          clear * - r24763 b24764 b24765 d24754
          omega
        have d24766 : (x 2 2 && x 2 6).toNat = 0 := by
          have r24767 := hand2 (x 2 2) (x 2 6)
          have b24768 := hb (x 2 6)
          have b24769 := hb (x 2 2 && x 2 6)
          clear * - r24767 b24768 b24769 d24762
          omega
        have d24770 : (x 2 2).toNat = 0 := by
          have r24771 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b24772 := hb (x 2 2)
          have b24773 := hb (x 2 14)
          clear * - r24771 b24772 b24773 d24754
          omega
        have d24774 : (x 3 13).toNat = 1 := by
          have r24775 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b24776 := hb (x 1 2)
          have b24777 := hb (x 3 13)
          have b24778 := hb (x 2 1 && x 2 14)
          clear * - r24775 b24776 b24777 b24778 d24758 g20
          omega
        have d24779 : (x 3 1).toNat = 1 := by
          have r24780 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b24781 := hb (x 3 1)
          have b24782 := hb (x 3 13)
          clear * - r24780 b24781 b24782 d24774
          omega
        have d24783 : (x 4 12).toNat = 0 := by
          have r24784 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24785 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e24786 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b24787 := hb (x 1 3)
          have b24788 := hb (x 2 2)
          have b24789 := hb (x 3 13)
          have b24790 := hb (x 4 12)
          clear * - r24784 e24785 e24786 b24787 b24788 b24789 b24790 d24774 d24770
          omega
        have d24791 : (x 4 3 && x 4 12).toNat = 0 := by
          have r24792 := hand2 (x 4 3) (x 4 12)
          have b24793 := hb (x 4 12)
          have b24794 := hb (x 4 3 && x 4 12)
          clear * - r24792 b24793 b24794 d24783
          omega
        have d24795 : (x 4 4).toNat = 0 := by
          have r24796 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b24797 := hb (x 4 4)
          have b24798 := hb (x 4 12)
          clear * - r24796 b24797 b24798 d24783
          omega
        have d24799 : (x 1 3).toNat = 0 := by
          have r24800 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e24801 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e24802 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b24803 := hb (x 1 3)
          have b24804 := hb (x 2 2)
          have b24805 := hb (x 3 13)
          have b24806 := hb (x 4 12)
          clear * - r24800 e24801 e24802 b24803 b24804 b24805 b24806 d24783 d24774 d24770
          omega
        have d24807 : (x 1 3 && x 1 7).toNat = 0 := by
          have r24808 := hand1 (x 1 3) (x 1 7)
          have b24809 := hb (x 1 3)
          have b24810 := hb (x 1 3 && x 1 7)
          clear * - r24808 b24809 b24810 d24799
          omega
        have r24811 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24812 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24813 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24814 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e24815 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e24816 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e24817 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e24818 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e24819 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r24820 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24821 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e24822 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have r24823 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24824 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
        have e24825 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
        have r24826 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24827 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24828 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24829 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r24830 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
        have r24831 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have r24832 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have r24833 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
        have r24834 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have r24835 := hand1 (x (-4) 8) (x (-4) 12)
        have r24836 := hand1 (x (-5) 9) (x (-5) 13)
        have r24837 := hand2 (x 1 1) (x 1 7)
        have r24838 := hand1 (x (-4) 6) (x (-4) 12)
        have r24839 := hand1 (x (-5) 7) (x (-5) 13)
        have r24840 := hand1 (x (-6) 8) (x (-6) 14)
        have r24841 := hand2 (x 6 1) (x 6 10)
        have r24842 := hand2 (x 5 2) (x 5 11)
        have r24843 := hand2 (x (-7) 1) (x (-7) 11)
        have r24844 := hand2 (x (-8) 2) (x (-8) 12)
        have r24845 := hand2 (x (-9) 3) (x (-9) 13)
        have r24846 := hand2 (x (-10) 4) (x (-10) 14)
        have r24847 := hand1 (x (-4) 4) (x (-4) 14)
        linarith only [r24811, r24812, r24813, e24814, e24815, e24816, e24817, e24818, e24819, r24820, e24821, e24822, r24823, e24824, e24825, r24826, r24827, r24828, r24829, r24830, r24831, r24832, r24833, r24834, r24835, r24836, r24837, r24838, r24839, r24840, r24841, r24842, r24843, r24844, r24845, r24846, r24847, g0, g2, g6, g7, g14, g15, g19, f24753, d24799, g23, d24770, d24762, d24779, d24795, d24766, d24807, d22368, g27, g28, g29, d22364, g54, g55, g56, d24791, g80, g81, g83, g84, g85]
    · have f24922 : (x 0 9).toNat = 1 := by rw [h22372]; rfl
      have d24923 : (x 1 8).toNat = 0 := by
        have r24924 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24925 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e24926 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e24927 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e24928 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e24929 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e24930 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b24931 := hb (x (-6) 7)
        have b24932 := hb (x (-5) 6)
        have b24933 := hb (x (-4) 5)
        have b24934 := hb (x (-3) 4)
        have b24935 := hb (x (-2) 11)
        have b24936 := hb (x (-1) 10)
        have b24937 := hb (x 0 9)
        have b24938 := hb (x 1 8)
        clear * - r24924 e24925 e24926 e24927 e24928 e24929 e24930 b24931 b24932 b24933 b24934 b24935 b24936 b24937 b24938 f24922 g11 g5
        omega
      have d24939 : (x (-3) 4).toNat = 0 := by
        have r24940 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24941 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e24942 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e24943 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e24944 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e24945 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e24946 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b24947 := hb (x (-6) 7)
        have b24948 := hb (x (-5) 6)
        have b24949 := hb (x (-4) 5)
        have b24950 := hb (x (-3) 4)
        have b24951 := hb (x (-2) 11)
        have b24952 := hb (x (-1) 10)
        have b24953 := hb (x 0 9)
        have b24954 := hb (x 1 8)
        clear * - r24940 e24941 e24942 e24943 e24944 e24945 e24946 b24947 b24948 b24949 b24950 b24951 b24952 b24953 b24954 d24923 f24922 g11 g5
        omega
      have d24955 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
        have r24956 := hand1 (x (-3) 4) (x (-3) 13)
        have b24957 := hb (x (-3) 4)
        have b24958 := hb (x (-3) 4 && x (-3) 13)
        clear * - r24956 b24957 b24958 d24939
        omega
      have d24959 : (x (-4) 5).toNat = 0 := by
        have r24960 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24961 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e24962 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e24963 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e24964 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e24965 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e24966 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b24967 := hb (x (-6) 7)
        have b24968 := hb (x (-5) 6)
        have b24969 := hb (x (-4) 5)
        have b24970 := hb (x (-3) 4)
        have b24971 := hb (x (-2) 11)
        have b24972 := hb (x (-1) 10)
        have b24973 := hb (x 0 9)
        have b24974 := hb (x 1 8)
        clear * - r24960 e24961 e24962 e24963 e24964 e24965 e24966 b24967 b24968 b24969 b24970 b24971 b24972 b24973 b24974 d24923 f24922 g11 g5 d24939
        omega
      have d24975 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
        have r24976 := hand1 (x (-4) 5) (x (-4) 14)
        have b24977 := hb (x (-4) 5)
        have b24978 := hb (x (-4) 5 && x (-4) 14)
        clear * - r24976 b24977 b24978 d24959
        omega
      have d24979 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
        have r24980 := hand1 (x (-4) 5) (x (-4) 12)
        have b24981 := hb (x (-4) 5)
        have b24982 := hb (x (-4) 5 && x (-4) 12)
        clear * - r24980 b24981 b24982 d24959
        omega
      have d24983 : (x (-5) 6).toNat = 0 := by
        have r24984 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24985 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e24986 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e24987 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e24988 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e24989 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e24990 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b24991 := hb (x (-6) 7)
        have b24992 := hb (x (-5) 6)
        have b24993 := hb (x (-4) 5)
        have b24994 := hb (x (-3) 4)
        have b24995 := hb (x (-2) 11)
        have b24996 := hb (x (-1) 10)
        have b24997 := hb (x 0 9)
        have b24998 := hb (x 1 8)
        clear * - r24984 e24985 e24986 e24987 e24988 e24989 e24990 b24991 b24992 b24993 b24994 b24995 b24996 b24997 b24998 d24923 f24922 g11 g5 d24939 d24959
        omega
      have d24999 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
        have r25000 := hand1 (x (-5) 6) (x (-5) 13)
        have b25001 := hb (x (-5) 6)
        have b25002 := hb (x (-5) 6 && x (-5) 13)
        clear * - r25000 b25001 b25002 d24983
        omega
      have d25003 : (x 1 9).toNat = 1 := by
        have r25004 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b25005 := hb (x (-5) 6)
        have b25006 := hb (x 1 9)
        have b25007 := hb (x 0 1 && x 0 10)
        have b25008 := hb (x (-1) 2 && x (-1) 11)
        have b25009 := hb (x (-2) 3 && x (-2) 12)
        have b25010 := hb (x (-3) 4 && x (-3) 13)
        have b25011 := hb (x (-4) 5 && x (-4) 14)
        clear * - r25004 b25005 b25006 b25007 b25008 b25009 b25010 b25011 g77 g78 g79 d24955 d24975 d24983
        omega
      have d25012 : (x 1 1).toNat = 1 := by
        have r25013 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
        have b25014 := hb (x 1 1)
        have b25015 := hb (x 1 9)
        clear * - r25013 b25014 b25015 d25003
        omega
      have d25016 : (x 2 14).toNat = 0 := by
        have r25017 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b25018 := hb (x 1 1)
        have b25019 := hb (x 2 14)
        clear * - r25017 b25018 b25019 d25012
        omega
      have d25020 : (x 2 1 && x 2 14).toNat = 0 := by
        have r25021 := hand2 (x 2 1) (x 2 14)
        have b25022 := hb (x 2 14)
        have b25023 := hb (x 2 1 && x 2 14)
        clear * - r25021 b25022 b25023 d25016
        omega
      have d25024 : (x 3 13).toNat = 1 := by
        have r25025 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b25026 := hb (x 1 2)
        have b25027 := hb (x 3 13)
        have b25028 := hb (x 2 1 && x 2 14)
        clear * - r25025 b25026 b25027 b25028 d25020 g20
        omega
      have d25029 : (x 3 1).toNat = 1 := by
        have r25030 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b25031 := hb (x 3 1)
        have b25032 := hb (x 3 13)
        clear * - r25030 b25031 b25032 d25024
        omega
      have d25033 : (x 4 12).toNat = 0 := by
        have r25034 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e25035 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e25036 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b25037 := hb (x 1 3)
        have b25038 := hb (x 2 2)
        have b25039 := hb (x 3 13)
        have b25040 := hb (x 4 12)
        clear * - r25034 e25035 e25036 b25037 b25038 b25039 b25040 d25024
        omega
      have d25041 : (x 4 3 && x 4 12).toNat = 0 := by
        have r25042 := hand2 (x 4 3) (x 4 12)
        have b25043 := hb (x 4 12)
        have b25044 := hb (x 4 3 && x 4 12)
        clear * - r25042 b25043 b25044 d25033
        omega
      have d25045 : (x 4 4).toNat = 0 := by
        have r25046 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b25047 := hb (x 4 4)
        have b25048 := hb (x 4 12)
        clear * - r25046 b25047 b25048 d25033
        omega
      have d25049 : (x 2 2).toNat = 0 := by
        have r25050 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e25051 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e25052 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b25053 := hb (x 1 3)
        have b25054 := hb (x 2 2)
        have b25055 := hb (x 3 13)
        have b25056 := hb (x 4 12)
        clear * - r25050 e25051 e25052 b25053 b25054 b25055 b25056 d25033 d25024
        omega
      have d25057 : (x 2 2 && x 2 6).toNat = 0 := by
        have r25058 := hand1 (x 2 2) (x 2 6)
        have b25059 := hb (x 2 2)
        have b25060 := hb (x 2 2 && x 2 6)
        clear * - r25058 b25059 b25060 d25049
        omega
      have d25061 : (x 1 3).toNat = 0 := by
        have r25062 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e25063 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e25064 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b25065 := hb (x 1 3)
        have b25066 := hb (x 2 2)
        have b25067 := hb (x 3 13)
        have b25068 := hb (x 4 12)
        clear * - r25062 e25063 e25064 b25065 b25066 b25067 b25068 d25033 d25024 d25049
        omega
      have d25069 : (x 1 3 && x 1 7).toNat = 0 := by
        have r25070 := hand1 (x 1 3) (x 1 7)
        have b25071 := hb (x 1 3)
        have b25072 := hb (x 1 3 && x 1 7)
        clear * - r25070 b25071 b25072 d25061
        omega
      have d25073 : (x 2 6).toNat = 0 := by
        have r25074 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
        have b25075 := hb (x 2 6)
        have b25076 := hb (x 2 14)
        clear * - r25074 b25075 b25076 d25016
        omega
      have d25077 : (x (-6) 7).toNat = 0 := by
        have r25078 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e25079 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e25080 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e25081 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e25082 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e25083 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e25084 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b25085 := hb (x (-6) 7)
        have b25086 := hb (x (-5) 6)
        have b25087 := hb (x (-4) 5)
        have b25088 := hb (x (-3) 4)
        have b25089 := hb (x (-2) 11)
        have b25090 := hb (x (-1) 10)
        have b25091 := hb (x 0 9)
        have b25092 := hb (x 1 8)
        clear * - r25078 e25079 e25080 e25081 e25082 e25083 e25084 b25085 b25086 b25087 b25088 b25089 b25090 b25091 b25092 d24923 f24922 g11 g5 d24939 d24959 d24983
        omega
      have d25093 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
        have r25094 := hand1 (x (-6) 7) (x (-6) 14)
        have b25095 := hb (x (-6) 7)
        have b25096 := hb (x (-6) 7 && x (-6) 14)
        clear * - r25094 b25095 b25096 d25077
        omega
      have r25097 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r25098 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25099 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e25100 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e25101 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e25102 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e25103 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e25104 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have r25105 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25106 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e25107 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e25108 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e25109 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e25110 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e25111 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r25112 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25113 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e25114 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have r25115 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25116 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
      have e25117 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
      have r25118 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r25119 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r25120 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r25121 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r25122 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have r25123 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have r25124 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have r25125 := hand1 (x (-4) 8) (x (-4) 12)
      have r25126 := hand1 (x (-5) 9) (x (-5) 13)
      have r25127 := hand2 (x 6 1) (x 6 10)
      have r25128 := hand2 (x 5 2) (x 5 11)
      have r25129 := hand1 (x (-4) 4) (x (-4) 14)
      have r25130 := hand2 (x (-8) 1) (x (-8) 12)
      have r25131 := hand2 (x (-9) 2) (x (-9) 13)
      have r25132 := hand2 (x (-10) 3) (x (-10) 14)
      linarith only [r25097, r25098, e25099, e25100, e25101, e25102, e25103, e25104, r25105, e25106, e25107, e25108, e25109, e25110, e25111, r25112, e25113, e25114, r25115, e25116, e25117, r25118, r25119, r25120, r25121, r25122, r25123, r25124, r25125, r25126, r25127, r25128, r25129, r25130, r25131, r25132, g0, g2, g7, g15, g19, d25061, g23, d25049, d25073, d25029, d25045, d25057, d25069, d22368, g27, g28, g29, d22356, g63, g64, g65, d24979, d24999, d25093, d25041, g80, g81, g83, g84, g85]
  · have f25198 : (x 0 8).toNat = 1 := by rw [h22354]; rfl
    have d25199 : (x (-4) 4).toNat = 0 := by
      have r25200 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25201 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e25202 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e25203 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e25204 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e25205 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e25206 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b25207 := hb (x (-7) 7)
      have b25208 := hb (x (-6) 6)
      have b25209 := hb (x (-5) 5)
      have b25210 := hb (x (-4) 4)
      have b25211 := hb (x (-3) 11)
      have b25212 := hb (x (-2) 10)
      have b25213 := hb (x (-1) 9)
      have b25214 := hb (x 0 8)
      clear * - r25200 e25201 e25202 e25203 e25204 e25205 e25206 b25207 b25208 b25209 b25210 b25211 b25212 b25213 b25214 f25198 g10 g4 g1
      omega
    have d25215 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
      have r25216 := hand1 (x (-4) 4) (x (-4) 14)
      have b25217 := hb (x (-4) 4)
      have b25218 := hb (x (-4) 4 && x (-4) 14)
      clear * - r25216 b25217 b25218 d25199
      omega
    have d25219 : (x (-5) 5).toNat = 1 := by
      have r25220 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25221 := hb (x (-5) 5)
      have b25222 := hb (x 0 10)
      have b25223 := hb (x (-1) 1 && x (-1) 11)
      have b25224 := hb (x (-2) 2 && x (-2) 12)
      have b25225 := hb (x (-3) 3 && x (-3) 13)
      have b25226 := hb (x (-4) 4 && x (-4) 14)
      clear * - r25220 b25221 b25222 b25223 b25224 b25225 b25226 g19 g83 g84 g85 d25215
      omega
    have r25227 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25228 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e25229 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e25230 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e25231 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e25232 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e25233 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b25234 := hb (x (-7) 7)
    have b25235 := hb (x (-6) 6)
    have b25236 := hb (x (-5) 5)
    have b25237 := hb (x (-4) 4)
    have b25238 := hb (x (-3) 11)
    have b25239 := hb (x (-2) 10)
    have b25240 := hb (x (-1) 9)
    have b25241 := hb (x 0 8)
    linarith only [r25227, e25228, e25229, e25230, e25231, e25232, e25233, b25234, b25235, b25236, b25237, b25238, b25239, b25240, b25241, f25198, g10, g4, g1, d25199, d25219]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b1110 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-2) 7).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-1) 3).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 6).toNat = 0)
    (g9 : (x (-1) 7).toNat = 0)
    (g10 : (x (-1) 9).toNat = 0)
    (g11 : (x (-1) 10).toNat = 0)
    (g12 : (x (-1) 11).toNat = 0)
    (g13 : (x (-1) 13).toNat = 0)
    (g14 : (x 0 2).toNat = 1)
    (g15 : (x 0 4).toNat = 1)
    (g16 : (x 0 5).toNat = 1)
    (g17 : (x 0 6).toNat = 1)
    (g18 : (x 0 7).toNat = 0)
    (g19 : (x 0 10).toNat = 0)
    (g20 : (x 1 2).toNat = 0)
    (g21 : (x 1 4).toNat = 0)
    (g22 : (x 1 5).toNat = 0)
    (g23 : (x 1 6).toNat = 0)
    (g24 : (x 2 4).toNat = 0)
    (g25 : (x 2 5).toNat = 0)
    (g26 : (x 3 4).toNat = 0)
    (g27 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g28 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g29 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g30 : (x 1 4 && x 1 8).toNat = 0)
    (g31 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g32 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g33 : (x 2 4 && x 2 8).toNat = 0)
    (g34 : (x 1 5 && x 1 9).toNat = 0)
    (g35 : (x 0 6 && x 0 10).toNat = 0)
    (g36 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g37 : (x 3 4 && x 3 8).toNat = 0)
    (g38 : (x 2 5 && x 2 9).toNat = 0)
    (g39 : (x 1 6 && x 1 10).toNat = 0)
    (g40 : (x 6 4 && x 6 8).toNat = 0)
    (g41 : (x 5 5 && x 5 9).toNat = 0)
    (g42 : (x 4 6 && x 4 10).toNat = 0)
    (g43 : (x 3 7 && x 3 11).toNat = 0)
    (g44 : (x 2 8 && x 2 12).toNat = 0)
    (g45 : (x 1 9 && x 1 13).toNat = 0)
    (g46 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g47 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g48 : (x 6 3 && x 6 8).toNat = 0)
    (g49 : (x 5 4 && x 5 9).toNat = 0)
    (g50 : (x 4 5 && x 4 10).toNat = 0)
    (g51 : (x 3 6 && x 3 11).toNat = 0)
    (g52 : (x 2 7 && x 2 12).toNat = 0)
    (g53 : (x 1 8 && x 1 13).toNat = 0)
    (g54 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g55 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g56 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g57 : (x 6 2 && x 6 8).toNat = 0)
    (g58 : (x 5 3 && x 5 9).toNat = 0)
    (g59 : (x 4 4 && x 4 10).toNat = 0)
    (g60 : (x 3 5 && x 3 11).toNat = 0)
    (g61 : (x 2 6 && x 2 12).toNat = 0)
    (g62 : (x 1 7 && x 1 13).toNat = 0)
    (g63 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g64 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g65 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g66 : (x 6 1 && x 6 8).toNat = 0)
    (g67 : (x 5 2 && x 5 9).toNat = 0)
    (g68 : (x 4 3 && x 4 10).toNat = 0)
    (g69 : (x 3 4 && x 3 11).toNat = 0)
    (g70 : (x 2 5 && x 2 12).toNat = 0)
    (g71 : (x 1 6 && x 1 13).toNat = 0)
    (g72 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g73 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g74 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g75 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g76 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g77 : (x 0 1 && x 0 10).toNat = 0)
    (g78 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g79 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g80 : (x 3 4 && x 3 13).toNat = 0)
    (g81 : (x 2 5 && x 2 14).toNat = 0)
    (g82 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g83 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g84 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g85 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g86 : (x 2 4 && x 2 14).toNat = 0)
    (g87 : (x 3 4 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b1110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87
