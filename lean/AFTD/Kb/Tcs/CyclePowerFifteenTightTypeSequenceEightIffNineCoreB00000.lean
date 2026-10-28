import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b00000

Topic: combinatorics   Node: 009a6902f8b0

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 54 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b00000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 7).toNat = 0)
    (g1 : (x (-5) 6).toNat = 0)
    (g2 : (x (-4) 5).toNat = 0)
    (g3 : (x (-3) 4).toNat = 0)
    (g4 : (x (-2) 11).toNat = 0)
    (g5 : (x (-1) 10).toNat = 0)
    (g6 : (x 0 1).toNat = 1)
    (g7 : (x 0 2).toNat = 0)
    (g8 : (x 0 3).toNat = 0)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 6).toNat = 0)
    (g11 : (x 0 11).toNat = 0)
    (g12 : (x 1 2).toNat = 0)
    (g13 : (x 1 6).toNat = 0)
    (g14 : (x 1 10).toNat = 0)
    (g15 : (x 2 1).toNat = 1)
    (g16 : (x 3 2).toNat = 0)
    (g17 : (x 3 4).toNat = 0)
    (g18 : (x 3 6).toNat = 0)
    (g19 : (x 0 1 && x 0 2).toNat = 0)
    (g20 : (x (-3) 4 && x (-3) 5).toNat = 0)
    (g21 : (x (-4) 5 && x (-4) 6).toNat = 0)
    (g22 : (x (-5) 6 && x (-5) 7).toNat = 0)
    (g23 : (x (-6) 7 && x (-6) 8).toNat = 0)
    (g24 : (x 1 2 && x 1 6).toNat = 0)
    (g25 : (x 0 3 && x 0 7).toNat = 0)
    (g26 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g27 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g28 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g29 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g30 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g31 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g32 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g33 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g34 : (x 1 1 && x 1 8).toNat = 0)
    (g35 : (x 0 2 && x 0 9).toNat = 0)
    (g36 : (x (-1) 3 && x (-1) 10).toNat = 0)
    (g37 : (x (-2) 4 && x (-2) 11).toNat = 0)
    (g38 : (x 0 1 && x 0 10).toNat = 0)
    (g39 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g40 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g41 : (x 3 3 && x 3 12).toNat = 0)
    (g42 : (x 1 5 && x 1 14).toNat = 0)
    (g43 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g44 : (x 0 1 && x 0 11).toNat = 0)
    (g45 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g46 : (x 3 2 && x 3 12).toNat = 0)
    (g47 : (x 1 4 && x 1 14).toNat = 0)
    (g48 : (x 3 4 && x 3 14).toNat = 0)
    (g49 : (x 1 2 && x 1 13).toNat = 0)
    (g50 : (x 0 3 && x 0 14).toNat = 0)
    (g51 : (x 3 2 && x 3 13).toNat = 0)
    (g52 : (x 3 3 && x 3 14).toNat = 0)
    (g53 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d476 : (x 0 1 && x 0 6).toNat = 0 := by
    have r477 := hand2 (x 0 1) (x 0 6)
    have b478 := hb (x 0 6)
    have b479 := hb (x 0 1 && x 0 6)
    clear * - r477 b478 b479 g10
    omega
  cases h480 : x 0 7
  · have f481 : (x 0 7).toNat = 0 := by rw [h480]; rfl
    have d482 : (x 0 1 && x 0 7).toNat = 0 := by
      have r483 := hand2 (x 0 1) (x 0 7)
      have b484 := hb (x 0 7)
      have b485 := hb (x 0 1 && x 0 7)
      clear * - r483 b484 b485 f481
      omega
    cases h486 : x 0 13
    · have f487 : (x 0 13).toNat = 0 := by rw [h486]; rfl
      cases h488 : x 1 1
      · have f489 : (x 1 1).toNat = 0 := by rw [h488]; rfl
        have d490 : (x 1 13).toNat = 0 := by
          have r491 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b492 := hb (x 1 1)
          have b493 := hb (x 1 13)
          clear * - r491 b492 b493 f489
          omega
        have d494 : (x 1 9).toNat = 0 := by
          have r495 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
          have b496 := hb (x 1 1)
          have b497 := hb (x 1 9)
          clear * - r495 b496 b497 f489
          omega
        have d498 : (x 1 5).toNat = 0 := by
          have r499 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
          have b500 := hb (x 1 5)
          have b501 := hb (x 1 13)
          clear * - r499 b500 b501 d490
          omega
        cases h502 : x (-1) 2
        · have f503 : (x (-1) 2).toNat = 0 := by rw [h502]; rfl
          have d504 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
            have r505 := hand1 (x (-1) 2) (x (-1) 12)
            have b506 := hb (x (-1) 2)
            have b507 := hb (x (-1) 2 && x (-1) 12)
            clear * - r505 b506 b507 f503
            omega
          have d508 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
            have r509 := hand1 (x (-1) 2) (x (-1) 11)
            have b510 := hb (x (-1) 2)
            have b511 := hb (x (-1) 2 && x (-1) 11)
            clear * - r509 b510 b511 f503
            omega
          have d512 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
            have r513 := hand1 (x (-1) 2) (x (-1) 7)
            have b514 := hb (x (-1) 2)
            have b515 := hb (x (-1) 2 && x (-1) 7)
            clear * - r513 b514 b515 f503
            omega
          have d516 : (x (-1) 2 && x (-1) 3).toNat = 0 := by
            have r517 := hand1 (x (-1) 2) (x (-1) 3)
            have b518 := hb (x (-1) 2)
            have b519 := hb (x (-1) 2 && x (-1) 3)
            clear * - r517 b518 b519 f503
            omega
          have d520 : (x 0 1 && x 0 14).toNat = 1 := by
            have r521 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b522 := hb (x (-1) 2)
            have b523 := hb (x 1 13)
            have b524 := hb (x 0 1 && x 0 14)
            clear * - r521 b522 b523 b524 d490 f503
            omega
          have d525 : (x 0 14).toNat = 1 := by
            have r526 := hand2 (x 0 1) (x 0 14)
            have b527 := hb (x 0 14)
            have b528 := hb (x 0 1 && x 0 14)
            clear * - r526 b527 b528 d520
            omega
          have d529 : (x (-1) 1).toNat = 0 := by
            have r530 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b531 := hb (x (-1) 1)
            have b532 := hb (x 0 14)
            clear * - r530 b531 b532 d525
            omega
          have d533 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
            have r534 := hand1 (x (-1) 1) (x (-1) 14)
            have b535 := hb (x (-1) 1)
            have b536 := hb (x (-1) 1 && x (-1) 14)
            clear * - r534 b535 b536 d529
            omega
          have d537 : (x (-2) 2).toNat = 1 := by
            have r538 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b539 := hb (x (-2) 2)
            have b540 := hb (x 0 13)
            have b541 := hb (x (-1) 1 && x (-1) 14)
            clear * - r538 b539 b540 b541 f487 d533
            omega
          have d542 : (x (-2) 14).toNat = 1 := by
            have r543 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
            have b544 := hb (x (-2) 2)
            have b545 := hb (x (-2) 14)
            clear * - r543 b544 b545 d537
            omega
          have d546 : (x (-3) 1).toNat = 0 := by
            have r547 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b548 := hb (x (-3) 1)
            have b549 := hb (x (-2) 14)
            clear * - r547 b548 b549 d542
            omega
          have d550 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
            have r551 := hand1 (x (-3) 1) (x (-3) 12)
            have b552 := hb (x (-3) 1)
            have b553 := hb (x (-3) 1 && x (-3) 12)
            clear * - r551 b552 b553 d546
            omega
          have d554 : (x (-3) 13).toNat = 0 := by
            have r555 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
            have b556 := hb (x (-3) 1)
            have b557 := hb (x (-3) 13)
            clear * - r555 b556 b557 d546
            omega
          have d558 : (x (-3) 5).toNat = 0 := by
            have r559 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
            have b560 := hb (x (-3) 5)
            have b561 := hb (x (-3) 13)
            clear * - r559 b560 b561 d554
            omega
          have d562 : (x (-3) 9).toNat = 0 := by
            have r563 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
            have b564 := hb (x (-3) 1)
            have b565 := hb (x (-3) 9)
            clear * - r563 b564 b565 d546
            omega
          have d566 : (x (-2) 3 && x (-2) 13).toNat = 1 := by
            have r567 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b568 := hb (x (-4) 5)
            have b569 := hb (x 1 10)
            have b570 := hb (x 0 1 && x 0 11)
            have b571 := hb (x (-1) 2 && x (-1) 12)
            have b572 := hb (x (-2) 3 && x (-2) 13)
            have b573 := hb (x (-3) 4 && x (-3) 14)
            clear * - r567 b568 b569 b570 b571 b572 b573 g14 g44 d504 g45 g2
            omega
          have d574 : (x (-2) 3).toNat = 1 := by
            have r575 := hand1 (x (-2) 3) (x (-2) 13)
            have b576 := hb (x (-2) 3)
            have b577 := hb (x (-2) 3 && x (-2) 13)
            clear * - r575 b576 b577 d566
            omega
          have d578 : (x (-2) 3 && x (-2) 12).toNat = 1 := by
            have r579 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b580 := hb (x (-5) 6)
            have b581 := hb (x 1 9)
            have b582 := hb (x 0 1 && x 0 10)
            have b583 := hb (x (-1) 2 && x (-1) 11)
            have b584 := hb (x (-2) 3 && x (-2) 12)
            have b585 := hb (x (-3) 4 && x (-3) 13)
            have b586 := hb (x (-4) 5 && x (-4) 14)
            clear * - r579 b580 b581 b582 b583 b584 b585 b586 d494 g38 d508 g39 g40 g1
            omega
          have d587 : (x (-2) 12).toNat = 1 := by
            have r588 := hand2 (x (-2) 3) (x (-2) 12)
            have b589 := hb (x (-2) 12)
            have b590 := hb (x (-2) 3 && x (-2) 12)
            clear * - r588 b589 b590 d578
            omega
          have d591 : (x (-4) 2).toNat = 0 := by
            have r592 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e593 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e594 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b595 := hb (x (-5) 3)
            have b596 := hb (x (-4) 2)
            have b597 := hb (x (-3) 13)
            have b598 := hb (x (-2) 12)
            clear * - r592 e593 e594 b595 b596 b597 b598 d587 d554
            omega
          have d599 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
            have r600 := hand1 (x (-4) 2) (x (-4) 13)
            have b601 := hb (x (-4) 2)
            have b602 := hb (x (-4) 2 && x (-4) 13)
            clear * - r600 b601 b602 d591
            omega
          have d603 : (x (-4) 10).toNat = 0 := by
            have r604 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
            have b605 := hb (x (-4) 2)
            have b606 := hb (x (-4) 10)
            clear * - r604 b605 b606 d591
            omega
          have d607 : (x (-4) 1 && x (-4) 10).toNat = 0 := by
            have r608 := hand2 (x (-4) 1) (x (-4) 10)
            have b609 := hb (x (-4) 10)
            have b610 := hb (x (-4) 1 && x (-4) 10)
            clear * - r608 b609 b610 d603
            omega
          have d611 : (x (-5) 3).toNat = 0 := by
            have r612 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e613 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e614 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b615 := hb (x (-5) 3)
            have b616 := hb (x (-4) 2)
            have b617 := hb (x (-3) 13)
            have b618 := hb (x (-2) 12)
            clear * - r612 e613 e614 b615 b616 b617 b618 d587 d554 d591
            omega
          have d619 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
            have r620 := hand1 (x (-5) 3) (x (-5) 14)
            have b621 := hb (x (-5) 3)
            have b622 := hb (x (-5) 3 && x (-5) 14)
            clear * - r620 b621 b622 d611
            omega
          have d623 : (x (-6) 4).toNat = 1 := by
            have r624 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b625 := hb (x (-6) 4)
            have b626 := hb (x (-2) 11)
            have b627 := hb (x (-3) 1 && x (-3) 12)
            have b628 := hb (x (-4) 2 && x (-4) 13)
            have b629 := hb (x (-5) 3 && x (-5) 14)
            clear * - r624 b625 b626 b627 b628 b629 g4 d550 d599 d619
            omega
          have d630 : (x (-6) 12).toNat = 1 := by
            have r631 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
            have b632 := hb (x (-6) 4)
            have b633 := hb (x (-6) 12)
            clear * - r631 b632 b633 d623
            omega
          have d634 : (x (-7) 13).toNat = 0 := by
            have r635 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e636 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
            have e637 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
            have b638 := hb (x (-9) 3)
            have b639 := hb (x (-8) 2)
            have b640 := hb (x (-7) 13)
            have b641 := hb (x (-6) 12)
            clear * - r635 e636 e637 b638 b639 b640 b641 d630
            omega
          have d642 : (x (-7) 4 && x (-7) 13).toNat = 0 := by
            have r643 := hand2 (x (-7) 4) (x (-7) 13)
            have b644 := hb (x (-7) 13)
            have b645 := hb (x (-7) 4 && x (-7) 13)
            clear * - r643 b644 b645 d634
            omega
          have d646 : (x (-7) 8 && x (-7) 13).toNat = 0 := by
            have r647 := hand2 (x (-7) 8) (x (-7) 13)
            have b648 := hb (x (-7) 13)
            have b649 := hb (x (-7) 8 && x (-7) 13)
            clear * - r647 b648 b649 d634
            omega
          have d650 : (x (-7) 5).toNat = 0 := by
            have r651 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
            have b652 := hb (x (-7) 5)
            have b653 := hb (x (-7) 13)
            clear * - r651 b652 b653 d634
            omega
          have d654 : (x (-8) 2).toNat = 0 := by
            have r655 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e656 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
            have e657 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
            have b658 := hb (x (-9) 3)
            have b659 := hb (x (-8) 2)
            have b660 := hb (x (-7) 13)
            have b661 := hb (x (-6) 12)
            clear * - r655 e656 e657 b658 b659 b660 b661 d630 d634
            omega
          have d662 : (x (-8) 2 && x (-8) 9).toNat = 0 := by
            have r663 := hand1 (x (-8) 2) (x (-8) 9)
            have b664 := hb (x (-8) 2)
            have b665 := hb (x (-8) 2 && x (-8) 9)
            clear * - r663 b664 b665 d654
            omega
          have d666 : (x (-8) 10).toNat = 0 := by
            have r667 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
            have b668 := hb (x (-8) 2)
            have b669 := hb (x (-8) 10)
            clear * - r667 b668 b669 d654
            omega
          have d670 : (x (-8) 1 && x (-8) 10).toNat = 0 := by
            have r671 := hand2 (x (-8) 1) (x (-8) 10)
            have b672 := hb (x (-8) 10)
            have b673 := hb (x (-8) 1 && x (-8) 10)
            clear * - r671 b672 b673 d666
            omega
          have d674 : (x (-8) 5 && x (-8) 10).toNat = 0 := by
            have r675 := hand2 (x (-8) 5) (x (-8) 10)
            have b676 := hb (x (-8) 10)
            have b677 := hb (x (-8) 5 && x (-8) 10)
            clear * - r675 b676 b677 d666
            omega
          have d678 : (x (-8) 9 && x (-8) 10).toNat = 0 := by
            have r679 := hand2 (x (-8) 9) (x (-8) 10)
            have b680 := hb (x (-8) 10)
            have b681 := hb (x (-8) 9 && x (-8) 10)
            clear * - r679 b680 b681 d666
            omega
          have d682 : (x (-9) 3).toNat = 0 := by
            have r683 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e684 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
            have e685 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
            have b686 := hb (x (-9) 3)
            have b687 := hb (x (-8) 2)
            have b688 := hb (x (-7) 13)
            have b689 := hb (x (-6) 12)
            clear * - r683 e684 e685 b686 b687 b688 b689 d630 d634 d654
            omega
          have d690 : (x (-9) 3 && x (-9) 10).toNat = 0 := by
            have r691 := hand1 (x (-9) 3) (x (-9) 10)
            have b692 := hb (x (-9) 3)
            have b693 := hb (x (-9) 3 && x (-9) 10)
            clear * - r691 b692 b693 d682
            omega
          have d694 : (x (-9) 11).toNat = 0 := by
            have r695 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
            have b696 := hb (x (-9) 3)
            have b697 := hb (x (-9) 11)
            clear * - r695 b696 b697 d682
            omega
          have d698 : (x (-9) 2 && x (-9) 11).toNat = 0 := by
            have r699 := hand2 (x (-9) 2) (x (-9) 11)
            have b700 := hb (x (-9) 11)
            have b701 := hb (x (-9) 2 && x (-9) 11)
            clear * - r699 b700 b701 d694
            omega
          have d702 : (x (-9) 6 && x (-9) 11).toNat = 0 := by
            have r703 := hand2 (x (-9) 6) (x (-9) 11)
            have b704 := hb (x (-9) 11)
            have b705 := hb (x (-9) 6 && x (-9) 11)
            clear * - r703 b704 b705 d694
            omega
          have d706 : (x (-9) 10 && x (-9) 11).toNat = 0 := by
            have r707 := hand2 (x (-9) 10) (x (-9) 11)
            have b708 := hb (x (-9) 11)
            have b709 := hb (x (-9) 10 && x (-9) 11)
            clear * - r707 b708 b709 d694
            omega
          have d710 : (x (-5) 11).toNat = 0 := by
            have r711 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
            have b712 := hb (x (-5) 3)
            have b713 := hb (x (-5) 11)
            clear * - r711 b712 b713 d611
            omega
          have d714 : (x (-5) 2 && x (-5) 11).toNat = 0 := by
            have r715 := hand2 (x (-5) 2) (x (-5) 11)
            have b716 := hb (x (-5) 11)
            have b717 := hb (x (-5) 2 && x (-5) 11)
            clear * - r715 b716 b717 d710
            omega
          have d718 : (x (-2) 8).toNat = 0 := by
            have r719 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e720 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e721 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e722 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e723 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e724 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e725 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have b726 := hb (x (-9) 7)
            have b727 := hb (x (-8) 6)
            have b728 := hb (x (-7) 5)
            have b729 := hb (x (-6) 4)
            have b730 := hb (x (-5) 11)
            have b731 := hb (x (-4) 10)
            have b732 := hb (x (-3) 9)
            have b733 := hb (x (-2) 8)
            clear * - r719 e720 e721 e722 e723 e724 e725 b726 b727 b728 b729 b730 b731 b732 b733 d562 d603 d710 d623 d650
            omega
          have d734 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
            have r735 := hand2 (x (-2) 3) (x (-2) 8)
            have b736 := hb (x (-2) 8)
            have b737 := hb (x (-2) 3 && x (-2) 8)
            clear * - r735 b736 b737 d718
            omega
          have r738 : (x (-4) 1).toNat + (x (-5) 2).toNat + (x (-6) 3).toNat + (x (-7) 4).toNat + (x (-8) 5).toNat + (x (-9) 6).toNat + (x (-10) 7).toNat + (x (-11) 8).toNat + (x (-12) 9).toNat + (x (-13) 10).toNat + (x (-14) 11).toNat + (x (-15) 12).toNat + (x (-16) 13).toNat + (x (-17) 14).toNat = 3 := by have q := hcount (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r739 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r740 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r741 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e742 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
          have e743 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
          have e744 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
          have e745 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
          have e746 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
          have e747 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
          have r748 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e749 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
          have e750 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
          have e751 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
          have e752 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
          have e753 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
          have e754 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
          have r755 : 1 ≤ (x 1 1).toNat + (x 0 1 && x 0 2).toNat + (x (-1) 2 && x (-1) 3).toNat + (x (-2) 3 && x (-2) 4).toNat + (x (-3) 4 && x (-3) 5).toNat + (x (-4) 5 && x (-4) 6).toNat + (x (-5) 6 && x (-5) 7).toNat + (x (-6) 7 && x (-6) 8).toNat + (x (-7) 8 && x (-7) 9).toNat + (x (-8) 9 && x (-8) 10).toNat + (x (-9) 10 && x (-9) 11).toNat + (x (-10) 11 && x (-10) 12).toNat + (x (-11) 12 && x (-11) 13).toNat + (x (-12) 13 && x (-12) 14).toNat + (x (-13) 14).toNat := by have q := hcov1 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r756 : 1 ≤ (x (-3) 5).toNat + (x (-4) 1 && x (-4) 6).toNat + (x (-5) 2 && x (-5) 7).toNat + (x (-6) 3 && x (-6) 8).toNat + (x (-7) 4 && x (-7) 9).toNat + (x (-8) 5 && x (-8) 10).toNat + (x (-9) 6 && x (-9) 11).toNat + (x (-10) 7 && x (-10) 12).toNat + (x (-11) 8 && x (-11) 13).toNat + (x (-12) 9 && x (-12) 14).toNat + (x (-13) 10).toNat := by have q := hcov5 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r757 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r758 : 1 ≤ (x (-6) 7).toNat + (x (-7) 1 && x (-7) 8).toNat + (x (-8) 2 && x (-8) 9).toNat + (x (-9) 3 && x (-9) 10).toNat + (x (-10) 4 && x (-10) 11).toNat + (x (-11) 5 && x (-11) 12).toNat + (x (-12) 6 && x (-12) 13).toNat + (x (-13) 7 && x (-13) 14).toNat + (x (-14) 8).toNat := by have q := hcov7 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r759 : 1 ≤ (x (-7) 9).toNat + (x (-8) 1 && x (-8) 10).toNat + (x (-9) 2 && x (-9) 11).toNat + (x (-10) 3 && x (-10) 12).toNat + (x (-11) 4 && x (-11) 13).toNat + (x (-12) 5 && x (-12) 14).toNat + (x (-13) 6).toNat := by have q := hcov9 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r760 : 1 ≤ (x (-3) 9).toNat + (x (-4) 1 && x (-4) 10).toNat + (x (-5) 2 && x (-5) 11).toNat + (x (-6) 3 && x (-6) 12).toNat + (x (-7) 4 && x (-7) 13).toNat + (x (-8) 5 && x (-8) 14).toNat + (x (-9) 6).toNat := by have q := hcov9 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r761 : 1 ≤ (x (-14) 11).toNat + (x (-15) 1 && x (-15) 12).toNat + (x (-16) 2 && x (-16) 13).toNat + (x (-17) 3 && x (-17) 14).toNat + (x (-18) 4).toNat := by have q := hcov11 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r762 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r763 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r764 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
          have r765 := hand2 (x (-2) 3) (x (-2) 4)
          have r766 := hand1 (x (-7) 8) (x (-7) 9)
          have r767 := hand1 (x (-10) 11) (x (-10) 12)
          have r768 := hand1 (x (-11) 12) (x (-11) 13)
          have r769 := hand1 (x (-12) 13) (x (-12) 14)
          have r770 := hand2 (x (-4) 1) (x (-4) 6)
          have r771 := hand2 (x (-5) 2) (x (-5) 7)
          have r772 := hand2 (x (-6) 3) (x (-6) 8)
          have r773 := hand1 (x (-7) 4) (x (-7) 9)
          have r774 := hand1 (x (-10) 7) (x (-10) 12)
          have r775 := hand1 (x (-11) 8) (x (-11) 13)
          have r776 := hand1 (x (-12) 9) (x (-12) 14)
          have r777 := hand1 (x (-8) 9) (x (-8) 14)
          have r778 := hand2 (x (-7) 1) (x (-7) 8)
          have r779 := hand2 (x (-10) 4) (x (-10) 11)
          have r780 := hand2 (x (-11) 5) (x (-11) 12)
          have r781 := hand2 (x (-12) 6) (x (-12) 13)
          have r782 := hand2 (x (-13) 7) (x (-13) 14)
          have r783 := hand2 (x (-10) 3) (x (-10) 12)
          have r784 := hand1 (x (-11) 4) (x (-11) 13)
          have r785 := hand1 (x (-12) 5) (x (-12) 14)
          have r786 := hand1 (x (-6) 3) (x (-6) 12)
          have r787 := hand1 (x (-8) 5) (x (-8) 14)
          have r788 := hand2 (x (-15) 1) (x (-15) 12)
          have r789 := hand2 (x (-16) 2) (x (-16) 13)
          have r790 := hand2 (x (-17) 3) (x (-17) 14)
          have r791 := hand2 (x (-12) 1) (x (-12) 14)
          have r792 := hand1 (x (-4) 1) (x (-4) 14)
          linarith only [r738, r739, r740, r741, e742, e743, e744, e745, e746, e747, r748, e749, e750, e751, e752, e753, e754, r755, r756, r757, r758, r759, r760, r761, r762, r763, r764, r765, r766, r767, r768, r769, r770, r771, r772, r773, r774, r775, r776, r777, r778, r779, r780, r781, r782, r783, r784, r785, r786, r787, r788, r789, r790, r791, r792, d694, d666, g0, g1, g2, g3, d558, d562, d554, d574, f503, g6, g7, f489, d498, g19, d516, g20, g21, g22, g23, d678, d706, d674, d702, d476, d512, d734, g26, g27, g28, g29, d646, d662, d690, d670, d698, d607, d714, d642]
        · have f904 : (x (-1) 2).toNat = 1 := by rw [h502]; rfl
          have d905 : (x (-1) 14).toNat = 1 := by
            have r906 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
            have b907 := hb (x (-1) 2)
            have b908 := hb (x (-1) 14)
            clear * - r906 b907 b908 f904
            omega
          have d909 : (x (-2) 1).toNat = 0 := by
            have r910 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b911 := hb (x (-2) 1)
            have b912 := hb (x (-1) 14)
            clear * - r910 b911 b912 d905
            omega
          have d913 : (x (-2) 13).toNat = 0 := by
            have r914 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b915 := hb (x (-2) 1)
            have b916 := hb (x (-2) 13)
            clear * - r914 b915 b916 d909
            omega
          have d917 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
            have r918 := hand2 (x (-2) 3) (x (-2) 13)
            have b919 := hb (x (-2) 13)
            have b920 := hb (x (-2) 3 && x (-2) 13)
            clear * - r918 b919 b920 d913
            omega
          have d921 : (x (-2) 5).toNat = 0 := by
            have r922 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
            have b923 := hb (x (-2) 5)
            have b924 := hb (x (-2) 13)
            clear * - r922 b923 b924 d913
            omega
          have d925 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
            have r926 := hand1 (x (-2) 5) (x (-2) 9)
            have b927 := hb (x (-2) 5)
            have b928 := hb (x (-2) 5 && x (-2) 9)
            clear * - r926 b927 b928 d921
            omega
          have d929 : (x (-2) 9).toNat = 0 := by
            have r930 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
            have b931 := hb (x (-2) 1)
            have b932 := hb (x (-2) 9)
            clear * - r930 b931 b932 d909
            omega
          have d933 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
            have r934 := hand2 (x (-2) 3) (x (-2) 9)
            have b935 := hb (x (-2) 9)
            have b936 := hb (x (-2) 3 && x (-2) 9)
            clear * - r934 b935 b936 d929
            omega
          have d937 : (x 1 12).toNat = 0 := by
            have r938 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e939 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e940 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b941 := hb (x (-2) 3)
            have b942 := hb (x (-1) 2)
            have b943 := hb (x 0 13)
            have b944 := hb (x 1 12)
            clear * - r938 e939 e940 b941 b942 b943 b944 f487 f904
            omega
          have d945 : (x 1 4).toNat = 0 := by
            have r946 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
            have b947 := hb (x 1 4)
            have b948 := hb (x 1 12)
            clear * - r946 b947 b948 d937
            omega
          have d949 : (x (-2) 3).toNat = 0 := by
            have r950 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e951 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e952 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b953 := hb (x (-2) 3)
            have b954 := hb (x (-1) 2)
            have b955 := hb (x 0 13)
            have b956 := hb (x 1 12)
            clear * - r950 e951 e952 b953 b954 b955 b956 d937 f487 f904
            omega
          have d957 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
            have r958 := hand1 (x (-2) 3) (x (-2) 12)
            have b959 := hb (x (-2) 3)
            have b960 := hb (x (-2) 3 && x (-2) 12)
            clear * - r958 b959 b960 d949
            omega
          have d961 : (x (-1) 2 && x (-1) 12).toNat = 1 := by
            have r962 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b963 := hb (x (-4) 5)
            have b964 := hb (x 1 10)
            have b965 := hb (x 0 1 && x 0 11)
            have b966 := hb (x (-1) 2 && x (-1) 12)
            have b967 := hb (x (-2) 3 && x (-2) 13)
            have b968 := hb (x (-3) 4 && x (-3) 14)
            clear * - r962 b963 b964 b965 b966 b967 b968 g14 g44 d917 g45 g2
            omega
          have d969 : (x (-1) 12).toNat = 1 := by
            have r970 := hand2 (x (-1) 2) (x (-1) 12)
            have b971 := hb (x (-1) 12)
            have b972 := hb (x (-1) 2 && x (-1) 12)
            clear * - r970 b971 b972 d961
            omega
          have d973 : (x (-3) 2).toNat = 0 := by
            have r974 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e975 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e976 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b977 := hb (x (-4) 3)
            have b978 := hb (x (-3) 2)
            have b979 := hb (x (-2) 13)
            have b980 := hb (x (-1) 12)
            clear * - r974 e975 e976 b977 b978 b979 b980 d969 d913
            omega
          have d981 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
            have r982 := hand1 (x (-3) 2) (x (-3) 12)
            have b983 := hb (x (-3) 2)
            have b984 := hb (x (-3) 2 && x (-3) 12)
            clear * - r982 b983 b984 d973
            omega
          have d985 : (x (-3) 10).toNat = 0 := by
            have r986 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
            have b987 := hb (x (-3) 2)
            have b988 := hb (x (-3) 10)
            clear * - r986 b987 b988 d973
            omega
          have d989 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
            have r990 := hand2 (x (-3) 6) (x (-3) 10)
            have b991 := hb (x (-3) 10)
            have b992 := hb (x (-3) 6 && x (-3) 10)
            clear * - r990 b991 b992 d985
            omega
          have d993 : (x (-4) 3).toNat = 0 := by
            have r994 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e995 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e996 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b997 := hb (x (-4) 3)
            have b998 := hb (x (-3) 2)
            have b999 := hb (x (-2) 13)
            have b1000 := hb (x (-1) 12)
            clear * - r994 e995 e996 b997 b998 b999 b1000 d969 d913 d973
            omega
          have d1001 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
            have r1002 := hand1 (x (-4) 3) (x (-4) 13)
            have b1003 := hb (x (-4) 3)
            have b1004 := hb (x (-4) 3 && x (-4) 13)
            clear * - r1002 b1003 b1004 d993
            omega
          have d1005 : (x (-4) 11).toNat = 0 := by
            have r1006 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
            have b1007 := hb (x (-4) 3)
            have b1008 := hb (x (-4) 11)
            clear * - r1006 b1007 b1008 d993
            omega
          have d1009 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
            have r1010 := hand2 (x (-4) 7) (x (-4) 11)
            have b1011 := hb (x (-4) 11)
            have b1012 := hb (x (-4) 7 && x (-4) 11)
            clear * - r1010 b1011 b1012 d1005
            omega
          have d1013 : (x (-1) 2 && x (-1) 11).toNat = 1 := by
            have r1014 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1015 := hb (x (-5) 6)
            have b1016 := hb (x 1 9)
            have b1017 := hb (x 0 1 && x 0 10)
            have b1018 := hb (x (-1) 2 && x (-1) 11)
            have b1019 := hb (x (-2) 3 && x (-2) 12)
            have b1020 := hb (x (-3) 4 && x (-3) 13)
            have b1021 := hb (x (-4) 5 && x (-4) 14)
            clear * - r1014 b1015 b1016 b1017 b1018 b1019 b1020 b1021 d494 g38 d957 g39 g40 g1
            omega
          have d1022 : (x (-1) 11).toNat = 1 := by
            have r1023 := hand2 (x (-1) 2) (x (-1) 11)
            have b1024 := hb (x (-1) 11)
            have b1025 := hb (x (-1) 2 && x (-1) 11)
            clear * - r1023 b1024 b1025 d1013
            omega
          have d1026 : (x (-1) 3).toNat = 1 := by
            have r1027 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
            have b1028 := hb (x (-1) 3)
            have b1029 := hb (x (-1) 11)
            clear * - r1027 b1028 b1029 d1022
            omega
          have d1030 : (x 2 12).toNat = 0 := by
            have r1031 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1032 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e1033 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b1034 := hb (x (-1) 3)
            have b1035 := hb (x 0 2)
            have b1036 := hb (x 1 13)
            have b1037 := hb (x 2 12)
            clear * - r1031 e1032 e1033 b1034 b1035 b1036 b1037 d490 g7 d1026
            omega
          have d1038 : (x 2 1 && x 2 12).toNat = 0 := by
            have r1039 := hand2 (x 2 1) (x 2 12)
            have b1040 := hb (x 2 12)
            have b1041 := hb (x 2 1 && x 2 12)
            clear * - r1039 b1040 b1041 d1030
            omega
          have d1042 : (x 2 4).toNat = 0 := by
            have r1043 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
            have b1044 := hb (x 2 4)
            have b1045 := hb (x 2 12)
            clear * - r1043 b1044 b1045 d1030
            omega
          have d1046 : (x 2 4 && x 2 13).toNat = 0 := by
            have r1047 := hand1 (x 2 4) (x 2 13)
            have b1048 := hb (x 2 4)
            have b1049 := hb (x 2 4 && x 2 13)
            clear * - r1047 b1048 b1049 d1042
            omega
          cases h1050 : x 1 3
          · have f1051 : (x 1 3).toNat = 0 := by rw [h1050]; rfl
            cases h1052 : x (-1) 4
            · have f1053 : (x (-1) 4).toNat = 0 := by rw [h1052]; rfl
              have d1054 : (x 3 11).toNat = 1 := by
                have r1055 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1056 := hb (x (-1) 4)
                have b1057 := hb (x 3 11)
                have b1058 := hb (x 2 1 && x 2 12)
                have b1059 := hb (x 1 2 && x 1 13)
                have b1060 := hb (x 0 3 && x 0 14)
                clear * - r1055 b1056 b1057 b1058 b1059 b1060 d1038 g49 g50 f1053
                omega
              have d1061 : (x 3 3).toNat = 1 := by
                have r1062 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                have b1063 := hb (x 3 3)
                have b1064 := hb (x 3 11)
                clear * - r1062 b1063 b1064 d1054
                omega
              have d1065 : (x 6 12).toNat = 0 := by
                have r1066 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1067 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e1068 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b1069 := hb (x 3 3)
                have b1070 := hb (x 4 2)
                have b1071 := hb (x 5 13)
                have b1072 := hb (x 6 12)
                clear * - r1066 e1067 e1068 b1069 b1070 b1071 b1072 d1061
                omega
              have d1073 : (x 6 1 && x 6 12).toNat = 0 := by
                have r1074 := hand2 (x 6 1) (x 6 12)
                have b1075 := hb (x 6 12)
                have b1076 := hb (x 6 1 && x 6 12)
                clear * - r1074 b1075 b1076 d1065
                omega
              have d1077 : (x 6 4).toNat = 0 := by
                have r1078 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                have b1079 := hb (x 6 4)
                have b1080 := hb (x 6 12)
                clear * - r1078 b1079 b1080 d1065
                omega
              have d1081 : (x 5 13).toNat = 0 := by
                have r1082 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1083 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e1084 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b1085 := hb (x 3 3)
                have b1086 := hb (x 4 2)
                have b1087 := hb (x 5 13)
                have b1088 := hb (x 6 12)
                clear * - r1082 e1083 e1084 b1085 b1086 b1087 b1088 d1065 d1061
                omega
              have d1089 : (x 5 2 && x 5 13).toNat = 0 := by
                have r1090 := hand2 (x 5 2) (x 5 13)
                have b1091 := hb (x 5 13)
                have b1092 := hb (x 5 2 && x 5 13)
                clear * - r1090 b1091 b1092 d1081
                omega
              have d1093 : (x 4 1 && x 4 14).toNat = 1 := by
                have r1094 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1095 := hb (x 3 2)
                have b1096 := hb (x 5 13)
                have b1097 := hb (x 4 1 && x 4 14)
                clear * - r1094 b1095 b1096 b1097 d1081 g16
                omega
              have d1098 : (x 4 1).toNat = 1 := by
                have r1099 := hand1 (x 4 1) (x 4 14)
                have b1100 := hb (x 4 1)
                have b1101 := hb (x 4 1 && x 4 14)
                clear * - r1099 b1100 b1101 d1093
                omega
              have d1102 : (x 5 14).toNat = 0 := by
                have r1103 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1104 := hb (x 4 1)
                have b1105 := hb (x 5 14)
                clear * - r1103 b1104 b1105 d1098
                omega
              have d1106 : (x 5 1 && x 5 14).toNat = 0 := by
                have r1107 := hand2 (x 5 1) (x 5 14)
                have b1108 := hb (x 5 14)
                have b1109 := hb (x 5 1 && x 5 14)
                clear * - r1107 b1108 b1109 d1102
                omega
              have d1110 : (x 5 2).toNat = 0 := by
                have r1111 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b1112 := hb (x 5 2)
                have b1113 := hb (x 5 14)
                clear * - r1111 b1112 b1113 d1102
                omega
              have d1114 : (x 4 2).toNat = 0 := by
                have r1115 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1116 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e1117 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b1118 := hb (x 3 3)
                have b1119 := hb (x 4 2)
                have b1120 := hb (x 5 13)
                have b1121 := hb (x 6 12)
                clear * - r1115 e1116 e1117 b1118 b1119 b1120 b1121 d1065 d1081 d1061
                omega
              have d1122 : (x 4 2 && x 4 13).toNat = 0 := by
                have r1123 := hand1 (x 4 2) (x 4 13)
                have b1124 := hb (x 4 2)
                have b1125 := hb (x 4 2 && x 4 13)
                clear * - r1123 b1124 b1125 d1114
                omega
              have d1126 : (x 6 13).toNat = 1 := by
                have r1127 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1128 := hb (x 4 2)
                have b1129 := hb (x 6 13)
                have b1130 := hb (x 5 1 && x 5 14)
                clear * - r1127 b1128 b1129 b1130 d1106 d1114
                omega
              have d1131 : (x 6 1).toNat = 1 := by
                have r1132 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                have b1133 := hb (x 6 1)
                have b1134 := hb (x 6 13)
                clear * - r1132 b1133 b1134 d1126
                omega
              have d1135 : (x 7 14).toNat = 0 := by
                have r1136 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1137 := hb (x 6 1)
                have b1138 := hb (x 7 14)
                clear * - r1136 b1137 b1138 d1131
                omega
              have d1139 : (x 7 3 && x 7 14).toNat = 0 := by
                have r1140 := hand2 (x 7 3) (x 7 14)
                have b1141 := hb (x 7 14)
                have b1142 := hb (x 7 3 && x 7 14)
                clear * - r1140 b1141 b1142 d1135
                omega
              have d1143 : (x 7 2).toNat = 0 := by
                have r1144 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b1145 := hb (x 7 2)
                have b1146 := hb (x 7 14)
                clear * - r1144 b1145 b1146 d1135
                omega
              have d1147 : (x 7 12).toNat = 0 := by
                have r1148 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1149 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e1150 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b1151 := hb (x 4 3)
                have b1152 := hb (x 5 2)
                have b1153 := hb (x 6 13)
                have b1154 := hb (x 7 12)
                clear * - r1148 e1149 e1150 b1151 b1152 b1153 b1154 d1126 d1110
                omega
              have d1155 : (x 7 4).toNat = 0 := by
                have r1156 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have b1157 := hb (x 7 4)
                have b1158 := hb (x 7 12)
                clear * - r1156 b1157 b1158 d1147
                omega
              have d1159 : (x 4 3).toNat = 0 := by
                have r1160 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1161 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e1162 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b1163 := hb (x 4 3)
                have b1164 := hb (x 5 2)
                have b1165 := hb (x 6 13)
                have b1166 := hb (x 7 12)
                clear * - r1160 e1161 e1162 b1163 b1164 b1165 b1166 d1147 d1126 d1110
                omega
              have d1167 : (x 4 3 && x 4 14).toNat = 0 := by
                have r1168 := hand1 (x 4 3) (x 4 14)
                have b1169 := hb (x 4 3)
                have b1170 := hb (x 4 3 && x 4 14)
                clear * - r1168 b1169 b1170 d1159
                omega
              have d1171 : (x 7 11).toNat = 1 := by
                have r1172 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1173 := hb (x 3 4)
                have b1174 := hb (x 7 11)
                have b1175 := hb (x 6 1 && x 6 12)
                have b1176 := hb (x 5 2 && x 5 13)
                have b1177 := hb (x 4 3 && x 4 14)
                clear * - r1172 b1173 b1174 b1175 b1176 b1177 d1073 d1089 d1167 g17
                omega
              have d1178 : (x 7 3).toNat = 1 := by
                have r1179 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                have b1180 := hb (x 7 3)
                have b1181 := hb (x 7 11)
                clear * - r1179 b1180 b1181 d1171
                omega
              have d1182 : (x 10 12).toNat = 0 := by
                have r1183 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1184 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e1185 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b1186 := hb (x 7 3)
                have b1187 := hb (x 8 2)
                have b1188 := hb (x 9 13)
                have b1189 := hb (x 10 12)
                clear * - r1183 e1184 e1185 b1186 b1187 b1188 b1189 d1178
                omega
              have d1190 : (x 10 1 && x 10 12).toNat = 0 := by
                have r1191 := hand2 (x 10 1) (x 10 12)
                have b1192 := hb (x 10 12)
                have b1193 := hb (x 10 1 && x 10 12)
                clear * - r1191 b1192 b1193 d1182
                omega
              have d1194 : (x 10 4).toNat = 0 := by
                have r1195 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                have b1196 := hb (x 10 4)
                have b1197 := hb (x 10 12)
                clear * - r1195 b1196 b1197 d1182
                omega
              have d1198 : (x 9 13).toNat = 0 := by
                have r1199 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1200 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e1201 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b1202 := hb (x 7 3)
                have b1203 := hb (x 8 2)
                have b1204 := hb (x 9 13)
                have b1205 := hb (x 10 12)
                clear * - r1199 e1200 e1201 b1202 b1203 b1204 b1205 d1182 d1178
                omega
              have d1206 : (x 9 2 && x 9 13).toNat = 0 := by
                have r1207 := hand2 (x 9 2) (x 9 13)
                have b1208 := hb (x 9 13)
                have b1209 := hb (x 9 2 && x 9 13)
                clear * - r1207 b1208 b1209 d1198
                omega
              have d1210 : (x 8 1 && x 8 14).toNat = 1 := by
                have r1211 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1212 := hb (x 7 2)
                have b1213 := hb (x 9 13)
                have b1214 := hb (x 8 1 && x 8 14)
                clear * - r1211 b1212 b1213 b1214 d1198 d1143
                omega
              have d1215 : (x 8 14).toNat = 1 := by
                have r1216 := hand2 (x 8 1) (x 8 14)
                have b1217 := hb (x 8 14)
                have b1218 := hb (x 8 1 && x 8 14)
                clear * - r1216 b1217 b1218 d1210
                omega
              have d1219 : (x 7 1).toNat = 0 := by
                have r1220 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1221 := hb (x 7 1)
                have b1222 := hb (x 8 14)
                clear * - r1220 b1221 b1222 d1215
                omega
              have d1223 : (x 7 13).toNat = 0 := by
                have r1224 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                have b1225 := hb (x 7 1)
                have b1226 := hb (x 7 13)
                clear * - r1224 b1225 b1226 d1219
                omega
              have d1227 : (x 6 1 && x 6 14).toNat = 1 := by
                have r1228 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1229 := hb (x 5 2)
                have b1230 := hb (x 7 13)
                have b1231 := hb (x 6 1 && x 6 14)
                clear * - r1228 b1229 b1230 b1231 d1223 d1110
                omega
              have d1232 : (x 6 14).toNat = 1 := by
                have r1233 := hand2 (x 6 1) (x 6 14)
                have b1234 := hb (x 6 14)
                have b1235 := hb (x 6 1 && x 6 14)
                clear * - r1233 b1234 b1235 d1227
                omega
              have d1236 : (x 5 1).toNat = 0 := by
                have r1237 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1238 := hb (x 5 1)
                have b1239 := hb (x 6 14)
                clear * - r1237 b1238 b1239 d1232
                omega
              have d1240 : (x 5 1 && x 5 12).toNat = 0 := by
                have r1241 := hand1 (x 5 1) (x 5 12)
                have b1242 := hb (x 5 1)
                have b1243 := hb (x 5 1 && x 5 12)
                clear * - r1241 b1242 b1243 d1236
                omega
              have d1244 : (x 6 11).toNat = 1 := by
                have r1245 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1246 := hb (x 2 4)
                have b1247 := hb (x 6 11)
                have b1248 := hb (x 5 1 && x 5 12)
                have b1249 := hb (x 4 2 && x 4 13)
                have b1250 := hb (x 3 3 && x 3 14)
                clear * - r1245 b1246 b1247 b1248 b1249 b1250 d1240 d1122 g52 d1042
                omega
              have d1251 : (x 6 3).toNat = 1 := by
                have r1252 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                have b1253 := hb (x 6 3)
                have b1254 := hb (x 6 11)
                clear * - r1252 b1253 b1254 d1244
                omega
              have d1255 : (x 9 12).toNat = 0 := by
                have r1256 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1257 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e1258 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b1259 := hb (x 6 3)
                have b1260 := hb (x 7 2)
                have b1261 := hb (x 8 13)
                have b1262 := hb (x 9 12)
                clear * - r1256 e1257 e1258 b1259 b1260 b1261 b1262 d1143 d1251
                omega
              have d1263 : (x 9 1 && x 9 12).toNat = 0 := by
                have r1264 := hand2 (x 9 1) (x 9 12)
                have b1265 := hb (x 9 12)
                have b1266 := hb (x 9 1 && x 9 12)
                clear * - r1264 b1265 b1266 d1255
                omega
              have d1267 : (x 8 13).toNat = 0 := by
                have r1268 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1269 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e1270 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b1271 := hb (x 6 3)
                have b1272 := hb (x 7 2)
                have b1273 := hb (x 8 13)
                have b1274 := hb (x 9 12)
                clear * - r1268 e1269 e1270 b1271 b1272 b1273 b1274 d1255 d1143 d1251
                omega
              have d1275 : (x 8 2 && x 8 13).toNat = 0 := by
                have r1276 := hand2 (x 8 2) (x 8 13)
                have b1277 := hb (x 8 13)
                have b1278 := hb (x 8 2 && x 8 13)
                clear * - r1276 b1277 b1278 d1267
                omega
              have d1279 : (x 10 11).toNat = 1 := by
                have r1280 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1281 := hb (x 6 4)
                have b1282 := hb (x 10 11)
                have b1283 := hb (x 9 1 && x 9 12)
                have b1284 := hb (x 8 2 && x 8 13)
                have b1285 := hb (x 7 3 && x 7 14)
                clear * - r1280 b1281 b1282 b1283 b1284 b1285 d1263 d1275 d1139 d1077
                omega
              have d1286 : (x 10 3).toNat = 1 := by
                have r1287 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
                have b1288 := hb (x 10 3)
                have b1289 := hb (x 10 11)
                clear * - r1287 b1288 b1289 d1279
                omega
              have d1290 : (x 13 12).toNat = 0 := by
                have r1291 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1292 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e1293 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b1294 := hb (x 10 3)
                have b1295 := hb (x 11 2)
                have b1296 := hb (x 12 13)
                have b1297 := hb (x 13 12)
                clear * - r1291 e1292 e1293 b1294 b1295 b1296 b1297 d1286
                omega
              have d1298 : (x 13 1 && x 13 12).toNat = 0 := by
                have r1299 := hand2 (x 13 1) (x 13 12)
                have b1300 := hb (x 13 12)
                have b1301 := hb (x 13 1 && x 13 12)
                clear * - r1299 b1300 b1301 d1290
                omega
              have d1302 : (x 12 13).toNat = 0 := by
                have r1303 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1304 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e1305 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b1306 := hb (x 10 3)
                have b1307 := hb (x 11 2)
                have b1308 := hb (x 12 13)
                have b1309 := hb (x 13 12)
                clear * - r1303 e1304 e1305 b1306 b1307 b1308 b1309 d1290 d1286
                omega
              have d1310 : (x 12 2 && x 12 13).toNat = 0 := by
                have r1311 := hand2 (x 12 2) (x 12 13)
                have b1312 := hb (x 12 13)
                have b1313 := hb (x 12 2 && x 12 13)
                clear * - r1311 b1312 b1313 d1302
                omega
              have d1314 : (x 11 2).toNat = 0 := by
                have r1315 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1316 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e1317 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b1318 := hb (x 10 3)
                have b1319 := hb (x 11 2)
                have b1320 := hb (x 12 13)
                have b1321 := hb (x 13 12)
                clear * - r1315 e1316 e1317 b1318 b1319 b1320 b1321 d1290 d1302 d1286
                omega
              have d1322 : (x 8 1).toNat = 1 := by
                have r1323 := hand1 (x 8 1) (x 8 14)
                have b1324 := hb (x 8 1)
                have b1325 := hb (x 8 1 && x 8 14)
                clear * - r1323 b1324 b1325 d1210
                omega
              have d1326 : (x 9 14).toNat = 0 := by
                have r1327 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1328 := hb (x 8 1)
                have b1329 := hb (x 9 14)
                clear * - r1327 b1328 b1329 d1322
                omega
              have d1330 : (x 9 1 && x 9 14).toNat = 0 := by
                have r1331 := hand2 (x 9 1) (x 9 14)
                have b1332 := hb (x 9 14)
                have b1333 := hb (x 9 1 && x 9 14)
                clear * - r1331 b1332 b1333 d1326
                omega
              have d1334 : (x 9 2).toNat = 0 := by
                have r1335 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b1336 := hb (x 9 2)
                have b1337 := hb (x 9 14)
                clear * - r1335 b1336 b1337 d1326
                omega
              have d1338 : (x 8 2).toNat = 0 := by
                have r1339 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1340 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e1341 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b1342 := hb (x 7 3)
                have b1343 := hb (x 8 2)
                have b1344 := hb (x 9 13)
                have b1345 := hb (x 10 12)
                clear * - r1339 e1340 e1341 b1342 b1343 b1344 b1345 d1182 d1198 d1178
                omega
              have d1346 : (x 10 13).toNat = 1 := by
                have r1347 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1348 := hb (x 8 2)
                have b1349 := hb (x 10 13)
                have b1350 := hb (x 9 1 && x 9 14)
                clear * - r1347 b1348 b1349 b1350 d1330 d1338
                omega
              have d1351 : (x 10 1).toNat = 1 := by
                have r1352 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                have b1353 := hb (x 10 1)
                have b1354 := hb (x 10 13)
                clear * - r1352 b1353 b1354 d1346
                omega
              have d1355 : (x 11 14).toNat = 0 := by
                have r1356 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1357 := hb (x 10 1)
                have b1358 := hb (x 11 14)
                clear * - r1356 b1357 b1358 d1351
                omega
              have d1359 : (x 11 1 && x 11 14).toNat = 0 := by
                have r1360 := hand2 (x 11 1) (x 11 14)
                have b1361 := hb (x 11 14)
                have b1362 := hb (x 11 1 && x 11 14)
                clear * - r1360 b1361 b1362 d1355
                omega
              have d1363 : (x 10 2).toNat = 1 := by
                have r1364 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1365 := hb (x 10 2)
                have b1366 := hb (x 12 13)
                have b1367 := hb (x 11 1 && x 11 14)
                clear * - r1364 b1365 b1366 b1367 d1302 d1359
                omega
              have d1368 : (x 12 12).toNat = 0 := by
                have r1369 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1370 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e1371 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b1372 := hb (x 9 3)
                have b1373 := hb (x 10 2)
                have b1374 := hb (x 11 13)
                have b1375 := hb (x 12 12)
                clear * - r1369 e1370 e1371 b1372 b1373 b1374 b1375 d1363
                omega
              have d1376 : (x 12 4).toNat = 0 := by
                have r1377 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
                have b1378 := hb (x 12 4)
                have b1379 := hb (x 12 12)
                clear * - r1377 b1378 b1379 d1368
                omega
              have d1380 : (x 12 4 && x 12 14).toNat = 0 := by
                have r1381 := hand1 (x 12 4) (x 12 14)
                have b1382 := hb (x 12 4)
                have b1383 := hb (x 12 4 && x 12 14)
                clear * - r1381 b1382 b1383 d1376
                omega
              have d1384 : (x 11 13).toNat = 0 := by
                have r1385 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1386 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e1387 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b1388 := hb (x 9 3)
                have b1389 := hb (x 10 2)
                have b1390 := hb (x 11 13)
                have b1391 := hb (x 12 12)
                clear * - r1385 e1386 e1387 b1388 b1389 b1390 b1391 d1368 d1363
                omega
              have d1392 : (x 11 5).toNat = 0 := by
                have r1393 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
                have b1394 := hb (x 11 5)
                have b1395 := hb (x 11 13)
                clear * - r1393 b1394 b1395 d1384
                omega
              have d1396 : (x 11 3 && x 11 14).toNat = 0 := by
                have r1397 := hand2 (x 11 3) (x 11 14)
                have b1398 := hb (x 11 14)
                have b1399 := hb (x 11 3 && x 11 14)
                clear * - r1397 b1398 b1399 d1355
                omega
              have d1400 : (x 14 11).toNat = 1 := by
                have r1401 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1402 := hb (x 10 4)
                have b1403 := hb (x 14 11)
                have b1404 := hb (x 13 1 && x 13 12)
                have b1405 := hb (x 12 2 && x 12 13)
                have b1406 := hb (x 11 3 && x 11 14)
                clear * - r1401 b1402 b1403 b1404 b1405 b1406 d1298 d1310 d1396 d1194
                omega
              have d1407 : (x 14 3).toNat = 1 := by
                have r1408 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                have b1409 := hb (x 14 3)
                have b1410 := hb (x 14 11)
                clear * - r1408 b1409 b1410 d1400
                omega
              have d1411 : (x 17 12).toNat = 0 := by
                have r1412 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1413 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e1414 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b1415 := hb (x 14 3)
                have b1416 := hb (x 15 2)
                have b1417 := hb (x 16 13)
                have b1418 := hb (x 17 12)
                clear * - r1412 e1413 e1414 b1415 b1416 b1417 b1418 d1407
                omega
              have d1419 : (x 16 13).toNat = 0 := by
                have r1420 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1421 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e1422 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b1423 := hb (x 14 3)
                have b1424 := hb (x 15 2)
                have b1425 := hb (x 16 13)
                have b1426 := hb (x 17 12)
                clear * - r1420 e1421 e1422 b1423 b1424 b1425 b1426 d1411 d1407
                omega
              have d1427 : (x 15 2).toNat = 0 := by
                have r1428 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1429 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e1430 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b1431 := hb (x 14 3)
                have b1432 := hb (x 15 2)
                have b1433 := hb (x 16 13)
                have b1434 := hb (x 17 12)
                clear * - r1428 e1429 e1430 b1431 b1432 b1433 b1434 d1411 d1419 d1407
                omega
              have d1435 : (x 11 12).toNat = 0 := by
                have r1436 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1437 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e1438 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b1439 := hb (x 8 3)
                have b1440 := hb (x 9 2)
                have b1441 := hb (x 10 13)
                have b1442 := hb (x 11 12)
                clear * - r1436 e1437 e1438 b1439 b1440 b1441 b1442 d1346 d1334
                omega
              have d1443 : (x 11 4).toNat = 0 := by
                have r1444 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                have b1445 := hb (x 11 4)
                have b1446 := hb (x 11 12)
                clear * - r1444 b1445 b1446 d1435
                omega
              have d1447 : (x 8 3).toNat = 0 := by
                have r1448 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1449 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e1450 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b1451 := hb (x 8 3)
                have b1452 := hb (x 9 2)
                have b1453 := hb (x 10 13)
                have b1454 := hb (x 11 12)
                clear * - r1448 e1449 e1450 b1451 b1452 b1453 b1454 d1435 d1346 d1334
                omega
              have d1455 : (x 8 3 && x 8 14).toNat = 0 := by
                have r1456 := hand1 (x 8 3) (x 8 14)
                have b1457 := hb (x 8 3)
                have b1458 := hb (x 8 3 && x 8 14)
                clear * - r1456 b1457 b1458 d1447
                omega
              have d1459 : (x 11 11).toNat = 1 := by
                have r1460 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1461 := hb (x 7 4)
                have b1462 := hb (x 11 11)
                have b1463 := hb (x 10 1 && x 10 12)
                have b1464 := hb (x 9 2 && x 9 13)
                have b1465 := hb (x 8 3 && x 8 14)
                clear * - r1460 b1461 b1462 b1463 b1464 b1465 d1190 d1206 d1455 d1155
                omega
              have d1466 : (x 11 3).toNat = 1 := by
                have r1467 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
                have b1468 := hb (x 11 3)
                have b1469 := hb (x 11 11)
                clear * - r1467 b1468 b1469 d1459
                omega
              have d1470 : (x 14 12).toNat = 0 := by
                have r1471 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1472 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e1473 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b1474 := hb (x 11 3)
                have b1475 := hb (x 12 2)
                have b1476 := hb (x 13 13)
                have b1477 := hb (x 14 12)
                clear * - r1471 e1472 e1473 b1474 b1475 b1476 b1477 d1466
                omega
              have d1478 : (x 14 1 && x 14 12).toNat = 0 := by
                have r1479 := hand2 (x 14 1) (x 14 12)
                have b1480 := hb (x 14 12)
                have b1481 := hb (x 14 1 && x 14 12)
                clear * - r1479 b1480 b1481 d1470
                omega
              have d1482 : (x 14 2 && x 14 12).toNat = 0 := by
                have r1483 := hand2 (x 14 2) (x 14 12)
                have b1484 := hb (x 14 12)
                have b1485 := hb (x 14 2 && x 14 12)
                clear * - r1483 b1484 b1485 d1470
                omega
              have d1486 : (x 13 13).toNat = 0 := by
                have r1487 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1488 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e1489 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b1490 := hb (x 11 3)
                have b1491 := hb (x 12 2)
                have b1492 := hb (x 13 13)
                have b1493 := hb (x 14 12)
                clear * - r1487 e1488 e1489 b1490 b1491 b1492 b1493 d1470 d1466
                omega
              have d1494 : (x 13 2 && x 13 13).toNat = 0 := by
                have r1495 := hand2 (x 13 2) (x 13 13)
                have b1496 := hb (x 13 13)
                have b1497 := hb (x 13 2 && x 13 13)
                clear * - r1495 b1496 b1497 d1486
                omega
              have d1498 : (x 13 3 && x 13 13).toNat = 0 := by
                have r1499 := hand2 (x 13 3) (x 13 13)
                have b1500 := hb (x 13 13)
                have b1501 := hb (x 13 3 && x 13 13)
                clear * - r1499 b1500 b1501 d1486
                omega
              have d1502 : (x 12 1 && x 12 14).toNat = 1 := by
                have r1503 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1504 := hb (x 11 2)
                have b1505 := hb (x 13 13)
                have b1506 := hb (x 12 1 && x 12 14)
                clear * - r1503 b1504 b1505 b1506 d1486 d1314
                omega
              have d1507 : (x 12 1).toNat = 1 := by
                have r1508 := hand1 (x 12 1) (x 12 14)
                have b1509 := hb (x 12 1)
                have b1510 := hb (x 12 1 && x 12 14)
                clear * - r1508 b1509 b1510 d1502
                omega
              have d1511 : (x 13 14).toNat = 0 := by
                have r1512 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1513 := hb (x 12 1)
                have b1514 := hb (x 13 14)
                clear * - r1512 b1513 b1514 d1507
                omega
              have d1515 : (x 13 1 && x 13 14).toNat = 0 := by
                have r1516 := hand2 (x 13 1) (x 13 14)
                have b1517 := hb (x 13 14)
                have b1518 := hb (x 13 1 && x 13 14)
                clear * - r1516 b1517 b1518 d1511
                omega
              have d1519 : (x 13 2).toNat = 0 := by
                have r1520 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
                have b1521 := hb (x 13 2)
                have b1522 := hb (x 13 14)
                clear * - r1520 b1521 b1522 d1511
                omega
              have d1523 : (x 12 2).toNat = 0 := by
                have r1524 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1525 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e1526 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b1527 := hb (x 11 3)
                have b1528 := hb (x 12 2)
                have b1529 := hb (x 13 13)
                have b1530 := hb (x 14 12)
                clear * - r1524 e1525 e1526 b1527 b1528 b1529 b1530 d1470 d1486 d1466
                omega
              have d1531 : (x 14 13).toNat = 1 := by
                have r1532 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1533 := hb (x 12 2)
                have b1534 := hb (x 14 13)
                have b1535 := hb (x 13 1 && x 13 14)
                clear * - r1532 b1533 b1534 b1535 d1515 d1523
                omega
              have d1536 : (x 15 12).toNat = 0 := by
                have r1537 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1538 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e1539 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b1540 := hb (x 12 3)
                have b1541 := hb (x 13 2)
                have b1542 := hb (x 14 13)
                have b1543 := hb (x 15 12)
                clear * - r1537 e1538 e1539 b1540 b1541 b1542 b1543 d1531 d1519
                omega
              have d1544 : (x 12 3).toNat = 0 := by
                have r1545 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1546 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e1547 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b1548 := hb (x 12 3)
                have b1549 := hb (x 13 2)
                have b1550 := hb (x 14 13)
                have b1551 := hb (x 15 12)
                clear * - r1545 e1546 e1547 b1548 b1549 b1550 b1551 d1536 d1531 d1519
                omega
              have d1552 : (x 12 3 && x 12 14).toNat = 0 := by
                have r1553 := hand1 (x 12 3) (x 12 14)
                have b1554 := hb (x 12 3)
                have b1555 := hb (x 12 3 && x 12 14)
                clear * - r1553 b1554 b1555 d1544
                omega
              have d1556 : (x 15 11).toNat = 1 := by
                have r1557 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1558 := hb (x 11 4)
                have b1559 := hb (x 15 11)
                have b1560 := hb (x 14 1 && x 14 12)
                have b1561 := hb (x 13 2 && x 13 13)
                have b1562 := hb (x 12 3 && x 12 14)
                clear * - r1557 b1558 b1559 b1560 b1561 b1562 d1478 d1494 d1552 d1443
                omega
              have d1563 : (x 15 3).toNat = 1 := by
                have r1564 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
                have b1565 := hb (x 15 3)
                have b1566 := hb (x 15 11)
                clear * - r1564 b1565 b1566 d1556
                omega
              have d1567 : (x 18 12).toNat = 0 := by
                have r1568 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1569 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e1570 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b1571 := hb (x 15 3)
                have b1572 := hb (x 16 2)
                have b1573 := hb (x 17 13)
                have b1574 := hb (x 18 12)
                clear * - r1568 e1569 e1570 b1571 b1572 b1573 b1574 d1563
                omega
              have d1575 : (x 17 13).toNat = 0 := by
                have r1576 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1577 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e1578 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b1579 := hb (x 15 3)
                have b1580 := hb (x 16 2)
                have b1581 := hb (x 17 13)
                have b1582 := hb (x 18 12)
                clear * - r1576 e1577 e1578 b1579 b1580 b1581 b1582 d1567 d1563
                omega
              have d1583 : (x 16 1 && x 16 14).toNat = 1 := by
                have r1584 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1585 := hb (x 15 2)
                have b1586 := hb (x 17 13)
                have b1587 := hb (x 16 1 && x 16 14)
                clear * - r1584 b1585 b1586 b1587 d1575 d1427
                omega
              have d1588 : (x 16 14).toNat = 1 := by
                have r1589 := hand2 (x 16 1) (x 16 14)
                have b1590 := hb (x 16 14)
                have b1591 := hb (x 16 1 && x 16 14)
                clear * - r1589 b1590 b1591 d1583
                omega
              have d1592 : (x 15 1).toNat = 0 := by
                have r1593 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1594 := hb (x 15 1)
                have b1595 := hb (x 16 14)
                clear * - r1593 b1594 b1595 d1588
                omega
              have d1596 : (x 15 1 && x 15 11).toNat = 0 := by
                have r1597 := hand1 (x 15 1) (x 15 11)
                have b1598 := hb (x 15 1)
                have b1599 := hb (x 15 1 && x 15 11)
                clear * - r1597 b1598 b1599 d1592
                omega
              have d1600 : (x 16 2).toNat = 0 := by
                have r1601 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1602 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e1603 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b1604 := hb (x 15 3)
                have b1605 := hb (x 16 2)
                have b1606 := hb (x 17 13)
                have b1607 := hb (x 18 12)
                clear * - r1601 e1602 e1603 b1604 b1605 b1606 b1607 d1567 d1575 d1563
                omega
              have d1608 : (x 16 10).toNat = 0 := by
                have r1609 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
                have b1610 := hb (x 16 2)
                have b1611 := hb (x 16 10)
                clear * - r1609 b1610 b1611 d1600
                omega
              have r1612 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b1613 := hb (x 11 5)
              have b1614 := hb (x 16 10)
              have b1615 := hb (x 15 1 && x 15 11)
              have b1616 := hb (x 14 2 && x 14 12)
              have b1617 := hb (x 13 3 && x 13 13)
              have b1618 := hb (x 12 4 && x 12 14)
              linarith only [r1612, b1613, b1614, b1615, b1616, b1617, b1618, d1608, d1596, d1482, d1498, d1380, d1392]
            · have f1619 : (x (-1) 4).toNat = 1 := by rw [h1052]; rfl
              have d1620 : (x 3 8).toNat = 0 := by
                have r1621 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1622 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e1623 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e1624 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e1625 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e1626 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e1627 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b1628 := hb (x (-4) 7)
                have b1629 := hb (x (-3) 6)
                have b1630 := hb (x (-2) 5)
                have b1631 := hb (x (-1) 4)
                have b1632 := hb (x 0 11)
                have b1633 := hb (x 1 10)
                have b1634 := hb (x 2 9)
                have b1635 := hb (x 3 8)
                clear * - r1621 e1622 e1623 e1624 e1625 e1626 e1627 b1628 b1629 b1630 b1631 b1632 b1633 b1634 b1635 g14 g11 f1619 d921
                omega
              have d1636 : (x 2 9).toNat = 0 := by
                have r1637 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1638 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e1639 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e1640 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e1641 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e1642 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e1643 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b1644 := hb (x (-4) 7)
                have b1645 := hb (x (-3) 6)
                have b1646 := hb (x (-2) 5)
                have b1647 := hb (x (-1) 4)
                have b1648 := hb (x 0 11)
                have b1649 := hb (x 1 10)
                have b1650 := hb (x 2 9)
                have b1651 := hb (x 3 8)
                clear * - r1637 e1638 e1639 e1640 e1641 e1642 e1643 b1644 b1645 b1646 b1647 b1648 b1649 b1650 b1651 d1620 g14 g11 f1619 d921
                omega
              have d1652 : (x (-3) 6).toNat = 0 := by
                have r1653 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1654 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e1655 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e1656 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e1657 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e1658 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e1659 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b1660 := hb (x (-4) 7)
                have b1661 := hb (x (-3) 6)
                have b1662 := hb (x (-2) 5)
                have b1663 := hb (x (-1) 4)
                have b1664 := hb (x 0 11)
                have b1665 := hb (x 1 10)
                have b1666 := hb (x 2 9)
                have b1667 := hb (x 3 8)
                clear * - r1653 e1654 e1655 e1656 e1657 e1658 e1659 b1660 b1661 b1662 b1663 b1664 b1665 b1666 b1667 d1620 d1636 g14 g11 f1619 d921
                omega
              have d1668 : (x (-4) 7).toNat = 0 := by
                have r1669 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1670 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e1671 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e1672 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e1673 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e1674 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e1675 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b1676 := hb (x (-4) 7)
                have b1677 := hb (x (-3) 6)
                have b1678 := hb (x (-2) 5)
                have b1679 := hb (x (-1) 4)
                have b1680 := hb (x 0 11)
                have b1681 := hb (x 1 10)
                have b1682 := hb (x 2 9)
                have b1683 := hb (x 3 8)
                clear * - r1669 e1670 e1671 e1672 e1673 e1674 e1675 b1676 b1677 b1678 b1679 b1680 b1681 b1682 b1683 d1620 d1636 g14 g11 f1619 d921 d1652
                omega
              have r1684 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r1685 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1686 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e1687 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e1688 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e1689 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e1690 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e1691 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have r1692 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1693 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e1694 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e1695 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e1696 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e1697 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e1698 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have r1699 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1700 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
              have e1701 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
              have e1702 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
              have e1703 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
              have e1704 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
              have e1705 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
              have r1706 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1707 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e1708 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have r1709 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1710 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
              have e1711 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
              have r1712 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r1713 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r1714 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r1715 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r1716 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
              have r1717 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
              have r1718 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
              have r1719 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
              have r1720 := hand2 (x (-1) 4) (x (-1) 8)
              have r1721 := hand1 (x (-5) 8) (x (-5) 12)
              have r1722 := hand1 (x (-6) 9) (x (-6) 13)
              have r1723 := hand2 (x (-1) 2) (x (-1) 8)
              have r1724 := hand1 (x (-7) 8) (x (-7) 14)
              have r1725 := hand2 (x 5 1) (x 5 10)
              have r1726 := hand2 (x 4 2) (x 4 11)
              have r1727 := hand2 (x (-8) 1) (x (-8) 11)
              have r1728 := hand2 (x (-9) 2) (x (-9) 12)
              have r1729 := hand2 (x (-10) 3) (x (-10) 13)
              have r1730 := hand2 (x (-11) 4) (x (-11) 14)
              have r1731 := hand1 (x (-5) 4) (x (-5) 14)
              linarith only [r1684, r1685, e1686, e1687, e1688, e1689, e1690, e1691, r1692, e1693, e1694, e1695, e1696, e1697, e1698, r1699, e1700, e1701, e1702, e1703, e1704, e1705, r1706, e1707, e1708, r1709, e1710, e1711, r1712, r1713, r1714, r1715, r1716, r1717, r1718, r1719, r1720, r1721, r1722, r1723, r1724, r1725, r1726, r1727, r1728, r1729, r1730, r1731, d1668, d1005, d1652, d985, d921, d929, f1619, g5, g8, g10, f481, g12, g13, g15, g17, g24, g25, d925, d989, d1009, d482, d933, g30, g31, g32, g33, g41, d1046, g42, g43, d981, d1001]
          · have f1805 : (x 1 3).toNat = 1 := by rw [h1050]; rfl
            have d1806 : (x 4 12).toNat = 0 := by
              have r1807 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1808 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e1809 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b1810 := hb (x 1 3)
              have b1811 := hb (x 2 2)
              have b1812 := hb (x 3 13)
              have b1813 := hb (x 4 12)
              clear * - r1807 e1808 e1809 b1810 b1811 b1812 b1813 f1805
              omega
            have d1814 : (x 4 1 && x 4 12).toNat = 0 := by
              have r1815 := hand2 (x 4 1) (x 4 12)
              have b1816 := hb (x 4 12)
              have b1817 := hb (x 4 1 && x 4 12)
              clear * - r1815 b1816 b1817 d1806
              omega
            have d1818 : (x 4 4).toNat = 0 := by
              have r1819 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b1820 := hb (x 4 4)
              have b1821 := hb (x 4 12)
              clear * - r1819 b1820 b1821 d1806
              omega
            have d1822 : (x 3 13).toNat = 0 := by
              have r1823 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1824 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e1825 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b1826 := hb (x 1 3)
              have b1827 := hb (x 2 2)
              have b1828 := hb (x 3 13)
              have b1829 := hb (x 4 12)
              clear * - r1823 e1824 e1825 b1826 b1827 b1828 b1829 d1806 f1805
              omega
            have d1830 : (x 2 2).toNat = 0 := by
              have r1831 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1832 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e1833 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b1834 := hb (x 1 3)
              have b1835 := hb (x 2 2)
              have b1836 := hb (x 3 13)
              have b1837 := hb (x 4 12)
              clear * - r1831 e1832 e1833 b1834 b1835 b1836 b1837 d1806 d1822 f1805
              omega
            have d1838 : (x 4 13).toNat = 1 := by
              have r1839 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b1840 := hb (x 2 2)
              have b1841 := hb (x 4 13)
              have b1842 := hb (x 3 1 && x 3 14)
              clear * - r1839 b1840 b1841 b1842 g53 d1830
              omega
            have d1843 : (x 4 1).toNat = 1 := by
              have r1844 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
              have b1845 := hb (x 4 1)
              have b1846 := hb (x 4 13)
              clear * - r1844 b1845 b1846 d1838
              omega
            have d1847 : (x 5 14).toNat = 0 := by
              have r1848 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b1849 := hb (x 4 1)
              have b1850 := hb (x 5 14)
              clear * - r1848 b1849 b1850 d1843
              omega
            have d1851 : (x 5 3 && x 5 14).toNat = 0 := by
              have r1852 := hand2 (x 5 3) (x 5 14)
              have b1853 := hb (x 5 14)
              have b1854 := hb (x 5 3 && x 5 14)
              clear * - r1852 b1853 b1854 d1847
              omega
            have d1855 : (x 5 2).toNat = 0 := by
              have r1856 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b1857 := hb (x 5 2)
              have b1858 := hb (x 5 14)
              clear * - r1856 b1857 b1858 d1847
              omega
            have d1859 : (x 5 12).toNat = 0 := by
              have r1860 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1861 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e1862 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b1863 := hb (x 2 3)
              have b1864 := hb (x 3 2)
              have b1865 := hb (x 4 13)
              have b1866 := hb (x 5 12)
              clear * - r1860 e1861 e1862 b1863 b1864 b1865 b1866 d1838 g16
              omega
            have d1867 : (x 5 4).toNat = 0 := by
              have r1868 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b1869 := hb (x 5 4)
              have b1870 := hb (x 5 12)
              clear * - r1868 b1869 b1870 d1859
              omega
            have d1871 : (x 2 3).toNat = 0 := by
              have r1872 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1873 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e1874 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b1875 := hb (x 2 3)
              have b1876 := hb (x 3 2)
              have b1877 := hb (x 4 13)
              have b1878 := hb (x 5 12)
              clear * - r1872 e1873 e1874 b1875 b1876 b1877 b1878 d1859 d1838 g16
              omega
            have d1879 : (x 2 3 && x 2 14).toNat = 0 := by
              have r1880 := hand1 (x 2 3) (x 2 14)
              have b1881 := hb (x 2 3)
              have b1882 := hb (x 2 3 && x 2 14)
              clear * - r1880 b1881 b1882 d1871
              omega
            have d1883 : (x 5 11).toNat = 1 := by
              have r1884 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b1885 := hb (x 1 4)
              have b1886 := hb (x 5 11)
              have b1887 := hb (x 4 1 && x 4 12)
              have b1888 := hb (x 3 2 && x 3 13)
              have b1889 := hb (x 2 3 && x 2 14)
              clear * - r1884 b1885 b1886 b1887 b1888 b1889 d1814 g51 d1879 d945
              omega
            have d1890 : (x 5 3).toNat = 1 := by
              have r1891 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have b1892 := hb (x 5 3)
              have b1893 := hb (x 5 11)
              clear * - r1891 b1892 b1893 d1883
              omega
            have d1894 : (x 8 12).toNat = 0 := by
              have r1895 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1896 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e1897 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b1898 := hb (x 5 3)
              have b1899 := hb (x 6 2)
              have b1900 := hb (x 7 13)
              have b1901 := hb (x 8 12)
              clear * - r1895 e1896 e1897 b1898 b1899 b1900 b1901 d1890
              omega
            have d1902 : (x 8 1 && x 8 12).toNat = 0 := by
              have r1903 := hand2 (x 8 1) (x 8 12)
              have b1904 := hb (x 8 12)
              have b1905 := hb (x 8 1 && x 8 12)
              clear * - r1903 b1904 b1905 d1894
              omega
            have d1906 : (x 8 4).toNat = 0 := by
              have r1907 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have b1908 := hb (x 8 4)
              have b1909 := hb (x 8 12)
              clear * - r1907 b1908 b1909 d1894
              omega
            have d1910 : (x 7 13).toNat = 0 := by
              have r1911 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1912 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e1913 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b1914 := hb (x 5 3)
              have b1915 := hb (x 6 2)
              have b1916 := hb (x 7 13)
              have b1917 := hb (x 8 12)
              clear * - r1911 e1912 e1913 b1914 b1915 b1916 b1917 d1894 d1890
              omega
            have d1918 : (x 7 2 && x 7 13).toNat = 0 := by
              have r1919 := hand2 (x 7 2) (x 7 13)
              have b1920 := hb (x 7 13)
              have b1921 := hb (x 7 2 && x 7 13)
              clear * - r1919 b1920 b1921 d1910
              omega
            have d1922 : (x 6 1 && x 6 14).toNat = 1 := by
              have r1923 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b1924 := hb (x 5 2)
              have b1925 := hb (x 7 13)
              have b1926 := hb (x 6 1 && x 6 14)
              clear * - r1923 b1924 b1925 b1926 d1910 d1855
              omega
            have d1927 : (x 6 1).toNat = 1 := by
              have r1928 := hand1 (x 6 1) (x 6 14)
              have b1929 := hb (x 6 1)
              have b1930 := hb (x 6 1 && x 6 14)
              clear * - r1928 b1929 b1930 d1922
              omega
            have d1931 : (x 7 14).toNat = 0 := by
              have r1932 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b1933 := hb (x 6 1)
              have b1934 := hb (x 7 14)
              clear * - r1932 b1933 b1934 d1927
              omega
            have d1935 : (x 7 1 && x 7 14).toNat = 0 := by
              have r1936 := hand2 (x 7 1) (x 7 14)
              have b1937 := hb (x 7 14)
              have b1938 := hb (x 7 1 && x 7 14)
              clear * - r1936 b1937 b1938 d1931
              omega
            have d1939 : (x 7 2).toNat = 0 := by
              have r1940 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b1941 := hb (x 7 2)
              have b1942 := hb (x 7 14)
              clear * - r1940 b1941 b1942 d1931
              omega
            have d1943 : (x 6 2).toNat = 0 := by
              have r1944 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1945 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e1946 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b1947 := hb (x 5 3)
              have b1948 := hb (x 6 2)
              have b1949 := hb (x 7 13)
              have b1950 := hb (x 8 12)
              clear * - r1944 e1945 e1946 b1947 b1948 b1949 b1950 d1894 d1910 d1890
              omega
            have d1951 : (x 6 2 && x 6 13).toNat = 0 := by
              have r1952 := hand1 (x 6 2) (x 6 13)
              have b1953 := hb (x 6 2)
              have b1954 := hb (x 6 2 && x 6 13)
              clear * - r1952 b1953 b1954 d1943
              omega
            have d1955 : (x 8 13).toNat = 1 := by
              have r1956 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b1957 := hb (x 6 2)
              have b1958 := hb (x 8 13)
              have b1959 := hb (x 7 1 && x 7 14)
              clear * - r1956 b1957 b1958 b1959 d1935 d1943
              omega
            have d1960 : (x 8 1).toNat = 1 := by
              have r1961 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
              have b1962 := hb (x 8 1)
              have b1963 := hb (x 8 13)
              clear * - r1961 b1962 b1963 d1955
              omega
            have d1964 : (x 9 14).toNat = 0 := by
              have r1965 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b1966 := hb (x 8 1)
              have b1967 := hb (x 9 14)
              clear * - r1965 b1966 b1967 d1960
              omega
            have d1968 : (x 9 3 && x 9 14).toNat = 0 := by
              have r1969 := hand2 (x 9 3) (x 9 14)
              have b1970 := hb (x 9 14)
              have b1971 := hb (x 9 3 && x 9 14)
              clear * - r1969 b1970 b1971 d1964
              omega
            have d1972 : (x 9 2).toNat = 0 := by
              have r1973 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
              have b1974 := hb (x 9 2)
              have b1975 := hb (x 9 14)
              clear * - r1973 b1974 b1975 d1964
              omega
            have d1976 : (x 9 12).toNat = 0 := by
              have r1977 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1978 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e1979 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b1980 := hb (x 6 3)
              have b1981 := hb (x 7 2)
              have b1982 := hb (x 8 13)
              have b1983 := hb (x 9 12)
              clear * - r1977 e1978 e1979 b1980 b1981 b1982 b1983 d1955 d1939
              omega
            have d1984 : (x 9 4).toNat = 0 := by
              have r1985 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
              have b1986 := hb (x 9 4)
              have b1987 := hb (x 9 12)
              clear * - r1985 b1986 b1987 d1976
              omega
            have d1988 : (x 6 3).toNat = 0 := by
              have r1989 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e1990 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e1991 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b1992 := hb (x 6 3)
              have b1993 := hb (x 7 2)
              have b1994 := hb (x 8 13)
              have b1995 := hb (x 9 12)
              clear * - r1989 e1990 e1991 b1992 b1993 b1994 b1995 d1976 d1955 d1939
              omega
            have d1996 : (x 6 3 && x 6 14).toNat = 0 := by
              have r1997 := hand1 (x 6 3) (x 6 14)
              have b1998 := hb (x 6 3)
              have b1999 := hb (x 6 3 && x 6 14)
              clear * - r1997 b1998 b1999 d1988
              omega
            have d2000 : (x 9 11).toNat = 1 := by
              have r2001 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2002 := hb (x 5 4)
              have b2003 := hb (x 9 11)
              have b2004 := hb (x 8 1 && x 8 12)
              have b2005 := hb (x 7 2 && x 7 13)
              have b2006 := hb (x 6 3 && x 6 14)
              clear * - r2001 b2002 b2003 b2004 b2005 b2006 d1902 d1918 d1996 d1867
              omega
            have d2007 : (x 9 3).toNat = 1 := by
              have r2008 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
              have b2009 := hb (x 9 3)
              have b2010 := hb (x 9 11)
              clear * - r2008 b2009 b2010 d2000
              omega
            have d2011 : (x 12 12).toNat = 0 := by
              have r2012 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2013 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e2014 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b2015 := hb (x 9 3)
              have b2016 := hb (x 10 2)
              have b2017 := hb (x 11 13)
              have b2018 := hb (x 12 12)
              clear * - r2012 e2013 e2014 b2015 b2016 b2017 b2018 d2007
              omega
            have d2019 : (x 12 1 && x 12 12).toNat = 0 := by
              have r2020 := hand2 (x 12 1) (x 12 12)
              have b2021 := hb (x 12 12)
              have b2022 := hb (x 12 1 && x 12 12)
              clear * - r2020 b2021 b2022 d2011
              omega
            have d2023 : (x 12 4).toNat = 0 := by
              have r2024 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
              have b2025 := hb (x 12 4)
              have b2026 := hb (x 12 12)
              clear * - r2024 b2025 b2026 d2011
              omega
            have d2027 : (x 11 13).toNat = 0 := by
              have r2028 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2029 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e2030 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b2031 := hb (x 9 3)
              have b2032 := hb (x 10 2)
              have b2033 := hb (x 11 13)
              have b2034 := hb (x 12 12)
              clear * - r2028 e2029 e2030 b2031 b2032 b2033 b2034 d2011 d2007
              omega
            have d2035 : (x 11 2 && x 11 13).toNat = 0 := by
              have r2036 := hand2 (x 11 2) (x 11 13)
              have b2037 := hb (x 11 13)
              have b2038 := hb (x 11 2 && x 11 13)
              clear * - r2036 b2037 b2038 d2027
              omega
            have d2039 : (x 10 1 && x 10 14).toNat = 1 := by
              have r2040 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2041 := hb (x 9 2)
              have b2042 := hb (x 11 13)
              have b2043 := hb (x 10 1 && x 10 14)
              clear * - r2040 b2041 b2042 b2043 d2027 d1972
              omega
            have d2044 : (x 10 14).toNat = 1 := by
              have r2045 := hand2 (x 10 1) (x 10 14)
              have b2046 := hb (x 10 14)
              have b2047 := hb (x 10 1 && x 10 14)
              clear * - r2045 b2046 b2047 d2039
              omega
            have d2048 : (x 9 1).toNat = 0 := by
              have r2049 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2050 := hb (x 9 1)
              have b2051 := hb (x 10 14)
              clear * - r2049 b2050 b2051 d2044
              omega
            have d2052 : (x 9 13).toNat = 0 := by
              have r2053 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
              have b2054 := hb (x 9 1)
              have b2055 := hb (x 9 13)
              clear * - r2053 b2054 b2055 d2048
              omega
            have d2056 : (x 8 1 && x 8 14).toNat = 1 := by
              have r2057 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2058 := hb (x 7 2)
              have b2059 := hb (x 9 13)
              have b2060 := hb (x 8 1 && x 8 14)
              clear * - r2057 b2058 b2059 b2060 d2052 d1939
              omega
            have d2061 : (x 8 14).toNat = 1 := by
              have r2062 := hand2 (x 8 1) (x 8 14)
              have b2063 := hb (x 8 14)
              have b2064 := hb (x 8 1 && x 8 14)
              clear * - r2062 b2063 b2064 d2056
              omega
            have d2065 : (x 7 1).toNat = 0 := by
              have r2066 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2067 := hb (x 7 1)
              have b2068 := hb (x 8 14)
              clear * - r2066 b2067 b2068 d2061
              omega
            have d2069 : (x 7 1 && x 7 12).toNat = 0 := by
              have r2070 := hand1 (x 7 1) (x 7 12)
              have b2071 := hb (x 7 1)
              have b2072 := hb (x 7 1 && x 7 12)
              clear * - r2070 b2071 b2072 d2065
              omega
            have d2073 : (x 8 11).toNat = 1 := by
              have r2074 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2075 := hb (x 4 4)
              have b2076 := hb (x 8 11)
              have b2077 := hb (x 7 1 && x 7 12)
              have b2078 := hb (x 6 2 && x 6 13)
              have b2079 := hb (x 5 3 && x 5 14)
              clear * - r2074 b2075 b2076 b2077 b2078 b2079 d2069 d1951 d1851 d1818
              omega
            have d2080 : (x 8 3).toNat = 1 := by
              have r2081 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
              have b2082 := hb (x 8 3)
              have b2083 := hb (x 8 11)
              clear * - r2081 b2082 b2083 d2073
              omega
            have d2084 : (x 11 12).toNat = 0 := by
              have r2085 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2086 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e2087 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b2088 := hb (x 8 3)
              have b2089 := hb (x 9 2)
              have b2090 := hb (x 10 13)
              have b2091 := hb (x 11 12)
              clear * - r2085 e2086 e2087 b2088 b2089 b2090 b2091 d1972 d2080
              omega
            have d2092 : (x 11 1 && x 11 12).toNat = 0 := by
              have r2093 := hand2 (x 11 1) (x 11 12)
              have b2094 := hb (x 11 12)
              have b2095 := hb (x 11 1 && x 11 12)
              clear * - r2093 b2094 b2095 d2084
              omega
            have d2096 : (x 10 13).toNat = 0 := by
              have r2097 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2098 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e2099 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b2100 := hb (x 8 3)
              have b2101 := hb (x 9 2)
              have b2102 := hb (x 10 13)
              have b2103 := hb (x 11 12)
              clear * - r2097 e2098 e2099 b2100 b2101 b2102 b2103 d2084 d1972 d2080
              omega
            have d2104 : (x 10 2 && x 10 13).toNat = 0 := by
              have r2105 := hand2 (x 10 2) (x 10 13)
              have b2106 := hb (x 10 13)
              have b2107 := hb (x 10 2 && x 10 13)
              clear * - r2105 b2106 b2107 d2096
              omega
            have d2108 : (x 12 11).toNat = 1 := by
              have r2109 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2110 := hb (x 8 4)
              have b2111 := hb (x 12 11)
              have b2112 := hb (x 11 1 && x 11 12)
              have b2113 := hb (x 10 2 && x 10 13)
              have b2114 := hb (x 9 3 && x 9 14)
              clear * - r2109 b2110 b2111 b2112 b2113 b2114 d2092 d2104 d1968 d1906
              omega
            have d2115 : (x 12 3).toNat = 1 := by
              have r2116 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
              have b2117 := hb (x 12 3)
              have b2118 := hb (x 12 11)
              clear * - r2116 b2117 b2118 d2108
              omega
            have d2119 : (x 15 12).toNat = 0 := by
              have r2120 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2121 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e2122 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b2123 := hb (x 12 3)
              have b2124 := hb (x 13 2)
              have b2125 := hb (x 14 13)
              have b2126 := hb (x 15 12)
              clear * - r2120 e2121 e2122 b2123 b2124 b2125 b2126 d2115
              omega
            have d2127 : (x 15 1 && x 15 12).toNat = 0 := by
              have r2128 := hand2 (x 15 1) (x 15 12)
              have b2129 := hb (x 15 12)
              have b2130 := hb (x 15 1 && x 15 12)
              clear * - r2128 b2129 b2130 d2119
              omega
            have d2131 : (x 14 13).toNat = 0 := by
              have r2132 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2133 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e2134 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b2135 := hb (x 12 3)
              have b2136 := hb (x 13 2)
              have b2137 := hb (x 14 13)
              have b2138 := hb (x 15 12)
              clear * - r2132 e2133 e2134 b2135 b2136 b2137 b2138 d2119 d2115
              omega
            have d2139 : (x 14 2 && x 14 13).toNat = 0 := by
              have r2140 := hand2 (x 14 2) (x 14 13)
              have b2141 := hb (x 14 13)
              have b2142 := hb (x 14 2 && x 14 13)
              clear * - r2140 b2141 b2142 d2131
              omega
            have d2143 : (x 13 2).toNat = 0 := by
              have r2144 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2145 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e2146 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b2147 := hb (x 12 3)
              have b2148 := hb (x 13 2)
              have b2149 := hb (x 14 13)
              have b2150 := hb (x 15 12)
              clear * - r2144 e2145 e2146 b2147 b2148 b2149 b2150 d2119 d2131 d2115
              omega
            have d2151 : (x 10 1).toNat = 1 := by
              have r2152 := hand1 (x 10 1) (x 10 14)
              have b2153 := hb (x 10 1)
              have b2154 := hb (x 10 1 && x 10 14)
              clear * - r2152 b2153 b2154 d2039
              omega
            have d2155 : (x 11 14).toNat = 0 := by
              have r2156 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2157 := hb (x 10 1)
              have b2158 := hb (x 11 14)
              clear * - r2156 b2157 b2158 d2151
              omega
            have d2159 : (x 11 1 && x 11 14).toNat = 0 := by
              have r2160 := hand2 (x 11 1) (x 11 14)
              have b2161 := hb (x 11 14)
              have b2162 := hb (x 11 1 && x 11 14)
              clear * - r2160 b2161 b2162 d2155
              omega
            have d2163 : (x 11 2).toNat = 0 := by
              have r2164 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
              have b2165 := hb (x 11 2)
              have b2166 := hb (x 11 14)
              clear * - r2164 b2165 b2166 d2155
              omega
            have d2167 : (x 10 2).toNat = 0 := by
              have r2168 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2169 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e2170 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b2171 := hb (x 9 3)
              have b2172 := hb (x 10 2)
              have b2173 := hb (x 11 13)
              have b2174 := hb (x 12 12)
              clear * - r2168 e2169 e2170 b2171 b2172 b2173 b2174 d2011 d2027 d2007
              omega
            have d2175 : (x 12 13).toNat = 1 := by
              have r2176 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2177 := hb (x 10 2)
              have b2178 := hb (x 12 13)
              have b2179 := hb (x 11 1 && x 11 14)
              clear * - r2176 b2177 b2178 b2179 d2159 d2167
              omega
            have d2180 : (x 12 1).toNat = 1 := by
              have r2181 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
              have b2182 := hb (x 12 1)
              have b2183 := hb (x 12 13)
              clear * - r2181 b2182 b2183 d2175
              omega
            have d2184 : (x 13 14).toNat = 0 := by
              have r2185 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2186 := hb (x 12 1)
              have b2187 := hb (x 13 14)
              clear * - r2185 b2186 b2187 d2180
              omega
            have d2188 : (x 13 1 && x 13 14).toNat = 0 := by
              have r2189 := hand2 (x 13 1) (x 13 14)
              have b2190 := hb (x 13 14)
              have b2191 := hb (x 13 1 && x 13 14)
              clear * - r2189 b2190 b2191 d2184
              omega
            have d2192 : (x 12 2).toNat = 1 := by
              have r2193 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2194 := hb (x 12 2)
              have b2195 := hb (x 14 13)
              have b2196 := hb (x 13 1 && x 13 14)
              clear * - r2193 b2194 b2195 b2196 d2131 d2188
              omega
            have d2197 : (x 14 12).toNat = 0 := by
              have r2198 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2199 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e2200 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b2201 := hb (x 11 3)
              have b2202 := hb (x 12 2)
              have b2203 := hb (x 13 13)
              have b2204 := hb (x 14 12)
              clear * - r2198 e2199 e2200 b2201 b2202 b2203 b2204 d2192
              omega
            have d2205 : (x 14 4).toNat = 0 := by
              have r2206 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
              have b2207 := hb (x 14 4)
              have b2208 := hb (x 14 12)
              clear * - r2206 b2207 b2208 d2197
              omega
            have d2209 : (x 14 4 && x 14 14).toNat = 0 := by
              have r2210 := hand1 (x 14 4) (x 14 14)
              have b2211 := hb (x 14 4)
              have b2212 := hb (x 14 4 && x 14 14)
              clear * - r2210 b2211 b2212 d2205
              omega
            have d2213 : (x 13 13).toNat = 0 := by
              have r2214 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2215 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e2216 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b2217 := hb (x 11 3)
              have b2218 := hb (x 12 2)
              have b2219 := hb (x 13 13)
              have b2220 := hb (x 14 12)
              clear * - r2214 e2215 e2216 b2217 b2218 b2219 b2220 d2197 d2192
              omega
            have d2221 : (x 13 5).toNat = 0 := by
              have r2222 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
              have b2223 := hb (x 13 5)
              have b2224 := hb (x 13 13)
              clear * - r2222 b2223 b2224 d2213
              omega
            have d2225 : (x 13 3 && x 13 14).toNat = 0 := by
              have r2226 := hand2 (x 13 3) (x 13 14)
              have b2227 := hb (x 13 14)
              have b2228 := hb (x 13 3 && x 13 14)
              clear * - r2226 b2227 b2228 d2184
              omega
            have d2229 : (x 16 11).toNat = 1 := by
              have r2230 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2231 := hb (x 12 4)
              have b2232 := hb (x 16 11)
              have b2233 := hb (x 15 1 && x 15 12)
              have b2234 := hb (x 14 2 && x 14 13)
              have b2235 := hb (x 13 3 && x 13 14)
              clear * - r2230 b2231 b2232 b2233 b2234 b2235 d2127 d2139 d2225 d2023
              omega
            have d2236 : (x 16 3).toNat = 1 := by
              have r2237 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
              have b2238 := hb (x 16 3)
              have b2239 := hb (x 16 11)
              clear * - r2237 b2238 b2239 d2229
              omega
            have d2240 : (x 19 12).toNat = 0 := by
              have r2241 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2242 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e2243 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b2244 := hb (x 16 3)
              have b2245 := hb (x 17 2)
              have b2246 := hb (x 18 13)
              have b2247 := hb (x 19 12)
              clear * - r2241 e2242 e2243 b2244 b2245 b2246 b2247 d2236
              omega
            have d2248 : (x 18 13).toNat = 0 := by
              have r2249 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2250 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e2251 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b2252 := hb (x 16 3)
              have b2253 := hb (x 17 2)
              have b2254 := hb (x 18 13)
              have b2255 := hb (x 19 12)
              clear * - r2249 e2250 e2251 b2252 b2253 b2254 b2255 d2240 d2236
              omega
            have d2256 : (x 17 2).toNat = 0 := by
              have r2257 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2258 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e2259 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b2260 := hb (x 16 3)
              have b2261 := hb (x 17 2)
              have b2262 := hb (x 18 13)
              have b2263 := hb (x 19 12)
              clear * - r2257 e2258 e2259 b2260 b2261 b2262 b2263 d2240 d2248 d2236
              omega
            have d2264 : (x 13 12).toNat = 0 := by
              have r2265 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2266 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e2267 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b2268 := hb (x 10 3)
              have b2269 := hb (x 11 2)
              have b2270 := hb (x 12 13)
              have b2271 := hb (x 13 12)
              clear * - r2265 e2266 e2267 b2268 b2269 b2270 b2271 d2175 d2163
              omega
            have d2272 : (x 13 4).toNat = 0 := by
              have r2273 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
              have b2274 := hb (x 13 4)
              have b2275 := hb (x 13 12)
              clear * - r2273 b2274 b2275 d2264
              omega
            have d2276 : (x 10 3).toNat = 0 := by
              have r2277 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2278 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e2279 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b2280 := hb (x 10 3)
              have b2281 := hb (x 11 2)
              have b2282 := hb (x 12 13)
              have b2283 := hb (x 13 12)
              clear * - r2277 e2278 e2279 b2280 b2281 b2282 b2283 d2264 d2175 d2163
              omega
            have d2284 : (x 10 3 && x 10 14).toNat = 0 := by
              have r2285 := hand1 (x 10 3) (x 10 14)
              have b2286 := hb (x 10 3)
              have b2287 := hb (x 10 3 && x 10 14)
              clear * - r2285 b2286 b2287 d2276
              omega
            have d2288 : (x 13 11).toNat = 1 := by
              have r2289 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2290 := hb (x 9 4)
              have b2291 := hb (x 13 11)
              have b2292 := hb (x 12 1 && x 12 12)
              have b2293 := hb (x 11 2 && x 11 13)
              have b2294 := hb (x 10 3 && x 10 14)
              clear * - r2289 b2290 b2291 b2292 b2293 b2294 d2019 d2035 d2284 d1984
              omega
            have d2295 : (x 13 3).toNat = 1 := by
              have r2296 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
              have b2297 := hb (x 13 3)
              have b2298 := hb (x 13 11)
              clear * - r2296 b2297 b2298 d2288
              omega
            have d2299 : (x 16 12).toNat = 0 := by
              have r2300 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2301 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e2302 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b2303 := hb (x 13 3)
              have b2304 := hb (x 14 2)
              have b2305 := hb (x 15 13)
              have b2306 := hb (x 16 12)
              clear * - r2300 e2301 e2302 b2303 b2304 b2305 b2306 d2295
              omega
            have d2307 : (x 16 1 && x 16 12).toNat = 0 := by
              have r2308 := hand2 (x 16 1) (x 16 12)
              have b2309 := hb (x 16 12)
              have b2310 := hb (x 16 1 && x 16 12)
              clear * - r2308 b2309 b2310 d2299
              omega
            have d2311 : (x 16 2 && x 16 12).toNat = 0 := by
              have r2312 := hand2 (x 16 2) (x 16 12)
              have b2313 := hb (x 16 12)
              have b2314 := hb (x 16 2 && x 16 12)
              clear * - r2312 b2313 b2314 d2299
              omega
            have d2315 : (x 15 13).toNat = 0 := by
              have r2316 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2317 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e2318 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b2319 := hb (x 13 3)
              have b2320 := hb (x 14 2)
              have b2321 := hb (x 15 13)
              have b2322 := hb (x 16 12)
              clear * - r2316 e2317 e2318 b2319 b2320 b2321 b2322 d2299 d2295
              omega
            have d2323 : (x 15 2 && x 15 13).toNat = 0 := by
              have r2324 := hand2 (x 15 2) (x 15 13)
              have b2325 := hb (x 15 13)
              have b2326 := hb (x 15 2 && x 15 13)
              clear * - r2324 b2325 b2326 d2315
              omega
            have d2327 : (x 15 3 && x 15 13).toNat = 0 := by
              have r2328 := hand2 (x 15 3) (x 15 13)
              have b2329 := hb (x 15 13)
              have b2330 := hb (x 15 3 && x 15 13)
              clear * - r2328 b2329 b2330 d2315
              omega
            have d2331 : (x 14 1 && x 14 14).toNat = 1 := by
              have r2332 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2333 := hb (x 13 2)
              have b2334 := hb (x 15 13)
              have b2335 := hb (x 14 1 && x 14 14)
              clear * - r2332 b2333 b2334 b2335 d2315 d2143
              omega
            have d2336 : (x 14 1).toNat = 1 := by
              have r2337 := hand1 (x 14 1) (x 14 14)
              have b2338 := hb (x 14 1)
              have b2339 := hb (x 14 1 && x 14 14)
              clear * - r2337 b2338 b2339 d2331
              omega
            have d2340 : (x 15 14).toNat = 0 := by
              have r2341 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2342 := hb (x 14 1)
              have b2343 := hb (x 15 14)
              clear * - r2341 b2342 b2343 d2336
              omega
            have d2344 : (x 15 1 && x 15 14).toNat = 0 := by
              have r2345 := hand2 (x 15 1) (x 15 14)
              have b2346 := hb (x 15 14)
              have b2347 := hb (x 15 1 && x 15 14)
              clear * - r2345 b2346 b2347 d2340
              omega
            have d2348 : (x 15 2).toNat = 0 := by
              have r2349 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
              have b2350 := hb (x 15 2)
              have b2351 := hb (x 15 14)
              clear * - r2349 b2350 b2351 d2340
              omega
            have d2352 : (x 14 2).toNat = 0 := by
              have r2353 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2354 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e2355 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b2356 := hb (x 13 3)
              have b2357 := hb (x 14 2)
              have b2358 := hb (x 15 13)
              have b2359 := hb (x 16 12)
              clear * - r2353 e2354 e2355 b2356 b2357 b2358 b2359 d2299 d2315 d2295
              omega
            have d2360 : (x 16 13).toNat = 1 := by
              have r2361 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2362 := hb (x 14 2)
              have b2363 := hb (x 16 13)
              have b2364 := hb (x 15 1 && x 15 14)
              clear * - r2361 b2362 b2363 b2364 d2344 d2352
              omega
            have d2365 : (x 17 12).toNat = 0 := by
              have r2366 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2367 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e2368 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b2369 := hb (x 14 3)
              have b2370 := hb (x 15 2)
              have b2371 := hb (x 16 13)
              have b2372 := hb (x 17 12)
              clear * - r2366 e2367 e2368 b2369 b2370 b2371 b2372 d2360 d2348
              omega
            have d2373 : (x 14 3).toNat = 0 := by
              have r2374 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2375 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e2376 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b2377 := hb (x 14 3)
              have b2378 := hb (x 15 2)
              have b2379 := hb (x 16 13)
              have b2380 := hb (x 17 12)
              clear * - r2374 e2375 e2376 b2377 b2378 b2379 b2380 d2365 d2360 d2348
              omega
            have d2381 : (x 14 3 && x 14 14).toNat = 0 := by
              have r2382 := hand1 (x 14 3) (x 14 14)
              have b2383 := hb (x 14 3)
              have b2384 := hb (x 14 3 && x 14 14)
              clear * - r2382 b2383 b2384 d2373
              omega
            have d2385 : (x 17 11).toNat = 1 := by
              have r2386 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2387 := hb (x 13 4)
              have b2388 := hb (x 17 11)
              have b2389 := hb (x 16 1 && x 16 12)
              have b2390 := hb (x 15 2 && x 15 13)
              have b2391 := hb (x 14 3 && x 14 14)
              clear * - r2386 b2387 b2388 b2389 b2390 b2391 d2307 d2323 d2381 d2272
              omega
            have d2392 : (x 17 3).toNat = 1 := by
              have r2393 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
              have b2394 := hb (x 17 3)
              have b2395 := hb (x 17 11)
              clear * - r2393 b2394 b2395 d2385
              omega
            have d2396 : (x 20 12).toNat = 0 := by
              have r2397 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2398 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e2399 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b2400 := hb (x 17 3)
              have b2401 := hb (x 18 2)
              have b2402 := hb (x 19 13)
              have b2403 := hb (x 20 12)
              clear * - r2397 e2398 e2399 b2400 b2401 b2402 b2403 d2392
              omega
            have d2404 : (x 19 13).toNat = 0 := by
              have r2405 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2406 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e2407 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b2408 := hb (x 17 3)
              have b2409 := hb (x 18 2)
              have b2410 := hb (x 19 13)
              have b2411 := hb (x 20 12)
              clear * - r2405 e2406 e2407 b2408 b2409 b2410 b2411 d2396 d2392
              omega
            have d2412 : (x 18 1 && x 18 14).toNat = 1 := by
              have r2413 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2414 := hb (x 17 2)
              have b2415 := hb (x 19 13)
              have b2416 := hb (x 18 1 && x 18 14)
              clear * - r2413 b2414 b2415 b2416 d2404 d2256
              omega
            have d2417 : (x 18 14).toNat = 1 := by
              have r2418 := hand2 (x 18 1) (x 18 14)
              have b2419 := hb (x 18 14)
              have b2420 := hb (x 18 1 && x 18 14)
              clear * - r2418 b2419 b2420 d2412
              omega
            have d2421 : (x 17 1).toNat = 0 := by
              have r2422 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2423 := hb (x 17 1)
              have b2424 := hb (x 18 14)
              clear * - r2422 b2423 b2424 d2417
              omega
            have d2425 : (x 17 1 && x 17 11).toNat = 0 := by
              have r2426 := hand1 (x 17 1) (x 17 11)
              have b2427 := hb (x 17 1)
              have b2428 := hb (x 17 1 && x 17 11)
              clear * - r2426 b2427 b2428 d2421
              omega
            have d2429 : (x 18 2).toNat = 0 := by
              have r2430 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2431 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e2432 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b2433 := hb (x 17 3)
              have b2434 := hb (x 18 2)
              have b2435 := hb (x 19 13)
              have b2436 := hb (x 20 12)
              clear * - r2430 e2431 e2432 b2433 b2434 b2435 b2436 d2396 d2404 d2392
              omega
            have d2437 : (x 18 10).toNat = 0 := by
              have r2438 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
              have b2439 := hb (x 18 2)
              have b2440 := hb (x 18 10)
              clear * - r2438 b2439 b2440 d2429
              omega
            have r2441 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b2442 := hb (x 13 5)
            have b2443 := hb (x 18 10)
            have b2444 := hb (x 17 1 && x 17 11)
            have b2445 := hb (x 16 2 && x 16 12)
            have b2446 := hb (x 15 3 && x 15 13)
            have b2447 := hb (x 14 4 && x 14 14)
            linarith only [r2441, b2442, b2443, b2444, b2445, b2446, b2447, d2437, d2425, d2311, d2327, d2209, d2221]
      · have f2448 : (x 1 1).toNat = 1 := by rw [h488]; rfl
        have d2449 : (x 2 14).toNat = 0 := by
          have r2450 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2451 := hb (x 1 1)
          have b2452 := hb (x 2 14)
          clear * - r2450 b2451 b2452 f2448
          omega
        have d2453 : (x 2 1 && x 2 14).toNat = 0 := by
          have r2454 := hand2 (x 2 1) (x 2 14)
          have b2455 := hb (x 2 14)
          have b2456 := hb (x 2 1 && x 2 14)
          clear * - r2454 b2455 b2456 d2449
          omega
        have d2457 : (x 2 2).toNat = 0 := by
          have r2458 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b2459 := hb (x 2 2)
          have b2460 := hb (x 2 14)
          clear * - r2458 b2459 b2460 d2449
          omega
        have d2461 : (x 4 13).toNat = 1 := by
          have r2462 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2463 := hb (x 2 2)
          have b2464 := hb (x 4 13)
          have b2465 := hb (x 3 1 && x 3 14)
          clear * - r2462 b2463 b2464 b2465 g53 d2457
          omega
        have d2466 : (x 4 1).toNat = 1 := by
          have r2467 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b2468 := hb (x 4 1)
          have b2469 := hb (x 4 13)
          clear * - r2467 b2468 b2469 d2461
          omega
        have d2470 : (x 5 14).toNat = 0 := by
          have r2471 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2472 := hb (x 4 1)
          have b2473 := hb (x 5 14)
          clear * - r2471 b2472 b2473 d2466
          omega
        have d2474 : (x 5 1 && x 5 14).toNat = 0 := by
          have r2475 := hand2 (x 5 1) (x 5 14)
          have b2476 := hb (x 5 14)
          have b2477 := hb (x 5 1 && x 5 14)
          clear * - r2475 b2476 b2477 d2470
          omega
        have d2478 : (x 5 2).toNat = 0 := by
          have r2479 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b2480 := hb (x 5 2)
          have b2481 := hb (x 5 14)
          clear * - r2479 b2480 b2481 d2470
          omega
        have d2482 : (x 3 13).toNat = 1 := by
          have r2483 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2484 := hb (x 1 2)
          have b2485 := hb (x 3 13)
          have b2486 := hb (x 2 1 && x 2 14)
          clear * - r2483 b2484 b2485 b2486 d2453 g12
          omega
        have d2487 : (x 3 1).toNat = 1 := by
          have r2488 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b2489 := hb (x 3 1)
          have b2490 := hb (x 3 13)
          clear * - r2488 b2489 b2490 d2482
          omega
        have d2491 : (x 4 14).toNat = 0 := by
          have r2492 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2493 := hb (x 3 1)
          have b2494 := hb (x 4 14)
          clear * - r2492 b2493 b2494 d2487
          omega
        have d2495 : (x 4 1 && x 4 14).toNat = 0 := by
          have r2496 := hand2 (x 4 1) (x 4 14)
          have b2497 := hb (x 4 14)
          have b2498 := hb (x 4 1 && x 4 14)
          clear * - r2496 b2497 b2498 d2491
          omega
        have d2499 : (x 5 13).toNat = 1 := by
          have r2500 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2501 := hb (x 3 2)
          have b2502 := hb (x 5 13)
          have b2503 := hb (x 4 1 && x 4 14)
          clear * - r2500 b2501 b2502 b2503 d2495 g16
          omega
        have d2504 : (x 5 1).toNat = 1 := by
          have r2505 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
          have b2506 := hb (x 5 1)
          have b2507 := hb (x 5 13)
          clear * - r2505 b2506 b2507 d2499
          omega
        have d2508 : (x 6 14).toNat = 0 := by
          have r2509 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2510 := hb (x 5 1)
          have b2511 := hb (x 6 14)
          clear * - r2509 b2510 b2511 d2504
          omega
        have d2512 : (x 6 1 && x 6 14).toNat = 0 := by
          have r2513 := hand2 (x 6 1) (x 6 14)
          have b2514 := hb (x 6 14)
          have b2515 := hb (x 6 1 && x 6 14)
          clear * - r2513 b2514 b2515 d2508
          omega
        have d2516 : (x 7 13).toNat = 1 := by
          have r2517 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2518 := hb (x 5 2)
          have b2519 := hb (x 7 13)
          have b2520 := hb (x 6 1 && x 6 14)
          clear * - r2517 b2518 b2519 b2520 d2512 d2478
          omega
        have d2521 : (x 7 1).toNat = 1 := by
          have r2522 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b2523 := hb (x 7 1)
          have b2524 := hb (x 7 13)
          clear * - r2522 b2523 b2524 d2516
          omega
        have d2525 : (x 8 14).toNat = 0 := by
          have r2526 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2527 := hb (x 7 1)
          have b2528 := hb (x 8 14)
          clear * - r2526 b2527 b2528 d2521
          omega
        have d2529 : (x 8 1 && x 8 14).toNat = 0 := by
          have r2530 := hand2 (x 8 1) (x 8 14)
          have b2531 := hb (x 8 14)
          have b2532 := hb (x 8 1 && x 8 14)
          clear * - r2530 b2531 b2532 d2525
          omega
        have d2533 : (x 8 2).toNat = 0 := by
          have r2534 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
          have b2535 := hb (x 8 2)
          have b2536 := hb (x 8 14)
          clear * - r2534 b2535 b2536 d2525
          omega
        have d2537 : (x 6 2).toNat = 0 := by
          have r2538 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
          have b2539 := hb (x 6 2)
          have b2540 := hb (x 6 14)
          clear * - r2538 b2539 b2540 d2508
          omega
        have d2541 : (x 4 2).toNat = 0 := by
          have r2542 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b2543 := hb (x 4 2)
          have b2544 := hb (x 4 14)
          clear * - r2542 b2543 b2544 d2491
          omega
        have d2545 : (x 6 13).toNat = 1 := by
          have r2546 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2547 := hb (x 4 2)
          have b2548 := hb (x 6 13)
          have b2549 := hb (x 5 1 && x 5 14)
          clear * - r2546 b2547 b2548 b2549 d2474 d2541
          omega
        have d2550 : (x 6 1).toNat = 1 := by
          have r2551 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b2552 := hb (x 6 1)
          have b2553 := hb (x 6 13)
          clear * - r2551 b2552 b2553 d2545
          omega
        have d2554 : (x 7 14).toNat = 0 := by
          have r2555 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2556 := hb (x 6 1)
          have b2557 := hb (x 7 14)
          clear * - r2555 b2556 b2557 d2550
          omega
        have d2558 : (x 7 1 && x 7 14).toNat = 0 := by
          have r2559 := hand2 (x 7 1) (x 7 14)
          have b2560 := hb (x 7 14)
          have b2561 := hb (x 7 1 && x 7 14)
          clear * - r2559 b2560 b2561 d2554
          omega
        have d2562 : (x 8 13).toNat = 1 := by
          have r2563 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2564 := hb (x 6 2)
          have b2565 := hb (x 8 13)
          have b2566 := hb (x 7 1 && x 7 14)
          clear * - r2563 b2564 b2565 b2566 d2558 d2537
          omega
        have d2567 : (x 8 1).toNat = 1 := by
          have r2568 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b2569 := hb (x 8 1)
          have b2570 := hb (x 8 13)
          clear * - r2568 b2569 b2570 d2562
          omega
        have d2571 : (x 9 14).toNat = 0 := by
          have r2572 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2573 := hb (x 8 1)
          have b2574 := hb (x 9 14)
          clear * - r2572 b2573 b2574 d2567
          omega
        have d2575 : (x 9 1 && x 9 14).toNat = 0 := by
          have r2576 := hand2 (x 9 1) (x 9 14)
          have b2577 := hb (x 9 14)
          have b2578 := hb (x 9 1 && x 9 14)
          clear * - r2576 b2577 b2578 d2571
          omega
        have d2579 : (x 10 13).toNat = 1 := by
          have r2580 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2581 := hb (x 8 2)
          have b2582 := hb (x 10 13)
          have b2583 := hb (x 9 1 && x 9 14)
          clear * - r2580 b2581 b2582 b2583 d2575 d2533
          omega
        have d2584 : (x 10 1).toNat = 1 := by
          have r2585 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b2586 := hb (x 10 1)
          have b2587 := hb (x 10 13)
          clear * - r2585 b2586 b2587 d2579
          omega
        have d2588 : (x 11 14).toNat = 0 := by
          have r2589 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2590 := hb (x 10 1)
          have b2591 := hb (x 11 14)
          clear * - r2589 b2590 b2591 d2584
          omega
        have d2592 : (x 11 1 && x 11 14).toNat = 0 := by
          have r2593 := hand2 (x 11 1) (x 11 14)
          have b2594 := hb (x 11 14)
          have b2595 := hb (x 11 1 && x 11 14)
          clear * - r2593 b2594 b2595 d2588
          omega
        have d2596 : (x 11 2).toNat = 0 := by
          have r2597 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b2598 := hb (x 11 2)
          have b2599 := hb (x 11 14)
          clear * - r2597 b2598 b2599 d2588
          omega
        have d2600 : (x 9 2).toNat = 0 := by
          have r2601 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b2602 := hb (x 9 2)
          have b2603 := hb (x 9 14)
          clear * - r2601 b2602 b2603 d2571
          omega
        have d2604 : (x 7 2).toNat = 0 := by
          have r2605 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b2606 := hb (x 7 2)
          have b2607 := hb (x 7 14)
          clear * - r2605 b2606 b2607 d2554
          omega
        have d2608 : (x 9 13).toNat = 1 := by
          have r2609 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2610 := hb (x 7 2)
          have b2611 := hb (x 9 13)
          have b2612 := hb (x 8 1 && x 8 14)
          clear * - r2609 b2610 b2611 b2612 d2529 d2604
          omega
        have d2613 : (x 9 1).toNat = 1 := by
          have r2614 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b2615 := hb (x 9 1)
          have b2616 := hb (x 9 13)
          clear * - r2614 b2615 b2616 d2608
          omega
        have d2617 : (x 10 14).toNat = 0 := by
          have r2618 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2619 := hb (x 9 1)
          have b2620 := hb (x 10 14)
          clear * - r2618 b2619 b2620 d2613
          omega
        have d2621 : (x 10 1 && x 10 14).toNat = 0 := by
          have r2622 := hand2 (x 10 1) (x 10 14)
          have b2623 := hb (x 10 14)
          have b2624 := hb (x 10 1 && x 10 14)
          clear * - r2622 b2623 b2624 d2617
          omega
        have d2625 : (x 11 13).toNat = 1 := by
          have r2626 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2627 := hb (x 9 2)
          have b2628 := hb (x 11 13)
          have b2629 := hb (x 10 1 && x 10 14)
          clear * - r2626 b2627 b2628 b2629 d2621 d2600
          omega
        have d2630 : (x 11 1).toNat = 1 := by
          have r2631 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
          have b2632 := hb (x 11 1)
          have b2633 := hb (x 11 13)
          clear * - r2631 b2632 b2633 d2625
          omega
        have d2634 : (x 12 14).toNat = 0 := by
          have r2635 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2636 := hb (x 11 1)
          have b2637 := hb (x 12 14)
          clear * - r2635 b2636 b2637 d2630
          omega
        have d2638 : (x 12 1 && x 12 14).toNat = 0 := by
          have r2639 := hand2 (x 12 1) (x 12 14)
          have b2640 := hb (x 12 14)
          have b2641 := hb (x 12 1 && x 12 14)
          clear * - r2639 b2640 b2641 d2634
          omega
        have d2642 : (x 13 13).toNat = 1 := by
          have r2643 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2644 := hb (x 11 2)
          have b2645 := hb (x 13 13)
          have b2646 := hb (x 12 1 && x 12 14)
          clear * - r2643 b2644 b2645 b2646 d2638 d2596
          omega
        have d2647 : (x 13 1).toNat = 1 := by
          have r2648 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have b2649 := hb (x 13 1)
          have b2650 := hb (x 13 13)
          clear * - r2648 b2649 b2650 d2642
          omega
        have d2651 : (x 14 14).toNat = 0 := by
          have r2652 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2653 := hb (x 13 1)
          have b2654 := hb (x 14 14)
          clear * - r2652 b2653 b2654 d2647
          omega
        have d2655 : (x 14 1 && x 14 14).toNat = 0 := by
          have r2656 := hand2 (x 14 1) (x 14 14)
          have b2657 := hb (x 14 14)
          have b2658 := hb (x 14 1 && x 14 14)
          clear * - r2656 b2657 b2658 d2651
          omega
        have d2659 : (x 14 3 && x 14 14).toNat = 0 := by
          have r2660 := hand2 (x 14 3) (x 14 14)
          have b2661 := hb (x 14 14)
          have b2662 := hb (x 14 3 && x 14 14)
          clear * - r2660 b2661 b2662 d2651
          omega
        have d2663 : (x 14 2).toNat = 0 := by
          have r2664 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
          have b2665 := hb (x 14 2)
          have b2666 := hb (x 14 14)
          clear * - r2664 b2665 b2666 d2651
          omega
        have d2667 : (x 12 2).toNat = 0 := by
          have r2668 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
          have b2669 := hb (x 12 2)
          have b2670 := hb (x 12 14)
          clear * - r2668 b2669 b2670 d2634
          omega
        have d2671 : (x 10 2).toNat = 0 := by
          have r2672 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
          have b2673 := hb (x 10 2)
          have b2674 := hb (x 10 14)
          clear * - r2672 b2673 b2674 d2617
          omega
        have d2675 : (x 12 13).toNat = 1 := by
          have r2676 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2677 := hb (x 10 2)
          have b2678 := hb (x 12 13)
          have b2679 := hb (x 11 1 && x 11 14)
          clear * - r2676 b2677 b2678 b2679 d2592 d2671
          omega
        have d2680 : (x 12 1).toNat = 1 := by
          have r2681 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b2682 := hb (x 12 1)
          have b2683 := hb (x 12 13)
          clear * - r2681 b2682 b2683 d2675
          omega
        have d2684 : (x 13 14).toNat = 0 := by
          have r2685 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2686 := hb (x 12 1)
          have b2687 := hb (x 13 14)
          clear * - r2685 b2686 b2687 d2680
          omega
        have d2688 : (x 13 1 && x 13 14).toNat = 0 := by
          have r2689 := hand2 (x 13 1) (x 13 14)
          have b2690 := hb (x 13 14)
          have b2691 := hb (x 13 1 && x 13 14)
          clear * - r2689 b2690 b2691 d2684
          omega
        have d2692 : (x 14 13).toNat = 1 := by
          have r2693 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2694 := hb (x 12 2)
          have b2695 := hb (x 14 13)
          have b2696 := hb (x 13 1 && x 13 14)
          clear * - r2693 b2694 b2695 b2696 d2688 d2667
          omega
        have d2697 : (x 14 1).toNat = 1 := by
          have r2698 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
          have b2699 := hb (x 14 1)
          have b2700 := hb (x 14 13)
          clear * - r2698 b2699 b2700 d2692
          omega
        have d2701 : (x 15 14).toNat = 0 := by
          have r2702 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2703 := hb (x 14 1)
          have b2704 := hb (x 15 14)
          clear * - r2702 b2703 b2704 d2697
          omega
        have d2705 : (x 15 1 && x 15 14).toNat = 0 := by
          have r2706 := hand2 (x 15 1) (x 15 14)
          have b2707 := hb (x 15 14)
          have b2708 := hb (x 15 1 && x 15 14)
          clear * - r2706 b2707 b2708 d2701
          omega
        have d2709 : (x 16 13).toNat = 1 := by
          have r2710 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2711 := hb (x 14 2)
          have b2712 := hb (x 16 13)
          have b2713 := hb (x 15 1 && x 15 14)
          clear * - r2710 b2711 b2712 b2713 d2705 d2663
          omega
        have d2714 : (x 16 1).toNat = 1 := by
          have r2715 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
          have b2716 := hb (x 16 1)
          have b2717 := hb (x 16 13)
          clear * - r2715 b2716 b2717 d2709
          omega
        have d2718 : (x 17 14).toNat = 0 := by
          have r2719 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2720 := hb (x 16 1)
          have b2721 := hb (x 17 14)
          clear * - r2719 b2720 b2721 d2714
          omega
        have d2722 : (x 17 2).toNat = 0 := by
          have r2723 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
          have b2724 := hb (x 17 2)
          have b2725 := hb (x 17 14)
          clear * - r2723 b2724 b2725 d2718
          omega
        have d2726 : (x 15 2).toNat = 0 := by
          have r2727 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b2728 := hb (x 15 2)
          have b2729 := hb (x 15 14)
          clear * - r2727 b2728 b2729 d2701
          omega
        have d2730 : (x 15 2 && x 15 13).toNat = 0 := by
          have r2731 := hand1 (x 15 2) (x 15 13)
          have b2732 := hb (x 15 2)
          have b2733 := hb (x 15 2 && x 15 13)
          clear * - r2731 b2732 b2733 d2726
          omega
        have d2734 : (x 13 2).toNat = 0 := by
          have r2735 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b2736 := hb (x 13 2)
          have b2737 := hb (x 13 14)
          clear * - r2735 b2736 b2737 d2684
          omega
        have d2738 : (x 15 13).toNat = 1 := by
          have r2739 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2740 := hb (x 13 2)
          have b2741 := hb (x 15 13)
          have b2742 := hb (x 14 1 && x 14 14)
          clear * - r2739 b2740 b2741 b2742 d2655 d2734
          omega
        have d2743 : (x 15 1).toNat = 1 := by
          have r2744 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
          have b2745 := hb (x 15 1)
          have b2746 := hb (x 15 13)
          clear * - r2744 b2745 b2746 d2738
          omega
        have d2747 : (x 16 14).toNat = 0 := by
          have r2748 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2749 := hb (x 15 1)
          have b2750 := hb (x 16 14)
          clear * - r2748 b2749 b2750 d2743
          omega
        have d2751 : (x 16 1 && x 16 14).toNat = 0 := by
          have r2752 := hand2 (x 16 1) (x 16 14)
          have b2753 := hb (x 16 14)
          have b2754 := hb (x 16 1 && x 16 14)
          clear * - r2752 b2753 b2754 d2747
          omega
        have d2755 : (x 17 13).toNat = 1 := by
          have r2756 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2757 := hb (x 15 2)
          have b2758 := hb (x 17 13)
          have b2759 := hb (x 16 1 && x 16 14)
          clear * - r2756 b2757 b2758 b2759 d2751 d2726
          omega
        have d2760 : (x 17 1).toNat = 1 := by
          have r2761 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
          have b2762 := hb (x 17 1)
          have b2763 := hb (x 17 13)
          clear * - r2761 b2762 b2763 d2755
          omega
        have d2764 : (x 18 14).toNat = 0 := by
          have r2765 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2766 := hb (x 17 1)
          have b2767 := hb (x 18 14)
          clear * - r2765 b2766 b2767 d2760
          omega
        have d2768 : (x 18 1 && x 18 14).toNat = 0 := by
          have r2769 := hand2 (x 18 1) (x 18 14)
          have b2770 := hb (x 18 14)
          have b2771 := hb (x 18 1 && x 18 14)
          clear * - r2769 b2770 b2771 d2764
          omega
        have d2772 : (x 19 13).toNat = 1 := by
          have r2773 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b2774 := hb (x 17 2)
          have b2775 := hb (x 19 13)
          have b2776 := hb (x 18 1 && x 18 14)
          clear * - r2773 b2774 b2775 b2776 d2768 d2722
          omega
        have d2777 : (x 18 2).toNat = 0 := by
          have r2778 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
          have b2779 := hb (x 18 2)
          have b2780 := hb (x 18 14)
          clear * - r2778 b2779 b2780 d2764
          omega
        have d2781 : (x 20 12).toNat = 0 := by
          have r2782 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2783 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e2784 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b2785 := hb (x 17 3)
          have b2786 := hb (x 18 2)
          have b2787 := hb (x 19 13)
          have b2788 := hb (x 20 12)
          clear * - r2782 e2783 e2784 b2785 b2786 b2787 b2788 d2772 d2777
          omega
        have d2789 : (x 17 3).toNat = 0 := by
          have r2790 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2791 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e2792 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b2793 := hb (x 17 3)
          have b2794 := hb (x 18 2)
          have b2795 := hb (x 19 13)
          have b2796 := hb (x 20 12)
          clear * - r2790 e2791 e2792 b2793 b2794 b2795 b2796 d2781 d2772 d2777
          omega
        have d2797 : (x 17 11).toNat = 0 := by
          have r2798 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b2799 := hb (x 17 3)
          have b2800 := hb (x 17 11)
          clear * - r2798 b2799 b2800 d2789
          omega
        have d2801 : (x 16 12).toNat = 0 := by
          have r2802 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2803 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e2804 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b2805 := hb (x 13 3)
          have b2806 := hb (x 14 2)
          have b2807 := hb (x 15 13)
          have b2808 := hb (x 16 12)
          clear * - r2802 e2803 e2804 b2805 b2806 b2807 b2808 d2738 d2663
          omega
        have d2809 : (x 16 1 && x 16 12).toNat = 0 := by
          have r2810 := hand2 (x 16 1) (x 16 12)
          have b2811 := hb (x 16 12)
          have b2812 := hb (x 16 1 && x 16 12)
          clear * - r2810 b2811 b2812 d2801
          omega
        have d2813 : (x 13 12).toNat = 0 := by
          have r2814 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e2815 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e2816 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b2817 := hb (x 10 3)
          have b2818 := hb (x 11 2)
          have b2819 := hb (x 12 13)
          have b2820 := hb (x 13 12)
          clear * - r2814 e2815 e2816 b2817 b2818 b2819 b2820 d2675 d2596
          omega
        have d2821 : (x 13 4).toNat = 0 := by
          have r2822 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b2823 := hb (x 13 4)
          have b2824 := hb (x 13 12)
          clear * - r2822 b2823 b2824 d2813
          omega
        have r2825 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b2826 := hb (x 13 4)
        have b2827 := hb (x 17 11)
        have b2828 := hb (x 16 1 && x 16 12)
        have b2829 := hb (x 15 2 && x 15 13)
        have b2830 := hb (x 14 3 && x 14 14)
        linarith only [r2825, b2826, b2827, b2828, b2829, b2830, d2797, d2809, d2730, d2659, d2821]
    · have f2831 : (x 0 13).toNat = 1 := by rw [h486]; rfl
      have d2832 : (x 1 12).toNat = 0 := by
        have r2833 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e2834 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e2835 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b2836 := hb (x (-2) 3)
        have b2837 := hb (x (-1) 2)
        have b2838 := hb (x 0 13)
        have b2839 := hb (x 1 12)
        clear * - r2833 e2834 e2835 b2836 b2837 b2838 b2839 f2831
        omega
      have d2840 : (x (-1) 2).toNat = 0 := by
        have r2841 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e2842 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e2843 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b2844 := hb (x (-2) 3)
        have b2845 := hb (x (-1) 2)
        have b2846 := hb (x 0 13)
        have b2847 := hb (x 1 12)
        clear * - r2841 e2842 e2843 b2844 b2845 b2846 b2847 d2832 f2831
        omega
      have d2848 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
        have r2849 := hand1 (x (-1) 2) (x (-1) 12)
        have b2850 := hb (x (-1) 2)
        have b2851 := hb (x (-1) 2 && x (-1) 12)
        clear * - r2849 b2850 b2851 d2840
        omega
      have d2852 : (x (-2) 3).toNat = 0 := by
        have r2853 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e2854 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e2855 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b2856 := hb (x (-2) 3)
        have b2857 := hb (x (-1) 2)
        have b2858 := hb (x 0 13)
        have b2859 := hb (x 1 12)
        clear * - r2853 e2854 e2855 b2856 b2857 b2858 b2859 d2832 f2831 d2840
        omega
      have d2860 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
        have r2861 := hand1 (x (-2) 3) (x (-2) 13)
        have b2862 := hb (x (-2) 3)
        have b2863 := hb (x (-2) 3 && x (-2) 13)
        clear * - r2861 b2862 b2863 d2852
        omega
      have r2864 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2865 := hb (x (-4) 5)
      have b2866 := hb (x 1 10)
      have b2867 := hb (x 0 1 && x 0 11)
      have b2868 := hb (x (-1) 2 && x (-1) 12)
      have b2869 := hb (x (-2) 3 && x (-2) 13)
      have b2870 := hb (x (-3) 4 && x (-3) 14)
      linarith only [r2864, b2865, b2866, b2867, b2868, b2869, b2870, g14, g44, d2848, d2860, g45, g2]
  · have f2871 : (x 0 7).toNat = 1 := by rw [h480]; rfl
    have d2872 : (x 7 8).toNat = 0 := by
      have r2873 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2874 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e2875 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e2876 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e2877 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e2878 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e2879 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b2880 := hb (x 0 7)
      have b2881 := hb (x 1 6)
      have b2882 := hb (x 2 5)
      have b2883 := hb (x 3 4)
      have b2884 := hb (x 4 11)
      have b2885 := hb (x 5 10)
      have b2886 := hb (x 6 9)
      have b2887 := hb (x 7 8)
      clear * - r2873 e2874 e2875 e2876 e2877 e2878 e2879 b2880 b2881 b2882 b2883 b2884 b2885 b2886 b2887 g17 g13 f2871
      omega
    have d2888 : (x 6 9).toNat = 0 := by
      have r2889 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2890 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e2891 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e2892 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e2893 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e2894 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e2895 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b2896 := hb (x 0 7)
      have b2897 := hb (x 1 6)
      have b2898 := hb (x 2 5)
      have b2899 := hb (x 3 4)
      have b2900 := hb (x 4 11)
      have b2901 := hb (x 5 10)
      have b2902 := hb (x 6 9)
      have b2903 := hb (x 7 8)
      clear * - r2889 e2890 e2891 e2892 e2893 e2894 e2895 b2896 b2897 b2898 b2899 b2900 b2901 b2902 b2903 d2872 g17 g13 f2871
      omega
    have d2904 : (x 5 10).toNat = 0 := by
      have r2905 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2906 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e2907 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e2908 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e2909 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e2910 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e2911 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b2912 := hb (x 0 7)
      have b2913 := hb (x 1 6)
      have b2914 := hb (x 2 5)
      have b2915 := hb (x 3 4)
      have b2916 := hb (x 4 11)
      have b2917 := hb (x 5 10)
      have b2918 := hb (x 6 9)
      have b2919 := hb (x 7 8)
      clear * - r2905 e2906 e2907 e2908 e2909 e2910 e2911 b2912 b2913 b2914 b2915 b2916 b2917 b2918 b2919 d2872 d2888 g17 g13 f2871
      omega
    have d2920 : (x 5 1 && x 5 10).toNat = 0 := by
      have r2921 := hand2 (x 5 1) (x 5 10)
      have b2922 := hb (x 5 10)
      have b2923 := hb (x 5 1 && x 5 10)
      clear * - r2921 b2922 b2923 d2904
      omega
    have d2924 : (x 4 11).toNat = 0 := by
      have r2925 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2926 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e2927 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e2928 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e2929 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e2930 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e2931 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b2932 := hb (x 0 7)
      have b2933 := hb (x 1 6)
      have b2934 := hb (x 2 5)
      have b2935 := hb (x 3 4)
      have b2936 := hb (x 4 11)
      have b2937 := hb (x 5 10)
      have b2938 := hb (x 6 9)
      have b2939 := hb (x 7 8)
      clear * - r2925 e2926 e2927 e2928 e2929 e2930 e2931 b2932 b2933 b2934 b2935 b2936 b2937 b2938 b2939 d2872 d2888 d2904 g17 g13 f2871
      omega
    have d2940 : (x 4 1 && x 4 11).toNat = 0 := by
      have r2941 := hand2 (x 4 1) (x 4 11)
      have b2942 := hb (x 4 11)
      have b2943 := hb (x 4 1 && x 4 11)
      clear * - r2941 b2942 b2943 d2924
      omega
    have d2944 : (x 2 3 && x 2 13).toNat = 1 := by
      have r2945 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2946 := hb (x 0 5)
      have b2947 := hb (x 5 10)
      have b2948 := hb (x 4 1 && x 4 11)
      have b2949 := hb (x 3 2 && x 3 12)
      have b2950 := hb (x 2 3 && x 2 13)
      have b2951 := hb (x 1 4 && x 1 14)
      clear * - r2945 b2946 b2947 b2948 b2949 b2950 b2951 d2904 d2940 g46 g47 g9
      omega
    have d2952 : (x 2 3).toNat = 1 := by
      have r2953 := hand1 (x 2 3) (x 2 13)
      have b2954 := hb (x 2 3)
      have b2955 := hb (x 2 3 && x 2 13)
      clear * - r2953 b2954 b2955 d2944
      omega
    have d2956 : (x 5 12).toNat = 0 := by
      have r2957 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2958 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e2959 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b2960 := hb (x 2 3)
      have b2961 := hb (x 3 2)
      have b2962 := hb (x 4 13)
      have b2963 := hb (x 5 12)
      clear * - r2957 e2958 e2959 b2960 b2961 b2962 b2963 g16 d2952
      omega
    have d2964 : (x 5 2 && x 5 12).toNat = 0 := by
      have r2965 := hand2 (x 5 2) (x 5 12)
      have b2966 := hb (x 5 12)
      have b2967 := hb (x 5 2 && x 5 12)
      clear * - r2965 b2966 b2967 d2956
      omega
    have d2968 : (x 5 4).toNat = 0 := by
      have r2969 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b2970 := hb (x 5 4)
      have b2971 := hb (x 5 12)
      clear * - r2969 b2970 b2971 d2956
      omega
    have d2972 : (x 4 13).toNat = 0 := by
      have r2973 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2974 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e2975 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b2976 := hb (x 2 3)
      have b2977 := hb (x 3 2)
      have b2978 := hb (x 4 13)
      have b2979 := hb (x 5 12)
      clear * - r2973 e2974 e2975 b2976 b2977 b2978 b2979 d2956 g16 d2952
      omega
    have d2980 : (x 4 3 && x 4 13).toNat = 0 := by
      have r2981 := hand2 (x 4 3) (x 4 13)
      have b2982 := hb (x 4 13)
      have b2983 := hb (x 4 3 && x 4 13)
      clear * - r2981 b2982 b2983 d2972
      omega
    have d2984 : (x 4 5).toNat = 0 := by
      have r2985 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
      have b2986 := hb (x 4 5)
      have b2987 := hb (x 4 13)
      clear * - r2985 b2986 b2987 d2972
      omega
    have d2988 : (x 2 2).toNat = 1 := by
      have r2989 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2990 := hb (x 2 2)
      have b2991 := hb (x 4 13)
      have b2992 := hb (x 3 1 && x 3 14)
      clear * - r2989 b2990 b2991 b2992 d2972 g53
      omega
    have d2993 : (x 2 14).toNat = 1 := by
      have r2994 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b2995 := hb (x 2 2)
      have b2996 := hb (x 2 14)
      clear * - r2994 b2995 b2996 d2988
      omega
    have d2997 : (x 1 1).toNat = 0 := by
      have r2998 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2999 := hb (x 1 1)
      have b3000 := hb (x 2 14)
      clear * - r2998 b2999 b3000 d2993
      omega
    have d3001 : (x 1 13).toNat = 0 := by
      have r3002 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b3003 := hb (x 1 1)
      have b3004 := hb (x 1 13)
      clear * - r3002 b3003 b3004 d2997
      omega
    have d3005 : (x 1 5).toNat = 0 := by
      have r3006 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b3007 := hb (x 1 5)
      have b3008 := hb (x 1 13)
      clear * - r3006 b3007 b3008 d3001
      omega
    have d3009 : (x 1 9).toNat = 0 := by
      have r3010 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b3011 := hb (x 1 1)
      have b3012 := hb (x 1 9)
      clear * - r3010 b3011 b3012 d2997
      omega
    have d3013 : (x 4 2 && x 4 11).toNat = 0 := by
      have r3014 := hand2 (x 4 2) (x 4 11)
      have b3015 := hb (x 4 11)
      have b3016 := hb (x 4 2 && x 4 11)
      clear * - r3014 b3015 b3016 d2924
      omega
    have d3017 : (x 2 4 && x 2 13).toNat = 1 := by
      have r3018 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b3019 := hb (x 0 6)
      have b3020 := hb (x 6 9)
      have b3021 := hb (x 5 1 && x 5 10)
      have b3022 := hb (x 4 2 && x 4 11)
      have b3023 := hb (x 3 3 && x 3 12)
      have b3024 := hb (x 2 4 && x 2 13)
      have b3025 := hb (x 1 5 && x 1 14)
      clear * - r3018 b3019 b3020 b3021 b3022 b3023 b3024 b3025 d2888 d2920 d3013 g41 g42 g10
      omega
    have d3026 : (x 2 4).toNat = 1 := by
      have r3027 := hand1 (x 2 4) (x 2 13)
      have b3028 := hb (x 2 4)
      have b3029 := hb (x 2 4 && x 2 13)
      clear * - r3027 b3028 b3029 d3017
      omega
    have d3030 : (x 2 12).toNat = 1 := by
      have r3031 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b3032 := hb (x 2 4)
      have b3033 := hb (x 2 12)
      clear * - r3031 b3032 b3033 d3026
      omega
    have d3034 : (x (-1) 3).toNat = 0 := by
      have r3035 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3036 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e3037 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b3038 := hb (x (-1) 3)
      have b3039 := hb (x 0 2)
      have b3040 := hb (x 1 13)
      have b3041 := hb (x 2 12)
      clear * - r3035 e3036 e3037 b3038 b3039 b3040 b3041 d3030 d3001 g7
      omega
    have d3042 : (x (-1) 2 && x (-1) 3).toNat = 0 := by
      have r3043 := hand2 (x (-1) 2) (x (-1) 3)
      have b3044 := hb (x (-1) 3)
      have b3045 := hb (x (-1) 2 && x (-1) 3)
      clear * - r3043 b3044 b3045 d3034
      omega
    have d3046 : (x (-1) 11).toNat = 0 := by
      have r3047 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b3048 := hb (x (-1) 3)
      have b3049 := hb (x (-1) 11)
      clear * - r3047 b3048 b3049 d3034
      omega
    have d3050 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
      have r3051 := hand2 (x (-1) 2) (x (-1) 11)
      have b3052 := hb (x (-1) 11)
      have b3053 := hb (x (-1) 2 && x (-1) 11)
      clear * - r3051 b3052 b3053 d3046
      omega
    have d3054 : (x (-2) 3 && x (-2) 12).toNat = 1 := by
      have r3055 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b3056 := hb (x (-5) 6)
      have b3057 := hb (x 1 9)
      have b3058 := hb (x 0 1 && x 0 10)
      have b3059 := hb (x (-1) 2 && x (-1) 11)
      have b3060 := hb (x (-2) 3 && x (-2) 12)
      have b3061 := hb (x (-3) 4 && x (-3) 13)
      have b3062 := hb (x (-4) 5 && x (-4) 14)
      clear * - r3055 b3056 b3057 b3058 b3059 b3060 b3061 b3062 d3009 g38 d3050 g39 g40 g1
      omega
    have d3063 : (x (-2) 12).toNat = 1 := by
      have r3064 := hand2 (x (-2) 3) (x (-2) 12)
      have b3065 := hb (x (-2) 12)
      have b3066 := hb (x (-2) 3 && x (-2) 12)
      clear * - r3064 b3065 b3066 d3054
      omega
    have d3067 : (x (-3) 13).toNat = 0 := by
      have r3068 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3069 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e3070 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b3071 := hb (x (-5) 3)
      have b3072 := hb (x (-4) 2)
      have b3073 := hb (x (-3) 13)
      have b3074 := hb (x (-2) 12)
      clear * - r3068 e3069 e3070 b3071 b3072 b3073 b3074 d3063
      omega
    have d3075 : (x (-3) 5).toNat = 0 := by
      have r3076 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have b3077 := hb (x (-3) 5)
      have b3078 := hb (x (-3) 13)
      clear * - r3076 b3077 b3078 d3067
      omega
    have d3079 : (x (-3) 5 && x (-3) 12).toNat = 0 := by
      have r3080 := hand1 (x (-3) 5) (x (-3) 12)
      have b3081 := hb (x (-3) 5)
      have b3082 := hb (x (-3) 5 && x (-3) 12)
      clear * - r3080 b3081 b3082 d3075
      omega
    have d3083 : (x (-4) 2).toNat = 0 := by
      have r3084 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3085 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e3086 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b3087 := hb (x (-5) 3)
      have b3088 := hb (x (-4) 2)
      have b3089 := hb (x (-3) 13)
      have b3090 := hb (x (-2) 12)
      clear * - r3084 e3085 e3086 b3087 b3088 b3089 b3090 d3063 d3067
      omega
    have d3091 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
      have r3092 := hand1 (x (-4) 2) (x (-4) 13)
      have b3093 := hb (x (-4) 2)
      have b3094 := hb (x (-4) 2 && x (-4) 13)
      clear * - r3092 b3093 b3094 d3083
      omega
    have d3095 : (x (-4) 10).toNat = 0 := by
      have r3096 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
      have b3097 := hb (x (-4) 2)
      have b3098 := hb (x (-4) 10)
      clear * - r3096 b3097 b3098 d3083
      omega
    have d3099 : (x (-5) 3).toNat = 0 := by
      have r3100 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3101 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e3102 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b3103 := hb (x (-5) 3)
      have b3104 := hb (x (-4) 2)
      have b3105 := hb (x (-3) 13)
      have b3106 := hb (x (-2) 12)
      clear * - r3100 e3101 e3102 b3103 b3104 b3105 b3106 d3063 d3067 d3083
      omega
    have d3107 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
      have r3108 := hand1 (x (-5) 3) (x (-5) 14)
      have b3109 := hb (x (-5) 3)
      have b3110 := hb (x (-5) 3 && x (-5) 14)
      clear * - r3108 b3109 b3110 d3099
      omega
    have d3111 : (x (-5) 11).toNat = 0 := by
      have r3112 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b3113 := hb (x (-5) 3)
      have b3114 := hb (x (-5) 11)
      clear * - r3112 b3113 b3114 d3099
      omega
    have d3115 : (x (-2) 3).toNat = 1 := by
      have r3116 := hand1 (x (-2) 3) (x (-2) 12)
      have b3117 := hb (x (-2) 3)
      have b3118 := hb (x (-2) 3 && x (-2) 12)
      clear * - r3116 b3117 b3118 d3054
      omega
    have d3119 : (x 1 12).toNat = 0 := by
      have r3120 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3121 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e3122 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b3123 := hb (x (-2) 3)
      have b3124 := hb (x (-1) 2)
      have b3125 := hb (x 0 13)
      have b3126 := hb (x 1 12)
      clear * - r3120 e3121 e3122 b3123 b3124 b3125 b3126 d3115
      omega
    have d3127 : (x 0 13).toNat = 0 := by
      have r3128 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3129 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e3130 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b3131 := hb (x (-2) 3)
      have b3132 := hb (x (-1) 2)
      have b3133 := hb (x 0 13)
      have b3134 := hb (x 1 12)
      clear * - r3128 e3129 e3130 b3131 b3132 b3133 b3134 d3119 d3115
      omega
    have d3135 : (x (-1) 2).toNat = 0 := by
      have r3136 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3137 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e3138 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b3139 := hb (x (-2) 3)
      have b3140 := hb (x (-1) 2)
      have b3141 := hb (x 0 13)
      have b3142 := hb (x 1 12)
      clear * - r3136 e3137 e3138 b3139 b3140 b3141 b3142 d3119 d3127 d3115
      omega
    have d3143 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
      have r3144 := hand1 (x (-1) 2) (x (-1) 12)
      have b3145 := hb (x (-1) 2)
      have b3146 := hb (x (-1) 2 && x (-1) 12)
      clear * - r3144 b3145 b3146 d3135
      omega
    have d3147 : (x (-2) 3 && x (-2) 13).toNat = 1 := by
      have r3148 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b3149 := hb (x (-4) 5)
      have b3150 := hb (x 1 10)
      have b3151 := hb (x 0 1 && x 0 11)
      have b3152 := hb (x (-1) 2 && x (-1) 12)
      have b3153 := hb (x (-2) 3 && x (-2) 13)
      have b3154 := hb (x (-3) 4 && x (-3) 14)
      clear * - r3148 b3149 b3150 b3151 b3152 b3153 b3154 g14 g44 d3143 g45 g2
      omega
    have d3155 : (x (-2) 13).toNat = 1 := by
      have r3156 := hand2 (x (-2) 3) (x (-2) 13)
      have b3157 := hb (x (-2) 13)
      have b3158 := hb (x (-2) 3 && x (-2) 13)
      clear * - r3156 b3157 b3158 d3147
      omega
    have d3159 : (x (-2) 1).toNat = 1 := by
      have r3160 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b3161 := hb (x (-2) 1)
      have b3162 := hb (x (-2) 13)
      clear * - r3160 b3161 b3162 d3155
      omega
    have d3163 : (x (-1) 14).toNat = 0 := by
      have r3164 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b3165 := hb (x (-2) 1)
      have b3166 := hb (x (-1) 14)
      clear * - r3164 b3165 b3166 d3159
      omega
    have d3167 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r3168 := hand2 (x (-1) 1) (x (-1) 14)
      have b3169 := hb (x (-1) 14)
      have b3170 := hb (x (-1) 1 && x (-1) 14)
      clear * - r3168 b3169 b3170 d3163
      omega
    have d3171 : (x (-2) 2).toNat = 1 := by
      have r3172 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b3173 := hb (x (-2) 2)
      have b3174 := hb (x 0 13)
      have b3175 := hb (x (-1) 1 && x (-1) 14)
      clear * - r3172 b3173 b3174 b3175 d3127 d3167
      omega
    have d3176 : (x (-2) 14).toNat = 1 := by
      have r3177 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
      have b3178 := hb (x (-2) 2)
      have b3179 := hb (x (-2) 14)
      clear * - r3177 b3178 b3179 d3171
      omega
    have d3180 : (x (-3) 1).toNat = 0 := by
      have r3181 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b3182 := hb (x (-3) 1)
      have b3183 := hb (x (-2) 14)
      clear * - r3181 b3182 b3183 d3176
      omega
    have d3184 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
      have r3185 := hand1 (x (-3) 1) (x (-3) 12)
      have b3186 := hb (x (-3) 1)
      have b3187 := hb (x (-3) 1 && x (-3) 12)
      clear * - r3185 b3186 b3187 d3180
      omega
    have d3188 : (x (-6) 4).toNat = 1 := by
      have r3189 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b3190 := hb (x (-6) 4)
      have b3191 := hb (x (-2) 11)
      have b3192 := hb (x (-3) 1 && x (-3) 12)
      have b3193 := hb (x (-4) 2 && x (-4) 13)
      have b3194 := hb (x (-5) 3 && x (-5) 14)
      clear * - r3189 b3190 b3191 b3192 b3193 b3194 g4 d3184 d3091 d3107
      omega
    have d3195 : (x (-6) 12).toNat = 1 := by
      have r3196 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have b3197 := hb (x (-6) 4)
      have b3198 := hb (x (-6) 12)
      clear * - r3196 b3197 b3198 d3188
      omega
    have d3199 : (x (-7) 13).toNat = 0 := by
      have r3200 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3201 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e3202 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b3203 := hb (x (-9) 3)
      have b3204 := hb (x (-8) 2)
      have b3205 := hb (x (-7) 13)
      have b3206 := hb (x (-6) 12)
      clear * - r3200 e3201 e3202 b3203 b3204 b3205 b3206 d3195
      omega
    have d3207 : (x (-7) 8 && x (-7) 13).toNat = 0 := by
      have r3208 := hand2 (x (-7) 8) (x (-7) 13)
      have b3209 := hb (x (-7) 13)
      have b3210 := hb (x (-7) 8 && x (-7) 13)
      clear * - r3208 b3209 b3210 d3199
      omega
    have d3211 : (x (-7) 5).toNat = 0 := by
      have r3212 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b3213 := hb (x (-7) 5)
      have b3214 := hb (x (-7) 13)
      clear * - r3212 b3213 b3214 d3199
      omega
    have d3215 : (x (-8) 2).toNat = 0 := by
      have r3216 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3217 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e3218 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b3219 := hb (x (-9) 3)
      have b3220 := hb (x (-8) 2)
      have b3221 := hb (x (-7) 13)
      have b3222 := hb (x (-6) 12)
      clear * - r3216 e3217 e3218 b3219 b3220 b3221 b3222 d3195 d3199
      omega
    have d3223 : (x (-8) 10).toNat = 0 := by
      have r3224 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have b3225 := hb (x (-8) 2)
      have b3226 := hb (x (-8) 10)
      clear * - r3224 b3225 b3226 d3215
      omega
    have d3227 : (x (-8) 1 && x (-8) 10).toNat = 0 := by
      have r3228 := hand2 (x (-8) 1) (x (-8) 10)
      have b3229 := hb (x (-8) 10)
      have b3230 := hb (x (-8) 1 && x (-8) 10)
      clear * - r3228 b3229 b3230 d3223
      omega
    have d3231 : (x (-8) 9 && x (-8) 10).toNat = 0 := by
      have r3232 := hand2 (x (-8) 9) (x (-8) 10)
      have b3233 := hb (x (-8) 10)
      have b3234 := hb (x (-8) 9 && x (-8) 10)
      clear * - r3232 b3233 b3234 d3223
      omega
    have d3235 : (x (-9) 3).toNat = 0 := by
      have r3236 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3237 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e3238 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b3239 := hb (x (-9) 3)
      have b3240 := hb (x (-8) 2)
      have b3241 := hb (x (-7) 13)
      have b3242 := hb (x (-6) 12)
      clear * - r3236 e3237 e3238 b3239 b3240 b3241 b3242 d3195 d3199 d3215
      omega
    have d3243 : (x (-9) 11).toNat = 0 := by
      have r3244 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
      have b3245 := hb (x (-9) 3)
      have b3246 := hb (x (-9) 11)
      clear * - r3244 b3245 b3246 d3235
      omega
    have d3247 : (x (-9) 2 && x (-9) 11).toNat = 0 := by
      have r3248 := hand2 (x (-9) 2) (x (-9) 11)
      have b3249 := hb (x (-9) 11)
      have b3250 := hb (x (-9) 2 && x (-9) 11)
      clear * - r3248 b3249 b3250 d3243
      omega
    have d3251 : (x (-9) 10 && x (-9) 11).toNat = 0 := by
      have r3252 := hand2 (x (-9) 10) (x (-9) 11)
      have b3253 := hb (x (-9) 11)
      have b3254 := hb (x (-9) 10 && x (-9) 11)
      clear * - r3252 b3253 b3254 d3243
      omega
    have d3255 : (x (-3) 9).toNat = 0 := by
      have r3256 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
      have b3257 := hb (x (-3) 1)
      have b3258 := hb (x (-3) 9)
      clear * - r3256 b3257 b3258 d3180
      omega
    have d3259 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
      have r3260 := hand1 (x (-1) 2) (x (-1) 7)
      have b3261 := hb (x (-1) 2)
      have b3262 := hb (x (-1) 2 && x (-1) 7)
      clear * - r3260 b3261 b3262 d3135
      omega
    have d3263 : (x 2 5).toNat = 0 := by
      have r3264 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3265 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e3266 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e3267 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e3268 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e3269 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e3270 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b3271 := hb (x 0 7)
      have b3272 := hb (x 1 6)
      have b3273 := hb (x 2 5)
      have b3274 := hb (x 3 4)
      have b3275 := hb (x 4 11)
      have b3276 := hb (x 5 10)
      have b3277 := hb (x 6 9)
      have b3278 := hb (x 7 8)
      clear * - r3264 e3265 e3266 e3267 e3268 e3269 e3270 b3271 b3272 b3273 b3274 b3275 b3276 b3277 b3278 d2872 d2888 d2904 d2924 g17 g13 f2871
      omega
    have d3279 : (x (-2) 8).toNat = 0 := by
      have r3280 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e3281 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e3282 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e3283 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e3284 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e3285 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e3286 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have b3287 := hb (x (-9) 7)
      have b3288 := hb (x (-8) 6)
      have b3289 := hb (x (-7) 5)
      have b3290 := hb (x (-6) 4)
      have b3291 := hb (x (-5) 11)
      have b3292 := hb (x (-4) 10)
      have b3293 := hb (x (-3) 9)
      have b3294 := hb (x (-2) 8)
      clear * - r3280 e3281 e3282 e3283 e3284 e3285 e3286 b3287 b3288 b3289 b3290 b3291 b3292 b3293 b3294 d3255 d3095 d3111 d3188 d3211
      omega
    have d3295 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
      have r3296 := hand2 (x (-2) 3) (x (-2) 8)
      have b3297 := hb (x (-2) 8)
      have b3298 := hb (x (-2) 3 && x (-2) 8)
      clear * - r3296 b3297 b3298 d3279
      omega
    have r3299 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r3300 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r3301 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3302 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
    have e3303 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
    have e3304 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
    have e3305 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
    have e3306 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
    have e3307 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
    have r3308 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e3309 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e3310 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e3311 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e3312 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e3313 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e3314 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have r3315 : 1 ≤ (x 1 1).toNat + (x 0 1 && x 0 2).toNat + (x (-1) 2 && x (-1) 3).toNat + (x (-2) 3 && x (-2) 4).toNat + (x (-3) 4 && x (-3) 5).toNat + (x (-4) 5 && x (-4) 6).toNat + (x (-5) 6 && x (-5) 7).toNat + (x (-6) 7 && x (-6) 8).toNat + (x (-7) 8 && x (-7) 9).toNat + (x (-8) 9 && x (-8) 10).toNat + (x (-9) 10 && x (-9) 11).toNat + (x (-10) 11 && x (-10) 12).toNat + (x (-11) 12 && x (-11) 13).toNat + (x (-12) 13 && x (-12) 14).toNat + (x (-13) 14).toNat := by have q := hcov1 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r3316 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r3317 : 1 ≤ (x 2 7).toNat + (x 1 1 && x 1 8).toNat + (x 0 2 && x 0 9).toNat + (x (-1) 3 && x (-1) 10).toNat + (x (-2) 4 && x (-2) 11).toNat + (x (-3) 5 && x (-3) 12).toNat + (x (-4) 6 && x (-4) 13).toNat + (x (-5) 7 && x (-5) 14).toNat + (x (-6) 8).toNat := by have q := hcov7 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r3318 : 1 ≤ (x (-7) 9).toNat + (x (-8) 1 && x (-8) 10).toNat + (x (-9) 2 && x (-9) 11).toNat + (x (-10) 3 && x (-10) 12).toNat + (x (-11) 4 && x (-11) 13).toNat + (x (-12) 5 && x (-12) 14).toNat + (x (-13) 6).toNat := by have q := hcov9 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r3319 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r3320 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r3321 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
    have r3322 := hand2 (x (-2) 3) (x (-2) 4)
    have r3323 := hand1 (x (-7) 8) (x (-7) 9)
    have r3324 := hand1 (x (-10) 11) (x (-10) 12)
    have r3325 := hand1 (x (-11) 12) (x (-11) 13)
    have r3326 := hand1 (x (-12) 13) (x (-12) 14)
    have r3327 := hand1 (x (-8) 9) (x (-8) 14)
    have r3328 := hand1 (x (-4) 6) (x (-4) 13)
    have r3329 := hand1 (x (-5) 7) (x (-5) 14)
    have r3330 := hand2 (x (-10) 3) (x (-10) 12)
    have r3331 := hand1 (x (-11) 4) (x (-11) 13)
    have r3332 := hand1 (x (-12) 5) (x (-12) 14)
    have r3333 := hand2 (x 6 1) (x 6 11)
    have r3334 := hand2 (x (-12) 1) (x (-12) 14)
    linarith only [r3299, r3300, r3301, e3302, e3303, e3304, e3305, e3306, e3307, r3308, e3309, e3310, e3311, e3312, e3313, e3314, r3315, r3316, r3317, r3318, r3319, r3320, r3321, r3322, r3323, r3324, r3325, r3326, r3327, r3328, r3329, r3330, r3331, r3332, r3333, r3334, d3243, d3223, g0, g1, g2, g3, d3075, d3115, d3135, d3034, g6, g7, d2997, d3005, d3263, g18, d2984, d2968, g19, d3042, g20, g21, g22, g23, d3231, d3251, d476, d3259, d3295, g26, g27, g28, g29, d3207, g34, g35, g36, g37, d3079, d3227, d3247, d2964, d2980, g48]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b00000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 7).toNat = 0)
    (g1 : (x (-5) 6).toNat = 0)
    (g2 : (x (-4) 5).toNat = 0)
    (g3 : (x (-3) 4).toNat = 0)
    (g4 : (x (-2) 11).toNat = 0)
    (g5 : (x (-1) 10).toNat = 0)
    (g6 : (x 0 1).toNat = 1)
    (g7 : (x 0 2).toNat = 0)
    (g8 : (x 0 3).toNat = 0)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 6).toNat = 0)
    (g11 : (x 0 11).toNat = 0)
    (g12 : (x 1 2).toNat = 0)
    (g13 : (x 1 6).toNat = 0)
    (g14 : (x 1 10).toNat = 0)
    (g15 : (x 2 1).toNat = 1)
    (g16 : (x 3 2).toNat = 0)
    (g17 : (x 3 4).toNat = 0)
    (g18 : (x 3 6).toNat = 0)
    (g19 : (x 0 1 && x 0 2).toNat = 0)
    (g20 : (x (-3) 4 && x (-3) 5).toNat = 0)
    (g21 : (x (-4) 5 && x (-4) 6).toNat = 0)
    (g22 : (x (-5) 6 && x (-5) 7).toNat = 0)
    (g23 : (x (-6) 7 && x (-6) 8).toNat = 0)
    (g24 : (x 1 2 && x 1 6).toNat = 0)
    (g25 : (x 0 3 && x 0 7).toNat = 0)
    (g26 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g27 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g28 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g29 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g30 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g31 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g32 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g33 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g34 : (x 1 1 && x 1 8).toNat = 0)
    (g35 : (x 0 2 && x 0 9).toNat = 0)
    (g36 : (x (-1) 3 && x (-1) 10).toNat = 0)
    (g37 : (x (-2) 4 && x (-2) 11).toNat = 0)
    (g38 : (x 0 1 && x 0 10).toNat = 0)
    (g39 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g40 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g41 : (x 3 3 && x 3 12).toNat = 0)
    (g42 : (x 1 5 && x 1 14).toNat = 0)
    (g43 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g44 : (x 0 1 && x 0 11).toNat = 0)
    (g45 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g46 : (x 3 2 && x 3 12).toNat = 0)
    (g47 : (x 1 4 && x 1 14).toNat = 0)
    (g48 : (x 3 4 && x 3 14).toNat = 0)
    (g49 : (x 1 2 && x 1 13).toNat = 0)
    (g50 : (x 0 3 && x 0 14).toNat = 0)
    (g51 : (x 3 2 && x 3 13).toNat = 0)
    (g52 : (x 3 3 && x 3 14).toNat = 0)
    (g53 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b00000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53
