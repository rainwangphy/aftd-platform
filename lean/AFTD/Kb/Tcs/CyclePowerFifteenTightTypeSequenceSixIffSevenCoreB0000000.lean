import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b0000000

Topic: combinatorics   Node: 23223fce1773

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 29 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b0000000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 0 3).toNat = 0)
    (g2 : (x 0 5).toNat = 0)
    (g3 : (x 0 6).toNat = 0)
    (g4 : (x 0 9).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 1 1).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 2 5).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 5 10).toNat = 0)
    (g12 : (x 6 9).toNat = 0)
    (g13 : (x 1 2 && x 1 6).toNat = 0)
    (g14 : (x 0 3 && x 0 7).toNat = 0)
    (g15 : (x 0 9 && x 0 13).toNat = 0)
    (g16 : (x 0 1 && x 0 7).toNat = 0)
    (g17 : (x 7 2 && x 7 8).toNat = 0)
    (g18 : (x 6 3 && x 6 9).toNat = 0)
    (g19 : (x 5 4 && x 5 10).toNat = 0)
    (g20 : (x 4 5 && x 4 11).toNat = 0)
    (g21 : (x 0 1 && x 0 10).toNat = 0)
    (g22 : (x 0 2 && x 0 11).toNat = 0)
    (g23 : (x 5 1 && x 5 10).toNat = 0)
    (g24 : (x 4 2 && x 4 11).toNat = 0)
    (g25 : (x 0 3 && x 0 13).toNat = 0)
    (g26 : (x 4 1 && x 4 11).toNat = 0)
    (g27 : (x 3 4 && x 3 14).toNat = 0)
    (g28 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d443 : (x 1 1 && x 1 14).toNat = 0 := by
    have r444 := hand1 (x 1 1) (x 1 14)
    have b445 := hb (x 1 1)
    have b446 := hb (x 1 1 && x 1 14)
    clear * - r444 b445 b446 g7
    omega
  have d447 : (x 1 1 && x 1 10).toNat = 0 := by
    have r448 := hand1 (x 1 1) (x 1 10)
    have b449 := hb (x 1 1)
    have b450 := hb (x 1 1 && x 1 10)
    clear * - r448 b449 b450 g7
    omega
  have d451 : (x 1 13).toNat = 0 := by
    have r452 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b453 := hb (x 1 1)
    have b454 := hb (x 1 13)
    clear * - r452 b453 b454 g7
    omega
  have d455 : (x 1 9).toNat = 0 := by
    have r456 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b457 := hb (x 1 1)
    have b458 := hb (x 1 9)
    clear * - r456 b457 b458 g7
    omega
  have d459 : (x 1 5).toNat = 0 := by
    have r460 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b461 := hb (x 1 5)
    have b462 := hb (x 1 13)
    clear * - r460 b461 b462 d451
    omega
  have d463 : (x 1 5 && x 1 14).toNat = 0 := by
    have r464 := hand1 (x 1 5) (x 1 14)
    have b465 := hb (x 1 5)
    have b466 := hb (x 1 5 && x 1 14)
    clear * - r464 b465 b466 d459
    omega
  have d467 : (x 2 13).toNat = 1 := by
    have r468 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b469 := hb (x 0 2)
    have b470 := hb (x 2 13)
    have b471 := hb (x 1 1 && x 1 14)
    clear * - r468 b469 b470 b471 d443 g0
    omega
  have d472 : (x 2 1).toNat = 1 := by
    have r473 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b474 := hb (x 2 1)
    have b475 := hb (x 2 13)
    clear * - r473 b474 b475 d467
    omega
  have d476 : (x 3 14).toNat = 0 := by
    have r477 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b478 := hb (x 2 1)
    have b479 := hb (x 3 14)
    clear * - r477 b478 b479 d472
    omega
  have d480 : (x 3 6).toNat = 0 := by
    have r481 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b482 := hb (x 3 6)
    have b483 := hb (x 3 14)
    clear * - r481 b482 b483 d476
    omega
  have d484 : (x 3 6 && x 3 12).toNat = 0 := by
    have r485 := hand1 (x 3 6) (x 3 12)
    have b486 := hb (x 3 6)
    have b487 := hb (x 3 6 && x 3 12)
    clear * - r485 b486 b487 d480
    omega
  have d488 : (x 3 6 && x 3 10).toNat = 0 := by
    have r489 := hand1 (x 3 6) (x 3 10)
    have b490 := hb (x 3 6)
    have b491 := hb (x 3 6 && x 3 10)
    clear * - r489 b490 b491 d480
    omega
  have d492 : (x 3 2).toNat = 0 := by
    have r493 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b494 := hb (x 3 2)
    have b495 := hb (x 3 14)
    clear * - r493 b494 b495 d476
    omega
  have d496 : (x 3 2 && x 3 12).toNat = 0 := by
    have r497 := hand1 (x 3 2) (x 3 12)
    have b498 := hb (x 3 2)
    have b499 := hb (x 3 2 && x 3 12)
    clear * - r497 b498 b499 d492
    omega
  have d500 : (x 3 10).toNat = 0 := by
    have r501 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b502 := hb (x 3 2)
    have b503 := hb (x 3 10)
    clear * - r501 b502 b503 d492
    omega
  have d504 : (x (-1) 2).toNat = 1 := by
    have r505 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b506 := hb (x (-1) 2)
    have b507 := hb (x 1 13)
    have b508 := hb (x 0 1 && x 0 14)
    clear * - r505 b506 b507 b508 d451 g28
    omega
  have d509 : (x (-1) 14).toNat = 1 := by
    have r510 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b511 := hb (x (-1) 2)
    have b512 := hb (x (-1) 14)
    clear * - r510 b511 b512 d504
    omega
  have d513 : (x (-2) 1).toNat = 0 := by
    have r514 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b515 := hb (x (-2) 1)
    have b516 := hb (x (-1) 14)
    clear * - r514 b515 b516 d509
    omega
  have d517 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
    have r518 := hand1 (x (-2) 1) (x (-2) 12)
    have b519 := hb (x (-2) 1)
    have b520 := hb (x (-2) 1 && x (-2) 12)
    clear * - r518 b519 b520 d513
    omega
  have d521 : (x (-2) 1 && x (-2) 8).toNat = 0 := by
    have r522 := hand1 (x (-2) 1) (x (-2) 8)
    have b523 := hb (x (-2) 1)
    have b524 := hb (x (-2) 1 && x (-2) 8)
    clear * - r522 b523 b524 d513
    omega
  have d525 : (x (-2) 13).toNat = 0 := by
    have r526 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b527 := hb (x (-2) 1)
    have b528 := hb (x (-2) 13)
    clear * - r526 b527 b528 d513
    omega
  have d529 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
    have r530 := hand2 (x (-2) 4) (x (-2) 13)
    have b531 := hb (x (-2) 13)
    have b532 := hb (x (-2) 4 && x (-2) 13)
    clear * - r530 b531 b532 d525
    omega
  have d533 : (x (-2) 5).toNat = 0 := by
    have r534 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b535 := hb (x (-2) 5)
    have b536 := hb (x (-2) 13)
    clear * - r534 b535 b536 d525
    omega
  have d537 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
    have r538 := hand1 (x (-2) 5) (x (-2) 9)
    have b539 := hb (x (-2) 5)
    have b540 := hb (x (-2) 5 && x (-2) 9)
    clear * - r538 b539 b540 d533
    omega
  have d541 : (x (-2) 9).toNat = 0 := by
    have r542 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
    have b543 := hb (x (-2) 1)
    have b544 := hb (x (-2) 9)
    clear * - r542 b543 b544 d513
    omega
  have d545 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
    have r546 := hand2 (x (-2) 3) (x (-2) 9)
    have b547 := hb (x (-2) 9)
    have b548 := hb (x (-2) 3 && x (-2) 9)
    clear * - r546 b547 b548 d541
    omega
  have d549 : (x 3 12).toNat = 0 := by
    have r550 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e551 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e552 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b553 := hb (x 0 3)
    have b554 := hb (x 1 2)
    have b555 := hb (x 2 13)
    have b556 := hb (x 3 12)
    clear * - r550 e551 e552 b553 b554 b555 b556 d467 g1
    omega
  have d557 : (x 3 3 && x 3 12).toNat = 0 := by
    have r558 := hand2 (x 3 3) (x 3 12)
    have b559 := hb (x 3 12)
    have b560 := hb (x 3 3 && x 3 12)
    clear * - r558 b559 b560 d549
    omega
  have d561 : (x 1 2).toNat = 0 := by
    have r562 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e563 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e564 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b565 := hb (x 0 3)
    have b566 := hb (x 1 2)
    have b567 := hb (x 2 13)
    have b568 := hb (x 3 12)
    clear * - r562 e563 e564 b565 b566 b567 b568 d549 d467 g1
    omega
  have d569 : (x 1 2 && x 1 12).toNat = 0 := by
    have r570 := hand1 (x 1 2) (x 1 12)
    have b571 := hb (x 1 2)
    have b572 := hb (x 1 2 && x 1 12)
    clear * - r570 b571 b572 d561
    omega
  have d573 : (x 1 10).toNat = 0 := by
    have r574 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b575 := hb (x 1 2)
    have b576 := hb (x 1 10)
    clear * - r574 b575 b576 d561
    omega
  have d577 : (x 1 12).toNat = 0 := by
    have r578 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e579 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e580 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b581 := hb (x (-2) 3)
    have b582 := hb (x (-1) 2)
    have b583 := hb (x 0 13)
    have b584 := hb (x 1 12)
    clear * - r578 e579 e580 b581 b582 b583 b584 g6 d504
    omega
  have d585 : (x 1 8 && x 1 12).toNat = 0 := by
    have r586 := hand2 (x 1 8) (x 1 12)
    have b587 := hb (x 1 12)
    have b588 := hb (x 1 8 && x 1 12)
    clear * - r586 b587 b588 d577
    omega
  have d589 : (x 1 4).toNat = 0 := by
    have r590 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b591 := hb (x 1 4)
    have b592 := hb (x 1 12)
    clear * - r590 b591 b592 d577
    omega
  have d593 : (x 1 4 && x 1 14).toNat = 0 := by
    have r594 := hand1 (x 1 4) (x 1 14)
    have b595 := hb (x 1 4)
    have b596 := hb (x 1 4 && x 1 14)
    clear * - r594 b595 b596 d589
    omega
  have d597 : (x (-2) 3).toNat = 0 := by
    have r598 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e599 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e600 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b601 := hb (x (-2) 3)
    have b602 := hb (x (-1) 2)
    have b603 := hb (x 0 13)
    have b604 := hb (x 1 12)
    clear * - r598 e599 e600 b601 b602 b603 b604 d577 g6 d504
    omega
  have d605 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
    have r606 := hand1 (x (-2) 3) (x (-2) 12)
    have b607 := hb (x (-2) 3)
    have b608 := hb (x (-2) 3 && x (-2) 12)
    clear * - r606 b607 b608 d597
    omega
  have d609 : (x (-2) 11).toNat = 0 := by
    have r610 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b611 := hb (x (-2) 3)
    have b612 := hb (x (-2) 11)
    clear * - r610 b611 b612 d597
    omega
  have d613 : (x 2 3 && x 2 13).toNat = 1 := by
    have r614 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b615 := hb (x 0 5)
    have b616 := hb (x 5 10)
    have b617 := hb (x 4 1 && x 4 11)
    have b618 := hb (x 3 2 && x 3 12)
    have b619 := hb (x 2 3 && x 2 13)
    have b620 := hb (x 1 4 && x 1 14)
    clear * - r614 b615 b616 b617 b618 b619 b620 g11 g26 d496 d593 g2
    omega
  have d621 : (x 2 3).toNat = 1 := by
    have r622 := hand1 (x 2 3) (x 2 13)
    have b623 := hb (x 2 3)
    have b624 := hb (x 2 3 && x 2 13)
    clear * - r622 b623 b624 d613
    omega
  have d625 : (x 5 12).toNat = 0 := by
    have r626 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e627 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e628 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b629 := hb (x 2 3)
    have b630 := hb (x 3 2)
    have b631 := hb (x 4 13)
    have b632 := hb (x 5 12)
    clear * - r626 e627 e628 b629 b630 b631 b632 d492 d621
    omega
  have d633 : (x 5 2 && x 5 12).toNat = 0 := by
    have r634 := hand2 (x 5 2) (x 5 12)
    have b635 := hb (x 5 12)
    have b636 := hb (x 5 2 && x 5 12)
    clear * - r634 b635 b636 d625
    omega
  have d637 : (x 5 4).toNat = 0 := by
    have r638 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b639 := hb (x 5 4)
    have b640 := hb (x 5 12)
    clear * - r638 b639 b640 d625
    omega
  have d641 : (x 5 4 && x 5 8).toNat = 0 := by
    have r642 := hand1 (x 5 4) (x 5 8)
    have b643 := hb (x 5 4)
    have b644 := hb (x 5 4 && x 5 8)
    clear * - r642 b643 b644 d637
    omega
  have d645 : (x 4 13).toNat = 0 := by
    have r646 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e647 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e648 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b649 := hb (x 2 3)
    have b650 := hb (x 3 2)
    have b651 := hb (x 4 13)
    have b652 := hb (x 5 12)
    clear * - r646 e647 e648 b649 b650 b651 b652 d625 d492 d621
    omega
  have d653 : (x 4 3 && x 4 13).toNat = 0 := by
    have r654 := hand2 (x 4 3) (x 4 13)
    have b655 := hb (x 4 13)
    have b656 := hb (x 4 3 && x 4 13)
    clear * - r654 b655 b656 d645
    omega
  have d657 : (x 4 5).toNat = 0 := by
    have r658 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b659 := hb (x 4 5)
    have b660 := hb (x 4 13)
    clear * - r658 b659 b660 d645
    omega
  have d661 : (x 4 5 && x 4 9).toNat = 0 := by
    have r662 := hand1 (x 4 5) (x 4 9)
    have b663 := hb (x 4 5)
    have b664 := hb (x 4 5 && x 4 9)
    clear * - r662 b663 b664 d657
    omega
  have d665 : (x 2 4 && x 2 13).toNat = 1 := by
    have r666 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b667 := hb (x 0 6)
    have b668 := hb (x 6 9)
    have b669 := hb (x 5 1 && x 5 10)
    have b670 := hb (x 4 2 && x 4 11)
    have b671 := hb (x 3 3 && x 3 12)
    have b672 := hb (x 2 4 && x 2 13)
    have b673 := hb (x 1 5 && x 1 14)
    clear * - r666 b667 b668 b669 b670 b671 b672 b673 g12 g23 g24 d557 d463 g3
    omega
  have d674 : (x 2 4).toNat = 1 := by
    have r675 := hand1 (x 2 4) (x 2 13)
    have b676 := hb (x 2 4)
    have b677 := hb (x 2 4 && x 2 13)
    clear * - r675 b676 b677 d665
    omega
  have d678 : (x 2 12).toNat = 1 := by
    have r679 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b680 := hb (x 2 4)
    have b681 := hb (x 2 12)
    clear * - r679 b680 b681 d674
    omega
  have d682 : (x (-1) 3).toNat = 0 := by
    have r683 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e684 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e685 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b686 := hb (x (-1) 3)
    have b687 := hb (x 0 2)
    have b688 := hb (x 1 13)
    have b689 := hb (x 2 12)
    clear * - r683 e684 e685 b686 b687 b688 b689 d678 d451 g0
    omega
  have d690 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
    have r691 := hand1 (x (-1) 3) (x (-1) 12)
    have b692 := hb (x (-1) 3)
    have b693 := hb (x (-1) 3 && x (-1) 12)
    clear * - r691 b692 b693 d682
    omega
  have d694 : (x (-1) 11).toNat = 0 := by
    have r695 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b696 := hb (x (-1) 3)
    have b697 := hb (x (-1) 11)
    clear * - r695 b696 b697 d682
    omega
  have d698 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
    have r699 := hand2 (x (-1) 2) (x (-1) 11)
    have b700 := hb (x (-1) 11)
    have b701 := hb (x (-1) 2 && x (-1) 11)
    clear * - r699 b700 b701 d694
    omega
  have d702 : (x 6 8).toNat = 0 := by
    have r703 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e704 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e705 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e706 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e707 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e708 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e709 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b710 := hb (x (-1) 7)
    have b711 := hb (x 0 6)
    have b712 := hb (x 1 5)
    have b713 := hb (x 2 4)
    have b714 := hb (x 3 11)
    have b715 := hb (x 4 10)
    have b716 := hb (x 5 9)
    have b717 := hb (x 6 8)
    clear * - r703 e704 e705 e706 e707 e708 e709 b710 b711 b712 b713 b714 b715 b716 b717 d674 d459 g3
    omega
  have d718 : (x 5 9).toNat = 0 := by
    have r719 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e720 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e721 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e722 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e723 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e724 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e725 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b726 := hb (x (-1) 7)
    have b727 := hb (x 0 6)
    have b728 := hb (x 1 5)
    have b729 := hb (x 2 4)
    have b730 := hb (x 3 11)
    have b731 := hb (x 4 10)
    have b732 := hb (x 5 9)
    have b733 := hb (x 6 8)
    clear * - r719 e720 e721 e722 e723 e724 e725 b726 b727 b728 b729 b730 b731 b732 b733 d702 d674 d459 g3
    omega
  have d734 : (x 4 10).toNat = 0 := by
    have r735 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e736 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e737 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e738 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e739 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e740 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e741 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b742 := hb (x (-1) 7)
    have b743 := hb (x 0 6)
    have b744 := hb (x 1 5)
    have b745 := hb (x 2 4)
    have b746 := hb (x 3 11)
    have b747 := hb (x 4 10)
    have b748 := hb (x 5 9)
    have b749 := hb (x 6 8)
    clear * - r735 e736 e737 e738 e739 e740 e741 b742 b743 b744 b745 b746 b747 b748 b749 d702 d718 d674 d459 g3
    omega
  have d750 : (x 3 11).toNat = 0 := by
    have r751 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e752 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e753 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e754 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e755 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e756 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e757 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b758 := hb (x (-1) 7)
    have b759 := hb (x 0 6)
    have b760 := hb (x 1 5)
    have b761 := hb (x 2 4)
    have b762 := hb (x 3 11)
    have b763 := hb (x 4 10)
    have b764 := hb (x 5 9)
    have b765 := hb (x 6 8)
    clear * - r751 e752 e753 e754 e755 e756 e757 b758 b759 b760 b761 b762 b763 b764 b765 d702 d718 d734 d674 d459 g3
    omega
  have d766 : (x (-1) 7).toNat = 0 := by
    have r767 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e768 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e769 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e770 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e771 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e772 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e773 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b774 := hb (x (-1) 7)
    have b775 := hb (x 0 6)
    have b776 := hb (x 1 5)
    have b777 := hb (x 2 4)
    have b778 := hb (x 3 11)
    have b779 := hb (x 4 10)
    have b780 := hb (x 5 9)
    have b781 := hb (x 6 8)
    clear * - r767 e768 e769 e770 e771 e772 e773 b774 b775 b776 b777 b778 b779 b780 b781 d702 d718 d734 d750 d674 d459 g3
    omega
  cases h782 : x (-1) 4
  · have f783 : (x (-1) 4).toNat = 0 := by rw [h782]; rfl
    have d784 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
      have r785 := hand1 (x (-1) 4) (x (-1) 14)
      have b786 := hb (x (-1) 4)
      have b787 := hb (x (-1) 4 && x (-1) 14)
      clear * - r785 b786 b787 f783
      omega
    have d788 : (x 2 1 && x 2 11).toNat = 1 := by
      have r789 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b790 := hb (x (-2) 5)
      have b791 := hb (x 3 10)
      have b792 := hb (x 2 1 && x 2 11)
      have b793 := hb (x 1 2 && x 1 12)
      have b794 := hb (x 0 3 && x 0 13)
      have b795 := hb (x (-1) 4 && x (-1) 14)
      clear * - r789 b790 b791 b792 b793 b794 b795 d500 d569 g25 d784 d533
      omega
    have d796 : (x 2 11).toNat = 1 := by
      have r797 := hand2 (x 2 1) (x 2 11)
      have b798 := hb (x 2 11)
      have b799 := hb (x 2 1 && x 2 11)
      clear * - r797 b798 b799 d788
      omega
    have d800 : (x 5 8).toNat = 0 := by
      have r801 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e802 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e803 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e804 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e805 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e806 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e807 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b808 := hb (x (-2) 7)
      have b809 := hb (x (-1) 6)
      have b810 := hb (x 0 5)
      have b811 := hb (x 1 4)
      have b812 := hb (x 2 11)
      have b813 := hb (x 3 10)
      have b814 := hb (x 4 9)
      have b815 := hb (x 5 8)
      clear * - r801 e802 e803 e804 e805 e806 e807 b808 b809 b810 b811 b812 b813 b814 b815 d500 d796 d589 g2
      omega
    have d816 : (x 4 9).toNat = 0 := by
      have r817 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e818 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e819 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e820 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e821 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e822 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e823 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b824 := hb (x (-2) 7)
      have b825 := hb (x (-1) 6)
      have b826 := hb (x 0 5)
      have b827 := hb (x 1 4)
      have b828 := hb (x 2 11)
      have b829 := hb (x 3 10)
      have b830 := hb (x 4 9)
      have b831 := hb (x 5 8)
      clear * - r817 e818 e819 e820 e821 e822 e823 b824 b825 b826 b827 b828 b829 b830 b831 d800 d500 d796 d589 g2
      omega
    have r832 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r833 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e834 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e835 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e836 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e837 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e838 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e839 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have r840 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e841 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e842 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e843 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e844 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e845 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e846 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have r847 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e848 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e849 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e850 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e851 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e852 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e853 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have r854 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e855 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e856 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have r857 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e858 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
    have e859 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
    have r860 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := by have q := hcov6 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r861 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r862 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r863 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r864 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
    have r865 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
    have r866 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
    have r867 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have r868 := hand2 (x 7 2) (x 7 6)
    have r869 := hand2 (x 6 3) (x 6 7)
    have r870 := hand1 (x 2 7) (x 2 11)
    have r871 := hand2 (x 8 1) (x 8 7)
    have r872 := hand1 (x 2 7) (x 2 13)
    have r873 := hand1 (x 1 8) (x 1 14)
    have r874 := hand1 (x (-3) 4) (x (-3) 13)
    have r875 := hand1 (x (-4) 5) (x (-4) 14)
    have r876 := hand2 (x 6 1) (x 6 11)
    have r877 := hand1 (x 12 1) (x 12 11)
    have r878 := hand1 (x 11 2) (x 11 12)
    have r879 := hand1 (x 10 3) (x 10 13)
    have r880 := hand1 (x 9 4) (x 9 14)
    linarith only [r832, r833, e834, e835, e836, e837, e838, e839, r840, e841, e842, e843, e844, e845, e846, r847, e848, e849, e850, e851, e852, e853, r854, e855, e856, r857, e858, e859, r860, r861, r862, r863, r864, r865, r866, r867, r868, r869, r870, r871, r872, r873, r874, r875, r876, r877, r878, r879, r880, d609, d509, g4, g6, d455, d577, g9, d796, d480, d500, d657, d816, d637, d800, d641, d661, d488, d585, g15, g17, g18, g19, g20, d484, g21, d698, d605, d633, d653, g27]
  · have f954 : (x (-1) 4).toNat = 1 := by rw [h782]; rfl
    have d955 : (x (-1) 12).toNat = 1 := by
      have r956 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b957 := hb (x (-1) 4)
      have b958 := hb (x (-1) 12)
      clear * - r956 b957 b958 f954
      omega
    have d959 : (x (-3) 2).toNat = 0 := by
      have r960 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e961 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e962 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b963 := hb (x (-4) 3)
      have b964 := hb (x (-3) 2)
      have b965 := hb (x (-2) 13)
      have b966 := hb (x (-1) 12)
      clear * - r960 e961 e962 b963 b964 b965 b966 d955 d525
      omega
    have d967 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
      have r968 := hand1 (x (-3) 2) (x (-3) 13)
      have b969 := hb (x (-3) 2)
      have b970 := hb (x (-3) 2 && x (-3) 13)
      clear * - r968 b969 b970 d959
      omega
    have d971 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
      have r972 := hand1 (x (-3) 2) (x (-3) 9)
      have b973 := hb (x (-3) 2)
      have b974 := hb (x (-3) 2 && x (-3) 9)
      clear * - r972 b973 b974 d959
      omega
    have d975 : (x (-3) 10).toNat = 0 := by
      have r976 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
      have b977 := hb (x (-3) 2)
      have b978 := hb (x (-3) 10)
      clear * - r976 b977 b978 d959
      omega
    have d979 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
      have r980 := hand2 (x (-3) 1) (x (-3) 10)
      have b981 := hb (x (-3) 10)
      have b982 := hb (x (-3) 1 && x (-3) 10)
      clear * - r980 b981 b982 d975
      omega
    have d983 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
      have r984 := hand2 (x (-3) 4) (x (-3) 10)
      have b985 := hb (x (-3) 10)
      have b986 := hb (x (-3) 4 && x (-3) 10)
      clear * - r984 b985 b986 d975
      omega
    have d987 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
      have r988 := hand2 (x (-3) 6) (x (-3) 10)
      have b989 := hb (x (-3) 10)
      have b990 := hb (x (-3) 6 && x (-3) 10)
      clear * - r988 b989 b990 d975
      omega
    have d991 : (x (-4) 3).toNat = 0 := by
      have r992 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e993 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e994 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b995 := hb (x (-4) 3)
      have b996 := hb (x (-3) 2)
      have b997 := hb (x (-2) 13)
      have b998 := hb (x (-1) 12)
      clear * - r992 e993 e994 b995 b996 b997 b998 d955 d525 d959
      omega
    have d999 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
      have r1000 := hand1 (x (-4) 3) (x (-4) 14)
      have b1001 := hb (x (-4) 3)
      have b1002 := hb (x (-4) 3 && x (-4) 14)
      clear * - r1000 b1001 b1002 d991
      omega
    have d1003 : (x (-4) 3 && x (-4) 10).toNat = 0 := by
      have r1004 := hand1 (x (-4) 3) (x (-4) 10)
      have b1005 := hb (x (-4) 3)
      have b1006 := hb (x (-4) 3 && x (-4) 10)
      clear * - r1004 b1005 b1006 d991
      omega
    have d1007 : (x (-4) 11).toNat = 0 := by
      have r1008 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b1009 := hb (x (-4) 3)
      have b1010 := hb (x (-4) 11)
      clear * - r1008 b1009 b1010 d991
      omega
    have d1011 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
      have r1012 := hand2 (x (-4) 2) (x (-4) 11)
      have b1013 := hb (x (-4) 11)
      have b1014 := hb (x (-4) 2 && x (-4) 11)
      clear * - r1012 b1013 b1014 d1007
      omega
    have d1015 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
      have r1016 := hand2 (x (-4) 5) (x (-4) 11)
      have b1017 := hb (x (-4) 11)
      have b1018 := hb (x (-4) 5 && x (-4) 11)
      clear * - r1016 b1017 b1018 d1007
      omega
    have d1019 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
      have r1020 := hand2 (x (-4) 7) (x (-4) 11)
      have b1021 := hb (x (-4) 11)
      have b1022 := hb (x (-4) 7 && x (-4) 11)
      clear * - r1020 b1021 b1022 d1007
      omega
    have d1023 : (x (-5) 4).toNat = 1 := by
      have r1024 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1025 := hb (x (-5) 4)
      have b1026 := hb (x (-1) 11)
      have b1027 := hb (x (-2) 1 && x (-2) 12)
      have b1028 := hb (x (-3) 2 && x (-3) 13)
      have b1029 := hb (x (-4) 3 && x (-4) 14)
      clear * - r1024 b1025 b1026 b1027 b1028 b1029 d694 d517 d967 d999
      omega
    have d1030 : (x (-5) 12).toNat = 1 := by
      have r1031 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
      have b1032 := hb (x (-5) 4)
      have b1033 := hb (x (-5) 12)
      clear * - r1031 b1032 b1033 d1023
      omega
    have d1034 : (x (-6) 13).toNat = 0 := by
      have r1035 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1036 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e1037 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b1038 := hb (x (-8) 3)
      have b1039 := hb (x (-7) 2)
      have b1040 := hb (x (-6) 13)
      have b1041 := hb (x (-5) 12)
      clear * - r1035 e1036 e1037 b1038 b1039 b1040 b1041 d1030
      omega
    have d1042 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
      have r1043 := hand2 (x (-6) 4) (x (-6) 13)
      have b1044 := hb (x (-6) 13)
      have b1045 := hb (x (-6) 4 && x (-6) 13)
      clear * - r1043 b1044 b1045 d1034
      omega
    have d1046 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
      have r1047 := hand2 (x (-6) 7) (x (-6) 13)
      have b1048 := hb (x (-6) 13)
      have b1049 := hb (x (-6) 7 && x (-6) 13)
      clear * - r1047 b1048 b1049 d1034
      omega
    have d1050 : (x (-6) 9 && x (-6) 13).toNat = 0 := by
      have r1051 := hand2 (x (-6) 9) (x (-6) 13)
      have b1052 := hb (x (-6) 13)
      have b1053 := hb (x (-6) 9 && x (-6) 13)
      clear * - r1051 b1052 b1053 d1034
      omega
    have d1054 : (x (-6) 5).toNat = 0 := by
      have r1055 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
      have b1056 := hb (x (-6) 5)
      have b1057 := hb (x (-6) 13)
      clear * - r1055 b1056 b1057 d1034
      omega
    have d1058 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
      have r1059 := hand1 (x (-6) 5) (x (-6) 12)
      have b1060 := hb (x (-6) 5)
      have b1061 := hb (x (-6) 5 && x (-6) 12)
      clear * - r1059 b1060 b1061 d1054
      omega
    have d1062 : (x (-7) 2).toNat = 0 := by
      have r1063 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1064 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e1065 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b1066 := hb (x (-8) 3)
      have b1067 := hb (x (-7) 2)
      have b1068 := hb (x (-6) 13)
      have b1069 := hb (x (-5) 12)
      clear * - r1063 e1064 e1065 b1066 b1067 b1068 b1069 d1030 d1034
      omega
    have d1070 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
      have r1071 := hand1 (x (-7) 2) (x (-7) 13)
      have b1072 := hb (x (-7) 2)
      have b1073 := hb (x (-7) 2 && x (-7) 13)
      clear * - r1071 b1072 b1073 d1062
      omega
    have d1074 : (x (-7) 2 && x (-7) 12).toNat = 0 := by
      have r1075 := hand1 (x (-7) 2) (x (-7) 12)
      have b1076 := hb (x (-7) 2)
      have b1077 := hb (x (-7) 2 && x (-7) 12)
      clear * - r1075 b1076 b1077 d1062
      omega
    have d1078 : (x (-7) 10).toNat = 0 := by
      have r1079 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
      have b1080 := hb (x (-7) 2)
      have b1081 := hb (x (-7) 10)
      clear * - r1079 b1080 b1081 d1062
      omega
    have d1082 : (x (-7) 1 && x (-7) 10).toNat = 0 := by
      have r1083 := hand2 (x (-7) 1) (x (-7) 10)
      have b1084 := hb (x (-7) 10)
      have b1085 := hb (x (-7) 1 && x (-7) 10)
      clear * - r1083 b1084 b1085 d1078
      omega
    have d1086 : (x (-7) 4 && x (-7) 10).toNat = 0 := by
      have r1087 := hand2 (x (-7) 4) (x (-7) 10)
      have b1088 := hb (x (-7) 10)
      have b1089 := hb (x (-7) 4 && x (-7) 10)
      clear * - r1087 b1088 b1089 d1078
      omega
    have d1090 : (x (-7) 5 && x (-7) 10).toNat = 0 := by
      have r1091 := hand2 (x (-7) 5) (x (-7) 10)
      have b1092 := hb (x (-7) 10)
      have b1093 := hb (x (-7) 5 && x (-7) 10)
      clear * - r1091 b1092 b1093 d1078
      omega
    have d1094 : (x (-8) 3).toNat = 0 := by
      have r1095 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1096 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e1097 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b1098 := hb (x (-8) 3)
      have b1099 := hb (x (-7) 2)
      have b1100 := hb (x (-6) 13)
      have b1101 := hb (x (-5) 12)
      clear * - r1095 e1096 e1097 b1098 b1099 b1100 b1101 d1030 d1034 d1062
      omega
    have d1102 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
      have r1103 := hand1 (x (-8) 3) (x (-8) 14)
      have b1104 := hb (x (-8) 3)
      have b1105 := hb (x (-8) 3 && x (-8) 14)
      clear * - r1103 b1104 b1105 d1094
      omega
    have d1106 : (x (-8) 3 && x (-8) 13).toNat = 0 := by
      have r1107 := hand1 (x (-8) 3) (x (-8) 13)
      have b1108 := hb (x (-8) 3)
      have b1109 := hb (x (-8) 3 && x (-8) 13)
      clear * - r1107 b1108 b1109 d1094
      omega
    have d1110 : (x (-8) 11).toNat = 0 := by
      have r1111 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
      have b1112 := hb (x (-8) 3)
      have b1113 := hb (x (-8) 11)
      clear * - r1111 b1112 b1113 d1094
      omega
    have d1114 : (x (-8) 1 && x (-8) 11).toNat = 0 := by
      have r1115 := hand2 (x (-8) 1) (x (-8) 11)
      have b1116 := hb (x (-8) 11)
      have b1117 := hb (x (-8) 1 && x (-8) 11)
      clear * - r1115 b1116 b1117 d1110
      omega
    have d1118 : (x (-8) 2 && x (-8) 11).toNat = 0 := by
      have r1119 := hand2 (x (-8) 2) (x (-8) 11)
      have b1120 := hb (x (-8) 11)
      have b1121 := hb (x (-8) 2 && x (-8) 11)
      clear * - r1119 b1120 b1121 d1110
      omega
    have d1122 : (x (-8) 5 && x (-8) 11).toNat = 0 := by
      have r1123 := hand2 (x (-8) 5) (x (-8) 11)
      have b1124 := hb (x (-8) 11)
      have b1125 := hb (x (-8) 5 && x (-8) 11)
      clear * - r1123 b1124 b1125 d1110
      omega
    have d1126 : (x (-8) 6 && x (-8) 11).toNat = 0 := by
      have r1127 := hand2 (x (-8) 6) (x (-8) 11)
      have b1128 := hb (x (-8) 11)
      have b1129 := hb (x (-8) 6 && x (-8) 11)
      clear * - r1127 b1128 b1129 d1110
      omega
    have d1130 : (x 3 8).toNat = 0 := by
      have r1131 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1132 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e1133 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e1134 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e1135 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e1136 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e1137 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b1138 := hb (x (-4) 7)
      have b1139 := hb (x (-3) 6)
      have b1140 := hb (x (-2) 5)
      have b1141 := hb (x (-1) 4)
      have b1142 := hb (x 0 11)
      have b1143 := hb (x 1 10)
      have b1144 := hb (x 2 9)
      have b1145 := hb (x 3 8)
      clear * - r1131 e1132 e1133 e1134 e1135 e1136 e1137 b1138 b1139 b1140 b1141 b1142 b1143 b1144 b1145 d573 g5 f954 d533
      omega
    have d1146 : (x 2 9).toNat = 0 := by
      have r1147 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1148 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e1149 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e1150 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e1151 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e1152 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e1153 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b1154 := hb (x (-4) 7)
      have b1155 := hb (x (-3) 6)
      have b1156 := hb (x (-2) 5)
      have b1157 := hb (x (-1) 4)
      have b1158 := hb (x 0 11)
      have b1159 := hb (x 1 10)
      have b1160 := hb (x 2 9)
      have b1161 := hb (x 3 8)
      clear * - r1147 e1148 e1149 e1150 e1151 e1152 e1153 b1154 b1155 b1156 b1157 b1158 b1159 b1160 b1161 d1130 d573 g5 f954 d533
      omega
    have d1162 : (x (-3) 6).toNat = 0 := by
      have r1163 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1164 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e1165 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e1166 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e1167 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e1168 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e1169 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b1170 := hb (x (-4) 7)
      have b1171 := hb (x (-3) 6)
      have b1172 := hb (x (-2) 5)
      have b1173 := hb (x (-1) 4)
      have b1174 := hb (x 0 11)
      have b1175 := hb (x 1 10)
      have b1176 := hb (x 2 9)
      have b1177 := hb (x 3 8)
      clear * - r1163 e1164 e1165 e1166 e1167 e1168 e1169 b1170 b1171 b1172 b1173 b1174 b1175 b1176 b1177 d1130 d1146 d573 g5 f954 d533
      omega
    have d1178 : (x (-3) 1 && x (-3) 6).toNat = 0 := by
      have r1179 := hand2 (x (-3) 1) (x (-3) 6)
      have b1180 := hb (x (-3) 6)
      have b1181 := hb (x (-3) 1 && x (-3) 6)
      clear * - r1179 b1180 b1181 d1162
      omega
    have d1182 : (x (-4) 7).toNat = 0 := by
      have r1183 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1184 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e1185 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e1186 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e1187 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e1188 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e1189 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b1190 := hb (x (-4) 7)
      have b1191 := hb (x (-3) 6)
      have b1192 := hb (x (-2) 5)
      have b1193 := hb (x (-1) 4)
      have b1194 := hb (x 0 11)
      have b1195 := hb (x 1 10)
      have b1196 := hb (x 2 9)
      have b1197 := hb (x 3 8)
      clear * - r1183 e1184 e1185 e1186 e1187 e1188 e1189 b1190 b1191 b1192 b1193 b1194 b1195 b1196 b1197 d1130 d1146 d573 g5 f954 d533 d1162
      omega
    have d1198 : (x (-4) 1 && x (-4) 7).toNat = 0 := by
      have r1199 := hand2 (x (-4) 1) (x (-4) 7)
      have b1200 := hb (x (-4) 7)
      have b1201 := hb (x (-4) 1 && x (-4) 7)
      clear * - r1199 b1200 b1201 d1182
      omega
    have d1202 : (x (-4) 2 && x (-4) 7).toNat = 0 := by
      have r1203 := hand2 (x (-4) 2) (x (-4) 7)
      have b1204 := hb (x (-4) 7)
      have b1205 := hb (x (-4) 2 && x (-4) 7)
      clear * - r1203 b1204 b1205 d1182
      omega
    have d1206 : (x (-1) 8).toNat = 0 := by
      have r1207 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1208 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e1209 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e1210 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e1211 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e1212 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e1213 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b1214 := hb (x (-8) 7)
      have b1215 := hb (x (-7) 6)
      have b1216 := hb (x (-6) 5)
      have b1217 := hb (x (-5) 4)
      have b1218 := hb (x (-4) 11)
      have b1219 := hb (x (-3) 10)
      have b1220 := hb (x (-2) 9)
      have b1221 := hb (x (-1) 8)
      clear * - r1207 e1208 e1209 e1210 e1211 e1212 e1213 b1214 b1215 b1216 b1217 b1218 b1219 b1220 b1221 d541 d975 d1007 d1023 d1054
      omega
    have d1222 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
      have r1223 := hand2 (x (-1) 2) (x (-1) 8)
      have b1224 := hb (x (-1) 8)
      have b1225 := hb (x (-1) 2 && x (-1) 8)
      clear * - r1223 b1224 b1225 d1206
      omega
    have d1226 : (x (-1) 4 && x (-1) 8).toNat = 0 := by
      have r1227 := hand2 (x (-1) 4) (x (-1) 8)
      have b1228 := hb (x (-1) 8)
      have b1229 := hb (x (-1) 4 && x (-1) 8)
      clear * - r1227 b1228 b1229 d1206
      omega
    have d1230 : (x (-7) 6).toNat = 0 := by
      have r1231 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1232 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e1233 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e1234 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e1235 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e1236 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e1237 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b1238 := hb (x (-8) 7)
      have b1239 := hb (x (-7) 6)
      have b1240 := hb (x (-6) 5)
      have b1241 := hb (x (-5) 4)
      have b1242 := hb (x (-4) 11)
      have b1243 := hb (x (-3) 10)
      have b1244 := hb (x (-2) 9)
      have b1245 := hb (x (-1) 8)
      clear * - r1231 e1232 e1233 e1234 e1235 e1236 e1237 b1238 b1239 b1240 b1241 b1242 b1243 b1244 b1245 d1206 d541 d975 d1007 d1023 d1054
      omega
    have d1246 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
      have r1247 := hand1 (x (-7) 6) (x (-7) 13)
      have b1248 := hb (x (-7) 6)
      have b1249 := hb (x (-7) 6 && x (-7) 13)
      clear * - r1247 b1248 b1249 d1230
      omega
    have d1250 : (x (-8) 7).toNat = 0 := by
      have r1251 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1252 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e1253 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e1254 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e1255 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e1256 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e1257 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b1258 := hb (x (-8) 7)
      have b1259 := hb (x (-7) 6)
      have b1260 := hb (x (-6) 5)
      have b1261 := hb (x (-5) 4)
      have b1262 := hb (x (-4) 11)
      have b1263 := hb (x (-3) 10)
      have b1264 := hb (x (-2) 9)
      have b1265 := hb (x (-1) 8)
      clear * - r1251 e1252 e1253 e1254 e1255 e1256 e1257 b1258 b1259 b1260 b1261 b1262 b1263 b1264 b1265 d1206 d541 d975 d1007 d1023 d1054 d1230
      omega
    have d1266 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
      have r1267 := hand1 (x (-8) 7) (x (-8) 14)
      have b1268 := hb (x (-8) 7)
      have b1269 := hb (x (-8) 7 && x (-8) 14)
      clear * - r1267 b1268 b1269 d1250
      omega
    have d1270 : (x (-5) 8 && x (-5) 12).toNat = 1 := by
      have r1271 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1272 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
      have e1273 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
      have b1274 := hb (x (-8) 11)
      have b1275 := hb (x (-7) 10)
      have b1276 := hb (x 2 5)
      have b1277 := hb (x 3 4)
      have b1278 := hb (x 1 2 && x 1 6)
      have b1279 := hb (x 0 3 && x 0 7)
      have b1280 := hb (x (-1) 4 && x (-1) 8)
      have b1281 := hb (x (-2) 5 && x (-2) 9)
      have b1282 := hb (x (-3) 6 && x (-3) 10)
      have b1283 := hb (x (-4) 7 && x (-4) 11)
      have b1284 := hb (x (-5) 8 && x (-5) 12)
      have b1285 := hb (x (-6) 9 && x (-6) 13)
      clear * - r1271 e1272 e1273 b1274 b1275 b1276 b1277 b1278 b1279 b1280 b1281 b1282 b1283 b1284 b1285 g10 g9 g13 g14 d1226 d537 d987 d1019 d1050 d1078 d1110
      omega
    have d1286 : (x (-5) 8).toNat = 1 := by
      have r1287 := hand1 (x (-5) 8) (x (-5) 12)
      have b1288 := hb (x (-5) 8)
      have b1289 := hb (x (-5) 8 && x (-5) 12)
      clear * - r1287 b1288 b1289 d1270
      omega
    have d1290 : (x (-6) 9).toNat = 0 := by
      have r1291 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1292 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
      have e1293 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
      have e1294 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
      have e1295 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
      have e1296 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
      have e1297 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
      have b1298 := hb (x (-12) 7)
      have b1299 := hb (x (-11) 6)
      have b1300 := hb (x (-10) 5)
      have b1301 := hb (x (-9) 4)
      have b1302 := hb (x (-8) 11)
      have b1303 := hb (x (-7) 10)
      have b1304 := hb (x (-6) 9)
      have b1305 := hb (x (-5) 8)
      clear * - r1291 e1292 e1293 e1294 e1295 e1296 e1297 b1298 b1299 b1300 b1301 b1302 b1303 b1304 b1305 d1286 d1078 d1110
      omega
    have d1306 : (x (-6) 3 && x (-6) 9).toNat = 0 := by
      have r1307 := hand2 (x (-6) 3) (x (-6) 9)
      have b1308 := hb (x (-6) 9)
      have b1309 := hb (x (-6) 3 && x (-6) 9)
      clear * - r1307 b1308 b1309 d1290
      omega
    have d1310 : (x (-6) 4 && x (-6) 9).toNat = 0 := by
      have r1311 := hand2 (x (-6) 4) (x (-6) 9)
      have b1312 := hb (x (-6) 9)
      have b1313 := hb (x (-6) 4 && x (-6) 9)
      clear * - r1311 b1312 b1313 d1290
      omega
    have d1314 : (x (-9) 4).toNat = 0 := by
      have r1315 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1316 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
      have e1317 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
      have e1318 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
      have e1319 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
      have e1320 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
      have e1321 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
      have b1322 := hb (x (-12) 7)
      have b1323 := hb (x (-11) 6)
      have b1324 := hb (x (-10) 5)
      have b1325 := hb (x (-9) 4)
      have b1326 := hb (x (-8) 11)
      have b1327 := hb (x (-7) 10)
      have b1328 := hb (x (-6) 9)
      have b1329 := hb (x (-5) 8)
      clear * - r1315 e1316 e1317 e1318 e1319 e1320 e1321 b1322 b1323 b1324 b1325 b1326 b1327 b1328 b1329 d1286 d1290 d1078 d1110
      omega
    have d1330 : (x (-9) 4 && x (-9) 14).toNat = 0 := by
      have r1331 := hand1 (x (-9) 4) (x (-9) 14)
      have b1332 := hb (x (-9) 4)
      have b1333 := hb (x (-9) 4 && x (-9) 14)
      clear * - r1331 b1332 b1333 d1314
      omega
    have d1334 : (x (-10) 5).toNat = 0 := by
      have r1335 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1336 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
      have e1337 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
      have e1338 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
      have e1339 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
      have e1340 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
      have e1341 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
      have b1342 := hb (x (-12) 7)
      have b1343 := hb (x (-11) 6)
      have b1344 := hb (x (-10) 5)
      have b1345 := hb (x (-9) 4)
      have b1346 := hb (x (-8) 11)
      have b1347 := hb (x (-7) 10)
      have b1348 := hb (x (-6) 9)
      have b1349 := hb (x (-5) 8)
      clear * - r1335 e1336 e1337 e1338 e1339 e1340 e1341 b1342 b1343 b1344 b1345 b1346 b1347 b1348 b1349 d1286 d1290 d1078 d1110 d1314
      omega
    have d1350 : (x (-11) 6).toNat = 0 := by
      have r1351 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1352 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
      have e1353 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
      have e1354 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
      have e1355 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
      have e1356 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
      have e1357 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
      have b1358 := hb (x (-12) 7)
      have b1359 := hb (x (-11) 6)
      have b1360 := hb (x (-10) 5)
      have b1361 := hb (x (-9) 4)
      have b1362 := hb (x (-8) 11)
      have b1363 := hb (x (-7) 10)
      have b1364 := hb (x (-6) 9)
      have b1365 := hb (x (-5) 8)
      clear * - r1351 e1352 e1353 e1354 e1355 e1356 e1357 b1358 b1359 b1360 b1361 b1362 b1363 b1364 b1365 d1286 d1290 d1078 d1110 d1314 d1334
      omega
    have d1366 : (x (-11) 2 && x (-11) 6).toNat = 0 := by
      have r1367 := hand2 (x (-11) 2) (x (-11) 6)
      have b1368 := hb (x (-11) 6)
      have b1369 := hb (x (-11) 2 && x (-11) 6)
      clear * - r1367 b1368 b1369 d1350
      omega
    have d1370 : (x (-12) 7).toNat = 0 := by
      have r1371 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1372 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
      have e1373 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
      have e1374 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
      have e1375 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
      have e1376 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
      have e1377 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
      have b1378 := hb (x (-12) 7)
      have b1379 := hb (x (-11) 6)
      have b1380 := hb (x (-10) 5)
      have b1381 := hb (x (-9) 4)
      have b1382 := hb (x (-8) 11)
      have b1383 := hb (x (-7) 10)
      have b1384 := hb (x (-6) 9)
      have b1385 := hb (x (-5) 8)
      clear * - r1371 e1372 e1373 e1374 e1375 e1376 e1377 b1378 b1379 b1380 b1381 b1382 b1383 b1384 b1385 d1286 d1290 d1078 d1110 d1314 d1334 d1350
      omega
    have d1386 : (x (-12) 3 && x (-12) 7).toNat = 0 := by
      have r1387 := hand2 (x (-12) 3) (x (-12) 7)
      have b1388 := hb (x (-12) 7)
      have b1389 := hb (x (-12) 3 && x (-12) 7)
      clear * - r1387 b1388 b1389 d1370
      omega
    have d1390 : (x (-9) 12).toNat = 0 := by
      have r1391 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1392 := hb (x (-11) 14)
      have b1393 := hb (x (-10) 13)
      have b1394 := hb (x (-9) 12)
      have b1395 := hb (x (-8) 11)
      have b1396 := hb (x (-7) 10)
      have b1397 := hb (x (-6) 9)
      have b1398 := hb (x (-5) 8)
      have b1399 := hb (x (-4) 7)
      have b1400 := hb (x (-3) 6)
      have b1401 := hb (x (-2) 5)
      have b1402 := hb (x (-1) 4)
      have b1403 := hb (x 0 3)
      have b1404 := hb (x 1 2)
      have b1405 := hb (x 2 1)
      clear * - r1391 b1392 b1393 b1394 b1395 b1396 b1397 b1398 b1399 b1400 b1401 b1402 b1403 b1404 b1405 d472 d561 g1 f954 d533 d1162 d1182 d1286 d1290 d1078 d1110
      omega
    have d1406 : (x (-9) 2 && x (-9) 12).toNat = 0 := by
      have r1407 := hand2 (x (-9) 2) (x (-9) 12)
      have b1408 := hb (x (-9) 12)
      have b1409 := hb (x (-9) 2 && x (-9) 12)
      clear * - r1407 b1408 b1409 d1390
      omega
    have d1410 : (x (-9) 3 && x (-9) 12).toNat = 0 := by
      have r1411 := hand2 (x (-9) 3) (x (-9) 12)
      have b1412 := hb (x (-9) 12)
      have b1413 := hb (x (-9) 3 && x (-9) 12)
      clear * - r1411 b1412 b1413 d1390
      omega
    have d1414 : (x (-9) 6 && x (-9) 12).toNat = 0 := by
      have r1415 := hand2 (x (-9) 6) (x (-9) 12)
      have b1416 := hb (x (-9) 12)
      have b1417 := hb (x (-9) 6 && x (-9) 12)
      clear * - r1415 b1416 b1417 d1390
      omega
    have d1418 : (x (-9) 7 && x (-9) 12).toNat = 0 := by
      have r1419 := hand2 (x (-9) 7) (x (-9) 12)
      have b1420 := hb (x (-9) 12)
      have b1421 := hb (x (-9) 7 && x (-9) 12)
      clear * - r1419 b1420 b1421 d1390
      omega
    have d1422 : (x (-10) 13).toNat = 0 := by
      have r1423 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1424 := hb (x (-11) 14)
      have b1425 := hb (x (-10) 13)
      have b1426 := hb (x (-9) 12)
      have b1427 := hb (x (-8) 11)
      have b1428 := hb (x (-7) 10)
      have b1429 := hb (x (-6) 9)
      have b1430 := hb (x (-5) 8)
      have b1431 := hb (x (-4) 7)
      have b1432 := hb (x (-3) 6)
      have b1433 := hb (x (-2) 5)
      have b1434 := hb (x (-1) 4)
      have b1435 := hb (x 0 3)
      have b1436 := hb (x 1 2)
      have b1437 := hb (x 2 1)
      clear * - r1423 b1424 b1425 b1426 b1427 b1428 b1429 b1430 b1431 b1432 b1433 b1434 b1435 b1436 b1437 d472 d561 g1 f954 d533 d1162 d1182 d1286 d1290 d1078 d1110 d1390
      omega
    have d1438 : (x (-10) 3 && x (-10) 13).toNat = 0 := by
      have r1439 := hand2 (x (-10) 3) (x (-10) 13)
      have b1440 := hb (x (-10) 13)
      have b1441 := hb (x (-10) 3 && x (-10) 13)
      clear * - r1439 b1440 b1441 d1422
      omega
    have d1442 : (x (-10) 4 && x (-10) 13).toNat = 0 := by
      have r1443 := hand2 (x (-10) 4) (x (-10) 13)
      have b1444 := hb (x (-10) 13)
      have b1445 := hb (x (-10) 4 && x (-10) 13)
      clear * - r1443 b1444 b1445 d1422
      omega
    have d1446 : (x (-10) 7 && x (-10) 13).toNat = 0 := by
      have r1447 := hand2 (x (-10) 7) (x (-10) 13)
      have b1448 := hb (x (-10) 13)
      have b1449 := hb (x (-10) 7 && x (-10) 13)
      clear * - r1447 b1448 b1449 d1422
      omega
    have d1450 : (x (-10) 8 && x (-10) 13).toNat = 0 := by
      have r1451 := hand2 (x (-10) 8) (x (-10) 13)
      have b1452 := hb (x (-10) 13)
      have b1453 := hb (x (-10) 8 && x (-10) 13)
      clear * - r1451 b1452 b1453 d1422
      omega
    have d1454 : (x (-11) 14).toNat = 0 := by
      have r1455 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1456 := hb (x (-11) 14)
      have b1457 := hb (x (-10) 13)
      have b1458 := hb (x (-9) 12)
      have b1459 := hb (x (-8) 11)
      have b1460 := hb (x (-7) 10)
      have b1461 := hb (x (-6) 9)
      have b1462 := hb (x (-5) 8)
      have b1463 := hb (x (-4) 7)
      have b1464 := hb (x (-3) 6)
      have b1465 := hb (x (-2) 5)
      have b1466 := hb (x (-1) 4)
      have b1467 := hb (x 0 3)
      have b1468 := hb (x 1 2)
      have b1469 := hb (x 2 1)
      clear * - r1455 b1456 b1457 b1458 b1459 b1460 b1461 b1462 b1463 b1464 b1465 b1466 b1467 b1468 b1469 d472 d561 g1 f954 d533 d1162 d1182 d1286 d1290 d1078 d1110 d1390 d1422
      omega
    have d1470 : (x (-11) 1 && x (-11) 14).toNat = 0 := by
      have r1471 := hand2 (x (-11) 1) (x (-11) 14)
      have b1472 := hb (x (-11) 14)
      have b1473 := hb (x (-11) 1 && x (-11) 14)
      clear * - r1471 b1472 b1473 d1454
      omega
    have d1474 : (x (-12) 2).toNat = 1 := by
      have r1475 : 1 ≤ (x (-10) 13).toNat + (x (-11) 1 && x (-11) 14).toNat + (x (-12) 2).toNat := by have q := hcov13 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1476 := hb (x (-12) 2)
      have b1477 := hb (x (-10) 13)
      have b1478 := hb (x (-11) 1 && x (-11) 14)
      clear * - r1475 b1476 b1477 b1478 d1422 d1470
      omega
    have d1479 : (x (-12) 14).toNat = 1 := by
      have r1480 : (x (-12) 2).toNat ≤ (x (-12) 14).toNat := himp _ _ (hp2 (-12))
      have b1481 := hb (x (-12) 2)
      have b1482 := hb (x (-12) 14)
      clear * - r1480 b1481 b1482 d1474
      omega
    have d1483 : (x (-13) 1).toNat = 0 := by
      have r1484 : (x (-12) 14).toNat + (x (-13) 1).toNat = 1 := by have q := hd14 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1485 := hb (x (-13) 1)
      have b1486 := hb (x (-12) 14)
      clear * - r1484 b1485 b1486 d1479
      omega
    have d1487 : (x (-13) 1 && x (-13) 14).toNat = 0 := by
      have r1488 := hand1 (x (-13) 1) (x (-13) 14)
      have b1489 := hb (x (-13) 1)
      have b1490 := hb (x (-13) 1 && x (-13) 14)
      clear * - r1488 b1489 b1490 d1483
      omega
    have d1491 : (x (-13) 13).toNat = 0 := by
      have r1492 : (x (-13) 13).toNat ≤ (x (-13) 1).toNat := himp _ _ (hp13 (-13))
      have b1493 := hb (x (-13) 1)
      have b1494 := hb (x (-13) 13)
      clear * - r1492 b1493 b1494 d1483
      omega
    have d1495 : (x (-13) 5).toNat = 0 := by
      have r1496 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
      have b1497 := hb (x (-13) 5)
      have b1498 := hb (x (-13) 13)
      clear * - r1496 b1497 b1498 d1491
      omega
    have d1499 : (x (-10) 12).toNat = 0 := by
      have r1500 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1501 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
      have e1502 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
      have b1503 := hb (x (-13) 3)
      have b1504 := hb (x (-12) 2)
      have b1505 := hb (x (-11) 13)
      have b1506 := hb (x (-10) 12)
      clear * - r1500 e1501 e1502 b1503 b1504 b1505 b1506 d1474
      omega
    have d1507 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
      have r1508 := hand2 (x (-10) 2) (x (-10) 12)
      have b1509 := hb (x (-10) 12)
      have b1510 := hb (x (-10) 2 && x (-10) 12)
      clear * - r1508 b1509 b1510 d1499
      omega
    have d1511 : (x (-10) 4).toNat = 0 := by
      have r1512 : (x (-10) 4).toNat ≤ (x (-10) 12).toNat := himp _ _ (hp4 (-10))
      have b1513 := hb (x (-10) 4)
      have b1514 := hb (x (-10) 12)
      clear * - r1512 b1513 b1514 d1499
      omega
    have d1515 : (x (-11) 13).toNat = 0 := by
      have r1516 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1517 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
      have e1518 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
      have b1519 := hb (x (-13) 3)
      have b1520 := hb (x (-12) 2)
      have b1521 := hb (x (-11) 13)
      have b1522 := hb (x (-10) 12)
      clear * - r1516 e1517 e1518 b1519 b1520 b1521 b1522 d1499 d1474
      omega
    have d1523 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
      have r1524 := hand2 (x (-11) 3) (x (-11) 13)
      have b1525 := hb (x (-11) 13)
      have b1526 := hb (x (-11) 3 && x (-11) 13)
      clear * - r1524 b1525 b1526 d1515
      omega
    have d1527 : (x (-11) 5).toNat = 0 := by
      have r1528 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
      have b1529 := hb (x (-11) 5)
      have b1530 := hb (x (-11) 13)
      clear * - r1528 b1529 b1530 d1515
      omega
    have d1531 : (x (-11) 5 && x (-11) 14).toNat = 0 := by
      have r1532 := hand1 (x (-11) 5) (x (-11) 14)
      have b1533 := hb (x (-11) 5)
      have b1534 := hb (x (-11) 5 && x (-11) 14)
      clear * - r1532 b1533 b1534 d1527
      omega
    have d1535 : (x (-12) 6).toNat = 1 := by
      have r1536 : 1 ≤ (x (-6) 9).toNat + (x (-7) 1 && x (-7) 10).toNat + (x (-8) 2 && x (-8) 11).toNat + (x (-9) 3 && x (-9) 12).toNat + (x (-10) 4 && x (-10) 13).toNat + (x (-11) 5 && x (-11) 14).toNat + (x (-12) 6).toNat := by have q := hcov9 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1537 := hb (x (-12) 6)
      have b1538 := hb (x (-6) 9)
      have b1539 := hb (x (-7) 1 && x (-7) 10)
      have b1540 := hb (x (-8) 2 && x (-8) 11)
      have b1541 := hb (x (-9) 3 && x (-9) 12)
      have b1542 := hb (x (-10) 4 && x (-10) 13)
      have b1543 := hb (x (-11) 5 && x (-11) 14)
      clear * - r1536 b1537 b1538 b1539 b1540 b1541 b1542 b1543 d1290 d1082 d1118 d1410 d1442 d1531
      omega
    have d1544 : (x (-6) 8).toNat = 0 := by
      have r1545 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1546 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e1547 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e1548 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e1549 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e1550 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e1551 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b1552 := hb (x (-13) 7)
      have b1553 := hb (x (-12) 6)
      have b1554 := hb (x (-11) 5)
      have b1555 := hb (x (-10) 4)
      have b1556 := hb (x (-9) 11)
      have b1557 := hb (x (-8) 10)
      have b1558 := hb (x (-7) 9)
      have b1559 := hb (x (-6) 8)
      clear * - r1545 e1546 e1547 e1548 e1549 e1550 e1551 b1552 b1553 b1554 b1555 b1556 b1557 b1558 b1559 d1511 d1527 d1535
      omega
    have d1560 : (x (-7) 9).toNat = 0 := by
      have r1561 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1562 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e1563 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e1564 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e1565 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e1566 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e1567 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b1568 := hb (x (-13) 7)
      have b1569 := hb (x (-12) 6)
      have b1570 := hb (x (-11) 5)
      have b1571 := hb (x (-10) 4)
      have b1572 := hb (x (-9) 11)
      have b1573 := hb (x (-8) 10)
      have b1574 := hb (x (-7) 9)
      have b1575 := hb (x (-6) 8)
      clear * - r1561 e1562 e1563 e1564 e1565 e1566 e1567 b1568 b1569 b1570 b1571 b1572 b1573 b1574 b1575 d1544 d1511 d1527 d1535
      omega
    have d1576 : (x (-8) 10).toNat = 0 := by
      have r1577 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1578 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e1579 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e1580 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e1581 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e1582 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e1583 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b1584 := hb (x (-13) 7)
      have b1585 := hb (x (-12) 6)
      have b1586 := hb (x (-11) 5)
      have b1587 := hb (x (-10) 4)
      have b1588 := hb (x (-9) 11)
      have b1589 := hb (x (-8) 10)
      have b1590 := hb (x (-7) 9)
      have b1591 := hb (x (-6) 8)
      clear * - r1577 e1578 e1579 e1580 e1581 e1582 e1583 b1584 b1585 b1586 b1587 b1588 b1589 b1590 b1591 d1544 d1560 d1511 d1527 d1535
      omega
    have d1592 : (x (-9) 11).toNat = 0 := by
      have r1593 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1594 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e1595 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e1596 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e1597 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e1598 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e1599 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b1600 := hb (x (-13) 7)
      have b1601 := hb (x (-12) 6)
      have b1602 := hb (x (-11) 5)
      have b1603 := hb (x (-10) 4)
      have b1604 := hb (x (-9) 11)
      have b1605 := hb (x (-8) 10)
      have b1606 := hb (x (-7) 9)
      have b1607 := hb (x (-6) 8)
      clear * - r1593 e1594 e1595 e1596 e1597 e1598 e1599 b1600 b1601 b1602 b1603 b1604 b1605 b1606 b1607 d1544 d1560 d1576 d1511 d1527 d1535
      omega
    have d1608 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
      have r1609 := hand2 (x (-9) 1) (x (-9) 11)
      have b1610 := hb (x (-9) 11)
      have b1611 := hb (x (-9) 1 && x (-9) 11)
      clear * - r1609 b1610 b1611 d1592
      omega
    have d1612 : (x (-12) 4 && x (-12) 14).toNat = 1 := by
      have r1613 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1614 := hb (x (-13) 5)
      have b1615 := hb (x (-8) 10)
      have b1616 := hb (x (-9) 1 && x (-9) 11)
      have b1617 := hb (x (-10) 2 && x (-10) 12)
      have b1618 := hb (x (-11) 3 && x (-11) 13)
      have b1619 := hb (x (-12) 4 && x (-12) 14)
      clear * - r1613 b1614 b1615 b1616 b1617 b1618 b1619 d1576 d1608 d1507 d1523 d1495
      omega
    have d1620 : (x (-12) 4).toNat = 1 := by
      have r1621 := hand1 (x (-12) 4) (x (-12) 14)
      have b1622 := hb (x (-12) 4)
      have b1623 := hb (x (-12) 4 && x (-12) 14)
      clear * - r1621 b1622 b1623 d1612
      omega
    have d1624 : (x (-12) 12).toNat = 1 := by
      have r1625 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
      have b1626 := hb (x (-12) 4)
      have b1627 := hb (x (-12) 12)
      clear * - r1625 b1626 b1627 d1620
      omega
    have d1628 : (x (-14) 2).toNat = 0 := by
      have r1629 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1630 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
      have e1631 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
      have b1632 := hb (x (-15) 3)
      have b1633 := hb (x (-14) 2)
      have b1634 := hb (x (-13) 13)
      have b1635 := hb (x (-12) 12)
      clear * - r1629 e1630 e1631 b1632 b1633 b1634 b1635 d1624 d1491
      omega
    have d1636 : (x (-12) 13).toNat = 1 := by
      have r1637 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1638 := hb (x (-14) 2)
      have b1639 := hb (x (-12) 13)
      have b1640 := hb (x (-13) 1 && x (-13) 14)
      clear * - r1637 b1638 b1639 b1640 d1487 d1628
      omega
    have d1641 : (x (-11) 12).toNat = 0 := by
      have r1642 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1643 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
      have e1644 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
      have b1645 := hb (x (-14) 3)
      have b1646 := hb (x (-13) 2)
      have b1647 := hb (x (-12) 13)
      have b1648 := hb (x (-11) 12)
      clear * - r1642 e1643 e1644 b1645 b1646 b1647 b1648 d1636
      omega
    have d1649 : (x (-11) 2 && x (-11) 12).toNat = 0 := by
      have r1650 := hand2 (x (-11) 2) (x (-11) 12)
      have b1651 := hb (x (-11) 12)
      have b1652 := hb (x (-11) 2 && x (-11) 12)
      clear * - r1650 b1651 b1652 d1641
      omega
    have d1653 : (x (-11) 4).toNat = 0 := by
      have r1654 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
      have b1655 := hb (x (-11) 4)
      have b1656 := hb (x (-11) 12)
      clear * - r1654 b1655 b1656 d1641
      omega
    have d1657 : (x (-11) 4 && x (-11) 14).toNat = 0 := by
      have r1658 := hand1 (x (-11) 4) (x (-11) 14)
      have b1659 := hb (x (-11) 4)
      have b1660 := hb (x (-11) 4 && x (-11) 14)
      clear * - r1658 b1659 b1660 d1653
      omega
    have d1661 : (x (-12) 5).toNat = 1 := by
      have r1662 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1663 := hb (x (-12) 5)
      have b1664 := hb (x (-7) 10)
      have b1665 := hb (x (-8) 1 && x (-8) 11)
      have b1666 := hb (x (-9) 2 && x (-9) 12)
      have b1667 := hb (x (-10) 3 && x (-10) 13)
      have b1668 := hb (x (-11) 4 && x (-11) 14)
      clear * - r1662 b1663 b1664 b1665 b1666 b1667 b1668 d1078 d1114 d1406 d1438 d1657
      omega
    have d1669 : (x (-7) 8).toNat = 0 := by
      have r1670 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1671 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e1672 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e1673 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e1674 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e1675 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e1676 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b1677 := hb (x (-14) 7)
      have b1678 := hb (x (-13) 6)
      have b1679 := hb (x (-12) 5)
      have b1680 := hb (x (-11) 4)
      have b1681 := hb (x (-10) 11)
      have b1682 := hb (x (-9) 10)
      have b1683 := hb (x (-8) 9)
      have b1684 := hb (x (-7) 8)
      clear * - r1670 e1671 e1672 e1673 e1674 e1675 e1676 b1677 b1678 b1679 b1680 b1681 b1682 b1683 b1684 d1653 d1661
      omega
    have d1685 : (x (-7) 8 && x (-7) 14).toNat = 0 := by
      have r1686 := hand1 (x (-7) 8) (x (-7) 14)
      have b1687 := hb (x (-7) 8)
      have b1688 := hb (x (-7) 8 && x (-7) 14)
      clear * - r1686 b1687 b1688 d1669
      omega
    have d1689 : (x (-8) 9).toNat = 0 := by
      have r1690 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1691 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e1692 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e1693 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e1694 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e1695 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e1696 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b1697 := hb (x (-14) 7)
      have b1698 := hb (x (-13) 6)
      have b1699 := hb (x (-12) 5)
      have b1700 := hb (x (-11) 4)
      have b1701 := hb (x (-10) 11)
      have b1702 := hb (x (-9) 10)
      have b1703 := hb (x (-8) 9)
      have b1704 := hb (x (-7) 8)
      clear * - r1690 e1691 e1692 e1693 e1694 e1695 e1696 b1697 b1698 b1699 b1700 b1701 b1702 b1703 b1704 d1669 d1653 d1661
      omega
    have d1705 : (x (-9) 10).toNat = 0 := by
      have r1706 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1707 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e1708 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e1709 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e1710 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e1711 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e1712 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b1713 := hb (x (-14) 7)
      have b1714 := hb (x (-13) 6)
      have b1715 := hb (x (-12) 5)
      have b1716 := hb (x (-11) 4)
      have b1717 := hb (x (-10) 11)
      have b1718 := hb (x (-9) 10)
      have b1719 := hb (x (-8) 9)
      have b1720 := hb (x (-7) 8)
      clear * - r1706 e1707 e1708 e1709 e1710 e1711 e1712 b1713 b1714 b1715 b1716 b1717 b1718 b1719 b1720 d1669 d1689 d1653 d1661
      omega
    have d1721 : (x (-10) 11).toNat = 0 := by
      have r1722 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1723 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e1724 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e1725 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e1726 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e1727 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e1728 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b1729 := hb (x (-14) 7)
      have b1730 := hb (x (-13) 6)
      have b1731 := hb (x (-12) 5)
      have b1732 := hb (x (-11) 4)
      have b1733 := hb (x (-10) 11)
      have b1734 := hb (x (-9) 10)
      have b1735 := hb (x (-8) 9)
      have b1736 := hb (x (-7) 8)
      clear * - r1722 e1723 e1724 e1725 e1726 e1727 e1728 b1729 b1730 b1731 b1732 b1733 b1734 b1735 b1736 d1669 d1689 d1705 d1653 d1661
      omega
    have d1737 : (x (-10) 1 && x (-10) 11).toNat = 0 := by
      have r1738 := hand2 (x (-10) 1) (x (-10) 11)
      have b1739 := hb (x (-10) 11)
      have b1740 := hb (x (-10) 1 && x (-10) 11)
      clear * - r1738 b1739 b1740 d1721
      omega
    have d1741 : (x (-5) 6 && x (-5) 12).toNat = 1 := by
      have r1742 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1743 := hb (x (-8) 9)
      have b1744 := hb (x 1 6)
      have b1745 := hb (x 0 1 && x 0 7)
      have b1746 := hb (x (-1) 2 && x (-1) 8)
      have b1747 := hb (x (-2) 3 && x (-2) 9)
      have b1748 := hb (x (-3) 4 && x (-3) 10)
      have b1749 := hb (x (-4) 5 && x (-4) 11)
      have b1750 := hb (x (-5) 6 && x (-5) 12)
      have b1751 := hb (x (-6) 7 && x (-6) 13)
      have b1752 := hb (x (-7) 8 && x (-7) 14)
      clear * - r1742 b1743 b1744 b1745 b1746 b1747 b1748 b1749 b1750 b1751 b1752 g8 g16 d1222 d545 d983 d1015 d1046 d1685 d1689
      omega
    have d1753 : (x (-5) 6).toNat = 1 := by
      have r1754 := hand1 (x (-5) 6) (x (-5) 12)
      have b1755 := hb (x (-5) 6)
      have b1756 := hb (x (-5) 6 && x (-5) 12)
      clear * - r1754 b1755 b1756 d1741
      omega
    have d1757 : (x (-5) 14).toNat = 1 := by
      have r1758 : (x (-5) 6).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp6 (-5))
      have b1759 := hb (x (-5) 6)
      have b1760 := hb (x (-5) 14)
      clear * - r1758 b1759 b1760 d1753
      omega
    have d1761 : (x (-6) 1).toNat = 0 := by
      have r1762 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1763 := hb (x (-6) 1)
      have b1764 := hb (x (-5) 14)
      clear * - r1762 b1763 b1764 d1757
      omega
    have d1765 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
      have r1766 := hand1 (x (-6) 1) (x (-6) 14)
      have b1767 := hb (x (-6) 1)
      have b1768 := hb (x (-6) 1 && x (-6) 14)
      clear * - r1766 b1767 b1768 d1761
      omega
    have d1769 : (x (-5) 13).toNat = 1 := by
      have r1770 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1771 := hb (x (-7) 2)
      have b1772 := hb (x (-5) 13)
      have b1773 := hb (x (-6) 1 && x (-6) 14)
      clear * - r1770 b1771 b1772 b1773 d1765 d1062
      omega
    have d1774 : (x (-5) 1).toNat = 1 := by
      have r1775 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
      have b1776 := hb (x (-5) 1)
      have b1777 := hb (x (-5) 13)
      clear * - r1775 b1776 b1777 d1769
      omega
    have d1778 : (x (-4) 14).toNat = 0 := by
      have r1779 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1780 := hb (x (-5) 1)
      have b1781 := hb (x (-4) 14)
      clear * - r1779 b1780 b1781 d1774
      omega
    have d1782 : (x (-4) 6).toNat = 0 := by
      have r1783 : (x (-4) 6).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp6 (-4))
      have b1784 := hb (x (-4) 6)
      have b1785 := hb (x (-4) 14)
      clear * - r1783 b1784 b1785 d1778
      omega
    have d1786 : (x (-3) 5 && x (-3) 14).toNat = 1 := by
      have r1787 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1788 := hb (x (-4) 6)
      have b1789 := hb (x 2 9)
      have b1790 := hb (x 1 1 && x 1 10)
      have b1791 := hb (x 0 2 && x 0 11)
      have b1792 := hb (x (-1) 3 && x (-1) 12)
      have b1793 := hb (x (-2) 4 && x (-2) 13)
      have b1794 := hb (x (-3) 5 && x (-3) 14)
      clear * - r1787 b1788 b1789 b1790 b1791 b1792 b1793 b1794 d1146 d447 g22 d690 d529 d1782
      omega
    have d1795 : (x (-3) 14).toNat = 1 := by
      have r1796 := hand2 (x (-3) 5) (x (-3) 14)
      have b1797 := hb (x (-3) 14)
      have b1798 := hb (x (-3) 5 && x (-3) 14)
      clear * - r1796 b1797 b1798 d1786
      omega
    have d1799 : (x (-4) 1).toNat = 0 := by
      have r1800 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1801 := hb (x (-4) 1)
      have b1802 := hb (x (-3) 14)
      clear * - r1800 b1801 b1802 d1795
      omega
    have d1803 : (x (-4) 13).toNat = 0 := by
      have r1804 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b1805 := hb (x (-4) 1)
      have b1806 := hb (x (-4) 13)
      clear * - r1804 b1805 b1806 d1799
      omega
    have d1807 : (x (-4) 9).toNat = 0 := by
      have r1808 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
      have b1809 := hb (x (-4) 1)
      have b1810 := hb (x (-4) 9)
      clear * - r1808 b1809 b1810 d1799
      omega
    have d1811 : (x (-3) 5).toNat = 1 := by
      have r1812 := hand1 (x (-3) 5) (x (-3) 14)
      have b1813 := hb (x (-3) 5)
      have b1814 := hb (x (-3) 5 && x (-3) 14)
      clear * - r1812 b1813 b1814 d1786
      omega
    have d1815 : (x (-3) 13).toNat = 1 := by
      have r1816 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have b1817 := hb (x (-3) 5)
      have b1818 := hb (x (-3) 13)
      clear * - r1816 b1817 b1818 d1811
      omega
    have d1819 : (x (-2) 12).toNat = 0 := by
      have r1820 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1821 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e1822 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b1823 := hb (x (-5) 3)
      have b1824 := hb (x (-4) 2)
      have b1825 := hb (x (-3) 13)
      have b1826 := hb (x (-2) 12)
      clear * - r1820 e1821 e1822 b1823 b1824 b1825 b1826 d1815
      omega
    have d1827 : (x (-4) 2).toNat = 0 := by
      have r1828 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1829 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e1830 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b1831 := hb (x (-5) 3)
      have b1832 := hb (x (-4) 2)
      have b1833 := hb (x (-3) 13)
      have b1834 := hb (x (-2) 12)
      clear * - r1828 e1829 e1830 b1831 b1832 b1833 b1834 d1819 d1815
      omega
    have d1835 : (x (-5) 3).toNat = 0 := by
      have r1836 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1837 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e1838 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b1839 := hb (x (-5) 3)
      have b1840 := hb (x (-4) 2)
      have b1841 := hb (x (-3) 13)
      have b1842 := hb (x (-2) 12)
      clear * - r1836 e1837 e1838 b1839 b1840 b1841 b1842 d1819 d1815 d1827
      omega
    have d1843 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
      have r1844 := hand1 (x (-5) 3) (x (-5) 12)
      have b1845 := hb (x (-5) 3)
      have b1846 := hb (x (-5) 3 && x (-5) 12)
      clear * - r1844 b1845 b1846 d1835
      omega
    have d1847 : (x (-5) 3 && x (-5) 8).toNat = 0 := by
      have r1848 := hand1 (x (-5) 3) (x (-5) 8)
      have b1849 := hb (x (-5) 3)
      have b1850 := hb (x (-5) 3 && x (-5) 8)
      clear * - r1848 b1849 b1850 d1835
      omega
    have d1851 : (x (-5) 11).toNat = 0 := by
      have r1852 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b1853 := hb (x (-5) 3)
      have b1854 := hb (x (-5) 11)
      clear * - r1852 b1853 b1854 d1835
      omega
    have d1855 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
      have r1856 := hand2 (x (-5) 4) (x (-5) 11)
      have b1857 := hb (x (-5) 11)
      have b1858 := hb (x (-5) 4 && x (-5) 11)
      clear * - r1856 b1857 b1858 d1851
      omega
    have d1859 : (x (-9) 8).toNat = 1 := by
      have r1860 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1861 := hb (x (-9) 8)
      have b1862 := hb (x (-1) 7)
      have b1863 := hb (x (-2) 1 && x (-2) 8)
      have b1864 := hb (x (-3) 2 && x (-3) 9)
      have b1865 := hb (x (-4) 3 && x (-4) 10)
      have b1866 := hb (x (-5) 4 && x (-5) 11)
      have b1867 := hb (x (-6) 5 && x (-6) 12)
      have b1868 := hb (x (-7) 6 && x (-7) 13)
      have b1869 := hb (x (-8) 7 && x (-8) 14)
      clear * - r1860 b1861 b1862 b1863 b1864 b1865 b1866 b1867 b1868 b1869 d766 d521 d971 d1003 d1855 d1058 d1246 d1266
      omega
    have d1870 : (x (-10) 9).toNat = 0 := by
      have r1871 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1872 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e1873 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e1874 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e1875 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e1876 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e1877 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b1878 := hb (x (-16) 7)
      have b1879 := hb (x (-15) 6)
      have b1880 := hb (x (-14) 5)
      have b1881 := hb (x (-13) 4)
      have b1882 := hb (x (-12) 11)
      have b1883 := hb (x (-11) 10)
      have b1884 := hb (x (-10) 9)
      have b1885 := hb (x (-9) 8)
      clear * - r1871 e1872 e1873 e1874 e1875 e1876 e1877 b1878 b1879 b1880 b1881 b1882 b1883 b1884 b1885 d1859
      omega
    have d1886 : (x (-11) 10).toNat = 0 := by
      have r1887 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1888 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e1889 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e1890 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e1891 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e1892 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e1893 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b1894 := hb (x (-16) 7)
      have b1895 := hb (x (-15) 6)
      have b1896 := hb (x (-14) 5)
      have b1897 := hb (x (-13) 4)
      have b1898 := hb (x (-12) 11)
      have b1899 := hb (x (-11) 10)
      have b1900 := hb (x (-10) 9)
      have b1901 := hb (x (-9) 8)
      clear * - r1887 e1888 e1889 e1890 e1891 e1892 e1893 b1894 b1895 b1896 b1897 b1898 b1899 b1900 b1901 d1859 d1870
      omega
    have d1902 : (x (-11) 1 && x (-11) 10).toNat = 0 := by
      have r1903 := hand2 (x (-11) 1) (x (-11) 10)
      have b1904 := hb (x (-11) 10)
      have b1905 := hb (x (-11) 1 && x (-11) 10)
      clear * - r1903 b1904 b1905 d1886
      omega
    have d1906 : (x (-12) 11).toNat = 0 := by
      have r1907 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1908 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e1909 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e1910 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e1911 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e1912 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e1913 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b1914 := hb (x (-16) 7)
      have b1915 := hb (x (-15) 6)
      have b1916 := hb (x (-14) 5)
      have b1917 := hb (x (-13) 4)
      have b1918 := hb (x (-12) 11)
      have b1919 := hb (x (-11) 10)
      have b1920 := hb (x (-10) 9)
      have b1921 := hb (x (-9) 8)
      clear * - r1907 e1908 e1909 e1910 e1911 e1912 e1913 b1914 b1915 b1916 b1917 b1918 b1919 b1920 b1921 d1859 d1870 d1886
      omega
    have d1922 : (x (-12) 1 && x (-12) 11).toNat = 0 := by
      have r1923 := hand2 (x (-12) 1) (x (-12) 11)
      have b1924 := hb (x (-12) 11)
      have b1925 := hb (x (-12) 1 && x (-12) 11)
      clear * - r1923 b1924 b1925 d1906
      omega
    have d1926 : (x (-12) 2 && x (-12) 11).toNat = 0 := by
      have r1927 := hand2 (x (-12) 2) (x (-12) 11)
      have b1928 := hb (x (-12) 11)
      have b1929 := hb (x (-12) 2 && x (-12) 11)
      clear * - r1927 b1928 b1929 d1906
      omega
    have d1930 : (x (-13) 4).toNat = 0 := by
      have r1931 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1932 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e1933 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e1934 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e1935 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e1936 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e1937 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b1938 := hb (x (-16) 7)
      have b1939 := hb (x (-15) 6)
      have b1940 := hb (x (-14) 5)
      have b1941 := hb (x (-13) 4)
      have b1942 := hb (x (-12) 11)
      have b1943 := hb (x (-11) 10)
      have b1944 := hb (x (-10) 9)
      have b1945 := hb (x (-9) 8)
      clear * - r1931 e1932 e1933 e1934 e1935 e1936 e1937 b1938 b1939 b1940 b1941 b1942 b1943 b1944 b1945 d1859 d1870 d1886 d1906
      omega
    have d1946 : (x (-13) 4 && x (-13) 14).toNat = 0 := by
      have r1947 := hand1 (x (-13) 4) (x (-13) 14)
      have b1948 := hb (x (-13) 4)
      have b1949 := hb (x (-13) 4 && x (-13) 14)
      clear * - r1947 b1948 b1949 d1930
      omega
    have d1950 : (x (-13) 4 && x (-13) 10).toNat = 0 := by
      have r1951 := hand1 (x (-13) 4) (x (-13) 10)
      have b1952 := hb (x (-13) 4)
      have b1953 := hb (x (-13) 4 && x (-13) 10)
      clear * - r1951 b1952 b1953 d1930
      omega
    have d1954 : (x (-13) 4 && x (-13) 8).toNat = 0 := by
      have r1955 := hand1 (x (-13) 4) (x (-13) 8)
      have b1956 := hb (x (-13) 4)
      have b1957 := hb (x (-13) 4 && x (-13) 8)
      clear * - r1955 b1956 b1957 d1930
      omega
    have d1958 : (x (-14) 5).toNat = 0 := by
      have r1959 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1960 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e1961 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e1962 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e1963 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e1964 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e1965 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b1966 := hb (x (-16) 7)
      have b1967 := hb (x (-15) 6)
      have b1968 := hb (x (-14) 5)
      have b1969 := hb (x (-13) 4)
      have b1970 := hb (x (-12) 11)
      have b1971 := hb (x (-11) 10)
      have b1972 := hb (x (-10) 9)
      have b1973 := hb (x (-9) 8)
      clear * - r1959 e1960 e1961 e1962 e1963 e1964 e1965 b1966 b1967 b1968 b1969 b1970 b1971 b1972 b1973 d1859 d1870 d1886 d1906 d1930
      omega
    have d1974 : (x (-14) 5 && x (-14) 11).toNat = 0 := by
      have r1975 := hand1 (x (-14) 5) (x (-14) 11)
      have b1976 := hb (x (-14) 5)
      have b1977 := hb (x (-14) 5 && x (-14) 11)
      clear * - r1975 b1976 b1977 d1958
      omega
    have d1978 : (x (-14) 5 && x (-14) 9).toNat = 0 := by
      have r1979 := hand1 (x (-14) 5) (x (-14) 9)
      have b1980 := hb (x (-14) 5)
      have b1981 := hb (x (-14) 5 && x (-14) 9)
      clear * - r1979 b1980 b1981 d1958
      omega
    have d1982 : (x (-12) 3 && x (-12) 13).toNat = 1 := by
      have r1983 : 1 ≤ (x (-9) 10).toNat + (x (-10) 1 && x (-10) 11).toNat + (x (-11) 2 && x (-11) 12).toNat + (x (-12) 3 && x (-12) 13).toNat + (x (-13) 4 && x (-13) 14).toNat + (x (-14) 5).toNat := by have q := hcov10 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1984 := hb (x (-14) 5)
      have b1985 := hb (x (-9) 10)
      have b1986 := hb (x (-10) 1 && x (-10) 11)
      have b1987 := hb (x (-11) 2 && x (-11) 12)
      have b1988 := hb (x (-12) 3 && x (-12) 13)
      have b1989 := hb (x (-13) 4 && x (-13) 14)
      clear * - r1983 b1984 b1985 b1986 b1987 b1988 b1989 d1705 d1737 d1649 d1946 d1958
      omega
    have d1990 : (x (-12) 3).toNat = 1 := by
      have r1991 := hand1 (x (-12) 3) (x (-12) 13)
      have b1992 := hb (x (-12) 3)
      have b1993 := hb (x (-12) 3 && x (-12) 13)
      clear * - r1991 b1992 b1993 d1982
      omega
    have d1994 : (x (-11) 2).toNat = 0 := by
      have r1995 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1996 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
      have e1997 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
      have b1998 := hb (x (-12) 3)
      have b1999 := hb (x (-11) 2)
      have b2000 := hb (x (-10) 13)
      have b2001 := hb (x (-9) 12)
      clear * - r1995 e1996 e1997 b1998 b1999 b2000 b2001 d1390 d1422 d1990
      omega
    have d2002 : (x (-11) 2 && x (-11) 8).toNat = 0 := by
      have r2003 := hand1 (x (-11) 2) (x (-11) 8)
      have b2004 := hb (x (-11) 2)
      have b2005 := hb (x (-11) 2 && x (-11) 8)
      clear * - r2003 b2004 b2005 d1994
      omega
    have d2006 : (x (-15) 6).toNat = 0 := by
      have r2007 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2008 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e2009 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e2010 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e2011 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e2012 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e2013 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b2014 := hb (x (-16) 7)
      have b2015 := hb (x (-15) 6)
      have b2016 := hb (x (-14) 5)
      have b2017 := hb (x (-13) 4)
      have b2018 := hb (x (-12) 11)
      have b2019 := hb (x (-11) 10)
      have b2020 := hb (x (-10) 9)
      have b2021 := hb (x (-9) 8)
      clear * - r2007 e2008 e2009 e2010 e2011 e2012 e2013 b2014 b2015 b2016 b2017 b2018 b2019 b2020 b2021 d1859 d1870 d1886 d1906 d1930 d1958
      omega
    have d2022 : (x (-15) 6 && x (-15) 12).toNat = 0 := by
      have r2023 := hand1 (x (-15) 6) (x (-15) 12)
      have b2024 := hb (x (-15) 6)
      have b2025 := hb (x (-15) 6 && x (-15) 12)
      clear * - r2023 b2024 b2025 d2006
      omega
    have d2026 : (x (-15) 6 && x (-15) 10).toNat = 0 := by
      have r2027 := hand1 (x (-15) 6) (x (-15) 10)
      have b2028 := hb (x (-15) 6)
      have b2029 := hb (x (-15) 6 && x (-15) 10)
      clear * - r2027 b2028 b2029 d2006
      omega
    have d2030 : (x (-16) 7).toNat = 0 := by
      have r2031 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2032 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e2033 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e2034 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e2035 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e2036 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e2037 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b2038 := hb (x (-16) 7)
      have b2039 := hb (x (-15) 6)
      have b2040 := hb (x (-14) 5)
      have b2041 := hb (x (-13) 4)
      have b2042 := hb (x (-12) 11)
      have b2043 := hb (x (-11) 10)
      have b2044 := hb (x (-10) 9)
      have b2045 := hb (x (-9) 8)
      clear * - r2031 e2032 e2033 e2034 e2035 e2036 e2037 b2038 b2039 b2040 b2041 b2042 b2043 b2044 b2045 d1859 d1870 d1886 d1906 d1930 d1958 d2006
      omega
    have d2046 : (x (-16) 7 && x (-16) 13).toNat = 0 := by
      have r2047 := hand1 (x (-16) 7) (x (-16) 13)
      have b2048 := hb (x (-16) 7)
      have b2049 := hb (x (-16) 7 && x (-16) 13)
      clear * - r2047 b2048 b2049 d2030
      omega
    have d2050 : (x (-16) 7 && x (-16) 11).toNat = 0 := by
      have r2051 := hand1 (x (-16) 7) (x (-16) 11)
      have b2052 := hb (x (-16) 7)
      have b2053 := hb (x (-16) 7 && x (-16) 11)
      clear * - r2051 b2052 b2053 d2030
      omega
    have d2054 : (x (-6) 1 && x (-6) 12).toNat = 1 := by
      have r2055 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2056 := hb (x (-9) 4)
      have b2057 := hb (x (-5) 11)
      have b2058 := hb (x (-6) 1 && x (-6) 12)
      have b2059 := hb (x (-7) 2 && x (-7) 13)
      have b2060 := hb (x (-8) 3 && x (-8) 14)
      clear * - r2055 b2056 b2057 b2058 b2059 b2060 d1851 d1070 d1102 d1314
      omega
    have d2061 : (x (-6) 12).toNat = 1 := by
      have r2062 := hand2 (x (-6) 1) (x (-6) 12)
      have b2063 := hb (x (-6) 12)
      have b2064 := hb (x (-6) 1 && x (-6) 12)
      clear * - r2062 b2063 b2064 d2054
      omega
    have d2065 : (x (-7) 13).toNat = 0 := by
      have r2066 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2067 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e2068 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b2069 := hb (x (-9) 3)
      have b2070 := hb (x (-8) 2)
      have b2071 := hb (x (-7) 13)
      have b2072 := hb (x (-6) 12)
      clear * - r2066 e2067 e2068 b2069 b2070 b2071 b2072 d2061
      omega
    have d2073 : (x (-7) 5).toNat = 0 := by
      have r2074 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b2075 := hb (x (-7) 5)
      have b2076 := hb (x (-7) 13)
      clear * - r2074 b2075 b2076 d2065
      omega
    have d2077 : (x (-7) 5 && x (-7) 14).toNat = 0 := by
      have r2078 := hand1 (x (-7) 5) (x (-7) 14)
      have b2079 := hb (x (-7) 5)
      have b2080 := hb (x (-7) 5 && x (-7) 14)
      clear * - r2078 b2079 b2080 d2073
      omega
    have d2081 : (x (-8) 6).toNat = 1 := by
      have r2082 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2083 := hb (x (-8) 6)
      have b2084 := hb (x (-2) 9)
      have b2085 := hb (x (-3) 1 && x (-3) 10)
      have b2086 := hb (x (-4) 2 && x (-4) 11)
      have b2087 := hb (x (-5) 3 && x (-5) 12)
      have b2088 := hb (x (-6) 4 && x (-6) 13)
      have b2089 := hb (x (-7) 5 && x (-7) 14)
      clear * - r2082 b2083 b2084 b2085 b2086 b2087 b2088 b2089 d541 d979 d1011 d1843 d1042 d2077
      omega
    have d2090 : (x (-8) 14).toNat = 1 := by
      have r2091 : (x (-8) 6).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp6 (-8))
      have b2092 := hb (x (-8) 6)
      have b2093 := hb (x (-8) 14)
      clear * - r2091 b2092 b2093 d2081
      omega
    have d2094 : (x (-9) 1).toNat = 0 := by
      have r2095 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2096 := hb (x (-9) 1)
      have b2097 := hb (x (-8) 14)
      clear * - r2095 b2096 b2097 d2090
      omega
    have d2098 : (x (-9) 13).toNat = 0 := by
      have r2099 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
      have b2100 := hb (x (-9) 1)
      have b2101 := hb (x (-9) 13)
      clear * - r2099 b2100 b2101 d2094
      omega
    have d2102 : (x (-10) 1 && x (-10) 14).toNat = 1 := by
      have r2103 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2104 := hb (x (-11) 2)
      have b2105 := hb (x (-9) 13)
      have b2106 := hb (x (-10) 1 && x (-10) 14)
      clear * - r2103 b2104 b2105 b2106 d2098 d1994
      omega
    have d2107 : (x (-10) 14).toNat = 1 := by
      have r2108 := hand2 (x (-10) 1) (x (-10) 14)
      have b2109 := hb (x (-10) 14)
      have b2110 := hb (x (-10) 1 && x (-10) 14)
      clear * - r2108 b2109 b2110 d2102
      omega
    have d2111 : (x (-11) 1).toNat = 0 := by
      have r2112 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2113 := hb (x (-11) 1)
      have b2114 := hb (x (-10) 14)
      clear * - r2112 b2113 b2114 d2107
      omega
    have d2115 : (x (-11) 9).toNat = 0 := by
      have r2116 : (x (-11) 9).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp9 (-11))
      have b2117 := hb (x (-11) 1)
      have b2118 := hb (x (-11) 9)
      clear * - r2116 b2117 b2118 d2111
      omega
    have d2119 : (x (-11) 9 && x (-11) 14).toNat = 0 := by
      have r2120 := hand1 (x (-11) 9) (x (-11) 14)
      have b2121 := hb (x (-11) 9)
      have b2122 := hb (x (-11) 9 && x (-11) 14)
      clear * - r2120 b2121 b2122 d2115
      omega
    have d2123 : (x (-12) 10).toNat = 1 := by
      have r2124 : 1 ≤ (x (-2) 5).toNat + (x (-3) 1 && x (-3) 6).toNat + (x (-4) 2 && x (-4) 7).toNat + (x (-5) 3 && x (-5) 8).toNat + (x (-6) 4 && x (-6) 9).toNat + (x (-7) 5 && x (-7) 10).toNat + (x (-8) 6 && x (-8) 11).toNat + (x (-9) 7 && x (-9) 12).toNat + (x (-10) 8 && x (-10) 13).toNat + (x (-11) 9 && x (-11) 14).toNat + (x (-12) 10).toNat := by have q := hcov5 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2125 := hb (x (-12) 10)
      have b2126 := hb (x (-2) 5)
      have b2127 := hb (x (-3) 1 && x (-3) 6)
      have b2128 := hb (x (-4) 2 && x (-4) 7)
      have b2129 := hb (x (-5) 3 && x (-5) 8)
      have b2130 := hb (x (-6) 4 && x (-6) 9)
      have b2131 := hb (x (-7) 5 && x (-7) 10)
      have b2132 := hb (x (-8) 6 && x (-8) 11)
      have b2133 := hb (x (-9) 7 && x (-9) 12)
      have b2134 := hb (x (-10) 8 && x (-10) 13)
      have b2135 := hb (x (-11) 9 && x (-11) 14)
      clear * - r2124 b2125 b2126 b2127 b2128 b2129 b2130 b2131 b2132 b2133 b2134 b2135 d533 d1178 d1202 d1847 d1310 d1090 d1126 d1418 d1450 d2119
      omega
    have d2136 : (x (-10) 8).toNat = 0 := by
      have r2137 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2138 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
      have e2139 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
      have e2140 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
      have e2141 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
      have e2142 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
      have e2143 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
      have b2144 := hb (x (-17) 7)
      have b2145 := hb (x (-16) 6)
      have b2146 := hb (x (-15) 5)
      have b2147 := hb (x (-14) 4)
      have b2148 := hb (x (-13) 11)
      have b2149 := hb (x (-12) 10)
      have b2150 := hb (x (-11) 9)
      have b2151 := hb (x (-10) 8)
      clear * - r2137 e2138 e2139 e2140 e2141 e2142 e2143 b2144 b2145 b2146 b2147 b2148 b2149 b2150 b2151 d2115 d2123
      omega
    have d2152 : (x (-13) 11).toNat = 0 := by
      have r2153 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2154 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
      have e2155 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
      have e2156 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
      have e2157 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
      have e2158 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
      have e2159 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
      have b2160 := hb (x (-17) 7)
      have b2161 := hb (x (-16) 6)
      have b2162 := hb (x (-15) 5)
      have b2163 := hb (x (-14) 4)
      have b2164 := hb (x (-13) 11)
      have b2165 := hb (x (-12) 10)
      have b2166 := hb (x (-11) 9)
      have b2167 := hb (x (-10) 8)
      clear * - r2153 e2154 e2155 e2156 e2157 e2158 e2159 b2160 b2161 b2162 b2163 b2164 b2165 b2166 b2167 d2136 d2115 d2123
      omega
    have d2168 : (x (-14) 4).toNat = 0 := by
      have r2169 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2170 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
      have e2171 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
      have e2172 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
      have e2173 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
      have e2174 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
      have e2175 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
      have b2176 := hb (x (-17) 7)
      have b2177 := hb (x (-16) 6)
      have b2178 := hb (x (-15) 5)
      have b2179 := hb (x (-14) 4)
      have b2180 := hb (x (-13) 11)
      have b2181 := hb (x (-12) 10)
      have b2182 := hb (x (-11) 9)
      have b2183 := hb (x (-10) 8)
      clear * - r2169 e2170 e2171 e2172 e2173 e2174 e2175 b2176 b2177 b2178 b2179 b2180 b2181 b2182 b2183 d2136 d2115 d2123 d2152
      omega
    have d2184 : (x (-14) 4 && x (-14) 13).toNat = 0 := by
      have r2185 := hand1 (x (-14) 4) (x (-14) 13)
      have b2186 := hb (x (-14) 4)
      have b2187 := hb (x (-14) 4 && x (-14) 13)
      clear * - r2185 b2186 b2187 d2168
      omega
    have d2188 : (x (-15) 5).toNat = 0 := by
      have r2189 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2190 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
      have e2191 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
      have e2192 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
      have e2193 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
      have e2194 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
      have e2195 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
      have b2196 := hb (x (-17) 7)
      have b2197 := hb (x (-16) 6)
      have b2198 := hb (x (-15) 5)
      have b2199 := hb (x (-14) 4)
      have b2200 := hb (x (-13) 11)
      have b2201 := hb (x (-12) 10)
      have b2202 := hb (x (-11) 9)
      have b2203 := hb (x (-10) 8)
      clear * - r2189 e2190 e2191 e2192 e2193 e2194 e2195 b2196 b2197 b2198 b2199 b2200 b2201 b2202 b2203 d2136 d2115 d2123 d2152 d2168
      omega
    have d2204 : (x (-15) 5 && x (-15) 14).toNat = 0 := by
      have r2205 := hand1 (x (-15) 5) (x (-15) 14)
      have b2206 := hb (x (-15) 5)
      have b2207 := hb (x (-15) 5 && x (-15) 14)
      clear * - r2205 b2206 b2207 d2188
      omega
    have d2208 : (x (-16) 6).toNat = 0 := by
      have r2209 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2210 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
      have e2211 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
      have e2212 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
      have e2213 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
      have e2214 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
      have e2215 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
      have b2216 := hb (x (-17) 7)
      have b2217 := hb (x (-16) 6)
      have b2218 := hb (x (-15) 5)
      have b2219 := hb (x (-14) 4)
      have b2220 := hb (x (-13) 11)
      have b2221 := hb (x (-12) 10)
      have b2222 := hb (x (-11) 9)
      have b2223 := hb (x (-10) 8)
      clear * - r2209 e2210 e2211 e2212 e2213 e2214 e2215 b2216 b2217 b2218 b2219 b2220 b2221 b2222 b2223 d2136 d2115 d2123 d2152 d2168 d2188
      omega
    have d2224 : (x (-13) 3 && x (-13) 12).toNat = 1 := by
      have r2225 : 1 ≤ (x (-10) 9).toNat + (x (-11) 1 && x (-11) 10).toNat + (x (-12) 2 && x (-12) 11).toNat + (x (-13) 3 && x (-13) 12).toNat + (x (-14) 4 && x (-14) 13).toNat + (x (-15) 5 && x (-15) 14).toNat + (x (-16) 6).toNat := by have q := hcov9 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2226 := hb (x (-16) 6)
      have b2227 := hb (x (-10) 9)
      have b2228 := hb (x (-11) 1 && x (-11) 10)
      have b2229 := hb (x (-12) 2 && x (-12) 11)
      have b2230 := hb (x (-13) 3 && x (-13) 12)
      have b2231 := hb (x (-14) 4 && x (-14) 13)
      have b2232 := hb (x (-15) 5 && x (-15) 14)
      clear * - r2225 b2226 b2227 b2228 b2229 b2230 b2231 b2232 d1870 d1902 d1926 d2184 d2204 d2208
      omega
    have d2233 : (x (-13) 12).toNat = 1 := by
      have r2234 := hand2 (x (-13) 3) (x (-13) 12)
      have b2235 := hb (x (-13) 12)
      have b2236 := hb (x (-13) 3 && x (-13) 12)
      clear * - r2234 b2235 b2236 d2224
      omega
    have d2237 : (x (-14) 13).toNat = 0 := by
      have r2238 : (x (-13) 12).toNat + (x (-14) 1 && x (-14) 13).toNat + (x (-15) 2 && x (-15) 14).toNat + (x (-16) 3).toNat = 1 := by have q := hd12 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2239 : (x (-14) 1 && x (-14) 13).toNat = (x (-14) 13).toNat := handr _ _ (fun h => hp13 (-14) (h))
      have e2240 : (x (-15) 2 && x (-15) 14).toNat = (x (-15) 2).toNat := handl _ _ (fun h => hp2 (-15) (h))
      have b2241 := hb (x (-16) 3)
      have b2242 := hb (x (-15) 2)
      have b2243 := hb (x (-14) 13)
      have b2244 := hb (x (-13) 12)
      clear * - r2238 e2239 e2240 b2241 b2242 b2243 b2244 d2233
      omega
    have d2245 : (x (-14) 3 && x (-14) 13).toNat = 0 := by
      have r2246 := hand2 (x (-14) 3) (x (-14) 13)
      have b2247 := hb (x (-14) 13)
      have b2248 := hb (x (-14) 3 && x (-14) 13)
      clear * - r2246 b2247 b2248 d2237
      omega
    have d2249 : (x (-15) 2).toNat = 0 := by
      have r2250 : (x (-13) 12).toNat + (x (-14) 1 && x (-14) 13).toNat + (x (-15) 2 && x (-15) 14).toNat + (x (-16) 3).toNat = 1 := by have q := hd12 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2251 : (x (-14) 1 && x (-14) 13).toNat = (x (-14) 13).toNat := handr _ _ (fun h => hp13 (-14) (h))
      have e2252 : (x (-15) 2 && x (-15) 14).toNat = (x (-15) 2).toNat := handl _ _ (fun h => hp2 (-15) (h))
      have b2253 := hb (x (-16) 3)
      have b2254 := hb (x (-15) 2)
      have b2255 := hb (x (-14) 13)
      have b2256 := hb (x (-13) 12)
      clear * - r2250 e2251 e2252 b2253 b2254 b2255 b2256 d2233 d2237
      omega
    have d2257 : (x (-15) 2 && x (-15) 13).toNat = 0 := by
      have r2258 := hand1 (x (-15) 2) (x (-15) 13)
      have b2259 := hb (x (-15) 2)
      have b2260 := hb (x (-15) 2 && x (-15) 13)
      clear * - r2258 b2259 b2260 d2249
      omega
    have d2261 : (x (-14) 1 && x (-14) 14).toNat = 1 := by
      have r2262 : 1 ≤ (x (-13) 13).toNat + (x (-14) 1 && x (-14) 14).toNat + (x (-15) 2).toNat := by have q := hcov13 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2263 := hb (x (-15) 2)
      have b2264 := hb (x (-13) 13)
      have b2265 := hb (x (-14) 1 && x (-14) 14)
      clear * - r2262 b2263 b2264 b2265 d1491 d2249
      omega
    have d2266 : (x (-14) 14).toNat = 1 := by
      have r2267 := hand2 (x (-14) 1) (x (-14) 14)
      have b2268 := hb (x (-14) 14)
      have b2269 := hb (x (-14) 1 && x (-14) 14)
      clear * - r2267 b2268 b2269 d2261
      omega
    have d2270 : (x (-15) 1).toNat = 0 := by
      have r2271 : (x (-14) 14).toNat + (x (-15) 1).toNat = 1 := by have q := hd14 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2272 := hb (x (-15) 1)
      have b2273 := hb (x (-14) 14)
      clear * - r2271 b2272 b2273 d2266
      omega
    have d2274 : (x (-15) 1 && x (-15) 14).toNat = 0 := by
      have r2275 := hand1 (x (-15) 1) (x (-15) 14)
      have b2276 := hb (x (-15) 1)
      have b2277 := hb (x (-15) 1 && x (-15) 14)
      clear * - r2275 b2276 b2277 d2270
      omega
    have d2278 : (x (-16) 2).toNat = 1 := by
      have r2279 : 1 ≤ (x (-14) 13).toNat + (x (-15) 1 && x (-15) 14).toNat + (x (-16) 2).toNat := by have q := hcov13 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2280 := hb (x (-16) 2)
      have b2281 := hb (x (-14) 13)
      have b2282 := hb (x (-15) 1 && x (-15) 14)
      clear * - r2279 b2280 b2281 b2282 d2237 d2274
      omega
    have d2283 : (x (-16) 14).toNat = 1 := by
      have r2284 : (x (-16) 2).toNat ≤ (x (-16) 14).toNat := himp _ _ (hp2 (-16))
      have b2285 := hb (x (-16) 2)
      have b2286 := hb (x (-16) 14)
      clear * - r2284 b2285 b2286 d2278
      omega
    have d2287 : (x (-17) 1).toNat = 0 := by
      have r2288 : (x (-16) 14).toNat + (x (-17) 1).toNat = 1 := by have q := hd14 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2289 := hb (x (-17) 1)
      have b2290 := hb (x (-16) 14)
      clear * - r2288 b2289 b2290 d2283
      omega
    have d2291 : (x (-17) 13).toNat = 0 := by
      have r2292 : (x (-17) 13).toNat ≤ (x (-17) 1).toNat := himp _ _ (hp13 (-17))
      have b2293 := hb (x (-17) 1)
      have b2294 := hb (x (-17) 13)
      clear * - r2292 b2293 b2294 d2287
      omega
    have d2295 : (x (-14) 12).toNat = 0 := by
      have r2296 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2297 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
      have e2298 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
      have b2299 := hb (x (-17) 3)
      have b2300 := hb (x (-16) 2)
      have b2301 := hb (x (-15) 13)
      have b2302 := hb (x (-14) 12)
      clear * - r2296 e2297 e2298 b2299 b2300 b2301 b2302 d2278
      omega
    have d2303 : (x (-14) 1 && x (-14) 12).toNat = 0 := by
      have r2304 := hand2 (x (-14) 1) (x (-14) 12)
      have b2305 := hb (x (-14) 12)
      have b2306 := hb (x (-14) 1 && x (-14) 12)
      clear * - r2304 b2305 b2306 d2295
      omega
    have d2307 : (x (-15) 13).toNat = 0 := by
      have r2308 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2309 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
      have e2310 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
      have b2311 := hb (x (-17) 3)
      have b2312 := hb (x (-16) 2)
      have b2313 := hb (x (-15) 13)
      have b2314 := hb (x (-14) 12)
      clear * - r2308 e2309 e2310 b2311 b2312 b2313 b2314 d2295 d2278
      omega
    have d2315 : (x (-14) 1).toNat = 1 := by
      have r2316 := hand1 (x (-14) 1) (x (-14) 14)
      have b2317 := hb (x (-14) 1)
      have b2318 := hb (x (-14) 1 && x (-14) 14)
      clear * - r2316 b2317 b2318 d2261
      omega
    have d2319 : (x (-13) 14).toNat = 0 := by
      have r2320 : (x (-13) 14).toNat + (x (-14) 1).toNat = 1 := by have q := hd14 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2321 := hb (x (-14) 1)
      have b2322 := hb (x (-13) 14)
      clear * - r2320 b2321 b2322 d2315
      omega
    have d2323 : (x (-13) 2).toNat = 0 := by
      have r2324 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
      have b2325 := hb (x (-13) 2)
      have b2326 := hb (x (-13) 14)
      clear * - r2324 b2325 b2326 d2319
      omega
    have d2327 : (x (-13) 2 && x (-13) 12).toNat = 0 := by
      have r2328 := hand1 (x (-13) 2) (x (-13) 12)
      have b2329 := hb (x (-13) 2)
      have b2330 := hb (x (-13) 2 && x (-13) 12)
      clear * - r2328 b2329 b2330 d2323
      omega
    have d2331 : (x (-13) 10).toNat = 0 := by
      have r2332 : (x (-13) 10).toNat ≤ (x (-13) 2).toNat := himp _ _ (hp10 (-13))
      have b2333 := hb (x (-13) 2)
      have b2334 := hb (x (-13) 10)
      clear * - r2332 b2333 b2334 d2323
      omega
    have d2335 : (x (-16) 3).toNat = 0 := by
      have r2336 : (x (-13) 12).toNat + (x (-14) 1 && x (-14) 13).toNat + (x (-15) 2 && x (-15) 14).toNat + (x (-16) 3).toNat = 1 := by have q := hd12 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2337 : (x (-14) 1 && x (-14) 13).toNat = (x (-14) 13).toNat := handr _ _ (fun h => hp13 (-14) (h))
      have e2338 : (x (-15) 2 && x (-15) 14).toNat = (x (-15) 2).toNat := handl _ _ (fun h => hp2 (-15) (h))
      have b2339 := hb (x (-16) 3)
      have b2340 := hb (x (-15) 2)
      have b2341 := hb (x (-14) 13)
      have b2342 := hb (x (-13) 12)
      clear * - r2336 e2337 e2338 b2339 b2340 b2341 b2342 d2233 d2237 d2249
      omega
    have d2343 : (x (-16) 3 && x (-16) 14).toNat = 0 := by
      have r2344 := hand1 (x (-16) 3) (x (-16) 14)
      have b2345 := hb (x (-16) 3)
      have b2346 := hb (x (-16) 3 && x (-16) 14)
      clear * - r2344 b2345 b2346 d2335
      omega
    have d2347 : (x (-17) 4).toNat = 1 := by
      have r2348 : 1 ≤ (x (-13) 11).toNat + (x (-14) 1 && x (-14) 12).toNat + (x (-15) 2 && x (-15) 13).toNat + (x (-16) 3 && x (-16) 14).toNat + (x (-17) 4).toNat := by have q := hcov11 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2349 := hb (x (-17) 4)
      have b2350 := hb (x (-13) 11)
      have b2351 := hb (x (-14) 1 && x (-14) 12)
      have b2352 := hb (x (-15) 2 && x (-15) 13)
      have b2353 := hb (x (-16) 3 && x (-16) 14)
      clear * - r2348 b2349 b2350 b2351 b2352 b2353 d2152 d2303 d2257 d2343
      omega
    have d2354 : (x (-17) 12).toNat = 1 := by
      have r2355 : (x (-17) 4).toNat ≤ (x (-17) 12).toNat := himp _ _ (hp4 (-17))
      have b2356 := hb (x (-17) 4)
      have b2357 := hb (x (-17) 12)
      clear * - r2355 b2356 b2357 d2347
      omega
    have d2358 : (x (-18) 13).toNat = 0 := by
      have r2359 : (x (-17) 12).toNat + (x (-18) 1 && x (-18) 13).toNat + (x (-19) 2 && x (-19) 14).toNat + (x (-20) 3).toNat = 1 := by have q := hd12 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2360 : (x (-18) 1 && x (-18) 13).toNat = (x (-18) 13).toNat := handr _ _ (fun h => hp13 (-18) (h))
      have e2361 : (x (-19) 2 && x (-19) 14).toNat = (x (-19) 2).toNat := handl _ _ (fun h => hp2 (-19) (h))
      have b2362 := hb (x (-20) 3)
      have b2363 := hb (x (-19) 2)
      have b2364 := hb (x (-18) 13)
      have b2365 := hb (x (-17) 12)
      clear * - r2359 e2360 e2361 b2362 b2363 b2364 b2365 d2354
      omega
    have d2366 : (x (-18) 9 && x (-18) 13).toNat = 0 := by
      have r2367 := hand2 (x (-18) 9) (x (-18) 13)
      have b2368 := hb (x (-18) 13)
      have b2369 := hb (x (-18) 9 && x (-18) 13)
      clear * - r2367 b2368 b2369 d2358
      omega
    have d2370 : (x (-19) 2).toNat = 0 := by
      have r2371 : (x (-17) 12).toNat + (x (-18) 1 && x (-18) 13).toNat + (x (-19) 2 && x (-19) 14).toNat + (x (-20) 3).toNat = 1 := by have q := hd12 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2372 : (x (-18) 1 && x (-18) 13).toNat = (x (-18) 13).toNat := handr _ _ (fun h => hp13 (-18) (h))
      have e2373 : (x (-19) 2 && x (-19) 14).toNat = (x (-19) 2).toNat := handl _ _ (fun h => hp2 (-19) (h))
      have b2374 := hb (x (-20) 3)
      have b2375 := hb (x (-19) 2)
      have b2376 := hb (x (-18) 13)
      have b2377 := hb (x (-17) 12)
      clear * - r2371 e2372 e2373 b2374 b2375 b2376 b2377 d2354 d2358
      omega
    have d2378 : (x (-19) 10).toNat = 0 := by
      have r2379 : (x (-19) 10).toNat ≤ (x (-19) 2).toNat := himp _ _ (hp10 (-19))
      have b2380 := hb (x (-19) 2)
      have b2381 := hb (x (-19) 10)
      clear * - r2379 b2380 b2381 d2370
      omega
    have d2382 : (x (-18) 1 && x (-18) 14).toNat = 1 := by
      have r2383 : 1 ≤ (x (-17) 13).toNat + (x (-18) 1 && x (-18) 14).toNat + (x (-19) 2).toNat := by have q := hcov13 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2384 := hb (x (-19) 2)
      have b2385 := hb (x (-17) 13)
      have b2386 := hb (x (-18) 1 && x (-18) 14)
      clear * - r2383 b2384 b2385 b2386 d2291 d2370
      omega
    have d2387 : (x (-18) 1).toNat = 1 := by
      have r2388 := hand1 (x (-18) 1) (x (-18) 14)
      have b2389 := hb (x (-18) 1)
      have b2390 := hb (x (-18) 1 && x (-18) 14)
      clear * - r2388 b2389 b2390 d2382
      omega
    have d2391 : (x (-17) 14).toNat = 0 := by
      have r2392 : (x (-17) 14).toNat + (x (-18) 1).toNat = 1 := by have q := hd14 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2393 := hb (x (-18) 1)
      have b2394 := hb (x (-17) 14)
      clear * - r2392 b2393 b2394 d2387
      omega
    have d2395 : (x (-17) 8 && x (-17) 14).toNat = 0 := by
      have r2396 := hand2 (x (-17) 8) (x (-17) 14)
      have b2397 := hb (x (-17) 14)
      have b2398 := hb (x (-17) 8 && x (-17) 14)
      clear * - r2396 b2397 b2398 d2391
      omega
    have d2399 : (x (-17) 6).toNat = 0 := by
      have r2400 : (x (-17) 6).toNat ≤ (x (-17) 14).toNat := himp _ _ (hp6 (-17))
      have b2401 := hb (x (-17) 6)
      have b2402 := hb (x (-17) 14)
      clear * - r2400 b2401 b2402 d2391
      omega
    have d2403 : (x (-17) 2).toNat = 0 := by
      have r2404 : (x (-17) 2).toNat ≤ (x (-17) 14).toNat := himp _ _ (hp2 (-17))
      have b2405 := hb (x (-17) 2)
      have b2406 := hb (x (-17) 14)
      clear * - r2404 b2405 b2406 d2391
      omega
    have d2407 : (x (-16) 1 && x (-16) 14).toNat = 1 := by
      have r2408 : 1 ≤ (x (-15) 13).toNat + (x (-16) 1 && x (-16) 14).toNat + (x (-17) 2).toNat := by have q := hcov13 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2409 := hb (x (-17) 2)
      have b2410 := hb (x (-15) 13)
      have b2411 := hb (x (-16) 1 && x (-16) 14)
      clear * - r2408 b2409 b2410 b2411 d2307 d2403
      omega
    have d2412 : (x (-16) 1).toNat = 1 := by
      have r2413 := hand1 (x (-16) 1) (x (-16) 14)
      have b2414 := hb (x (-16) 1)
      have b2415 := hb (x (-16) 1 && x (-16) 14)
      clear * - r2413 b2414 b2415 d2407
      omega
    have d2416 : (x (-15) 14).toNat = 0 := by
      have r2417 : (x (-15) 14).toNat + (x (-16) 1).toNat = 1 := by have q := hd14 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2418 := hb (x (-16) 1)
      have b2419 := hb (x (-15) 14)
      clear * - r2417 b2418 b2419 d2412
      omega
    have d2420 : (x (-15) 4 && x (-15) 14).toNat = 0 := by
      have r2421 := hand2 (x (-15) 4) (x (-15) 14)
      have b2422 := hb (x (-15) 14)
      have b2423 := hb (x (-15) 4 && x (-15) 14)
      clear * - r2421 b2422 b2423 d2416
      omega
    have d2424 : (x (-16) 5).toNat = 1 := by
      have r2425 : 1 ≤ (x (-11) 10).toNat + (x (-12) 1 && x (-12) 11).toNat + (x (-13) 2 && x (-13) 12).toNat + (x (-14) 3 && x (-14) 13).toNat + (x (-15) 4 && x (-15) 14).toNat + (x (-16) 5).toNat := by have q := hcov10 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2426 := hb (x (-16) 5)
      have b2427 := hb (x (-11) 10)
      have b2428 := hb (x (-12) 1 && x (-12) 11)
      have b2429 := hb (x (-13) 2 && x (-13) 12)
      have b2430 := hb (x (-14) 3 && x (-14) 13)
      have b2431 := hb (x (-15) 4 && x (-15) 14)
      clear * - r2425 b2426 b2427 b2428 b2429 b2430 b2431 d1886 d1922 d2327 d2245 d2420
      omega
    have d2432 : (x (-11) 8).toNat = 0 := by
      have r2433 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2434 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
      have e2435 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
      have e2436 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
      have e2437 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
      have e2438 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
      have e2439 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
      have b2440 := hb (x (-18) 7)
      have b2441 := hb (x (-17) 6)
      have b2442 := hb (x (-16) 5)
      have b2443 := hb (x (-15) 4)
      have b2444 := hb (x (-14) 11)
      have b2445 := hb (x (-13) 10)
      have b2446 := hb (x (-12) 9)
      have b2447 := hb (x (-11) 8)
      clear * - r2433 e2434 e2435 e2436 e2437 e2438 e2439 b2440 b2441 b2442 b2443 b2444 b2445 b2446 b2447 d2331 d2424 d2399
      omega
    have d2448 : (x (-11) 8 && x (-11) 14).toNat = 0 := by
      have r2449 := hand1 (x (-11) 8) (x (-11) 14)
      have b2450 := hb (x (-11) 8)
      have b2451 := hb (x (-11) 8 && x (-11) 14)
      clear * - r2449 b2450 b2451 d2432
      omega
    have d2452 : (x (-12) 9).toNat = 0 := by
      have r2453 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2454 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
      have e2455 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
      have e2456 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
      have e2457 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
      have e2458 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
      have e2459 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
      have b2460 := hb (x (-18) 7)
      have b2461 := hb (x (-17) 6)
      have b2462 := hb (x (-16) 5)
      have b2463 := hb (x (-15) 4)
      have b2464 := hb (x (-14) 11)
      have b2465 := hb (x (-13) 10)
      have b2466 := hb (x (-12) 9)
      have b2467 := hb (x (-11) 8)
      clear * - r2453 e2454 e2455 e2456 e2457 e2458 e2459 b2460 b2461 b2462 b2463 b2464 b2465 b2466 b2467 d2432 d2331 d2424 d2399
      omega
    have d2468 : (x (-12) 3 && x (-12) 9).toNat = 0 := by
      have r2469 := hand2 (x (-12) 3) (x (-12) 9)
      have b2470 := hb (x (-12) 9)
      have b2471 := hb (x (-12) 3 && x (-12) 9)
      clear * - r2469 b2470 b2471 d2452
      omega
    have d2472 : (x (-5) 2 && x (-5) 8).toNat = 1 := by
      have r2473 : 1 ≤ (x (-3) 6).toNat + (x (-4) 1 && x (-4) 7).toNat + (x (-5) 2 && x (-5) 8).toNat + (x (-6) 3 && x (-6) 9).toNat + (x (-7) 4 && x (-7) 10).toNat + (x (-8) 5 && x (-8) 11).toNat + (x (-9) 6 && x (-9) 12).toNat + (x (-10) 7 && x (-10) 13).toNat + (x (-11) 8 && x (-11) 14).toNat + (x (-12) 9).toNat := by have q := hcov6 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2474 := hb (x (-12) 9)
      have b2475 := hb (x (-3) 6)
      have b2476 := hb (x (-4) 1 && x (-4) 7)
      have b2477 := hb (x (-5) 2 && x (-5) 8)
      have b2478 := hb (x (-6) 3 && x (-6) 9)
      have b2479 := hb (x (-7) 4 && x (-7) 10)
      have b2480 := hb (x (-8) 5 && x (-8) 11)
      have b2481 := hb (x (-9) 6 && x (-9) 12)
      have b2482 := hb (x (-10) 7 && x (-10) 13)
      have b2483 := hb (x (-11) 8 && x (-11) 14)
      clear * - r2473 b2474 b2475 b2476 b2477 b2478 b2479 b2480 b2481 b2482 b2483 d1162 d1198 d1306 d1086 d1122 d1414 d1446 d2448 d2452
      omega
    have d2484 : (x (-5) 2).toNat = 1 := by
      have r2485 := hand1 (x (-5) 2) (x (-5) 8)
      have b2486 := hb (x (-5) 2)
      have b2487 := hb (x (-5) 2 && x (-5) 8)
      clear * - r2485 b2486 b2487 d2472
      omega
    have d2488 : (x (-3) 12).toNat = 0 := by
      have r2489 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2490 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e2491 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b2492 := hb (x (-6) 3)
      have b2493 := hb (x (-5) 2)
      have b2494 := hb (x (-4) 13)
      have b2495 := hb (x (-3) 12)
      clear * - r2489 e2490 e2491 b2492 b2493 b2494 b2495 d1803 d2484
      omega
    have d2496 : (x (-6) 3).toNat = 0 := by
      have r2497 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2498 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e2499 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b2500 := hb (x (-6) 3)
      have b2501 := hb (x (-5) 2)
      have b2502 := hb (x (-4) 13)
      have b2503 := hb (x (-3) 12)
      clear * - r2497 e2498 e2499 b2500 b2501 b2502 b2503 d2488 d1803 d2484
      omega
    have d2504 : (x (-6) 11).toNat = 0 := by
      have r2505 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
      have b2506 := hb (x (-6) 3)
      have b2507 := hb (x (-6) 11)
      clear * - r2505 b2506 b2507 d2496
      omega
    have d2508 : (x (-6) 1 && x (-6) 11).toNat = 0 := by
      have r2509 := hand2 (x (-6) 1) (x (-6) 11)
      have b2510 := hb (x (-6) 11)
      have b2511 := hb (x (-6) 1 && x (-6) 11)
      clear * - r2509 b2510 b2511 d2504
      omega
    have d2512 : (x (-5) 10).toNat = 1 := by
      have r2513 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2514 := hb (x (-10) 5)
      have b2515 := hb (x (-5) 10)
      have b2516 := hb (x (-6) 1 && x (-6) 11)
      have b2517 := hb (x (-7) 2 && x (-7) 12)
      have b2518 := hb (x (-8) 3 && x (-8) 13)
      have b2519 := hb (x (-9) 4 && x (-9) 14)
      clear * - r2513 b2514 b2515 b2516 b2517 b2518 b2519 d2508 d1074 d1106 d1330 d1334
      omega
    have d2520 : (x (-3) 8).toNat = 0 := by
      have r2521 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2522 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e2523 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e2524 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e2525 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e2526 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e2527 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have b2528 := hb (x (-10) 7)
      have b2529 := hb (x (-9) 6)
      have b2530 := hb (x (-8) 5)
      have b2531 := hb (x (-7) 4)
      have b2532 := hb (x (-6) 11)
      have b2533 := hb (x (-5) 10)
      have b2534 := hb (x (-4) 9)
      have b2535 := hb (x (-3) 8)
      clear * - r2521 e2522 e2523 e2524 e2525 e2526 e2527 b2528 b2529 b2530 b2531 b2532 b2533 b2534 b2535 d1807 d2512 d2504
      omega
    have d2536 : (x (-7) 4).toNat = 0 := by
      have r2537 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2538 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e2539 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e2540 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e2541 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e2542 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e2543 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have b2544 := hb (x (-10) 7)
      have b2545 := hb (x (-9) 6)
      have b2546 := hb (x (-8) 5)
      have b2547 := hb (x (-7) 4)
      have b2548 := hb (x (-6) 11)
      have b2549 := hb (x (-5) 10)
      have b2550 := hb (x (-4) 9)
      have b2551 := hb (x (-3) 8)
      clear * - r2537 e2538 e2539 e2540 e2541 e2542 e2543 b2544 b2545 b2546 b2547 b2548 b2549 b2550 b2551 d2520 d1807 d2512 d2504
      omega
    have d2552 : (x (-8) 5).toNat = 0 := by
      have r2553 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2554 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e2555 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e2556 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e2557 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e2558 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e2559 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have b2560 := hb (x (-10) 7)
      have b2561 := hb (x (-9) 6)
      have b2562 := hb (x (-8) 5)
      have b2563 := hb (x (-7) 4)
      have b2564 := hb (x (-6) 11)
      have b2565 := hb (x (-5) 10)
      have b2566 := hb (x (-4) 9)
      have b2567 := hb (x (-3) 8)
      clear * - r2553 e2554 e2555 e2556 e2557 e2558 e2559 b2560 b2561 b2562 b2563 b2564 b2565 b2566 b2567 d2520 d1807 d2512 d2504 d2536
      omega
    have d2568 : (x (-9) 6).toNat = 0 := by
      have r2569 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2570 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e2571 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e2572 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e2573 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e2574 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e2575 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have b2576 := hb (x (-10) 7)
      have b2577 := hb (x (-9) 6)
      have b2578 := hb (x (-8) 5)
      have b2579 := hb (x (-7) 4)
      have b2580 := hb (x (-6) 11)
      have b2581 := hb (x (-5) 10)
      have b2582 := hb (x (-4) 9)
      have b2583 := hb (x (-3) 8)
      clear * - r2569 e2570 e2571 e2572 e2573 e2574 e2575 b2576 b2577 b2578 b2579 b2580 b2581 b2582 b2583 d2520 d1807 d2512 d2504 d2536 d2552
      omega
    have d2584 : (x (-10) 7).toNat = 0 := by
      have r2585 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2586 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e2587 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e2588 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e2589 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e2590 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e2591 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have b2592 := hb (x (-10) 7)
      have b2593 := hb (x (-9) 6)
      have b2594 := hb (x (-8) 5)
      have b2595 := hb (x (-7) 4)
      have b2596 := hb (x (-6) 11)
      have b2597 := hb (x (-5) 10)
      have b2598 := hb (x (-4) 9)
      have b2599 := hb (x (-3) 8)
      clear * - r2585 e2586 e2587 e2588 e2589 e2590 e2591 b2592 b2593 b2594 b2595 b2596 b2597 b2598 b2599 d2520 d1807 d2512 d2504 d2536 d2552 d2568
      omega
    have d2600 : (x (-10) 1 && x (-10) 7).toNat = 0 := by
      have r2601 := hand2 (x (-10) 1) (x (-10) 7)
      have b2602 := hb (x (-10) 7)
      have b2603 := hb (x (-10) 1 && x (-10) 7)
      clear * - r2601 b2602 b2603 d2584
      omega
    have d2604 : (x (-18) 9).toNat = 1 := by
      have r2605 : 1 ≤ (x (-9) 6).toNat + (x (-10) 1 && x (-10) 7).toNat + (x (-11) 2 && x (-11) 8).toNat + (x (-12) 3 && x (-12) 9).toNat + (x (-13) 4 && x (-13) 10).toNat + (x (-14) 5 && x (-14) 11).toNat + (x (-15) 6 && x (-15) 12).toNat + (x (-16) 7 && x (-16) 13).toNat + (x (-17) 8 && x (-17) 14).toNat + (x (-18) 9).toNat := by have q := hcov6 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b2606 := hb (x (-18) 9)
      have b2607 := hb (x (-9) 6)
      have b2608 := hb (x (-10) 1 && x (-10) 7)
      have b2609 := hb (x (-11) 2 && x (-11) 8)
      have b2610 := hb (x (-12) 3 && x (-12) 9)
      have b2611 := hb (x (-13) 4 && x (-13) 10)
      have b2612 := hb (x (-14) 5 && x (-14) 11)
      have b2613 := hb (x (-15) 6 && x (-15) 12)
      have b2614 := hb (x (-16) 7 && x (-16) 13)
      have b2615 := hb (x (-17) 8 && x (-17) 14)
      clear * - r2605 b2606 b2607 b2608 b2609 b2610 b2611 b2612 b2613 b2614 b2615 d2568 d2600 d2002 d2468 d1950 d1974 d2022 d2046 d2395
      omega
    have d2616 : (x (-17) 8).toNat = 0 := by
      have r2617 : (x (-17) 8).toNat + (x (-18) 1 && x (-18) 9).toNat + (x (-19) 2 && x (-19) 10).toNat + (x (-20) 3 && x (-20) 11).toNat + (x (-21) 4 && x (-21) 12).toNat + (x (-22) 5 && x (-22) 13).toNat + (x (-23) 6 && x (-23) 14).toNat + (x (-24) 7).toNat = 1 := by have q := hd8 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2618 : (x (-18) 1 && x (-18) 9).toNat = (x (-18) 9).toNat := handr _ _ (fun h => hp9 (-18) (h))
      have e2619 : (x (-19) 2 && x (-19) 10).toNat = (x (-19) 10).toNat := handr _ _ (fun h => hp10 (-19) (h))
      have e2620 : (x (-20) 3 && x (-20) 11).toNat = (x (-20) 11).toNat := handr _ _ (fun h => hp11 (-20) (h))
      have e2621 : (x (-21) 4 && x (-21) 12).toNat = (x (-21) 4).toNat := handl _ _ (fun h => hp4 (-21) (h))
      have e2622 : (x (-22) 5 && x (-22) 13).toNat = (x (-22) 5).toNat := handl _ _ (fun h => hp5 (-22) (h))
      have e2623 : (x (-23) 6 && x (-23) 14).toNat = (x (-23) 6).toNat := handl _ _ (fun h => hp6 (-23) (h))
      have b2624 := hb (x (-24) 7)
      have b2625 := hb (x (-23) 6)
      have b2626 := hb (x (-22) 5)
      have b2627 := hb (x (-21) 4)
      have b2628 := hb (x (-20) 11)
      have b2629 := hb (x (-19) 10)
      have b2630 := hb (x (-18) 9)
      have b2631 := hb (x (-17) 8)
      clear * - r2617 e2618 e2619 e2620 e2621 e2622 e2623 b2624 b2625 b2626 b2627 b2628 b2629 b2630 b2631 d2604 d2378
      omega
    have d2632 : (x (-17) 8 && x (-17) 12).toNat = 0 := by
      have r2633 := hand1 (x (-17) 8) (x (-17) 12)
      have b2634 := hb (x (-17) 8)
      have b2635 := hb (x (-17) 8 && x (-17) 12)
      clear * - r2633 b2634 b2635 d2616
      omega
    have d2636 : (x (-20) 11).toNat = 1 := by
      have r2637 : 1 ≤ (x (-9) 4).toNat + (x (-10) 1 && x (-10) 5).toNat + (x (-11) 2 && x (-11) 6).toNat + (x (-12) 3 && x (-12) 7).toNat + (x (-13) 4 && x (-13) 8).toNat + (x (-14) 5 && x (-14) 9).toNat + (x (-15) 6 && x (-15) 10).toNat + (x (-16) 7 && x (-16) 11).toNat + (x (-17) 8 && x (-17) 12).toNat + (x (-18) 9 && x (-18) 13).toNat + (x (-19) 10 && x (-19) 14).toNat + (x (-20) 11).toNat := by have q := hcov4 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e2638 : (x (-10) 1 && x (-10) 5).toNat = (x (-10) 5).toNat := handr _ _ (fun h => hp13 (-10) (hp5 (-10) (h)))
      have e2639 : (x (-19) 10 && x (-19) 14).toNat = (x (-19) 10).toNat := handl _ _ (fun h => hp2 (-19) (hp10 (-19) (h)))
      have b2640 := hb (x (-20) 11)
      have b2641 := hb (x (-19) 10)
      have b2642 := hb (x (-10) 5)
      have b2643 := hb (x (-9) 4)
      have b2644 := hb (x (-11) 2 && x (-11) 6)
      have b2645 := hb (x (-12) 3 && x (-12) 7)
      have b2646 := hb (x (-13) 4 && x (-13) 8)
      have b2647 := hb (x (-14) 5 && x (-14) 9)
      have b2648 := hb (x (-15) 6 && x (-15) 10)
      have b2649 := hb (x (-16) 7 && x (-16) 11)
      have b2650 := hb (x (-17) 8 && x (-17) 12)
      have b2651 := hb (x (-18) 9 && x (-18) 13)
      clear * - r2637 e2638 e2639 b2640 b2641 b2642 b2643 b2644 b2645 b2646 b2647 b2648 b2649 b2650 b2651 d1314 d1334 d1366 d1386 d1954 d1978 d2026 d2050 d2632 d2366 d2378
      omega
    have r2652 : (x (-17) 8).toNat + (x (-18) 1 && x (-18) 9).toNat + (x (-19) 2 && x (-19) 10).toNat + (x (-20) 3 && x (-20) 11).toNat + (x (-21) 4 && x (-21) 12).toNat + (x (-22) 5 && x (-22) 13).toNat + (x (-23) 6 && x (-23) 14).toNat + (x (-24) 7).toNat = 1 := by have q := hd8 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2653 : (x (-18) 1 && x (-18) 9).toNat = (x (-18) 9).toNat := handr _ _ (fun h => hp9 (-18) (h))
    have e2654 : (x (-19) 2 && x (-19) 10).toNat = (x (-19) 10).toNat := handr _ _ (fun h => hp10 (-19) (h))
    have e2655 : (x (-20) 3 && x (-20) 11).toNat = (x (-20) 11).toNat := handr _ _ (fun h => hp11 (-20) (h))
    have e2656 : (x (-21) 4 && x (-21) 12).toNat = (x (-21) 4).toNat := handl _ _ (fun h => hp4 (-21) (h))
    have e2657 : (x (-22) 5 && x (-22) 13).toNat = (x (-22) 5).toNat := handl _ _ (fun h => hp5 (-22) (h))
    have e2658 : (x (-23) 6 && x (-23) 14).toNat = (x (-23) 6).toNat := handl _ _ (fun h => hp6 (-23) (h))
    have b2659 := hb (x (-24) 7)
    have b2660 := hb (x (-23) 6)
    have b2661 := hb (x (-22) 5)
    have b2662 := hb (x (-21) 4)
    have b2663 := hb (x (-20) 11)
    have b2664 := hb (x (-19) 10)
    have b2665 := hb (x (-18) 9)
    have b2666 := hb (x (-17) 8)
    linarith only [r2652, e2653, e2654, e2655, e2656, e2657, e2658, b2659, b2660, b2661, b2662, b2663, b2664, b2665, b2666, d2616, d2604, d2378, d2636]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b0000000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 0 3).toNat = 0)
    (g2 : (x 0 5).toNat = 0)
    (g3 : (x 0 6).toNat = 0)
    (g4 : (x 0 9).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 1 1).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 2 5).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 5 10).toNat = 0)
    (g12 : (x 6 9).toNat = 0)
    (g13 : (x 1 2 && x 1 6).toNat = 0)
    (g14 : (x 0 3 && x 0 7).toNat = 0)
    (g15 : (x 0 9 && x 0 13).toNat = 0)
    (g16 : (x 0 1 && x 0 7).toNat = 0)
    (g17 : (x 7 2 && x 7 8).toNat = 0)
    (g18 : (x 6 3 && x 6 9).toNat = 0)
    (g19 : (x 5 4 && x 5 10).toNat = 0)
    (g20 : (x 4 5 && x 4 11).toNat = 0)
    (g21 : (x 0 1 && x 0 10).toNat = 0)
    (g22 : (x 0 2 && x 0 11).toNat = 0)
    (g23 : (x 5 1 && x 5 10).toNat = 0)
    (g24 : (x 4 2 && x 4 11).toNat = 0)
    (g25 : (x 0 3 && x 0 13).toNat = 0)
    (g26 : (x 4 1 && x 4 11).toNat = 0)
    (g27 : (x 3 4 && x 3 14).toNat = 0)
    (g28 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b0000000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28
