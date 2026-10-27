import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00000

Topic: combinatorics   Node: 53f992550361

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core: under the layer-free tight-cover constraints for k = 15 and 5 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 2).toNat = 0)
    (g1 : (x 0 14).toNat = 0)
    (g2 : (x 1 2).toNat = 0)
    (g3 : (x 3 2).toNat = 0)
    (g4 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d448 : (x 0 1 && x 0 14).toNat = 0 := by
    have r449 := hand2 (x 0 1) (x 0 14)
    have b450 := hb (x 0 14)
    have b451 := hb (x 0 1 && x 0 14)
    clear * - r449 b450 b451 g1
    omega
  have d452 : (x 1 13).toNat = 1 := by
    have r453 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b454 := hb (x (-1) 2)
    have b455 := hb (x 1 13)
    have b456 := hb (x 0 1 && x 0 14)
    clear * - r453 b454 b455 b456 d448 g0
    omega
  have d457 : (x 1 1).toNat = 1 := by
    have r458 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b459 := hb (x 1 1)
    have b460 := hb (x 1 13)
    clear * - r458 b459 b460 d452
    omega
  have d461 : (x 2 14).toNat = 0 := by
    have r462 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b463 := hb (x 1 1)
    have b464 := hb (x 2 14)
    clear * - r462 b463 b464 d457
    omega
  have d465 : (x 2 1 && x 2 14).toNat = 0 := by
    have r466 := hand2 (x 2 1) (x 2 14)
    have b467 := hb (x 2 14)
    have b468 := hb (x 2 1 && x 2 14)
    clear * - r466 b467 b468 d461
    omega
  have d469 : (x 3 13).toNat = 1 := by
    have r470 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b471 := hb (x 1 2)
    have b472 := hb (x 3 13)
    have b473 := hb (x 2 1 && x 2 14)
    clear * - r470 b471 b472 b473 d465 g2
    omega
  have d474 : (x 3 1).toNat = 1 := by
    have r475 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b476 := hb (x 3 1)
    have b477 := hb (x 3 13)
    clear * - r475 b476 b477 d469
    omega
  have d478 : (x 4 14).toNat = 0 := by
    have r479 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b480 := hb (x 3 1)
    have b481 := hb (x 4 14)
    clear * - r479 b480 b481 d474
    omega
  have d482 : (x 4 1 && x 4 14).toNat = 0 := by
    have r483 := hand2 (x 4 1) (x 4 14)
    have b484 := hb (x 4 14)
    have b485 := hb (x 4 1 && x 4 14)
    clear * - r483 b484 b485 d478
    omega
  have d486 : (x 5 13).toNat = 1 := by
    have r487 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b488 := hb (x 3 2)
    have b489 := hb (x 5 13)
    have b490 := hb (x 4 1 && x 4 14)
    clear * - r487 b488 b489 b490 d482 g3
    omega
  have d491 : (x 5 1).toNat = 1 := by
    have r492 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b493 := hb (x 5 1)
    have b494 := hb (x 5 13)
    clear * - r492 b493 b494 d486
    omega
  have d495 : (x 6 14).toNat = 0 := by
    have r496 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b497 := hb (x 5 1)
    have b498 := hb (x 6 14)
    clear * - r496 b497 b498 d491
    omega
  have d499 : (x 6 1 && x 6 14).toNat = 0 := by
    have r500 := hand2 (x 6 1) (x 6 14)
    have b501 := hb (x 6 14)
    have b502 := hb (x 6 1 && x 6 14)
    clear * - r500 b501 b502 d495
    omega
  have d503 : (x 6 2).toNat = 0 := by
    have r504 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b505 := hb (x 6 2)
    have b506 := hb (x 6 14)
    clear * - r504 b505 b506 d495
    omega
  have d507 : (x 4 2).toNat = 0 := by
    have r508 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b509 := hb (x 4 2)
    have b510 := hb (x 4 14)
    clear * - r508 b509 b510 d478
    omega
  have d511 : (x 2 2).toNat = 0 := by
    have r512 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b513 := hb (x 2 2)
    have b514 := hb (x 2 14)
    clear * - r512 b513 b514 d461
    omega
  have d515 : (x 4 13).toNat = 1 := by
    have r516 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b517 := hb (x 2 2)
    have b518 := hb (x 4 13)
    have b519 := hb (x 3 1 && x 3 14)
    clear * - r516 b517 b518 b519 g4 d511
    omega
  have d520 : (x 4 1).toNat = 1 := by
    have r521 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b522 := hb (x 4 1)
    have b523 := hb (x 4 13)
    clear * - r521 b522 b523 d515
    omega
  have d524 : (x 5 14).toNat = 0 := by
    have r525 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b526 := hb (x 4 1)
    have b527 := hb (x 5 14)
    clear * - r525 b526 b527 d520
    omega
  have d528 : (x 5 1 && x 5 14).toNat = 0 := by
    have r529 := hand2 (x 5 1) (x 5 14)
    have b530 := hb (x 5 14)
    have b531 := hb (x 5 1 && x 5 14)
    clear * - r529 b530 b531 d524
    omega
  have d532 : (x 6 13).toNat = 1 := by
    have r533 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b534 := hb (x 4 2)
    have b535 := hb (x 6 13)
    have b536 := hb (x 5 1 && x 5 14)
    clear * - r533 b534 b535 b536 d528 d507
    omega
  have d537 : (x 6 1).toNat = 1 := by
    have r538 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b539 := hb (x 6 1)
    have b540 := hb (x 6 13)
    clear * - r538 b539 b540 d532
    omega
  have d541 : (x 7 14).toNat = 0 := by
    have r542 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b543 := hb (x 6 1)
    have b544 := hb (x 7 14)
    clear * - r542 b543 b544 d537
    omega
  have d545 : (x 7 1 && x 7 14).toNat = 0 := by
    have r546 := hand2 (x 7 1) (x 7 14)
    have b547 := hb (x 7 14)
    have b548 := hb (x 7 1 && x 7 14)
    clear * - r546 b547 b548 d541
    omega
  have d549 : (x 8 13).toNat = 1 := by
    have r550 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b551 := hb (x 6 2)
    have b552 := hb (x 8 13)
    have b553 := hb (x 7 1 && x 7 14)
    clear * - r550 b551 b552 b553 d545 d503
    omega
  have d554 : (x 8 1).toNat = 1 := by
    have r555 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b556 := hb (x 8 1)
    have b557 := hb (x 8 13)
    clear * - r555 b556 b557 d549
    omega
  have d558 : (x 9 14).toNat = 0 := by
    have r559 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b560 := hb (x 8 1)
    have b561 := hb (x 9 14)
    clear * - r559 b560 b561 d554
    omega
  have d562 : (x 9 1 && x 9 14).toNat = 0 := by
    have r563 := hand2 (x 9 1) (x 9 14)
    have b564 := hb (x 9 14)
    have b565 := hb (x 9 1 && x 9 14)
    clear * - r563 b564 b565 d558
    omega
  have d566 : (x 9 2).toNat = 0 := by
    have r567 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b568 := hb (x 9 2)
    have b569 := hb (x 9 14)
    clear * - r567 b568 b569 d558
    omega
  have d570 : (x 7 2).toNat = 0 := by
    have r571 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b572 := hb (x 7 2)
    have b573 := hb (x 7 14)
    clear * - r571 b572 b573 d541
    omega
  have d574 : (x 5 2).toNat = 0 := by
    have r575 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b576 := hb (x 5 2)
    have b577 := hb (x 5 14)
    clear * - r575 b576 b577 d524
    omega
  have d578 : (x 7 13).toNat = 1 := by
    have r579 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b580 := hb (x 5 2)
    have b581 := hb (x 7 13)
    have b582 := hb (x 6 1 && x 6 14)
    clear * - r579 b580 b581 b582 d499 d574
    omega
  have d583 : (x 7 1).toNat = 1 := by
    have r584 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b585 := hb (x 7 1)
    have b586 := hb (x 7 13)
    clear * - r584 b585 b586 d578
    omega
  have d587 : (x 8 14).toNat = 0 := by
    have r588 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b589 := hb (x 7 1)
    have b590 := hb (x 8 14)
    clear * - r588 b589 b590 d583
    omega
  have d591 : (x 8 1 && x 8 14).toNat = 0 := by
    have r592 := hand2 (x 8 1) (x 8 14)
    have b593 := hb (x 8 14)
    have b594 := hb (x 8 1 && x 8 14)
    clear * - r592 b593 b594 d587
    omega
  have d595 : (x 9 13).toNat = 1 := by
    have r596 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b597 := hb (x 7 2)
    have b598 := hb (x 9 13)
    have b599 := hb (x 8 1 && x 8 14)
    clear * - r596 b597 b598 b599 d591 d570
    omega
  have d600 : (x 9 1).toNat = 1 := by
    have r601 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b602 := hb (x 9 1)
    have b603 := hb (x 9 13)
    clear * - r601 b602 b603 d595
    omega
  have d604 : (x 10 14).toNat = 0 := by
    have r605 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b606 := hb (x 9 1)
    have b607 := hb (x 10 14)
    clear * - r605 b606 b607 d600
    omega
  have d608 : (x 10 1 && x 10 14).toNat = 0 := by
    have r609 := hand2 (x 10 1) (x 10 14)
    have b610 := hb (x 10 14)
    have b611 := hb (x 10 1 && x 10 14)
    clear * - r609 b610 b611 d604
    omega
  have d612 : (x 11 13).toNat = 1 := by
    have r613 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b614 := hb (x 9 2)
    have b615 := hb (x 11 13)
    have b616 := hb (x 10 1 && x 10 14)
    clear * - r613 b614 b615 b616 d608 d566
    omega
  have d617 : (x 11 1).toNat = 1 := by
    have r618 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b619 := hb (x 11 1)
    have b620 := hb (x 11 13)
    clear * - r618 b619 b620 d612
    omega
  have d621 : (x 12 14).toNat = 0 := by
    have r622 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b623 := hb (x 11 1)
    have b624 := hb (x 12 14)
    clear * - r622 b623 b624 d617
    omega
  have d625 : (x 12 1 && x 12 14).toNat = 0 := by
    have r626 := hand2 (x 12 1) (x 12 14)
    have b627 := hb (x 12 14)
    have b628 := hb (x 12 1 && x 12 14)
    clear * - r626 b627 b628 d621
    omega
  have d629 : (x 12 2).toNat = 0 := by
    have r630 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
    have b631 := hb (x 12 2)
    have b632 := hb (x 12 14)
    clear * - r630 b631 b632 d621
    omega
  have d633 : (x 10 2).toNat = 0 := by
    have r634 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
    have b635 := hb (x 10 2)
    have b636 := hb (x 10 14)
    clear * - r634 b635 b636 d604
    omega
  have d637 : (x 8 2).toNat = 0 := by
    have r638 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b639 := hb (x 8 2)
    have b640 := hb (x 8 14)
    clear * - r638 b639 b640 d587
    omega
  have d641 : (x 10 13).toNat = 1 := by
    have r642 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b643 := hb (x 8 2)
    have b644 := hb (x 10 13)
    have b645 := hb (x 9 1 && x 9 14)
    clear * - r642 b643 b644 b645 d562 d637
    omega
  have d646 : (x 10 1).toNat = 1 := by
    have r647 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b648 := hb (x 10 1)
    have b649 := hb (x 10 13)
    clear * - r647 b648 b649 d641
    omega
  have d650 : (x 11 14).toNat = 0 := by
    have r651 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b652 := hb (x 10 1)
    have b653 := hb (x 11 14)
    clear * - r651 b652 b653 d646
    omega
  have d654 : (x 11 1 && x 11 14).toNat = 0 := by
    have r655 := hand2 (x 11 1) (x 11 14)
    have b656 := hb (x 11 14)
    have b657 := hb (x 11 1 && x 11 14)
    clear * - r655 b656 b657 d650
    omega
  have d658 : (x 12 13).toNat = 1 := by
    have r659 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b660 := hb (x 10 2)
    have b661 := hb (x 12 13)
    have b662 := hb (x 11 1 && x 11 14)
    clear * - r659 b660 b661 b662 d654 d633
    omega
  have d663 : (x 12 1).toNat = 1 := by
    have r664 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b665 := hb (x 12 1)
    have b666 := hb (x 12 13)
    clear * - r664 b665 b666 d658
    omega
  have d667 : (x 13 14).toNat = 0 := by
    have r668 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b669 := hb (x 12 1)
    have b670 := hb (x 13 14)
    clear * - r668 b669 b670 d663
    omega
  have d671 : (x 13 1 && x 13 14).toNat = 0 := by
    have r672 := hand2 (x 13 1) (x 13 14)
    have b673 := hb (x 13 14)
    have b674 := hb (x 13 1 && x 13 14)
    clear * - r672 b673 b674 d667
    omega
  have d675 : (x 14 13).toNat = 1 := by
    have r676 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b677 := hb (x 12 2)
    have b678 := hb (x 14 13)
    have b679 := hb (x 13 1 && x 13 14)
    clear * - r676 b677 b678 b679 d671 d629
    omega
  have d680 : (x 14 1).toNat = 1 := by
    have r681 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b682 := hb (x 14 1)
    have b683 := hb (x 14 13)
    clear * - r681 b682 b683 d675
    omega
  have d684 : (x 15 14).toNat = 0 := by
    have r685 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b686 := hb (x 14 1)
    have b687 := hb (x 15 14)
    clear * - r685 b686 b687 d680
    omega
  have d688 : (x 15 1 && x 15 14).toNat = 0 := by
    have r689 := hand2 (x 15 1) (x 15 14)
    have b690 := hb (x 15 14)
    have b691 := hb (x 15 1 && x 15 14)
    clear * - r689 b690 b691 d684
    omega
  have d692 : (x 15 2).toNat = 0 := by
    have r693 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b694 := hb (x 15 2)
    have b695 := hb (x 15 14)
    clear * - r693 b694 b695 d684
    omega
  have d696 : (x 15 2 && x 15 13).toNat = 0 := by
    have r697 := hand1 (x 15 2) (x 15 13)
    have b698 := hb (x 15 2)
    have b699 := hb (x 15 2 && x 15 13)
    clear * - r697 b698 b699 d692
    omega
  have d700 : (x 13 2).toNat = 0 := by
    have r701 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
    have b702 := hb (x 13 2)
    have b703 := hb (x 13 14)
    clear * - r701 b702 b703 d667
    omega
  have d704 : (x 11 2).toNat = 0 := by
    have r705 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b706 := hb (x 11 2)
    have b707 := hb (x 11 14)
    clear * - r705 b706 b707 d650
    omega
  have d708 : (x 13 13).toNat = 1 := by
    have r709 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b710 := hb (x 11 2)
    have b711 := hb (x 13 13)
    have b712 := hb (x 12 1 && x 12 14)
    clear * - r709 b710 b711 b712 d625 d704
    omega
  have d713 : (x 13 1).toNat = 1 := by
    have r714 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
    have b715 := hb (x 13 1)
    have b716 := hb (x 13 13)
    clear * - r714 b715 b716 d708
    omega
  have d717 : (x 14 14).toNat = 0 := by
    have r718 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b719 := hb (x 13 1)
    have b720 := hb (x 14 14)
    clear * - r718 b719 b720 d713
    omega
  have d721 : (x 14 1 && x 14 14).toNat = 0 := by
    have r722 := hand2 (x 14 1) (x 14 14)
    have b723 := hb (x 14 14)
    have b724 := hb (x 14 1 && x 14 14)
    clear * - r722 b723 b724 d717
    omega
  have d725 : (x 15 13).toNat = 1 := by
    have r726 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b727 := hb (x 13 2)
    have b728 := hb (x 15 13)
    have b729 := hb (x 14 1 && x 14 14)
    clear * - r726 b727 b728 b729 d721 d700
    omega
  have d730 : (x 15 1).toNat = 1 := by
    have r731 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have b732 := hb (x 15 1)
    have b733 := hb (x 15 13)
    clear * - r731 b732 b733 d725
    omega
  have d734 : (x 16 14).toNat = 0 := by
    have r735 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b736 := hb (x 15 1)
    have b737 := hb (x 16 14)
    clear * - r735 b736 b737 d730
    omega
  have d738 : (x 16 1 && x 16 14).toNat = 0 := by
    have r739 := hand2 (x 16 1) (x 16 14)
    have b740 := hb (x 16 14)
    have b741 := hb (x 16 1 && x 16 14)
    clear * - r739 b740 b741 d734
    omega
  have d742 : (x 17 13).toNat = 1 := by
    have r743 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b744 := hb (x 15 2)
    have b745 := hb (x 17 13)
    have b746 := hb (x 16 1 && x 16 14)
    clear * - r743 b744 b745 b746 d738 d692
    omega
  have d747 : (x 17 1).toNat = 1 := by
    have r748 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
    have b749 := hb (x 17 1)
    have b750 := hb (x 17 13)
    clear * - r748 b749 b750 d742
    omega
  have d751 : (x 18 14).toNat = 0 := by
    have r752 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b753 := hb (x 17 1)
    have b754 := hb (x 18 14)
    clear * - r752 b753 b754 d747
    omega
  have d755 : (x 18 1 && x 18 14).toNat = 0 := by
    have r756 := hand2 (x 18 1) (x 18 14)
    have b757 := hb (x 18 14)
    have b758 := hb (x 18 1 && x 18 14)
    clear * - r756 b757 b758 d751
    omega
  have d759 : (x 18 2).toNat = 0 := by
    have r760 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
    have b761 := hb (x 18 2)
    have b762 := hb (x 18 14)
    clear * - r760 b761 b762 d751
    omega
  have d763 : (x 14 3 && x 14 14).toNat = 0 := by
    have r764 := hand2 (x 14 3) (x 14 14)
    have b765 := hb (x 14 14)
    have b766 := hb (x 14 3 && x 14 14)
    clear * - r764 b765 b766 d717
    omega
  have d767 : (x 14 2).toNat = 0 := by
    have r768 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
    have b769 := hb (x 14 2)
    have b770 := hb (x 14 14)
    clear * - r768 b769 b770 d717
    omega
  have d771 : (x 16 13).toNat = 1 := by
    have r772 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b773 := hb (x 14 2)
    have b774 := hb (x 16 13)
    have b775 := hb (x 15 1 && x 15 14)
    clear * - r772 b773 b774 b775 d688 d767
    omega
  have d776 : (x 16 1).toNat = 1 := by
    have r777 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
    have b778 := hb (x 16 1)
    have b779 := hb (x 16 13)
    clear * - r777 b778 b779 d771
    omega
  have d780 : (x 17 14).toNat = 0 := by
    have r781 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b782 := hb (x 16 1)
    have b783 := hb (x 17 14)
    clear * - r781 b782 b783 d776
    omega
  have d784 : (x 17 2).toNat = 0 := by
    have r785 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
    have b786 := hb (x 17 2)
    have b787 := hb (x 17 14)
    clear * - r785 b786 b787 d780
    omega
  have d788 : (x 19 13).toNat = 1 := by
    have r789 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b790 := hb (x 17 2)
    have b791 := hb (x 19 13)
    have b792 := hb (x 18 1 && x 18 14)
    clear * - r789 b790 b791 b792 d755 d784
    omega
  have d793 : (x 20 12).toNat = 0 := by
    have r794 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e795 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e796 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b797 := hb (x 17 3)
    have b798 := hb (x 18 2)
    have b799 := hb (x 19 13)
    have b800 := hb (x 20 12)
    clear * - r794 e795 e796 b797 b798 b799 b800 d788 d759
    omega
  have d801 : (x 17 3).toNat = 0 := by
    have r802 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e803 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e804 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b805 := hb (x 17 3)
    have b806 := hb (x 18 2)
    have b807 := hb (x 19 13)
    have b808 := hb (x 20 12)
    clear * - r802 e803 e804 b805 b806 b807 b808 d793 d788 d759
    omega
  have d809 : (x 17 11).toNat = 0 := by
    have r810 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b811 := hb (x 17 3)
    have b812 := hb (x 17 11)
    clear * - r810 b811 b812 d801
    omega
  have d813 : (x 16 12).toNat = 0 := by
    have r814 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e815 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e816 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b817 := hb (x 13 3)
    have b818 := hb (x 14 2)
    have b819 := hb (x 15 13)
    have b820 := hb (x 16 12)
    clear * - r814 e815 e816 b817 b818 b819 b820 d725 d767
    omega
  have d821 : (x 16 1 && x 16 12).toNat = 0 := by
    have r822 := hand2 (x 16 1) (x 16 12)
    have b823 := hb (x 16 12)
    have b824 := hb (x 16 1 && x 16 12)
    clear * - r822 b823 b824 d813
    omega
  have d825 : (x 13 12).toNat = 0 := by
    have r826 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e827 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e828 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b829 := hb (x 10 3)
    have b830 := hb (x 11 2)
    have b831 := hb (x 12 13)
    have b832 := hb (x 13 12)
    clear * - r826 e827 e828 b829 b830 b831 b832 d658 d704
    omega
  have d833 : (x 13 4).toNat = 0 := by
    have r834 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b835 := hb (x 13 4)
    have b836 := hb (x 13 12)
    clear * - r834 b835 b836 d825
    omega
  have r837 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b838 := hb (x 13 4)
  have b839 := hb (x 17 11)
  have b840 := hb (x 16 1 && x 16 12)
  have b841 := hb (x 15 2 && x 15 13)
  have b842 := hb (x 14 3 && x 14 14)
  linarith only [r837, b838, b839, b840, b841, b842, d809, d821, d696, d763, d833]

theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 2).toNat = 0)
    (g1 : (x 0 14).toNat = 0)
    (g2 : (x 1 2).toNat = 0)
    (g3 : (x 3 2).toNat = 0)
    (g4 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4
