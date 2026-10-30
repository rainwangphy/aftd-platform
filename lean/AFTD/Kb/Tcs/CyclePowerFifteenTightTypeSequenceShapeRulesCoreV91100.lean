import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_shape_rules_core_v91_100

Topic: combinatorics   Node: 8f3f09dbf8d3

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

Window refutation for k = 15: in the layer-free tight-class model on the integer line (x p j: the class starting at p contains p + j; inner count 3 per vertex, distances 14, 12, 8 covered exactly once, the other distances covered, classes closed under the tight-class parent map), with x p 1 = x p 14 and x p 2 = x p 3 everywhere, the class at 0 cannot have bit 9 = 1 and bit 10 = 0.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v91_100_aux (x : ℤ → Fin 16 → Bool)
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
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 9).toNat = 1) (g1 : (x 0 10).toNat = 0) : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8445 : (x 0 1 && x 0 10).toNat = 0 := by
    have r8446 := hand2 (x 0 1) (x 0 10)
    have b8447 := hb (x 0 10)
    have b8448 := hb (x 0 1 && x 0 10)
    clear * - r8446 b8447 b8448 g1
    omega
  have d8449 : (x 0 3 && x 0 10).toNat = 0 := by
    have r8450 := hand2 (x 0 3) (x 0 10)
    have b8451 := hb (x 0 10)
    have b8452 := hb (x 0 3 && x 0 10)
    clear * - r8450 b8451 b8452 g1
    omega
  have d8453 : (x 0 6 && x 0 10).toNat = 0 := by
    have r8454 := hand2 (x 0 6) (x 0 10)
    have b8455 := hb (x 0 10)
    have b8456 := hb (x 0 6 && x 0 10)
    clear * - r8454 b8455 b8456 g1
    omega
  have d8457 : (x 0 9 && x 0 10).toNat = 0 := by
    have r8458 := hand2 (x 0 9) (x 0 10)
    have b8459 := hb (x 0 10)
    have b8460 := hb (x 0 9 && x 0 10)
    clear * - r8458 b8459 b8460 g1
    omega
  have d8461 : (x 0 1).toNat = 1 := by
    have r8462 : (x 0 9).toNat ≤ (x 0 1).toNat := himp _ _ (hp9 0)
    have b8463 := hb (x 0 1)
    have b8464 := hb (x 0 9)
    clear * - r8462 b8463 b8464 g0
    omega
  have d8465 : (x 0 14).toNat = 1 := by
    have r8466 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
    have b8467 := hb (x 0 1)
    have b8468 := hb (x 0 14)
    clear * - r8466 b8467 b8468 d8461
    omega
  have d8469 : (x 1 14).toNat = 0 := by
    have r8470 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8471 := hb (x 0 1)
    have b8472 := hb (x 1 14)
    clear * - r8470 b8471 b8472 d8461
    omega
  have d8473 : (x 1 1).toNat = 0 := by
    have r8474 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
    have b8475 := hb (x 1 1)
    have b8476 := hb (x 1 14)
    clear * - r8474 b8475 b8476 d8469
    omega
  have d8477 : (x 1 13).toNat = 0 := by
    have r8478 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b8479 := hb (x 1 1)
    have b8480 := hb (x 1 13)
    clear * - r8478 b8479 b8480 d8473
    omega
  have d8481 : (x 1 4 && x 1 13).toNat = 0 := by
    have r8482 := hand2 (x 1 4) (x 1 13)
    have b8483 := hb (x 1 13)
    have b8484 := hb (x 1 4 && x 1 13)
    clear * - r8482 b8483 b8484 d8477
    omega
  have d8485 : (x 1 5).toNat = 0 := by
    have r8486 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b8487 := hb (x 1 5)
    have b8488 := hb (x 1 13)
    clear * - r8486 b8487 b8488 d8477
    omega
  have d8489 : (x 1 5 && x 1 9).toNat = 0 := by
    have r8490 := hand1 (x 1 5) (x 1 9)
    have b8491 := hb (x 1 5)
    have b8492 := hb (x 1 5 && x 1 9)
    clear * - r8490 b8491 b8492 d8485
    omega
  have d8493 : (x 1 9).toNat = 0 := by
    have r8494 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b8495 := hb (x 1 1)
    have b8496 := hb (x 1 9)
    clear * - r8494 b8495 b8496 d8473
    omega
  have d8497 : (x 1 2 && x 1 9).toNat = 0 := by
    have r8498 := hand2 (x 1 2) (x 1 9)
    have b8499 := hb (x 1 9)
    have b8500 := hb (x 1 2 && x 1 9)
    clear * - r8498 b8499 b8500 d8493
    omega
  have d8501 : (x 1 8 && x 1 9).toNat = 0 := by
    have r8502 := hand2 (x 1 8) (x 1 9)
    have b8503 := hb (x 1 9)
    have b8504 := hb (x 1 8 && x 1 9)
    clear * - r8502 b8503 b8504 d8493
    omega
  have d8505 : (x 2 14).toNat = 1 := by
    have r8506 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8507 := hb (x 1 1)
    have b8508 := hb (x 2 14)
    clear * - r8506 b8507 b8508 d8473
    omega
  have d8509 : (x 2 1).toNat = 1 := by
    have r8510 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
    have b8511 := hb (x 2 1)
    have b8512 := hb (x 2 14)
    clear * - r8510 b8511 b8512 d8505
    omega
  have d8513 : (x 3 14).toNat = 0 := by
    have r8514 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8515 := hb (x 2 1)
    have b8516 := hb (x 3 14)
    clear * - r8514 b8515 b8516 d8509
    omega
  have d8517 : (x 3 1).toNat = 0 := by
    have r8518 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
    have b8519 := hb (x 3 1)
    have b8520 := hb (x 3 14)
    clear * - r8518 b8519 b8520 d8513
    omega
  have d8521 : (x 4 14).toNat = 1 := by
    have r8522 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8523 := hb (x 3 1)
    have b8524 := hb (x 4 14)
    clear * - r8522 b8523 b8524 d8517
    omega
  have d8525 : (x 4 1).toNat = 1 := by
    have r8526 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
    have b8527 := hb (x 4 1)
    have b8528 := hb (x 4 14)
    clear * - r8526 b8527 b8528 d8521
    omega
  have d8529 : (x 5 14).toNat = 0 := by
    have r8530 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8531 := hb (x 4 1)
    have b8532 := hb (x 5 14)
    clear * - r8530 b8531 b8532 d8525
    omega
  have d8533 : (x 5 1).toNat = 0 := by
    have r8534 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
    have b8535 := hb (x 5 1)
    have b8536 := hb (x 5 14)
    clear * - r8534 b8535 b8536 d8529
    omega
  have d8537 : (x 5 13).toNat = 0 := by
    have r8538 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b8539 := hb (x 5 1)
    have b8540 := hb (x 5 13)
    clear * - r8538 b8539 b8540 d8533
    omega
  have d8541 : (x 5 4 && x 5 13).toNat = 0 := by
    have r8542 := hand2 (x 5 4) (x 5 13)
    have b8543 := hb (x 5 13)
    have b8544 := hb (x 5 4 && x 5 13)
    clear * - r8542 b8543 b8544 d8537
    omega
  have d8545 : (x 5 5).toNat = 0 := by
    have r8546 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b8547 := hb (x 5 5)
    have b8548 := hb (x 5 13)
    clear * - r8546 b8547 b8548 d8537
    omega
  have d8549 : (x 5 4 && x 5 5).toNat = 0 := by
    have r8550 := hand2 (x 5 4) (x 5 5)
    have b8551 := hb (x 5 5)
    have b8552 := hb (x 5 4 && x 5 5)
    clear * - r8550 b8551 b8552 d8545
    omega
  have d8553 : (x 5 9).toNat = 0 := by
    have r8554 : (x 5 9).toNat ≤ (x 5 1).toNat := himp _ _ (hp9 5)
    have b8555 := hb (x 5 1)
    have b8556 := hb (x 5 9)
    clear * - r8554 b8555 b8556 d8533
    omega
  have d8557 : (x 6 14).toNat = 1 := by
    have r8558 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8559 := hb (x 5 1)
    have b8560 := hb (x 6 14)
    clear * - r8558 b8559 b8560 d8533
    omega
  have d8561 : (x 6 1).toNat = 1 := by
    have r8562 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
    have b8563 := hb (x 6 1)
    have b8564 := hb (x 6 14)
    clear * - r8562 b8563 b8564 d8557
    omega
  have d8565 : (x 7 14).toNat = 0 := by
    have r8566 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8567 := hb (x 6 1)
    have b8568 := hb (x 7 14)
    clear * - r8566 b8567 b8568 d8561
    omega
  have d8569 : (x 7 1).toNat = 0 := by
    have r8570 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
    have b8571 := hb (x 7 1)
    have b8572 := hb (x 7 14)
    clear * - r8570 b8571 b8572 d8565
    omega
  have d8573 : (x 8 14).toNat = 1 := by
    have r8574 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8575 := hb (x 7 1)
    have b8576 := hb (x 8 14)
    clear * - r8574 b8575 b8576 d8569
    omega
  have d8577 : (x 8 1).toNat = 1 := by
    have r8578 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
    have b8579 := hb (x 8 1)
    have b8580 := hb (x 8 14)
    clear * - r8578 b8579 b8580 d8573
    omega
  have d8581 : (x 9 14).toNat = 0 := by
    have r8582 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8583 := hb (x 8 1)
    have b8584 := hb (x 9 14)
    clear * - r8582 b8583 b8584 d8577
    omega
  have d8585 : (x 9 1).toNat = 0 := by
    have r8586 : (x 9 1).toNat = (x 9 14).toNat := congrArg Bool.toNat (h114 9)
    have b8587 := hb (x 9 1)
    have b8588 := hb (x 9 14)
    clear * - r8586 b8587 b8588 d8581
    omega
  have d8589 : (x 9 9).toNat = 0 := by
    have r8590 : (x 9 9).toNat ≤ (x 9 1).toNat := himp _ _ (hp9 9)
    have b8591 := hb (x 9 1)
    have b8592 := hb (x 9 9)
    clear * - r8590 b8591 b8592 d8585
    omega
  have d8593 : (x 7 2).toNat = 0 := by
    have r8594 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b8595 := hb (x 7 2)
    have b8596 := hb (x 7 14)
    clear * - r8594 b8595 b8596 d8565
    omega
  have d8597 : (x 7 2 && x 7 11).toNat = 0 := by
    have r8598 := hand1 (x 7 2) (x 7 11)
    have b8599 := hb (x 7 2)
    have b8600 := hb (x 7 2 && x 7 11)
    clear * - r8598 b8599 b8600 d8593
    omega
  have d8601 : (x 7 2 && x 7 3).toNat = 0 := by
    have r8602 := hand1 (x 7 2) (x 7 3)
    have b8603 := hb (x 7 2)
    have b8604 := hb (x 7 2 && x 7 3)
    clear * - r8602 b8603 b8604 d8593
    omega
  have d8605 : (x 7 3).toNat = 0 := by
    have r8606 : (x 7 2).toNat = (x 7 3).toNat := congrArg Bool.toNat (h23 7)
    have b8607 := hb (x 7 2)
    have b8608 := hb (x 7 3)
    clear * - r8606 b8607 b8608 d8593
    omega
  have d8609 : (x 3 6).toNat = 0 := by
    have r8610 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b8611 := hb (x 3 6)
    have b8612 := hb (x 3 14)
    clear * - r8610 b8611 b8612 d8513
    omega
  have d8613 : (x 3 6 && x 3 7).toNat = 0 := by
    have r8614 := hand1 (x 3 6) (x 3 7)
    have b8615 := hb (x 3 6)
    have b8616 := hb (x 3 6 && x 3 7)
    clear * - r8614 b8615 b8616 d8609
    omega
  have d8617 : (x 3 2).toNat = 0 := by
    have r8618 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b8619 := hb (x 3 2)
    have b8620 := hb (x 3 14)
    clear * - r8618 b8619 b8620 d8513
    omega
  have d8621 : (x 3 2 && x 3 11).toNat = 0 := by
    have r8622 := hand1 (x 3 2) (x 3 11)
    have b8623 := hb (x 3 2)
    have b8624 := hb (x 3 2 && x 3 11)
    clear * - r8622 b8623 b8624 d8617
    omega
  have d8625 : (x 3 3).toNat = 0 := by
    have r8626 : (x 3 2).toNat = (x 3 3).toNat := congrArg Bool.toNat (h23 3)
    have b8627 := hb (x 3 2)
    have b8628 := hb (x 3 3)
    clear * - r8626 b8627 b8628 d8617
    omega
  have d8629 : (x 3 3 && x 3 7).toNat = 0 := by
    have r8630 := hand1 (x 3 3) (x 3 7)
    have b8631 := hb (x 3 3)
    have b8632 := hb (x 3 3 && x 3 7)
    clear * - r8630 b8631 b8632 d8625
    omega
  have d8633 : (x 3 11).toNat = 0 := by
    have r8634 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b8635 := hb (x 3 3)
    have b8636 := hb (x 3 11)
    clear * - r8634 b8635 b8636 d8625
    omega
  have d8637 : (x 1 2).toNat = 0 := by
    have r8638 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b8639 := hb (x 1 2)
    have b8640 := hb (x 1 14)
    clear * - r8638 b8639 b8640 d8469
    omega
  have d8641 : (x 1 2 && x 1 8).toNat = 0 := by
    have r8642 := hand1 (x 1 2) (x 1 8)
    have b8643 := hb (x 1 2)
    have b8644 := hb (x 1 2 && x 1 8)
    clear * - r8642 b8643 b8644 d8637
    omega
  have d8645 : (x (-1) 1).toNat = 0 := by
    have r8646 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8647 := hb (x (-1) 1)
    have b8648 := hb (x 0 14)
    clear * - r8646 b8647 b8648 d8465
    omega
  have d8649 : (x (-1) 14).toNat = 0 := by
    have r8650 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
    have b8651 := hb (x (-1) 1)
    have b8652 := hb (x (-1) 14)
    clear * - r8650 b8651 b8652 d8645
    omega
  have d8653 : (x (-1) 6).toNat = 0 := by
    have r8654 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b8655 := hb (x (-1) 6)
    have b8656 := hb (x (-1) 14)
    clear * - r8654 b8655 b8656 d8649
    omega
  have d8657 : (x (-1) 2 && x (-1) 6).toNat = 0 := by
    have r8658 := hand2 (x (-1) 2) (x (-1) 6)
    have b8659 := hb (x (-1) 6)
    have b8660 := hb (x (-1) 2 && x (-1) 6)
    clear * - r8658 b8659 b8660 d8653
    omega
  have d8661 : (x (-1) 2).toNat = 0 := by
    have r8662 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b8663 := hb (x (-1) 2)
    have b8664 := hb (x (-1) 14)
    clear * - r8662 b8663 b8664 d8649
    omega
  have d8665 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
    have r8666 := hand1 (x (-1) 2) (x (-1) 11)
    have b8667 := hb (x (-1) 2)
    have b8668 := hb (x (-1) 2 && x (-1) 11)
    clear * - r8666 b8667 b8668 d8661
    omega
  have d8669 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
    have r8670 := hand1 (x (-1) 2) (x (-1) 7)
    have b8671 := hb (x (-1) 2)
    have b8672 := hb (x (-1) 2 && x (-1) 7)
    clear * - r8670 b8671 b8672 d8661
    omega
  have d8673 : (x (-1) 3).toNat = 0 := by
    have r8674 : (x (-1) 2).toNat = (x (-1) 3).toNat := congrArg Bool.toNat (h23 (-1))
    have b8675 := hb (x (-1) 2)
    have b8676 := hb (x (-1) 3)
    clear * - r8674 b8675 b8676 d8661
    omega
  have d8677 : (x (-1) 11).toNat = 0 := by
    have r8678 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b8679 := hb (x (-1) 3)
    have b8680 := hb (x (-1) 11)
    clear * - r8678 b8679 b8680 d8673
    omega
  have d8681 : (x (-1) 4 && x (-1) 11).toNat = 0 := by
    have r8682 := hand2 (x (-1) 4) (x (-1) 11)
    have b8683 := hb (x (-1) 11)
    have b8684 := hb (x (-1) 4 && x (-1) 11)
    clear * - r8682 b8683 b8684 d8677
    omega
  have d8685 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
    have r8686 := hand2 (x (-1) 7) (x (-1) 11)
    have b8687 := hb (x (-1) 11)
    have b8688 := hb (x (-1) 7 && x (-1) 11)
    clear * - r8686 b8687 b8688 d8677
    omega
  have d8689 : (x (-1) 10 && x (-1) 11).toNat = 0 := by
    have r8690 := hand2 (x (-1) 10) (x (-1) 11)
    have b8691 := hb (x (-1) 11)
    have b8692 := hb (x (-1) 10 && x (-1) 11)
    clear * - r8690 b8691 b8692 d8677
    omega
  have d8693 : (x (-1) 10).toNat = 0 := by
    have r8694 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b8695 := hb (x (-1) 2)
    have b8696 := hb (x (-1) 10)
    clear * - r8694 b8695 b8696 d8661
    omega
  have d8697 : (x (-1) 4 && x (-1) 10).toNat = 0 := by
    have r8698 := hand2 (x (-1) 4) (x (-1) 10)
    have b8699 := hb (x (-1) 10)
    have b8700 := hb (x (-1) 4 && x (-1) 10)
    clear * - r8698 b8699 b8700 d8693
    omega
  have d8701 : (x (-2) 1).toNat = 1 := by
    have r8702 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8703 := hb (x (-2) 1)
    have b8704 := hb (x (-1) 14)
    clear * - r8702 b8703 b8704 d8649
    omega
  have d8705 : (x (-2) 14).toNat = 1 := by
    have r8706 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
    have b8707 := hb (x (-2) 1)
    have b8708 := hb (x (-2) 14)
    clear * - r8706 b8707 b8708 d8701
    omega
  have d8709 : (x (-3) 1).toNat = 0 := by
    have r8710 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8711 := hb (x (-3) 1)
    have b8712 := hb (x (-2) 14)
    clear * - r8710 b8711 b8712 d8705
    omega
  have d8713 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r8714 := hand1 (x (-3) 1) (x (-3) 14)
    have b8715 := hb (x (-3) 1)
    have b8716 := hb (x (-3) 1 && x (-3) 14)
    clear * - r8714 b8715 b8716 d8709
    omega
  have d8717 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
    have r8718 := hand1 (x (-3) 1) (x (-3) 12)
    have b8719 := hb (x (-3) 1)
    have b8720 := hb (x (-3) 1 && x (-3) 12)
    clear * - r8718 b8719 b8720 d8709
    omega
  have d8721 : (x (-3) 14).toNat = 0 := by
    have r8722 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
    have b8723 := hb (x (-3) 1)
    have b8724 := hb (x (-3) 14)
    clear * - r8722 b8723 b8724 d8709
    omega
  have d8725 : (x (-3) 6).toNat = 0 := by
    have r8726 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
    have b8727 := hb (x (-3) 6)
    have b8728 := hb (x (-3) 14)
    clear * - r8726 b8727 b8728 d8721
    omega
  have d8729 : (x (-3) 6 && x (-3) 13).toNat = 0 := by
    have r8730 := hand1 (x (-3) 6) (x (-3) 13)
    have b8731 := hb (x (-3) 6)
    have b8732 := hb (x (-3) 6 && x (-3) 13)
    clear * - r8730 b8731 b8732 d8725
    omega
  have d8733 : (x (-3) 6 && x (-3) 12).toNat = 0 := by
    have r8734 := hand1 (x (-3) 6) (x (-3) 12)
    have b8735 := hb (x (-3) 6)
    have b8736 := hb (x (-3) 6 && x (-3) 12)
    clear * - r8734 b8735 b8736 d8725
    omega
  have d8737 : (x (-3) 2).toNat = 0 := by
    have r8738 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b8739 := hb (x (-3) 2)
    have b8740 := hb (x (-3) 14)
    clear * - r8738 b8739 b8740 d8721
    omega
  have d8741 : (x (-3) 13).toNat = 0 := by
    have r8742 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b8743 := hb (x (-3) 1)
    have b8744 := hb (x (-3) 13)
    clear * - r8742 b8743 b8744 d8709
    omega
  have d8745 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
    have r8746 := hand2 (x (-3) 4) (x (-3) 13)
    have b8747 := hb (x (-3) 13)
    have b8748 := hb (x (-3) 4 && x (-3) 13)
    clear * - r8746 b8747 b8748 d8741
    omega
  have d8749 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
    have r8750 := hand2 (x (-3) 9) (x (-3) 13)
    have b8751 := hb (x (-3) 13)
    have b8752 := hb (x (-3) 9 && x (-3) 13)
    clear * - r8750 b8751 b8752 d8741
    omega
  have d8753 : (x (-3) 12 && x (-3) 13).toNat = 0 := by
    have r8754 := hand2 (x (-3) 12) (x (-3) 13)
    have b8755 := hb (x (-3) 13)
    have b8756 := hb (x (-3) 12 && x (-3) 13)
    clear * - r8754 b8755 b8756 d8741
    omega
  have d8757 : (x (-3) 9).toNat = 0 := by
    have r8758 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b8759 := hb (x (-3) 1)
    have b8760 := hb (x (-3) 9)
    clear * - r8758 b8759 b8760 d8709
    omega
  have d8761 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
    have r8762 := hand2 (x (-3) 4) (x (-3) 9)
    have b8763 := hb (x (-3) 9)
    have b8764 := hb (x (-3) 4 && x (-3) 9)
    clear * - r8762 b8763 b8764 d8757
    omega
  have d8765 : (x (-4) 1).toNat = 1 := by
    have r8766 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8767 := hb (x (-4) 1)
    have b8768 := hb (x (-3) 14)
    clear * - r8766 b8767 b8768 d8721
    omega
  have d8769 : (x (-4) 14).toNat = 1 := by
    have r8770 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
    have b8771 := hb (x (-4) 1)
    have b8772 := hb (x (-4) 14)
    clear * - r8770 b8771 b8772 d8765
    omega
  have d8773 : (x (-5) 1).toNat = 0 := by
    have r8774 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8775 := hb (x (-5) 1)
    have b8776 := hb (x (-4) 14)
    clear * - r8774 b8775 b8776 d8769
    omega
  have d8777 : (x (-5) 14).toNat = 0 := by
    have r8778 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
    have b8779 := hb (x (-5) 1)
    have b8780 := hb (x (-5) 14)
    clear * - r8778 b8779 b8780 d8773
    omega
  have d8781 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
    have r8782 := hand2 (x (-5) 3) (x (-5) 14)
    have b8783 := hb (x (-5) 14)
    have b8784 := hb (x (-5) 3 && x (-5) 14)
    clear * - r8782 b8783 b8784 d8777
    omega
  have d8785 : (x (-5) 8 && x (-5) 14).toNat = 0 := by
    have r8786 := hand2 (x (-5) 8) (x (-5) 14)
    have b8787 := hb (x (-5) 14)
    have b8788 := hb (x (-5) 8 && x (-5) 14)
    clear * - r8786 b8787 b8788 d8777
    omega
  have d8789 : (x (-5) 6).toNat = 0 := by
    have r8790 : (x (-5) 6).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp6 (-5))
    have b8791 := hb (x (-5) 6)
    have b8792 := hb (x (-5) 14)
    clear * - r8790 b8791 b8792 d8777
    omega
  have d8793 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
    have r8794 := hand1 (x (-5) 6) (x (-5) 11)
    have b8795 := hb (x (-5) 6)
    have b8796 := hb (x (-5) 6 && x (-5) 11)
    clear * - r8794 b8795 b8796 d8789
    omega
  have d8797 : (x (-5) 6 && x (-5) 10).toNat = 0 := by
    have r8798 := hand1 (x (-5) 6) (x (-5) 10)
    have b8799 := hb (x (-5) 6)
    have b8800 := hb (x (-5) 6 && x (-5) 10)
    clear * - r8798 b8799 b8800 d8789
    omega
  have d8801 : (x (-5) 2).toNat = 0 := by
    have r8802 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
    have b8803 := hb (x (-5) 2)
    have b8804 := hb (x (-5) 14)
    clear * - r8802 b8803 b8804 d8777
    omega
  have d8805 : (x (-5) 3).toNat = 0 := by
    have r8806 : (x (-5) 2).toNat = (x (-5) 3).toNat := congrArg Bool.toNat (h23 (-5))
    have b8807 := hb (x (-5) 2)
    have b8808 := hb (x (-5) 3)
    clear * - r8806 b8807 b8808 d8801
    omega
  have d8809 : (x (-5) 11).toNat = 0 := by
    have r8810 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
    have b8811 := hb (x (-5) 3)
    have b8812 := hb (x (-5) 11)
    clear * - r8810 b8811 b8812 d8805
    omega
  have d8813 : (x (-5) 10).toNat = 0 := by
    have r8814 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b8815 := hb (x (-5) 2)
    have b8816 := hb (x (-5) 10)
    clear * - r8814 b8815 b8816 d8801
    omega
  have d8817 : (x (-6) 1).toNat = 1 := by
    have r8818 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8819 := hb (x (-6) 1)
    have b8820 := hb (x (-5) 14)
    clear * - r8818 b8819 b8820 d8777
    omega
  have d8821 : (x (-6) 14).toNat = 1 := by
    have r8822 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
    have b8823 := hb (x (-6) 1)
    have b8824 := hb (x (-6) 14)
    clear * - r8822 b8823 b8824 d8817
    omega
  have d8825 : (x (-7) 1).toNat = 0 := by
    have r8826 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8827 := hb (x (-7) 1)
    have b8828 := hb (x (-6) 14)
    clear * - r8826 b8827 b8828 d8821
    omega
  have d8829 : (x (-7) 14).toNat = 0 := by
    have r8830 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
    have b8831 := hb (x (-7) 1)
    have b8832 := hb (x (-7) 14)
    clear * - r8830 b8831 b8832 d8825
    omega
  have d8833 : (x (-7) 2).toNat = 0 := by
    have r8834 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b8835 := hb (x (-7) 2)
    have b8836 := hb (x (-7) 14)
    clear * - r8834 b8835 b8836 d8829
    omega
  have d8837 : (x (-7) 2 && x (-7) 12).toNat = 0 := by
    have r8838 := hand1 (x (-7) 2) (x (-7) 12)
    have b8839 := hb (x (-7) 2)
    have b8840 := hb (x (-7) 2 && x (-7) 12)
    clear * - r8838 b8839 b8840 d8833
    omega
  have d8841 : (x (-7) 10).toNat = 0 := by
    have r8842 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
    have b8843 := hb (x (-7) 2)
    have b8844 := hb (x (-7) 10)
    clear * - r8842 b8843 b8844 d8833
    omega
  have d8845 : (x (-7) 13).toNat = 0 := by
    have r8846 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
    have b8847 := hb (x (-7) 1)
    have b8848 := hb (x (-7) 13)
    clear * - r8846 b8847 b8848 d8825
    omega
  have d8849 : (x (-7) 8 && x (-7) 13).toNat = 0 := by
    have r8850 := hand2 (x (-7) 8) (x (-7) 13)
    have b8851 := hb (x (-7) 13)
    have b8852 := hb (x (-7) 8 && x (-7) 13)
    clear * - r8850 b8851 b8852 d8845
    omega
  have d8853 : (x (-7) 5).toNat = 0 := by
    have r8854 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
    have b8855 := hb (x (-7) 5)
    have b8856 := hb (x (-7) 13)
    clear * - r8854 b8855 b8856 d8845
    omega
  have d8857 : (x (-8) 1).toNat = 1 := by
    have r8858 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8859 := hb (x (-8) 1)
    have b8860 := hb (x (-7) 14)
    clear * - r8858 b8859 b8860 d8829
    omega
  have d8861 : (x (-8) 14).toNat = 1 := by
    have r8862 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
    have b8863 := hb (x (-8) 1)
    have b8864 := hb (x (-8) 14)
    clear * - r8862 b8863 b8864 d8857
    omega
  have d8865 : (x (-9) 1).toNat = 0 := by
    have r8866 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8867 := hb (x (-9) 1)
    have b8868 := hb (x (-8) 14)
    clear * - r8866 b8867 b8868 d8861
    omega
  have d8869 : (x (-9) 14).toNat = 0 := by
    have r8870 : (x (-9) 1).toNat = (x (-9) 14).toNat := congrArg Bool.toNat (h114 (-9))
    have b8871 := hb (x (-9) 1)
    have b8872 := hb (x (-9) 14)
    clear * - r8870 b8871 b8872 d8865
    omega
  have d8873 : (x (-9) 4 && x (-9) 14).toNat = 0 := by
    have r8874 := hand2 (x (-9) 4) (x (-9) 14)
    have b8875 := hb (x (-9) 14)
    have b8876 := hb (x (-9) 4 && x (-9) 14)
    clear * - r8874 b8875 b8876 d8869
    omega
  have d8877 : (x (-9) 2).toNat = 0 := by
    have r8878 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
    have b8879 := hb (x (-9) 2)
    have b8880 := hb (x (-9) 14)
    clear * - r8878 b8879 b8880 d8869
    omega
  have d8881 : (x (-9) 2 && x (-9) 12).toNat = 0 := by
    have r8882 := hand1 (x (-9) 2) (x (-9) 12)
    have b8883 := hb (x (-9) 2)
    have b8884 := hb (x (-9) 2 && x (-9) 12)
    clear * - r8882 b8883 b8884 d8877
    omega
  have d8885 : (x (-9) 3).toNat = 0 := by
    have r8886 : (x (-9) 2).toNat = (x (-9) 3).toNat := congrArg Bool.toNat (h23 (-9))
    have b8887 := hb (x (-9) 2)
    have b8888 := hb (x (-9) 3)
    clear * - r8886 b8887 b8888 d8877
    omega
  have d8889 : (x (-9) 10).toNat = 0 := by
    have r8890 : (x (-9) 10).toNat ≤ (x (-9) 2).toNat := himp _ _ (hp10 (-9))
    have b8891 := hb (x (-9) 2)
    have b8892 := hb (x (-9) 10)
    clear * - r8890 b8891 b8892 d8877
    omega
  have d8893 : (x 1 8).toNat = 0 := by
    have r8894 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8895 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e8896 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e8897 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e8898 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e8899 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e8900 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b8901 := hb (x (-6) 7)
    have b8902 := hb (x (-5) 6)
    have b8903 := hb (x (-4) 5)
    have b8904 := hb (x (-3) 4)
    have b8905 := hb (x (-2) 11)
    have b8906 := hb (x (-1) 10)
    have b8907 := hb (x 0 9)
    have b8908 := hb (x 1 8)
    clear * - r8894 e8895 e8896 e8897 e8898 e8899 e8900 b8901 b8902 b8903 b8904 b8905 b8906 b8907 b8908 g0 d8693 d8789
    omega
  have d8909 : (x (-2) 11).toNat = 0 := by
    have r8910 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8911 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e8912 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e8913 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e8914 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e8915 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e8916 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b8917 := hb (x (-6) 7)
    have b8918 := hb (x (-5) 6)
    have b8919 := hb (x (-4) 5)
    have b8920 := hb (x (-3) 4)
    have b8921 := hb (x (-2) 11)
    have b8922 := hb (x (-1) 10)
    have b8923 := hb (x 0 9)
    have b8924 := hb (x 1 8)
    clear * - r8910 e8911 e8912 e8913 e8914 e8915 e8916 b8917 b8918 b8919 b8920 b8921 b8922 b8923 b8924 d8893 g0 d8693 d8789
    omega
  have d8925 : (x (-2) 5 && x (-2) 11).toNat = 0 := by
    have r8926 := hand2 (x (-2) 5) (x (-2) 11)
    have b8927 := hb (x (-2) 11)
    have b8928 := hb (x (-2) 5 && x (-2) 11)
    clear * - r8926 b8927 b8928 d8909
    omega
  have d8929 : (x (-2) 11 && x (-2) 12).toNat = 0 := by
    have r8930 := hand1 (x (-2) 11) (x (-2) 12)
    have b8931 := hb (x (-2) 11)
    have b8932 := hb (x (-2) 11 && x (-2) 12)
    clear * - r8930 b8931 b8932 d8909
    omega
  have d8933 : (x (-3) 4).toNat = 0 := by
    have r8934 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8935 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e8936 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e8937 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e8938 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e8939 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e8940 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b8941 := hb (x (-6) 7)
    have b8942 := hb (x (-5) 6)
    have b8943 := hb (x (-4) 5)
    have b8944 := hb (x (-3) 4)
    have b8945 := hb (x (-2) 11)
    have b8946 := hb (x (-1) 10)
    have b8947 := hb (x 0 9)
    have b8948 := hb (x 1 8)
    clear * - r8934 e8935 e8936 e8937 e8938 e8939 e8940 b8941 b8942 b8943 b8944 b8945 b8946 b8947 b8948 d8893 g0 d8693 d8909 d8789
    omega
  have d8949 : (x (-3) 4 && x (-3) 8).toNat = 0 := by
    have r8950 := hand1 (x (-3) 4) (x (-3) 8)
    have b8951 := hb (x (-3) 4)
    have b8952 := hb (x (-3) 4 && x (-3) 8)
    clear * - r8950 b8951 b8952 d8933
    omega
  have d8953 : (x (-4) 5).toNat = 0 := by
    have r8954 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8955 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e8956 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e8957 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e8958 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e8959 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e8960 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b8961 := hb (x (-6) 7)
    have b8962 := hb (x (-5) 6)
    have b8963 := hb (x (-4) 5)
    have b8964 := hb (x (-3) 4)
    have b8965 := hb (x (-2) 11)
    have b8966 := hb (x (-1) 10)
    have b8967 := hb (x 0 9)
    have b8968 := hb (x 1 8)
    clear * - r8954 e8955 e8956 e8957 e8958 e8959 e8960 b8961 b8962 b8963 b8964 b8965 b8966 b8967 b8968 d8893 g0 d8693 d8909 d8933 d8789
    omega
  have d8969 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
    have r8970 := hand1 (x (-4) 5) (x (-4) 14)
    have b8971 := hb (x (-4) 5)
    have b8972 := hb (x (-4) 5 && x (-4) 14)
    clear * - r8970 b8971 b8972 d8953
    omega
  have d8973 : (x (-2) 3 && x (-2) 12).toNat = 1 := by
    have r8974 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8975 := hb (x (-5) 6)
    have b8976 := hb (x 1 9)
    have b8977 := hb (x 0 1 && x 0 10)
    have b8978 := hb (x (-1) 2 && x (-1) 11)
    have b8979 := hb (x (-2) 3 && x (-2) 12)
    have b8980 := hb (x (-3) 4 && x (-3) 13)
    have b8981 := hb (x (-4) 5 && x (-4) 14)
    clear * - r8974 b8975 b8976 b8977 b8978 b8979 b8980 b8981 d8493 d8445 d8665 d8745 d8969 d8789
    omega
  have d8982 : (x (-2) 12).toNat = 1 := by
    have r8983 := hand2 (x (-2) 3) (x (-2) 12)
    have b8984 := hb (x (-2) 12)
    have b8985 := hb (x (-2) 3 && x (-2) 12)
    clear * - r8983 b8984 b8985 d8973
    omega
  have d8986 : (x (-4) 2).toNat = 0 := by
    have r8987 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8988 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e8989 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b8990 := hb (x (-5) 3)
    have b8991 := hb (x (-4) 2)
    have b8992 := hb (x (-3) 13)
    have b8993 := hb (x (-2) 12)
    clear * - r8987 e8988 e8989 b8990 b8991 b8992 b8993 d8982 d8741 d8805
    omega
  have d8994 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
    have r8995 := hand1 (x (-4) 2) (x (-4) 13)
    have b8996 := hb (x (-4) 2)
    have b8997 := hb (x (-4) 2 && x (-4) 13)
    clear * - r8995 b8996 b8997 d8986
    omega
  have d8998 : (x (-6) 4).toNat = 1 := by
    have r8999 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9000 := hb (x (-6) 4)
    have b9001 := hb (x (-2) 11)
    have b9002 := hb (x (-3) 1 && x (-3) 12)
    have b9003 := hb (x (-4) 2 && x (-4) 13)
    have b9004 := hb (x (-5) 3 && x (-5) 14)
    clear * - r8999 b9000 b9001 b9002 b9003 b9004 d8909 d8717 d8994 d8781
    omega
  have d9005 : (x (-6) 12).toNat = 1 := by
    have r9006 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
    have b9007 := hb (x (-6) 4)
    have b9008 := hb (x (-6) 12)
    clear * - r9006 b9007 b9008 d8998
    omega
  have d9009 : (x (-8) 2).toNat = 0 := by
    have r9010 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9011 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
    have e9012 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
    have b9013 := hb (x (-9) 3)
    have b9014 := hb (x (-8) 2)
    have b9015 := hb (x (-7) 13)
    have b9016 := hb (x (-6) 12)
    clear * - r9010 e9011 e9012 b9013 b9014 b9015 b9016 d9005 d8845 d8885
    omega
  have d9017 : (x (-8) 3).toNat = 0 := by
    have r9018 : (x (-8) 2).toNat = (x (-8) 3).toNat := congrArg Bool.toNat (h23 (-8))
    have b9019 := hb (x (-8) 2)
    have b9020 := hb (x (-8) 3)
    clear * - r9018 b9019 b9020 d9009
    omega
  have d9021 : (x (-8) 3 && x (-8) 13).toNat = 0 := by
    have r9022 := hand1 (x (-8) 3) (x (-8) 13)
    have b9023 := hb (x (-8) 3)
    have b9024 := hb (x (-8) 3 && x (-8) 13)
    clear * - r9022 b9023 b9024 d9017
    omega
  have d9025 : (x (-8) 11).toNat = 0 := by
    have r9026 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
    have b9027 := hb (x (-8) 3)
    have b9028 := hb (x (-8) 11)
    clear * - r9026 b9027 b9028 d9017
    omega
  have d9029 : (x (-8) 1 && x (-8) 11).toNat = 0 := by
    have r9030 := hand2 (x (-8) 1) (x (-8) 11)
    have b9031 := hb (x (-8) 11)
    have b9032 := hb (x (-8) 1 && x (-8) 11)
    clear * - r9030 b9031 b9032 d9025
    omega
  have d9033 : (x (-4) 3).toNat = 0 := by
    have r9034 : (x (-4) 2).toNat = (x (-4) 3).toNat := congrArg Bool.toNat (h23 (-4))
    have b9035 := hb (x (-4) 2)
    have b9036 := hb (x (-4) 3)
    clear * - r9034 b9035 b9036 d8986
    omega
  have d9037 : (x (-4) 10).toNat = 0 := by
    have r9038 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
    have b9039 := hb (x (-4) 2)
    have b9040 := hb (x (-4) 10)
    clear * - r9038 b9039 b9040 d8986
    omega
  have d9041 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
    have r9042 := hand2 (x (-4) 5) (x (-4) 10)
    have b9043 := hb (x (-4) 10)
    have b9044 := hb (x (-4) 5 && x (-4) 10)
    clear * - r9042 b9043 b9044 d9037
    omega
  have d9045 : (x (-2) 13).toNat = 1 := by
    have r9046 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9047 := hb (x (-4) 2)
    have b9048 := hb (x (-2) 13)
    have b9049 := hb (x (-3) 1 && x (-3) 14)
    clear * - r9046 b9047 b9048 b9049 d8713 d8986
    omega
  have d9050 : (x (-1) 12).toNat = 0 := by
    have r9051 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9052 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e9053 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b9054 := hb (x (-4) 3)
    have b9055 := hb (x (-3) 2)
    have b9056 := hb (x (-2) 13)
    have b9057 := hb (x (-1) 12)
    clear * - r9051 e9052 e9053 b9054 b9055 b9056 b9057 d9045 d8737 d9033
    omega
  have d9058 : (x (-1) 4).toNat = 0 := by
    have r9059 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b9060 := hb (x (-1) 4)
    have b9061 := hb (x (-1) 12)
    clear * - r9059 b9060 b9061 d9050
    omega
  have d9062 : (x (-2) 3).toNat = 1 := by
    have r9063 := hand1 (x (-2) 3) (x (-2) 12)
    have b9064 := hb (x (-2) 3)
    have b9065 := hb (x (-2) 3 && x (-2) 12)
    clear * - r9063 b9064 b9065 d8973
    omega
  have d9066 : (x 1 12).toNat = 0 := by
    have r9067 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9068 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e9069 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b9070 := hb (x (-2) 3)
    have b9071 := hb (x (-1) 2)
    have b9072 := hb (x 0 13)
    have b9073 := hb (x 1 12)
    clear * - r9067 e9068 e9069 b9070 b9071 b9072 b9073 d8661 d9062
    omega
  have d9074 : (x 1 4).toNat = 0 := by
    have r9075 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b9076 := hb (x 1 4)
    have b9077 := hb (x 1 12)
    clear * - r9075 b9076 b9077 d9066
    omega
  have d9078 : (x 0 13).toNat = 0 := by
    have r9079 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9080 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e9081 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b9082 := hb (x (-2) 3)
    have b9083 := hb (x (-1) 2)
    have b9084 := hb (x 0 13)
    have b9085 := hb (x 1 12)
    clear * - r9079 e9080 e9081 b9082 b9083 b9084 b9085 d9066 d8661 d9062
    omega
  have d9086 : (x 0 5).toNat = 0 := by
    have r9087 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
    have b9088 := hb (x 0 5)
    have b9089 := hb (x 0 13)
    clear * - r9087 b9088 b9089 d9078
    omega
  have d9090 : (x 0 5 && x 0 14).toNat = 0 := by
    have r9091 := hand1 (x 0 5) (x 0 14)
    have b9092 := hb (x 0 5)
    have b9093 := hb (x 0 5 && x 0 14)
    clear * - r9091 b9092 b9093 d9086
    omega
  have d9094 : (x (-4) 5 && x (-4) 9).toNat = 0 := by
    have r9095 := hand1 (x (-4) 5) (x (-4) 9)
    have b9096 := hb (x (-4) 5)
    have b9097 := hb (x (-4) 5 && x (-4) 9)
    clear * - r9095 b9096 b9097 d8953
    omega
  have d9098 : (x (-6) 7).toNat = 0 := by
    have r9099 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9100 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e9101 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e9102 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e9103 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e9104 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e9105 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b9106 := hb (x (-6) 7)
    have b9107 := hb (x (-5) 6)
    have b9108 := hb (x (-4) 5)
    have b9109 := hb (x (-3) 4)
    have b9110 := hb (x (-2) 11)
    have b9111 := hb (x (-1) 10)
    have b9112 := hb (x 0 9)
    have b9113 := hb (x 1 8)
    clear * - r9099 e9100 e9101 e9102 e9103 e9104 e9105 b9106 b9107 b9108 b9109 b9110 b9111 b9112 b9113 d8893 g0 d8693 d8909 d8933 d8953 d8789
    omega
  have d9114 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
    have r9115 := hand1 (x (-6) 7) (x (-6) 12)
    have b9116 := hb (x (-6) 7)
    have b9117 := hb (x (-6) 7 && x (-6) 12)
    clear * - r9115 b9116 b9117 d9098
    omega
  have d9118 : (x (-6) 7 && x (-6) 11).toNat = 0 := by
    have r9119 := hand1 (x (-6) 7) (x (-6) 11)
    have b9120 := hb (x (-6) 7)
    have b9121 := hb (x (-6) 7 && x (-6) 11)
    clear * - r9119 b9120 b9121 d9098
    omega
  have d9122 : (x (-2) 8).toNat = 0 := by
    have r9123 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9124 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e9125 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e9126 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e9127 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e9128 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e9129 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b9130 := hb (x (-9) 7)
    have b9131 := hb (x (-8) 6)
    have b9132 := hb (x (-7) 5)
    have b9133 := hb (x (-6) 4)
    have b9134 := hb (x (-5) 11)
    have b9135 := hb (x (-4) 10)
    have b9136 := hb (x (-3) 9)
    have b9137 := hb (x (-2) 8)
    clear * - r9123 e9124 e9125 e9126 e9127 e9128 e9129 b9130 b9131 b9132 b9133 b9134 b9135 b9136 b9137 d8757 d9037 d8809 d8998 d8853
    omega
  have d9138 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
    have r9139 := hand2 (x (-2) 3) (x (-2) 8)
    have b9140 := hb (x (-2) 8)
    have b9141 := hb (x (-2) 3 && x (-2) 8)
    clear * - r9139 b9140 b9141 d9122
    omega
  have d9142 : (x (-2) 8 && x (-2) 12).toNat = 0 := by
    have r9143 := hand1 (x (-2) 8) (x (-2) 12)
    have b9144 := hb (x (-2) 8)
    have b9145 := hb (x (-2) 8 && x (-2) 12)
    clear * - r9143 b9144 b9145 d9122
    omega
  have r9146 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9147 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9148 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9149 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9150 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9151 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
  have e9152 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
  have e9153 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
  have e9154 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
  have e9155 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
  have e9156 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
  have r9157 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9158 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
  have e9159 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
  have e9160 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
  have e9161 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
  have e9162 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
  have e9163 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
  have r9164 : 1 ≤ (x 9 1).toNat + (x 8 1 && x 8 2).toNat + (x 7 2 && x 7 3).toNat + (x 6 3 && x 6 4).toNat + (x 5 4 && x 5 5).toNat + (x 4 5 && x 4 6).toNat + (x 3 6 && x 3 7).toNat + (x 2 7 && x 2 8).toNat + (x 1 8 && x 1 9).toNat + (x 0 9 && x 0 10).toNat + (x (-1) 10 && x (-1) 11).toNat + (x (-2) 11 && x (-2) 12).toNat + (x (-3) 12 && x (-3) 13).toNat + (x (-4) 13 && x (-4) 14).toNat + (x (-5) 14).toNat := by have q := hcov1 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9165 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := by have q := hcov4 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9166 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
  have e9167 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
  have r9168 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9169 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
  have e9170 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
  have r9171 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9172 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9173 : 1 ≤ (x 3 7).toNat + (x 2 1 && x 2 8).toNat + (x 1 2 && x 1 9).toNat + (x 0 3 && x 0 10).toNat + (x (-1) 4 && x (-1) 11).toNat + (x (-2) 5 && x (-2) 12).toNat + (x (-3) 6 && x (-3) 13).toNat + (x (-4) 7 && x (-4) 14).toNat + (x (-5) 8).toNat := by have q := hcov7 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9174 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9175 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9176 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9177 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9178 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
  have r9179 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
  have r9180 := hand2 (x 8 1) (x 8 2)
  have r9181 := hand2 (x 6 3) (x 6 4)
  have r9182 := hand2 (x 4 5) (x 4 6)
  have r9183 := hand1 (x 2 7) (x 2 8)
  have r9184 := hand1 (x (-4) 13) (x (-4) 14)
  have r9185 := hand2 (x (-2) 3) (x (-2) 7)
  have r9186 := hand1 (x (-7) 8) (x (-7) 12)
  have r9187 := hand2 (x (-8) 9) (x (-8) 13)
  have r9188 := hand2 (x 4 2) (x 4 6)
  have r9189 := hand2 (x 2 4) (x 2 8)
  have r9190 := hand2 (x 0 1) (x 0 6)
  have r9191 := hand1 (x (-8) 9) (x (-8) 14)
  have r9192 := hand2 (x 2 1) (x 2 7)
  have r9193 := hand1 (x 0 3) (x 0 9)
  have r9194 := hand2 (x (-4) 7) (x (-4) 13)
  have r9195 := hand2 (x 2 1) (x 2 8)
  have r9196 := hand1 (x (-2) 5) (x (-2) 12)
  have r9197 := hand1 (x (-4) 7) (x (-4) 14)
  have r9198 := hand2 (x 4 1) (x 4 10)
  have r9199 := hand1 (x 2 3) (x 2 12)
  have r9200 := hand2 (x 8 1) (x 8 10)
  have r9201 := hand1 (x 6 3) (x 6 12)
  have r9202 := hand1 (x 4 5) (x 4 14)
  have r9203 := hand2 (x (-10) 3) (x (-10) 13)
  have r9204 := hand1 (x (-11) 4) (x (-11) 14)
  have r9205 := hand2 (x (-6) 1) (x (-6) 11)
  have b9206 := hb (x (-14) 7)
  have b9207 := hb (x (-13) 6)
  have b9208 := hb (x (-12) 5)
  have b9209 := hb (x (-11) 4)
  have b9210 := hb (x (-11) 14)
  have b9211 := hb (x (-10) 5)
  have b9212 := hb (x (-10) 11)
  have b9213 := hb (x (-10) 13)
  have b9214 := hb (x (-9) 10)
  have b9215 := hb (x (-9) 12)
  have b9216 := hb (x (-9) 14)
  have b9217 := hb (x (-8) 9)
  have b9218 := hb (x (-8) 11)
  have b9219 := hb (x (-8) 13)
  have b9220 := hb (x (-7) 8)
  have b9221 := hb (x (-7) 10)
  have b9222 := hb (x (-7) 12)
  have b9223 := hb (x (-6) 9)
  have b9224 := hb (x (-6) 11)
  have b9225 := hb (x (-5) 8)
  have b9226 := hb (x (-5) 10)
  have b9227 := hb (x (-5) 11)
  have b9228 := hb (x (-5) 14)
  have b9229 := hb (x (-4) 7)
  have b9230 := hb (x (-4) 9)
  have b9231 := hb (x (-4) 10)
  have b9232 := hb (x (-4) 13)
  have b9233 := hb (x (-4) 14)
  have b9234 := hb (x (-3) 6)
  have b9235 := hb (x (-3) 8)
  have b9236 := hb (x (-3) 12)
  have b9237 := hb (x (-3) 13)
  have b9238 := hb (x (-2) 5)
  have b9239 := hb (x (-2) 7)
  have b9240 := hb (x (-2) 11)
  have b9241 := hb (x (-2) 12)
  have b9242 := hb (x (-1) 4)
  have b9243 := hb (x (-1) 6)
  have b9244 := hb (x (-1) 7)
  have b9245 := hb (x (-1) 10)
  have b9246 := hb (x (-1) 11)
  have b9247 := hb (x 0 3)
  have b9248 := hb (x 0 5)
  have b9249 := hb (x 0 6)
  have b9250 := hb (x 0 9)
  have b9251 := hb (x 0 10)
  have b9252 := hb (x 1 2)
  have b9253 := hb (x 1 4)
  have b9254 := hb (x 1 5)
  have b9255 := hb (x 1 8)
  have b9256 := hb (x 1 9)
  have b9257 := hb (x 2 1)
  have b9258 := hb (x 2 3)
  have b9259 := hb (x 2 4)
  have b9260 := hb (x 2 7)
  have b9261 := hb (x 2 8)
  have b9262 := hb (x 3 2)
  have b9263 := hb (x 3 6)
  have b9264 := hb (x 3 7)
  have b9265 := hb (x 3 11)
  have b9266 := hb (x 4 1)
  have b9267 := hb (x 4 5)
  have b9268 := hb (x 4 6)
  have b9269 := hb (x 4 10)
  have b9270 := hb (x 5 4)
  have b9271 := hb (x 5 5)
  have b9272 := hb (x 5 9)
  have b9273 := hb (x 6 3)
  have b9274 := hb (x 6 4)
  have b9275 := hb (x 6 8)
  have b9276 := hb (x 7 2)
  have b9277 := hb (x 7 3)
  have b9278 := hb (x 8 1)
  have b9279 := hb (x 8 2)
  have b9280 := hb (x 8 10)
  have b9281 := hb (x 9 1)
  have b9282 := hb (x 9 9)
  have b9283 := hb (x 8 1 && x 8 2)
  have b9284 := hb (x 7 2 && x 7 3)
  have b9285 := hb (x 6 3 && x 6 4)
  have b9286 := hb (x 5 4 && x 5 5)
  have b9287 := hb (x 4 5 && x 4 6)
  have b9288 := hb (x 3 6 && x 3 7)
  have b9289 := hb (x 2 7 && x 2 8)
  have b9290 := hb (x 1 8 && x 1 9)
  have b9291 := hb (x 0 9 && x 0 10)
  have b9292 := hb (x (-1) 10 && x (-1) 11)
  have b9293 := hb (x (-2) 11 && x (-2) 12)
  have b9294 := hb (x (-3) 12 && x (-3) 13)
  have b9295 := hb (x (-4) 13 && x (-4) 14)
  have b9296 := hb (x (-1) 2 && x (-1) 6)
  have b9297 := hb (x (-2) 3 && x (-2) 7)
  have b9298 := hb (x (-3) 4 && x (-3) 8)
  have b9299 := hb (x (-4) 5 && x (-4) 9)
  have b9300 := hb (x (-5) 6 && x (-5) 10)
  have b9301 := hb (x (-6) 7 && x (-6) 11)
  have b9302 := hb (x (-7) 8 && x (-7) 12)
  have b9303 := hb (x (-8) 9 && x (-8) 13)
  have b9304 := hb (x 4 2 && x 4 6)
  have b9305 := hb (x 3 3 && x 3 7)
  have b9306 := hb (x 2 4 && x 2 8)
  have b9307 := hb (x 1 5 && x 1 9)
  have b9308 := hb (x 0 6 && x 0 10)
  have b9309 := hb (x (-1) 7 && x (-1) 11)
  have b9310 := hb (x (-2) 8 && x (-2) 12)
  have b9311 := hb (x (-3) 9 && x (-3) 13)
  have b9312 := hb (x 0 1 && x 0 6)
  have b9313 := hb (x (-1) 2 && x (-1) 7)
  have b9314 := hb (x (-2) 3 && x (-2) 8)
  have b9315 := hb (x (-3) 4 && x (-3) 9)
  have b9316 := hb (x (-4) 5 && x (-4) 10)
  have b9317 := hb (x (-5) 6 && x (-5) 11)
  have b9318 := hb (x (-6) 7 && x (-6) 12)
  have b9319 := hb (x (-7) 8 && x (-7) 13)
  have b9320 := hb (x (-8) 9 && x (-8) 14)
  have b9321 := hb (x 2 1 && x 2 7)
  have b9322 := hb (x 1 2 && x 1 8)
  have b9323 := hb (x 0 3 && x 0 9)
  have b9324 := hb (x (-1) 4 && x (-1) 10)
  have b9325 := hb (x (-2) 5 && x (-2) 11)
  have b9326 := hb (x (-3) 6 && x (-3) 12)
  have b9327 := hb (x (-4) 7 && x (-4) 13)
  have b9328 := hb (x (-5) 8 && x (-5) 14)
  have b9329 := hb (x 2 1 && x 2 8)
  have b9330 := hb (x 1 2 && x 1 9)
  have b9331 := hb (x 0 3 && x 0 10)
  have b9332 := hb (x (-1) 4 && x (-1) 11)
  have b9333 := hb (x (-2) 5 && x (-2) 12)
  have b9334 := hb (x (-3) 6 && x (-3) 13)
  have b9335 := hb (x (-4) 7 && x (-4) 14)
  have b9336 := hb (x 4 1 && x 4 10)
  have b9337 := hb (x 3 2 && x 3 11)
  have b9338 := hb (x 2 3 && x 2 12)
  have b9339 := hb (x 1 4 && x 1 13)
  have b9340 := hb (x 0 5 && x 0 14)
  have b9341 := hb (x 8 1 && x 8 10)
  have b9342 := hb (x 7 2 && x 7 11)
  have b9343 := hb (x 6 3 && x 6 12)
  have b9344 := hb (x 5 4 && x 5 13)
  have b9345 := hb (x 4 5 && x 4 14)
  have b9346 := hb (x (-8) 1 && x (-8) 11)
  have b9347 := hb (x (-9) 2 && x (-9) 12)
  have b9348 := hb (x (-10) 3 && x (-10) 13)
  have b9349 := hb (x (-11) 4 && x (-11) 14)
  have b9350 := hb (x (-6) 1 && x (-6) 11)
  have b9351 := hb (x (-7) 2 && x (-7) 12)
  have b9352 := hb (x (-8) 3 && x (-8) 13)
  have b9353 := hb (x (-9) 4 && x (-9) 14)
  linarith only [r9146, r9147, r9148, r9149, r9150, e9151, e9152, e9153, e9154, e9155, e9156, r9157, e9158, e9159, e9160, e9161, e9162, e9163, r9164, r9165, e9166, e9167, r9168, e9169, e9170, r9171, r9172, r9173, r9174, r9175, r9176, r9177, r9178, r9179, r9180, r9181, r9182, r9183, r9184, r9185, r9186, r9187, r9188, r9189, r9190, r9191, r9192, r9193, r9194, r9195, r9196, r9197, r9198, r9199, r9200, r9201, r9202, r9203, r9204, r9205, b9206, b9207, b9208, b9209, b9210, b9211, b9212, b9213, b9214, b9215, b9216, b9217, b9218, b9219, b9220, b9221, b9222, b9223, b9224, b9225, b9226, b9227, b9228, b9229, b9230, b9231, b9232, b9233, b9234, b9235, b9236, b9237, b9238, b9239, b9240, b9241, b9242, b9243, b9244, b9245, b9246, b9247, b9248, b9249, b9250, b9251, b9252, b9253, b9254, b9255, b9256, b9257, b9258, b9259, b9260, b9261, b9262, b9263, b9264, b9265, b9266, b9267, b9268, b9269, b9270, b9271, b9272, b9273, b9274, b9275, b9276, b9277, b9278, b9279, b9280, b9281, b9282, b9283, b9284, b9285, b9286, b9287, b9288, b9289, b9290, b9291, b9292, b9293, b9294, b9295, b9296, b9297, b9298, b9299, b9300, b9301, b9302, b9303, b9304, b9305, b9306, b9307, b9308, b9309, b9310, b9311, b9312, b9313, b9314, b9315, b9316, b9317, b9318, b9319, b9320, b9321, b9322, b9323, b9324, b9325, b9326, b9327, b9328, b9329, b9330, b9331, b9332, b9333, b9334, b9335, b9336, b9337, b9338, b9339, b9340, b9341, b9342, b9343, b9344, b9345, b9346, b9347, b9348, b9349, b9350, b9351, b9352, b9353, d8889, d8869, d9025, d8841, d8813, d8809, d8777, d9037, d8769, d8725, d8741, d8909, d8982, d9058, d8653, d8693, d8677, d9086, g0, g1, d8637, d9074, d8485, d8893, d8493, d8509, d8617, d8609, d8633, d8525, d8545, d8553, d8593, d8605, d8577, d8585, d8589, d8601, d8549, d8613, d8501, d8457, d8689, d8929, d8753, d8657, d8949, d9094, d8797, d9118, d8629, d8489, d8453, d8685, d9142, d8749, d8669, d9138, d8761, d9041, d8793, d9114, d8849, d8641, d8697, d8925, d8733, d8785, d8497, d8449, d8681, d8729, d8621, d8481, d9090, d8597, d8541, d9029, d8881, d8837, d9021, d8873]

theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v91_100 (x : ℤ → Fin 16 → Bool)
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
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 9).toNat = 1) (g1 : (x 0 10).toNat = 0) : False := cycle_power_fifteen_tight_type_sequence_shape_rules_core_v91_100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 h114 h23 g0 g1
