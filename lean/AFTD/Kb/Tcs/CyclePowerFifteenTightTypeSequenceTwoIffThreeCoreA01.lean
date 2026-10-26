import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a01

Topic: combinatorics   Node: ed61077bb389

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 32 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a01_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 5).toNat = 0)
    (g1 : (x (-3) 13).toNat = 0)
    (g2 : (x (-1) 5).toNat = 0)
    (g3 : (x (-1) 11).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 3).toNat = 0)
    (g6 : (x 0 5).toNat = 0)
    (g7 : (x 0 7).toNat = 1)
    (g8 : (x 0 13).toNat = 0)
    (g9 : (x 0 14).toNat = 1)
    (g10 : (x 1 5).toNat = 0)
    (g11 : (x 1 13).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 12).toNat = 0)
    (g14 : (x 2 8 && x 2 12).toNat = 0)
    (g15 : (x 1 9 && x 1 13).toNat = 0)
    (g16 : (x 0 2 && x 0 11).toNat = 0)
    (g17 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g18 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g19 : (x 2 4 && x 2 13).toNat = 0)
    (g20 : (x 1 5 && x 1 14).toNat = 0)
    (g21 : (x 2 2 && x 2 12).toNat = 0)
    (g22 : (x 1 3 && x 1 13).toNat = 0)
    (g23 : (x 0 4 && x 0 14).toNat = 0)
    (g24 : (x 0 1 && x 0 12).toNat = 0)
    (g25 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g26 : (x 0 2 && x 0 13).toNat = 0)
    (g27 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g28 : (x 2 1 && x 2 12).toNat = 0)
    (g29 : (x 1 2 && x 1 13).toNat = 0)
    (g30 : (x 0 3 && x 0 14).toNat = 0)
    (g31 : (x (-3) 1 && x (-3) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8523 : (x 7 8).toNat = 0 := by
    have r8524 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8525 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8526 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8527 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8528 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8529 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8530 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8531 := hb (x 0 7)
    have b8532 := hb (x 1 6)
    have b8533 := hb (x 2 5)
    have b8534 := hb (x 3 4)
    have b8535 := hb (x 4 11)
    have b8536 := hb (x 5 10)
    have b8537 := hb (x 6 9)
    have b8538 := hb (x 7 8)
    clear * - r8524 e8525 e8526 e8527 e8528 e8529 e8530 b8531 b8532 b8533 b8534 b8535 b8536 b8537 b8538 g7
    omega
  have d8539 : (x 6 9).toNat = 0 := by
    have r8540 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8541 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8542 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8543 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8544 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8545 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8546 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8547 := hb (x 0 7)
    have b8548 := hb (x 1 6)
    have b8549 := hb (x 2 5)
    have b8550 := hb (x 3 4)
    have b8551 := hb (x 4 11)
    have b8552 := hb (x 5 10)
    have b8553 := hb (x 6 9)
    have b8554 := hb (x 7 8)
    clear * - r8540 e8541 e8542 e8543 e8544 e8545 e8546 b8547 b8548 b8549 b8550 b8551 b8552 b8553 b8554 d8523 g7
    omega
  have d8555 : (x 5 10).toNat = 0 := by
    have r8556 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8557 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8558 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8559 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8560 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8561 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8562 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8563 := hb (x 0 7)
    have b8564 := hb (x 1 6)
    have b8565 := hb (x 2 5)
    have b8566 := hb (x 3 4)
    have b8567 := hb (x 4 11)
    have b8568 := hb (x 5 10)
    have b8569 := hb (x 6 9)
    have b8570 := hb (x 7 8)
    clear * - r8556 e8557 e8558 e8559 e8560 e8561 e8562 b8563 b8564 b8565 b8566 b8567 b8568 b8569 b8570 d8523 d8539 g7
    omega
  have d8571 : (x 5 1 && x 5 10).toNat = 0 := by
    have r8572 := hand2 (x 5 1) (x 5 10)
    have b8573 := hb (x 5 10)
    have b8574 := hb (x 5 1 && x 5 10)
    clear * - r8572 b8573 b8574 d8555
    omega
  have d8575 : (x 4 11).toNat = 0 := by
    have r8576 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8577 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8578 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8579 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8580 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8581 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8582 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8583 := hb (x 0 7)
    have b8584 := hb (x 1 6)
    have b8585 := hb (x 2 5)
    have b8586 := hb (x 3 4)
    have b8587 := hb (x 4 11)
    have b8588 := hb (x 5 10)
    have b8589 := hb (x 6 9)
    have b8590 := hb (x 7 8)
    clear * - r8576 e8577 e8578 e8579 e8580 e8581 e8582 b8583 b8584 b8585 b8586 b8587 b8588 b8589 b8590 d8523 d8539 d8555 g7
    omega
  have d8591 : (x 4 1 && x 4 11).toNat = 0 := by
    have r8592 := hand2 (x 4 1) (x 4 11)
    have b8593 := hb (x 4 11)
    have b8594 := hb (x 4 1 && x 4 11)
    clear * - r8592 b8593 b8594 d8575
    omega
  have d8595 : (x 4 2 && x 4 11).toNat = 0 := by
    have r8596 := hand2 (x 4 2) (x 4 11)
    have b8597 := hb (x 4 11)
    have b8598 := hb (x 4 2 && x 4 11)
    clear * - r8596 b8597 b8598 d8575
    omega
  have d8599 : (x 3 4).toNat = 0 := by
    have r8600 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8601 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8602 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8603 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8604 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8605 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8606 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8607 := hb (x 0 7)
    have b8608 := hb (x 1 6)
    have b8609 := hb (x 2 5)
    have b8610 := hb (x 3 4)
    have b8611 := hb (x 4 11)
    have b8612 := hb (x 5 10)
    have b8613 := hb (x 6 9)
    have b8614 := hb (x 7 8)
    clear * - r8600 e8601 e8602 e8603 e8604 e8605 e8606 b8607 b8608 b8609 b8610 b8611 b8612 b8613 b8614 d8523 d8539 d8555 d8575 g7
    omega
  cases h8615 : x 0 1
  · have f8616 : (x 0 1).toNat = 0 := by rw [h8615]; rfl
    have d8617 : (x 0 1 && x 0 14).toNat = 0 := by
      have r8618 := hand1 (x 0 1) (x 0 14)
      have b8619 := hb (x 0 1)
      have b8620 := hb (x 0 1 && x 0 14)
      clear * - r8618 b8619 b8620 f8616
      omega
    have d8621 : (x (-1) 2).toNat = 1 := by
      have r8622 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8623 := hb (x (-1) 2)
      have b8624 := hb (x 1 13)
      have b8625 := hb (x 0 1 && x 0 14)
      clear * - r8622 b8623 b8624 b8625 g11 d8617
      omega
    have d8626 : (x (-1) 14).toNat = 1 := by
      have r8627 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
      have b8628 := hb (x (-1) 2)
      have b8629 := hb (x (-1) 14)
      clear * - r8627 b8628 b8629 d8621
      omega
    have d8630 : (x (-2) 1).toNat = 0 := by
      have r8631 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8632 := hb (x (-2) 1)
      have b8633 := hb (x (-1) 14)
      clear * - r8631 b8632 b8633 d8626
      omega
    have d8634 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r8635 := hand1 (x (-2) 1) (x (-2) 14)
      have b8636 := hb (x (-2) 1)
      have b8637 := hb (x (-2) 1 && x (-2) 14)
      clear * - r8635 b8636 b8637 d8630
      omega
    have d8638 : (x (-2) 13).toNat = 0 := by
      have r8639 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b8640 := hb (x (-2) 1)
      have b8641 := hb (x (-2) 13)
      clear * - r8639 b8640 b8641 d8630
      omega
    have d8642 : (x (-3) 2).toNat = 1 := by
      have r8643 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8644 := hb (x (-3) 2)
      have b8645 := hb (x (-1) 13)
      have b8646 := hb (x (-2) 1 && x (-2) 14)
      clear * - r8643 b8644 b8645 b8646 g4 d8634
      omega
    have d8647 : (x (-3) 14).toNat = 1 := by
      have r8648 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b8649 := hb (x (-3) 2)
      have b8650 := hb (x (-3) 14)
      clear * - r8648 b8649 b8650 d8642
      omega
    have d8651 : (x (-4) 1).toNat = 0 := by
      have r8652 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8653 := hb (x (-4) 1)
      have b8654 := hb (x (-3) 14)
      clear * - r8652 b8653 b8654 d8647
      omega
    have d8655 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
      have r8656 := hand1 (x (-4) 1) (x (-4) 14)
      have b8657 := hb (x (-4) 1)
      have b8658 := hb (x (-4) 1 && x (-4) 14)
      clear * - r8656 b8657 b8658 d8651
      omega
    have d8659 : (x (-4) 13).toNat = 0 := by
      have r8660 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b8661 := hb (x (-4) 1)
      have b8662 := hb (x (-4) 13)
      clear * - r8660 b8661 b8662 d8651
      omega
    have d8663 : (x (-4) 2).toNat = 1 := by
      have r8664 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8665 := hb (x (-4) 2)
      have b8666 := hb (x (-2) 13)
      have b8667 := hb (x (-3) 1 && x (-3) 14)
      clear * - r8664 b8665 b8666 b8667 d8638 g31
      omega
    have d8668 : (x (-5) 2).toNat = 1 := by
      have r8669 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8670 := hb (x (-5) 2)
      have b8671 := hb (x (-3) 13)
      have b8672 := hb (x (-4) 1 && x (-4) 14)
      clear * - r8669 b8670 b8671 b8672 g1 d8655
      omega
    have d8673 : (x 1 12).toNat = 0 := by
      have r8674 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8675 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e8676 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b8677 := hb (x (-2) 3)
      have b8678 := hb (x (-1) 2)
      have b8679 := hb (x 0 13)
      have b8680 := hb (x 1 12)
      clear * - r8674 e8675 e8676 b8677 b8678 b8679 b8680 g8 d8621
      omega
    have d8681 : (x 1 1 && x 1 12).toNat = 0 := by
      have r8682 := hand2 (x 1 1) (x 1 12)
      have b8683 := hb (x 1 12)
      have b8684 := hb (x 1 1 && x 1 12)
      clear * - r8682 b8683 b8684 d8673
      omega
    have d8685 : (x (-2) 3).toNat = 0 := by
      have r8686 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8687 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e8688 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b8689 := hb (x (-2) 3)
      have b8690 := hb (x (-1) 2)
      have b8691 := hb (x 0 13)
      have b8692 := hb (x 1 12)
      clear * - r8686 e8687 e8688 b8689 b8690 b8691 b8692 d8673 g8 d8621
      omega
    have d8693 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
      have r8694 := hand1 (x (-2) 3) (x (-2) 14)
      have b8695 := hb (x (-2) 3)
      have b8696 := hb (x (-2) 3 && x (-2) 14)
      clear * - r8694 b8695 b8696 d8685
      omega
    have d8697 : (x (-1) 12).toNat = 0 := by
      have r8698 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8699 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e8700 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b8701 := hb (x (-4) 3)
      have b8702 := hb (x (-3) 2)
      have b8703 := hb (x (-2) 13)
      have b8704 := hb (x (-1) 12)
      clear * - r8698 e8699 e8700 b8701 b8702 b8703 b8704 d8638 d8642
      omega
    have d8705 : (x (-1) 4).toNat = 0 := by
      have r8706 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b8707 := hb (x (-1) 4)
      have b8708 := hb (x (-1) 12)
      clear * - r8706 b8707 b8708 d8697
      omega
    have d8709 : (x (-2) 12).toNat = 0 := by
      have r8710 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8711 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e8712 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b8713 := hb (x (-5) 3)
      have b8714 := hb (x (-4) 2)
      have b8715 := hb (x (-3) 13)
      have b8716 := hb (x (-2) 12)
      clear * - r8710 e8711 e8712 b8713 b8714 b8715 b8716 g1 d8663
      omega
    have d8717 : (x (-2) 4).toNat = 0 := by
      have r8718 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have b8719 := hb (x (-2) 4)
      have b8720 := hb (x (-2) 12)
      clear * - r8718 b8719 b8720 d8709
      omega
    have d8721 : (x (-3) 12).toNat = 0 := by
      have r8722 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8723 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e8724 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b8725 := hb (x (-6) 3)
      have b8726 := hb (x (-5) 2)
      have b8727 := hb (x (-4) 13)
      have b8728 := hb (x (-3) 12)
      clear * - r8722 e8723 e8724 b8725 b8726 b8727 b8728 d8659 d8668
      omega
    have d8729 : (x (-3) 4).toNat = 0 := by
      have r8730 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b8731 := hb (x (-3) 4)
      have b8732 := hb (x (-3) 12)
      clear * - r8730 b8731 b8732 d8721
      omega
    have d8733 : (x 3 11).toNat = 1 := by
      have r8734 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8735 := hb (x (-1) 4)
      have b8736 := hb (x 3 11)
      have b8737 := hb (x 2 1 && x 2 12)
      have b8738 := hb (x 1 2 && x 1 13)
      have b8739 := hb (x 0 3 && x 0 14)
      clear * - r8734 b8735 b8736 b8737 b8738 b8739 g28 g29 g30 d8705
      omega
    have d8740 : (x 3 3).toNat = 1 := by
      have r8741 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b8742 := hb (x 3 3)
      have b8743 := hb (x 3 11)
      clear * - r8741 b8742 b8743 d8733
      omega
    have d8744 : (x 6 12).toNat = 0 := by
      have r8745 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8746 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e8747 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b8748 := hb (x 3 3)
      have b8749 := hb (x 4 2)
      have b8750 := hb (x 5 13)
      have b8751 := hb (x 6 12)
      clear * - r8745 e8746 e8747 b8748 b8749 b8750 b8751 d8740
      omega
    have d8752 : (x 5 13).toNat = 0 := by
      have r8753 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8754 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e8755 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b8756 := hb (x 3 3)
      have b8757 := hb (x 4 2)
      have b8758 := hb (x 5 13)
      have b8759 := hb (x 6 12)
      clear * - r8753 e8754 e8755 b8756 b8757 b8758 b8759 d8744 d8740
      omega
    have d8760 : (x 2 11).toNat = 1 := by
      have r8761 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8762 := hb (x (-2) 4)
      have b8763 := hb (x 2 11)
      have b8764 := hb (x 1 1 && x 1 12)
      have b8765 := hb (x 0 2 && x 0 13)
      have b8766 := hb (x (-1) 3 && x (-1) 14)
      clear * - r8761 b8762 b8763 b8764 b8765 b8766 d8681 g26 g27 d8717
      omega
    have d8767 : (x 2 3).toNat = 1 := by
      have r8768 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have b8769 := hb (x 2 3)
      have b8770 := hb (x 2 11)
      clear * - r8768 b8769 b8770 d8760
      omega
    have d8771 : (x 5 12).toNat = 0 := by
      have r8772 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8773 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e8774 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b8775 := hb (x 2 3)
      have b8776 := hb (x 3 2)
      have b8777 := hb (x 4 13)
      have b8778 := hb (x 5 12)
      clear * - r8772 e8773 e8774 b8775 b8776 b8777 b8778 d8767
      omega
    have d8779 : (x 4 13).toNat = 0 := by
      have r8780 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8781 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e8782 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b8783 := hb (x 2 3)
      have b8784 := hb (x 3 2)
      have b8785 := hb (x 4 13)
      have b8786 := hb (x 5 12)
      clear * - r8780 e8781 e8782 b8783 b8784 b8785 b8786 d8771 d8767
      omega
    have d8787 : (x 3 2).toNat = 0 := by
      have r8788 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8789 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e8790 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b8791 := hb (x 2 3)
      have b8792 := hb (x 3 2)
      have b8793 := hb (x 4 13)
      have b8794 := hb (x 5 12)
      clear * - r8788 e8789 e8790 b8791 b8792 b8793 b8794 d8771 d8779 d8767
      omega
    have d8795 : (x 4 1 && x 4 14).toNat = 1 := by
      have r8796 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8797 := hb (x 3 2)
      have b8798 := hb (x 5 13)
      have b8799 := hb (x 4 1 && x 4 14)
      clear * - r8796 b8797 b8798 b8799 d8752 d8787
      omega
    have d8800 : (x 4 14).toNat = 1 := by
      have r8801 := hand2 (x 4 1) (x 4 14)
      have b8802 := hb (x 4 14)
      have b8803 := hb (x 4 1 && x 4 14)
      clear * - r8801 b8802 b8803 d8795
      omega
    have d8804 : (x 3 1).toNat = 0 := by
      have r8805 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8806 := hb (x 3 1)
      have b8807 := hb (x 4 14)
      clear * - r8805 b8806 b8807 d8800
      omega
    have d8808 : (x 3 1 && x 3 14).toNat = 0 := by
      have r8809 := hand1 (x 3 1) (x 3 14)
      have b8810 := hb (x 3 1)
      have b8811 := hb (x 3 1 && x 3 14)
      clear * - r8809 b8810 b8811 d8804
      omega
    have d8812 : (x 2 2).toNat = 1 := by
      have r8813 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8814 := hb (x 2 2)
      have b8815 := hb (x 4 13)
      have b8816 := hb (x 3 1 && x 3 14)
      clear * - r8813 b8814 b8815 b8816 d8779 d8808
      omega
    have d8817 : (x 4 12).toNat = 0 := by
      have r8818 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8819 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e8820 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b8821 := hb (x 1 3)
      have b8822 := hb (x 2 2)
      have b8823 := hb (x 3 13)
      have b8824 := hb (x 4 12)
      clear * - r8818 e8819 e8820 b8821 b8822 b8823 b8824 d8812
      omega
    have d8825 : (x 3 13).toNat = 0 := by
      have r8826 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8827 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e8828 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b8829 := hb (x 1 3)
      have b8830 := hb (x 2 2)
      have b8831 := hb (x 3 13)
      have b8832 := hb (x 4 12)
      clear * - r8826 e8827 e8828 b8829 b8830 b8831 b8832 d8817 d8812
      omega
    have d8833 : (x 1 3).toNat = 0 := by
      have r8834 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8835 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e8836 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b8837 := hb (x 1 3)
      have b8838 := hb (x 2 2)
      have b8839 := hb (x 3 13)
      have b8840 := hb (x 4 12)
      clear * - r8834 e8835 e8836 b8837 b8838 b8839 b8840 d8817 d8825 d8812
      omega
    have d8841 : (x 1 11).toNat = 0 := by
      have r8842 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b8843 := hb (x 1 3)
      have b8844 := hb (x 1 11)
      clear * - r8842 b8843 b8844 d8833
      omega
    have r8845 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8846 := hb (x (-3) 4)
    have b8847 := hb (x 1 11)
    have b8848 := hb (x 0 1 && x 0 12)
    have b8849 := hb (x (-1) 2 && x (-1) 13)
    have b8850 := hb (x (-2) 3 && x (-2) 14)
    linarith only [r8845, b8846, b8847, b8848, b8849, b8850, d8841, g24, g25, d8693, d8729]
  · have f8851 : (x 0 1).toNat = 1 := by rw [h8615]; rfl
    have d8852 : (x 1 14).toNat = 0 := by
      have r8853 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b8854 := hb (x 0 1)
      have b8855 := hb (x 1 14)
      clear * - r8853 b8854 b8855 f8851
      omega
    have d8856 : (x 1 4 && x 1 14).toNat = 0 := by
      have r8857 := hand2 (x 1 4) (x 1 14)
      have b8858 := hb (x 1 14)
      have b8859 := hb (x 1 4 && x 1 14)
      clear * - r8857 b8858 b8859 d8852
      omega
    have d8860 : (x 1 2).toNat = 0 := by
      have r8861 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
      have b8862 := hb (x 1 2)
      have b8863 := hb (x 1 14)
      clear * - r8861 b8862 b8863 d8852
      omega
    have d8864 : (x 1 10).toNat = 0 := by
      have r8865 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b8866 := hb (x 1 2)
      have b8867 := hb (x 1 10)
      clear * - r8865 b8866 b8867 d8860
      omega
    have d8868 : (x 1 1 && x 1 10).toNat = 0 := by
      have r8869 := hand2 (x 1 1) (x 1 10)
      have b8870 := hb (x 1 10)
      have b8871 := hb (x 1 1 && x 1 10)
      clear * - r8869 b8870 b8871 d8864
      omega
    have r8872 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8873 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8874 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8875 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e8876 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e8877 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e8878 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e8879 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e8880 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have r8881 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8882 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e8883 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e8884 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e8885 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e8886 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e8887 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have r8888 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8889 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e8890 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e8891 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e8892 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e8893 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e8894 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have r8895 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8896 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e8897 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e8898 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e8899 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e8900 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e8901 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have r8902 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8903 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e8904 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have r8905 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8906 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e8907 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have r8908 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8909 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e8910 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have r8911 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8912 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e8913 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have r8914 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8915 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8916 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8917 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
    have e8918 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
    have r8919 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8920 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8921 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8922 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8923 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8924 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8925 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8926 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
    have r8927 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have r8928 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have r8929 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have r8930 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
    have r8931 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have r8932 := hand1 (x 8 2) (x 8 6)
    have r8933 := hand2 (x 7 3) (x 7 7)
    have r8934 := hand1 (x 6 4) (x 6 8)
    have r8935 := hand1 (x 5 5) (x 5 9)
    have r8936 := hand1 (x 4 6) (x 4 10)
    have r8937 := hand1 (x 3 7) (x 3 11)
    have r8938 := hand1 (x (-2) 4) (x (-2) 13)
    have r8939 := hand1 (x 3 3) (x 3 12)
    have r8940 := hand2 (x 3 3) (x 3 12)
    have r8941 := hand2 (x 13 1) (x 13 10)
    have r8942 := hand2 (x 12 2) (x 12 11)
    have r8943 := hand1 (x 11 3) (x 11 12)
    have r8944 := hand1 (x 10 4) (x 10 13)
    have r8945 := hand1 (x 9 5) (x 9 14)
    have r8946 := hand1 (x 3 1) (x 3 11)
    have r8947 := hand2 (x 3 1) (x 3 11)
    have r8948 := hand1 (x 3 2) (x 3 12)
    have r8949 := hand2 (x 2 3) (x 2 13)
    have r8950 := hand2 (x 6 1) (x 6 12)
    have r8951 := hand2 (x 5 2) (x 5 13)
    have r8952 := hand2 (x 4 3) (x 4 14)
    have r8953 := hand1 (x 13 1) (x 13 14)
    have b9022 := hb (x 14 1)
    linarith only [r8872, r8873, r8874, e8875, e8876, e8877, e8878, e8879, e8880, r8881, e8882, e8883, e8884, e8885, e8886, e8887, r8888, e8889, e8890, e8891, e8892, e8893, e8894, r8895, e8896, e8897, e8898, e8899, e8900, e8901, r8902, e8903, e8904, r8905, e8906, e8907, r8908, e8909, e8910, r8911, e8912, e8913, r8914, r8915, r8916, e8917, e8918, r8919, r8920, r8921, r8922, r8923, r8924, r8925, r8926, r8927, r8928, r8929, r8930, r8931, r8932, r8933, r8934, r8935, r8936, r8937, r8938, r8939, r8940, r8941, r8942, r8943, r8944, r8945, r8946, r8947, r8948, r8949, r8950, r8951, r8952, r8953, b9022, g0, g2, g3, g5, g6, g9, d8860, g10, g11, d8852, g12, g13, d8599, d8575, d8555, d8539, d8523, g14, g15, d8868, g16, g17, g18, d8571, d8595, g19, g20, g21, g22, g23, d8591, d8856]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a01 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 5).toNat = 0)
    (g1 : (x (-3) 13).toNat = 0)
    (g2 : (x (-1) 5).toNat = 0)
    (g3 : (x (-1) 11).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 3).toNat = 0)
    (g6 : (x 0 5).toNat = 0)
    (g7 : (x 0 7).toNat = 1)
    (g8 : (x 0 13).toNat = 0)
    (g9 : (x 0 14).toNat = 1)
    (g10 : (x 1 5).toNat = 0)
    (g11 : (x 1 13).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 12).toNat = 0)
    (g14 : (x 2 8 && x 2 12).toNat = 0)
    (g15 : (x 1 9 && x 1 13).toNat = 0)
    (g16 : (x 0 2 && x 0 11).toNat = 0)
    (g17 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g18 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g19 : (x 2 4 && x 2 13).toNat = 0)
    (g20 : (x 1 5 && x 1 14).toNat = 0)
    (g21 : (x 2 2 && x 2 12).toNat = 0)
    (g22 : (x 1 3 && x 1 13).toNat = 0)
    (g23 : (x 0 4 && x 0 14).toNat = 0)
    (g24 : (x 0 1 && x 0 12).toNat = 0)
    (g25 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g26 : (x 0 2 && x 0 13).toNat = 0)
    (g27 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g28 : (x 2 1 && x 2 12).toNat = 0)
    (g29 : (x 1 2 && x 1 13).toNat = 0)
    (g30 : (x 0 3 && x 0 14).toNat = 0)
    (g31 : (x (-3) 1 && x (-3) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a01_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31
