import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001101

Topic: combinatorics   Node: c7cfe9d8993a

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 10 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001101_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 13).toNat = 0)
    (g1 : (x 0 12).toNat = 1)
    (g2 : (x 2 4).toNat = 0)
    (g3 : (x 3 2).toNat = 0)
    (g4 : (x 3 4).toNat = 0)
    (g5 : (x 2 1 && x 2 12).toNat = 0)
    (g6 : (x 1 2 && x 1 13).toNat = 0)
    (g7 : (x 0 3 && x 0 14).toNat = 0)
    (g8 : (x 3 3 && x 3 14).toNat = 0)
    (g9 : (x (-2) 1 && x (-2) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d40494 : (x (-1) 13).toNat = 0 := by
    have r40495 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
    have e40496 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e40497 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b40498 := hb (x (-3) 3)
    have b40499 := hb (x (-2) 2)
    have b40500 := hb (x (-1) 13)
    have b40501 := hb (x 0 12)
    clear * - r40495 e40496 e40497 b40498 b40499 b40500 b40501 g1
    omega
  have d40502 : (x (-3) 2).toNat = 1 := by
    have r40503 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
    have b40504 := hb (x (-3) 2)
    have b40505 := hb (x (-1) 13)
    have b40506 := hb (x (-2) 1 && x (-2) 14)
    clear * - r40503 b40504 b40505 b40506 d40494 g9
    omega
  have d40507 : (x (-1) 12).toNat = 0 := by
    have r40508 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
    have e40509 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e40510 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b40511 := hb (x (-4) 3)
    have b40512 := hb (x (-3) 2)
    have b40513 := hb (x (-2) 13)
    have b40514 := hb (x (-1) 12)
    clear * - r40508 e40509 e40510 b40511 b40512 b40513 b40514 g0 d40502
    omega
  have d40515 : (x (-1) 4).toNat = 0 := by
    have r40516 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b40517 := hb (x (-1) 4)
    have b40518 := hb (x (-1) 12)
    clear * - r40516 b40517 b40518 d40507
    omega
  have d40519 : (x 3 11).toNat = 1 := by
    have r40520 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
    have b40521 := hb (x (-1) 4)
    have b40522 := hb (x 3 11)
    have b40523 := hb (x 2 1 && x 2 12)
    have b40524 := hb (x 1 2 && x 1 13)
    have b40525 := hb (x 0 3 && x 0 14)
    clear * - r40520 b40521 b40522 b40523 b40524 b40525 g5 g6 g7 d40515
    omega
  have d40526 : (x 3 3).toNat = 1 := by
    have r40527 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b40528 := hb (x 3 3)
    have b40529 := hb (x 3 11)
    clear * - r40527 b40528 b40529 d40519
    omega
  have d40530 : (x 6 12).toNat = 0 := by
    have r40531 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e40532 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e40533 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b40534 := hb (x 3 3)
    have b40535 := hb (x 4 2)
    have b40536 := hb (x 5 13)
    have b40537 := hb (x 6 12)
    clear * - r40531 e40532 e40533 b40534 b40535 b40536 b40537 d40526
    omega
  have d40538 : (x 6 1 && x 6 12).toNat = 0 := by
    have r40539 := hand2 (x 6 1) (x 6 12)
    have b40540 := hb (x 6 12)
    have b40541 := hb (x 6 1 && x 6 12)
    clear * - r40539 b40540 b40541 d40530
    omega
  have d40542 : (x 6 4).toNat = 0 := by
    have r40543 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b40544 := hb (x 6 4)
    have b40545 := hb (x 6 12)
    clear * - r40543 b40544 b40545 d40530
    omega
  have d40546 : (x 5 13).toNat = 0 := by
    have r40547 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e40548 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e40549 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b40550 := hb (x 3 3)
    have b40551 := hb (x 4 2)
    have b40552 := hb (x 5 13)
    have b40553 := hb (x 6 12)
    clear * - r40547 e40548 e40549 b40550 b40551 b40552 b40553 d40530 d40526
    omega
  have d40554 : (x 5 2 && x 5 13).toNat = 0 := by
    have r40555 := hand2 (x 5 2) (x 5 13)
    have b40556 := hb (x 5 13)
    have b40557 := hb (x 5 2 && x 5 13)
    clear * - r40555 b40556 b40557 d40546
    omega
  have d40558 : (x 4 1 && x 4 14).toNat = 1 := by
    have r40559 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
    have b40560 := hb (x 3 2)
    have b40561 := hb (x 5 13)
    have b40562 := hb (x 4 1 && x 4 14)
    clear * - r40559 b40560 b40561 b40562 d40546 g3
    omega
  have d40563 : (x 4 1).toNat = 1 := by
    have r40564 := hand1 (x 4 1) (x 4 14)
    have b40565 := hb (x 4 1)
    have b40566 := hb (x 4 1 && x 4 14)
    clear * - r40564 b40565 b40566 d40558
    omega
  have d40567 : (x 5 14).toNat = 0 := by
    have r40568 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
    have b40569 := hb (x 4 1)
    have b40570 := hb (x 5 14)
    clear * - r40568 b40569 b40570 d40563
    omega
  have d40571 : (x 5 1 && x 5 14).toNat = 0 := by
    have r40572 := hand2 (x 5 1) (x 5 14)
    have b40573 := hb (x 5 14)
    have b40574 := hb (x 5 1 && x 5 14)
    clear * - r40572 b40573 b40574 d40567
    omega
  have d40575 : (x 5 2).toNat = 0 := by
    have r40576 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b40577 := hb (x 5 2)
    have b40578 := hb (x 5 14)
    clear * - r40576 b40577 b40578 d40567
    omega
  have d40579 : (x 4 2).toNat = 0 := by
    have r40580 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e40581 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e40582 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b40583 := hb (x 3 3)
    have b40584 := hb (x 4 2)
    have b40585 := hb (x 5 13)
    have b40586 := hb (x 6 12)
    clear * - r40580 e40581 e40582 b40583 b40584 b40585 b40586 d40530 d40546 d40526
    omega
  have d40587 : (x 4 2 && x 4 13).toNat = 0 := by
    have r40588 := hand1 (x 4 2) (x 4 13)
    have b40589 := hb (x 4 2)
    have b40590 := hb (x 4 2 && x 4 13)
    clear * - r40588 b40589 b40590 d40579
    omega
  have d40591 : (x 6 13).toNat = 1 := by
    have r40592 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
    have b40593 := hb (x 4 2)
    have b40594 := hb (x 6 13)
    have b40595 := hb (x 5 1 && x 5 14)
    clear * - r40592 b40593 b40594 b40595 d40571 d40579
    omega
  have d40596 : (x 6 1).toNat = 1 := by
    have r40597 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b40598 := hb (x 6 1)
    have b40599 := hb (x 6 13)
    clear * - r40597 b40598 b40599 d40591
    omega
  have d40600 : (x 7 14).toNat = 0 := by
    have r40601 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
    have b40602 := hb (x 6 1)
    have b40603 := hb (x 7 14)
    clear * - r40601 b40602 b40603 d40596
    omega
  have d40604 : (x 7 3 && x 7 14).toNat = 0 := by
    have r40605 := hand2 (x 7 3) (x 7 14)
    have b40606 := hb (x 7 14)
    have b40607 := hb (x 7 3 && x 7 14)
    clear * - r40605 b40606 b40607 d40600
    omega
  have d40608 : (x 7 2).toNat = 0 := by
    have r40609 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b40610 := hb (x 7 2)
    have b40611 := hb (x 7 14)
    clear * - r40609 b40610 b40611 d40600
    omega
  have d40612 : (x 7 12).toNat = 0 := by
    have r40613 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e40614 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e40615 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b40616 := hb (x 4 3)
    have b40617 := hb (x 5 2)
    have b40618 := hb (x 6 13)
    have b40619 := hb (x 7 12)
    clear * - r40613 e40614 e40615 b40616 b40617 b40618 b40619 d40591 d40575
    omega
  have d40620 : (x 7 4).toNat = 0 := by
    have r40621 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b40622 := hb (x 7 4)
    have b40623 := hb (x 7 12)
    clear * - r40621 b40622 b40623 d40612
    omega
  have d40624 : (x 4 3).toNat = 0 := by
    have r40625 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e40626 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e40627 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b40628 := hb (x 4 3)
    have b40629 := hb (x 5 2)
    have b40630 := hb (x 6 13)
    have b40631 := hb (x 7 12)
    clear * - r40625 e40626 e40627 b40628 b40629 b40630 b40631 d40612 d40591 d40575
    omega
  have d40632 : (x 4 3 && x 4 14).toNat = 0 := by
    have r40633 := hand1 (x 4 3) (x 4 14)
    have b40634 := hb (x 4 3)
    have b40635 := hb (x 4 3 && x 4 14)
    clear * - r40633 b40634 b40635 d40624
    omega
  have d40636 : (x 7 11).toNat = 1 := by
    have r40637 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
    have b40638 := hb (x 3 4)
    have b40639 := hb (x 7 11)
    have b40640 := hb (x 6 1 && x 6 12)
    have b40641 := hb (x 5 2 && x 5 13)
    have b40642 := hb (x 4 3 && x 4 14)
    clear * - r40637 b40638 b40639 b40640 b40641 b40642 d40538 d40554 d40632 g4
    omega
  have d40643 : (x 7 3).toNat = 1 := by
    have r40644 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b40645 := hb (x 7 3)
    have b40646 := hb (x 7 11)
    clear * - r40644 b40645 b40646 d40636
    omega
  have d40647 : (x 10 12).toNat = 0 := by
    have r40648 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e40649 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e40650 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b40651 := hb (x 7 3)
    have b40652 := hb (x 8 2)
    have b40653 := hb (x 9 13)
    have b40654 := hb (x 10 12)
    clear * - r40648 e40649 e40650 b40651 b40652 b40653 b40654 d40643
    omega
  have d40655 : (x 10 1 && x 10 12).toNat = 0 := by
    have r40656 := hand2 (x 10 1) (x 10 12)
    have b40657 := hb (x 10 12)
    have b40658 := hb (x 10 1 && x 10 12)
    clear * - r40656 b40657 b40658 d40647
    omega
  have d40659 : (x 10 4).toNat = 0 := by
    have r40660 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have b40661 := hb (x 10 4)
    have b40662 := hb (x 10 12)
    clear * - r40660 b40661 b40662 d40647
    omega
  have d40663 : (x 9 13).toNat = 0 := by
    have r40664 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e40665 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e40666 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b40667 := hb (x 7 3)
    have b40668 := hb (x 8 2)
    have b40669 := hb (x 9 13)
    have b40670 := hb (x 10 12)
    clear * - r40664 e40665 e40666 b40667 b40668 b40669 b40670 d40647 d40643
    omega
  have d40671 : (x 9 2 && x 9 13).toNat = 0 := by
    have r40672 := hand2 (x 9 2) (x 9 13)
    have b40673 := hb (x 9 13)
    have b40674 := hb (x 9 2 && x 9 13)
    clear * - r40672 b40673 b40674 d40663
    omega
  have d40675 : (x 8 1 && x 8 14).toNat = 1 := by
    have r40676 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
    have b40677 := hb (x 7 2)
    have b40678 := hb (x 9 13)
    have b40679 := hb (x 8 1 && x 8 14)
    clear * - r40676 b40677 b40678 b40679 d40663 d40608
    omega
  have d40680 : (x 8 14).toNat = 1 := by
    have r40681 := hand2 (x 8 1) (x 8 14)
    have b40682 := hb (x 8 14)
    have b40683 := hb (x 8 1 && x 8 14)
    clear * - r40681 b40682 b40683 d40675
    omega
  have d40684 : (x 7 1).toNat = 0 := by
    have r40685 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
    have b40686 := hb (x 7 1)
    have b40687 := hb (x 8 14)
    clear * - r40685 b40686 b40687 d40680
    omega
  have d40688 : (x 7 13).toNat = 0 := by
    have r40689 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b40690 := hb (x 7 1)
    have b40691 := hb (x 7 13)
    clear * - r40689 b40690 b40691 d40684
    omega
  have d40692 : (x 6 1 && x 6 14).toNat = 1 := by
    have r40693 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
    have b40694 := hb (x 5 2)
    have b40695 := hb (x 7 13)
    have b40696 := hb (x 6 1 && x 6 14)
    clear * - r40693 b40694 b40695 b40696 d40688 d40575
    omega
  have d40697 : (x 6 14).toNat = 1 := by
    have r40698 := hand2 (x 6 1) (x 6 14)
    have b40699 := hb (x 6 14)
    have b40700 := hb (x 6 1 && x 6 14)
    clear * - r40698 b40699 b40700 d40692
    omega
  have d40701 : (x 5 1).toNat = 0 := by
    have r40702 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
    have b40703 := hb (x 5 1)
    have b40704 := hb (x 6 14)
    clear * - r40702 b40703 b40704 d40697
    omega
  have d40705 : (x 5 1 && x 5 12).toNat = 0 := by
    have r40706 := hand1 (x 5 1) (x 5 12)
    have b40707 := hb (x 5 1)
    have b40708 := hb (x 5 1 && x 5 12)
    clear * - r40706 b40707 b40708 d40701
    omega
  have d40709 : (x 6 11).toNat = 1 := by
    have r40710 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
    have b40711 := hb (x 2 4)
    have b40712 := hb (x 6 11)
    have b40713 := hb (x 5 1 && x 5 12)
    have b40714 := hb (x 4 2 && x 4 13)
    have b40715 := hb (x 3 3 && x 3 14)
    clear * - r40710 b40711 b40712 b40713 b40714 b40715 d40705 d40587 g8 g2
    omega
  have d40716 : (x 6 3).toNat = 1 := by
    have r40717 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
    have b40718 := hb (x 6 3)
    have b40719 := hb (x 6 11)
    clear * - r40717 b40718 b40719 d40709
    omega
  have d40720 : (x 9 12).toNat = 0 := by
    have r40721 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e40722 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e40723 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b40724 := hb (x 6 3)
    have b40725 := hb (x 7 2)
    have b40726 := hb (x 8 13)
    have b40727 := hb (x 9 12)
    clear * - r40721 e40722 e40723 b40724 b40725 b40726 b40727 d40608 d40716
    omega
  have d40728 : (x 9 1 && x 9 12).toNat = 0 := by
    have r40729 := hand2 (x 9 1) (x 9 12)
    have b40730 := hb (x 9 12)
    have b40731 := hb (x 9 1 && x 9 12)
    clear * - r40729 b40730 b40731 d40720
    omega
  have d40732 : (x 8 13).toNat = 0 := by
    have r40733 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e40734 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e40735 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b40736 := hb (x 6 3)
    have b40737 := hb (x 7 2)
    have b40738 := hb (x 8 13)
    have b40739 := hb (x 9 12)
    clear * - r40733 e40734 e40735 b40736 b40737 b40738 b40739 d40720 d40608 d40716
    omega
  have d40740 : (x 8 2 && x 8 13).toNat = 0 := by
    have r40741 := hand2 (x 8 2) (x 8 13)
    have b40742 := hb (x 8 13)
    have b40743 := hb (x 8 2 && x 8 13)
    clear * - r40741 b40742 b40743 d40732
    omega
  have d40744 : (x 10 11).toNat = 1 := by
    have r40745 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := hcov11 10
    have b40746 := hb (x 6 4)
    have b40747 := hb (x 10 11)
    have b40748 := hb (x 9 1 && x 9 12)
    have b40749 := hb (x 8 2 && x 8 13)
    have b40750 := hb (x 7 3 && x 7 14)
    clear * - r40745 b40746 b40747 b40748 b40749 b40750 d40728 d40740 d40604 d40542
    omega
  have d40751 : (x 10 3).toNat = 1 := by
    have r40752 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
    have b40753 := hb (x 10 3)
    have b40754 := hb (x 10 11)
    clear * - r40752 b40753 b40754 d40744
    omega
  have d40755 : (x 13 12).toNat = 0 := by
    have r40756 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e40757 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e40758 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b40759 := hb (x 10 3)
    have b40760 := hb (x 11 2)
    have b40761 := hb (x 12 13)
    have b40762 := hb (x 13 12)
    clear * - r40756 e40757 e40758 b40759 b40760 b40761 b40762 d40751
    omega
  have d40763 : (x 13 1 && x 13 12).toNat = 0 := by
    have r40764 := hand2 (x 13 1) (x 13 12)
    have b40765 := hb (x 13 12)
    have b40766 := hb (x 13 1 && x 13 12)
    clear * - r40764 b40765 b40766 d40755
    omega
  have d40767 : (x 12 13).toNat = 0 := by
    have r40768 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e40769 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e40770 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b40771 := hb (x 10 3)
    have b40772 := hb (x 11 2)
    have b40773 := hb (x 12 13)
    have b40774 := hb (x 13 12)
    clear * - r40768 e40769 e40770 b40771 b40772 b40773 b40774 d40755 d40751
    omega
  have d40775 : (x 12 2 && x 12 13).toNat = 0 := by
    have r40776 := hand2 (x 12 2) (x 12 13)
    have b40777 := hb (x 12 13)
    have b40778 := hb (x 12 2 && x 12 13)
    clear * - r40776 b40777 b40778 d40767
    omega
  have d40779 : (x 11 2).toNat = 0 := by
    have r40780 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e40781 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e40782 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b40783 := hb (x 10 3)
    have b40784 := hb (x 11 2)
    have b40785 := hb (x 12 13)
    have b40786 := hb (x 13 12)
    clear * - r40780 e40781 e40782 b40783 b40784 b40785 b40786 d40755 d40767 d40751
    omega
  have d40787 : (x 8 1).toNat = 1 := by
    have r40788 := hand1 (x 8 1) (x 8 14)
    have b40789 := hb (x 8 1)
    have b40790 := hb (x 8 1 && x 8 14)
    clear * - r40788 b40789 b40790 d40675
    omega
  have d40791 : (x 9 14).toNat = 0 := by
    have r40792 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
    have b40793 := hb (x 8 1)
    have b40794 := hb (x 9 14)
    clear * - r40792 b40793 b40794 d40787
    omega
  have d40795 : (x 9 1 && x 9 14).toNat = 0 := by
    have r40796 := hand2 (x 9 1) (x 9 14)
    have b40797 := hb (x 9 14)
    have b40798 := hb (x 9 1 && x 9 14)
    clear * - r40796 b40797 b40798 d40791
    omega
  have d40799 : (x 9 2).toNat = 0 := by
    have r40800 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b40801 := hb (x 9 2)
    have b40802 := hb (x 9 14)
    clear * - r40800 b40801 b40802 d40791
    omega
  have d40803 : (x 8 2).toNat = 0 := by
    have r40804 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e40805 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e40806 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b40807 := hb (x 7 3)
    have b40808 := hb (x 8 2)
    have b40809 := hb (x 9 13)
    have b40810 := hb (x 10 12)
    clear * - r40804 e40805 e40806 b40807 b40808 b40809 b40810 d40647 d40663 d40643
    omega
  have d40811 : (x 10 13).toNat = 1 := by
    have r40812 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
    have b40813 := hb (x 8 2)
    have b40814 := hb (x 10 13)
    have b40815 := hb (x 9 1 && x 9 14)
    clear * - r40812 b40813 b40814 b40815 d40795 d40803
    omega
  have d40816 : (x 10 1).toNat = 1 := by
    have r40817 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b40818 := hb (x 10 1)
    have b40819 := hb (x 10 13)
    clear * - r40817 b40818 b40819 d40811
    omega
  have d40820 : (x 11 14).toNat = 0 := by
    have r40821 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
    have b40822 := hb (x 10 1)
    have b40823 := hb (x 11 14)
    clear * - r40821 b40822 b40823 d40816
    omega
  have d40824 : (x 11 1 && x 11 14).toNat = 0 := by
    have r40825 := hand2 (x 11 1) (x 11 14)
    have b40826 := hb (x 11 14)
    have b40827 := hb (x 11 1 && x 11 14)
    clear * - r40825 b40826 b40827 d40820
    omega
  have d40828 : (x 10 2).toNat = 1 := by
    have r40829 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
    have b40830 := hb (x 10 2)
    have b40831 := hb (x 12 13)
    have b40832 := hb (x 11 1 && x 11 14)
    clear * - r40829 b40830 b40831 b40832 d40767 d40824
    omega
  have d40833 : (x 12 12).toNat = 0 := by
    have r40834 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e40835 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e40836 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b40837 := hb (x 9 3)
    have b40838 := hb (x 10 2)
    have b40839 := hb (x 11 13)
    have b40840 := hb (x 12 12)
    clear * - r40834 e40835 e40836 b40837 b40838 b40839 b40840 d40828
    omega
  have d40841 : (x 12 4).toNat = 0 := by
    have r40842 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b40843 := hb (x 12 4)
    have b40844 := hb (x 12 12)
    clear * - r40842 b40843 b40844 d40833
    omega
  have d40845 : (x 12 4 && x 12 14).toNat = 0 := by
    have r40846 := hand1 (x 12 4) (x 12 14)
    have b40847 := hb (x 12 4)
    have b40848 := hb (x 12 4 && x 12 14)
    clear * - r40846 b40847 b40848 d40841
    omega
  have d40849 : (x 11 13).toNat = 0 := by
    have r40850 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e40851 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e40852 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b40853 := hb (x 9 3)
    have b40854 := hb (x 10 2)
    have b40855 := hb (x 11 13)
    have b40856 := hb (x 12 12)
    clear * - r40850 e40851 e40852 b40853 b40854 b40855 b40856 d40833 d40828
    omega
  have d40857 : (x 11 5).toNat = 0 := by
    have r40858 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
    have b40859 := hb (x 11 5)
    have b40860 := hb (x 11 13)
    clear * - r40858 b40859 b40860 d40849
    omega
  have d40861 : (x 11 3 && x 11 14).toNat = 0 := by
    have r40862 := hand2 (x 11 3) (x 11 14)
    have b40863 := hb (x 11 14)
    have b40864 := hb (x 11 3 && x 11 14)
    clear * - r40862 b40863 b40864 d40820
    omega
  have d40865 : (x 14 11).toNat = 1 := by
    have r40866 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
    have b40867 := hb (x 10 4)
    have b40868 := hb (x 14 11)
    have b40869 := hb (x 13 1 && x 13 12)
    have b40870 := hb (x 12 2 && x 12 13)
    have b40871 := hb (x 11 3 && x 11 14)
    clear * - r40866 b40867 b40868 b40869 b40870 b40871 d40763 d40775 d40861 d40659
    omega
  have d40872 : (x 14 3).toNat = 1 := by
    have r40873 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
    have b40874 := hb (x 14 3)
    have b40875 := hb (x 14 11)
    clear * - r40873 b40874 b40875 d40865
    omega
  have d40876 : (x 17 12).toNat = 0 := by
    have r40877 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e40878 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e40879 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b40880 := hb (x 14 3)
    have b40881 := hb (x 15 2)
    have b40882 := hb (x 16 13)
    have b40883 := hb (x 17 12)
    clear * - r40877 e40878 e40879 b40880 b40881 b40882 b40883 d40872
    omega
  have d40884 : (x 16 13).toNat = 0 := by
    have r40885 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e40886 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e40887 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b40888 := hb (x 14 3)
    have b40889 := hb (x 15 2)
    have b40890 := hb (x 16 13)
    have b40891 := hb (x 17 12)
    clear * - r40885 e40886 e40887 b40888 b40889 b40890 b40891 d40876 d40872
    omega
  have d40892 : (x 15 2).toNat = 0 := by
    have r40893 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e40894 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e40895 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b40896 := hb (x 14 3)
    have b40897 := hb (x 15 2)
    have b40898 := hb (x 16 13)
    have b40899 := hb (x 17 12)
    clear * - r40893 e40894 e40895 b40896 b40897 b40898 b40899 d40876 d40884 d40872
    omega
  have d40900 : (x 11 12).toNat = 0 := by
    have r40901 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e40902 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e40903 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b40904 := hb (x 8 3)
    have b40905 := hb (x 9 2)
    have b40906 := hb (x 10 13)
    have b40907 := hb (x 11 12)
    clear * - r40901 e40902 e40903 b40904 b40905 b40906 b40907 d40811 d40799
    omega
  have d40908 : (x 11 4).toNat = 0 := by
    have r40909 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b40910 := hb (x 11 4)
    have b40911 := hb (x 11 12)
    clear * - r40909 b40910 b40911 d40900
    omega
  have d40912 : (x 8 3).toNat = 0 := by
    have r40913 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e40914 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e40915 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b40916 := hb (x 8 3)
    have b40917 := hb (x 9 2)
    have b40918 := hb (x 10 13)
    have b40919 := hb (x 11 12)
    clear * - r40913 e40914 e40915 b40916 b40917 b40918 b40919 d40900 d40811 d40799
    omega
  have d40920 : (x 8 3 && x 8 14).toNat = 0 := by
    have r40921 := hand1 (x 8 3) (x 8 14)
    have b40922 := hb (x 8 3)
    have b40923 := hb (x 8 3 && x 8 14)
    clear * - r40921 b40922 b40923 d40912
    omega
  have d40924 : (x 11 11).toNat = 1 := by
    have r40925 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
    have b40926 := hb (x 7 4)
    have b40927 := hb (x 11 11)
    have b40928 := hb (x 10 1 && x 10 12)
    have b40929 := hb (x 9 2 && x 9 13)
    have b40930 := hb (x 8 3 && x 8 14)
    clear * - r40925 b40926 b40927 b40928 b40929 b40930 d40655 d40671 d40920 d40620
    omega
  have d40931 : (x 11 3).toNat = 1 := by
    have r40932 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b40933 := hb (x 11 3)
    have b40934 := hb (x 11 11)
    clear * - r40932 b40933 b40934 d40924
    omega
  have d40935 : (x 14 12).toNat = 0 := by
    have r40936 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e40937 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e40938 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b40939 := hb (x 11 3)
    have b40940 := hb (x 12 2)
    have b40941 := hb (x 13 13)
    have b40942 := hb (x 14 12)
    clear * - r40936 e40937 e40938 b40939 b40940 b40941 b40942 d40931
    omega
  have d40943 : (x 14 1 && x 14 12).toNat = 0 := by
    have r40944 := hand2 (x 14 1) (x 14 12)
    have b40945 := hb (x 14 12)
    have b40946 := hb (x 14 1 && x 14 12)
    clear * - r40944 b40945 b40946 d40935
    omega
  have d40947 : (x 14 2 && x 14 12).toNat = 0 := by
    have r40948 := hand2 (x 14 2) (x 14 12)
    have b40949 := hb (x 14 12)
    have b40950 := hb (x 14 2 && x 14 12)
    clear * - r40948 b40949 b40950 d40935
    omega
  have d40951 : (x 13 13).toNat = 0 := by
    have r40952 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e40953 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e40954 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b40955 := hb (x 11 3)
    have b40956 := hb (x 12 2)
    have b40957 := hb (x 13 13)
    have b40958 := hb (x 14 12)
    clear * - r40952 e40953 e40954 b40955 b40956 b40957 b40958 d40935 d40931
    omega
  have d40959 : (x 13 2 && x 13 13).toNat = 0 := by
    have r40960 := hand2 (x 13 2) (x 13 13)
    have b40961 := hb (x 13 13)
    have b40962 := hb (x 13 2 && x 13 13)
    clear * - r40960 b40961 b40962 d40951
    omega
  have d40963 : (x 13 3 && x 13 13).toNat = 0 := by
    have r40964 := hand2 (x 13 3) (x 13 13)
    have b40965 := hb (x 13 13)
    have b40966 := hb (x 13 3 && x 13 13)
    clear * - r40964 b40965 b40966 d40951
    omega
  have d40967 : (x 12 1 && x 12 14).toNat = 1 := by
    have r40968 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
    have b40969 := hb (x 11 2)
    have b40970 := hb (x 13 13)
    have b40971 := hb (x 12 1 && x 12 14)
    clear * - r40968 b40969 b40970 b40971 d40951 d40779
    omega
  have d40972 : (x 12 1).toNat = 1 := by
    have r40973 := hand1 (x 12 1) (x 12 14)
    have b40974 := hb (x 12 1)
    have b40975 := hb (x 12 1 && x 12 14)
    clear * - r40973 b40974 b40975 d40967
    omega
  have d40976 : (x 13 14).toNat = 0 := by
    have r40977 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
    have b40978 := hb (x 12 1)
    have b40979 := hb (x 13 14)
    clear * - r40977 b40978 b40979 d40972
    omega
  have d40980 : (x 13 1 && x 13 14).toNat = 0 := by
    have r40981 := hand2 (x 13 1) (x 13 14)
    have b40982 := hb (x 13 14)
    have b40983 := hb (x 13 1 && x 13 14)
    clear * - r40981 b40982 b40983 d40976
    omega
  have d40984 : (x 13 2).toNat = 0 := by
    have r40985 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
    have b40986 := hb (x 13 2)
    have b40987 := hb (x 13 14)
    clear * - r40985 b40986 b40987 d40976
    omega
  have d40988 : (x 12 2).toNat = 0 := by
    have r40989 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e40990 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e40991 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b40992 := hb (x 11 3)
    have b40993 := hb (x 12 2)
    have b40994 := hb (x 13 13)
    have b40995 := hb (x 14 12)
    clear * - r40989 e40990 e40991 b40992 b40993 b40994 b40995 d40935 d40951 d40931
    omega
  have d40996 : (x 14 13).toNat = 1 := by
    have r40997 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
    have b40998 := hb (x 12 2)
    have b40999 := hb (x 14 13)
    have b41000 := hb (x 13 1 && x 13 14)
    clear * - r40997 b40998 b40999 b41000 d40980 d40988
    omega
  have d41001 : (x 15 12).toNat = 0 := by
    have r41002 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e41003 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e41004 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b41005 := hb (x 12 3)
    have b41006 := hb (x 13 2)
    have b41007 := hb (x 14 13)
    have b41008 := hb (x 15 12)
    clear * - r41002 e41003 e41004 b41005 b41006 b41007 b41008 d40996 d40984
    omega
  have d41009 : (x 12 3).toNat = 0 := by
    have r41010 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e41011 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e41012 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b41013 := hb (x 12 3)
    have b41014 := hb (x 13 2)
    have b41015 := hb (x 14 13)
    have b41016 := hb (x 15 12)
    clear * - r41010 e41011 e41012 b41013 b41014 b41015 b41016 d41001 d40996 d40984
    omega
  have d41017 : (x 12 3 && x 12 14).toNat = 0 := by
    have r41018 := hand1 (x 12 3) (x 12 14)
    have b41019 := hb (x 12 3)
    have b41020 := hb (x 12 3 && x 12 14)
    clear * - r41018 b41019 b41020 d41009
    omega
  have d41021 : (x 15 11).toNat = 1 := by
    have r41022 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
    have b41023 := hb (x 11 4)
    have b41024 := hb (x 15 11)
    have b41025 := hb (x 14 1 && x 14 12)
    have b41026 := hb (x 13 2 && x 13 13)
    have b41027 := hb (x 12 3 && x 12 14)
    clear * - r41022 b41023 b41024 b41025 b41026 b41027 d40943 d40959 d41017 d40908
    omega
  have d41028 : (x 15 3).toNat = 1 := by
    have r41029 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
    have b41030 := hb (x 15 3)
    have b41031 := hb (x 15 11)
    clear * - r41029 b41030 b41031 d41021
    omega
  have d41032 : (x 18 12).toNat = 0 := by
    have r41033 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e41034 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e41035 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b41036 := hb (x 15 3)
    have b41037 := hb (x 16 2)
    have b41038 := hb (x 17 13)
    have b41039 := hb (x 18 12)
    clear * - r41033 e41034 e41035 b41036 b41037 b41038 b41039 d41028
    omega
  have d41040 : (x 17 13).toNat = 0 := by
    have r41041 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e41042 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e41043 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b41044 := hb (x 15 3)
    have b41045 := hb (x 16 2)
    have b41046 := hb (x 17 13)
    have b41047 := hb (x 18 12)
    clear * - r41041 e41042 e41043 b41044 b41045 b41046 b41047 d41032 d41028
    omega
  have d41048 : (x 16 1 && x 16 14).toNat = 1 := by
    have r41049 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
    have b41050 := hb (x 15 2)
    have b41051 := hb (x 17 13)
    have b41052 := hb (x 16 1 && x 16 14)
    clear * - r41049 b41050 b41051 b41052 d41040 d40892
    omega
  have d41053 : (x 16 14).toNat = 1 := by
    have r41054 := hand2 (x 16 1) (x 16 14)
    have b41055 := hb (x 16 14)
    have b41056 := hb (x 16 1 && x 16 14)
    clear * - r41054 b41055 b41056 d41048
    omega
  have d41057 : (x 15 1).toNat = 0 := by
    have r41058 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
    have b41059 := hb (x 15 1)
    have b41060 := hb (x 16 14)
    clear * - r41058 b41059 b41060 d41053
    omega
  have d41061 : (x 15 1 && x 15 11).toNat = 0 := by
    have r41062 := hand1 (x 15 1) (x 15 11)
    have b41063 := hb (x 15 1)
    have b41064 := hb (x 15 1 && x 15 11)
    clear * - r41062 b41063 b41064 d41057
    omega
  have d41065 : (x 16 2).toNat = 0 := by
    have r41066 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e41067 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e41068 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b41069 := hb (x 15 3)
    have b41070 := hb (x 16 2)
    have b41071 := hb (x 17 13)
    have b41072 := hb (x 18 12)
    clear * - r41066 e41067 e41068 b41069 b41070 b41071 b41072 d41032 d41040 d41028
    omega
  have d41073 : (x 16 10).toNat = 0 := by
    have r41074 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
    have b41075 := hb (x 16 2)
    have b41076 := hb (x 16 10)
    clear * - r41074 b41075 b41076 d41065
    omega
  have r41077 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := hcov10 16
  have b41078 := hb (x 11 5)
  have b41079 := hb (x 16 10)
  have b41080 := hb (x 15 1 && x 15 11)
  have b41081 := hb (x 14 2 && x 14 12)
  have b41082 := hb (x 13 3 && x 13 13)
  have b41083 := hb (x 12 4 && x 12 14)
  linarith only [r41077, b41078, b41079, b41080, b41081, b41082, b41083, d41073, d41061, d40947, d40963, d40845, d40857]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 13).toNat = 0)
    (g1 : (x 0 12).toNat = 1)
    (g2 : (x 2 4).toNat = 0)
    (g3 : (x 3 2).toNat = 0)
    (g4 : (x 3 4).toNat = 0)
    (g5 : (x 2 1 && x 2 12).toNat = 0)
    (g6 : (x 1 2 && x 1 13).toNat = 0)
    (g7 : (x 0 3 && x 0 14).toNat = 0)
    (g8 : (x 3 3 && x 3 14).toNat = 0)
    (g9 : (x (-2) 1 && x (-2) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001101_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
