import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100000

Topic: combinatorics   Node: b5839c196084

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 8 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 4).toNat = 0)
    (g1 : (x 2 4).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 4).toNat = 0)
    (g4 : (x 2 1 && x 2 12).toNat = 0)
    (g5 : (x 1 2 && x 1 13).toNat = 0)
    (g6 : (x 0 3 && x 0 14).toNat = 0)
    (g7 : (x 3 3 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d30507 : (x 3 11).toNat = 1 := by
    have r30508 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
    have b30509 := hb (x (-1) 4)
    have b30510 := hb (x 3 11)
    have b30511 := hb (x 2 1 && x 2 12)
    have b30512 := hb (x 1 2 && x 1 13)
    have b30513 := hb (x 0 3 && x 0 14)
    clear * - r30508 b30509 b30510 b30511 b30512 b30513 g4 g5 g6 g0
    omega
  have d30514 : (x 3 3).toNat = 1 := by
    have r30515 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b30516 := hb (x 3 3)
    have b30517 := hb (x 3 11)
    clear * - r30515 b30516 b30517 d30507
    omega
  have d30518 : (x 6 12).toNat = 0 := by
    have r30519 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e30520 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e30521 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b30522 := hb (x 3 3)
    have b30523 := hb (x 4 2)
    have b30524 := hb (x 5 13)
    have b30525 := hb (x 6 12)
    clear * - r30519 e30520 e30521 b30522 b30523 b30524 b30525 d30514
    omega
  have d30526 : (x 6 1 && x 6 12).toNat = 0 := by
    have r30527 := hand2 (x 6 1) (x 6 12)
    have b30528 := hb (x 6 12)
    have b30529 := hb (x 6 1 && x 6 12)
    clear * - r30527 b30528 b30529 d30518
    omega
  have d30530 : (x 6 4).toNat = 0 := by
    have r30531 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b30532 := hb (x 6 4)
    have b30533 := hb (x 6 12)
    clear * - r30531 b30532 b30533 d30518
    omega
  have d30534 : (x 5 13).toNat = 0 := by
    have r30535 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e30536 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e30537 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b30538 := hb (x 3 3)
    have b30539 := hb (x 4 2)
    have b30540 := hb (x 5 13)
    have b30541 := hb (x 6 12)
    clear * - r30535 e30536 e30537 b30538 b30539 b30540 b30541 d30518 d30514
    omega
  have d30542 : (x 5 2 && x 5 13).toNat = 0 := by
    have r30543 := hand2 (x 5 2) (x 5 13)
    have b30544 := hb (x 5 13)
    have b30545 := hb (x 5 2 && x 5 13)
    clear * - r30543 b30544 b30545 d30534
    omega
  have d30546 : (x 4 1 && x 4 14).toNat = 1 := by
    have r30547 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
    have b30548 := hb (x 3 2)
    have b30549 := hb (x 5 13)
    have b30550 := hb (x 4 1 && x 4 14)
    clear * - r30547 b30548 b30549 b30550 d30534 g2
    omega
  have d30551 : (x 4 1).toNat = 1 := by
    have r30552 := hand1 (x 4 1) (x 4 14)
    have b30553 := hb (x 4 1)
    have b30554 := hb (x 4 1 && x 4 14)
    clear * - r30552 b30553 b30554 d30546
    omega
  have d30555 : (x 5 14).toNat = 0 := by
    have r30556 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
    have b30557 := hb (x 4 1)
    have b30558 := hb (x 5 14)
    clear * - r30556 b30557 b30558 d30551
    omega
  have d30559 : (x 5 1 && x 5 14).toNat = 0 := by
    have r30560 := hand2 (x 5 1) (x 5 14)
    have b30561 := hb (x 5 14)
    have b30562 := hb (x 5 1 && x 5 14)
    clear * - r30560 b30561 b30562 d30555
    omega
  have d30563 : (x 5 2).toNat = 0 := by
    have r30564 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b30565 := hb (x 5 2)
    have b30566 := hb (x 5 14)
    clear * - r30564 b30565 b30566 d30555
    omega
  have d30567 : (x 4 2).toNat = 0 := by
    have r30568 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e30569 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e30570 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b30571 := hb (x 3 3)
    have b30572 := hb (x 4 2)
    have b30573 := hb (x 5 13)
    have b30574 := hb (x 6 12)
    clear * - r30568 e30569 e30570 b30571 b30572 b30573 b30574 d30518 d30534 d30514
    omega
  have d30575 : (x 4 2 && x 4 13).toNat = 0 := by
    have r30576 := hand1 (x 4 2) (x 4 13)
    have b30577 := hb (x 4 2)
    have b30578 := hb (x 4 2 && x 4 13)
    clear * - r30576 b30577 b30578 d30567
    omega
  have d30579 : (x 6 13).toNat = 1 := by
    have r30580 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
    have b30581 := hb (x 4 2)
    have b30582 := hb (x 6 13)
    have b30583 := hb (x 5 1 && x 5 14)
    clear * - r30580 b30581 b30582 b30583 d30559 d30567
    omega
  have d30584 : (x 6 1).toNat = 1 := by
    have r30585 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b30586 := hb (x 6 1)
    have b30587 := hb (x 6 13)
    clear * - r30585 b30586 b30587 d30579
    omega
  have d30588 : (x 7 14).toNat = 0 := by
    have r30589 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
    have b30590 := hb (x 6 1)
    have b30591 := hb (x 7 14)
    clear * - r30589 b30590 b30591 d30584
    omega
  have d30592 : (x 7 3 && x 7 14).toNat = 0 := by
    have r30593 := hand2 (x 7 3) (x 7 14)
    have b30594 := hb (x 7 14)
    have b30595 := hb (x 7 3 && x 7 14)
    clear * - r30593 b30594 b30595 d30588
    omega
  have d30596 : (x 7 2).toNat = 0 := by
    have r30597 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b30598 := hb (x 7 2)
    have b30599 := hb (x 7 14)
    clear * - r30597 b30598 b30599 d30588
    omega
  have d30600 : (x 7 12).toNat = 0 := by
    have r30601 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e30602 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e30603 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b30604 := hb (x 4 3)
    have b30605 := hb (x 5 2)
    have b30606 := hb (x 6 13)
    have b30607 := hb (x 7 12)
    clear * - r30601 e30602 e30603 b30604 b30605 b30606 b30607 d30579 d30563
    omega
  have d30608 : (x 7 4).toNat = 0 := by
    have r30609 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b30610 := hb (x 7 4)
    have b30611 := hb (x 7 12)
    clear * - r30609 b30610 b30611 d30600
    omega
  have d30612 : (x 4 3).toNat = 0 := by
    have r30613 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e30614 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e30615 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b30616 := hb (x 4 3)
    have b30617 := hb (x 5 2)
    have b30618 := hb (x 6 13)
    have b30619 := hb (x 7 12)
    clear * - r30613 e30614 e30615 b30616 b30617 b30618 b30619 d30600 d30579 d30563
    omega
  have d30620 : (x 4 3 && x 4 14).toNat = 0 := by
    have r30621 := hand1 (x 4 3) (x 4 14)
    have b30622 := hb (x 4 3)
    have b30623 := hb (x 4 3 && x 4 14)
    clear * - r30621 b30622 b30623 d30612
    omega
  have d30624 : (x 7 11).toNat = 1 := by
    have r30625 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
    have b30626 := hb (x 3 4)
    have b30627 := hb (x 7 11)
    have b30628 := hb (x 6 1 && x 6 12)
    have b30629 := hb (x 5 2 && x 5 13)
    have b30630 := hb (x 4 3 && x 4 14)
    clear * - r30625 b30626 b30627 b30628 b30629 b30630 d30526 d30542 d30620 g3
    omega
  have d30631 : (x 7 3).toNat = 1 := by
    have r30632 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b30633 := hb (x 7 3)
    have b30634 := hb (x 7 11)
    clear * - r30632 b30633 b30634 d30624
    omega
  have d30635 : (x 10 12).toNat = 0 := by
    have r30636 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e30637 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e30638 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b30639 := hb (x 7 3)
    have b30640 := hb (x 8 2)
    have b30641 := hb (x 9 13)
    have b30642 := hb (x 10 12)
    clear * - r30636 e30637 e30638 b30639 b30640 b30641 b30642 d30631
    omega
  have d30643 : (x 10 1 && x 10 12).toNat = 0 := by
    have r30644 := hand2 (x 10 1) (x 10 12)
    have b30645 := hb (x 10 12)
    have b30646 := hb (x 10 1 && x 10 12)
    clear * - r30644 b30645 b30646 d30635
    omega
  have d30647 : (x 10 4).toNat = 0 := by
    have r30648 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have b30649 := hb (x 10 4)
    have b30650 := hb (x 10 12)
    clear * - r30648 b30649 b30650 d30635
    omega
  have d30651 : (x 9 13).toNat = 0 := by
    have r30652 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e30653 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e30654 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b30655 := hb (x 7 3)
    have b30656 := hb (x 8 2)
    have b30657 := hb (x 9 13)
    have b30658 := hb (x 10 12)
    clear * - r30652 e30653 e30654 b30655 b30656 b30657 b30658 d30635 d30631
    omega
  have d30659 : (x 9 2 && x 9 13).toNat = 0 := by
    have r30660 := hand2 (x 9 2) (x 9 13)
    have b30661 := hb (x 9 13)
    have b30662 := hb (x 9 2 && x 9 13)
    clear * - r30660 b30661 b30662 d30651
    omega
  have d30663 : (x 8 1 && x 8 14).toNat = 1 := by
    have r30664 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
    have b30665 := hb (x 7 2)
    have b30666 := hb (x 9 13)
    have b30667 := hb (x 8 1 && x 8 14)
    clear * - r30664 b30665 b30666 b30667 d30651 d30596
    omega
  have d30668 : (x 8 14).toNat = 1 := by
    have r30669 := hand2 (x 8 1) (x 8 14)
    have b30670 := hb (x 8 14)
    have b30671 := hb (x 8 1 && x 8 14)
    clear * - r30669 b30670 b30671 d30663
    omega
  have d30672 : (x 7 1).toNat = 0 := by
    have r30673 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
    have b30674 := hb (x 7 1)
    have b30675 := hb (x 8 14)
    clear * - r30673 b30674 b30675 d30668
    omega
  have d30676 : (x 7 13).toNat = 0 := by
    have r30677 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b30678 := hb (x 7 1)
    have b30679 := hb (x 7 13)
    clear * - r30677 b30678 b30679 d30672
    omega
  have d30680 : (x 6 1 && x 6 14).toNat = 1 := by
    have r30681 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
    have b30682 := hb (x 5 2)
    have b30683 := hb (x 7 13)
    have b30684 := hb (x 6 1 && x 6 14)
    clear * - r30681 b30682 b30683 b30684 d30676 d30563
    omega
  have d30685 : (x 6 14).toNat = 1 := by
    have r30686 := hand2 (x 6 1) (x 6 14)
    have b30687 := hb (x 6 14)
    have b30688 := hb (x 6 1 && x 6 14)
    clear * - r30686 b30687 b30688 d30680
    omega
  have d30689 : (x 5 1).toNat = 0 := by
    have r30690 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
    have b30691 := hb (x 5 1)
    have b30692 := hb (x 6 14)
    clear * - r30690 b30691 b30692 d30685
    omega
  have d30693 : (x 5 1 && x 5 12).toNat = 0 := by
    have r30694 := hand1 (x 5 1) (x 5 12)
    have b30695 := hb (x 5 1)
    have b30696 := hb (x 5 1 && x 5 12)
    clear * - r30694 b30695 b30696 d30689
    omega
  have d30697 : (x 6 11).toNat = 1 := by
    have r30698 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
    have b30699 := hb (x 2 4)
    have b30700 := hb (x 6 11)
    have b30701 := hb (x 5 1 && x 5 12)
    have b30702 := hb (x 4 2 && x 4 13)
    have b30703 := hb (x 3 3 && x 3 14)
    clear * - r30698 b30699 b30700 b30701 b30702 b30703 d30693 d30575 g7 g1
    omega
  have d30704 : (x 6 3).toNat = 1 := by
    have r30705 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
    have b30706 := hb (x 6 3)
    have b30707 := hb (x 6 11)
    clear * - r30705 b30706 b30707 d30697
    omega
  have d30708 : (x 9 12).toNat = 0 := by
    have r30709 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e30710 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e30711 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b30712 := hb (x 6 3)
    have b30713 := hb (x 7 2)
    have b30714 := hb (x 8 13)
    have b30715 := hb (x 9 12)
    clear * - r30709 e30710 e30711 b30712 b30713 b30714 b30715 d30596 d30704
    omega
  have d30716 : (x 9 1 && x 9 12).toNat = 0 := by
    have r30717 := hand2 (x 9 1) (x 9 12)
    have b30718 := hb (x 9 12)
    have b30719 := hb (x 9 1 && x 9 12)
    clear * - r30717 b30718 b30719 d30708
    omega
  have d30720 : (x 8 13).toNat = 0 := by
    have r30721 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e30722 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e30723 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b30724 := hb (x 6 3)
    have b30725 := hb (x 7 2)
    have b30726 := hb (x 8 13)
    have b30727 := hb (x 9 12)
    clear * - r30721 e30722 e30723 b30724 b30725 b30726 b30727 d30708 d30596 d30704
    omega
  have d30728 : (x 8 2 && x 8 13).toNat = 0 := by
    have r30729 := hand2 (x 8 2) (x 8 13)
    have b30730 := hb (x 8 13)
    have b30731 := hb (x 8 2 && x 8 13)
    clear * - r30729 b30730 b30731 d30720
    omega
  have d30732 : (x 10 11).toNat = 1 := by
    have r30733 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := hcov11 10
    have b30734 := hb (x 6 4)
    have b30735 := hb (x 10 11)
    have b30736 := hb (x 9 1 && x 9 12)
    have b30737 := hb (x 8 2 && x 8 13)
    have b30738 := hb (x 7 3 && x 7 14)
    clear * - r30733 b30734 b30735 b30736 b30737 b30738 d30716 d30728 d30592 d30530
    omega
  have d30739 : (x 10 3).toNat = 1 := by
    have r30740 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
    have b30741 := hb (x 10 3)
    have b30742 := hb (x 10 11)
    clear * - r30740 b30741 b30742 d30732
    omega
  have d30743 : (x 13 12).toNat = 0 := by
    have r30744 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e30745 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e30746 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b30747 := hb (x 10 3)
    have b30748 := hb (x 11 2)
    have b30749 := hb (x 12 13)
    have b30750 := hb (x 13 12)
    clear * - r30744 e30745 e30746 b30747 b30748 b30749 b30750 d30739
    omega
  have d30751 : (x 13 1 && x 13 12).toNat = 0 := by
    have r30752 := hand2 (x 13 1) (x 13 12)
    have b30753 := hb (x 13 12)
    have b30754 := hb (x 13 1 && x 13 12)
    clear * - r30752 b30753 b30754 d30743
    omega
  have d30755 : (x 12 13).toNat = 0 := by
    have r30756 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e30757 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e30758 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b30759 := hb (x 10 3)
    have b30760 := hb (x 11 2)
    have b30761 := hb (x 12 13)
    have b30762 := hb (x 13 12)
    clear * - r30756 e30757 e30758 b30759 b30760 b30761 b30762 d30743 d30739
    omega
  have d30763 : (x 12 2 && x 12 13).toNat = 0 := by
    have r30764 := hand2 (x 12 2) (x 12 13)
    have b30765 := hb (x 12 13)
    have b30766 := hb (x 12 2 && x 12 13)
    clear * - r30764 b30765 b30766 d30755
    omega
  have d30767 : (x 11 2).toNat = 0 := by
    have r30768 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e30769 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e30770 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b30771 := hb (x 10 3)
    have b30772 := hb (x 11 2)
    have b30773 := hb (x 12 13)
    have b30774 := hb (x 13 12)
    clear * - r30768 e30769 e30770 b30771 b30772 b30773 b30774 d30743 d30755 d30739
    omega
  have d30775 : (x 8 1).toNat = 1 := by
    have r30776 := hand1 (x 8 1) (x 8 14)
    have b30777 := hb (x 8 1)
    have b30778 := hb (x 8 1 && x 8 14)
    clear * - r30776 b30777 b30778 d30663
    omega
  have d30779 : (x 9 14).toNat = 0 := by
    have r30780 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
    have b30781 := hb (x 8 1)
    have b30782 := hb (x 9 14)
    clear * - r30780 b30781 b30782 d30775
    omega
  have d30783 : (x 9 1 && x 9 14).toNat = 0 := by
    have r30784 := hand2 (x 9 1) (x 9 14)
    have b30785 := hb (x 9 14)
    have b30786 := hb (x 9 1 && x 9 14)
    clear * - r30784 b30785 b30786 d30779
    omega
  have d30787 : (x 9 2).toNat = 0 := by
    have r30788 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b30789 := hb (x 9 2)
    have b30790 := hb (x 9 14)
    clear * - r30788 b30789 b30790 d30779
    omega
  have d30791 : (x 8 2).toNat = 0 := by
    have r30792 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e30793 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e30794 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b30795 := hb (x 7 3)
    have b30796 := hb (x 8 2)
    have b30797 := hb (x 9 13)
    have b30798 := hb (x 10 12)
    clear * - r30792 e30793 e30794 b30795 b30796 b30797 b30798 d30635 d30651 d30631
    omega
  have d30799 : (x 10 13).toNat = 1 := by
    have r30800 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
    have b30801 := hb (x 8 2)
    have b30802 := hb (x 10 13)
    have b30803 := hb (x 9 1 && x 9 14)
    clear * - r30800 b30801 b30802 b30803 d30783 d30791
    omega
  have d30804 : (x 10 1).toNat = 1 := by
    have r30805 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b30806 := hb (x 10 1)
    have b30807 := hb (x 10 13)
    clear * - r30805 b30806 b30807 d30799
    omega
  have d30808 : (x 11 14).toNat = 0 := by
    have r30809 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
    have b30810 := hb (x 10 1)
    have b30811 := hb (x 11 14)
    clear * - r30809 b30810 b30811 d30804
    omega
  have d30812 : (x 11 1 && x 11 14).toNat = 0 := by
    have r30813 := hand2 (x 11 1) (x 11 14)
    have b30814 := hb (x 11 14)
    have b30815 := hb (x 11 1 && x 11 14)
    clear * - r30813 b30814 b30815 d30808
    omega
  have d30816 : (x 10 2).toNat = 1 := by
    have r30817 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
    have b30818 := hb (x 10 2)
    have b30819 := hb (x 12 13)
    have b30820 := hb (x 11 1 && x 11 14)
    clear * - r30817 b30818 b30819 b30820 d30755 d30812
    omega
  have d30821 : (x 12 12).toNat = 0 := by
    have r30822 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e30823 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e30824 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b30825 := hb (x 9 3)
    have b30826 := hb (x 10 2)
    have b30827 := hb (x 11 13)
    have b30828 := hb (x 12 12)
    clear * - r30822 e30823 e30824 b30825 b30826 b30827 b30828 d30816
    omega
  have d30829 : (x 12 4).toNat = 0 := by
    have r30830 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b30831 := hb (x 12 4)
    have b30832 := hb (x 12 12)
    clear * - r30830 b30831 b30832 d30821
    omega
  have d30833 : (x 12 4 && x 12 14).toNat = 0 := by
    have r30834 := hand1 (x 12 4) (x 12 14)
    have b30835 := hb (x 12 4)
    have b30836 := hb (x 12 4 && x 12 14)
    clear * - r30834 b30835 b30836 d30829
    omega
  have d30837 : (x 11 13).toNat = 0 := by
    have r30838 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e30839 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e30840 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b30841 := hb (x 9 3)
    have b30842 := hb (x 10 2)
    have b30843 := hb (x 11 13)
    have b30844 := hb (x 12 12)
    clear * - r30838 e30839 e30840 b30841 b30842 b30843 b30844 d30821 d30816
    omega
  have d30845 : (x 11 5).toNat = 0 := by
    have r30846 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
    have b30847 := hb (x 11 5)
    have b30848 := hb (x 11 13)
    clear * - r30846 b30847 b30848 d30837
    omega
  have d30849 : (x 11 3 && x 11 14).toNat = 0 := by
    have r30850 := hand2 (x 11 3) (x 11 14)
    have b30851 := hb (x 11 14)
    have b30852 := hb (x 11 3 && x 11 14)
    clear * - r30850 b30851 b30852 d30808
    omega
  have d30853 : (x 14 11).toNat = 1 := by
    have r30854 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
    have b30855 := hb (x 10 4)
    have b30856 := hb (x 14 11)
    have b30857 := hb (x 13 1 && x 13 12)
    have b30858 := hb (x 12 2 && x 12 13)
    have b30859 := hb (x 11 3 && x 11 14)
    clear * - r30854 b30855 b30856 b30857 b30858 b30859 d30751 d30763 d30849 d30647
    omega
  have d30860 : (x 14 3).toNat = 1 := by
    have r30861 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
    have b30862 := hb (x 14 3)
    have b30863 := hb (x 14 11)
    clear * - r30861 b30862 b30863 d30853
    omega
  have d30864 : (x 17 12).toNat = 0 := by
    have r30865 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e30866 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e30867 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b30868 := hb (x 14 3)
    have b30869 := hb (x 15 2)
    have b30870 := hb (x 16 13)
    have b30871 := hb (x 17 12)
    clear * - r30865 e30866 e30867 b30868 b30869 b30870 b30871 d30860
    omega
  have d30872 : (x 16 13).toNat = 0 := by
    have r30873 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e30874 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e30875 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b30876 := hb (x 14 3)
    have b30877 := hb (x 15 2)
    have b30878 := hb (x 16 13)
    have b30879 := hb (x 17 12)
    clear * - r30873 e30874 e30875 b30876 b30877 b30878 b30879 d30864 d30860
    omega
  have d30880 : (x 15 2).toNat = 0 := by
    have r30881 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e30882 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e30883 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b30884 := hb (x 14 3)
    have b30885 := hb (x 15 2)
    have b30886 := hb (x 16 13)
    have b30887 := hb (x 17 12)
    clear * - r30881 e30882 e30883 b30884 b30885 b30886 b30887 d30864 d30872 d30860
    omega
  have d30888 : (x 11 12).toNat = 0 := by
    have r30889 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e30890 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e30891 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b30892 := hb (x 8 3)
    have b30893 := hb (x 9 2)
    have b30894 := hb (x 10 13)
    have b30895 := hb (x 11 12)
    clear * - r30889 e30890 e30891 b30892 b30893 b30894 b30895 d30799 d30787
    omega
  have d30896 : (x 11 4).toNat = 0 := by
    have r30897 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b30898 := hb (x 11 4)
    have b30899 := hb (x 11 12)
    clear * - r30897 b30898 b30899 d30888
    omega
  have d30900 : (x 8 3).toNat = 0 := by
    have r30901 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e30902 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e30903 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b30904 := hb (x 8 3)
    have b30905 := hb (x 9 2)
    have b30906 := hb (x 10 13)
    have b30907 := hb (x 11 12)
    clear * - r30901 e30902 e30903 b30904 b30905 b30906 b30907 d30888 d30799 d30787
    omega
  have d30908 : (x 8 3 && x 8 14).toNat = 0 := by
    have r30909 := hand1 (x 8 3) (x 8 14)
    have b30910 := hb (x 8 3)
    have b30911 := hb (x 8 3 && x 8 14)
    clear * - r30909 b30910 b30911 d30900
    omega
  have d30912 : (x 11 11).toNat = 1 := by
    have r30913 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
    have b30914 := hb (x 7 4)
    have b30915 := hb (x 11 11)
    have b30916 := hb (x 10 1 && x 10 12)
    have b30917 := hb (x 9 2 && x 9 13)
    have b30918 := hb (x 8 3 && x 8 14)
    clear * - r30913 b30914 b30915 b30916 b30917 b30918 d30643 d30659 d30908 d30608
    omega
  have d30919 : (x 11 3).toNat = 1 := by
    have r30920 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b30921 := hb (x 11 3)
    have b30922 := hb (x 11 11)
    clear * - r30920 b30921 b30922 d30912
    omega
  have d30923 : (x 14 12).toNat = 0 := by
    have r30924 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e30925 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e30926 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b30927 := hb (x 11 3)
    have b30928 := hb (x 12 2)
    have b30929 := hb (x 13 13)
    have b30930 := hb (x 14 12)
    clear * - r30924 e30925 e30926 b30927 b30928 b30929 b30930 d30919
    omega
  have d30931 : (x 14 1 && x 14 12).toNat = 0 := by
    have r30932 := hand2 (x 14 1) (x 14 12)
    have b30933 := hb (x 14 12)
    have b30934 := hb (x 14 1 && x 14 12)
    clear * - r30932 b30933 b30934 d30923
    omega
  have d30935 : (x 14 2 && x 14 12).toNat = 0 := by
    have r30936 := hand2 (x 14 2) (x 14 12)
    have b30937 := hb (x 14 12)
    have b30938 := hb (x 14 2 && x 14 12)
    clear * - r30936 b30937 b30938 d30923
    omega
  have d30939 : (x 13 13).toNat = 0 := by
    have r30940 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e30941 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e30942 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b30943 := hb (x 11 3)
    have b30944 := hb (x 12 2)
    have b30945 := hb (x 13 13)
    have b30946 := hb (x 14 12)
    clear * - r30940 e30941 e30942 b30943 b30944 b30945 b30946 d30923 d30919
    omega
  have d30947 : (x 13 2 && x 13 13).toNat = 0 := by
    have r30948 := hand2 (x 13 2) (x 13 13)
    have b30949 := hb (x 13 13)
    have b30950 := hb (x 13 2 && x 13 13)
    clear * - r30948 b30949 b30950 d30939
    omega
  have d30951 : (x 13 3 && x 13 13).toNat = 0 := by
    have r30952 := hand2 (x 13 3) (x 13 13)
    have b30953 := hb (x 13 13)
    have b30954 := hb (x 13 3 && x 13 13)
    clear * - r30952 b30953 b30954 d30939
    omega
  have d30955 : (x 12 1 && x 12 14).toNat = 1 := by
    have r30956 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
    have b30957 := hb (x 11 2)
    have b30958 := hb (x 13 13)
    have b30959 := hb (x 12 1 && x 12 14)
    clear * - r30956 b30957 b30958 b30959 d30939 d30767
    omega
  have d30960 : (x 12 1).toNat = 1 := by
    have r30961 := hand1 (x 12 1) (x 12 14)
    have b30962 := hb (x 12 1)
    have b30963 := hb (x 12 1 && x 12 14)
    clear * - r30961 b30962 b30963 d30955
    omega
  have d30964 : (x 13 14).toNat = 0 := by
    have r30965 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
    have b30966 := hb (x 12 1)
    have b30967 := hb (x 13 14)
    clear * - r30965 b30966 b30967 d30960
    omega
  have d30968 : (x 13 1 && x 13 14).toNat = 0 := by
    have r30969 := hand2 (x 13 1) (x 13 14)
    have b30970 := hb (x 13 14)
    have b30971 := hb (x 13 1 && x 13 14)
    clear * - r30969 b30970 b30971 d30964
    omega
  have d30972 : (x 13 2).toNat = 0 := by
    have r30973 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
    have b30974 := hb (x 13 2)
    have b30975 := hb (x 13 14)
    clear * - r30973 b30974 b30975 d30964
    omega
  have d30976 : (x 12 2).toNat = 0 := by
    have r30977 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e30978 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e30979 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b30980 := hb (x 11 3)
    have b30981 := hb (x 12 2)
    have b30982 := hb (x 13 13)
    have b30983 := hb (x 14 12)
    clear * - r30977 e30978 e30979 b30980 b30981 b30982 b30983 d30923 d30939 d30919
    omega
  have d30984 : (x 14 13).toNat = 1 := by
    have r30985 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
    have b30986 := hb (x 12 2)
    have b30987 := hb (x 14 13)
    have b30988 := hb (x 13 1 && x 13 14)
    clear * - r30985 b30986 b30987 b30988 d30968 d30976
    omega
  have d30989 : (x 15 12).toNat = 0 := by
    have r30990 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e30991 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e30992 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b30993 := hb (x 12 3)
    have b30994 := hb (x 13 2)
    have b30995 := hb (x 14 13)
    have b30996 := hb (x 15 12)
    clear * - r30990 e30991 e30992 b30993 b30994 b30995 b30996 d30984 d30972
    omega
  have d30997 : (x 12 3).toNat = 0 := by
    have r30998 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e30999 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e31000 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b31001 := hb (x 12 3)
    have b31002 := hb (x 13 2)
    have b31003 := hb (x 14 13)
    have b31004 := hb (x 15 12)
    clear * - r30998 e30999 e31000 b31001 b31002 b31003 b31004 d30989 d30984 d30972
    omega
  have d31005 : (x 12 3 && x 12 14).toNat = 0 := by
    have r31006 := hand1 (x 12 3) (x 12 14)
    have b31007 := hb (x 12 3)
    have b31008 := hb (x 12 3 && x 12 14)
    clear * - r31006 b31007 b31008 d30997
    omega
  have d31009 : (x 15 11).toNat = 1 := by
    have r31010 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
    have b31011 := hb (x 11 4)
    have b31012 := hb (x 15 11)
    have b31013 := hb (x 14 1 && x 14 12)
    have b31014 := hb (x 13 2 && x 13 13)
    have b31015 := hb (x 12 3 && x 12 14)
    clear * - r31010 b31011 b31012 b31013 b31014 b31015 d30931 d30947 d31005 d30896
    omega
  have d31016 : (x 15 3).toNat = 1 := by
    have r31017 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
    have b31018 := hb (x 15 3)
    have b31019 := hb (x 15 11)
    clear * - r31017 b31018 b31019 d31009
    omega
  have d31020 : (x 18 12).toNat = 0 := by
    have r31021 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e31022 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e31023 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b31024 := hb (x 15 3)
    have b31025 := hb (x 16 2)
    have b31026 := hb (x 17 13)
    have b31027 := hb (x 18 12)
    clear * - r31021 e31022 e31023 b31024 b31025 b31026 b31027 d31016
    omega
  have d31028 : (x 17 13).toNat = 0 := by
    have r31029 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e31030 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e31031 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b31032 := hb (x 15 3)
    have b31033 := hb (x 16 2)
    have b31034 := hb (x 17 13)
    have b31035 := hb (x 18 12)
    clear * - r31029 e31030 e31031 b31032 b31033 b31034 b31035 d31020 d31016
    omega
  have d31036 : (x 16 1 && x 16 14).toNat = 1 := by
    have r31037 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
    have b31038 := hb (x 15 2)
    have b31039 := hb (x 17 13)
    have b31040 := hb (x 16 1 && x 16 14)
    clear * - r31037 b31038 b31039 b31040 d31028 d30880
    omega
  have d31041 : (x 16 14).toNat = 1 := by
    have r31042 := hand2 (x 16 1) (x 16 14)
    have b31043 := hb (x 16 14)
    have b31044 := hb (x 16 1 && x 16 14)
    clear * - r31042 b31043 b31044 d31036
    omega
  have d31045 : (x 15 1).toNat = 0 := by
    have r31046 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
    have b31047 := hb (x 15 1)
    have b31048 := hb (x 16 14)
    clear * - r31046 b31047 b31048 d31041
    omega
  have d31049 : (x 15 1 && x 15 11).toNat = 0 := by
    have r31050 := hand1 (x 15 1) (x 15 11)
    have b31051 := hb (x 15 1)
    have b31052 := hb (x 15 1 && x 15 11)
    clear * - r31050 b31051 b31052 d31045
    omega
  have d31053 : (x 16 2).toNat = 0 := by
    have r31054 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e31055 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e31056 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b31057 := hb (x 15 3)
    have b31058 := hb (x 16 2)
    have b31059 := hb (x 17 13)
    have b31060 := hb (x 18 12)
    clear * - r31054 e31055 e31056 b31057 b31058 b31059 b31060 d31020 d31028 d31016
    omega
  have d31061 : (x 16 10).toNat = 0 := by
    have r31062 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
    have b31063 := hb (x 16 2)
    have b31064 := hb (x 16 10)
    clear * - r31062 b31063 b31064 d31053
    omega
  have r31065 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := hcov10 16
  have b31066 := hb (x 11 5)
  have b31067 := hb (x 16 10)
  have b31068 := hb (x 15 1 && x 15 11)
  have b31069 := hb (x 14 2 && x 14 12)
  have b31070 := hb (x 13 3 && x 13 13)
  have b31071 := hb (x 12 4 && x 12 14)
  linarith only [r31065, b31066, b31067, b31068, b31069, b31070, b31071, d31061, d31049, d30935, d30951, d30833, d30845]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 4).toNat = 0)
    (g1 : (x 2 4).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 4).toNat = 0)
    (g4 : (x 2 1 && x 2 12).toNat = 0)
    (g5 : (x 1 2 && x 1 13).toNat = 0)
    (g6 : (x 0 3 && x 0 14).toNat = 0)
    (g7 : (x 3 3 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7
