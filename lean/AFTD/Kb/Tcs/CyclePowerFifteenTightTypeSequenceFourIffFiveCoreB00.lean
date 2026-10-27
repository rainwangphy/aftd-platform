import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b00

Topic: combinatorics   Node: 6b7e406c5991

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_four_iff_five_core: under the layer-free tight-cover constraints for k = 15 and 49 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b00_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 2).toNat = 0)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 3).toNat = 0)
    (g5 : (x 0 4).toNat = 0)
    (g6 : (x 0 11).toNat = 0)
    (g7 : (x 1 2).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 2 11).toNat = 0)
    (g11 : (x 3 10).toNat = 0)
    (g12 : (x 4 9).toNat = 0)
    (g13 : (x 5 4 && x 5 8).toNat = 0)
    (g14 : (x 4 5 && x 4 9).toNat = 0)
    (g15 : (x 3 6 && x 3 10).toNat = 0)
    (g16 : (x 2 7 && x 2 11).toNat = 0)
    (g17 : (x 1 8 && x 1 12).toNat = 0)
    (g18 : (x 1 4 && x 1 10).toNat = 0)
    (g19 : (x 0 5 && x 0 11).toNat = 0)
    (g20 : (x (-1) 6 && x (-1) 12).toNat = 0)
    (g21 : (x (-2) 7 && x (-2) 13).toNat = 0)
    (g22 : (x 5 2 && x 5 8).toNat = 0)
    (g23 : (x 4 3 && x 4 9).toNat = 0)
    (g24 : (x 3 4 && x 3 10).toNat = 0)
    (g25 : (x 2 5 && x 2 11).toNat = 0)
    (g26 : (x 1 6 && x 1 12).toNat = 0)
    (g27 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g28 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g29 : (x 3 1 && x 3 10).toNat = 0)
    (g30 : (x 2 2 && x 2 11).toNat = 0)
    (g31 : (x 1 3 && x 1 12).toNat = 0)
    (g32 : (x 0 4 && x 0 13).toNat = 0)
    (g33 : (x 1 5 && x 1 14).toNat = 0)
    (g34 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g35 : (x 0 1 && x 0 11).toNat = 0)
    (g36 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g37 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g38 : (x 2 1 && x 2 11).toNat = 0)
    (g39 : (x 1 2 && x 1 12).toNat = 0)
    (g40 : (x 0 3 && x 0 13).toNat = 0)
    (g41 : (x 0 4 && x 0 14).toNat = 0)
    (g42 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g43 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g44 : (x 1 1 && x 1 12).toNat = 0)
    (g45 : (x 1 2 && x 1 13).toNat = 0)
    (g46 : (x 0 3 && x 0 14).toNat = 0)
    (g47 : (x 1 3 && x 1 14).toNat = 0)
    (g48 : (x 1 1 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d469 : (x 0 2 && x 0 13).toNat = 0 := by
    have r470 := hand1 (x 0 2) (x 0 13)
    have b471 := hb (x 0 2)
    have b472 := hb (x 0 2 && x 0 13)
    clear * - r470 b471 b472 g3
    omega
  have d473 : (x 0 2 && x 0 12).toNat = 0 := by
    have r474 := hand1 (x 0 2) (x 0 12)
    have b475 := hb (x 0 2)
    have b476 := hb (x 0 2 && x 0 12)
    clear * - r474 b475 b476 g3
    omega
  have d477 : (x 0 2 && x 0 6).toNat = 0 := by
    have r478 := hand1 (x 0 2) (x 0 6)
    have b479 := hb (x 0 2)
    have b480 := hb (x 0 2 && x 0 6)
    clear * - r478 b479 b480 g3
    omega
  have d481 : (x 0 10).toNat = 0 := by
    have r482 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
    have b483 := hb (x 0 2)
    have b484 := hb (x 0 10)
    clear * - r482 b483 b484 g3
    omega
  have d485 : (x 0 1 && x 0 10).toNat = 0 := by
    have r486 := hand2 (x 0 1) (x 0 10)
    have b487 := hb (x 0 10)
    have b488 := hb (x 0 1 && x 0 10)
    clear * - r486 b487 b488 d481
    omega
  have d489 : (x 2 13).toNat = 1 := by
    have r490 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b491 := hb (x 0 2)
    have b492 := hb (x 2 13)
    have b493 := hb (x 1 1 && x 1 14)
    clear * - r490 b491 b492 b493 g48 g3
    omega
  have d494 : (x 2 1).toNat = 1 := by
    have r495 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b496 := hb (x 2 1)
    have b497 := hb (x 2 13)
    clear * - r495 b496 b497 d489
    omega
  have d498 : (x 3 14).toNat = 0 := by
    have r499 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b500 := hb (x 2 1)
    have b501 := hb (x 3 14)
    clear * - r499 b500 b501 d494
    omega
  have d502 : (x 3 2).toNat = 0 := by
    have r503 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b504 := hb (x 3 2)
    have b505 := hb (x 3 14)
    clear * - r503 b504 b505 d498
    omega
  have d506 : (x 3 2 && x 3 8).toNat = 0 := by
    have r507 := hand1 (x 3 2) (x 3 8)
    have b508 := hb (x 3 2)
    have b509 := hb (x 3 2 && x 3 8)
    clear * - r507 b508 b509 d502
    omega
  have d510 : (x 3 12).toNat = 0 := by
    have r511 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e512 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e513 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b514 := hb (x 0 3)
    have b515 := hb (x 1 2)
    have b516 := hb (x 2 13)
    have b517 := hb (x 3 12)
    clear * - r511 e512 e513 b514 b515 b516 b517 d489 g7 g4
    omega
  have d518 : (x 3 1 && x 3 12).toNat = 0 := by
    have r519 := hand2 (x 3 1) (x 3 12)
    have b520 := hb (x 3 12)
    have b521 := hb (x 3 1 && x 3 12)
    clear * - r519 b520 b521 d510
    omega
  have d522 : (x 3 3 && x 3 12).toNat = 0 := by
    have r523 := hand2 (x 3 3) (x 3 12)
    have b524 := hb (x 3 12)
    have b525 := hb (x 3 3 && x 3 12)
    clear * - r523 b524 b525 d510
    omega
  have d526 : (x 3 8 && x 3 12).toNat = 0 := by
    have r527 := hand2 (x 3 8) (x 3 12)
    have b528 := hb (x 3 12)
    have b529 := hb (x 3 8 && x 3 12)
    clear * - r527 b528 b529 d510
    omega
  have d530 : (x 3 4).toNat = 0 := by
    have r531 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b532 := hb (x 3 4)
    have b533 := hb (x 3 12)
    clear * - r531 b532 b533 d510
    omega
  cases h534 : x 0 6
  · have f535 : (x 0 6).toNat = 0 := by rw [h534]; rfl
    have d536 : (x 0 6 && x 0 12).toNat = 0 := by
      have r537 := hand1 (x 0 6) (x 0 12)
      have b538 := hb (x 0 6)
      have b539 := hb (x 0 6 && x 0 12)
      clear * - r537 b538 b539 f535
      omega
    cases h540 : x 0 7
    · have f541 : (x 0 7).toNat = 0 := by rw [h540]; rfl
      have d542 : (x 0 7 && x 0 13).toNat = 0 := by
        have r543 := hand1 (x 0 7) (x 0 13)
        have b544 := hb (x 0 7)
        have b545 := hb (x 0 7 && x 0 13)
        clear * - r543 b544 b545 f541
        omega
      have r546 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e547 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e548 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e549 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e550 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e551 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e552 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have r553 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e554 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e555 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e556 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e557 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e558 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e559 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have r560 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e561 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e562 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e563 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e564 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e565 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e566 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have r567 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e568 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e569 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e570 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e571 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e572 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e573 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have r574 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e575 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e576 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e577 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e578 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e579 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e580 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have r581 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e582 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e583 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e584 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e585 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e586 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e587 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have r588 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e589 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e590 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have r591 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e592 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e593 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have r594 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e595 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e596 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have r597 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e598 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
      have e599 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
      have r600 : 1 ≤ (x 5 6).toNat + (x 4 1 && x 4 7).toNat + (x 3 2 && x 3 8).toNat + (x 2 3 && x 2 9).toNat + (x 1 4 && x 1 10).toNat + (x 0 5 && x 0 11).toNat + (x (-1) 6 && x (-1) 12).toNat + (x (-2) 7 && x (-2) 13).toNat + (x (-3) 8 && x (-3) 14).toNat + (x (-4) 9).toNat := by have q := hcov6 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r601 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r602 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r603 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r604 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r605 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r606 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r607 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
      have r608 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have r609 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
      have r610 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have r611 := hand1 (x 7 2) (x 7 6)
      have r612 := hand1 (x 6 3) (x 6 7)
      have r613 := hand1 (x 0 9) (x 0 13)
      have r614 := hand2 (x 4 1) (x 4 7)
      have r615 := hand2 (x 2 3) (x 2 9)
      have r616 := hand1 (x (-3) 8) (x (-3) 14)
      have r617 := hand2 (x 6 1) (x 6 7)
      have r618 := hand1 (x (-1) 8) (x (-1) 14)
      have r619 := hand2 (x (-4) 1) (x (-4) 11)
      have r620 := hand1 (x (-5) 2) (x (-5) 12)
      have r621 := hand1 (x (-6) 3) (x (-6) 13)
      have r622 := hand1 (x (-7) 4) (x (-7) 14)
      have r623 := hand1 (x (-3) 2) (x (-3) 12)
      have r624 := hand1 (x (-4) 3) (x (-4) 13)
      have r625 := hand1 (x (-5) 4) (x (-5) 14)
      have r626 := hand1 (x (-3) 4) (x (-3) 14)
      have r627 := hand1 (x (-1) 4) (x (-1) 14)
      have r628 := hand2 (x 10 1) (x 10 11)
      have r629 := hand2 (x 9 2) (x 9 12)
      have r630 := hand2 (x 8 3) (x 8 13)
      have r631 := hand1 (x 7 4) (x 7 14)
      linarith only [r546, e547, e548, e549, e550, e551, e552, r553, e554, e555, e556, e557, e558, e559, r560, e561, e562, e563, e564, e565, e566, r567, e568, e569, e570, e571, e572, e573, r574, e575, e576, e577, e578, e579, e580, r581, e582, e583, e584, e585, e586, e587, r588, e589, e590, r591, e592, e593, r594, e595, e596, r597, e598, e599, r600, r601, r602, r603, r604, r605, r606, r607, r608, r609, r610, r611, r612, r613, r614, r615, r616, r617, r618, r619, r620, r621, r622, r623, r624, r625, r626, r627, r628, r629, r630, r631, g0, g2, g6, g9, g11, g13, g14, g15, g16, g17, d506, g18, g19, g20, g21, g22, g23, g24, g25, g26, d542, g34, g35, g36, g37, g38, g39, g40]
    · have f737 : (x 0 7).toNat = 1 := by rw [h540]; rfl
      have d738 : (x 7 8).toNat = 0 := by
        have r739 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e740 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e741 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e742 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e743 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e744 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e745 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b746 := hb (x 0 7)
        have b747 := hb (x 1 6)
        have b748 := hb (x 2 5)
        have b749 := hb (x 3 4)
        have b750 := hb (x 4 11)
        have b751 := hb (x 5 10)
        have b752 := hb (x 6 9)
        have b753 := hb (x 7 8)
        clear * - r739 e740 e741 e742 e743 e744 e745 b746 b747 b748 b749 b750 b751 b752 b753 d530 g8 f737
        omega
      have d754 : (x 7 4 && x 7 8).toNat = 0 := by
        have r755 := hand2 (x 7 4) (x 7 8)
        have b756 := hb (x 7 8)
        have b757 := hb (x 7 4 && x 7 8)
        clear * - r755 b756 b757 d738
        omega
      have d758 : (x 6 9).toNat = 0 := by
        have r759 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e760 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e761 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e762 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e763 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e764 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e765 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b766 := hb (x 0 7)
        have b767 := hb (x 1 6)
        have b768 := hb (x 2 5)
        have b769 := hb (x 3 4)
        have b770 := hb (x 4 11)
        have b771 := hb (x 5 10)
        have b772 := hb (x 6 9)
        have b773 := hb (x 7 8)
        clear * - r759 e760 e761 e762 e763 e764 e765 b766 b767 b768 b769 b770 b771 b772 b773 d738 d530 g8 f737
        omega
      have d774 : (x 6 5 && x 6 9).toNat = 0 := by
        have r775 := hand2 (x 6 5) (x 6 9)
        have b776 := hb (x 6 9)
        have b777 := hb (x 6 5 && x 6 9)
        clear * - r775 b776 b777 d758
        omega
      have d778 : (x 5 10).toNat = 0 := by
        have r779 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e780 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e781 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e782 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e783 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e784 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e785 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b786 := hb (x 0 7)
        have b787 := hb (x 1 6)
        have b788 := hb (x 2 5)
        have b789 := hb (x 3 4)
        have b790 := hb (x 4 11)
        have b791 := hb (x 5 10)
        have b792 := hb (x 6 9)
        have b793 := hb (x 7 8)
        clear * - r779 e780 e781 e782 e783 e784 e785 b786 b787 b788 b789 b790 b791 b792 b793 d738 d758 d530 g8 f737
        omega
      have d794 : (x 5 1 && x 5 10).toNat = 0 := by
        have r795 := hand2 (x 5 1) (x 5 10)
        have b796 := hb (x 5 10)
        have b797 := hb (x 5 1 && x 5 10)
        clear * - r795 b796 b797 d778
        omega
      have d798 : (x 5 6 && x 5 10).toNat = 0 := by
        have r799 := hand2 (x 5 6) (x 5 10)
        have b800 := hb (x 5 10)
        have b801 := hb (x 5 6 && x 5 10)
        clear * - r799 b800 b801 d778
        omega
      have d802 : (x 4 11).toNat = 0 := by
        have r803 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e804 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e805 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e806 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e807 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e808 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e809 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b810 := hb (x 0 7)
        have b811 := hb (x 1 6)
        have b812 := hb (x 2 5)
        have b813 := hb (x 3 4)
        have b814 := hb (x 4 11)
        have b815 := hb (x 5 10)
        have b816 := hb (x 6 9)
        have b817 := hb (x 7 8)
        clear * - r803 e804 e805 e806 e807 e808 e809 b810 b811 b812 b813 b814 b815 b816 b817 d738 d758 d778 d530 g8 f737
        omega
      have d818 : (x 4 2 && x 4 11).toNat = 0 := by
        have r819 := hand2 (x 4 2) (x 4 11)
        have b820 := hb (x 4 11)
        have b821 := hb (x 4 2 && x 4 11)
        clear * - r819 b820 b821 d802
        omega
      have d822 : (x 2 4 && x 2 13).toNat = 1 := by
        have r823 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b824 := hb (x 0 6)
        have b825 := hb (x 6 9)
        have b826 := hb (x 5 1 && x 5 10)
        have b827 := hb (x 4 2 && x 4 11)
        have b828 := hb (x 3 3 && x 3 12)
        have b829 := hb (x 2 4 && x 2 13)
        have b830 := hb (x 1 5 && x 1 14)
        clear * - r823 b824 b825 b826 b827 b828 b829 b830 d758 d794 d818 d522 g33 f535
        omega
      have d831 : (x 2 4).toNat = 1 := by
        have r832 := hand1 (x 2 4) (x 2 13)
        have b833 := hb (x 2 4)
        have b834 := hb (x 2 4 && x 2 13)
        clear * - r832 b833 b834 d822
        omega
      have d835 : (x 2 12).toNat = 1 := by
        have r836 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
        have b837 := hb (x 2 4)
        have b838 := hb (x 2 12)
        clear * - r836 b837 b838 d831
        omega
      have d839 : (x 1 13).toNat = 0 := by
        have r840 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e841 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e842 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b843 := hb (x (-1) 3)
        have b844 := hb (x 0 2)
        have b845 := hb (x 1 13)
        have b846 := hb (x 2 12)
        clear * - r840 e841 e842 b843 b844 b845 b846 d835 g3
        omega
      have d847 : (x 1 5).toNat = 0 := by
        have r848 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
        have b849 := hb (x 1 5)
        have b850 := hb (x 1 13)
        clear * - r848 b849 b850 d839
        omega
      have d851 : (x 1 5 && x 1 11).toNat = 0 := by
        have r852 := hand1 (x 1 5) (x 1 11)
        have b853 := hb (x 1 5)
        have b854 := hb (x 1 5 && x 1 11)
        clear * - r852 b853 b854 d847
        omega
      have d855 : (x 0 1 && x 0 14).toNat = 1 := by
        have r856 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b857 := hb (x (-1) 2)
        have b858 := hb (x 1 13)
        have b859 := hb (x 0 1 && x 0 14)
        clear * - r856 b857 b858 b859 d839 g1
        omega
      have d860 : (x 0 14).toNat = 1 := by
        have r861 := hand2 (x 0 1) (x 0 14)
        have b862 := hb (x 0 14)
        have b863 := hb (x 0 1 && x 0 14)
        clear * - r861 b862 b863 d855
        omega
      have d864 : (x (-1) 1).toNat = 0 := by
        have r865 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b866 := hb (x (-1) 1)
        have b867 := hb (x 0 14)
        clear * - r865 b866 b867 d860
        omega
      have d868 : (x (-1) 13).toNat = 0 := by
        have r869 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
        have b870 := hb (x (-1) 1)
        have b871 := hb (x (-1) 13)
        clear * - r869 b870 b871 d864
        omega
      have d872 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
        have r873 := hand2 (x (-1) 7) (x (-1) 13)
        have b874 := hb (x (-1) 13)
        have b875 := hb (x (-1) 7 && x (-1) 13)
        clear * - r873 b874 b875 d868
        omega
      have d876 : (x (-1) 5).toNat = 0 := by
        have r877 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
        have b878 := hb (x (-1) 5)
        have b879 := hb (x (-1) 13)
        clear * - r877 b878 b879 d868
        omega
      have d880 : (x (-1) 5 && x (-1) 14).toNat = 0 := by
        have r881 := hand1 (x (-1) 5) (x (-1) 14)
        have b882 := hb (x (-1) 5)
        have b883 := hb (x (-1) 5 && x (-1) 14)
        clear * - r881 b882 b883 d876
        omega
      have d884 : (x (-2) 6).toNat = 1 := by
        have r885 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b886 := hb (x (-2) 6)
        have b887 := hb (x 4 9)
        have b888 := hb (x 3 1 && x 3 10)
        have b889 := hb (x 2 2 && x 2 11)
        have b890 := hb (x 1 3 && x 1 12)
        have b891 := hb (x 0 4 && x 0 13)
        have b892 := hb (x (-1) 5 && x (-1) 14)
        clear * - r885 b886 b887 b888 b889 b890 b891 b892 g12 g29 g30 g31 g32 d880
        omega
      have d893 : (x (-2) 14).toNat = 1 := by
        have r894 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
        have b895 := hb (x (-2) 6)
        have b896 := hb (x (-2) 14)
        clear * - r894 b895 b896 d884
        omega
      have d897 : (x (-3) 1).toNat = 0 := by
        have r898 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b899 := hb (x (-3) 1)
        have b900 := hb (x (-2) 14)
        clear * - r898 b899 b900 d893
        omega
      have d901 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
        have r902 := hand1 (x (-3) 1) (x (-3) 14)
        have b903 := hb (x (-3) 1)
        have b904 := hb (x (-3) 1 && x (-3) 14)
        clear * - r902 b903 b904 d897
        omega
      have d905 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
        have r906 := hand1 (x (-3) 1) (x (-3) 12)
        have b907 := hb (x (-3) 1)
        have b908 := hb (x (-3) 1 && x (-3) 12)
        clear * - r906 b907 b908 d897
        omega
      have d909 : (x (-3) 13).toNat = 0 := by
        have r910 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
        have b911 := hb (x (-3) 1)
        have b912 := hb (x (-3) 13)
        clear * - r910 b911 b912 d897
        omega
      have d913 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
        have r914 := hand2 (x (-3) 4) (x (-3) 13)
        have b915 := hb (x (-3) 13)
        have b916 := hb (x (-3) 4 && x (-3) 13)
        clear * - r914 b915 b916 d909
        omega
      have d917 : (x (-3) 9).toNat = 0 := by
        have r918 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
        have b919 := hb (x (-3) 1)
        have b920 := hb (x (-3) 9)
        clear * - r918 b919 b920 d897
        omega
      have d921 : (x (-1) 3).toNat = 0 := by
        have r922 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e923 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e924 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b925 := hb (x (-1) 3)
        have b926 := hb (x 0 2)
        have b927 := hb (x 1 13)
        have b928 := hb (x 2 12)
        clear * - r922 e923 e924 b925 b926 b927 b928 d835 d839 g3
        omega
      have d929 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
        have r930 := hand1 (x (-1) 3) (x (-1) 14)
        have b931 := hb (x (-1) 3)
        have b932 := hb (x (-1) 3 && x (-1) 14)
        clear * - r930 b931 b932 d921
        omega
      have d933 : (x (-2) 4).toNat = 1 := by
        have r934 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b935 := hb (x (-2) 4)
        have b936 := hb (x 2 11)
        have b937 := hb (x 1 1 && x 1 12)
        have b938 := hb (x 0 2 && x 0 13)
        have b939 := hb (x (-1) 3 && x (-1) 14)
        clear * - r934 b935 b936 b937 b938 b939 g10 g44 d469 d929
        omega
      have d940 : (x (-2) 12).toNat = 1 := by
        have r941 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have b942 := hb (x (-2) 4)
        have b943 := hb (x (-2) 12)
        clear * - r941 b942 b943 d933
        omega
      have d944 : (x (-4) 2).toNat = 0 := by
        have r945 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e946 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e947 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b948 := hb (x (-5) 3)
        have b949 := hb (x (-4) 2)
        have b950 := hb (x (-3) 13)
        have b951 := hb (x (-2) 12)
        clear * - r945 e946 e947 b948 b949 b950 b951 d940 d909
        omega
      have d952 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
        have r953 := hand1 (x (-4) 2) (x (-4) 13)
        have b954 := hb (x (-4) 2)
        have b955 := hb (x (-4) 2 && x (-4) 13)
        clear * - r953 b954 b955 d944
        omega
      have d956 : (x (-4) 10).toNat = 0 := by
        have r957 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
        have b958 := hb (x (-4) 2)
        have b959 := hb (x (-4) 10)
        clear * - r957 b958 b959 d944
        omega
      have d960 : (x (-2) 13).toNat = 1 := by
        have r961 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b962 := hb (x (-4) 2)
        have b963 := hb (x (-2) 13)
        have b964 := hb (x (-3) 1 && x (-3) 14)
        clear * - r961 b962 b963 b964 d901 d944
        omega
      have d965 : (x (-2) 1).toNat = 1 := by
        have r966 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b967 := hb (x (-2) 1)
        have b968 := hb (x (-2) 13)
        clear * - r966 b967 b968 d960
        omega
      have d969 : (x (-1) 14).toNat = 0 := by
        have r970 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b971 := hb (x (-2) 1)
        have b972 := hb (x (-1) 14)
        clear * - r970 b971 b972 d965
        omega
      have d973 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
        have r974 := hand2 (x (-1) 4) (x (-1) 14)
        have b975 := hb (x (-1) 14)
        have b976 := hb (x (-1) 4 && x (-1) 14)
        clear * - r974 b975 b976 d969
        omega
      have d977 : (x (-2) 5).toNat = 1 := by
        have r978 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b979 := hb (x (-2) 5)
        have b980 := hb (x 3 10)
        have b981 := hb (x 2 1 && x 2 11)
        have b982 := hb (x 1 2 && x 1 12)
        have b983 := hb (x 0 3 && x 0 13)
        have b984 := hb (x (-1) 4 && x (-1) 14)
        clear * - r978 b979 b980 b981 b982 b983 b984 g11 g38 g39 g40 d973
        omega
      have d985 : (x (-1) 12).toNat = 0 := by
        have r986 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e987 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e988 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b989 := hb (x (-4) 3)
        have b990 := hb (x (-3) 2)
        have b991 := hb (x (-2) 13)
        have b992 := hb (x (-1) 12)
        clear * - r986 e987 e988 b989 b990 b991 b992 d960
        omega
      have d993 : (x (-1) 4).toNat = 0 := by
        have r994 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b995 := hb (x (-1) 4)
        have b996 := hb (x (-1) 12)
        clear * - r994 b995 b996 d985
        omega
      have d997 : (x (-5) 3).toNat = 0 := by
        have r998 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e999 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e1000 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b1001 := hb (x (-5) 3)
        have b1002 := hb (x (-4) 2)
        have b1003 := hb (x (-3) 13)
        have b1004 := hb (x (-2) 12)
        clear * - r998 e999 e1000 b1001 b1002 b1003 b1004 d940 d909 d944
        omega
      have d1005 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
        have r1006 := hand1 (x (-5) 3) (x (-5) 14)
        have b1007 := hb (x (-5) 3)
        have b1008 := hb (x (-5) 3 && x (-5) 14)
        clear * - r1006 b1007 b1008 d997
        omega
      have d1009 : (x (-6) 4).toNat = 1 := by
        have r1010 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1011 := hb (x (-6) 4)
        have b1012 := hb (x (-2) 11)
        have b1013 := hb (x (-3) 1 && x (-3) 12)
        have b1014 := hb (x (-4) 2 && x (-4) 13)
        have b1015 := hb (x (-5) 3 && x (-5) 14)
        clear * - r1010 b1011 b1012 b1013 b1014 b1015 g0 d905 d952 d1005
        omega
      have d1016 : (x (-6) 12).toNat = 1 := by
        have r1017 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
        have b1018 := hb (x (-6) 4)
        have b1019 := hb (x (-6) 12)
        clear * - r1017 b1018 b1019 d1009
        omega
      have d1020 : (x (-7) 13).toNat = 0 := by
        have r1021 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1022 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e1023 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b1024 := hb (x (-9) 3)
        have b1025 := hb (x (-8) 2)
        have b1026 := hb (x (-7) 13)
        have b1027 := hb (x (-6) 12)
        clear * - r1021 e1022 e1023 b1024 b1025 b1026 b1027 d1016
        omega
      have d1028 : (x (-7) 5).toNat = 0 := by
        have r1029 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
        have b1030 := hb (x (-7) 5)
        have b1031 := hb (x (-7) 13)
        clear * - r1029 b1030 b1031 d1020
        omega
      have d1032 : (x (-5) 11).toNat = 0 := by
        have r1033 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
        have b1034 := hb (x (-5) 3)
        have b1035 := hb (x (-5) 11)
        clear * - r1033 b1034 b1035 d997
        omega
      have d1036 : (x 4 7 && x 4 11).toNat = 0 := by
        have r1037 := hand2 (x 4 7) (x 4 11)
        have b1038 := hb (x 4 11)
        have b1039 := hb (x 4 7 && x 4 11)
        clear * - r1037 b1038 b1039 d802
        omega
      have d1040 : (x 2 2 && x 2 13).toNat = 1 := by
        have r1041 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1042 := hb (x 0 4)
        have b1043 := hb (x 4 11)
        have b1044 := hb (x 3 1 && x 3 12)
        have b1045 := hb (x 2 2 && x 2 13)
        have b1046 := hb (x 1 3 && x 1 14)
        clear * - r1041 b1042 b1043 b1044 b1045 b1046 d802 d518 g47 g5
        omega
      have d1047 : (x 2 2).toNat = 1 := by
        have r1048 := hand1 (x 2 2) (x 2 13)
        have b1049 := hb (x 2 2)
        have b1050 := hb (x 2 2 && x 2 13)
        clear * - r1048 b1049 b1050 d1040
        omega
      have d1051 : (x 2 14).toNat = 1 := by
        have r1052 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b1053 := hb (x 2 2)
        have b1054 := hb (x 2 14)
        clear * - r1052 b1053 b1054 d1047
        omega
      have d1055 : (x 1 1).toNat = 0 := by
        have r1056 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1057 := hb (x 1 1)
        have b1058 := hb (x 2 14)
        clear * - r1056 b1057 b1058 d1051
        omega
      have d1059 : (x 1 9).toNat = 0 := by
        have r1060 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
        have b1061 := hb (x 1 1)
        have b1062 := hb (x 1 9)
        clear * - r1060 b1061 b1062 d1055
        omega
      have d1063 : (x 4 12).toNat = 0 := by
        have r1064 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1065 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e1066 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b1067 := hb (x 1 3)
        have b1068 := hb (x 2 2)
        have b1069 := hb (x 3 13)
        have b1070 := hb (x 4 12)
        clear * - r1064 e1065 e1066 b1067 b1068 b1069 b1070 d1047
        omega
      have d1071 : (x 3 13).toNat = 0 := by
        have r1072 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1073 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e1074 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b1075 := hb (x 1 3)
        have b1076 := hb (x 2 2)
        have b1077 := hb (x 3 13)
        have b1078 := hb (x 4 12)
        clear * - r1072 e1073 e1074 b1075 b1076 b1077 b1078 d1063 d1047
        omega
      have d1079 : (x 1 3).toNat = 0 := by
        have r1080 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1081 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e1082 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b1083 := hb (x 1 3)
        have b1084 := hb (x 2 2)
        have b1085 := hb (x 3 13)
        have b1086 := hb (x 4 12)
        clear * - r1080 e1081 e1082 b1083 b1084 b1085 b1086 d1063 d1071 d1047
        omega
      have d1087 : (x 1 11).toNat = 0 := by
        have r1088 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b1089 := hb (x 1 3)
        have b1090 := hb (x 1 11)
        clear * - r1088 b1089 b1090 d1079
        omega
      have d1091 : (x 4 8).toNat = 0 := by
        have r1092 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1093 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e1094 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e1095 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e1096 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e1097 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e1098 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b1099 := hb (x (-3) 7)
        have b1100 := hb (x (-2) 6)
        have b1101 := hb (x (-1) 5)
        have b1102 := hb (x 0 4)
        have b1103 := hb (x 1 11)
        have b1104 := hb (x 2 10)
        have b1105 := hb (x 3 9)
        have b1106 := hb (x 4 8)
        clear * - r1092 e1093 e1094 e1095 e1096 e1097 e1098 b1099 b1100 b1101 b1102 b1103 b1104 b1105 b1106 d1087 g5 d876 d884
        omega
      have d1107 : (x 4 2 && x 4 8).toNat = 0 := by
        have r1108 := hand2 (x 4 2) (x 4 8)
        have b1109 := hb (x 4 8)
        have b1110 := hb (x 4 2 && x 4 8)
        clear * - r1108 b1109 b1110 d1091
        omega
      have d1111 : (x 3 9).toNat = 0 := by
        have r1112 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1113 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e1114 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e1115 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e1116 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e1117 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e1118 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b1119 := hb (x (-3) 7)
        have b1120 := hb (x (-2) 6)
        have b1121 := hb (x (-1) 5)
        have b1122 := hb (x 0 4)
        have b1123 := hb (x 1 11)
        have b1124 := hb (x 2 10)
        have b1125 := hb (x 3 9)
        have b1126 := hb (x 4 8)
        clear * - r1112 e1113 e1114 e1115 e1116 e1117 e1118 b1119 b1120 b1121 b1122 b1123 b1124 b1125 b1126 d1091 d1087 g5 d876 d884
        omega
      have d1127 : (x 3 3 && x 3 9).toNat = 0 := by
        have r1128 := hand2 (x 3 3) (x 3 9)
        have b1129 := hb (x 3 9)
        have b1130 := hb (x 3 3 && x 3 9)
        clear * - r1128 b1129 b1130 d1111
        omega
      have d1131 : (x 2 10).toNat = 0 := by
        have r1132 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1133 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e1134 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e1135 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e1136 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e1137 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e1138 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b1139 := hb (x (-3) 7)
        have b1140 := hb (x (-2) 6)
        have b1141 := hb (x (-1) 5)
        have b1142 := hb (x 0 4)
        have b1143 := hb (x 1 11)
        have b1144 := hb (x 2 10)
        have b1145 := hb (x 3 9)
        have b1146 := hb (x 4 8)
        clear * - r1132 e1133 e1134 e1135 e1136 e1137 e1138 b1139 b1140 b1141 b1142 b1143 b1144 b1145 b1146 d1091 d1111 d1087 g5 d876 d884
        omega
      have d1147 : (x 2 4 && x 2 10).toNat = 0 := by
        have r1148 := hand2 (x 2 4) (x 2 10)
        have b1149 := hb (x 2 10)
        have b1150 := hb (x 2 4 && x 2 10)
        clear * - r1148 b1149 b1150 d1131
        omega
      have d1151 : (x 3 8).toNat = 0 := by
        have r1152 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1153 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e1154 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e1155 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e1156 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e1157 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e1158 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b1159 := hb (x (-4) 7)
        have b1160 := hb (x (-3) 6)
        have b1161 := hb (x (-2) 5)
        have b1162 := hb (x (-1) 4)
        have b1163 := hb (x 0 11)
        have b1164 := hb (x 1 10)
        have b1165 := hb (x 2 9)
        have b1166 := hb (x 3 8)
        clear * - r1152 e1153 e1154 e1155 e1156 e1157 e1158 b1159 b1160 b1161 b1162 b1163 b1164 b1165 b1166 g9 g6 d993 d977
        omega
      have d1167 : (x 2 9).toNat = 0 := by
        have r1168 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1169 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e1170 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e1171 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e1172 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e1173 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e1174 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b1175 := hb (x (-4) 7)
        have b1176 := hb (x (-3) 6)
        have b1177 := hb (x (-2) 5)
        have b1178 := hb (x (-1) 4)
        have b1179 := hb (x 0 11)
        have b1180 := hb (x 1 10)
        have b1181 := hb (x 2 9)
        have b1182 := hb (x 3 8)
        clear * - r1168 e1169 e1170 e1171 e1172 e1173 e1174 b1175 b1176 b1177 b1178 b1179 b1180 b1181 b1182 d1151 g9 g6 d993 d977
        omega
      have d1183 : (x 2 9 && x 2 13).toNat = 0 := by
        have r1184 := hand1 (x 2 9) (x 2 13)
        have b1185 := hb (x 2 9)
        have b1186 := hb (x 2 9 && x 2 13)
        clear * - r1184 b1185 b1186 d1167
        omega
      have d1187 : (x (-2) 8).toNat = 0 := by
        have r1188 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1189 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e1190 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e1191 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e1192 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e1193 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e1194 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b1195 := hb (x (-9) 7)
        have b1196 := hb (x (-8) 6)
        have b1197 := hb (x (-7) 5)
        have b1198 := hb (x (-6) 4)
        have b1199 := hb (x (-5) 11)
        have b1200 := hb (x (-4) 10)
        have b1201 := hb (x (-3) 9)
        have b1202 := hb (x (-2) 8)
        clear * - r1188 e1189 e1190 e1191 e1192 e1193 e1194 b1195 b1196 b1197 b1198 b1199 b1200 b1201 b1202 d917 d956 d1032 d1009 d1028
        omega
      have d1203 : (x (-2) 8 && x (-2) 14).toNat = 0 := by
        have r1204 := hand1 (x (-2) 8) (x (-2) 14)
        have b1205 := hb (x (-2) 8)
        have b1206 := hb (x (-2) 8 && x (-2) 14)
        clear * - r1204 b1205 b1206 d1187
        omega
      have r1207 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1208 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1209 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e1210 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e1211 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e1212 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e1213 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e1214 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have r1215 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1216 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e1217 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e1218 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e1219 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e1220 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e1221 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have r1222 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1223 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
      have e1224 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
      have r1225 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1226 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1227 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1228 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1229 := hand2 (x 9 2) (x 9 6)
      have r1230 := hand2 (x 8 3) (x 8 7)
      have r1231 := hand2 (x 5 1) (x 5 7)
      have r1232 := hand1 (x (-4) 5) (x (-4) 14)
      have r1233 := hand2 (x 0 1) (x 0 12)
      have r1234 := hand1 (x 11 1) (x 11 12)
      have r1235 := hand1 (x 10 2) (x 10 13)
      have r1236 := hand1 (x 9 3) (x 9 14)
      linarith only [r1207, r1208, e1209, e1210, e1211, e1212, e1213, e1214, r1215, e1216, e1217, e1218, e1219, e1220, e1221, r1222, e1223, e1224, r1225, r1226, r1227, r1228, r1229, r1230, r1231, r1232, r1233, r1234, r1235, r1236, d917, g0, d893, g2, d868, g6, d1059, g9, d1087, d1131, d1111, d1091, d754, d774, d798, d1036, d526, d1183, d1107, d1127, d1147, d851, d536, d872, d1203, d485, g27, g28, d913, g42, g43]
  · have f1298 : (x 0 6).toNat = 1 := by rw [h534]; rfl
    have d1299 : (x 0 14).toNat = 1 := by
      have r1300 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
      have b1301 := hb (x 0 6)
      have b1302 := hb (x 0 14)
      clear * - r1300 b1301 b1302 f1298
      omega
    have d1303 : (x (-1) 1).toNat = 0 := by
      have r1304 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1305 := hb (x (-1) 1)
      have b1306 := hb (x 0 14)
      clear * - r1304 b1305 b1306 d1299
      omega
    have d1307 : (x (-1) 13).toNat = 0 := by
      have r1308 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b1309 := hb (x (-1) 1)
      have b1310 := hb (x (-1) 13)
      clear * - r1308 b1309 b1310 d1303
      omega
    have d1311 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
      have r1312 := hand2 (x (-1) 3) (x (-1) 13)
      have b1313 := hb (x (-1) 13)
      have b1314 := hb (x (-1) 3 && x (-1) 13)
      clear * - r1312 b1313 b1314 d1307
      omega
    have d1315 : (x (-1) 5).toNat = 0 := by
      have r1316 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
      have b1317 := hb (x (-1) 5)
      have b1318 := hb (x (-1) 13)
      clear * - r1316 b1317 b1318 d1307
      omega
    have d1319 : (x (-1) 5 && x (-1) 14).toNat = 0 := by
      have r1320 := hand1 (x (-1) 5) (x (-1) 14)
      have b1321 := hb (x (-1) 5)
      have b1322 := hb (x (-1) 5 && x (-1) 14)
      clear * - r1320 b1321 b1322 d1315
      omega
    have d1323 : (x (-2) 6).toNat = 1 := by
      have r1324 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1325 := hb (x (-2) 6)
      have b1326 := hb (x 4 9)
      have b1327 := hb (x 3 1 && x 3 10)
      have b1328 := hb (x 2 2 && x 2 11)
      have b1329 := hb (x 1 3 && x 1 12)
      have b1330 := hb (x 0 4 && x 0 13)
      have b1331 := hb (x (-1) 5 && x (-1) 14)
      clear * - r1324 b1325 b1326 b1327 b1328 b1329 b1330 b1331 g12 g29 g30 g31 g32 d1319
      omega
    have d1332 : (x (-2) 14).toNat = 1 := by
      have r1333 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
      have b1334 := hb (x (-2) 6)
      have b1335 := hb (x (-2) 14)
      clear * - r1333 b1334 b1335 d1323
      omega
    have d1336 : (x (-3) 1).toNat = 0 := by
      have r1337 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1338 := hb (x (-3) 1)
      have b1339 := hb (x (-2) 14)
      clear * - r1337 b1338 b1339 d1332
      omega
    have d1340 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
      have r1341 := hand1 (x (-3) 1) (x (-3) 14)
      have b1342 := hb (x (-3) 1)
      have b1343 := hb (x (-3) 1 && x (-3) 14)
      clear * - r1341 b1342 b1343 d1336
      omega
    have d1344 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
      have r1345 := hand1 (x (-3) 1) (x (-3) 12)
      have b1346 := hb (x (-3) 1)
      have b1347 := hb (x (-3) 1 && x (-3) 12)
      clear * - r1345 b1346 b1347 d1336
      omega
    have d1348 : (x (-3) 13).toNat = 0 := by
      have r1349 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b1350 := hb (x (-3) 1)
      have b1351 := hb (x (-3) 13)
      clear * - r1349 b1350 b1351 d1336
      omega
    have d1352 : (x (-3) 5).toNat = 0 := by
      have r1353 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have b1354 := hb (x (-3) 5)
      have b1355 := hb (x (-3) 13)
      clear * - r1353 b1354 b1355 d1348
      omega
    have d1356 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
      have r1357 := hand1 (x (-3) 5) (x (-3) 9)
      have b1358 := hb (x (-3) 5)
      have b1359 := hb (x (-3) 5 && x (-3) 9)
      clear * - r1357 b1358 b1359 d1352
      omega
    have d1360 : (x (-3) 9).toNat = 0 := by
      have r1361 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
      have b1362 := hb (x (-3) 1)
      have b1363 := hb (x (-3) 9)
      clear * - r1361 b1362 b1363 d1336
      omega
    have d1364 : (x 6 8).toNat = 0 := by
      have r1365 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1366 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e1367 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e1368 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e1369 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e1370 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e1371 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b1372 := hb (x (-1) 7)
      have b1373 := hb (x 0 6)
      have b1374 := hb (x 1 5)
      have b1375 := hb (x 2 4)
      have b1376 := hb (x 3 11)
      have b1377 := hb (x 4 10)
      have b1378 := hb (x 5 9)
      have b1379 := hb (x 6 8)
      clear * - r1365 e1366 e1367 e1368 e1369 e1370 e1371 b1372 b1373 b1374 b1375 b1376 b1377 b1378 b1379 f1298
      omega
    have d1380 : (x 5 9).toNat = 0 := by
      have r1381 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1382 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e1383 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e1384 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e1385 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e1386 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e1387 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b1388 := hb (x (-1) 7)
      have b1389 := hb (x 0 6)
      have b1390 := hb (x 1 5)
      have b1391 := hb (x 2 4)
      have b1392 := hb (x 3 11)
      have b1393 := hb (x 4 10)
      have b1394 := hb (x 5 9)
      have b1395 := hb (x 6 8)
      clear * - r1381 e1382 e1383 e1384 e1385 e1386 e1387 b1388 b1389 b1390 b1391 b1392 b1393 b1394 b1395 d1364 f1298
      omega
    have d1396 : (x 4 10).toNat = 0 := by
      have r1397 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1398 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e1399 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e1400 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e1401 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e1402 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e1403 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b1404 := hb (x (-1) 7)
      have b1405 := hb (x 0 6)
      have b1406 := hb (x 1 5)
      have b1407 := hb (x 2 4)
      have b1408 := hb (x 3 11)
      have b1409 := hb (x 4 10)
      have b1410 := hb (x 5 9)
      have b1411 := hb (x 6 8)
      clear * - r1397 e1398 e1399 e1400 e1401 e1402 e1403 b1404 b1405 b1406 b1407 b1408 b1409 b1410 b1411 d1364 d1380 f1298
      omega
    have d1412 : (x 3 11).toNat = 0 := by
      have r1413 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1414 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e1415 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e1416 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e1417 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e1418 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e1419 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b1420 := hb (x (-1) 7)
      have b1421 := hb (x 0 6)
      have b1422 := hb (x 1 5)
      have b1423 := hb (x 2 4)
      have b1424 := hb (x 3 11)
      have b1425 := hb (x 4 10)
      have b1426 := hb (x 5 9)
      have b1427 := hb (x 6 8)
      clear * - r1413 e1414 e1415 e1416 e1417 e1418 e1419 b1420 b1421 b1422 b1423 b1424 b1425 b1426 b1427 d1364 d1380 d1396 f1298
      omega
    have d1428 : (x 3 1 && x 3 11).toNat = 0 := by
      have r1429 := hand2 (x 3 1) (x 3 11)
      have b1430 := hb (x 3 11)
      have b1431 := hb (x 3 1 && x 3 11)
      clear * - r1429 b1430 b1431 d1412
      omega
    have d1432 : (x 2 4).toNat = 0 := by
      have r1433 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1434 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e1435 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e1436 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e1437 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e1438 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e1439 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b1440 := hb (x (-1) 7)
      have b1441 := hb (x 0 6)
      have b1442 := hb (x 1 5)
      have b1443 := hb (x 2 4)
      have b1444 := hb (x 3 11)
      have b1445 := hb (x 4 10)
      have b1446 := hb (x 5 9)
      have b1447 := hb (x 6 8)
      clear * - r1433 e1434 e1435 e1436 e1437 e1438 e1439 b1440 b1441 b1442 b1443 b1444 b1445 b1446 b1447 d1364 d1380 d1396 d1412 f1298
      omega
    have d1448 : (x 1 5).toNat = 0 := by
      have r1449 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1450 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e1451 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e1452 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e1453 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e1454 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e1455 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b1456 := hb (x (-1) 7)
      have b1457 := hb (x 0 6)
      have b1458 := hb (x 1 5)
      have b1459 := hb (x 2 4)
      have b1460 := hb (x 3 11)
      have b1461 := hb (x 4 10)
      have b1462 := hb (x 5 9)
      have b1463 := hb (x 6 8)
      clear * - r1449 e1450 e1451 e1452 e1453 e1454 e1455 b1456 b1457 b1458 b1459 b1460 b1461 b1462 b1463 d1364 d1380 d1396 d1412 d1432 f1298
      omega
    have d1464 : (x (-1) 7).toNat = 0 := by
      have r1465 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1466 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e1467 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e1468 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e1469 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e1470 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e1471 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b1472 := hb (x (-1) 7)
      have b1473 := hb (x 0 6)
      have b1474 := hb (x 1 5)
      have b1475 := hb (x 2 4)
      have b1476 := hb (x 3 11)
      have b1477 := hb (x 4 10)
      have b1478 := hb (x 5 9)
      have b1479 := hb (x 6 8)
      clear * - r1465 e1466 e1467 e1468 e1469 e1470 e1471 b1472 b1473 b1474 b1475 b1476 b1477 b1478 b1479 d1364 d1380 d1396 d1412 d1432 d1448 f1298
      omega
    have d1480 : (x (-1) 3 && x (-1) 7).toNat = 0 := by
      have r1481 := hand2 (x (-1) 3) (x (-1) 7)
      have b1482 := hb (x (-1) 7)
      have b1483 := hb (x (-1) 3 && x (-1) 7)
      clear * - r1481 b1482 b1483 d1464
      omega
    have d1484 : (x 4 8).toNat = 0 := by
      have r1485 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1486 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e1487 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e1488 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e1489 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e1490 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e1491 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b1492 := hb (x (-3) 7)
      have b1493 := hb (x (-2) 6)
      have b1494 := hb (x (-1) 5)
      have b1495 := hb (x 0 4)
      have b1496 := hb (x 1 11)
      have b1497 := hb (x 2 10)
      have b1498 := hb (x 3 9)
      have b1499 := hb (x 4 8)
      clear * - r1485 e1486 e1487 e1488 e1489 e1490 e1491 b1492 b1493 b1494 b1495 b1496 b1497 b1498 b1499 g5 d1315 d1323
      omega
    have d1500 : (x 3 9).toNat = 0 := by
      have r1501 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1502 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e1503 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e1504 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e1505 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e1506 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e1507 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b1508 := hb (x (-3) 7)
      have b1509 := hb (x (-2) 6)
      have b1510 := hb (x (-1) 5)
      have b1511 := hb (x 0 4)
      have b1512 := hb (x 1 11)
      have b1513 := hb (x 2 10)
      have b1514 := hb (x 3 9)
      have b1515 := hb (x 4 8)
      clear * - r1501 e1502 e1503 e1504 e1505 e1506 e1507 b1508 b1509 b1510 b1511 b1512 b1513 b1514 b1515 d1484 g5 d1315 d1323
      omega
    have d1516 : (x 2 10).toNat = 0 := by
      have r1517 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1518 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e1519 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e1520 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e1521 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e1522 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e1523 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b1524 := hb (x (-3) 7)
      have b1525 := hb (x (-2) 6)
      have b1526 := hb (x (-1) 5)
      have b1527 := hb (x 0 4)
      have b1528 := hb (x 1 11)
      have b1529 := hb (x 2 10)
      have b1530 := hb (x 3 9)
      have b1531 := hb (x 4 8)
      clear * - r1517 e1518 e1519 e1520 e1521 e1522 e1523 b1524 b1525 b1526 b1527 b1528 b1529 b1530 b1531 d1484 d1500 g5 d1315 d1323
      omega
    have d1532 : (x 1 11).toNat = 0 := by
      have r1533 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1534 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e1535 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e1536 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e1537 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e1538 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e1539 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b1540 := hb (x (-3) 7)
      have b1541 := hb (x (-2) 6)
      have b1542 := hb (x (-1) 5)
      have b1543 := hb (x 0 4)
      have b1544 := hb (x 1 11)
      have b1545 := hb (x 2 10)
      have b1546 := hb (x 3 9)
      have b1547 := hb (x 4 8)
      clear * - r1533 e1534 e1535 e1536 e1537 e1538 e1539 b1540 b1541 b1542 b1543 b1544 b1545 b1546 b1547 d1484 d1500 d1516 g5 d1315 d1323
      omega
    have d1548 : (x 1 1 && x 1 11).toNat = 0 := by
      have r1549 := hand2 (x 1 1) (x 1 11)
      have b1550 := hb (x 1 11)
      have b1551 := hb (x 1 1 && x 1 11)
      clear * - r1549 b1550 b1551 d1532
      omega
    have d1552 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
      have r1553 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1554 := hb (x (-3) 5)
      have b1555 := hb (x 2 10)
      have b1556 := hb (x 1 1 && x 1 11)
      have b1557 := hb (x 0 2 && x 0 12)
      have b1558 := hb (x (-1) 3 && x (-1) 13)
      have b1559 := hb (x (-2) 4 && x (-2) 14)
      clear * - r1553 b1554 b1555 b1556 b1557 b1558 b1559 d1516 d1548 d473 d1311 d1352
      omega
    have d1560 : (x (-2) 4).toNat = 1 := by
      have r1561 := hand1 (x (-2) 4) (x (-2) 14)
      have b1562 := hb (x (-2) 4)
      have b1563 := hb (x (-2) 4 && x (-2) 14)
      clear * - r1561 b1562 b1563 d1552
      omega
    have d1564 : (x (-2) 12).toNat = 1 := by
      have r1565 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have b1566 := hb (x (-2) 4)
      have b1567 := hb (x (-2) 12)
      clear * - r1565 b1566 b1567 d1560
      omega
    have d1568 : (x (-4) 2).toNat = 0 := by
      have r1569 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1570 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e1571 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b1572 := hb (x (-5) 3)
      have b1573 := hb (x (-4) 2)
      have b1574 := hb (x (-3) 13)
      have b1575 := hb (x (-2) 12)
      clear * - r1569 e1570 e1571 b1572 b1573 b1574 b1575 d1564 d1348
      omega
    have d1576 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
      have r1577 := hand1 (x (-4) 2) (x (-4) 13)
      have b1578 := hb (x (-4) 2)
      have b1579 := hb (x (-4) 2 && x (-4) 13)
      clear * - r1577 b1578 b1579 d1568
      omega
    have d1580 : (x (-4) 10).toNat = 0 := by
      have r1581 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
      have b1582 := hb (x (-4) 2)
      have b1583 := hb (x (-4) 10)
      clear * - r1581 b1582 b1583 d1568
      omega
    have d1584 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
      have r1585 := hand2 (x (-4) 6) (x (-4) 10)
      have b1586 := hb (x (-4) 10)
      have b1587 := hb (x (-4) 6 && x (-4) 10)
      clear * - r1585 b1586 b1587 d1580
      omega
    have d1588 : (x (-2) 13).toNat = 1 := by
      have r1589 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1590 := hb (x (-4) 2)
      have b1591 := hb (x (-2) 13)
      have b1592 := hb (x (-3) 1 && x (-3) 14)
      clear * - r1589 b1590 b1591 b1592 d1340 d1568
      omega
    have d1593 : (x (-2) 1).toNat = 1 := by
      have r1594 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b1595 := hb (x (-2) 1)
      have b1596 := hb (x (-2) 13)
      clear * - r1594 b1595 b1596 d1588
      omega
    have d1597 : (x (-1) 14).toNat = 0 := by
      have r1598 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1599 := hb (x (-2) 1)
      have b1600 := hb (x (-1) 14)
      clear * - r1598 b1599 b1600 d1593
      omega
    have d1601 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
      have r1602 := hand2 (x (-1) 4) (x (-1) 14)
      have b1603 := hb (x (-1) 14)
      have b1604 := hb (x (-1) 4 && x (-1) 14)
      clear * - r1602 b1603 b1604 d1597
      omega
    have d1605 : (x (-2) 5).toNat = 1 := by
      have r1606 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1607 := hb (x (-2) 5)
      have b1608 := hb (x 3 10)
      have b1609 := hb (x 2 1 && x 2 11)
      have b1610 := hb (x 1 2 && x 1 12)
      have b1611 := hb (x 0 3 && x 0 13)
      have b1612 := hb (x (-1) 4 && x (-1) 14)
      clear * - r1606 b1607 b1608 b1609 b1610 b1611 b1612 g11 g38 g39 g40 d1601
      omega
    have d1613 : (x (-1) 12).toNat = 0 := by
      have r1614 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1615 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e1616 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b1617 := hb (x (-4) 3)
      have b1618 := hb (x (-3) 2)
      have b1619 := hb (x (-2) 13)
      have b1620 := hb (x (-1) 12)
      clear * - r1614 e1615 e1616 b1617 b1618 b1619 b1620 d1588
      omega
    have d1621 : (x (-1) 4).toNat = 0 := by
      have r1622 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b1623 := hb (x (-1) 4)
      have b1624 := hb (x (-1) 12)
      clear * - r1622 b1623 b1624 d1613
      omega
    have d1625 : (x 2 1 && x 2 12).toNat = 1 := by
      have r1626 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1627 := hb (x (-1) 4)
      have b1628 := hb (x 3 11)
      have b1629 := hb (x 2 1 && x 2 12)
      have b1630 := hb (x 1 2 && x 1 13)
      have b1631 := hb (x 0 3 && x 0 14)
      clear * - r1626 b1627 b1628 b1629 b1630 b1631 d1412 g45 g46 d1621
      omega
    have d1632 : (x 2 12).toNat = 1 := by
      have r1633 := hand2 (x 2 1) (x 2 12)
      have b1634 := hb (x 2 12)
      have b1635 := hb (x 2 1 && x 2 12)
      clear * - r1633 b1634 b1635 d1625
      omega
    have d1636 : (x 1 13).toNat = 0 := by
      have r1637 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1638 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e1639 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b1640 := hb (x (-1) 3)
      have b1641 := hb (x 0 2)
      have b1642 := hb (x 1 13)
      have b1643 := hb (x 2 12)
      clear * - r1637 e1638 e1639 b1640 b1641 b1642 b1643 d1632 g3
      omega
    have d1644 : (x 1 3 && x 1 13).toNat = 0 := by
      have r1645 := hand2 (x 1 3) (x 1 13)
      have b1646 := hb (x 1 13)
      have b1647 := hb (x 1 3 && x 1 13)
      clear * - r1645 b1646 b1647 d1636
      omega
    have d1648 : (x 2 2 && x 2 12).toNat = 1 := by
      have r1649 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1650 := hb (x (-1) 5)
      have b1651 := hb (x 4 10)
      have b1652 := hb (x 3 1 && x 3 11)
      have b1653 := hb (x 2 2 && x 2 12)
      have b1654 := hb (x 1 3 && x 1 13)
      have b1655 := hb (x 0 4 && x 0 14)
      clear * - r1649 b1650 b1651 b1652 b1653 b1654 b1655 d1396 d1428 d1644 g41 d1315
      omega
    have d1656 : (x 2 2).toNat = 1 := by
      have r1657 := hand1 (x 2 2) (x 2 12)
      have b1658 := hb (x 2 2)
      have b1659 := hb (x 2 2 && x 2 12)
      clear * - r1657 b1658 b1659 d1648
      omega
    have d1660 : (x 4 12).toNat = 0 := by
      have r1661 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1662 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e1663 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b1664 := hb (x 1 3)
      have b1665 := hb (x 2 2)
      have b1666 := hb (x 3 13)
      have b1667 := hb (x 4 12)
      clear * - r1661 e1662 e1663 b1664 b1665 b1666 b1667 d1656
      omega
    have d1668 : (x 3 13).toNat = 0 := by
      have r1669 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1670 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e1671 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b1672 := hb (x 1 3)
      have b1673 := hb (x 2 2)
      have b1674 := hb (x 3 13)
      have b1675 := hb (x 4 12)
      clear * - r1669 e1670 e1671 b1672 b1673 b1674 b1675 d1660 d1656
      omega
    have d1676 : (x 1 3).toNat = 0 := by
      have r1677 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1678 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e1679 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b1680 := hb (x 1 3)
      have b1681 := hb (x 2 2)
      have b1682 := hb (x 3 13)
      have b1683 := hb (x 4 12)
      clear * - r1677 e1678 e1679 b1680 b1681 b1682 b1683 d1660 d1668 d1656
      omega
    have d1684 : (x (-5) 3).toNat = 0 := by
      have r1685 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1686 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e1687 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b1688 := hb (x (-5) 3)
      have b1689 := hb (x (-4) 2)
      have b1690 := hb (x (-3) 13)
      have b1691 := hb (x (-2) 12)
      clear * - r1685 e1686 e1687 b1688 b1689 b1690 b1691 d1564 d1348 d1568
      omega
    have d1692 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
      have r1693 := hand1 (x (-5) 3) (x (-5) 14)
      have b1694 := hb (x (-5) 3)
      have b1695 := hb (x (-5) 3 && x (-5) 14)
      clear * - r1693 b1694 b1695 d1684
      omega
    have d1696 : (x (-6) 4).toNat = 1 := by
      have r1697 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1698 := hb (x (-6) 4)
      have b1699 := hb (x (-2) 11)
      have b1700 := hb (x (-3) 1 && x (-3) 12)
      have b1701 := hb (x (-4) 2 && x (-4) 13)
      have b1702 := hb (x (-5) 3 && x (-5) 14)
      clear * - r1697 b1698 b1699 b1700 b1701 b1702 g0 d1344 d1576 d1692
      omega
    have d1703 : (x (-6) 12).toNat = 1 := by
      have r1704 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have b1705 := hb (x (-6) 4)
      have b1706 := hb (x (-6) 12)
      clear * - r1704 b1705 b1706 d1696
      omega
    have d1707 : (x (-7) 13).toNat = 0 := by
      have r1708 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1709 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e1710 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b1711 := hb (x (-9) 3)
      have b1712 := hb (x (-8) 2)
      have b1713 := hb (x (-7) 13)
      have b1714 := hb (x (-6) 12)
      clear * - r1708 e1709 e1710 b1711 b1712 b1713 b1714 d1703
      omega
    have d1715 : (x (-7) 9 && x (-7) 13).toNat = 0 := by
      have r1716 := hand2 (x (-7) 9) (x (-7) 13)
      have b1717 := hb (x (-7) 13)
      have b1718 := hb (x (-7) 9 && x (-7) 13)
      clear * - r1716 b1717 b1718 d1707
      omega
    have d1719 : (x (-7) 5).toNat = 0 := by
      have r1720 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b1721 := hb (x (-7) 5)
      have b1722 := hb (x (-7) 13)
      clear * - r1720 b1721 b1722 d1707
      omega
    have d1723 : (x (-8) 2).toNat = 0 := by
      have r1724 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1725 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e1726 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b1727 := hb (x (-9) 3)
      have b1728 := hb (x (-8) 2)
      have b1729 := hb (x (-7) 13)
      have b1730 := hb (x (-6) 12)
      clear * - r1724 e1725 e1726 b1727 b1728 b1729 b1730 d1703 d1707
      omega
    have d1731 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
      have r1732 := hand1 (x (-8) 2) (x (-8) 12)
      have b1733 := hb (x (-8) 2)
      have b1734 := hb (x (-8) 2 && x (-8) 12)
      clear * - r1732 b1733 b1734 d1723
      omega
    have d1735 : (x (-8) 2 && x (-8) 11).toNat = 0 := by
      have r1736 := hand1 (x (-8) 2) (x (-8) 11)
      have b1737 := hb (x (-8) 2)
      have b1738 := hb (x (-8) 2 && x (-8) 11)
      clear * - r1736 b1737 b1738 d1723
      omega
    have d1739 : (x (-8) 10).toNat = 0 := by
      have r1740 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have b1741 := hb (x (-8) 2)
      have b1742 := hb (x (-8) 10)
      clear * - r1740 b1741 b1742 d1723
      omega
    have d1743 : (x (-9) 3).toNat = 0 := by
      have r1744 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1745 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e1746 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b1747 := hb (x (-9) 3)
      have b1748 := hb (x (-8) 2)
      have b1749 := hb (x (-7) 13)
      have b1750 := hb (x (-6) 12)
      clear * - r1744 e1745 e1746 b1747 b1748 b1749 b1750 d1703 d1707 d1723
      omega
    have d1751 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
      have r1752 := hand1 (x (-9) 3) (x (-9) 13)
      have b1753 := hb (x (-9) 3)
      have b1754 := hb (x (-9) 3 && x (-9) 13)
      clear * - r1752 b1753 b1754 d1743
      omega
    have d1755 : (x (-9) 3 && x (-9) 12).toNat = 0 := by
      have r1756 := hand1 (x (-9) 3) (x (-9) 12)
      have b1757 := hb (x (-9) 3)
      have b1758 := hb (x (-9) 3 && x (-9) 12)
      clear * - r1756 b1757 b1758 d1743
      omega
    have d1759 : (x (-9) 11).toNat = 0 := by
      have r1760 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
      have b1761 := hb (x (-9) 3)
      have b1762 := hb (x (-9) 11)
      clear * - r1760 b1761 b1762 d1743
      omega
    have d1763 : (x (-5) 11).toNat = 0 := by
      have r1764 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b1765 := hb (x (-5) 3)
      have b1766 := hb (x (-5) 11)
      clear * - r1764 b1765 b1766 d1684
      omega
    have d1767 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
      have r1768 := hand2 (x (-5) 7) (x (-5) 11)
      have b1769 := hb (x (-5) 11)
      have b1770 := hb (x (-5) 7 && x (-5) 11)
      clear * - r1768 b1769 b1770 d1763
      omega
    have d1771 : (x (-3) 7).toNat = 0 := by
      have r1772 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1773 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e1774 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e1775 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e1776 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e1777 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e1778 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b1779 := hb (x (-3) 7)
      have b1780 := hb (x (-2) 6)
      have b1781 := hb (x (-1) 5)
      have b1782 := hb (x 0 4)
      have b1783 := hb (x 1 11)
      have b1784 := hb (x 2 10)
      have b1785 := hb (x 3 9)
      have b1786 := hb (x 4 8)
      clear * - r1772 e1773 e1774 e1775 e1776 e1777 e1778 b1779 b1780 b1781 b1782 b1783 b1784 b1785 b1786 d1484 d1500 d1516 d1532 g5 d1315 d1323
      omega
    have d1787 : (x 3 8).toNat = 0 := by
      have r1788 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1789 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e1790 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e1791 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e1792 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e1793 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e1794 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b1795 := hb (x (-4) 7)
      have b1796 := hb (x (-3) 6)
      have b1797 := hb (x (-2) 5)
      have b1798 := hb (x (-1) 4)
      have b1799 := hb (x 0 11)
      have b1800 := hb (x 1 10)
      have b1801 := hb (x 2 9)
      have b1802 := hb (x 3 8)
      clear * - r1788 e1789 e1790 e1791 e1792 e1793 e1794 b1795 b1796 b1797 b1798 b1799 b1800 b1801 b1802 g9 g6 d1621 d1605
      omega
    have d1803 : (x 2 9).toNat = 0 := by
      have r1804 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1805 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e1806 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e1807 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e1808 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e1809 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e1810 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b1811 := hb (x (-4) 7)
      have b1812 := hb (x (-3) 6)
      have b1813 := hb (x (-2) 5)
      have b1814 := hb (x (-1) 4)
      have b1815 := hb (x 0 11)
      have b1816 := hb (x 1 10)
      have b1817 := hb (x 2 9)
      have b1818 := hb (x 3 8)
      clear * - r1804 e1805 e1806 e1807 e1808 e1809 e1810 b1811 b1812 b1813 b1814 b1815 b1816 b1817 b1818 d1787 g9 g6 d1621 d1605
      omega
    have d1819 : (x (-3) 6).toNat = 0 := by
      have r1820 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1821 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e1822 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e1823 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e1824 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e1825 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e1826 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b1827 := hb (x (-4) 7)
      have b1828 := hb (x (-3) 6)
      have b1829 := hb (x (-2) 5)
      have b1830 := hb (x (-1) 4)
      have b1831 := hb (x 0 11)
      have b1832 := hb (x 1 10)
      have b1833 := hb (x 2 9)
      have b1834 := hb (x 3 8)
      clear * - r1820 e1821 e1822 e1823 e1824 e1825 e1826 b1827 b1828 b1829 b1830 b1831 b1832 b1833 b1834 d1787 d1803 g9 g6 d1621 d1605
      omega
    have d1835 : (x (-4) 7).toNat = 0 := by
      have r1836 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1837 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e1838 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e1839 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e1840 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e1841 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e1842 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b1843 := hb (x (-4) 7)
      have b1844 := hb (x (-3) 6)
      have b1845 := hb (x (-2) 5)
      have b1846 := hb (x (-1) 4)
      have b1847 := hb (x 0 11)
      have b1848 := hb (x 1 10)
      have b1849 := hb (x 2 9)
      have b1850 := hb (x 3 8)
      clear * - r1836 e1837 e1838 e1839 e1840 e1841 e1842 b1843 b1844 b1845 b1846 b1847 b1848 b1849 b1850 d1787 d1803 g9 g6 d1621 d1605 d1819
      omega
    have d1851 : (x (-2) 8).toNat = 0 := by
      have r1852 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1853 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e1854 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e1855 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e1856 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e1857 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e1858 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have b1859 := hb (x (-9) 7)
      have b1860 := hb (x (-8) 6)
      have b1861 := hb (x (-7) 5)
      have b1862 := hb (x (-6) 4)
      have b1863 := hb (x (-5) 11)
      have b1864 := hb (x (-4) 10)
      have b1865 := hb (x (-3) 9)
      have b1866 := hb (x (-2) 8)
      clear * - r1852 e1853 e1854 e1855 e1856 e1857 e1858 b1859 b1860 b1861 b1862 b1863 b1864 b1865 b1866 d1360 d1580 d1763 d1696 d1719
      omega
    have d1867 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
      have r1868 := hand2 (x (-2) 4) (x (-2) 8)
      have b1869 := hb (x (-2) 8)
      have b1870 := hb (x (-2) 4 && x (-2) 8)
      clear * - r1868 b1869 b1870 d1851
      omega
    have d1871 : (x (-6) 8 && x (-6) 12).toNat = 1 := by
      have r1872 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1873 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
      have e1874 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
      have b1875 := hb (x (-9) 11)
      have b1876 := hb (x (-8) 10)
      have b1877 := hb (x 1 5)
      have b1878 := hb (x 2 4)
      have b1879 := hb (x 0 2 && x 0 6)
      have b1880 := hb (x (-1) 3 && x (-1) 7)
      have b1881 := hb (x (-2) 4 && x (-2) 8)
      have b1882 := hb (x (-3) 5 && x (-3) 9)
      have b1883 := hb (x (-4) 6 && x (-4) 10)
      have b1884 := hb (x (-5) 7 && x (-5) 11)
      have b1885 := hb (x (-6) 8 && x (-6) 12)
      have b1886 := hb (x (-7) 9 && x (-7) 13)
      clear * - r1872 e1873 e1874 b1875 b1876 b1877 b1878 b1879 b1880 b1881 b1882 b1883 b1884 b1885 b1886 d1432 d1448 d477 d1480 d1867 d1356 d1584 d1767 d1715 d1739 d1759
      omega
    have d1887 : (x (-6) 8).toNat = 1 := by
      have r1888 := hand1 (x (-6) 8) (x (-6) 12)
      have b1889 := hb (x (-6) 8)
      have b1890 := hb (x (-6) 8 && x (-6) 12)
      clear * - r1888 b1889 b1890 d1871
      omega
    have d1891 : (x (-7) 9).toNat = 0 := by
      have r1892 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1893 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e1894 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e1895 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e1896 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e1897 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e1898 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b1899 := hb (x (-13) 7)
      have b1900 := hb (x (-12) 6)
      have b1901 := hb (x (-11) 5)
      have b1902 := hb (x (-10) 4)
      have b1903 := hb (x (-9) 11)
      have b1904 := hb (x (-8) 10)
      have b1905 := hb (x (-7) 9)
      have b1906 := hb (x (-6) 8)
      clear * - r1892 e1893 e1894 e1895 e1896 e1897 e1898 b1899 b1900 b1901 b1902 b1903 b1904 b1905 b1906 d1887 d1739 d1759
      omega
    have d1907 : (x (-10) 4).toNat = 0 := by
      have r1908 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1909 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e1910 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e1911 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e1912 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e1913 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e1914 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b1915 := hb (x (-13) 7)
      have b1916 := hb (x (-12) 6)
      have b1917 := hb (x (-11) 5)
      have b1918 := hb (x (-10) 4)
      have b1919 := hb (x (-9) 11)
      have b1920 := hb (x (-8) 10)
      have b1921 := hb (x (-7) 9)
      have b1922 := hb (x (-6) 8)
      clear * - r1908 e1909 e1910 e1911 e1912 e1913 e1914 b1915 b1916 b1917 b1918 b1919 b1920 b1921 b1922 d1887 d1891 d1739 d1759
      omega
    have d1923 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
      have r1924 := hand1 (x (-10) 4) (x (-10) 14)
      have b1925 := hb (x (-10) 4)
      have b1926 := hb (x (-10) 4 && x (-10) 14)
      clear * - r1924 b1925 b1926 d1907
      omega
    have d1927 : (x (-10) 4 && x (-10) 13).toNat = 0 := by
      have r1928 := hand1 (x (-10) 4) (x (-10) 13)
      have b1929 := hb (x (-10) 4)
      have b1930 := hb (x (-10) 4 && x (-10) 13)
      clear * - r1928 b1929 b1930 d1907
      omega
    have d1931 : (x (-11) 5).toNat = 0 := by
      have r1932 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1933 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e1934 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e1935 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e1936 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e1937 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e1938 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b1939 := hb (x (-13) 7)
      have b1940 := hb (x (-12) 6)
      have b1941 := hb (x (-11) 5)
      have b1942 := hb (x (-10) 4)
      have b1943 := hb (x (-9) 11)
      have b1944 := hb (x (-8) 10)
      have b1945 := hb (x (-7) 9)
      have b1946 := hb (x (-6) 8)
      clear * - r1932 e1933 e1934 e1935 e1936 e1937 e1938 b1939 b1940 b1941 b1942 b1943 b1944 b1945 b1946 d1887 d1891 d1739 d1759 d1907
      omega
    have d1947 : (x (-11) 5 && x (-11) 14).toNat = 0 := by
      have r1948 := hand1 (x (-11) 5) (x (-11) 14)
      have b1949 := hb (x (-11) 5)
      have b1950 := hb (x (-11) 5 && x (-11) 14)
      clear * - r1948 b1949 b1950 d1931
      omega
    have d1951 : (x (-12) 6).toNat = 0 := by
      have r1952 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1953 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e1954 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e1955 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e1956 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e1957 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e1958 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b1959 := hb (x (-13) 7)
      have b1960 := hb (x (-12) 6)
      have b1961 := hb (x (-11) 5)
      have b1962 := hb (x (-10) 4)
      have b1963 := hb (x (-9) 11)
      have b1964 := hb (x (-8) 10)
      have b1965 := hb (x (-7) 9)
      have b1966 := hb (x (-6) 8)
      clear * - r1952 e1953 e1954 e1955 e1956 e1957 e1958 b1959 b1960 b1961 b1962 b1963 b1964 b1965 b1966 d1887 d1891 d1739 d1759 d1907 d1931
      omega
    have r1967 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r1968 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r1969 : 1 ≤ (x (-6) 9).toNat + (x (-7) 1 && x (-7) 10).toNat + (x (-8) 2 && x (-8) 11).toNat + (x (-9) 3 && x (-9) 12).toNat + (x (-10) 4 && x (-10) 13).toNat + (x (-11) 5 && x (-11) 14).toNat + (x (-12) 6).toNat := by have q := hcov9 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r1970 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r1971 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r1972 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
    have r1973 := hand2 (x (-7) 1) (x (-7) 10)
    have r1974 := hand2 (x (-7) 1) (x (-7) 11)
    have r1975 := hand2 (x (-10) 1) (x (-10) 14)
    linarith only [r1967, r1968, r1969, r1970, r1971, r1972, r1973, r1974, r1975, d1951, d1931, d1835, d1819, d1771, d1605, d1323, d1621, d1315, g4, g5, g7, d1676, d494, d1656, d1735, d1755, d1927, d1947, d1731, d1751, d1923]

theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b00 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 2).toNat = 0)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 3).toNat = 0)
    (g5 : (x 0 4).toNat = 0)
    (g6 : (x 0 11).toNat = 0)
    (g7 : (x 1 2).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 2 11).toNat = 0)
    (g11 : (x 3 10).toNat = 0)
    (g12 : (x 4 9).toNat = 0)
    (g13 : (x 5 4 && x 5 8).toNat = 0)
    (g14 : (x 4 5 && x 4 9).toNat = 0)
    (g15 : (x 3 6 && x 3 10).toNat = 0)
    (g16 : (x 2 7 && x 2 11).toNat = 0)
    (g17 : (x 1 8 && x 1 12).toNat = 0)
    (g18 : (x 1 4 && x 1 10).toNat = 0)
    (g19 : (x 0 5 && x 0 11).toNat = 0)
    (g20 : (x (-1) 6 && x (-1) 12).toNat = 0)
    (g21 : (x (-2) 7 && x (-2) 13).toNat = 0)
    (g22 : (x 5 2 && x 5 8).toNat = 0)
    (g23 : (x 4 3 && x 4 9).toNat = 0)
    (g24 : (x 3 4 && x 3 10).toNat = 0)
    (g25 : (x 2 5 && x 2 11).toNat = 0)
    (g26 : (x 1 6 && x 1 12).toNat = 0)
    (g27 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g28 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g29 : (x 3 1 && x 3 10).toNat = 0)
    (g30 : (x 2 2 && x 2 11).toNat = 0)
    (g31 : (x 1 3 && x 1 12).toNat = 0)
    (g32 : (x 0 4 && x 0 13).toNat = 0)
    (g33 : (x 1 5 && x 1 14).toNat = 0)
    (g34 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g35 : (x 0 1 && x 0 11).toNat = 0)
    (g36 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g37 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g38 : (x 2 1 && x 2 11).toNat = 0)
    (g39 : (x 1 2 && x 1 12).toNat = 0)
    (g40 : (x 0 3 && x 0 13).toNat = 0)
    (g41 : (x 0 4 && x 0 14).toNat = 0)
    (g42 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g43 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g44 : (x 1 1 && x 1 12).toNat = 0)
    (g45 : (x 1 2 && x 1 13).toNat = 0)
    (g46 : (x 0 3 && x 0 14).toNat = 0)
    (g47 : (x 1 3 && x 1 14).toNat = 0)
    (g48 : (x 1 1 && x 1 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b00_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48
