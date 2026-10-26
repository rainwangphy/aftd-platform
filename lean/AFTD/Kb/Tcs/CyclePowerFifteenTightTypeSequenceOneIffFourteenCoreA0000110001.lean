import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110001

Topic: combinatorics   Node: 95e964920100

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 5 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 1 3).toNat = 1)
    (g1 : (x 1 4).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 2 && x 3 13).toNat = 0)
    (g4 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d39468 : (x 4 12).toNat = 0 := by
    have r39469 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e39470 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e39471 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b39472 := hb (x 1 3)
    have b39473 := hb (x 2 2)
    have b39474 := hb (x 3 13)
    have b39475 := hb (x 4 12)
    clear * - r39469 e39470 e39471 b39472 b39473 b39474 b39475 g0
    omega
  have d39476 : (x 4 1 && x 4 12).toNat = 0 := by
    have r39477 := hand2 (x 4 1) (x 4 12)
    have b39478 := hb (x 4 12)
    have b39479 := hb (x 4 1 && x 4 12)
    clear * - r39477 b39478 b39479 d39468
    omega
  have d39480 : (x 4 4).toNat = 0 := by
    have r39481 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b39482 := hb (x 4 4)
    have b39483 := hb (x 4 12)
    clear * - r39481 b39482 b39483 d39468
    omega
  have d39484 : (x 3 13).toNat = 0 := by
    have r39485 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e39486 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e39487 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b39488 := hb (x 1 3)
    have b39489 := hb (x 2 2)
    have b39490 := hb (x 3 13)
    have b39491 := hb (x 4 12)
    clear * - r39485 e39486 e39487 b39488 b39489 b39490 b39491 d39468 g0
    omega
  have d39492 : (x 2 2).toNat = 0 := by
    have r39493 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e39494 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e39495 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b39496 := hb (x 1 3)
    have b39497 := hb (x 2 2)
    have b39498 := hb (x 3 13)
    have b39499 := hb (x 4 12)
    clear * - r39493 e39494 e39495 b39496 b39497 b39498 b39499 d39468 d39484 g0
    omega
  have d39500 : (x 4 13).toNat = 1 := by
    have r39501 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b39502 := hb (x 2 2)
    have b39503 := hb (x 4 13)
    have b39504 := hb (x 3 1 && x 3 14)
    clear * - r39501 b39502 b39503 b39504 g4 d39492
    omega
  have d39505 : (x 4 1).toNat = 1 := by
    have r39506 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b39507 := hb (x 4 1)
    have b39508 := hb (x 4 13)
    clear * - r39506 b39507 b39508 d39500
    omega
  have d39509 : (x 5 14).toNat = 0 := by
    have r39510 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
    have b39511 := hb (x 4 1)
    have b39512 := hb (x 5 14)
    clear * - r39510 b39511 b39512 d39505
    omega
  have d39513 : (x 5 3 && x 5 14).toNat = 0 := by
    have r39514 := hand2 (x 5 3) (x 5 14)
    have b39515 := hb (x 5 14)
    have b39516 := hb (x 5 3 && x 5 14)
    clear * - r39514 b39515 b39516 d39509
    omega
  have d39517 : (x 5 2).toNat = 0 := by
    have r39518 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b39519 := hb (x 5 2)
    have b39520 := hb (x 5 14)
    clear * - r39518 b39519 b39520 d39509
    omega
  have d39521 : (x 5 12).toNat = 0 := by
    have r39522 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e39523 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e39524 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b39525 := hb (x 2 3)
    have b39526 := hb (x 3 2)
    have b39527 := hb (x 4 13)
    have b39528 := hb (x 5 12)
    clear * - r39522 e39523 e39524 b39525 b39526 b39527 b39528 d39500 g2
    omega
  have d39529 : (x 5 4).toNat = 0 := by
    have r39530 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b39531 := hb (x 5 4)
    have b39532 := hb (x 5 12)
    clear * - r39530 b39531 b39532 d39521
    omega
  have d39533 : (x 2 3).toNat = 0 := by
    have r39534 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e39535 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e39536 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b39537 := hb (x 2 3)
    have b39538 := hb (x 3 2)
    have b39539 := hb (x 4 13)
    have b39540 := hb (x 5 12)
    clear * - r39534 e39535 e39536 b39537 b39538 b39539 b39540 d39521 d39500 g2
    omega
  have d39541 : (x 2 3 && x 2 14).toNat = 0 := by
    have r39542 := hand1 (x 2 3) (x 2 14)
    have b39543 := hb (x 2 3)
    have b39544 := hb (x 2 3 && x 2 14)
    clear * - r39542 b39543 b39544 d39533
    omega
  have d39545 : (x 5 11).toNat = 1 := by
    have r39546 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
    have b39547 := hb (x 1 4)
    have b39548 := hb (x 5 11)
    have b39549 := hb (x 4 1 && x 4 12)
    have b39550 := hb (x 3 2 && x 3 13)
    have b39551 := hb (x 2 3 && x 2 14)
    clear * - r39546 b39547 b39548 b39549 b39550 b39551 d39476 g3 d39541 g1
    omega
  have d39552 : (x 5 3).toNat = 1 := by
    have r39553 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b39554 := hb (x 5 3)
    have b39555 := hb (x 5 11)
    clear * - r39553 b39554 b39555 d39545
    omega
  have d39556 : (x 8 12).toNat = 0 := by
    have r39557 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
    have e39558 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e39559 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b39560 := hb (x 5 3)
    have b39561 := hb (x 6 2)
    have b39562 := hb (x 7 13)
    have b39563 := hb (x 8 12)
    clear * - r39557 e39558 e39559 b39560 b39561 b39562 b39563 d39552
    omega
  have d39564 : (x 8 1 && x 8 12).toNat = 0 := by
    have r39565 := hand2 (x 8 1) (x 8 12)
    have b39566 := hb (x 8 12)
    have b39567 := hb (x 8 1 && x 8 12)
    clear * - r39565 b39566 b39567 d39556
    omega
  have d39568 : (x 8 4).toNat = 0 := by
    have r39569 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b39570 := hb (x 8 4)
    have b39571 := hb (x 8 12)
    clear * - r39569 b39570 b39571 d39556
    omega
  have d39572 : (x 7 13).toNat = 0 := by
    have r39573 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
    have e39574 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e39575 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b39576 := hb (x 5 3)
    have b39577 := hb (x 6 2)
    have b39578 := hb (x 7 13)
    have b39579 := hb (x 8 12)
    clear * - r39573 e39574 e39575 b39576 b39577 b39578 b39579 d39556 d39552
    omega
  have d39580 : (x 7 2 && x 7 13).toNat = 0 := by
    have r39581 := hand2 (x 7 2) (x 7 13)
    have b39582 := hb (x 7 13)
    have b39583 := hb (x 7 2 && x 7 13)
    clear * - r39581 b39582 b39583 d39572
    omega
  have d39584 : (x 6 1 && x 6 14).toNat = 1 := by
    have r39585 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
    have b39586 := hb (x 5 2)
    have b39587 := hb (x 7 13)
    have b39588 := hb (x 6 1 && x 6 14)
    clear * - r39585 b39586 b39587 b39588 d39572 d39517
    omega
  have d39589 : (x 6 1).toNat = 1 := by
    have r39590 := hand1 (x 6 1) (x 6 14)
    have b39591 := hb (x 6 1)
    have b39592 := hb (x 6 1 && x 6 14)
    clear * - r39590 b39591 b39592 d39584
    omega
  have d39593 : (x 7 14).toNat = 0 := by
    have r39594 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
    have b39595 := hb (x 6 1)
    have b39596 := hb (x 7 14)
    clear * - r39594 b39595 b39596 d39589
    omega
  have d39597 : (x 7 1 && x 7 14).toNat = 0 := by
    have r39598 := hand2 (x 7 1) (x 7 14)
    have b39599 := hb (x 7 14)
    have b39600 := hb (x 7 1 && x 7 14)
    clear * - r39598 b39599 b39600 d39593
    omega
  have d39601 : (x 7 2).toNat = 0 := by
    have r39602 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b39603 := hb (x 7 2)
    have b39604 := hb (x 7 14)
    clear * - r39602 b39603 b39604 d39593
    omega
  have d39605 : (x 6 2).toNat = 0 := by
    have r39606 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
    have e39607 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e39608 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b39609 := hb (x 5 3)
    have b39610 := hb (x 6 2)
    have b39611 := hb (x 7 13)
    have b39612 := hb (x 8 12)
    clear * - r39606 e39607 e39608 b39609 b39610 b39611 b39612 d39556 d39572 d39552
    omega
  have d39613 : (x 6 2 && x 6 13).toNat = 0 := by
    have r39614 := hand1 (x 6 2) (x 6 13)
    have b39615 := hb (x 6 2)
    have b39616 := hb (x 6 2 && x 6 13)
    clear * - r39614 b39615 b39616 d39605
    omega
  have d39617 : (x 8 13).toNat = 1 := by
    have r39618 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
    have b39619 := hb (x 6 2)
    have b39620 := hb (x 8 13)
    have b39621 := hb (x 7 1 && x 7 14)
    clear * - r39618 b39619 b39620 b39621 d39597 d39605
    omega
  have d39622 : (x 8 1).toNat = 1 := by
    have r39623 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b39624 := hb (x 8 1)
    have b39625 := hb (x 8 13)
    clear * - r39623 b39624 b39625 d39617
    omega
  have d39626 : (x 9 14).toNat = 0 := by
    have r39627 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
    have b39628 := hb (x 8 1)
    have b39629 := hb (x 9 14)
    clear * - r39627 b39628 b39629 d39622
    omega
  have d39630 : (x 9 3 && x 9 14).toNat = 0 := by
    have r39631 := hand2 (x 9 3) (x 9 14)
    have b39632 := hb (x 9 14)
    have b39633 := hb (x 9 3 && x 9 14)
    clear * - r39631 b39632 b39633 d39626
    omega
  have d39634 : (x 9 2).toNat = 0 := by
    have r39635 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b39636 := hb (x 9 2)
    have b39637 := hb (x 9 14)
    clear * - r39635 b39636 b39637 d39626
    omega
  have d39638 : (x 9 12).toNat = 0 := by
    have r39639 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e39640 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e39641 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b39642 := hb (x 6 3)
    have b39643 := hb (x 7 2)
    have b39644 := hb (x 8 13)
    have b39645 := hb (x 9 12)
    clear * - r39639 e39640 e39641 b39642 b39643 b39644 b39645 d39617 d39601
    omega
  have d39646 : (x 9 4).toNat = 0 := by
    have r39647 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b39648 := hb (x 9 4)
    have b39649 := hb (x 9 12)
    clear * - r39647 b39648 b39649 d39638
    omega
  have d39650 : (x 6 3).toNat = 0 := by
    have r39651 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e39652 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e39653 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b39654 := hb (x 6 3)
    have b39655 := hb (x 7 2)
    have b39656 := hb (x 8 13)
    have b39657 := hb (x 9 12)
    clear * - r39651 e39652 e39653 b39654 b39655 b39656 b39657 d39638 d39617 d39601
    omega
  have d39658 : (x 6 3 && x 6 14).toNat = 0 := by
    have r39659 := hand1 (x 6 3) (x 6 14)
    have b39660 := hb (x 6 3)
    have b39661 := hb (x 6 3 && x 6 14)
    clear * - r39659 b39660 b39661 d39650
    omega
  have d39662 : (x 9 11).toNat = 1 := by
    have r39663 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := hcov11 9
    have b39664 := hb (x 5 4)
    have b39665 := hb (x 9 11)
    have b39666 := hb (x 8 1 && x 8 12)
    have b39667 := hb (x 7 2 && x 7 13)
    have b39668 := hb (x 6 3 && x 6 14)
    clear * - r39663 b39664 b39665 b39666 b39667 b39668 d39564 d39580 d39658 d39529
    omega
  have d39669 : (x 9 3).toNat = 1 := by
    have r39670 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
    have b39671 := hb (x 9 3)
    have b39672 := hb (x 9 11)
    clear * - r39670 b39671 b39672 d39662
    omega
  have d39673 : (x 12 12).toNat = 0 := by
    have r39674 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e39675 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e39676 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b39677 := hb (x 9 3)
    have b39678 := hb (x 10 2)
    have b39679 := hb (x 11 13)
    have b39680 := hb (x 12 12)
    clear * - r39674 e39675 e39676 b39677 b39678 b39679 b39680 d39669
    omega
  have d39681 : (x 12 1 && x 12 12).toNat = 0 := by
    have r39682 := hand2 (x 12 1) (x 12 12)
    have b39683 := hb (x 12 12)
    have b39684 := hb (x 12 1 && x 12 12)
    clear * - r39682 b39683 b39684 d39673
    omega
  have d39685 : (x 12 4).toNat = 0 := by
    have r39686 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b39687 := hb (x 12 4)
    have b39688 := hb (x 12 12)
    clear * - r39686 b39687 b39688 d39673
    omega
  have d39689 : (x 11 13).toNat = 0 := by
    have r39690 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e39691 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e39692 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b39693 := hb (x 9 3)
    have b39694 := hb (x 10 2)
    have b39695 := hb (x 11 13)
    have b39696 := hb (x 12 12)
    clear * - r39690 e39691 e39692 b39693 b39694 b39695 b39696 d39673 d39669
    omega
  have d39697 : (x 11 2 && x 11 13).toNat = 0 := by
    have r39698 := hand2 (x 11 2) (x 11 13)
    have b39699 := hb (x 11 13)
    have b39700 := hb (x 11 2 && x 11 13)
    clear * - r39698 b39699 b39700 d39689
    omega
  have d39701 : (x 10 1 && x 10 14).toNat = 1 := by
    have r39702 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
    have b39703 := hb (x 9 2)
    have b39704 := hb (x 11 13)
    have b39705 := hb (x 10 1 && x 10 14)
    clear * - r39702 b39703 b39704 b39705 d39689 d39634
    omega
  have d39706 : (x 10 14).toNat = 1 := by
    have r39707 := hand2 (x 10 1) (x 10 14)
    have b39708 := hb (x 10 14)
    have b39709 := hb (x 10 1 && x 10 14)
    clear * - r39707 b39708 b39709 d39701
    omega
  have d39710 : (x 9 1).toNat = 0 := by
    have r39711 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
    have b39712 := hb (x 9 1)
    have b39713 := hb (x 10 14)
    clear * - r39711 b39712 b39713 d39706
    omega
  have d39714 : (x 9 13).toNat = 0 := by
    have r39715 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b39716 := hb (x 9 1)
    have b39717 := hb (x 9 13)
    clear * - r39715 b39716 b39717 d39710
    omega
  have d39718 : (x 8 1 && x 8 14).toNat = 1 := by
    have r39719 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
    have b39720 := hb (x 7 2)
    have b39721 := hb (x 9 13)
    have b39722 := hb (x 8 1 && x 8 14)
    clear * - r39719 b39720 b39721 b39722 d39714 d39601
    omega
  have d39723 : (x 8 14).toNat = 1 := by
    have r39724 := hand2 (x 8 1) (x 8 14)
    have b39725 := hb (x 8 14)
    have b39726 := hb (x 8 1 && x 8 14)
    clear * - r39724 b39725 b39726 d39718
    omega
  have d39727 : (x 7 1).toNat = 0 := by
    have r39728 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
    have b39729 := hb (x 7 1)
    have b39730 := hb (x 8 14)
    clear * - r39728 b39729 b39730 d39723
    omega
  have d39731 : (x 7 1 && x 7 12).toNat = 0 := by
    have r39732 := hand1 (x 7 1) (x 7 12)
    have b39733 := hb (x 7 1)
    have b39734 := hb (x 7 1 && x 7 12)
    clear * - r39732 b39733 b39734 d39727
    omega
  have d39735 : (x 8 11).toNat = 1 := by
    have r39736 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
    have b39737 := hb (x 4 4)
    have b39738 := hb (x 8 11)
    have b39739 := hb (x 7 1 && x 7 12)
    have b39740 := hb (x 6 2 && x 6 13)
    have b39741 := hb (x 5 3 && x 5 14)
    clear * - r39736 b39737 b39738 b39739 b39740 b39741 d39731 d39613 d39513 d39480
    omega
  have d39742 : (x 8 3).toNat = 1 := by
    have r39743 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b39744 := hb (x 8 3)
    have b39745 := hb (x 8 11)
    clear * - r39743 b39744 b39745 d39735
    omega
  have d39746 : (x 11 12).toNat = 0 := by
    have r39747 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e39748 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e39749 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b39750 := hb (x 8 3)
    have b39751 := hb (x 9 2)
    have b39752 := hb (x 10 13)
    have b39753 := hb (x 11 12)
    clear * - r39747 e39748 e39749 b39750 b39751 b39752 b39753 d39634 d39742
    omega
  have d39754 : (x 11 1 && x 11 12).toNat = 0 := by
    have r39755 := hand2 (x 11 1) (x 11 12)
    have b39756 := hb (x 11 12)
    have b39757 := hb (x 11 1 && x 11 12)
    clear * - r39755 b39756 b39757 d39746
    omega
  have d39758 : (x 10 13).toNat = 0 := by
    have r39759 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e39760 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e39761 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b39762 := hb (x 8 3)
    have b39763 := hb (x 9 2)
    have b39764 := hb (x 10 13)
    have b39765 := hb (x 11 12)
    clear * - r39759 e39760 e39761 b39762 b39763 b39764 b39765 d39746 d39634 d39742
    omega
  have d39766 : (x 10 2 && x 10 13).toNat = 0 := by
    have r39767 := hand2 (x 10 2) (x 10 13)
    have b39768 := hb (x 10 13)
    have b39769 := hb (x 10 2 && x 10 13)
    clear * - r39767 b39768 b39769 d39758
    omega
  have d39770 : (x 12 11).toNat = 1 := by
    have r39771 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
    have b39772 := hb (x 8 4)
    have b39773 := hb (x 12 11)
    have b39774 := hb (x 11 1 && x 11 12)
    have b39775 := hb (x 10 2 && x 10 13)
    have b39776 := hb (x 9 3 && x 9 14)
    clear * - r39771 b39772 b39773 b39774 b39775 b39776 d39754 d39766 d39630 d39568
    omega
  have d39777 : (x 12 3).toNat = 1 := by
    have r39778 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b39779 := hb (x 12 3)
    have b39780 := hb (x 12 11)
    clear * - r39778 b39779 b39780 d39770
    omega
  have d39781 : (x 15 12).toNat = 0 := by
    have r39782 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e39783 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e39784 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b39785 := hb (x 12 3)
    have b39786 := hb (x 13 2)
    have b39787 := hb (x 14 13)
    have b39788 := hb (x 15 12)
    clear * - r39782 e39783 e39784 b39785 b39786 b39787 b39788 d39777
    omega
  have d39789 : (x 15 1 && x 15 12).toNat = 0 := by
    have r39790 := hand2 (x 15 1) (x 15 12)
    have b39791 := hb (x 15 12)
    have b39792 := hb (x 15 1 && x 15 12)
    clear * - r39790 b39791 b39792 d39781
    omega
  have d39793 : (x 14 13).toNat = 0 := by
    have r39794 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e39795 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e39796 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b39797 := hb (x 12 3)
    have b39798 := hb (x 13 2)
    have b39799 := hb (x 14 13)
    have b39800 := hb (x 15 12)
    clear * - r39794 e39795 e39796 b39797 b39798 b39799 b39800 d39781 d39777
    omega
  have d39801 : (x 14 2 && x 14 13).toNat = 0 := by
    have r39802 := hand2 (x 14 2) (x 14 13)
    have b39803 := hb (x 14 13)
    have b39804 := hb (x 14 2 && x 14 13)
    clear * - r39802 b39803 b39804 d39793
    omega
  have d39805 : (x 13 2).toNat = 0 := by
    have r39806 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e39807 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e39808 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b39809 := hb (x 12 3)
    have b39810 := hb (x 13 2)
    have b39811 := hb (x 14 13)
    have b39812 := hb (x 15 12)
    clear * - r39806 e39807 e39808 b39809 b39810 b39811 b39812 d39781 d39793 d39777
    omega
  have d39813 : (x 10 1).toNat = 1 := by
    have r39814 := hand1 (x 10 1) (x 10 14)
    have b39815 := hb (x 10 1)
    have b39816 := hb (x 10 1 && x 10 14)
    clear * - r39814 b39815 b39816 d39701
    omega
  have d39817 : (x 11 14).toNat = 0 := by
    have r39818 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
    have b39819 := hb (x 10 1)
    have b39820 := hb (x 11 14)
    clear * - r39818 b39819 b39820 d39813
    omega
  have d39821 : (x 11 1 && x 11 14).toNat = 0 := by
    have r39822 := hand2 (x 11 1) (x 11 14)
    have b39823 := hb (x 11 14)
    have b39824 := hb (x 11 1 && x 11 14)
    clear * - r39822 b39823 b39824 d39817
    omega
  have d39825 : (x 11 2).toNat = 0 := by
    have r39826 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b39827 := hb (x 11 2)
    have b39828 := hb (x 11 14)
    clear * - r39826 b39827 b39828 d39817
    omega
  have d39829 : (x 10 2).toNat = 0 := by
    have r39830 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e39831 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e39832 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b39833 := hb (x 9 3)
    have b39834 := hb (x 10 2)
    have b39835 := hb (x 11 13)
    have b39836 := hb (x 12 12)
    clear * - r39830 e39831 e39832 b39833 b39834 b39835 b39836 d39673 d39689 d39669
    omega
  have d39837 : (x 12 13).toNat = 1 := by
    have r39838 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
    have b39839 := hb (x 10 2)
    have b39840 := hb (x 12 13)
    have b39841 := hb (x 11 1 && x 11 14)
    clear * - r39838 b39839 b39840 b39841 d39821 d39829
    omega
  have d39842 : (x 12 1).toNat = 1 := by
    have r39843 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b39844 := hb (x 12 1)
    have b39845 := hb (x 12 13)
    clear * - r39843 b39844 b39845 d39837
    omega
  have d39846 : (x 13 14).toNat = 0 := by
    have r39847 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
    have b39848 := hb (x 12 1)
    have b39849 := hb (x 13 14)
    clear * - r39847 b39848 b39849 d39842
    omega
  have d39850 : (x 13 1 && x 13 14).toNat = 0 := by
    have r39851 := hand2 (x 13 1) (x 13 14)
    have b39852 := hb (x 13 14)
    have b39853 := hb (x 13 1 && x 13 14)
    clear * - r39851 b39852 b39853 d39846
    omega
  have d39854 : (x 12 2).toNat = 1 := by
    have r39855 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
    have b39856 := hb (x 12 2)
    have b39857 := hb (x 14 13)
    have b39858 := hb (x 13 1 && x 13 14)
    clear * - r39855 b39856 b39857 b39858 d39793 d39850
    omega
  have d39859 : (x 14 12).toNat = 0 := by
    have r39860 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e39861 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e39862 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b39863 := hb (x 11 3)
    have b39864 := hb (x 12 2)
    have b39865 := hb (x 13 13)
    have b39866 := hb (x 14 12)
    clear * - r39860 e39861 e39862 b39863 b39864 b39865 b39866 d39854
    omega
  have d39867 : (x 14 4).toNat = 0 := by
    have r39868 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
    have b39869 := hb (x 14 4)
    have b39870 := hb (x 14 12)
    clear * - r39868 b39869 b39870 d39859
    omega
  have d39871 : (x 14 4 && x 14 14).toNat = 0 := by
    have r39872 := hand1 (x 14 4) (x 14 14)
    have b39873 := hb (x 14 4)
    have b39874 := hb (x 14 4 && x 14 14)
    clear * - r39872 b39873 b39874 d39867
    omega
  have d39875 : (x 13 13).toNat = 0 := by
    have r39876 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e39877 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e39878 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b39879 := hb (x 11 3)
    have b39880 := hb (x 12 2)
    have b39881 := hb (x 13 13)
    have b39882 := hb (x 14 12)
    clear * - r39876 e39877 e39878 b39879 b39880 b39881 b39882 d39859 d39854
    omega
  have d39883 : (x 13 5).toNat = 0 := by
    have r39884 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
    have b39885 := hb (x 13 5)
    have b39886 := hb (x 13 13)
    clear * - r39884 b39885 b39886 d39875
    omega
  have d39887 : (x 13 3 && x 13 14).toNat = 0 := by
    have r39888 := hand2 (x 13 3) (x 13 14)
    have b39889 := hb (x 13 14)
    have b39890 := hb (x 13 3 && x 13 14)
    clear * - r39888 b39889 b39890 d39846
    omega
  have d39891 : (x 16 11).toNat = 1 := by
    have r39892 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := hcov11 16
    have b39893 := hb (x 12 4)
    have b39894 := hb (x 16 11)
    have b39895 := hb (x 15 1 && x 15 12)
    have b39896 := hb (x 14 2 && x 14 13)
    have b39897 := hb (x 13 3 && x 13 14)
    clear * - r39892 b39893 b39894 b39895 b39896 b39897 d39789 d39801 d39887 d39685
    omega
  have d39898 : (x 16 3).toNat = 1 := by
    have r39899 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
    have b39900 := hb (x 16 3)
    have b39901 := hb (x 16 11)
    clear * - r39899 b39900 b39901 d39891
    omega
  have d39902 : (x 19 12).toNat = 0 := by
    have r39903 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e39904 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e39905 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b39906 := hb (x 16 3)
    have b39907 := hb (x 17 2)
    have b39908 := hb (x 18 13)
    have b39909 := hb (x 19 12)
    clear * - r39903 e39904 e39905 b39906 b39907 b39908 b39909 d39898
    omega
  have d39910 : (x 18 13).toNat = 0 := by
    have r39911 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e39912 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e39913 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b39914 := hb (x 16 3)
    have b39915 := hb (x 17 2)
    have b39916 := hb (x 18 13)
    have b39917 := hb (x 19 12)
    clear * - r39911 e39912 e39913 b39914 b39915 b39916 b39917 d39902 d39898
    omega
  have d39918 : (x 17 2).toNat = 0 := by
    have r39919 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e39920 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e39921 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b39922 := hb (x 16 3)
    have b39923 := hb (x 17 2)
    have b39924 := hb (x 18 13)
    have b39925 := hb (x 19 12)
    clear * - r39919 e39920 e39921 b39922 b39923 b39924 b39925 d39902 d39910 d39898
    omega
  have d39926 : (x 13 12).toNat = 0 := by
    have r39927 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e39928 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e39929 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b39930 := hb (x 10 3)
    have b39931 := hb (x 11 2)
    have b39932 := hb (x 12 13)
    have b39933 := hb (x 13 12)
    clear * - r39927 e39928 e39929 b39930 b39931 b39932 b39933 d39837 d39825
    omega
  have d39934 : (x 13 4).toNat = 0 := by
    have r39935 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b39936 := hb (x 13 4)
    have b39937 := hb (x 13 12)
    clear * - r39935 b39936 b39937 d39926
    omega
  have d39938 : (x 10 3).toNat = 0 := by
    have r39939 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e39940 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e39941 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b39942 := hb (x 10 3)
    have b39943 := hb (x 11 2)
    have b39944 := hb (x 12 13)
    have b39945 := hb (x 13 12)
    clear * - r39939 e39940 e39941 b39942 b39943 b39944 b39945 d39926 d39837 d39825
    omega
  have d39946 : (x 10 3 && x 10 14).toNat = 0 := by
    have r39947 := hand1 (x 10 3) (x 10 14)
    have b39948 := hb (x 10 3)
    have b39949 := hb (x 10 3 && x 10 14)
    clear * - r39947 b39948 b39949 d39938
    omega
  have d39950 : (x 13 11).toNat = 1 := by
    have r39951 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := hcov11 13
    have b39952 := hb (x 9 4)
    have b39953 := hb (x 13 11)
    have b39954 := hb (x 12 1 && x 12 12)
    have b39955 := hb (x 11 2 && x 11 13)
    have b39956 := hb (x 10 3 && x 10 14)
    clear * - r39951 b39952 b39953 b39954 b39955 b39956 d39681 d39697 d39946 d39646
    omega
  have d39957 : (x 13 3).toNat = 1 := by
    have r39958 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
    have b39959 := hb (x 13 3)
    have b39960 := hb (x 13 11)
    clear * - r39958 b39959 b39960 d39950
    omega
  have d39961 : (x 16 12).toNat = 0 := by
    have r39962 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e39963 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e39964 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b39965 := hb (x 13 3)
    have b39966 := hb (x 14 2)
    have b39967 := hb (x 15 13)
    have b39968 := hb (x 16 12)
    clear * - r39962 e39963 e39964 b39965 b39966 b39967 b39968 d39957
    omega
  have d39969 : (x 16 1 && x 16 12).toNat = 0 := by
    have r39970 := hand2 (x 16 1) (x 16 12)
    have b39971 := hb (x 16 12)
    have b39972 := hb (x 16 1 && x 16 12)
    clear * - r39970 b39971 b39972 d39961
    omega
  have d39973 : (x 16 2 && x 16 12).toNat = 0 := by
    have r39974 := hand2 (x 16 2) (x 16 12)
    have b39975 := hb (x 16 12)
    have b39976 := hb (x 16 2 && x 16 12)
    clear * - r39974 b39975 b39976 d39961
    omega
  have d39977 : (x 15 13).toNat = 0 := by
    have r39978 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e39979 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e39980 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b39981 := hb (x 13 3)
    have b39982 := hb (x 14 2)
    have b39983 := hb (x 15 13)
    have b39984 := hb (x 16 12)
    clear * - r39978 e39979 e39980 b39981 b39982 b39983 b39984 d39961 d39957
    omega
  have d39985 : (x 15 2 && x 15 13).toNat = 0 := by
    have r39986 := hand2 (x 15 2) (x 15 13)
    have b39987 := hb (x 15 13)
    have b39988 := hb (x 15 2 && x 15 13)
    clear * - r39986 b39987 b39988 d39977
    omega
  have d39989 : (x 15 3 && x 15 13).toNat = 0 := by
    have r39990 := hand2 (x 15 3) (x 15 13)
    have b39991 := hb (x 15 13)
    have b39992 := hb (x 15 3 && x 15 13)
    clear * - r39990 b39991 b39992 d39977
    omega
  have d39993 : (x 14 1 && x 14 14).toNat = 1 := by
    have r39994 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
    have b39995 := hb (x 13 2)
    have b39996 := hb (x 15 13)
    have b39997 := hb (x 14 1 && x 14 14)
    clear * - r39994 b39995 b39996 b39997 d39977 d39805
    omega
  have d39998 : (x 14 1).toNat = 1 := by
    have r39999 := hand1 (x 14 1) (x 14 14)
    have b40000 := hb (x 14 1)
    have b40001 := hb (x 14 1 && x 14 14)
    clear * - r39999 b40000 b40001 d39993
    omega
  have d40002 : (x 15 14).toNat = 0 := by
    have r40003 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
    have b40004 := hb (x 14 1)
    have b40005 := hb (x 15 14)
    clear * - r40003 b40004 b40005 d39998
    omega
  have d40006 : (x 15 1 && x 15 14).toNat = 0 := by
    have r40007 := hand2 (x 15 1) (x 15 14)
    have b40008 := hb (x 15 14)
    have b40009 := hb (x 15 1 && x 15 14)
    clear * - r40007 b40008 b40009 d40002
    omega
  have d40010 : (x 15 2).toNat = 0 := by
    have r40011 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b40012 := hb (x 15 2)
    have b40013 := hb (x 15 14)
    clear * - r40011 b40012 b40013 d40002
    omega
  have d40014 : (x 14 2).toNat = 0 := by
    have r40015 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e40016 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e40017 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b40018 := hb (x 13 3)
    have b40019 := hb (x 14 2)
    have b40020 := hb (x 15 13)
    have b40021 := hb (x 16 12)
    clear * - r40015 e40016 e40017 b40018 b40019 b40020 b40021 d39961 d39977 d39957
    omega
  have d40022 : (x 16 13).toNat = 1 := by
    have r40023 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
    have b40024 := hb (x 14 2)
    have b40025 := hb (x 16 13)
    have b40026 := hb (x 15 1 && x 15 14)
    clear * - r40023 b40024 b40025 b40026 d40006 d40014
    omega
  have d40027 : (x 17 12).toNat = 0 := by
    have r40028 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e40029 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e40030 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b40031 := hb (x 14 3)
    have b40032 := hb (x 15 2)
    have b40033 := hb (x 16 13)
    have b40034 := hb (x 17 12)
    clear * - r40028 e40029 e40030 b40031 b40032 b40033 b40034 d40022 d40010
    omega
  have d40035 : (x 14 3).toNat = 0 := by
    have r40036 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e40037 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e40038 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b40039 := hb (x 14 3)
    have b40040 := hb (x 15 2)
    have b40041 := hb (x 16 13)
    have b40042 := hb (x 17 12)
    clear * - r40036 e40037 e40038 b40039 b40040 b40041 b40042 d40027 d40022 d40010
    omega
  have d40043 : (x 14 3 && x 14 14).toNat = 0 := by
    have r40044 := hand1 (x 14 3) (x 14 14)
    have b40045 := hb (x 14 3)
    have b40046 := hb (x 14 3 && x 14 14)
    clear * - r40044 b40045 b40046 d40035
    omega
  have d40047 : (x 17 11).toNat = 1 := by
    have r40048 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
    have b40049 := hb (x 13 4)
    have b40050 := hb (x 17 11)
    have b40051 := hb (x 16 1 && x 16 12)
    have b40052 := hb (x 15 2 && x 15 13)
    have b40053 := hb (x 14 3 && x 14 14)
    clear * - r40048 b40049 b40050 b40051 b40052 b40053 d39969 d39985 d40043 d39934
    omega
  have d40054 : (x 17 3).toNat = 1 := by
    have r40055 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b40056 := hb (x 17 3)
    have b40057 := hb (x 17 11)
    clear * - r40055 b40056 b40057 d40047
    omega
  have d40058 : (x 20 12).toNat = 0 := by
    have r40059 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e40060 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e40061 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b40062 := hb (x 17 3)
    have b40063 := hb (x 18 2)
    have b40064 := hb (x 19 13)
    have b40065 := hb (x 20 12)
    clear * - r40059 e40060 e40061 b40062 b40063 b40064 b40065 d40054
    omega
  have d40066 : (x 19 13).toNat = 0 := by
    have r40067 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e40068 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e40069 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b40070 := hb (x 17 3)
    have b40071 := hb (x 18 2)
    have b40072 := hb (x 19 13)
    have b40073 := hb (x 20 12)
    clear * - r40067 e40068 e40069 b40070 b40071 b40072 b40073 d40058 d40054
    omega
  have d40074 : (x 18 1 && x 18 14).toNat = 1 := by
    have r40075 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
    have b40076 := hb (x 17 2)
    have b40077 := hb (x 19 13)
    have b40078 := hb (x 18 1 && x 18 14)
    clear * - r40075 b40076 b40077 b40078 d40066 d39918
    omega
  have d40079 : (x 18 14).toNat = 1 := by
    have r40080 := hand2 (x 18 1) (x 18 14)
    have b40081 := hb (x 18 14)
    have b40082 := hb (x 18 1 && x 18 14)
    clear * - r40080 b40081 b40082 d40074
    omega
  have d40083 : (x 17 1).toNat = 0 := by
    have r40084 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
    have b40085 := hb (x 17 1)
    have b40086 := hb (x 18 14)
    clear * - r40084 b40085 b40086 d40079
    omega
  have d40087 : (x 17 1 && x 17 11).toNat = 0 := by
    have r40088 := hand1 (x 17 1) (x 17 11)
    have b40089 := hb (x 17 1)
    have b40090 := hb (x 17 1 && x 17 11)
    clear * - r40088 b40089 b40090 d40083
    omega
  have d40091 : (x 18 2).toNat = 0 := by
    have r40092 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e40093 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e40094 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b40095 := hb (x 17 3)
    have b40096 := hb (x 18 2)
    have b40097 := hb (x 19 13)
    have b40098 := hb (x 20 12)
    clear * - r40092 e40093 e40094 b40095 b40096 b40097 b40098 d40058 d40066 d40054
    omega
  have d40099 : (x 18 10).toNat = 0 := by
    have r40100 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
    have b40101 := hb (x 18 2)
    have b40102 := hb (x 18 10)
    clear * - r40100 b40101 b40102 d40091
    omega
  have r40103 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := hcov10 18
  have b40104 := hb (x 13 5)
  have b40105 := hb (x 18 10)
  have b40106 := hb (x 17 1 && x 17 11)
  have b40107 := hb (x 16 2 && x 16 12)
  have b40108 := hb (x 15 3 && x 15 13)
  have b40109 := hb (x 14 4 && x 14 14)
  linarith only [r40103, b40104, b40105, b40106, b40107, b40108, b40109, d40099, d40087, d39973, d39989, d39871, d39883]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 1 3).toNat = 1)
    (g1 : (x 1 4).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 2 && x 3 13).toNat = 0)
    (g4 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4
