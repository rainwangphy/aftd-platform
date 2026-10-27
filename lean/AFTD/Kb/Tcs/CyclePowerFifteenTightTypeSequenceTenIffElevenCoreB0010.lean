import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0010

Topic: combinatorics   Node: 2fc14ec8dded

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 8 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b000.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 6).toNat = 0)
    (g1 : (x 0 4).toNat = 0)
    (g2 : (x 0 5).toNat = 0)
    (g3 : (x 0 12).toNat = 0)
    (g4 : (x 1 2).toNat = 0)
    (g5 : (x 1 10).toNat = 0)
    (g6 : (x 2 5).toNat = 0)
    (g7 : (x 2 13).toNat = 0)
    (g8 : (x 3 4).toNat = 0)
    (g9 : (x 3 12 && x 3 13).toNat = 0)
    (g10 : (x 2 13 && x 2 14).toNat = 0)
    (g11 : (x 3 8 && x 3 13).toNat = 0)
    (g12 : (x 2 9 && x 2 14).toNat = 0)
    (g13 : (x 1 2 && x 1 11).toNat = 0)
    (g14 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g15 : (x (-2) 5 && x (-2) 14).toNat = 0)
    (g16 : (x 3 4 && x 3 13).toNat = 0)
    (g17 : (x 2 5 && x 2 14).toNat = 0)
    (g18 : (x 3 2 && x 3 12).toNat = 0)
    (g19 : (x 2 3 && x 2 13).toNat = 0)
    (g20 : (x 3 1 && x 3 12).toNat = 0)
    (g21 : (x 2 2 && x 2 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d499 : (x 0 1 && x 0 12).toNat = 0 := by
    have r500 := hand2 (x 0 1) (x 0 12)
    have b501 := hb (x 0 12)
    have b502 := hb (x 0 1 && x 0 12)
    clear * - r500 b501 b502 g3
    omega
  have d503 : (x 0 3 && x 0 12).toNat = 0 := by
    have r504 := hand2 (x 0 3) (x 0 12)
    have b505 := hb (x 0 12)
    have b506 := hb (x 0 3 && x 0 12)
    clear * - r504 b505 b506 g3
    omega
  cases h507 : x 0 2
  · have f508 : (x 0 2).toNat = 0 := by rw [h507]; rfl
    have d509 : (x 1 1 && x 1 14).toNat = 1 := by
      have r510 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b511 := hb (x 0 2)
      have b512 := hb (x 2 13)
      have b513 := hb (x 1 1 && x 1 14)
      clear * - r510 b511 b512 b513 g7 f508
      omega
    have d514 : (x 1 1).toNat = 1 := by
      have r515 := hand1 (x 1 1) (x 1 14)
      have b516 := hb (x 1 1)
      have b517 := hb (x 1 1 && x 1 14)
      clear * - r515 b516 b517 d509
      omega
    have d518 : (x 2 14).toNat = 0 := by
      have r519 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b520 := hb (x 1 1)
      have b521 := hb (x 2 14)
      clear * - r519 b520 b521 d514
      omega
    have d522 : (x 2 1 && x 2 14).toNat = 0 := by
      have r523 := hand2 (x 2 1) (x 2 14)
      have b524 := hb (x 2 14)
      have b525 := hb (x 2 1 && x 2 14)
      clear * - r523 b524 b525 d518
      omega
    have d526 : (x 3 13).toNat = 1 := by
      have r527 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b528 := hb (x 1 2)
      have b529 := hb (x 3 13)
      have b530 := hb (x 2 1 && x 2 14)
      clear * - r527 b528 b529 b530 d522 g4
      omega
    have d531 : (x 3 1).toNat = 1 := by
      have r532 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b533 := hb (x 3 1)
      have b534 := hb (x 3 13)
      clear * - r532 b533 b534 d526
      omega
    have d535 : (x 4 14).toNat = 0 := by
      have r536 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b537 := hb (x 3 1)
      have b538 := hb (x 4 14)
      clear * - r536 b537 b538 d531
      omega
    have d539 : (x 4 3 && x 4 14).toNat = 0 := by
      have r540 := hand2 (x 4 3) (x 4 14)
      have b541 := hb (x 4 14)
      have b542 := hb (x 4 3 && x 4 14)
      clear * - r540 b541 b542 d535
      omega
    have d543 : (x 4 2).toNat = 0 := by
      have r544 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b545 := hb (x 4 2)
      have b546 := hb (x 4 14)
      clear * - r544 b545 b546 d535
      omega
    have d547 : (x 2 2).toNat = 0 := by
      have r548 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b549 := hb (x 2 2)
      have b550 := hb (x 2 14)
      clear * - r548 b549 b550 d518
      omega
    have d551 : (x 4 12).toNat = 0 := by
      have r552 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e553 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e554 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b555 := hb (x 1 3)
      have b556 := hb (x 2 2)
      have b557 := hb (x 3 13)
      have b558 := hb (x 4 12)
      clear * - r552 e553 e554 b555 b556 b557 b558 d526 d547
      omega
    have d559 : (x 4 4).toNat = 0 := by
      have r560 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b561 := hb (x 4 4)
      have b562 := hb (x 4 12)
      clear * - r560 b561 b562 d551
      omega
    have d563 : (x 1 3).toNat = 0 := by
      have r564 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e565 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e566 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b567 := hb (x 1 3)
      have b568 := hb (x 2 2)
      have b569 := hb (x 3 13)
      have b570 := hb (x 4 12)
      clear * - r564 e565 e566 b567 b568 b569 b570 d551 d526 d547
      omega
    have d571 : (x 1 3 && x 1 14).toNat = 0 := by
      have r572 := hand1 (x 1 3) (x 1 14)
      have b573 := hb (x 1 3)
      have b574 := hb (x 1 3 && x 1 14)
      clear * - r572 b573 b574 d563
      omega
    have d575 : (x 4 11).toNat = 1 := by
      have r576 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b577 := hb (x 0 4)
      have b578 := hb (x 4 11)
      have b579 := hb (x 3 1 && x 3 12)
      have b580 := hb (x 2 2 && x 2 13)
      have b581 := hb (x 1 3 && x 1 14)
      clear * - r576 b577 b578 b579 b580 b581 g20 g21 d571 g1
      omega
    have d582 : (x 4 3).toNat = 1 := by
      have r583 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b584 := hb (x 4 3)
      have b585 := hb (x 4 11)
      clear * - r583 b584 b585 d575
      omega
    have d586 : (x 7 12).toNat = 0 := by
      have r587 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e588 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e589 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b590 := hb (x 4 3)
      have b591 := hb (x 5 2)
      have b592 := hb (x 6 13)
      have b593 := hb (x 7 12)
      clear * - r587 e588 e589 b590 b591 b592 b593 d582
      omega
    have d594 : (x 7 1 && x 7 12).toNat = 0 := by
      have r595 := hand2 (x 7 1) (x 7 12)
      have b596 := hb (x 7 12)
      have b597 := hb (x 7 1 && x 7 12)
      clear * - r595 b596 b597 d586
      omega
    have d598 : (x 7 4).toNat = 0 := by
      have r599 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
      have b600 := hb (x 7 4)
      have b601 := hb (x 7 12)
      clear * - r599 b600 b601 d586
      omega
    have d602 : (x 6 13).toNat = 0 := by
      have r603 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e604 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e605 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b606 := hb (x 4 3)
      have b607 := hb (x 5 2)
      have b608 := hb (x 6 13)
      have b609 := hb (x 7 12)
      clear * - r603 e604 e605 b606 b607 b608 b609 d586 d582
      omega
    have d610 : (x 6 2 && x 6 13).toNat = 0 := by
      have r611 := hand2 (x 6 2) (x 6 13)
      have b612 := hb (x 6 13)
      have b613 := hb (x 6 2 && x 6 13)
      clear * - r611 b612 b613 d602
      omega
    have d614 : (x 5 1 && x 5 14).toNat = 1 := by
      have r615 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b616 := hb (x 4 2)
      have b617 := hb (x 6 13)
      have b618 := hb (x 5 1 && x 5 14)
      clear * - r615 b616 b617 b618 d602 d543
      omega
    have d619 : (x 5 1).toNat = 1 := by
      have r620 := hand1 (x 5 1) (x 5 14)
      have b621 := hb (x 5 1)
      have b622 := hb (x 5 1 && x 5 14)
      clear * - r620 b621 b622 d614
      omega
    have d623 : (x 6 14).toNat = 0 := by
      have r624 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b625 := hb (x 5 1)
      have b626 := hb (x 6 14)
      clear * - r624 b625 b626 d619
      omega
    have d627 : (x 6 1 && x 6 14).toNat = 0 := by
      have r628 := hand2 (x 6 1) (x 6 14)
      have b629 := hb (x 6 14)
      have b630 := hb (x 6 1 && x 6 14)
      clear * - r628 b629 b630 d623
      omega
    have d631 : (x 6 2).toNat = 0 := by
      have r632 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b633 := hb (x 6 2)
      have b634 := hb (x 6 14)
      clear * - r632 b633 b634 d623
      omega
    have d635 : (x 5 2).toNat = 0 := by
      have r636 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e637 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e638 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b639 := hb (x 4 3)
      have b640 := hb (x 5 2)
      have b641 := hb (x 6 13)
      have b642 := hb (x 7 12)
      clear * - r636 e637 e638 b639 b640 b641 b642 d586 d602 d582
      omega
    have d643 : (x 5 2 && x 5 13).toNat = 0 := by
      have r644 := hand1 (x 5 2) (x 5 13)
      have b645 := hb (x 5 2)
      have b646 := hb (x 5 2 && x 5 13)
      clear * - r644 b645 b646 d635
      omega
    have d647 : (x 7 13).toNat = 1 := by
      have r648 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b649 := hb (x 5 2)
      have b650 := hb (x 7 13)
      have b651 := hb (x 6 1 && x 6 14)
      clear * - r648 b649 b650 b651 d627 d635
      omega
    have d652 : (x 7 1).toNat = 1 := by
      have r653 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b654 := hb (x 7 1)
      have b655 := hb (x 7 13)
      clear * - r653 b654 b655 d647
      omega
    have d656 : (x 8 14).toNat = 0 := by
      have r657 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b658 := hb (x 7 1)
      have b659 := hb (x 8 14)
      clear * - r657 b658 b659 d652
      omega
    have d660 : (x 8 3 && x 8 14).toNat = 0 := by
      have r661 := hand2 (x 8 3) (x 8 14)
      have b662 := hb (x 8 14)
      have b663 := hb (x 8 3 && x 8 14)
      clear * - r661 b662 b663 d656
      omega
    have d664 : (x 8 2).toNat = 0 := by
      have r665 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
      have b666 := hb (x 8 2)
      have b667 := hb (x 8 14)
      clear * - r665 b666 b667 d656
      omega
    have d668 : (x 8 12).toNat = 0 := by
      have r669 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e670 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e671 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b672 := hb (x 5 3)
      have b673 := hb (x 6 2)
      have b674 := hb (x 7 13)
      have b675 := hb (x 8 12)
      clear * - r669 e670 e671 b672 b673 b674 b675 d647 d631
      omega
    have d676 : (x 8 4).toNat = 0 := by
      have r677 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
      have b678 := hb (x 8 4)
      have b679 := hb (x 8 12)
      clear * - r677 b678 b679 d668
      omega
    have d680 : (x 5 3).toNat = 0 := by
      have r681 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e682 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e683 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b684 := hb (x 5 3)
      have b685 := hb (x 6 2)
      have b686 := hb (x 7 13)
      have b687 := hb (x 8 12)
      clear * - r681 e682 e683 b684 b685 b686 b687 d668 d647 d631
      omega
    have d688 : (x 5 3 && x 5 14).toNat = 0 := by
      have r689 := hand1 (x 5 3) (x 5 14)
      have b690 := hb (x 5 3)
      have b691 := hb (x 5 3 && x 5 14)
      clear * - r689 b690 b691 d680
      omega
    have d692 : (x 8 11).toNat = 1 := by
      have r693 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b694 := hb (x 4 4)
      have b695 := hb (x 8 11)
      have b696 := hb (x 7 1 && x 7 12)
      have b697 := hb (x 6 2 && x 6 13)
      have b698 := hb (x 5 3 && x 5 14)
      clear * - r693 b694 b695 b696 b697 b698 d594 d610 d688 d559
      omega
    have d699 : (x 8 3).toNat = 1 := by
      have r700 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b701 := hb (x 8 3)
      have b702 := hb (x 8 11)
      clear * - r700 b701 b702 d692
      omega
    have d703 : (x 11 12).toNat = 0 := by
      have r704 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e705 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e706 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b707 := hb (x 8 3)
      have b708 := hb (x 9 2)
      have b709 := hb (x 10 13)
      have b710 := hb (x 11 12)
      clear * - r704 e705 e706 b707 b708 b709 b710 d699
      omega
    have d711 : (x 11 1 && x 11 12).toNat = 0 := by
      have r712 := hand2 (x 11 1) (x 11 12)
      have b713 := hb (x 11 12)
      have b714 := hb (x 11 1 && x 11 12)
      clear * - r712 b713 b714 d703
      omega
    have d715 : (x 11 4).toNat = 0 := by
      have r716 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
      have b717 := hb (x 11 4)
      have b718 := hb (x 11 12)
      clear * - r716 b717 b718 d703
      omega
    have d719 : (x 10 13).toNat = 0 := by
      have r720 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e721 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e722 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b723 := hb (x 8 3)
      have b724 := hb (x 9 2)
      have b725 := hb (x 10 13)
      have b726 := hb (x 11 12)
      clear * - r720 e721 e722 b723 b724 b725 b726 d703 d699
      omega
    have d727 : (x 10 2 && x 10 13).toNat = 0 := by
      have r728 := hand2 (x 10 2) (x 10 13)
      have b729 := hb (x 10 13)
      have b730 := hb (x 10 2 && x 10 13)
      clear * - r728 b729 b730 d719
      omega
    have d731 : (x 9 1 && x 9 14).toNat = 1 := by
      have r732 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b733 := hb (x 8 2)
      have b734 := hb (x 10 13)
      have b735 := hb (x 9 1 && x 9 14)
      clear * - r732 b733 b734 b735 d719 d664
      omega
    have d736 : (x 9 14).toNat = 1 := by
      have r737 := hand2 (x 9 1) (x 9 14)
      have b738 := hb (x 9 14)
      have b739 := hb (x 9 1 && x 9 14)
      clear * - r737 b738 b739 d731
      omega
    have d740 : (x 8 1).toNat = 0 := by
      have r741 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b742 := hb (x 8 1)
      have b743 := hb (x 9 14)
      clear * - r741 b742 b743 d736
      omega
    have d744 : (x 8 13).toNat = 0 := by
      have r745 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b746 := hb (x 8 1)
      have b747 := hb (x 8 13)
      clear * - r745 b746 b747 d740
      omega
    have d748 : (x 7 1 && x 7 14).toNat = 1 := by
      have r749 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b750 := hb (x 6 2)
      have b751 := hb (x 8 13)
      have b752 := hb (x 7 1 && x 7 14)
      clear * - r749 b750 b751 b752 d744 d631
      omega
    have d753 : (x 7 14).toNat = 1 := by
      have r754 := hand2 (x 7 1) (x 7 14)
      have b755 := hb (x 7 14)
      have b756 := hb (x 7 1 && x 7 14)
      clear * - r754 b755 b756 d748
      omega
    have d757 : (x 6 1).toNat = 0 := by
      have r758 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b759 := hb (x 6 1)
      have b760 := hb (x 7 14)
      clear * - r758 b759 b760 d753
      omega
    have d761 : (x 6 1 && x 6 12).toNat = 0 := by
      have r762 := hand1 (x 6 1) (x 6 12)
      have b763 := hb (x 6 1)
      have b764 := hb (x 6 1 && x 6 12)
      clear * - r762 b763 b764 d757
      omega
    have d765 : (x 7 11).toNat = 1 := by
      have r766 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b767 := hb (x 3 4)
      have b768 := hb (x 7 11)
      have b769 := hb (x 6 1 && x 6 12)
      have b770 := hb (x 5 2 && x 5 13)
      have b771 := hb (x 4 3 && x 4 14)
      clear * - r766 b767 b768 b769 b770 b771 d761 d643 d539 g8
      omega
    have d772 : (x 7 3).toNat = 1 := by
      have r773 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b774 := hb (x 7 3)
      have b775 := hb (x 7 11)
      clear * - r773 b774 b775 d765
      omega
    have d776 : (x 10 12).toNat = 0 := by
      have r777 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e778 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e779 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b780 := hb (x 7 3)
      have b781 := hb (x 8 2)
      have b782 := hb (x 9 13)
      have b783 := hb (x 10 12)
      clear * - r777 e778 e779 b780 b781 b782 b783 d664 d772
      omega
    have d784 : (x 10 1 && x 10 12).toNat = 0 := by
      have r785 := hand2 (x 10 1) (x 10 12)
      have b786 := hb (x 10 12)
      have b787 := hb (x 10 1 && x 10 12)
      clear * - r785 b786 b787 d776
      omega
    have d788 : (x 9 13).toNat = 0 := by
      have r789 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e790 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e791 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b792 := hb (x 7 3)
      have b793 := hb (x 8 2)
      have b794 := hb (x 9 13)
      have b795 := hb (x 10 12)
      clear * - r789 e790 e791 b792 b793 b794 b795 d776 d664 d772
      omega
    have d796 : (x 9 2 && x 9 13).toNat = 0 := by
      have r797 := hand2 (x 9 2) (x 9 13)
      have b798 := hb (x 9 13)
      have b799 := hb (x 9 2 && x 9 13)
      clear * - r797 b798 b799 d788
      omega
    have d800 : (x 11 11).toNat = 1 := by
      have r801 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b802 := hb (x 7 4)
      have b803 := hb (x 11 11)
      have b804 := hb (x 10 1 && x 10 12)
      have b805 := hb (x 9 2 && x 9 13)
      have b806 := hb (x 8 3 && x 8 14)
      clear * - r801 b802 b803 b804 b805 b806 d784 d796 d660 d598
      omega
    have d807 : (x 11 3).toNat = 1 := by
      have r808 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
      have b809 := hb (x 11 3)
      have b810 := hb (x 11 11)
      clear * - r808 b809 b810 d800
      omega
    have d811 : (x 14 12).toNat = 0 := by
      have r812 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e813 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e814 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b815 := hb (x 11 3)
      have b816 := hb (x 12 2)
      have b817 := hb (x 13 13)
      have b818 := hb (x 14 12)
      clear * - r812 e813 e814 b815 b816 b817 b818 d807
      omega
    have d819 : (x 14 1 && x 14 12).toNat = 0 := by
      have r820 := hand2 (x 14 1) (x 14 12)
      have b821 := hb (x 14 12)
      have b822 := hb (x 14 1 && x 14 12)
      clear * - r820 b821 b822 d811
      omega
    have d823 : (x 13 13).toNat = 0 := by
      have r824 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e825 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e826 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b827 := hb (x 11 3)
      have b828 := hb (x 12 2)
      have b829 := hb (x 13 13)
      have b830 := hb (x 14 12)
      clear * - r824 e825 e826 b827 b828 b829 b830 d811 d807
      omega
    have d831 : (x 13 2 && x 13 13).toNat = 0 := by
      have r832 := hand2 (x 13 2) (x 13 13)
      have b833 := hb (x 13 13)
      have b834 := hb (x 13 2 && x 13 13)
      clear * - r832 b833 b834 d823
      omega
    have d835 : (x 12 2).toNat = 0 := by
      have r836 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e837 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e838 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b839 := hb (x 11 3)
      have b840 := hb (x 12 2)
      have b841 := hb (x 13 13)
      have b842 := hb (x 14 12)
      clear * - r836 e837 e838 b839 b840 b841 b842 d811 d823 d807
      omega
    have d843 : (x 9 1).toNat = 1 := by
      have r844 := hand1 (x 9 1) (x 9 14)
      have b845 := hb (x 9 1)
      have b846 := hb (x 9 1 && x 9 14)
      clear * - r844 b845 b846 d731
      omega
    have d847 : (x 10 14).toNat = 0 := by
      have r848 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b849 := hb (x 9 1)
      have b850 := hb (x 10 14)
      clear * - r848 b849 b850 d843
      omega
    have d851 : (x 10 1 && x 10 14).toNat = 0 := by
      have r852 := hand2 (x 10 1) (x 10 14)
      have b853 := hb (x 10 14)
      have b854 := hb (x 10 1 && x 10 14)
      clear * - r852 b853 b854 d847
      omega
    have d855 : (x 10 2).toNat = 0 := by
      have r856 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
      have b857 := hb (x 10 2)
      have b858 := hb (x 10 14)
      clear * - r856 b857 b858 d847
      omega
    have d859 : (x 9 2).toNat = 0 := by
      have r860 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e861 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e862 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b863 := hb (x 8 3)
      have b864 := hb (x 9 2)
      have b865 := hb (x 10 13)
      have b866 := hb (x 11 12)
      clear * - r860 e861 e862 b863 b864 b865 b866 d703 d719 d699
      omega
    have d867 : (x 11 13).toNat = 1 := by
      have r868 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b869 := hb (x 9 2)
      have b870 := hb (x 11 13)
      have b871 := hb (x 10 1 && x 10 14)
      clear * - r868 b869 b870 b871 d851 d859
      omega
    have d872 : (x 11 1).toNat = 1 := by
      have r873 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have b874 := hb (x 11 1)
      have b875 := hb (x 11 13)
      clear * - r873 b874 b875 d867
      omega
    have d876 : (x 12 14).toNat = 0 := by
      have r877 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b878 := hb (x 11 1)
      have b879 := hb (x 12 14)
      clear * - r877 b878 b879 d872
      omega
    have d880 : (x 12 1 && x 12 14).toNat = 0 := by
      have r881 := hand2 (x 12 1) (x 12 14)
      have b882 := hb (x 12 14)
      have b883 := hb (x 12 1 && x 12 14)
      clear * - r881 b882 b883 d876
      omega
    have d884 : (x 11 2).toNat = 1 := by
      have r885 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b886 := hb (x 11 2)
      have b887 := hb (x 13 13)
      have b888 := hb (x 12 1 && x 12 14)
      clear * - r885 b886 b887 b888 d823 d880
      omega
    have d889 : (x 13 12).toNat = 0 := by
      have r890 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e891 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e892 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b893 := hb (x 10 3)
      have b894 := hb (x 11 2)
      have b895 := hb (x 12 13)
      have b896 := hb (x 13 12)
      clear * - r890 e891 e892 b893 b894 b895 b896 d884
      omega
    have d897 : (x 13 4).toNat = 0 := by
      have r898 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b899 := hb (x 13 4)
      have b900 := hb (x 13 12)
      clear * - r898 b899 b900 d889
      omega
    have d901 : (x 13 4 && x 13 14).toNat = 0 := by
      have r902 := hand1 (x 13 4) (x 13 14)
      have b903 := hb (x 13 4)
      have b904 := hb (x 13 4 && x 13 14)
      clear * - r902 b903 b904 d897
      omega
    have d905 : (x 12 13).toNat = 0 := by
      have r906 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e907 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e908 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b909 := hb (x 10 3)
      have b910 := hb (x 11 2)
      have b911 := hb (x 12 13)
      have b912 := hb (x 13 12)
      clear * - r906 e907 e908 b909 b910 b911 b912 d889 d884
      omega
    have d913 : (x 12 5).toNat = 0 := by
      have r914 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
      have b915 := hb (x 12 5)
      have b916 := hb (x 12 13)
      clear * - r914 b915 b916 d905
      omega
    have d917 : (x 12 3 && x 12 14).toNat = 0 := by
      have r918 := hand2 (x 12 3) (x 12 14)
      have b919 := hb (x 12 14)
      have b920 := hb (x 12 3 && x 12 14)
      clear * - r918 b919 b920 d876
      omega
    have d921 : (x 15 11).toNat = 1 := by
      have r922 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b923 := hb (x 11 4)
      have b924 := hb (x 15 11)
      have b925 := hb (x 14 1 && x 14 12)
      have b926 := hb (x 13 2 && x 13 13)
      have b927 := hb (x 12 3 && x 12 14)
      clear * - r922 b923 b924 b925 b926 b927 d819 d831 d917 d715
      omega
    have d928 : (x 15 3).toNat = 1 := by
      have r929 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
      have b930 := hb (x 15 3)
      have b931 := hb (x 15 11)
      clear * - r929 b930 b931 d921
      omega
    have d932 : (x 18 12).toNat = 0 := by
      have r933 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e934 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e935 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b936 := hb (x 15 3)
      have b937 := hb (x 16 2)
      have b938 := hb (x 17 13)
      have b939 := hb (x 18 12)
      clear * - r933 e934 e935 b936 b937 b938 b939 d928
      omega
    have d940 : (x 17 13).toNat = 0 := by
      have r941 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e942 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e943 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b944 := hb (x 15 3)
      have b945 := hb (x 16 2)
      have b946 := hb (x 17 13)
      have b947 := hb (x 18 12)
      clear * - r941 e942 e943 b944 b945 b946 b947 d932 d928
      omega
    have d948 : (x 16 2).toNat = 0 := by
      have r949 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e950 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e951 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b952 := hb (x 15 3)
      have b953 := hb (x 16 2)
      have b954 := hb (x 17 13)
      have b955 := hb (x 18 12)
      clear * - r949 e950 e951 b952 b953 b954 b955 d932 d940 d928
      omega
    have d956 : (x 12 12).toNat = 0 := by
      have r957 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e958 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e959 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b960 := hb (x 9 3)
      have b961 := hb (x 10 2)
      have b962 := hb (x 11 13)
      have b963 := hb (x 12 12)
      clear * - r957 e958 e959 b960 b961 b962 b963 d867 d855
      omega
    have d964 : (x 12 4).toNat = 0 := by
      have r965 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b966 := hb (x 12 4)
      have b967 := hb (x 12 12)
      clear * - r965 b966 b967 d956
      omega
    have d968 : (x 9 3).toNat = 0 := by
      have r969 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e970 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e971 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b972 := hb (x 9 3)
      have b973 := hb (x 10 2)
      have b974 := hb (x 11 13)
      have b975 := hb (x 12 12)
      clear * - r969 e970 e971 b972 b973 b974 b975 d956 d867 d855
      omega
    have d976 : (x 9 3 && x 9 14).toNat = 0 := by
      have r977 := hand1 (x 9 3) (x 9 14)
      have b978 := hb (x 9 3)
      have b979 := hb (x 9 3 && x 9 14)
      clear * - r977 b978 b979 d968
      omega
    have d980 : (x 12 11).toNat = 1 := by
      have r981 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b982 := hb (x 8 4)
      have b983 := hb (x 12 11)
      have b984 := hb (x 11 1 && x 11 12)
      have b985 := hb (x 10 2 && x 10 13)
      have b986 := hb (x 9 3 && x 9 14)
      clear * - r981 b982 b983 b984 b985 b986 d711 d727 d976 d676
      omega
    have d987 : (x 12 3).toNat = 1 := by
      have r988 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
      have b989 := hb (x 12 3)
      have b990 := hb (x 12 11)
      clear * - r988 b989 b990 d980
      omega
    have d991 : (x 15 12).toNat = 0 := by
      have r992 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e993 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e994 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b995 := hb (x 12 3)
      have b996 := hb (x 13 2)
      have b997 := hb (x 14 13)
      have b998 := hb (x 15 12)
      clear * - r992 e993 e994 b995 b996 b997 b998 d987
      omega
    have d999 : (x 15 1 && x 15 12).toNat = 0 := by
      have r1000 := hand2 (x 15 1) (x 15 12)
      have b1001 := hb (x 15 12)
      have b1002 := hb (x 15 1 && x 15 12)
      clear * - r1000 b1001 b1002 d991
      omega
    have d1003 : (x 15 2 && x 15 12).toNat = 0 := by
      have r1004 := hand2 (x 15 2) (x 15 12)
      have b1005 := hb (x 15 12)
      have b1006 := hb (x 15 2 && x 15 12)
      clear * - r1004 b1005 b1006 d991
      omega
    have d1007 : (x 14 13).toNat = 0 := by
      have r1008 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1009 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e1010 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b1011 := hb (x 12 3)
      have b1012 := hb (x 13 2)
      have b1013 := hb (x 14 13)
      have b1014 := hb (x 15 12)
      clear * - r1008 e1009 e1010 b1011 b1012 b1013 b1014 d991 d987
      omega
    have d1015 : (x 14 2 && x 14 13).toNat = 0 := by
      have r1016 := hand2 (x 14 2) (x 14 13)
      have b1017 := hb (x 14 13)
      have b1018 := hb (x 14 2 && x 14 13)
      clear * - r1016 b1017 b1018 d1007
      omega
    have d1019 : (x 14 3 && x 14 13).toNat = 0 := by
      have r1020 := hand2 (x 14 3) (x 14 13)
      have b1021 := hb (x 14 13)
      have b1022 := hb (x 14 3 && x 14 13)
      clear * - r1020 b1021 b1022 d1007
      omega
    have d1023 : (x 13 1 && x 13 14).toNat = 1 := by
      have r1024 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1025 := hb (x 12 2)
      have b1026 := hb (x 14 13)
      have b1027 := hb (x 13 1 && x 13 14)
      clear * - r1024 b1025 b1026 b1027 d1007 d835
      omega
    have d1028 : (x 13 1).toNat = 1 := by
      have r1029 := hand1 (x 13 1) (x 13 14)
      have b1030 := hb (x 13 1)
      have b1031 := hb (x 13 1 && x 13 14)
      clear * - r1029 b1030 b1031 d1023
      omega
    have d1032 : (x 14 14).toNat = 0 := by
      have r1033 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1034 := hb (x 13 1)
      have b1035 := hb (x 14 14)
      clear * - r1033 b1034 b1035 d1028
      omega
    have d1036 : (x 14 1 && x 14 14).toNat = 0 := by
      have r1037 := hand2 (x 14 1) (x 14 14)
      have b1038 := hb (x 14 14)
      have b1039 := hb (x 14 1 && x 14 14)
      clear * - r1037 b1038 b1039 d1032
      omega
    have d1040 : (x 14 2).toNat = 0 := by
      have r1041 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
      have b1042 := hb (x 14 2)
      have b1043 := hb (x 14 14)
      clear * - r1041 b1042 b1043 d1032
      omega
    have d1044 : (x 13 2).toNat = 0 := by
      have r1045 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1046 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e1047 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b1048 := hb (x 12 3)
      have b1049 := hb (x 13 2)
      have b1050 := hb (x 14 13)
      have b1051 := hb (x 15 12)
      clear * - r1045 e1046 e1047 b1048 b1049 b1050 b1051 d991 d1007 d987
      omega
    have d1052 : (x 15 13).toNat = 1 := by
      have r1053 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1054 := hb (x 13 2)
      have b1055 := hb (x 15 13)
      have b1056 := hb (x 14 1 && x 14 14)
      clear * - r1053 b1054 b1055 b1056 d1036 d1044
      omega
    have d1057 : (x 16 12).toNat = 0 := by
      have r1058 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1059 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e1060 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b1061 := hb (x 13 3)
      have b1062 := hb (x 14 2)
      have b1063 := hb (x 15 13)
      have b1064 := hb (x 16 12)
      clear * - r1058 e1059 e1060 b1061 b1062 b1063 b1064 d1052 d1040
      omega
    have d1065 : (x 13 3).toNat = 0 := by
      have r1066 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1067 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e1068 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b1069 := hb (x 13 3)
      have b1070 := hb (x 14 2)
      have b1071 := hb (x 15 13)
      have b1072 := hb (x 16 12)
      clear * - r1066 e1067 e1068 b1069 b1070 b1071 b1072 d1057 d1052 d1040
      omega
    have d1073 : (x 13 3 && x 13 14).toNat = 0 := by
      have r1074 := hand1 (x 13 3) (x 13 14)
      have b1075 := hb (x 13 3)
      have b1076 := hb (x 13 3 && x 13 14)
      clear * - r1074 b1075 b1076 d1065
      omega
    have d1077 : (x 16 11).toNat = 1 := by
      have r1078 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1079 := hb (x 12 4)
      have b1080 := hb (x 16 11)
      have b1081 := hb (x 15 1 && x 15 12)
      have b1082 := hb (x 14 2 && x 14 13)
      have b1083 := hb (x 13 3 && x 13 14)
      clear * - r1078 b1079 b1080 b1081 b1082 b1083 d999 d1015 d1073 d964
      omega
    have d1084 : (x 16 3).toNat = 1 := by
      have r1085 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
      have b1086 := hb (x 16 3)
      have b1087 := hb (x 16 11)
      clear * - r1085 b1086 b1087 d1077
      omega
    have d1088 : (x 19 12).toNat = 0 := by
      have r1089 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1090 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e1091 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b1092 := hb (x 16 3)
      have b1093 := hb (x 17 2)
      have b1094 := hb (x 18 13)
      have b1095 := hb (x 19 12)
      clear * - r1089 e1090 e1091 b1092 b1093 b1094 b1095 d1084
      omega
    have d1096 : (x 18 13).toNat = 0 := by
      have r1097 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1098 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e1099 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b1100 := hb (x 16 3)
      have b1101 := hb (x 17 2)
      have b1102 := hb (x 18 13)
      have b1103 := hb (x 19 12)
      clear * - r1097 e1098 e1099 b1100 b1101 b1102 b1103 d1088 d1084
      omega
    have d1104 : (x 17 1 && x 17 14).toNat = 1 := by
      have r1105 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1106 := hb (x 16 2)
      have b1107 := hb (x 18 13)
      have b1108 := hb (x 17 1 && x 17 14)
      clear * - r1105 b1106 b1107 b1108 d1096 d948
      omega
    have d1109 : (x 17 14).toNat = 1 := by
      have r1110 := hand2 (x 17 1) (x 17 14)
      have b1111 := hb (x 17 14)
      have b1112 := hb (x 17 1 && x 17 14)
      clear * - r1110 b1111 b1112 d1104
      omega
    have d1113 : (x 16 1).toNat = 0 := by
      have r1114 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1115 := hb (x 16 1)
      have b1116 := hb (x 17 14)
      clear * - r1114 b1115 b1116 d1109
      omega
    have d1117 : (x 16 1 && x 16 11).toNat = 0 := by
      have r1118 := hand1 (x 16 1) (x 16 11)
      have b1119 := hb (x 16 1)
      have b1120 := hb (x 16 1 && x 16 11)
      clear * - r1118 b1119 b1120 d1113
      omega
    have d1121 : (x 17 2).toNat = 0 := by
      have r1122 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1123 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e1124 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b1125 := hb (x 16 3)
      have b1126 := hb (x 17 2)
      have b1127 := hb (x 18 13)
      have b1128 := hb (x 19 12)
      clear * - r1122 e1123 e1124 b1125 b1126 b1127 b1128 d1088 d1096 d1084
      omega
    have d1129 : (x 17 10).toNat = 0 := by
      have r1130 : (x 17 10).toNat ≤ (x 17 2).toNat := himp _ _ (hp10 17)
      have b1131 := hb (x 17 2)
      have b1132 := hb (x 17 10)
      clear * - r1130 b1131 b1132 d1121
      omega
    have r1133 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := by have q := hcov10 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1134 := hb (x 12 5)
    have b1135 := hb (x 17 10)
    have b1136 := hb (x 16 1 && x 16 11)
    have b1137 := hb (x 15 2 && x 15 12)
    have b1138 := hb (x 14 3 && x 14 13)
    have b1139 := hb (x 13 4 && x 13 14)
    linarith only [r1133, b1134, b1135, b1136, b1137, b1138, b1139, d1129, d1117, d1003, d1019, d901, d913]
  · have f1140 : (x 0 2).toNat = 1 := by rw [h507]; rfl
    have d1141 : (x 0 14).toNat = 1 := by
      have r1142 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b1143 := hb (x 0 2)
      have b1144 := hb (x 0 14)
      clear * - r1142 b1143 b1144 f1140
      omega
    have d1145 : (x (-1) 1).toNat = 0 := by
      have r1146 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b1147 := hb (x (-1) 1)
      have b1148 := hb (x 0 14)
      clear * - r1146 b1147 b1148 d1141
      omega
    have d1149 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r1150 := hand1 (x (-1) 1) (x (-1) 14)
      have b1151 := hb (x (-1) 1)
      have b1152 := hb (x (-1) 1 && x (-1) 14)
      clear * - r1150 b1151 b1152 d1145
      omega
    have d1153 : (x (-1) 13).toNat = 0 := by
      have r1154 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b1155 := hb (x (-1) 1)
      have b1156 := hb (x (-1) 13)
      clear * - r1154 b1155 b1156 d1145
      omega
    have d1157 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
      have r1158 := hand2 (x (-1) 2) (x (-1) 13)
      have b1159 := hb (x (-1) 13)
      have b1160 := hb (x (-1) 2 && x (-1) 13)
      clear * - r1158 b1159 b1160 d1153
      omega
    have d1161 : (x 2 12).toNat = 0 := by
      have r1162 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1163 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e1164 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b1165 := hb (x (-1) 3)
      have b1166 := hb (x 0 2)
      have b1167 := hb (x 1 13)
      have b1168 := hb (x 2 12)
      clear * - r1162 e1163 e1164 b1165 b1166 b1167 b1168 f1140
      omega
    have d1169 : (x 1 13).toNat = 0 := by
      have r1170 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1171 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e1172 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b1173 := hb (x (-1) 3)
      have b1174 := hb (x 0 2)
      have b1175 := hb (x 1 13)
      have b1176 := hb (x 2 12)
      clear * - r1170 e1171 e1172 b1173 b1174 b1175 b1176 d1161 f1140
      omega
    have d1177 : (x (-1) 3).toNat = 0 := by
      have r1178 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1179 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e1180 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b1181 := hb (x (-1) 3)
      have b1182 := hb (x 0 2)
      have b1183 := hb (x 1 13)
      have b1184 := hb (x 2 12)
      clear * - r1178 e1179 e1180 b1181 b1182 b1183 b1184 d1161 d1169 f1140
      omega
    have d1185 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
      have r1186 := hand1 (x (-1) 3) (x (-1) 14)
      have b1187 := hb (x (-1) 3)
      have b1188 := hb (x (-1) 3 && x (-1) 14)
      clear * - r1186 b1187 b1188 d1177
      omega
    cases h1189 : x 0 1
    · have f1190 : (x 0 1).toNat = 0 := by rw [h1189]; rfl
      have d1191 : (x 0 1 && x 0 14).toNat = 0 := by
        have r1192 := hand1 (x 0 1) (x 0 14)
        have b1193 := hb (x 0 1)
        have b1194 := hb (x 0 1 && x 0 14)
        clear * - r1192 b1193 b1194 f1190
        omega
      have d1195 : (x 0 13).toNat = 0 := by
        have r1196 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
        have b1197 := hb (x 0 1)
        have b1198 := hb (x 0 13)
        clear * - r1196 b1197 b1198 f1190
        omega
      have d1199 : (x 0 2 && x 0 13).toNat = 0 := by
        have r1200 := hand2 (x 0 2) (x 0 13)
        have b1201 := hb (x 0 13)
        have b1202 := hb (x 0 2 && x 0 13)
        clear * - r1200 b1201 b1202 d1195
        omega
      have d1203 : (x (-1) 2).toNat = 1 := by
        have r1204 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1205 := hb (x (-1) 2)
        have b1206 := hb (x 1 13)
        have b1207 := hb (x 0 1 && x 0 14)
        clear * - r1204 b1205 b1206 b1207 d1169 d1191
        omega
      have d1208 : (x (-1) 14).toNat = 1 := by
        have r1209 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b1210 := hb (x (-1) 2)
        have b1211 := hb (x (-1) 14)
        clear * - r1209 b1210 b1211 d1203
        omega
      have d1212 : (x (-2) 1).toNat = 0 := by
        have r1213 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1214 := hb (x (-2) 1)
        have b1215 := hb (x (-1) 14)
        clear * - r1213 b1214 b1215 d1208
        omega
      have d1216 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r1217 := hand1 (x (-2) 1) (x (-2) 14)
        have b1218 := hb (x (-2) 1)
        have b1219 := hb (x (-2) 1 && x (-2) 14)
        clear * - r1217 b1218 b1219 d1212
        omega
      have d1220 : (x (-2) 13).toNat = 0 := by
        have r1221 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b1222 := hb (x (-2) 1)
        have b1223 := hb (x (-2) 13)
        clear * - r1221 b1222 b1223 d1212
        omega
      have d1224 : (x (-2) 2).toNat = 1 := by
        have r1225 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1226 := hb (x (-2) 2)
        have b1227 := hb (x 0 13)
        have b1228 := hb (x (-1) 1 && x (-1) 14)
        clear * - r1225 b1226 b1227 b1228 d1195 d1149
        omega
      have d1229 : (x (-2) 14).toNat = 1 := by
        have r1230 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
        have b1231 := hb (x (-2) 2)
        have b1232 := hb (x (-2) 14)
        clear * - r1230 b1231 b1232 d1224
        omega
      have d1233 : (x (-3) 1).toNat = 0 := by
        have r1234 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1235 := hb (x (-3) 1)
        have b1236 := hb (x (-2) 14)
        clear * - r1234 b1235 b1236 d1229
        omega
      have d1237 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
        have r1238 := hand1 (x (-3) 1) (x (-3) 14)
        have b1239 := hb (x (-3) 1)
        have b1240 := hb (x (-3) 1 && x (-3) 14)
        clear * - r1238 b1239 b1240 d1233
        omega
      have d1241 : (x (-3) 13).toNat = 0 := by
        have r1242 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
        have b1243 := hb (x (-3) 1)
        have b1244 := hb (x (-3) 13)
        clear * - r1242 b1243 b1244 d1233
        omega
      have d1245 : (x (-3) 2).toNat = 1 := by
        have r1246 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1247 := hb (x (-3) 2)
        have b1248 := hb (x (-1) 13)
        have b1249 := hb (x (-2) 1 && x (-2) 14)
        clear * - r1246 b1247 b1248 b1249 d1153 d1216
        omega
      have d1250 : (x (-3) 14).toNat = 1 := by
        have r1251 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b1252 := hb (x (-3) 2)
        have b1253 := hb (x (-3) 14)
        clear * - r1251 b1252 b1253 d1245
        omega
      have d1254 : (x (-4) 1).toNat = 0 := by
        have r1255 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1256 := hb (x (-4) 1)
        have b1257 := hb (x (-3) 14)
        clear * - r1255 b1256 b1257 d1250
        omega
      have d1258 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
        have r1259 := hand1 (x (-4) 1) (x (-4) 14)
        have b1260 := hb (x (-4) 1)
        have b1261 := hb (x (-4) 1 && x (-4) 14)
        clear * - r1259 b1260 b1261 d1254
        omega
      have d1262 : (x (-4) 13).toNat = 0 := by
        have r1263 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b1264 := hb (x (-4) 1)
        have b1265 := hb (x (-4) 13)
        clear * - r1263 b1264 b1265 d1254
        omega
      have d1266 : (x (-4) 2).toNat = 1 := by
        have r1267 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1268 := hb (x (-4) 2)
        have b1269 := hb (x (-2) 13)
        have b1270 := hb (x (-3) 1 && x (-3) 14)
        clear * - r1267 b1268 b1269 b1270 d1220 d1237
        omega
      have d1271 : (x (-5) 2).toNat = 1 := by
        have r1272 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1273 := hb (x (-5) 2)
        have b1274 := hb (x (-3) 13)
        have b1275 := hb (x (-4) 1 && x (-4) 14)
        clear * - r1272 b1273 b1274 b1275 d1241 d1258
        omega
      have d1276 : (x 1 12).toNat = 0 := by
        have r1277 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1278 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e1279 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b1280 := hb (x (-2) 3)
        have b1281 := hb (x (-1) 2)
        have b1282 := hb (x 0 13)
        have b1283 := hb (x 1 12)
        clear * - r1277 e1278 e1279 b1280 b1281 b1282 b1283 d1195 d1203
        omega
      have d1284 : (x 1 1 && x 1 12).toNat = 0 := by
        have r1285 := hand2 (x 1 1) (x 1 12)
        have b1286 := hb (x 1 12)
        have b1287 := hb (x 1 1 && x 1 12)
        clear * - r1285 b1286 b1287 d1276
        omega
      have d1288 : (x (-2) 3).toNat = 0 := by
        have r1289 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1290 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e1291 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b1292 := hb (x (-2) 3)
        have b1293 := hb (x (-1) 2)
        have b1294 := hb (x 0 13)
        have b1295 := hb (x 1 12)
        clear * - r1289 e1290 e1291 b1292 b1293 b1294 b1295 d1276 d1195 d1203
        omega
      have d1296 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
        have r1297 := hand1 (x (-2) 3) (x (-2) 14)
        have b1298 := hb (x (-2) 3)
        have b1299 := hb (x (-2) 3 && x (-2) 14)
        clear * - r1297 b1298 b1299 d1288
        omega
      have d1300 : (x (-2) 12).toNat = 0 := by
        have r1301 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1302 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e1303 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b1304 := hb (x (-5) 3)
        have b1305 := hb (x (-4) 2)
        have b1306 := hb (x (-3) 13)
        have b1307 := hb (x (-2) 12)
        clear * - r1301 e1302 e1303 b1304 b1305 b1306 b1307 d1241 d1266
        omega
      have d1308 : (x (-2) 4).toNat = 0 := by
        have r1309 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have b1310 := hb (x (-2) 4)
        have b1311 := hb (x (-2) 12)
        clear * - r1309 b1310 b1311 d1300
        omega
      have d1312 : (x (-3) 12).toNat = 0 := by
        have r1313 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1314 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e1315 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b1316 := hb (x (-6) 3)
        have b1317 := hb (x (-5) 2)
        have b1318 := hb (x (-4) 13)
        have b1319 := hb (x (-3) 12)
        clear * - r1313 e1314 e1315 b1316 b1317 b1318 b1319 d1262 d1271
        omega
      have d1320 : (x (-3) 4).toNat = 0 := by
        have r1321 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b1322 := hb (x (-3) 4)
        have b1323 := hb (x (-3) 12)
        clear * - r1321 b1322 b1323 d1312
        omega
      have d1324 : (x 2 11).toNat = 1 := by
        have r1325 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1326 := hb (x (-2) 4)
        have b1327 := hb (x 2 11)
        have b1328 := hb (x 1 1 && x 1 12)
        have b1329 := hb (x 0 2 && x 0 13)
        have b1330 := hb (x (-1) 3 && x (-1) 14)
        clear * - r1325 b1326 b1327 b1328 b1329 b1330 d1284 d1199 d1185 d1308
        omega
      have d1331 : (x 2 3).toNat = 1 := by
        have r1332 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
        have b1333 := hb (x 2 3)
        have b1334 := hb (x 2 11)
        clear * - r1332 b1333 b1334 d1324
        omega
      have d1335 : (x 5 12).toNat = 0 := by
        have r1336 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1337 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e1338 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b1339 := hb (x 2 3)
        have b1340 := hb (x 3 2)
        have b1341 := hb (x 4 13)
        have b1342 := hb (x 5 12)
        clear * - r1336 e1337 e1338 b1339 b1340 b1341 b1342 d1331
        omega
      have d1343 : (x 4 13).toNat = 0 := by
        have r1344 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1345 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e1346 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b1347 := hb (x 2 3)
        have b1348 := hb (x 3 2)
        have b1349 := hb (x 4 13)
        have b1350 := hb (x 5 12)
        clear * - r1344 e1345 e1346 b1347 b1348 b1349 b1350 d1335 d1331
        omega
      have d1351 : (x 1 11).toNat = 1 := by
        have r1352 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1353 := hb (x (-3) 4)
        have b1354 := hb (x 1 11)
        have b1355 := hb (x 0 1 && x 0 12)
        have b1356 := hb (x (-1) 2 && x (-1) 13)
        have b1357 := hb (x (-2) 3 && x (-2) 14)
        clear * - r1352 b1353 b1354 b1355 b1356 b1357 d499 d1157 d1296 d1320
        omega
      have d1358 : (x 1 3).toNat = 1 := by
        have r1359 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b1360 := hb (x 1 3)
        have b1361 := hb (x 1 11)
        clear * - r1359 b1360 b1361 d1351
        omega
      have d1362 : (x 4 12).toNat = 0 := by
        have r1363 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1364 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e1365 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b1366 := hb (x 1 3)
        have b1367 := hb (x 2 2)
        have b1368 := hb (x 3 13)
        have b1369 := hb (x 4 12)
        clear * - r1363 e1364 e1365 b1366 b1367 b1368 b1369 d1358
        omega
      have d1370 : (x 3 13).toNat = 0 := by
        have r1371 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1372 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e1373 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b1374 := hb (x 1 3)
        have b1375 := hb (x 2 2)
        have b1376 := hb (x 3 13)
        have b1377 := hb (x 4 12)
        clear * - r1371 e1372 e1373 b1374 b1375 b1376 b1377 d1362 d1358
        omega
      have d1378 : (x 2 1 && x 2 14).toNat = 1 := by
        have r1379 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1380 := hb (x 1 2)
        have b1381 := hb (x 3 13)
        have b1382 := hb (x 2 1 && x 2 14)
        clear * - r1379 b1380 b1381 b1382 d1370 g4
        omega
      have d1383 : (x 2 1).toNat = 1 := by
        have r1384 := hand1 (x 2 1) (x 2 14)
        have b1385 := hb (x 2 1)
        have b1386 := hb (x 2 1 && x 2 14)
        clear * - r1384 b1385 b1386 d1378
        omega
      have d1387 : (x 3 14).toNat = 0 := by
        have r1388 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1389 := hb (x 2 1)
        have b1390 := hb (x 3 14)
        clear * - r1388 b1389 b1390 d1383
        omega
      have d1391 : (x 3 1 && x 3 14).toNat = 0 := by
        have r1392 := hand2 (x 3 1) (x 3 14)
        have b1393 := hb (x 3 14)
        have b1394 := hb (x 3 1 && x 3 14)
        clear * - r1392 b1393 b1394 d1387
        omega
      have d1395 : (x 2 2).toNat = 1 := by
        have r1396 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1397 := hb (x 2 2)
        have b1398 := hb (x 4 13)
        have b1399 := hb (x 3 1 && x 3 14)
        clear * - r1396 b1397 b1398 b1399 d1343 d1391
        omega
      have r1400 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1401 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e1402 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b1403 := hb (x 1 3)
      have b1404 := hb (x 2 2)
      have b1405 := hb (x 3 13)
      have b1406 := hb (x 4 12)
      linarith only [r1400, e1401, e1402, b1403, b1404, b1405, b1406, d1362, d1370, d1395, d1358]
    · have f1407 : (x 0 1).toNat = 1 := by rw [h1189]; rfl
      have d1408 : (x 1 14).toNat = 0 := by
        have r1409 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1410 := hb (x 0 1)
        have b1411 := hb (x 1 14)
        clear * - r1409 b1410 b1411 f1407
        omega
      have d1412 : (x 1 3 && x 1 14).toNat = 0 := by
        have r1413 := hand2 (x 1 3) (x 1 14)
        have b1414 := hb (x 1 14)
        have b1415 := hb (x 1 3 && x 1 14)
        clear * - r1413 b1414 b1415 d1408
        omega
      have d1416 : (x 1 4 && x 1 14).toNat = 0 := by
        have r1417 := hand2 (x 1 4) (x 1 14)
        have b1418 := hb (x 1 14)
        have b1419 := hb (x 1 4 && x 1 14)
        clear * - r1417 b1418 b1419 d1408
        omega
      have d1420 : (x 1 6).toNat = 0 := by
        have r1421 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
        have b1422 := hb (x 1 6)
        have b1423 := hb (x 1 14)
        clear * - r1421 b1422 b1423 d1408
        omega
      have d1424 : (x 4 11).toNat = 1 := by
        have r1425 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1426 := hb (x 0 4)
        have b1427 := hb (x 4 11)
        have b1428 := hb (x 3 1 && x 3 12)
        have b1429 := hb (x 2 2 && x 2 13)
        have b1430 := hb (x 1 3 && x 1 14)
        clear * - r1425 b1426 b1427 b1428 b1429 b1430 g20 g21 d1412 g1
        omega
      have d1431 : (x 4 3).toNat = 1 := by
        have r1432 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
        have b1433 := hb (x 4 3)
        have b1434 := hb (x 4 11)
        clear * - r1432 b1433 b1434 d1424
        omega
      have d1435 : (x 7 12).toNat = 0 := by
        have r1436 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1437 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e1438 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b1439 := hb (x 4 3)
        have b1440 := hb (x 5 2)
        have b1441 := hb (x 6 13)
        have b1442 := hb (x 7 12)
        clear * - r1436 e1437 e1438 b1439 b1440 b1441 b1442 d1431
        omega
      have d1443 : (x 7 1 && x 7 12).toNat = 0 := by
        have r1444 := hand2 (x 7 1) (x 7 12)
        have b1445 := hb (x 7 12)
        have b1446 := hb (x 7 1 && x 7 12)
        clear * - r1444 b1445 b1446 d1435
        omega
      have d1447 : (x 7 4).toNat = 0 := by
        have r1448 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
        have b1449 := hb (x 7 4)
        have b1450 := hb (x 7 12)
        clear * - r1448 b1449 b1450 d1435
        omega
      have d1451 : (x 7 4 && x 7 9).toNat = 0 := by
        have r1452 := hand1 (x 7 4) (x 7 9)
        have b1453 := hb (x 7 4)
        have b1454 := hb (x 7 4 && x 7 9)
        clear * - r1452 b1453 b1454 d1447
        omega
      have d1455 : (x 6 13).toNat = 0 := by
        have r1456 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1457 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e1458 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b1459 := hb (x 4 3)
        have b1460 := hb (x 5 2)
        have b1461 := hb (x 6 13)
        have b1462 := hb (x 7 12)
        clear * - r1456 e1457 e1458 b1459 b1460 b1461 b1462 d1435 d1431
        omega
      have d1463 : (x 6 2 && x 6 13).toNat = 0 := by
        have r1464 := hand2 (x 6 2) (x 6 13)
        have b1465 := hb (x 6 13)
        have b1466 := hb (x 6 2 && x 6 13)
        clear * - r1464 b1465 b1466 d1455
        omega
      have d1467 : (x 6 5).toNat = 0 := by
        have r1468 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
        have b1469 := hb (x 6 5)
        have b1470 := hb (x 6 13)
        clear * - r1468 b1469 b1470 d1455
        omega
      have d1471 : (x 6 5 && x 6 10).toNat = 0 := by
        have r1472 := hand1 (x 6 5) (x 6 10)
        have b1473 := hb (x 6 5)
        have b1474 := hb (x 6 5 && x 6 10)
        clear * - r1472 b1473 b1474 d1467
        omega
      have d1475 : (x 5 2).toNat = 0 := by
        have r1476 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1477 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e1478 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b1479 := hb (x 4 3)
        have b1480 := hb (x 5 2)
        have b1481 := hb (x 6 13)
        have b1482 := hb (x 7 12)
        clear * - r1476 e1477 e1478 b1479 b1480 b1481 b1482 d1435 d1455 d1431
        omega
      have d1483 : (x 5 2 && x 5 11).toNat = 0 := by
        have r1484 := hand1 (x 5 2) (x 5 11)
        have b1485 := hb (x 5 2)
        have b1486 := hb (x 5 2 && x 5 11)
        clear * - r1484 b1485 b1486 d1475
        omega
      have d1487 : (x 5 10).toNat = 0 := by
        have r1488 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
        have b1489 := hb (x 5 2)
        have b1490 := hb (x 5 10)
        clear * - r1488 b1489 b1490 d1475
        omega
      have d1491 : (x 5 10 && x 5 11).toNat = 0 := by
        have r1492 := hand1 (x 5 10) (x 5 11)
        have b1493 := hb (x 5 10)
        have b1494 := hb (x 5 10 && x 5 11)
        clear * - r1492 b1493 b1494 d1487
        omega
      have d1495 : (x 4 1 && x 4 11).toNat = 1 := by
        have r1496 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1497 := hb (x 0 5)
        have b1498 := hb (x 5 10)
        have b1499 := hb (x 4 1 && x 4 11)
        have b1500 := hb (x 3 2 && x 3 12)
        have b1501 := hb (x 2 3 && x 2 13)
        have b1502 := hb (x 1 4 && x 1 14)
        clear * - r1496 b1497 b1498 b1499 b1500 b1501 b1502 d1487 g18 g19 d1416 g2
        omega
      have d1503 : (x 4 1).toNat = 1 := by
        have r1504 := hand1 (x 4 1) (x 4 11)
        have b1505 := hb (x 4 1)
        have b1506 := hb (x 4 1 && x 4 11)
        clear * - r1504 b1505 b1506 d1495
        omega
      have d1507 : (x 5 14).toNat = 0 := by
        have r1508 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1509 := hb (x 4 1)
        have b1510 := hb (x 5 14)
        clear * - r1508 b1509 b1510 d1503
        omega
      have d1511 : (x 5 1 && x 5 14).toNat = 0 := by
        have r1512 := hand2 (x 5 1) (x 5 14)
        have b1513 := hb (x 5 14)
        have b1514 := hb (x 5 1 && x 5 14)
        clear * - r1512 b1513 b1514 d1507
        omega
      have d1515 : (x 4 2).toNat = 1 := by
        have r1516 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1517 := hb (x 4 2)
        have b1518 := hb (x 6 13)
        have b1519 := hb (x 5 1 && x 5 14)
        clear * - r1516 b1517 b1518 b1519 d1455 d1511
        omega
      have d1520 : (x 4 14).toNat = 1 := by
        have r1521 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
        have b1522 := hb (x 4 2)
        have b1523 := hb (x 4 14)
        clear * - r1521 b1522 b1523 d1515
        omega
      have d1524 : (x 3 1).toNat = 0 := by
        have r1525 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1526 := hb (x 3 1)
        have b1527 := hb (x 4 14)
        clear * - r1525 b1526 b1527 d1520
        omega
      have d1528 : (x 3 13).toNat = 0 := by
        have r1529 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b1530 := hb (x 3 1)
        have b1531 := hb (x 3 13)
        clear * - r1529 b1530 b1531 d1524
        omega
      have d1532 : (x 3 5).toNat = 0 := by
        have r1533 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
        have b1534 := hb (x 3 5)
        have b1535 := hb (x 3 13)
        clear * - r1533 b1534 b1535 d1528
        omega
      have d1536 : (x 2 1 && x 2 14).toNat = 1 := by
        have r1537 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1538 := hb (x 1 2)
        have b1539 := hb (x 3 13)
        have b1540 := hb (x 2 1 && x 2 14)
        clear * - r1537 b1538 b1539 b1540 d1528 g4
        omega
      have d1541 : (x 2 14).toNat = 1 := by
        have r1542 := hand2 (x 2 1) (x 2 14)
        have b1543 := hb (x 2 14)
        have b1544 := hb (x 2 1 && x 2 14)
        clear * - r1542 b1543 b1544 d1536
        omega
      have d1545 : (x 3 9).toNat = 0 := by
        have r1546 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
        have b1547 := hb (x 3 1)
        have b1548 := hb (x 3 9)
        clear * - r1546 b1547 b1548 d1524
        omega
      have d1549 : (x 5 3 && x 5 14).toNat = 0 := by
        have r1550 := hand2 (x 5 3) (x 5 14)
        have b1551 := hb (x 5 14)
        have b1552 := hb (x 5 3 && x 5 14)
        clear * - r1550 b1551 b1552 d1507
        omega
      have d1553 : (x 5 6).toNat = 0 := by
        have r1554 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
        have b1555 := hb (x 5 6)
        have b1556 := hb (x 5 14)
        clear * - r1554 b1555 b1556 d1507
        omega
      have d1557 : (x 5 6 && x 5 11).toNat = 0 := by
        have r1558 := hand1 (x 5 6) (x 5 11)
        have b1559 := hb (x 5 6)
        have b1560 := hb (x 5 6 && x 5 11)
        clear * - r1558 b1559 b1560 d1553
        omega
      have d1561 : (x 2 1 && x 2 10).toNat = 1 := by
        have r1562 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1563 := hb (x (-3) 6)
        have b1564 := hb (x 3 9)
        have b1565 := hb (x 2 1 && x 2 10)
        have b1566 := hb (x 1 2 && x 1 11)
        have b1567 := hb (x 0 3 && x 0 12)
        have b1568 := hb (x (-1) 4 && x (-1) 13)
        have b1569 := hb (x (-2) 5 && x (-2) 14)
        clear * - r1562 b1563 b1564 b1565 b1566 b1567 b1568 b1569 d1545 g13 d503 g14 g15 g0
        omega
      have d1570 : (x 2 10).toNat = 1 := by
        have r1571 := hand2 (x 2 1) (x 2 10)
        have b1572 := hb (x 2 10)
        have b1573 := hb (x 2 1 && x 2 10)
        clear * - r1571 b1572 b1573 d1561
        omega
      have d1574 : (x 2 2).toNat = 1 := by
        have r1575 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
        have b1576 := hb (x 2 2)
        have b1577 := hb (x 2 10)
        clear * - r1575 b1576 b1577 d1570
        omega
      have d1578 : (x 4 12).toNat = 0 := by
        have r1579 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1580 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e1581 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b1582 := hb (x 1 3)
        have b1583 := hb (x 2 2)
        have b1584 := hb (x 3 13)
        have b1585 := hb (x 4 12)
        clear * - r1579 e1580 e1581 b1582 b1583 b1584 b1585 d1528 d1574
        omega
      have d1586 : (x 4 3 && x 4 12).toNat = 0 := by
        have r1587 := hand2 (x 4 3) (x 4 12)
        have b1588 := hb (x 4 12)
        have b1589 := hb (x 4 3 && x 4 12)
        clear * - r1587 b1588 b1589 d1578
        omega
      have d1590 : (x 4 7 && x 4 12).toNat = 0 := by
        have r1591 := hand2 (x 4 7) (x 4 12)
        have b1592 := hb (x 4 12)
        have b1593 := hb (x 4 7 && x 4 12)
        clear * - r1591 b1592 b1593 d1578
        omega
      have d1594 : (x 4 11 && x 4 12).toNat = 0 := by
        have r1595 := hand2 (x 4 11) (x 4 12)
        have b1596 := hb (x 4 12)
        have b1597 := hb (x 4 11 && x 4 12)
        clear * - r1595 b1596 b1597 d1578
        omega
      have d1598 : (x 4 4).toNat = 0 := by
        have r1599 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b1600 := hb (x 4 4)
        have b1601 := hb (x 4 12)
        clear * - r1599 b1600 b1601 d1578
        omega
      have d1602 : (x 8 11).toNat = 1 := by
        have r1603 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b1604 := hb (x 4 4)
        have b1605 := hb (x 8 11)
        have b1606 := hb (x 7 1 && x 7 12)
        have b1607 := hb (x 6 2 && x 6 13)
        have b1608 := hb (x 5 3 && x 5 14)
        clear * - r1603 b1604 b1605 b1606 b1607 b1608 d1443 d1463 d1549 d1598
        omega
      have d1609 : (x 8 3).toNat = 1 := by
        have r1610 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b1611 := hb (x 8 3)
        have b1612 := hb (x 8 11)
        clear * - r1610 b1611 b1612 d1602
        omega
      have d1613 : (x 11 12).toNat = 0 := by
        have r1614 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1615 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e1616 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b1617 := hb (x 8 3)
        have b1618 := hb (x 9 2)
        have b1619 := hb (x 10 13)
        have b1620 := hb (x 11 12)
        clear * - r1614 e1615 e1616 b1617 b1618 b1619 b1620 d1609
        omega
      have d1621 : (x 11 4).toNat = 0 := by
        have r1622 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
        have b1623 := hb (x 11 4)
        have b1624 := hb (x 11 12)
        clear * - r1622 b1623 b1624 d1613
        omega
      have d1625 : (x 11 4 && x 11 5).toNat = 0 := by
        have r1626 := hand1 (x 11 4) (x 11 5)
        have b1627 := hb (x 11 4)
        have b1628 := hb (x 11 4 && x 11 5)
        clear * - r1626 b1627 b1628 d1621
        omega
      have d1629 : (x 10 13).toNat = 0 := by
        have r1630 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1631 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e1632 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b1633 := hb (x 8 3)
        have b1634 := hb (x 9 2)
        have b1635 := hb (x 10 13)
        have b1636 := hb (x 11 12)
        clear * - r1630 e1631 e1632 b1633 b1634 b1635 b1636 d1613 d1609
        omega
      have d1637 : (x 10 5).toNat = 0 := by
        have r1638 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
        have b1639 := hb (x 10 5)
        have b1640 := hb (x 10 13)
        clear * - r1638 b1639 b1640 d1629
        omega
      have d1641 : (x 10 5 && x 10 6).toNat = 0 := by
        have r1642 := hand1 (x 10 5) (x 10 6)
        have b1643 := hb (x 10 5)
        have b1644 := hb (x 10 5 && x 10 6)
        clear * - r1642 b1643 b1644 d1637
        omega
      have d1645 : (x 9 2).toNat = 0 := by
        have r1646 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1647 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e1648 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b1649 := hb (x 8 3)
        have b1650 := hb (x 9 2)
        have b1651 := hb (x 10 13)
        have b1652 := hb (x 11 12)
        clear * - r1646 e1647 e1648 b1649 b1650 b1651 b1652 d1613 d1629 d1609
        omega
      have d1653 : (x 9 2 && x 9 7).toNat = 0 := by
        have r1654 := hand1 (x 9 2) (x 9 7)
        have b1655 := hb (x 9 2)
        have b1656 := hb (x 9 2 && x 9 7)
        clear * - r1654 b1655 b1656 d1645
        omega
      have d1657 : (x 7 8).toNat = 0 := by
        have r1658 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1659 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e1660 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e1661 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e1662 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e1663 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e1664 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b1665 := hb (x 0 7)
        have b1666 := hb (x 1 6)
        have b1667 := hb (x 2 5)
        have b1668 := hb (x 3 4)
        have b1669 := hb (x 4 11)
        have b1670 := hb (x 5 10)
        have b1671 := hb (x 6 9)
        have b1672 := hb (x 7 8)
        clear * - r1658 e1659 e1660 e1661 e1662 e1663 e1664 b1665 b1666 b1667 b1668 b1669 b1670 b1671 b1672 d1487 d1424 g8 g6 d1420
        omega
      have d1673 : (x 7 8 && x 7 9).toNat = 0 := by
        have r1674 := hand1 (x 7 8) (x 7 9)
        have b1675 := hb (x 7 8)
        have b1676 := hb (x 7 8 && x 7 9)
        clear * - r1674 b1675 b1676 d1657
        omega
      have d1677 : (x 6 9).toNat = 0 := by
        have r1678 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e1679 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e1680 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e1681 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e1682 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e1683 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e1684 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b1685 := hb (x 0 7)
        have b1686 := hb (x 1 6)
        have b1687 := hb (x 2 5)
        have b1688 := hb (x 3 4)
        have b1689 := hb (x 4 11)
        have b1690 := hb (x 5 10)
        have b1691 := hb (x 6 9)
        have b1692 := hb (x 7 8)
        clear * - r1678 e1679 e1680 e1681 e1682 e1683 e1684 b1685 b1686 b1687 b1688 b1689 b1690 b1691 b1692 d1657 d1487 d1424 g8 g6 d1420
        omega
      have d1693 : (x 6 9 && x 6 10).toNat = 0 := by
        have r1694 := hand1 (x 6 9) (x 6 10)
        have b1695 := hb (x 6 9)
        have b1696 := hb (x 6 9 && x 6 10)
        clear * - r1694 b1695 b1696 d1677
        omega
      have r1697 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1698 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e1699 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e1700 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e1701 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e1702 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e1703 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e1704 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r1705 : 1 ≤ (x 15 1).toNat + (x 14 1 && x 14 2).toNat + (x 13 2 && x 13 3).toNat + (x 12 3 && x 12 4).toNat + (x 11 4 && x 11 5).toNat + (x 10 5 && x 10 6).toNat + (x 9 6 && x 9 7).toNat + (x 8 7 && x 8 8).toNat + (x 7 8 && x 7 9).toNat + (x 6 9 && x 6 10).toNat + (x 5 10 && x 5 11).toNat + (x 4 11 && x 4 12).toNat + (x 3 12 && x 3 13).toNat + (x 2 13 && x 2 14).toNat + (x 1 14).toNat := by have q := hcov1 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1706 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1707 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r1708 := hand2 (x 14 1) (x 14 2)
      have r1709 := hand2 (x 13 2) (x 13 3)
      have r1710 := hand2 (x 12 3) (x 12 4)
      have r1711 := hand2 (x 9 6) (x 9 7)
      have r1712 := hand2 (x 8 7) (x 8 8)
      have r1713 := hand2 (x 10 1) (x 10 6)
      have r1714 := hand2 (x 8 3) (x 8 8)
      have r1715 := hand2 (x 6 1) (x 6 10)
      linarith only [r1697, r1698, e1699, e1700, e1701, e1702, e1703, e1704, r1705, r1706, r1707, r1708, r1709, r1710, r1711, r1712, r1713, r1714, r1715, d1420, g5, d1408, d1541, d1532, d1528, d1598, d1578, d1625, d1641, d1673, d1693, d1491, d1594, g9, g10, d1653, d1451, d1471, d1557, d1590, g11, g12, d1483, d1586, g16, g17]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0010_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 2).toNat = 0)
    (g1 : (x 0 1).toNat = 0)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 2 13).toNat = 0)
    (g5 : (x 3 4).toNat = 0)
    (g6 : (x 3 1 && x 3 12).toNat = 0)
    (g7 : (x 2 2 && x 2 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d1863 : (x 0 13).toNat = 0 := by
    have r1864 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b1865 := hb (x 0 1)
    have b1866 := hb (x 0 13)
    clear * - r1864 b1865 b1866 g1
    omega
  have d1867 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
    have r1868 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1869 := hb (x (-2) 2)
    have b1870 := hb (x 0 13)
    have b1871 := hb (x (-1) 1 && x (-1) 14)
    clear * - r1868 b1869 b1870 b1871 d1863 g0
    omega
  have d1872 : (x (-1) 1).toNat = 1 := by
    have r1873 := hand1 (x (-1) 1) (x (-1) 14)
    have b1874 := hb (x (-1) 1)
    have b1875 := hb (x (-1) 1 && x (-1) 14)
    clear * - r1873 b1874 b1875 d1867
    omega
  have d1876 : (x 0 14).toNat = 0 := by
    have r1877 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1878 := hb (x (-1) 1)
    have b1879 := hb (x 0 14)
    clear * - r1877 b1878 b1879 d1872
    omega
  have d1880 : (x 0 2).toNat = 0 := by
    have r1881 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b1882 := hb (x 0 2)
    have b1883 := hb (x 0 14)
    clear * - r1881 b1882 b1883 d1876
    omega
  have d1884 : (x 1 1 && x 1 14).toNat = 1 := by
    have r1885 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1886 := hb (x 0 2)
    have b1887 := hb (x 2 13)
    have b1888 := hb (x 1 1 && x 1 14)
    clear * - r1885 b1886 b1887 b1888 g4 d1880
    omega
  have d1889 : (x 1 1).toNat = 1 := by
    have r1890 := hand1 (x 1 1) (x 1 14)
    have b1891 := hb (x 1 1)
    have b1892 := hb (x 1 1 && x 1 14)
    clear * - r1890 b1891 b1892 d1884
    omega
  have d1893 : (x 2 14).toNat = 0 := by
    have r1894 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1895 := hb (x 1 1)
    have b1896 := hb (x 2 14)
    clear * - r1894 b1895 b1896 d1889
    omega
  have d1897 : (x 2 1 && x 2 14).toNat = 0 := by
    have r1898 := hand2 (x 2 1) (x 2 14)
    have b1899 := hb (x 2 14)
    have b1900 := hb (x 2 1 && x 2 14)
    clear * - r1898 b1899 b1900 d1893
    omega
  have d1901 : (x 3 13).toNat = 1 := by
    have r1902 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1903 := hb (x 1 2)
    have b1904 := hb (x 3 13)
    have b1905 := hb (x 2 1 && x 2 14)
    clear * - r1902 b1903 b1904 b1905 d1897 g3
    omega
  have d1906 : (x 3 1).toNat = 1 := by
    have r1907 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b1908 := hb (x 3 1)
    have b1909 := hb (x 3 13)
    clear * - r1907 b1908 b1909 d1901
    omega
  have d1910 : (x 4 14).toNat = 0 := by
    have r1911 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1912 := hb (x 3 1)
    have b1913 := hb (x 4 14)
    clear * - r1911 b1912 b1913 d1906
    omega
  have d1914 : (x 4 3 && x 4 14).toNat = 0 := by
    have r1915 := hand2 (x 4 3) (x 4 14)
    have b1916 := hb (x 4 14)
    have b1917 := hb (x 4 3 && x 4 14)
    clear * - r1915 b1916 b1917 d1910
    omega
  have d1918 : (x 4 2).toNat = 0 := by
    have r1919 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b1920 := hb (x 4 2)
    have b1921 := hb (x 4 14)
    clear * - r1919 b1920 b1921 d1910
    omega
  have d1922 : (x 2 2).toNat = 0 := by
    have r1923 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b1924 := hb (x 2 2)
    have b1925 := hb (x 2 14)
    clear * - r1923 b1924 b1925 d1893
    omega
  have d1926 : (x 4 12).toNat = 0 := by
    have r1927 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1928 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e1929 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b1930 := hb (x 1 3)
    have b1931 := hb (x 2 2)
    have b1932 := hb (x 3 13)
    have b1933 := hb (x 4 12)
    clear * - r1927 e1928 e1929 b1930 b1931 b1932 b1933 d1901 d1922
    omega
  have d1934 : (x 4 4).toNat = 0 := by
    have r1935 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b1936 := hb (x 4 4)
    have b1937 := hb (x 4 12)
    clear * - r1935 b1936 b1937 d1926
    omega
  have d1938 : (x 1 3).toNat = 0 := by
    have r1939 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1940 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e1941 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b1942 := hb (x 1 3)
    have b1943 := hb (x 2 2)
    have b1944 := hb (x 3 13)
    have b1945 := hb (x 4 12)
    clear * - r1939 e1940 e1941 b1942 b1943 b1944 b1945 d1926 d1901 d1922
    omega
  have d1946 : (x 1 3 && x 1 14).toNat = 0 := by
    have r1947 := hand1 (x 1 3) (x 1 14)
    have b1948 := hb (x 1 3)
    have b1949 := hb (x 1 3 && x 1 14)
    clear * - r1947 b1948 b1949 d1938
    omega
  have d1950 : (x 4 11).toNat = 1 := by
    have r1951 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1952 := hb (x 0 4)
    have b1953 := hb (x 4 11)
    have b1954 := hb (x 3 1 && x 3 12)
    have b1955 := hb (x 2 2 && x 2 13)
    have b1956 := hb (x 1 3 && x 1 14)
    clear * - r1951 b1952 b1953 b1954 b1955 b1956 g6 g7 d1946 g2
    omega
  have d1957 : (x 4 3).toNat = 1 := by
    have r1958 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b1959 := hb (x 4 3)
    have b1960 := hb (x 4 11)
    clear * - r1958 b1959 b1960 d1950
    omega
  have d1961 : (x 7 12).toNat = 0 := by
    have r1962 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1963 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e1964 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b1965 := hb (x 4 3)
    have b1966 := hb (x 5 2)
    have b1967 := hb (x 6 13)
    have b1968 := hb (x 7 12)
    clear * - r1962 e1963 e1964 b1965 b1966 b1967 b1968 d1957
    omega
  have d1969 : (x 7 1 && x 7 12).toNat = 0 := by
    have r1970 := hand2 (x 7 1) (x 7 12)
    have b1971 := hb (x 7 12)
    have b1972 := hb (x 7 1 && x 7 12)
    clear * - r1970 b1971 b1972 d1961
    omega
  have d1973 : (x 7 4).toNat = 0 := by
    have r1974 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b1975 := hb (x 7 4)
    have b1976 := hb (x 7 12)
    clear * - r1974 b1975 b1976 d1961
    omega
  have d1977 : (x 6 13).toNat = 0 := by
    have r1978 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1979 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e1980 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b1981 := hb (x 4 3)
    have b1982 := hb (x 5 2)
    have b1983 := hb (x 6 13)
    have b1984 := hb (x 7 12)
    clear * - r1978 e1979 e1980 b1981 b1982 b1983 b1984 d1961 d1957
    omega
  have d1985 : (x 6 2 && x 6 13).toNat = 0 := by
    have r1986 := hand2 (x 6 2) (x 6 13)
    have b1987 := hb (x 6 13)
    have b1988 := hb (x 6 2 && x 6 13)
    clear * - r1986 b1987 b1988 d1977
    omega
  have d1989 : (x 5 1 && x 5 14).toNat = 1 := by
    have r1990 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1991 := hb (x 4 2)
    have b1992 := hb (x 6 13)
    have b1993 := hb (x 5 1 && x 5 14)
    clear * - r1990 b1991 b1992 b1993 d1977 d1918
    omega
  have d1994 : (x 5 1).toNat = 1 := by
    have r1995 := hand1 (x 5 1) (x 5 14)
    have b1996 := hb (x 5 1)
    have b1997 := hb (x 5 1 && x 5 14)
    clear * - r1995 b1996 b1997 d1989
    omega
  have d1998 : (x 6 14).toNat = 0 := by
    have r1999 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2000 := hb (x 5 1)
    have b2001 := hb (x 6 14)
    clear * - r1999 b2000 b2001 d1994
    omega
  have d2002 : (x 6 1 && x 6 14).toNat = 0 := by
    have r2003 := hand2 (x 6 1) (x 6 14)
    have b2004 := hb (x 6 14)
    have b2005 := hb (x 6 1 && x 6 14)
    clear * - r2003 b2004 b2005 d1998
    omega
  have d2006 : (x 6 2).toNat = 0 := by
    have r2007 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b2008 := hb (x 6 2)
    have b2009 := hb (x 6 14)
    clear * - r2007 b2008 b2009 d1998
    omega
  have d2010 : (x 5 2).toNat = 0 := by
    have r2011 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2012 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e2013 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b2014 := hb (x 4 3)
    have b2015 := hb (x 5 2)
    have b2016 := hb (x 6 13)
    have b2017 := hb (x 7 12)
    clear * - r2011 e2012 e2013 b2014 b2015 b2016 b2017 d1961 d1977 d1957
    omega
  have d2018 : (x 5 2 && x 5 13).toNat = 0 := by
    have r2019 := hand1 (x 5 2) (x 5 13)
    have b2020 := hb (x 5 2)
    have b2021 := hb (x 5 2 && x 5 13)
    clear * - r2019 b2020 b2021 d2010
    omega
  have d2022 : (x 7 13).toNat = 1 := by
    have r2023 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2024 := hb (x 5 2)
    have b2025 := hb (x 7 13)
    have b2026 := hb (x 6 1 && x 6 14)
    clear * - r2023 b2024 b2025 b2026 d2002 d2010
    omega
  have d2027 : (x 7 1).toNat = 1 := by
    have r2028 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b2029 := hb (x 7 1)
    have b2030 := hb (x 7 13)
    clear * - r2028 b2029 b2030 d2022
    omega
  have d2031 : (x 8 14).toNat = 0 := by
    have r2032 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2033 := hb (x 7 1)
    have b2034 := hb (x 8 14)
    clear * - r2032 b2033 b2034 d2027
    omega
  have d2035 : (x 8 3 && x 8 14).toNat = 0 := by
    have r2036 := hand2 (x 8 3) (x 8 14)
    have b2037 := hb (x 8 14)
    have b2038 := hb (x 8 3 && x 8 14)
    clear * - r2036 b2037 b2038 d2031
    omega
  have d2039 : (x 8 2).toNat = 0 := by
    have r2040 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b2041 := hb (x 8 2)
    have b2042 := hb (x 8 14)
    clear * - r2040 b2041 b2042 d2031
    omega
  have d2043 : (x 8 12).toNat = 0 := by
    have r2044 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2045 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e2046 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b2047 := hb (x 5 3)
    have b2048 := hb (x 6 2)
    have b2049 := hb (x 7 13)
    have b2050 := hb (x 8 12)
    clear * - r2044 e2045 e2046 b2047 b2048 b2049 b2050 d2022 d2006
    omega
  have d2051 : (x 8 4).toNat = 0 := by
    have r2052 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b2053 := hb (x 8 4)
    have b2054 := hb (x 8 12)
    clear * - r2052 b2053 b2054 d2043
    omega
  have d2055 : (x 5 3).toNat = 0 := by
    have r2056 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2057 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e2058 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b2059 := hb (x 5 3)
    have b2060 := hb (x 6 2)
    have b2061 := hb (x 7 13)
    have b2062 := hb (x 8 12)
    clear * - r2056 e2057 e2058 b2059 b2060 b2061 b2062 d2043 d2022 d2006
    omega
  have d2063 : (x 5 3 && x 5 14).toNat = 0 := by
    have r2064 := hand1 (x 5 3) (x 5 14)
    have b2065 := hb (x 5 3)
    have b2066 := hb (x 5 3 && x 5 14)
    clear * - r2064 b2065 b2066 d2055
    omega
  have d2067 : (x 8 11).toNat = 1 := by
    have r2068 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2069 := hb (x 4 4)
    have b2070 := hb (x 8 11)
    have b2071 := hb (x 7 1 && x 7 12)
    have b2072 := hb (x 6 2 && x 6 13)
    have b2073 := hb (x 5 3 && x 5 14)
    clear * - r2068 b2069 b2070 b2071 b2072 b2073 d1969 d1985 d2063 d1934
    omega
  have d2074 : (x 8 3).toNat = 1 := by
    have r2075 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b2076 := hb (x 8 3)
    have b2077 := hb (x 8 11)
    clear * - r2075 b2076 b2077 d2067
    omega
  have d2078 : (x 11 12).toNat = 0 := by
    have r2079 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2080 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e2081 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b2082 := hb (x 8 3)
    have b2083 := hb (x 9 2)
    have b2084 := hb (x 10 13)
    have b2085 := hb (x 11 12)
    clear * - r2079 e2080 e2081 b2082 b2083 b2084 b2085 d2074
    omega
  have d2086 : (x 11 1 && x 11 12).toNat = 0 := by
    have r2087 := hand2 (x 11 1) (x 11 12)
    have b2088 := hb (x 11 12)
    have b2089 := hb (x 11 1 && x 11 12)
    clear * - r2087 b2088 b2089 d2078
    omega
  have d2090 : (x 11 4).toNat = 0 := by
    have r2091 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b2092 := hb (x 11 4)
    have b2093 := hb (x 11 12)
    clear * - r2091 b2092 b2093 d2078
    omega
  have d2094 : (x 10 13).toNat = 0 := by
    have r2095 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2096 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e2097 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b2098 := hb (x 8 3)
    have b2099 := hb (x 9 2)
    have b2100 := hb (x 10 13)
    have b2101 := hb (x 11 12)
    clear * - r2095 e2096 e2097 b2098 b2099 b2100 b2101 d2078 d2074
    omega
  have d2102 : (x 10 2 && x 10 13).toNat = 0 := by
    have r2103 := hand2 (x 10 2) (x 10 13)
    have b2104 := hb (x 10 13)
    have b2105 := hb (x 10 2 && x 10 13)
    clear * - r2103 b2104 b2105 d2094
    omega
  have d2106 : (x 9 1 && x 9 14).toNat = 1 := by
    have r2107 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2108 := hb (x 8 2)
    have b2109 := hb (x 10 13)
    have b2110 := hb (x 9 1 && x 9 14)
    clear * - r2107 b2108 b2109 b2110 d2094 d2039
    omega
  have d2111 : (x 9 14).toNat = 1 := by
    have r2112 := hand2 (x 9 1) (x 9 14)
    have b2113 := hb (x 9 14)
    have b2114 := hb (x 9 1 && x 9 14)
    clear * - r2112 b2113 b2114 d2106
    omega
  have d2115 : (x 8 1).toNat = 0 := by
    have r2116 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2117 := hb (x 8 1)
    have b2118 := hb (x 9 14)
    clear * - r2116 b2117 b2118 d2111
    omega
  have d2119 : (x 8 13).toNat = 0 := by
    have r2120 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b2121 := hb (x 8 1)
    have b2122 := hb (x 8 13)
    clear * - r2120 b2121 b2122 d2115
    omega
  have d2123 : (x 7 1 && x 7 14).toNat = 1 := by
    have r2124 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2125 := hb (x 6 2)
    have b2126 := hb (x 8 13)
    have b2127 := hb (x 7 1 && x 7 14)
    clear * - r2124 b2125 b2126 b2127 d2119 d2006
    omega
  have d2128 : (x 7 14).toNat = 1 := by
    have r2129 := hand2 (x 7 1) (x 7 14)
    have b2130 := hb (x 7 14)
    have b2131 := hb (x 7 1 && x 7 14)
    clear * - r2129 b2130 b2131 d2123
    omega
  have d2132 : (x 6 1).toNat = 0 := by
    have r2133 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2134 := hb (x 6 1)
    have b2135 := hb (x 7 14)
    clear * - r2133 b2134 b2135 d2128
    omega
  have d2136 : (x 6 1 && x 6 12).toNat = 0 := by
    have r2137 := hand1 (x 6 1) (x 6 12)
    have b2138 := hb (x 6 1)
    have b2139 := hb (x 6 1 && x 6 12)
    clear * - r2137 b2138 b2139 d2132
    omega
  have d2140 : (x 7 11).toNat = 1 := by
    have r2141 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2142 := hb (x 3 4)
    have b2143 := hb (x 7 11)
    have b2144 := hb (x 6 1 && x 6 12)
    have b2145 := hb (x 5 2 && x 5 13)
    have b2146 := hb (x 4 3 && x 4 14)
    clear * - r2141 b2142 b2143 b2144 b2145 b2146 d2136 d2018 d1914 g5
    omega
  have d2147 : (x 7 3).toNat = 1 := by
    have r2148 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b2149 := hb (x 7 3)
    have b2150 := hb (x 7 11)
    clear * - r2148 b2149 b2150 d2140
    omega
  have d2151 : (x 10 12).toNat = 0 := by
    have r2152 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2153 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e2154 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b2155 := hb (x 7 3)
    have b2156 := hb (x 8 2)
    have b2157 := hb (x 9 13)
    have b2158 := hb (x 10 12)
    clear * - r2152 e2153 e2154 b2155 b2156 b2157 b2158 d2039 d2147
    omega
  have d2159 : (x 10 1 && x 10 12).toNat = 0 := by
    have r2160 := hand2 (x 10 1) (x 10 12)
    have b2161 := hb (x 10 12)
    have b2162 := hb (x 10 1 && x 10 12)
    clear * - r2160 b2161 b2162 d2151
    omega
  have d2163 : (x 9 13).toNat = 0 := by
    have r2164 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2165 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e2166 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b2167 := hb (x 7 3)
    have b2168 := hb (x 8 2)
    have b2169 := hb (x 9 13)
    have b2170 := hb (x 10 12)
    clear * - r2164 e2165 e2166 b2167 b2168 b2169 b2170 d2151 d2039 d2147
    omega
  have d2171 : (x 9 2 && x 9 13).toNat = 0 := by
    have r2172 := hand2 (x 9 2) (x 9 13)
    have b2173 := hb (x 9 13)
    have b2174 := hb (x 9 2 && x 9 13)
    clear * - r2172 b2173 b2174 d2163
    omega
  have d2175 : (x 11 11).toNat = 1 := by
    have r2176 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2177 := hb (x 7 4)
    have b2178 := hb (x 11 11)
    have b2179 := hb (x 10 1 && x 10 12)
    have b2180 := hb (x 9 2 && x 9 13)
    have b2181 := hb (x 8 3 && x 8 14)
    clear * - r2176 b2177 b2178 b2179 b2180 b2181 d2159 d2171 d2035 d1973
    omega
  have d2182 : (x 11 3).toNat = 1 := by
    have r2183 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b2184 := hb (x 11 3)
    have b2185 := hb (x 11 11)
    clear * - r2183 b2184 b2185 d2175
    omega
  have d2186 : (x 14 12).toNat = 0 := by
    have r2187 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2188 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e2189 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b2190 := hb (x 11 3)
    have b2191 := hb (x 12 2)
    have b2192 := hb (x 13 13)
    have b2193 := hb (x 14 12)
    clear * - r2187 e2188 e2189 b2190 b2191 b2192 b2193 d2182
    omega
  have d2194 : (x 14 1 && x 14 12).toNat = 0 := by
    have r2195 := hand2 (x 14 1) (x 14 12)
    have b2196 := hb (x 14 12)
    have b2197 := hb (x 14 1 && x 14 12)
    clear * - r2195 b2196 b2197 d2186
    omega
  have d2198 : (x 13 13).toNat = 0 := by
    have r2199 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2200 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e2201 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b2202 := hb (x 11 3)
    have b2203 := hb (x 12 2)
    have b2204 := hb (x 13 13)
    have b2205 := hb (x 14 12)
    clear * - r2199 e2200 e2201 b2202 b2203 b2204 b2205 d2186 d2182
    omega
  have d2206 : (x 13 2 && x 13 13).toNat = 0 := by
    have r2207 := hand2 (x 13 2) (x 13 13)
    have b2208 := hb (x 13 13)
    have b2209 := hb (x 13 2 && x 13 13)
    clear * - r2207 b2208 b2209 d2198
    omega
  have d2210 : (x 12 2).toNat = 0 := by
    have r2211 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2212 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e2213 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b2214 := hb (x 11 3)
    have b2215 := hb (x 12 2)
    have b2216 := hb (x 13 13)
    have b2217 := hb (x 14 12)
    clear * - r2211 e2212 e2213 b2214 b2215 b2216 b2217 d2186 d2198 d2182
    omega
  have d2218 : (x 9 1).toNat = 1 := by
    have r2219 := hand1 (x 9 1) (x 9 14)
    have b2220 := hb (x 9 1)
    have b2221 := hb (x 9 1 && x 9 14)
    clear * - r2219 b2220 b2221 d2106
    omega
  have d2222 : (x 10 14).toNat = 0 := by
    have r2223 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2224 := hb (x 9 1)
    have b2225 := hb (x 10 14)
    clear * - r2223 b2224 b2225 d2218
    omega
  have d2226 : (x 10 1 && x 10 14).toNat = 0 := by
    have r2227 := hand2 (x 10 1) (x 10 14)
    have b2228 := hb (x 10 14)
    have b2229 := hb (x 10 1 && x 10 14)
    clear * - r2227 b2228 b2229 d2222
    omega
  have d2230 : (x 10 2).toNat = 0 := by
    have r2231 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
    have b2232 := hb (x 10 2)
    have b2233 := hb (x 10 14)
    clear * - r2231 b2232 b2233 d2222
    omega
  have d2234 : (x 9 2).toNat = 0 := by
    have r2235 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2236 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e2237 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b2238 := hb (x 8 3)
    have b2239 := hb (x 9 2)
    have b2240 := hb (x 10 13)
    have b2241 := hb (x 11 12)
    clear * - r2235 e2236 e2237 b2238 b2239 b2240 b2241 d2078 d2094 d2074
    omega
  have d2242 : (x 11 13).toNat = 1 := by
    have r2243 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2244 := hb (x 9 2)
    have b2245 := hb (x 11 13)
    have b2246 := hb (x 10 1 && x 10 14)
    clear * - r2243 b2244 b2245 b2246 d2226 d2234
    omega
  have d2247 : (x 11 1).toNat = 1 := by
    have r2248 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b2249 := hb (x 11 1)
    have b2250 := hb (x 11 13)
    clear * - r2248 b2249 b2250 d2242
    omega
  have d2251 : (x 12 14).toNat = 0 := by
    have r2252 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2253 := hb (x 11 1)
    have b2254 := hb (x 12 14)
    clear * - r2252 b2253 b2254 d2247
    omega
  have d2255 : (x 12 1 && x 12 14).toNat = 0 := by
    have r2256 := hand2 (x 12 1) (x 12 14)
    have b2257 := hb (x 12 14)
    have b2258 := hb (x 12 1 && x 12 14)
    clear * - r2256 b2257 b2258 d2251
    omega
  have d2259 : (x 11 2).toNat = 1 := by
    have r2260 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2261 := hb (x 11 2)
    have b2262 := hb (x 13 13)
    have b2263 := hb (x 12 1 && x 12 14)
    clear * - r2260 b2261 b2262 b2263 d2198 d2255
    omega
  have d2264 : (x 13 12).toNat = 0 := by
    have r2265 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2266 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e2267 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b2268 := hb (x 10 3)
    have b2269 := hb (x 11 2)
    have b2270 := hb (x 12 13)
    have b2271 := hb (x 13 12)
    clear * - r2265 e2266 e2267 b2268 b2269 b2270 b2271 d2259
    omega
  have d2272 : (x 13 4).toNat = 0 := by
    have r2273 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b2274 := hb (x 13 4)
    have b2275 := hb (x 13 12)
    clear * - r2273 b2274 b2275 d2264
    omega
  have d2276 : (x 13 4 && x 13 14).toNat = 0 := by
    have r2277 := hand1 (x 13 4) (x 13 14)
    have b2278 := hb (x 13 4)
    have b2279 := hb (x 13 4 && x 13 14)
    clear * - r2277 b2278 b2279 d2272
    omega
  have d2280 : (x 12 13).toNat = 0 := by
    have r2281 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2282 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e2283 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b2284 := hb (x 10 3)
    have b2285 := hb (x 11 2)
    have b2286 := hb (x 12 13)
    have b2287 := hb (x 13 12)
    clear * - r2281 e2282 e2283 b2284 b2285 b2286 b2287 d2264 d2259
    omega
  have d2288 : (x 12 5).toNat = 0 := by
    have r2289 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
    have b2290 := hb (x 12 5)
    have b2291 := hb (x 12 13)
    clear * - r2289 b2290 b2291 d2280
    omega
  have d2292 : (x 12 3 && x 12 14).toNat = 0 := by
    have r2293 := hand2 (x 12 3) (x 12 14)
    have b2294 := hb (x 12 14)
    have b2295 := hb (x 12 3 && x 12 14)
    clear * - r2293 b2294 b2295 d2251
    omega
  have d2296 : (x 15 11).toNat = 1 := by
    have r2297 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2298 := hb (x 11 4)
    have b2299 := hb (x 15 11)
    have b2300 := hb (x 14 1 && x 14 12)
    have b2301 := hb (x 13 2 && x 13 13)
    have b2302 := hb (x 12 3 && x 12 14)
    clear * - r2297 b2298 b2299 b2300 b2301 b2302 d2194 d2206 d2292 d2090
    omega
  have d2303 : (x 15 3).toNat = 1 := by
    have r2304 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
    have b2305 := hb (x 15 3)
    have b2306 := hb (x 15 11)
    clear * - r2304 b2305 b2306 d2296
    omega
  have d2307 : (x 18 12).toNat = 0 := by
    have r2308 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2309 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e2310 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b2311 := hb (x 15 3)
    have b2312 := hb (x 16 2)
    have b2313 := hb (x 17 13)
    have b2314 := hb (x 18 12)
    clear * - r2308 e2309 e2310 b2311 b2312 b2313 b2314 d2303
    omega
  have d2315 : (x 17 13).toNat = 0 := by
    have r2316 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2317 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e2318 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b2319 := hb (x 15 3)
    have b2320 := hb (x 16 2)
    have b2321 := hb (x 17 13)
    have b2322 := hb (x 18 12)
    clear * - r2316 e2317 e2318 b2319 b2320 b2321 b2322 d2307 d2303
    omega
  have d2323 : (x 16 2).toNat = 0 := by
    have r2324 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2325 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e2326 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b2327 := hb (x 15 3)
    have b2328 := hb (x 16 2)
    have b2329 := hb (x 17 13)
    have b2330 := hb (x 18 12)
    clear * - r2324 e2325 e2326 b2327 b2328 b2329 b2330 d2307 d2315 d2303
    omega
  have d2331 : (x 12 12).toNat = 0 := by
    have r2332 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2333 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e2334 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b2335 := hb (x 9 3)
    have b2336 := hb (x 10 2)
    have b2337 := hb (x 11 13)
    have b2338 := hb (x 12 12)
    clear * - r2332 e2333 e2334 b2335 b2336 b2337 b2338 d2242 d2230
    omega
  have d2339 : (x 12 4).toNat = 0 := by
    have r2340 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b2341 := hb (x 12 4)
    have b2342 := hb (x 12 12)
    clear * - r2340 b2341 b2342 d2331
    omega
  have d2343 : (x 9 3).toNat = 0 := by
    have r2344 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2345 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e2346 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b2347 := hb (x 9 3)
    have b2348 := hb (x 10 2)
    have b2349 := hb (x 11 13)
    have b2350 := hb (x 12 12)
    clear * - r2344 e2345 e2346 b2347 b2348 b2349 b2350 d2331 d2242 d2230
    omega
  have d2351 : (x 9 3 && x 9 14).toNat = 0 := by
    have r2352 := hand1 (x 9 3) (x 9 14)
    have b2353 := hb (x 9 3)
    have b2354 := hb (x 9 3 && x 9 14)
    clear * - r2352 b2353 b2354 d2343
    omega
  have d2355 : (x 12 11).toNat = 1 := by
    have r2356 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2357 := hb (x 8 4)
    have b2358 := hb (x 12 11)
    have b2359 := hb (x 11 1 && x 11 12)
    have b2360 := hb (x 10 2 && x 10 13)
    have b2361 := hb (x 9 3 && x 9 14)
    clear * - r2356 b2357 b2358 b2359 b2360 b2361 d2086 d2102 d2351 d2051
    omega
  have d2362 : (x 12 3).toNat = 1 := by
    have r2363 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b2364 := hb (x 12 3)
    have b2365 := hb (x 12 11)
    clear * - r2363 b2364 b2365 d2355
    omega
  have d2366 : (x 15 12).toNat = 0 := by
    have r2367 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2368 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e2369 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b2370 := hb (x 12 3)
    have b2371 := hb (x 13 2)
    have b2372 := hb (x 14 13)
    have b2373 := hb (x 15 12)
    clear * - r2367 e2368 e2369 b2370 b2371 b2372 b2373 d2362
    omega
  have d2374 : (x 15 1 && x 15 12).toNat = 0 := by
    have r2375 := hand2 (x 15 1) (x 15 12)
    have b2376 := hb (x 15 12)
    have b2377 := hb (x 15 1 && x 15 12)
    clear * - r2375 b2376 b2377 d2366
    omega
  have d2378 : (x 15 2 && x 15 12).toNat = 0 := by
    have r2379 := hand2 (x 15 2) (x 15 12)
    have b2380 := hb (x 15 12)
    have b2381 := hb (x 15 2 && x 15 12)
    clear * - r2379 b2380 b2381 d2366
    omega
  have d2382 : (x 14 13).toNat = 0 := by
    have r2383 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2384 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e2385 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b2386 := hb (x 12 3)
    have b2387 := hb (x 13 2)
    have b2388 := hb (x 14 13)
    have b2389 := hb (x 15 12)
    clear * - r2383 e2384 e2385 b2386 b2387 b2388 b2389 d2366 d2362
    omega
  have d2390 : (x 14 2 && x 14 13).toNat = 0 := by
    have r2391 := hand2 (x 14 2) (x 14 13)
    have b2392 := hb (x 14 13)
    have b2393 := hb (x 14 2 && x 14 13)
    clear * - r2391 b2392 b2393 d2382
    omega
  have d2394 : (x 14 3 && x 14 13).toNat = 0 := by
    have r2395 := hand2 (x 14 3) (x 14 13)
    have b2396 := hb (x 14 13)
    have b2397 := hb (x 14 3 && x 14 13)
    clear * - r2395 b2396 b2397 d2382
    omega
  have d2398 : (x 13 1 && x 13 14).toNat = 1 := by
    have r2399 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2400 := hb (x 12 2)
    have b2401 := hb (x 14 13)
    have b2402 := hb (x 13 1 && x 13 14)
    clear * - r2399 b2400 b2401 b2402 d2382 d2210
    omega
  have d2403 : (x 13 1).toNat = 1 := by
    have r2404 := hand1 (x 13 1) (x 13 14)
    have b2405 := hb (x 13 1)
    have b2406 := hb (x 13 1 && x 13 14)
    clear * - r2404 b2405 b2406 d2398
    omega
  have d2407 : (x 14 14).toNat = 0 := by
    have r2408 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2409 := hb (x 13 1)
    have b2410 := hb (x 14 14)
    clear * - r2408 b2409 b2410 d2403
    omega
  have d2411 : (x 14 1 && x 14 14).toNat = 0 := by
    have r2412 := hand2 (x 14 1) (x 14 14)
    have b2413 := hb (x 14 14)
    have b2414 := hb (x 14 1 && x 14 14)
    clear * - r2412 b2413 b2414 d2407
    omega
  have d2415 : (x 14 2).toNat = 0 := by
    have r2416 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
    have b2417 := hb (x 14 2)
    have b2418 := hb (x 14 14)
    clear * - r2416 b2417 b2418 d2407
    omega
  have d2419 : (x 13 2).toNat = 0 := by
    have r2420 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2421 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e2422 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b2423 := hb (x 12 3)
    have b2424 := hb (x 13 2)
    have b2425 := hb (x 14 13)
    have b2426 := hb (x 15 12)
    clear * - r2420 e2421 e2422 b2423 b2424 b2425 b2426 d2366 d2382 d2362
    omega
  have d2427 : (x 15 13).toNat = 1 := by
    have r2428 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2429 := hb (x 13 2)
    have b2430 := hb (x 15 13)
    have b2431 := hb (x 14 1 && x 14 14)
    clear * - r2428 b2429 b2430 b2431 d2411 d2419
    omega
  have d2432 : (x 16 12).toNat = 0 := by
    have r2433 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2434 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e2435 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b2436 := hb (x 13 3)
    have b2437 := hb (x 14 2)
    have b2438 := hb (x 15 13)
    have b2439 := hb (x 16 12)
    clear * - r2433 e2434 e2435 b2436 b2437 b2438 b2439 d2427 d2415
    omega
  have d2440 : (x 13 3).toNat = 0 := by
    have r2441 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2442 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e2443 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b2444 := hb (x 13 3)
    have b2445 := hb (x 14 2)
    have b2446 := hb (x 15 13)
    have b2447 := hb (x 16 12)
    clear * - r2441 e2442 e2443 b2444 b2445 b2446 b2447 d2432 d2427 d2415
    omega
  have d2448 : (x 13 3 && x 13 14).toNat = 0 := by
    have r2449 := hand1 (x 13 3) (x 13 14)
    have b2450 := hb (x 13 3)
    have b2451 := hb (x 13 3 && x 13 14)
    clear * - r2449 b2450 b2451 d2440
    omega
  have d2452 : (x 16 11).toNat = 1 := by
    have r2453 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2454 := hb (x 12 4)
    have b2455 := hb (x 16 11)
    have b2456 := hb (x 15 1 && x 15 12)
    have b2457 := hb (x 14 2 && x 14 13)
    have b2458 := hb (x 13 3 && x 13 14)
    clear * - r2453 b2454 b2455 b2456 b2457 b2458 d2374 d2390 d2448 d2339
    omega
  have d2459 : (x 16 3).toNat = 1 := by
    have r2460 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
    have b2461 := hb (x 16 3)
    have b2462 := hb (x 16 11)
    clear * - r2460 b2461 b2462 d2452
    omega
  have d2463 : (x 19 12).toNat = 0 := by
    have r2464 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2465 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e2466 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b2467 := hb (x 16 3)
    have b2468 := hb (x 17 2)
    have b2469 := hb (x 18 13)
    have b2470 := hb (x 19 12)
    clear * - r2464 e2465 e2466 b2467 b2468 b2469 b2470 d2459
    omega
  have d2471 : (x 18 13).toNat = 0 := by
    have r2472 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2473 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e2474 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b2475 := hb (x 16 3)
    have b2476 := hb (x 17 2)
    have b2477 := hb (x 18 13)
    have b2478 := hb (x 19 12)
    clear * - r2472 e2473 e2474 b2475 b2476 b2477 b2478 d2463 d2459
    omega
  have d2479 : (x 17 1 && x 17 14).toNat = 1 := by
    have r2480 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2481 := hb (x 16 2)
    have b2482 := hb (x 18 13)
    have b2483 := hb (x 17 1 && x 17 14)
    clear * - r2480 b2481 b2482 b2483 d2471 d2323
    omega
  have d2484 : (x 17 14).toNat = 1 := by
    have r2485 := hand2 (x 17 1) (x 17 14)
    have b2486 := hb (x 17 14)
    have b2487 := hb (x 17 1 && x 17 14)
    clear * - r2485 b2486 b2487 d2479
    omega
  have d2488 : (x 16 1).toNat = 0 := by
    have r2489 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b2490 := hb (x 16 1)
    have b2491 := hb (x 17 14)
    clear * - r2489 b2490 b2491 d2484
    omega
  have d2492 : (x 16 1 && x 16 11).toNat = 0 := by
    have r2493 := hand1 (x 16 1) (x 16 11)
    have b2494 := hb (x 16 1)
    have b2495 := hb (x 16 1 && x 16 11)
    clear * - r2493 b2494 b2495 d2488
    omega
  have d2496 : (x 17 2).toNat = 0 := by
    have r2497 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e2498 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e2499 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b2500 := hb (x 16 3)
    have b2501 := hb (x 17 2)
    have b2502 := hb (x 18 13)
    have b2503 := hb (x 19 12)
    clear * - r2497 e2498 e2499 b2500 b2501 b2502 b2503 d2463 d2471 d2459
    omega
  have d2504 : (x 17 10).toNat = 0 := by
    have r2505 : (x 17 10).toNat ≤ (x 17 2).toNat := himp _ _ (hp10 17)
    have b2506 := hb (x 17 2)
    have b2507 := hb (x 17 10)
    clear * - r2505 b2506 b2507 d2496
    omega
  have r2508 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := by have q := hcov10 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b2509 := hb (x 12 5)
  have b2510 := hb (x 17 10)
  have b2511 := hb (x 16 1 && x 16 11)
  have b2512 := hb (x 15 2 && x 15 12)
  have b2513 := hb (x 14 3 && x 14 13)
  have b2514 := hb (x 13 4 && x 13 14)
  linarith only [r2508, b2509, b2510, b2511, b2512, b2513, b2514, d2504, d2492, d2378, d2394, d2276, d2288]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0010 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 2).toNat = 0)
    (g1 : (x 0 1).toNat = 0)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 2 13).toNat = 0)
    (g5 : (x 3 4).toNat = 0)
    (g6 : (x 3 1 && x 3 12).toNat = 0)
    (g7 : (x 2 2 && x 2 13).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b0010_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7
