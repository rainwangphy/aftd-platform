import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b100

Topic: combinatorics   Node: 34fee8debc08

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 64 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b100_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 6).toNat = 0)
    (g1 : (x (-4) 5).toNat = 0)
    (g2 : (x (-3) 4).toNat = 0)
    (g3 : (x (-2) 11).toNat = 0)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 10).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x (-1) 13).toNat = 0)
    (g9 : (x 0 3).toNat = 1)
    (g10 : (x 0 4).toNat = 0)
    (g11 : (x 0 5).toNat = 0)
    (g12 : (x 0 9).toNat = 1)
    (g13 : (x 1 2).toNat = 0)
    (g14 : (x 1 5).toNat = 0)
    (g15 : (x 1 6).toNat = 0)
    (g16 : (x 1 8).toNat = 0)
    (g17 : (x 1 10).toNat = 0)
    (g18 : (x 2 4).toNat = 0)
    (g19 : (x 2 5).toNat = 0)
    (g20 : (x 3 4).toNat = 0)
    (g21 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g22 : (x 3 4 && x 3 8).toNat = 0)
    (g23 : (x 2 5 && x 2 9).toNat = 0)
    (g24 : (x 1 6 && x 1 10).toNat = 0)
    (g25 : (x (-5) 1 && x (-5) 6).toNat = 0)
    (g26 : (x (-6) 2 && x (-6) 7).toNat = 0)
    (g27 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g28 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g29 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g30 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g31 : (x 2 4 && x 2 9).toNat = 0)
    (g32 : (x 1 5 && x 1 10).toNat = 0)
    (g33 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g34 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g35 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g36 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g37 : (x 0 1 && x 0 8).toNat = 0)
    (g38 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g39 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g40 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g41 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g42 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g43 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g44 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g45 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g46 : (x 3 4 && x 3 13).toNat = 0)
    (g47 : (x 2 5 && x 2 14).toNat = 0)
    (g48 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g49 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g50 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g51 : (x 1 2 && x 1 12).toNat = 0)
    (g52 : (x 2 2 && x 2 12).toNat = 0)
    (g53 : (x 1 3 && x 1 13).toNat = 0)
    (g54 : (x 3 2 && x 3 12).toNat = 0)
    (g55 : (x 2 3 && x 2 13).toNat = 0)
    (g56 : (x 1 4 && x 1 14).toNat = 0)
    (g57 : (x 2 4 && x 2 14).toNat = 0)
    (g58 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g59 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g60 : (x 3 1 && x 3 12).toNat = 0)
    (g61 : (x 2 2 && x 2 13).toNat = 0)
    (g62 : (x 1 3 && x 1 14).toNat = 0)
    (g63 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d7501 : (x 0 4 && x 0 14).toNat = 0 := by
    have r7502 := hand1 (x 0 4) (x 0 14)
    have b7503 := hb (x 0 4)
    have b7504 := hb (x 0 4 && x 0 14)
    clear * - r7502 b7503 b7504 g10
    omega
  have d7505 : (x 4 11).toNat = 1 := by
    have r7506 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7507 := hb (x 0 4)
    have b7508 := hb (x 4 11)
    have b7509 := hb (x 3 1 && x 3 12)
    have b7510 := hb (x 2 2 && x 2 13)
    have b7511 := hb (x 1 3 && x 1 14)
    clear * - r7506 b7507 b7508 b7509 b7510 b7511 g60 g61 g62 g10
    omega
  have d7512 : (x 4 3).toNat = 1 := by
    have r7513 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b7514 := hb (x 4 3)
    have b7515 := hb (x 4 11)
    clear * - r7513 b7514 b7515 d7505
    omega
  have d7516 : (x 7 12).toNat = 0 := by
    have r7517 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7518 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e7519 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b7520 := hb (x 4 3)
    have b7521 := hb (x 5 2)
    have b7522 := hb (x 6 13)
    have b7523 := hb (x 7 12)
    clear * - r7517 e7518 e7519 b7520 b7521 b7522 b7523 d7512
    omega
  have d7524 : (x 7 1 && x 7 12).toNat = 0 := by
    have r7525 := hand2 (x 7 1) (x 7 12)
    have b7526 := hb (x 7 12)
    have b7527 := hb (x 7 1 && x 7 12)
    clear * - r7525 b7526 b7527 d7516
    omega
  have d7528 : (x 7 2 && x 7 12).toNat = 0 := by
    have r7529 := hand2 (x 7 2) (x 7 12)
    have b7530 := hb (x 7 12)
    have b7531 := hb (x 7 2 && x 7 12)
    clear * - r7529 b7530 b7531 d7516
    omega
  have d7532 : (x 7 3 && x 7 12).toNat = 0 := by
    have r7533 := hand2 (x 7 3) (x 7 12)
    have b7534 := hb (x 7 12)
    have b7535 := hb (x 7 3 && x 7 12)
    clear * - r7533 b7534 b7535 d7516
    omega
  have d7536 : (x 7 4).toNat = 0 := by
    have r7537 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b7538 := hb (x 7 4)
    have b7539 := hb (x 7 12)
    clear * - r7537 b7538 b7539 d7516
    omega
  have d7540 : (x 7 4 && x 7 14).toNat = 0 := by
    have r7541 := hand1 (x 7 4) (x 7 14)
    have b7542 := hb (x 7 4)
    have b7543 := hb (x 7 4 && x 7 14)
    clear * - r7541 b7542 b7543 d7536
    omega
  have d7544 : (x 7 4 && x 7 9).toNat = 0 := by
    have r7545 := hand1 (x 7 4) (x 7 9)
    have b7546 := hb (x 7 4)
    have b7547 := hb (x 7 4 && x 7 9)
    clear * - r7545 b7546 b7547 d7536
    omega
  have d7548 : (x 6 13).toNat = 0 := by
    have r7549 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7550 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e7551 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b7552 := hb (x 4 3)
    have b7553 := hb (x 5 2)
    have b7554 := hb (x 6 13)
    have b7555 := hb (x 7 12)
    clear * - r7549 e7550 e7551 b7552 b7553 b7554 b7555 d7516 d7512
    omega
  have d7556 : (x 6 2 && x 6 13).toNat = 0 := by
    have r7557 := hand2 (x 6 2) (x 6 13)
    have b7558 := hb (x 6 13)
    have b7559 := hb (x 6 2 && x 6 13)
    clear * - r7557 b7558 b7559 d7548
    omega
  have d7560 : (x 6 3 && x 6 13).toNat = 0 := by
    have r7561 := hand2 (x 6 3) (x 6 13)
    have b7562 := hb (x 6 13)
    have b7563 := hb (x 6 3 && x 6 13)
    clear * - r7561 b7562 b7563 d7548
    omega
  have d7564 : (x 6 4 && x 6 13).toNat = 0 := by
    have r7565 := hand2 (x 6 4) (x 6 13)
    have b7566 := hb (x 6 13)
    have b7567 := hb (x 6 4 && x 6 13)
    clear * - r7565 b7566 b7567 d7548
    omega
  have d7568 : (x 6 5).toNat = 0 := by
    have r7569 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
    have b7570 := hb (x 6 5)
    have b7571 := hb (x 6 13)
    clear * - r7569 b7570 b7571 d7548
    omega
  have d7572 : (x 6 5 && x 6 10).toNat = 0 := by
    have r7573 := hand1 (x 6 5) (x 6 10)
    have b7574 := hb (x 6 5)
    have b7575 := hb (x 6 5 && x 6 10)
    clear * - r7573 b7574 b7575 d7568
    omega
  have d7576 : (x 5 2).toNat = 0 := by
    have r7577 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7578 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e7579 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b7580 := hb (x 4 3)
    have b7581 := hb (x 5 2)
    have b7582 := hb (x 6 13)
    have b7583 := hb (x 7 12)
    clear * - r7577 e7578 e7579 b7580 b7581 b7582 b7583 d7516 d7548 d7512
    omega
  have d7584 : (x 5 2 && x 5 11).toNat = 0 := by
    have r7585 := hand1 (x 5 2) (x 5 11)
    have b7586 := hb (x 5 2)
    have b7587 := hb (x 5 2 && x 5 11)
    clear * - r7585 b7586 b7587 d7576
    omega
  have d7588 : (x 5 2 && x 5 6).toNat = 0 := by
    have r7589 := hand1 (x 5 2) (x 5 6)
    have b7590 := hb (x 5 2)
    have b7591 := hb (x 5 2 && x 5 6)
    clear * - r7589 b7590 b7591 d7576
    omega
  have d7592 : (x 5 10).toNat = 0 := by
    have r7593 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b7594 := hb (x 5 2)
    have b7595 := hb (x 5 10)
    clear * - r7593 b7594 b7595 d7576
    omega
  have d7596 : (x 4 1 && x 4 11).toNat = 1 := by
    have r7597 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7598 := hb (x 0 5)
    have b7599 := hb (x 5 10)
    have b7600 := hb (x 4 1 && x 4 11)
    have b7601 := hb (x 3 2 && x 3 12)
    have b7602 := hb (x 2 3 && x 2 13)
    have b7603 := hb (x 1 4 && x 1 14)
    clear * - r7597 b7598 b7599 b7600 b7601 b7602 b7603 d7592 g54 g55 g56 g11
    omega
  have d7604 : (x 4 1).toNat = 1 := by
    have r7605 := hand1 (x 4 1) (x 4 11)
    have b7606 := hb (x 4 1)
    have b7607 := hb (x 4 1 && x 4 11)
    clear * - r7605 b7606 b7607 d7596
    omega
  have d7608 : (x 5 14).toNat = 0 := by
    have r7609 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7610 := hb (x 4 1)
    have b7611 := hb (x 5 14)
    clear * - r7609 b7610 b7611 d7604
    omega
  have d7612 : (x 5 1 && x 5 14).toNat = 0 := by
    have r7613 := hand2 (x 5 1) (x 5 14)
    have b7614 := hb (x 5 14)
    have b7615 := hb (x 5 1 && x 5 14)
    clear * - r7613 b7614 b7615 d7608
    omega
  have d7616 : (x 4 2).toNat = 1 := by
    have r7617 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7618 := hb (x 4 2)
    have b7619 := hb (x 6 13)
    have b7620 := hb (x 5 1 && x 5 14)
    clear * - r7617 b7618 b7619 b7620 d7548 d7612
    omega
  have d7621 : (x 4 14).toNat = 1 := by
    have r7622 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b7623 := hb (x 4 2)
    have b7624 := hb (x 4 14)
    clear * - r7622 b7623 b7624 d7616
    omega
  have d7625 : (x 3 1).toNat = 0 := by
    have r7626 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7627 := hb (x 3 1)
    have b7628 := hb (x 4 14)
    clear * - r7626 b7627 b7628 d7621
    omega
  have d7629 : (x 3 1 && x 3 14).toNat = 0 := by
    have r7630 := hand1 (x 3 1) (x 3 14)
    have b7631 := hb (x 3 1)
    have b7632 := hb (x 3 1 && x 3 14)
    clear * - r7630 b7631 b7632 d7625
    omega
  have d7633 : (x 3 1 && x 3 11).toNat = 0 := by
    have r7634 := hand1 (x 3 1) (x 3 11)
    have b7635 := hb (x 3 1)
    have b7636 := hb (x 3 1 && x 3 11)
    clear * - r7634 b7635 b7636 d7625
    omega
  have d7637 : (x 3 13).toNat = 0 := by
    have r7638 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b7639 := hb (x 3 1)
    have b7640 := hb (x 3 13)
    clear * - r7638 b7639 b7640 d7625
    omega
  have d7641 : (x 3 3 && x 3 13).toNat = 0 := by
    have r7642 := hand2 (x 3 3) (x 3 13)
    have b7643 := hb (x 3 13)
    have b7644 := hb (x 3 3 && x 3 13)
    clear * - r7642 b7643 b7644 d7637
    omega
  have d7645 : (x 3 6 && x 3 13).toNat = 0 := by
    have r7646 := hand2 (x 3 6) (x 3 13)
    have b7647 := hb (x 3 13)
    have b7648 := hb (x 3 6 && x 3 13)
    clear * - r7646 b7647 b7648 d7637
    omega
  have d7649 : (x 3 8 && x 3 13).toNat = 0 := by
    have r7650 := hand2 (x 3 8) (x 3 13)
    have b7651 := hb (x 3 13)
    have b7652 := hb (x 3 8 && x 3 13)
    clear * - r7650 b7651 b7652 d7637
    omega
  have d7653 : (x 3 5).toNat = 0 := by
    have r7654 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b7655 := hb (x 3 5)
    have b7656 := hb (x 3 13)
    clear * - r7654 b7655 b7656 d7637
    omega
  have d7657 : (x 3 5 && x 3 14).toNat = 0 := by
    have r7658 := hand1 (x 3 5) (x 3 14)
    have b7659 := hb (x 3 5)
    have b7660 := hb (x 3 5 && x 3 14)
    clear * - r7658 b7659 b7660 d7653
    omega
  have d7661 : (x 2 1 && x 2 14).toNat = 1 := by
    have r7662 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7663 := hb (x 1 2)
    have b7664 := hb (x 3 13)
    have b7665 := hb (x 2 1 && x 2 14)
    clear * - r7662 b7663 b7664 b7665 d7637 g13
    omega
  have d7666 : (x 2 14).toNat = 1 := by
    have r7667 := hand2 (x 2 1) (x 2 14)
    have b7668 := hb (x 2 14)
    have b7669 := hb (x 2 1 && x 2 14)
    clear * - r7667 b7668 b7669 d7661
    omega
  have d7670 : (x 1 1).toNat = 0 := by
    have r7671 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7672 := hb (x 1 1)
    have b7673 := hb (x 2 14)
    clear * - r7671 b7672 b7673 d7666
    omega
  have d7674 : (x 1 1 && x 1 12).toNat = 0 := by
    have r7675 := hand1 (x 1 1) (x 1 12)
    have b7676 := hb (x 1 1)
    have b7677 := hb (x 1 1 && x 1 12)
    clear * - r7675 b7676 b7677 d7670
    omega
  have d7678 : (x 1 1 && x 1 11).toNat = 0 := by
    have r7679 := hand1 (x 1 1) (x 1 11)
    have b7680 := hb (x 1 1)
    have b7681 := hb (x 1 1 && x 1 11)
    clear * - r7679 b7680 b7681 d7670
    omega
  have d7682 : (x 1 9).toNat = 0 := by
    have r7683 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b7684 := hb (x 1 1)
    have b7685 := hb (x 1 9)
    clear * - r7683 b7684 b7685 d7670
    omega
  have d7686 : (x 2 1).toNat = 1 := by
    have r7687 := hand1 (x 2 1) (x 2 14)
    have b7688 := hb (x 2 1)
    have b7689 := hb (x 2 1 && x 2 14)
    clear * - r7687 b7688 b7689 d7661
    omega
  have d7690 : (x 3 14).toNat = 0 := by
    have r7691 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7692 := hb (x 2 1)
    have b7693 := hb (x 3 14)
    clear * - r7691 b7692 b7693 d7686
    omega
  have d7694 : (x 3 3 && x 3 14).toNat = 0 := by
    have r7695 := hand2 (x 3 3) (x 3 14)
    have b7696 := hb (x 3 14)
    have b7697 := hb (x 3 3 && x 3 14)
    clear * - r7695 b7696 b7697 d7690
    omega
  have d7698 : (x 3 6).toNat = 0 := by
    have r7699 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b7700 := hb (x 3 6)
    have b7701 := hb (x 3 14)
    clear * - r7699 b7700 b7701 d7690
    omega
  have d7702 : (x 3 2).toNat = 0 := by
    have r7703 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b7704 := hb (x 3 2)
    have b7705 := hb (x 3 14)
    clear * - r7703 b7704 b7705 d7690
    omega
  have d7706 : (x 3 10).toNat = 0 := by
    have r7707 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b7708 := hb (x 3 2)
    have b7709 := hb (x 3 10)
    clear * - r7707 b7708 b7709 d7702
    omega
  have d7710 : (x 6 12).toNat = 0 := by
    have r7711 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7712 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7713 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7714 := hb (x 3 3)
    have b7715 := hb (x 4 2)
    have b7716 := hb (x 5 13)
    have b7717 := hb (x 6 12)
    clear * - r7711 e7712 e7713 b7714 b7715 b7716 b7717 d7616
    omega
  have d7718 : (x 6 4).toNat = 0 := by
    have r7719 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b7720 := hb (x 6 4)
    have b7721 := hb (x 6 12)
    clear * - r7719 b7720 b7721 d7710
    omega
  have d7722 : (x 5 13).toNat = 0 := by
    have r7723 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7724 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7725 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7726 := hb (x 3 3)
    have b7727 := hb (x 4 2)
    have b7728 := hb (x 5 13)
    have b7729 := hb (x 6 12)
    clear * - r7723 e7724 e7725 b7726 b7727 b7728 b7729 d7710 d7616
    omega
  have d7730 : (x 5 5).toNat = 0 := by
    have r7731 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b7732 := hb (x 5 5)
    have b7733 := hb (x 5 13)
    clear * - r7731 b7732 b7733 d7722
    omega
  have d7734 : (x 5 5 && x 5 14).toNat = 0 := by
    have r7735 := hand1 (x 5 5) (x 5 14)
    have b7736 := hb (x 5 5)
    have b7737 := hb (x 5 5 && x 5 14)
    clear * - r7735 b7736 b7737 d7730
    omega
  have d7738 : (x 3 3).toNat = 0 := by
    have r7739 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7740 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7741 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7742 := hb (x 3 3)
    have b7743 := hb (x 4 2)
    have b7744 := hb (x 5 13)
    have b7745 := hb (x 6 12)
    clear * - r7739 e7740 e7741 b7742 b7743 b7744 b7745 d7710 d7722 d7616
    omega
  have d7746 : (x 3 3 && x 3 8).toNat = 0 := by
    have r7747 := hand1 (x 3 3) (x 3 8)
    have b7748 := hb (x 3 3)
    have b7749 := hb (x 3 3 && x 3 8)
    clear * - r7747 b7748 b7749 d7738
    omega
  have d7750 : (x 3 11).toNat = 0 := by
    have r7751 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b7752 := hb (x 3 3)
    have b7753 := hb (x 3 11)
    clear * - r7751 b7752 b7753 d7738
    omega
  have d7754 : (x 5 3 && x 5 14).toNat = 0 := by
    have r7755 := hand2 (x 5 3) (x 5 14)
    have b7756 := hb (x 5 14)
    have b7757 := hb (x 5 3 && x 5 14)
    clear * - r7755 b7756 b7757 d7608
    omega
  have d7758 : (x 5 4 && x 5 14).toNat = 0 := by
    have r7759 := hand2 (x 5 4) (x 5 14)
    have b7760 := hb (x 5 14)
    have b7761 := hb (x 5 4 && x 5 14)
    clear * - r7759 b7760 b7761 d7608
    omega
  have d7762 : (x 5 6).toNat = 0 := by
    have r7763 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
    have b7764 := hb (x 5 6)
    have b7765 := hb (x 5 14)
    clear * - r7763 b7764 b7765 d7608
    omega
  have d7766 : (x 5 6 && x 5 11).toNat = 0 := by
    have r7767 := hand1 (x 5 6) (x 5 11)
    have b7768 := hb (x 5 6)
    have b7769 := hb (x 5 6 && x 5 11)
    clear * - r7767 b7768 b7769 d7762
    omega
  have d7770 : (x 5 1 && x 5 6).toNat = 0 := by
    have r7771 := hand2 (x 5 1) (x 5 6)
    have b7772 := hb (x 5 6)
    have b7773 := hb (x 5 1 && x 5 6)
    clear * - r7771 b7772 b7773 d7762
    omega
  have d7774 : (x 4 10).toNat = 1 := by
    have r7775 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7776 := hb (x (-1) 5)
    have b7777 := hb (x 4 10)
    have b7778 := hb (x 3 1 && x 3 11)
    have b7779 := hb (x 2 2 && x 2 12)
    have b7780 := hb (x 1 3 && x 1 13)
    have b7781 := hb (x 0 4 && x 0 14)
    clear * - r7775 b7776 b7777 b7778 b7779 b7780 b7781 d7633 g52 g53 d7501 g4
    omega
  have d7782 : (x 7 8).toNat = 0 := by
    have r7783 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7784 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e7785 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e7786 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e7787 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e7788 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e7789 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b7790 := hb (x 0 7)
    have b7791 := hb (x 1 6)
    have b7792 := hb (x 2 5)
    have b7793 := hb (x 3 4)
    have b7794 := hb (x 4 11)
    have b7795 := hb (x 5 10)
    have b7796 := hb (x 6 9)
    have b7797 := hb (x 7 8)
    clear * - r7783 e7784 e7785 e7786 e7787 e7788 e7789 b7790 b7791 b7792 b7793 b7794 b7795 b7796 b7797 d7592 d7505 g20 g19 g15
    omega
  have d7798 : (x 6 9).toNat = 0 := by
    have r7799 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7800 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e7801 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e7802 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e7803 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e7804 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e7805 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b7806 := hb (x 0 7)
    have b7807 := hb (x 1 6)
    have b7808 := hb (x 2 5)
    have b7809 := hb (x 3 4)
    have b7810 := hb (x 4 11)
    have b7811 := hb (x 5 10)
    have b7812 := hb (x 6 9)
    have b7813 := hb (x 7 8)
    clear * - r7799 e7800 e7801 e7802 e7803 e7804 e7805 b7806 b7807 b7808 b7809 b7810 b7811 b7812 b7813 d7782 d7592 d7505 g20 g19 g15
    omega
  have d7814 : (x 0 7).toNat = 0 := by
    have r7815 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7816 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e7817 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e7818 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e7819 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e7820 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e7821 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b7822 := hb (x 0 7)
    have b7823 := hb (x 1 6)
    have b7824 := hb (x 2 5)
    have b7825 := hb (x 3 4)
    have b7826 := hb (x 4 11)
    have b7827 := hb (x 5 10)
    have b7828 := hb (x 6 9)
    have b7829 := hb (x 7 8)
    clear * - r7815 e7816 e7817 e7818 e7819 e7820 e7821 b7822 b7823 b7824 b7825 b7826 b7827 b7828 b7829 d7782 d7798 d7592 d7505 g20 g19 g15
    omega
  have d7830 : (x 0 1 && x 0 7).toNat = 0 := by
    have r7831 := hand2 (x 0 1) (x 0 7)
    have b7832 := hb (x 0 7)
    have b7833 := hb (x 0 1 && x 0 7)
    clear * - r7831 b7832 b7833 d7814
    omega
  have d7834 : (x 0 7 && x 0 11).toNat = 0 := by
    have r7835 := hand1 (x 0 7) (x 0 11)
    have b7836 := hb (x 0 7)
    have b7837 := hb (x 0 7 && x 0 11)
    clear * - r7835 b7836 b7837 d7814
    omega
  have d7838 : (x 6 8).toNat = 0 := by
    have r7839 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7840 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e7841 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e7842 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e7843 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e7844 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e7845 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b7846 := hb (x (-1) 7)
    have b7847 := hb (x 0 6)
    have b7848 := hb (x 1 5)
    have b7849 := hb (x 2 4)
    have b7850 := hb (x 3 11)
    have b7851 := hb (x 4 10)
    have b7852 := hb (x 5 9)
    have b7853 := hb (x 6 8)
    clear * - r7839 e7840 e7841 e7842 e7843 e7844 e7845 b7846 b7847 b7848 b7849 b7850 b7851 b7852 b7853 d7774 d7750 g18 g14
    omega
  have d7854 : (x 5 9).toNat = 0 := by
    have r7855 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7856 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e7857 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e7858 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e7859 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e7860 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e7861 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b7862 := hb (x (-1) 7)
    have b7863 := hb (x 0 6)
    have b7864 := hb (x 1 5)
    have b7865 := hb (x 2 4)
    have b7866 := hb (x 3 11)
    have b7867 := hb (x 4 10)
    have b7868 := hb (x 5 9)
    have b7869 := hb (x 6 8)
    clear * - r7855 e7856 e7857 e7858 e7859 e7860 e7861 b7862 b7863 b7864 b7865 b7866 b7867 b7868 b7869 d7838 d7774 d7750 g18 g14
    omega
  have d7870 : (x 0 6).toNat = 0 := by
    have r7871 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7872 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e7873 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e7874 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e7875 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e7876 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e7877 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b7878 := hb (x (-1) 7)
    have b7879 := hb (x 0 6)
    have b7880 := hb (x 1 5)
    have b7881 := hb (x 2 4)
    have b7882 := hb (x 3 11)
    have b7883 := hb (x 4 10)
    have b7884 := hb (x 5 9)
    have b7885 := hb (x 6 8)
    clear * - r7871 e7872 e7873 e7874 e7875 e7876 e7877 b7878 b7879 b7880 b7881 b7882 b7883 b7884 b7885 d7838 d7854 d7774 d7750 g18 g14
    omega
  have d7886 : (x 0 6 && x 0 11).toNat = 0 := by
    have r7887 := hand1 (x 0 6) (x 0 11)
    have b7888 := hb (x 0 6)
    have b7889 := hb (x 0 6 && x 0 11)
    clear * - r7887 b7888 b7889 d7870
    omega
  have d7890 : (x 0 1 && x 0 6).toNat = 0 := by
    have r7891 := hand2 (x 0 1) (x 0 6)
    have b7892 := hb (x 0 6)
    have b7893 := hb (x 0 1 && x 0 6)
    clear * - r7891 b7892 b7893 d7870
    omega
  have d7894 : (x 0 2 && x 0 6).toNat = 0 := by
    have r7895 := hand2 (x 0 2) (x 0 6)
    have b7896 := hb (x 0 6)
    have b7897 := hb (x 0 2 && x 0 6)
    clear * - r7895 b7896 b7897 d7870
    omega
  have d7898 : (x (-1) 7).toNat = 0 := by
    have r7899 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7900 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e7901 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e7902 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e7903 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e7904 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e7905 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b7906 := hb (x (-1) 7)
    have b7907 := hb (x 0 6)
    have b7908 := hb (x 1 5)
    have b7909 := hb (x 2 4)
    have b7910 := hb (x 3 11)
    have b7911 := hb (x 4 10)
    have b7912 := hb (x 5 9)
    have b7913 := hb (x 6 8)
    clear * - r7899 e7900 e7901 e7902 e7903 e7904 e7905 b7906 b7907 b7908 b7909 b7910 b7911 b7912 b7913 d7838 d7854 d7774 d7750 g18 g14 d7870
    omega
  have d7914 : (x (-1) 7 && x (-1) 12).toNat = 0 := by
    have r7915 := hand1 (x (-1) 7) (x (-1) 12)
    have b7916 := hb (x (-1) 7)
    have b7917 := hb (x (-1) 7 && x (-1) 12)
    clear * - r7915 b7916 b7917 d7898
    omega
  have d7918 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
    have r7919 := hand2 (x (-1) 2) (x (-1) 7)
    have b7920 := hb (x (-1) 7)
    have b7921 := hb (x (-1) 2 && x (-1) 7)
    clear * - r7919 b7920 b7921 d7898
    omega
  cases h7922 : x 0 12
  · have f7923 : (x 0 12).toNat = 0 := by rw [h7922]; rfl
    have d7924 : (x 0 1 && x 0 12).toNat = 0 := by
      have r7925 := hand2 (x 0 1) (x 0 12)
      have b7926 := hb (x 0 12)
      have b7927 := hb (x 0 1 && x 0 12)
      clear * - r7925 b7926 b7927 f7923
      omega
    have d7928 : (x 0 2 && x 0 12).toNat = 0 := by
      have r7929 := hand2 (x 0 2) (x 0 12)
      have b7930 := hb (x 0 12)
      have b7931 := hb (x 0 2 && x 0 12)
      clear * - r7929 b7930 b7931 f7923
      omega
    cases h7932 : x 0 10
    · have f7933 : (x 0 10).toNat = 0 := by rw [h7932]; rfl
      have d7934 : (x 0 1 && x 0 10).toNat = 0 := by
        have r7935 := hand2 (x 0 1) (x 0 10)
        have b7936 := hb (x 0 10)
        have b7937 := hb (x 0 1 && x 0 10)
        clear * - r7935 b7936 b7937 f7933
        omega
      have d7938 : (x (-2) 3 && x (-2) 12).toNat = 1 := by
        have r7939 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b7940 := hb (x (-5) 6)
        have b7941 := hb (x 1 9)
        have b7942 := hb (x 0 1 && x 0 10)
        have b7943 := hb (x (-1) 2 && x (-1) 11)
        have b7944 := hb (x (-2) 3 && x (-2) 12)
        have b7945 := hb (x (-3) 4 && x (-3) 13)
        have b7946 := hb (x (-4) 5 && x (-4) 14)
        clear * - r7939 b7940 b7941 b7942 b7943 b7944 b7945 b7946 d7682 d7934 g43 g44 g45 g0
        omega
      have d7947 : (x (-2) 12).toNat = 1 := by
        have r7948 := hand2 (x (-2) 3) (x (-2) 12)
        have b7949 := hb (x (-2) 12)
        have b7950 := hb (x (-2) 3 && x (-2) 12)
        clear * - r7948 b7949 b7950 d7938
        omega
      have d7951 : (x (-3) 13).toNat = 0 := by
        have r7952 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7953 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e7954 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b7955 := hb (x (-5) 3)
        have b7956 := hb (x (-4) 2)
        have b7957 := hb (x (-3) 13)
        have b7958 := hb (x (-2) 12)
        clear * - r7952 e7953 e7954 b7955 b7956 b7957 b7958 d7947
        omega
      have d7959 : (x (-3) 5).toNat = 0 := by
        have r7960 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
        have b7961 := hb (x (-3) 5)
        have b7962 := hb (x (-3) 13)
        clear * - r7960 b7961 b7962 d7951
        omega
      have d7963 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
        have r7964 := hand1 (x (-3) 5) (x (-3) 9)
        have b7965 := hb (x (-3) 5)
        have b7966 := hb (x (-3) 5 && x (-3) 9)
        clear * - r7964 b7965 b7966 d7959
        omega
      have d7967 : (x (-4) 2).toNat = 0 := by
        have r7968 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7969 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e7970 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b7971 := hb (x (-5) 3)
        have b7972 := hb (x (-4) 2)
        have b7973 := hb (x (-3) 13)
        have b7974 := hb (x (-2) 12)
        clear * - r7968 e7969 e7970 b7971 b7972 b7973 b7974 d7947 d7951
        omega
      have d7975 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
        have r7976 := hand1 (x (-4) 2) (x (-4) 13)
        have b7977 := hb (x (-4) 2)
        have b7978 := hb (x (-4) 2 && x (-4) 13)
        clear * - r7976 b7977 b7978 d7967
        omega
      have d7979 : (x (-4) 10).toNat = 0 := by
        have r7980 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
        have b7981 := hb (x (-4) 2)
        have b7982 := hb (x (-4) 10)
        clear * - r7980 b7981 b7982 d7967
        omega
      have d7983 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
        have r7984 := hand2 (x (-4) 6) (x (-4) 10)
        have b7985 := hb (x (-4) 10)
        have b7986 := hb (x (-4) 6 && x (-4) 10)
        clear * - r7984 b7985 b7986 d7979
        omega
      have d7987 : (x (-5) 3).toNat = 0 := by
        have r7988 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7989 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e7990 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b7991 := hb (x (-5) 3)
        have b7992 := hb (x (-4) 2)
        have b7993 := hb (x (-3) 13)
        have b7994 := hb (x (-2) 12)
        clear * - r7988 e7989 e7990 b7991 b7992 b7993 b7994 d7947 d7951 d7967
        omega
      have d7995 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
        have r7996 := hand1 (x (-5) 3) (x (-5) 14)
        have b7997 := hb (x (-5) 3)
        have b7998 := hb (x (-5) 3 && x (-5) 14)
        clear * - r7996 b7997 b7998 d7987
        omega
      have d7999 : (x (-5) 11).toNat = 0 := by
        have r8000 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
        have b8001 := hb (x (-5) 3)
        have b8002 := hb (x (-5) 11)
        clear * - r8000 b8001 b8002 d7987
        omega
      have d8003 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
        have r8004 := hand2 (x (-5) 7) (x (-5) 11)
        have b8005 := hb (x (-5) 11)
        have b8006 := hb (x (-5) 7 && x (-5) 11)
        clear * - r8004 b8005 b8006 d7999
        omega
      have d8007 : (x (-2) 3).toNat = 1 := by
        have r8008 := hand1 (x (-2) 3) (x (-2) 12)
        have b8009 := hb (x (-2) 3)
        have b8010 := hb (x (-2) 3 && x (-2) 12)
        clear * - r8008 b8009 b8010 d7938
        omega
      have d8011 : (x 1 12).toNat = 0 := by
        have r8012 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8013 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e8014 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b8015 := hb (x (-2) 3)
        have b8016 := hb (x (-1) 2)
        have b8017 := hb (x 0 13)
        have b8018 := hb (x 1 12)
        clear * - r8012 e8013 e8014 b8015 b8016 b8017 b8018 d8007
        omega
      have d8019 : (x 0 13).toNat = 0 := by
        have r8020 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8021 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e8022 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b8023 := hb (x (-2) 3)
        have b8024 := hb (x (-1) 2)
        have b8025 := hb (x 0 13)
        have b8026 := hb (x 1 12)
        clear * - r8020 e8021 e8022 b8023 b8024 b8025 b8026 d8011 d8007
        omega
      have d8027 : (x 0 3 && x 0 13).toNat = 0 := by
        have r8028 := hand2 (x 0 3) (x 0 13)
        have b8029 := hb (x 0 13)
        have b8030 := hb (x 0 3 && x 0 13)
        clear * - r8028 b8029 b8030 d8019
        omega
      have d8031 : (x (-2) 2).toNat = 1 := by
        have r8032 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8033 := hb (x (-2) 2)
        have b8034 := hb (x 0 13)
        have b8035 := hb (x (-1) 1 && x (-1) 14)
        clear * - r8032 b8033 b8034 b8035 d8019 g63
        omega
      have d8036 : (x (-2) 14).toNat = 1 := by
        have r8037 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
        have b8038 := hb (x (-2) 2)
        have b8039 := hb (x (-2) 14)
        clear * - r8037 b8038 b8039 d8031
        omega
      have d8040 : (x (-3) 1).toNat = 0 := by
        have r8041 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8042 := hb (x (-3) 1)
        have b8043 := hb (x (-2) 14)
        clear * - r8041 b8042 b8043 d8036
        omega
      have d8044 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
        have r8045 := hand1 (x (-3) 1) (x (-3) 14)
        have b8046 := hb (x (-3) 1)
        have b8047 := hb (x (-3) 1 && x (-3) 14)
        clear * - r8045 b8046 b8047 d8040
        omega
      have d8048 : (x (-2) 13).toNat = 1 := by
        have r8049 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8050 := hb (x (-4) 2)
        have b8051 := hb (x (-2) 13)
        have b8052 := hb (x (-3) 1 && x (-3) 14)
        clear * - r8049 b8050 b8051 b8052 d8044 d7967
        omega
      have d8053 : (x (-2) 1).toNat = 1 := by
        have r8054 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b8055 := hb (x (-2) 1)
        have b8056 := hb (x (-2) 13)
        clear * - r8054 b8055 b8056 d8048
        omega
      have d8057 : (x (-1) 14).toNat = 0 := by
        have r8058 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8059 := hb (x (-2) 1)
        have b8060 := hb (x (-1) 14)
        clear * - r8058 b8059 b8060 d8053
        omega
      have d8061 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
        have r8062 := hand2 (x (-1) 4) (x (-1) 14)
        have b8063 := hb (x (-1) 14)
        have b8064 := hb (x (-1) 4 && x (-1) 14)
        clear * - r8062 b8063 b8064 d8057
        omega
      have d8065 : (x (-1) 2).toNat = 0 := by
        have r8066 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b8067 := hb (x (-1) 2)
        have b8068 := hb (x (-1) 14)
        clear * - r8066 b8067 b8068 d8057
        omega
      have d8069 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
        have r8070 := hand1 (x (-1) 2) (x (-1) 8)
        have b8071 := hb (x (-1) 2)
        have b8072 := hb (x (-1) 2 && x (-1) 8)
        clear * - r8070 b8071 b8072 d8065
        omega
      have d8073 : (x (-1) 12).toNat = 0 := by
        have r8074 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8075 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e8076 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b8077 := hb (x (-4) 3)
        have b8078 := hb (x (-3) 2)
        have b8079 := hb (x (-2) 13)
        have b8080 := hb (x (-1) 12)
        clear * - r8074 e8075 e8076 b8077 b8078 b8079 b8080 d8048
        omega
      have d8081 : (x (-1) 4).toNat = 0 := by
        have r8082 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b8083 := hb (x (-1) 4)
        have b8084 := hb (x (-1) 12)
        clear * - r8082 b8083 b8084 d8073
        omega
      have d8085 : (x (-3) 2).toNat = 0 := by
        have r8086 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8087 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e8088 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b8089 := hb (x (-4) 3)
        have b8090 := hb (x (-3) 2)
        have b8091 := hb (x (-2) 13)
        have b8092 := hb (x (-1) 12)
        clear * - r8086 e8087 e8088 b8089 b8090 b8091 b8092 d8073 d8048
        omega
      have d8093 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
        have r8094 := hand1 (x (-3) 2) (x (-3) 12)
        have b8095 := hb (x (-3) 2)
        have b8096 := hb (x (-3) 2 && x (-3) 12)
        clear * - r8094 b8095 b8096 d8085
        omega
      have d8097 : (x (-3) 10).toNat = 0 := by
        have r8098 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
        have b8099 := hb (x (-3) 2)
        have b8100 := hb (x (-3) 10)
        clear * - r8098 b8099 b8100 d8085
        omega
      have d8101 : (x (-4) 3).toNat = 0 := by
        have r8102 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8103 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e8104 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b8105 := hb (x (-4) 3)
        have b8106 := hb (x (-3) 2)
        have b8107 := hb (x (-2) 13)
        have b8108 := hb (x (-1) 12)
        clear * - r8102 e8103 e8104 b8105 b8106 b8107 b8108 d8073 d8048 d8085
        omega
      have d8109 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
        have r8110 := hand1 (x (-4) 3) (x (-4) 13)
        have b8111 := hb (x (-4) 3)
        have b8112 := hb (x (-4) 3 && x (-4) 13)
        clear * - r8110 b8111 b8112 d8101
        omega
      have d8113 : (x (-4) 11).toNat = 0 := by
        have r8114 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
        have b8115 := hb (x (-4) 3)
        have b8116 := hb (x (-4) 11)
        clear * - r8114 b8115 b8116 d8101
        omega
      have d8117 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
        have r8118 := hand1 (x (-3) 1) (x (-3) 12)
        have b8119 := hb (x (-3) 1)
        have b8120 := hb (x (-3) 1 && x (-3) 12)
        clear * - r8118 b8119 b8120 d8040
        omega
      have d8121 : (x (-6) 4).toNat = 1 := by
        have r8122 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8123 := hb (x (-6) 4)
        have b8124 := hb (x (-2) 11)
        have b8125 := hb (x (-3) 1 && x (-3) 12)
        have b8126 := hb (x (-4) 2 && x (-4) 13)
        have b8127 := hb (x (-5) 3 && x (-5) 14)
        clear * - r8122 b8123 b8124 b8125 b8126 b8127 g3 d8117 d7975 d7995
        omega
      have d8128 : (x (-6) 12).toNat = 1 := by
        have r8129 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
        have b8130 := hb (x (-6) 4)
        have b8131 := hb (x (-6) 12)
        clear * - r8129 b8130 b8131 d8121
        omega
      have d8132 : (x (-7) 13).toNat = 0 := by
        have r8133 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8134 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e8135 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b8136 := hb (x (-9) 3)
        have b8137 := hb (x (-8) 2)
        have b8138 := hb (x (-7) 13)
        have b8139 := hb (x (-6) 12)
        clear * - r8133 e8134 e8135 b8136 b8137 b8138 b8139 d8128
        omega
      have d8140 : (x (-7) 8 && x (-7) 13).toNat = 0 := by
        have r8141 := hand2 (x (-7) 8) (x (-7) 13)
        have b8142 := hb (x (-7) 13)
        have b8143 := hb (x (-7) 8 && x (-7) 13)
        clear * - r8141 b8142 b8143 d8132
        omega
      have d8144 : (x (-7) 9 && x (-7) 13).toNat = 0 := by
        have r8145 := hand2 (x (-7) 9) (x (-7) 13)
        have b8146 := hb (x (-7) 13)
        have b8147 := hb (x (-7) 9 && x (-7) 13)
        clear * - r8145 b8146 b8147 d8132
        omega
      have d8148 : (x (-7) 5).toNat = 0 := by
        have r8149 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
        have b8150 := hb (x (-7) 5)
        have b8151 := hb (x (-7) 13)
        clear * - r8149 b8150 b8151 d8132
        omega
      have d8152 : (x (-8) 2).toNat = 0 := by
        have r8153 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8154 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e8155 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b8156 := hb (x (-9) 3)
        have b8157 := hb (x (-8) 2)
        have b8158 := hb (x (-7) 13)
        have b8159 := hb (x (-6) 12)
        clear * - r8153 e8154 e8155 b8156 b8157 b8158 b8159 d8128 d8132
        omega
      have d8160 : (x (-8) 2 && x (-8) 13).toNat = 0 := by
        have r8161 := hand1 (x (-8) 2) (x (-8) 13)
        have b8162 := hb (x (-8) 2)
        have b8163 := hb (x (-8) 2 && x (-8) 13)
        clear * - r8161 b8162 b8163 d8152
        omega
      have d8164 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
        have r8165 := hand1 (x (-8) 2) (x (-8) 12)
        have b8166 := hb (x (-8) 2)
        have b8167 := hb (x (-8) 2 && x (-8) 12)
        clear * - r8165 b8166 b8167 d8152
        omega
      have d8168 : (x (-8) 2 && x (-8) 11).toNat = 0 := by
        have r8169 := hand1 (x (-8) 2) (x (-8) 11)
        have b8170 := hb (x (-8) 2)
        have b8171 := hb (x (-8) 2 && x (-8) 11)
        clear * - r8169 b8170 b8171 d8152
        omega
      have d8172 : (x (-8) 10).toNat = 0 := by
        have r8173 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
        have b8174 := hb (x (-8) 2)
        have b8175 := hb (x (-8) 10)
        clear * - r8173 b8174 b8175 d8152
        omega
      have d8176 : (x (-9) 3).toNat = 0 := by
        have r8177 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8178 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e8179 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b8180 := hb (x (-9) 3)
        have b8181 := hb (x (-8) 2)
        have b8182 := hb (x (-7) 13)
        have b8183 := hb (x (-6) 12)
        clear * - r8177 e8178 e8179 b8180 b8181 b8182 b8183 d8128 d8132 d8152
        omega
      have d8184 : (x (-9) 3 && x (-9) 14).toNat = 0 := by
        have r8185 := hand1 (x (-9) 3) (x (-9) 14)
        have b8186 := hb (x (-9) 3)
        have b8187 := hb (x (-9) 3 && x (-9) 14)
        clear * - r8185 b8186 b8187 d8176
        omega
      have d8188 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
        have r8189 := hand1 (x (-9) 3) (x (-9) 13)
        have b8190 := hb (x (-9) 3)
        have b8191 := hb (x (-9) 3 && x (-9) 13)
        clear * - r8189 b8190 b8191 d8176
        omega
      have d8192 : (x (-9) 3 && x (-9) 12).toNat = 0 := by
        have r8193 := hand1 (x (-9) 3) (x (-9) 12)
        have b8194 := hb (x (-9) 3)
        have b8195 := hb (x (-9) 3 && x (-9) 12)
        clear * - r8193 b8194 b8195 d8176
        omega
      have d8196 : (x (-9) 11).toNat = 0 := by
        have r8197 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
        have b8198 := hb (x (-9) 3)
        have b8199 := hb (x (-9) 11)
        clear * - r8197 b8198 b8199 d8176
        omega
      have d8200 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
        have r8201 := hand2 (x (-9) 1) (x (-9) 11)
        have b8202 := hb (x (-9) 11)
        have b8203 := hb (x (-9) 1 && x (-9) 11)
        clear * - r8201 b8202 b8203 d8196
        omega
      have d8204 : (x (-3) 9).toNat = 0 := by
        have r8205 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
        have b8206 := hb (x (-3) 1)
        have b8207 := hb (x (-3) 9)
        clear * - r8205 b8206 b8207 d8040
        omega
      have d8208 : (x (-3) 9 && x (-3) 14).toNat = 0 := by
        have r8209 := hand1 (x (-3) 9) (x (-3) 14)
        have b8210 := hb (x (-3) 9)
        have b8211 := hb (x (-3) 9 && x (-3) 14)
        clear * - r8209 b8210 b8211 d8204
        omega
      have d8212 : (x (-2) 8).toNat = 0 := by
        have r8213 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8214 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e8215 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e8216 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e8217 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e8218 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e8219 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b8220 := hb (x (-9) 7)
        have b8221 := hb (x (-8) 6)
        have b8222 := hb (x (-7) 5)
        have b8223 := hb (x (-6) 4)
        have b8224 := hb (x (-5) 11)
        have b8225 := hb (x (-4) 10)
        have b8226 := hb (x (-3) 9)
        have b8227 := hb (x (-2) 8)
        clear * - r8213 e8214 e8215 e8216 e8217 e8218 e8219 b8220 b8221 b8222 b8223 b8224 b8225 b8226 b8227 d8204 d7979 d7999 d8121 d8148
        omega
      have d8228 : (x (-2) 8 && x (-2) 13).toNat = 0 := by
        have r8229 := hand1 (x (-2) 8) (x (-2) 13)
        have b8230 := hb (x (-2) 8)
        have b8231 := hb (x (-2) 8 && x (-2) 13)
        clear * - r8229 b8230 b8231 d8212
        omega
      have d8232 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
        have r8233 := hand2 (x (-2) 3) (x (-2) 8)
        have b8234 := hb (x (-2) 8)
        have b8235 := hb (x (-2) 3 && x (-2) 8)
        clear * - r8233 b8234 b8235 d8212
        omega
      have d8236 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
        have r8237 := hand2 (x (-2) 4) (x (-2) 8)
        have b8238 := hb (x (-2) 8)
        have b8239 := hb (x (-2) 4 && x (-2) 8)
        clear * - r8237 b8238 b8239 d8212
        omega
      have d8240 : (x 4 2 && x 4 7).toNat = 1 := by
        have r8241 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8242 := hb (x (-4) 10)
        have b8243 := hb (x 6 5)
        have b8244 := hb (x 5 1 && x 5 6)
        have b8245 := hb (x 4 2 && x 4 7)
        have b8246 := hb (x 3 3 && x 3 8)
        have b8247 := hb (x 2 4 && x 2 9)
        have b8248 := hb (x 1 5 && x 1 10)
        have b8249 := hb (x 0 6 && x 0 11)
        have b8250 := hb (x (-1) 7 && x (-1) 12)
        have b8251 := hb (x (-2) 8 && x (-2) 13)
        have b8252 := hb (x (-3) 9 && x (-3) 14)
        clear * - r8241 b8242 b8243 b8244 b8245 b8246 b8247 b8248 b8249 b8250 b8251 b8252 d7568 d7770 d7746 g31 g32 d7886 d7914 d8228 d8208 d7979
        omega
      have d8253 : (x 4 7).toNat = 1 := by
        have r8254 := hand2 (x 4 2) (x 4 7)
        have b8255 := hb (x 4 7)
        have b8256 := hb (x 4 2 && x 4 7)
        clear * - r8254 b8255 b8256 d8240
        omega
      have d8257 : (x 11 8).toNat = 0 := by
        have r8258 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8259 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e8260 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e8261 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e8262 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e8263 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e8264 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b8265 := hb (x 4 7)
        have b8266 := hb (x 5 6)
        have b8267 := hb (x 6 5)
        have b8268 := hb (x 7 4)
        have b8269 := hb (x 8 11)
        have b8270 := hb (x 9 10)
        have b8271 := hb (x 10 9)
        have b8272 := hb (x 11 8)
        clear * - r8258 e8259 e8260 e8261 e8262 e8263 e8264 b8265 b8266 b8267 b8268 b8269 b8270 b8271 b8272 d7536 d7568 d7762 d8253
        omega
      have d8273 : (x 10 9).toNat = 0 := by
        have r8274 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8275 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e8276 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e8277 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e8278 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e8279 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e8280 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b8281 := hb (x 4 7)
        have b8282 := hb (x 5 6)
        have b8283 := hb (x 6 5)
        have b8284 := hb (x 7 4)
        have b8285 := hb (x 8 11)
        have b8286 := hb (x 9 10)
        have b8287 := hb (x 10 9)
        have b8288 := hb (x 11 8)
        clear * - r8274 e8275 e8276 e8277 e8278 e8279 e8280 b8281 b8282 b8283 b8284 b8285 b8286 b8287 b8288 d8257 d7536 d7568 d7762 d8253
        omega
      have d8289 : (x 9 10).toNat = 0 := by
        have r8290 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8291 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e8292 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e8293 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e8294 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e8295 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e8296 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b8297 := hb (x 4 7)
        have b8298 := hb (x 5 6)
        have b8299 := hb (x 6 5)
        have b8300 := hb (x 7 4)
        have b8301 := hb (x 8 11)
        have b8302 := hb (x 9 10)
        have b8303 := hb (x 10 9)
        have b8304 := hb (x 11 8)
        clear * - r8290 e8291 e8292 e8293 e8294 e8295 e8296 b8297 b8298 b8299 b8300 b8301 b8302 b8303 b8304 d8257 d8273 d7536 d7568 d7762 d8253
        omega
      have d8305 : (x 8 11).toNat = 0 := by
        have r8306 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8307 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e8308 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e8309 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e8310 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e8311 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e8312 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b8313 := hb (x 4 7)
        have b8314 := hb (x 5 6)
        have b8315 := hb (x 6 5)
        have b8316 := hb (x 7 4)
        have b8317 := hb (x 8 11)
        have b8318 := hb (x 9 10)
        have b8319 := hb (x 10 9)
        have b8320 := hb (x 11 8)
        clear * - r8306 e8307 e8308 e8309 e8310 e8311 e8312 b8313 b8314 b8315 b8316 b8317 b8318 b8319 b8320 d8257 d8273 d8289 d7536 d7568 d7762 d8253
        omega
      have d8321 : (x 8 1 && x 8 11).toNat = 0 := by
        have r8322 := hand2 (x 8 1) (x 8 11)
        have b8323 := hb (x 8 11)
        have b8324 := hb (x 8 1 && x 8 11)
        clear * - r8322 b8323 b8324 d8305
        omega
      have d8325 : (x 4 5).toNat = 1 := by
        have r8326 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8327 := hb (x 4 5)
        have b8328 := hb (x 9 10)
        have b8329 := hb (x 8 1 && x 8 11)
        have b8330 := hb (x 7 2 && x 7 12)
        have b8331 := hb (x 6 3 && x 6 13)
        have b8332 := hb (x 5 4 && x 5 14)
        clear * - r8326 b8327 b8328 b8329 b8330 b8331 b8332 d8289 d8321 d7528 d7560 d7758
        omega
      have d8333 : (x 4 13).toNat = 1 := by
        have r8334 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
        have b8335 := hb (x 4 5)
        have b8336 := hb (x 4 13)
        clear * - r8334 b8335 b8336 d8325
        omega
      have d8337 : (x 5 12).toNat = 0 := by
        have r8338 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8339 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e8340 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b8341 := hb (x 2 3)
        have b8342 := hb (x 3 2)
        have b8343 := hb (x 4 13)
        have b8344 := hb (x 5 12)
        clear * - r8338 e8339 e8340 b8341 b8342 b8343 b8344 d8333 d7702
        omega
      have d8345 : (x 2 3).toNat = 0 := by
        have r8346 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8347 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e8348 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b8349 := hb (x 2 3)
        have b8350 := hb (x 3 2)
        have b8351 := hb (x 4 13)
        have b8352 := hb (x 5 12)
        clear * - r8346 e8347 e8348 b8349 b8350 b8351 b8352 d8337 d8333 d7702
        omega
      have d8353 : (x 2 11).toNat = 0 := by
        have r8354 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
        have b8355 := hb (x 2 3)
        have b8356 := hb (x 2 11)
        clear * - r8354 b8355 b8356 d8345
        omega
      have d8357 : (x 2 1 && x 2 11).toNat = 0 := by
        have r8358 := hand2 (x 2 1) (x 2 11)
        have b8359 := hb (x 2 11)
        have b8360 := hb (x 2 1 && x 2 11)
        clear * - r8358 b8359 b8360 d8353
        omega
      have d8361 : (x (-2) 5).toNat = 1 := by
        have r8362 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8363 := hb (x (-2) 5)
        have b8364 := hb (x 3 10)
        have b8365 := hb (x 2 1 && x 2 11)
        have b8366 := hb (x 1 2 && x 1 12)
        have b8367 := hb (x 0 3 && x 0 13)
        have b8368 := hb (x (-1) 4 && x (-1) 14)
        clear * - r8362 b8363 b8364 b8365 b8366 b8367 b8368 d7706 d8357 g51 d8027 d8061
        omega
      have d8369 : (x 3 8).toNat = 0 := by
        have r8370 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8371 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e8372 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e8373 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e8374 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e8375 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e8376 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b8377 := hb (x (-4) 7)
        have b8378 := hb (x (-3) 6)
        have b8379 := hb (x (-2) 5)
        have b8380 := hb (x (-1) 4)
        have b8381 := hb (x 0 11)
        have b8382 := hb (x 1 10)
        have b8383 := hb (x 2 9)
        have b8384 := hb (x 3 8)
        clear * - r8370 e8371 e8372 e8373 e8374 e8375 e8376 b8377 b8378 b8379 b8380 b8381 b8382 b8383 b8384 g17 d8081 d8361
        omega
      have d8385 : (x 2 9).toNat = 0 := by
        have r8386 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8387 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e8388 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e8389 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e8390 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e8391 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e8392 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b8393 := hb (x (-4) 7)
        have b8394 := hb (x (-3) 6)
        have b8395 := hb (x (-2) 5)
        have b8396 := hb (x (-1) 4)
        have b8397 := hb (x 0 11)
        have b8398 := hb (x 1 10)
        have b8399 := hb (x 2 9)
        have b8400 := hb (x 3 8)
        clear * - r8386 e8387 e8388 e8389 e8390 e8391 e8392 b8393 b8394 b8395 b8396 b8397 b8398 b8399 b8400 d8369 g17 d8081 d8361
        omega
      have d8401 : (x 0 11).toNat = 0 := by
        have r8402 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8403 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e8404 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e8405 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e8406 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e8407 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e8408 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b8409 := hb (x (-4) 7)
        have b8410 := hb (x (-3) 6)
        have b8411 := hb (x (-2) 5)
        have b8412 := hb (x (-1) 4)
        have b8413 := hb (x 0 11)
        have b8414 := hb (x 1 10)
        have b8415 := hb (x 2 9)
        have b8416 := hb (x 3 8)
        clear * - r8402 e8403 e8404 e8405 e8406 e8407 e8408 b8409 b8410 b8411 b8412 b8413 b8414 b8415 b8416 d8369 d8385 g17 d8081 d8361
        omega
      have d8417 : (x (-3) 6).toNat = 0 := by
        have r8418 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8419 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e8420 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e8421 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e8422 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e8423 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e8424 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b8425 := hb (x (-4) 7)
        have b8426 := hb (x (-3) 6)
        have b8427 := hb (x (-2) 5)
        have b8428 := hb (x (-1) 4)
        have b8429 := hb (x 0 11)
        have b8430 := hb (x 1 10)
        have b8431 := hb (x 2 9)
        have b8432 := hb (x 3 8)
        clear * - r8418 e8419 e8420 e8421 e8422 e8423 e8424 b8425 b8426 b8427 b8428 b8429 b8430 b8431 b8432 d8369 d8385 g17 d8401 d8081 d8361
        omega
      have d8433 : (x (-4) 7).toNat = 0 := by
        have r8434 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8435 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e8436 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e8437 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e8438 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e8439 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e8440 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b8441 := hb (x (-4) 7)
        have b8442 := hb (x (-3) 6)
        have b8443 := hb (x (-2) 5)
        have b8444 := hb (x (-1) 4)
        have b8445 := hb (x 0 11)
        have b8446 := hb (x 1 10)
        have b8447 := hb (x 2 9)
        have b8448 := hb (x 3 8)
        clear * - r8434 e8435 e8436 e8437 e8438 e8439 e8440 b8441 b8442 b8443 b8444 b8445 b8446 b8447 b8448 d8369 d8385 g17 d8401 d8081 d8361 d8417
        omega
      have d8449 : (x (-6) 8 && x (-6) 12).toNat = 1 := by
        have r8450 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8451 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
        have e8452 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
        have b8453 := hb (x (-9) 11)
        have b8454 := hb (x (-8) 10)
        have b8455 := hb (x 1 5)
        have b8456 := hb (x 2 4)
        have b8457 := hb (x 0 2 && x 0 6)
        have b8458 := hb (x (-1) 3 && x (-1) 7)
        have b8459 := hb (x (-2) 4 && x (-2) 8)
        have b8460 := hb (x (-3) 5 && x (-3) 9)
        have b8461 := hb (x (-4) 6 && x (-4) 10)
        have b8462 := hb (x (-5) 7 && x (-5) 11)
        have b8463 := hb (x (-6) 8 && x (-6) 12)
        have b8464 := hb (x (-7) 9 && x (-7) 13)
        clear * - r8450 e8451 e8452 b8453 b8454 b8455 b8456 b8457 b8458 b8459 b8460 b8461 b8462 b8463 b8464 g18 g14 d7894 g21 d8236 d7963 d7983 d8003 d8144 d8172 d8196
        omega
      have d8465 : (x (-6) 8).toNat = 1 := by
        have r8466 := hand1 (x (-6) 8) (x (-6) 12)
        have b8467 := hb (x (-6) 8)
        have b8468 := hb (x (-6) 8 && x (-6) 12)
        clear * - r8466 b8467 b8468 d8449
        omega
      have d8469 : (x (-7) 9).toNat = 0 := by
        have r8470 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8471 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e8472 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e8473 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e8474 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e8475 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e8476 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have b8477 := hb (x (-13) 7)
        have b8478 := hb (x (-12) 6)
        have b8479 := hb (x (-11) 5)
        have b8480 := hb (x (-10) 4)
        have b8481 := hb (x (-9) 11)
        have b8482 := hb (x (-8) 10)
        have b8483 := hb (x (-7) 9)
        have b8484 := hb (x (-6) 8)
        clear * - r8470 e8471 e8472 e8473 e8474 e8475 e8476 b8477 b8478 b8479 b8480 b8481 b8482 b8483 b8484 d8465 d8172 d8196
        omega
      have d8485 : (x (-10) 4).toNat = 0 := by
        have r8486 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8487 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e8488 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e8489 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e8490 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e8491 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e8492 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have b8493 := hb (x (-13) 7)
        have b8494 := hb (x (-12) 6)
        have b8495 := hb (x (-11) 5)
        have b8496 := hb (x (-10) 4)
        have b8497 := hb (x (-9) 11)
        have b8498 := hb (x (-8) 10)
        have b8499 := hb (x (-7) 9)
        have b8500 := hb (x (-6) 8)
        clear * - r8486 e8487 e8488 e8489 e8490 e8491 e8492 b8493 b8494 b8495 b8496 b8497 b8498 b8499 b8500 d8465 d8469 d8172 d8196
        omega
      have d8501 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
        have r8502 := hand1 (x (-10) 4) (x (-10) 14)
        have b8503 := hb (x (-10) 4)
        have b8504 := hb (x (-10) 4 && x (-10) 14)
        clear * - r8502 b8503 b8504 d8485
        omega
      have d8505 : (x (-10) 4 && x (-10) 13).toNat = 0 := by
        have r8506 := hand1 (x (-10) 4) (x (-10) 13)
        have b8507 := hb (x (-10) 4)
        have b8508 := hb (x (-10) 4 && x (-10) 13)
        clear * - r8506 b8507 b8508 d8485
        omega
      have d8509 : (x (-11) 5).toNat = 0 := by
        have r8510 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8511 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e8512 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e8513 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e8514 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e8515 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e8516 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have b8517 := hb (x (-13) 7)
        have b8518 := hb (x (-12) 6)
        have b8519 := hb (x (-11) 5)
        have b8520 := hb (x (-10) 4)
        have b8521 := hb (x (-9) 11)
        have b8522 := hb (x (-8) 10)
        have b8523 := hb (x (-7) 9)
        have b8524 := hb (x (-6) 8)
        clear * - r8510 e8511 e8512 e8513 e8514 e8515 e8516 b8517 b8518 b8519 b8520 b8521 b8522 b8523 b8524 d8465 d8469 d8172 d8196 d8485
        omega
      have d8525 : (x (-11) 5 && x (-11) 14).toNat = 0 := by
        have r8526 := hand1 (x (-11) 5) (x (-11) 14)
        have b8527 := hb (x (-11) 5)
        have b8528 := hb (x (-11) 5 && x (-11) 14)
        clear * - r8526 b8527 b8528 d8509
        omega
      have d8529 : (x (-12) 6).toNat = 0 := by
        have r8530 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8531 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e8532 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e8533 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e8534 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e8535 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e8536 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have b8537 := hb (x (-13) 7)
        have b8538 := hb (x (-12) 6)
        have b8539 := hb (x (-11) 5)
        have b8540 := hb (x (-10) 4)
        have b8541 := hb (x (-9) 11)
        have b8542 := hb (x (-8) 10)
        have b8543 := hb (x (-7) 9)
        have b8544 := hb (x (-6) 8)
        clear * - r8530 e8531 e8532 e8533 e8534 e8535 e8536 b8537 b8538 b8539 b8540 b8541 b8542 b8543 b8544 d8465 d8469 d8172 d8196 d8485 d8509
        omega
      have d8545 : (x (-5) 8).toNat = 0 := by
        have r8546 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8547 := hb (x (-11) 14)
        have b8548 := hb (x (-10) 13)
        have b8549 := hb (x (-9) 12)
        have b8550 := hb (x (-8) 11)
        have b8551 := hb (x (-7) 10)
        have b8552 := hb (x (-6) 9)
        have b8553 := hb (x (-5) 8)
        have b8554 := hb (x (-4) 7)
        have b8555 := hb (x (-3) 6)
        have b8556 := hb (x (-2) 5)
        have b8557 := hb (x (-1) 4)
        have b8558 := hb (x 0 3)
        have b8559 := hb (x 1 2)
        have b8560 := hb (x 2 1)
        clear * - r8546 b8547 b8548 b8549 b8550 b8551 b8552 b8553 b8554 b8555 b8556 b8557 b8558 b8559 b8560 d7686 g13 g9 d8081 d8361 d8417 d8433
        omega
      have d8561 : (x (-5) 1 && x (-5) 8).toNat = 0 := by
        have r8562 := hand2 (x (-5) 1) (x (-5) 8)
        have b8563 := hb (x (-5) 8)
        have b8564 := hb (x (-5) 1 && x (-5) 8)
        clear * - r8562 b8563 b8564 d8545
        omega
      have d8565 : (x (-6) 9).toNat = 0 := by
        have r8566 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8567 := hb (x (-11) 14)
        have b8568 := hb (x (-10) 13)
        have b8569 := hb (x (-9) 12)
        have b8570 := hb (x (-8) 11)
        have b8571 := hb (x (-7) 10)
        have b8572 := hb (x (-6) 9)
        have b8573 := hb (x (-5) 8)
        have b8574 := hb (x (-4) 7)
        have b8575 := hb (x (-3) 6)
        have b8576 := hb (x (-2) 5)
        have b8577 := hb (x (-1) 4)
        have b8578 := hb (x 0 3)
        have b8579 := hb (x 1 2)
        have b8580 := hb (x 2 1)
        clear * - r8566 b8567 b8568 b8569 b8570 b8571 b8572 b8573 b8574 b8575 b8576 b8577 b8578 b8579 b8580 d7686 g13 g9 d8081 d8361 d8417 d8433 d8545
        omega
      have d8581 : (x (-6) 2 && x (-6) 9).toNat = 0 := by
        have r8582 := hand2 (x (-6) 2) (x (-6) 9)
        have b8583 := hb (x (-6) 9)
        have b8584 := hb (x (-6) 2 && x (-6) 9)
        clear * - r8582 b8583 b8584 d8565
        omega
      have d8585 : (x (-7) 1 && x (-7) 10).toNat = 1 := by
        have r8586 : 1 ≤ (x (-6) 9).toNat + (x (-7) 1 && x (-7) 10).toNat + (x (-8) 2 && x (-8) 11).toNat + (x (-9) 3 && x (-9) 12).toNat + (x (-10) 4 && x (-10) 13).toNat + (x (-11) 5 && x (-11) 14).toNat + (x (-12) 6).toNat := by have q := hcov9 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8587 := hb (x (-12) 6)
        have b8588 := hb (x (-6) 9)
        have b8589 := hb (x (-7) 1 && x (-7) 10)
        have b8590 := hb (x (-8) 2 && x (-8) 11)
        have b8591 := hb (x (-9) 3 && x (-9) 12)
        have b8592 := hb (x (-10) 4 && x (-10) 13)
        have b8593 := hb (x (-11) 5 && x (-11) 14)
        clear * - r8586 b8587 b8588 b8589 b8590 b8591 b8592 b8593 d8565 d8168 d8192 d8505 d8525 d8529
        omega
      have d8594 : (x (-7) 10).toNat = 1 := by
        have r8595 := hand2 (x (-7) 1) (x (-7) 10)
        have b8596 := hb (x (-7) 10)
        have b8597 := hb (x (-7) 1 && x (-7) 10)
        clear * - r8595 b8596 b8597 d8585
        omega
      have d8598 : (x (-7) 2).toNat = 1 := by
        have r8599 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
        have b8600 := hb (x (-7) 2)
        have b8601 := hb (x (-7) 10)
        clear * - r8599 b8600 b8601 d8594
        omega
      have d8602 : (x (-7) 14).toNat = 1 := by
        have r8603 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
        have b8604 := hb (x (-7) 2)
        have b8605 := hb (x (-7) 14)
        clear * - r8603 b8604 b8605 d8598
        omega
      have d8606 : (x (-8) 1).toNat = 0 := by
        have r8607 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8608 := hb (x (-8) 1)
        have b8609 := hb (x (-7) 14)
        clear * - r8607 b8608 b8609 d8602
        omega
      have d8610 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
        have r8611 := hand1 (x (-8) 1) (x (-8) 14)
        have b8612 := hb (x (-8) 1)
        have b8613 := hb (x (-8) 1 && x (-8) 14)
        clear * - r8611 b8612 b8613 d8606
        omega
      have d8614 : (x (-9) 2).toNat = 1 := by
        have r8615 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8616 := hb (x (-9) 2)
        have b8617 := hb (x (-7) 13)
        have b8618 := hb (x (-8) 1 && x (-8) 14)
        clear * - r8615 b8616 b8617 b8618 d8132 d8610
        omega
      have d8619 : (x (-9) 14).toNat = 1 := by
        have r8620 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
        have b8621 := hb (x (-9) 2)
        have b8622 := hb (x (-9) 14)
        clear * - r8620 b8621 b8622 d8614
        omega
      have d8623 : (x (-10) 1).toNat = 0 := by
        have r8624 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8625 := hb (x (-10) 1)
        have b8626 := hb (x (-9) 14)
        clear * - r8624 b8625 b8626 d8619
        omega
      have d8627 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
        have r8628 := hand1 (x (-10) 1) (x (-10) 14)
        have b8629 := hb (x (-10) 1)
        have b8630 := hb (x (-10) 1 && x (-10) 14)
        clear * - r8628 b8629 b8630 d8623
        omega
      have d8631 : (x (-10) 13).toNat = 0 := by
        have r8632 : (x (-10) 13).toNat ≤ (x (-10) 1).toNat := himp _ _ (hp13 (-10))
        have b8633 := hb (x (-10) 1)
        have b8634 := hb (x (-10) 13)
        clear * - r8632 b8633 b8634 d8623
        omega
      have d8635 : (x (-10) 6 && x (-10) 13).toNat = 0 := by
        have r8636 := hand2 (x (-10) 6) (x (-10) 13)
        have b8637 := hb (x (-10) 13)
        have b8638 := hb (x (-10) 6 && x (-10) 13)
        clear * - r8636 b8637 b8638 d8631
        omega
      have d8639 : (x (-7) 12).toNat = 0 := by
        have r8640 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8641 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e8642 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b8643 := hb (x (-10) 3)
        have b8644 := hb (x (-9) 2)
        have b8645 := hb (x (-8) 13)
        have b8646 := hb (x (-7) 12)
        clear * - r8640 e8641 e8642 b8643 b8644 b8645 b8646 d8614
        omega
      have d8647 : (x (-7) 1 && x (-7) 12).toNat = 0 := by
        have r8648 := hand2 (x (-7) 1) (x (-7) 12)
        have b8649 := hb (x (-7) 12)
        have b8650 := hb (x (-7) 1 && x (-7) 12)
        clear * - r8648 b8649 b8650 d8639
        omega
      have d8651 : (x (-6) 11).toNat = 1 := by
        have r8652 : 1 ≤ (x (-6) 11).toNat + (x (-7) 1 && x (-7) 12).toNat + (x (-8) 2 && x (-8) 13).toNat + (x (-9) 3 && x (-9) 14).toNat + (x (-10) 4).toNat := by have q := hcov11 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8653 := hb (x (-10) 4)
        have b8654 := hb (x (-6) 11)
        have b8655 := hb (x (-7) 1 && x (-7) 12)
        have b8656 := hb (x (-8) 2 && x (-8) 13)
        have b8657 := hb (x (-9) 3 && x (-9) 14)
        clear * - r8652 b8653 b8654 b8655 b8656 b8657 d8647 d8160 d8184 d8485
        omega
      have d8658 : (x (-6) 3).toNat = 1 := by
        have r8659 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
        have b8660 := hb (x (-6) 3)
        have b8661 := hb (x (-6) 11)
        clear * - r8659 b8660 b8661 d8651
        omega
      have d8662 : (x (-3) 12).toNat = 0 := by
        have r8663 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8664 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e8665 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b8666 := hb (x (-6) 3)
        have b8667 := hb (x (-5) 2)
        have b8668 := hb (x (-4) 13)
        have b8669 := hb (x (-3) 12)
        clear * - r8663 e8664 e8665 b8666 b8667 b8668 b8669 d8658
        omega
      have d8670 : (x (-4) 13).toNat = 0 := by
        have r8671 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8672 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e8673 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b8674 := hb (x (-6) 3)
        have b8675 := hb (x (-5) 2)
        have b8676 := hb (x (-4) 13)
        have b8677 := hb (x (-3) 12)
        clear * - r8671 e8672 e8673 b8674 b8675 b8676 b8677 d8662 d8658
        omega
      have d8678 : (x (-5) 2).toNat = 0 := by
        have r8679 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8680 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e8681 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b8682 := hb (x (-6) 3)
        have b8683 := hb (x (-5) 2)
        have b8684 := hb (x (-4) 13)
        have b8685 := hb (x (-3) 12)
        clear * - r8679 e8680 e8681 b8682 b8683 b8684 b8685 d8662 d8670 d8658
        omega
      have d8686 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
        have r8687 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8688 := hb (x (-5) 2)
        have b8689 := hb (x (-3) 13)
        have b8690 := hb (x (-4) 1 && x (-4) 14)
        clear * - r8687 b8688 b8689 b8690 d7951 d8678
        omega
      have d8691 : (x (-4) 14).toNat = 1 := by
        have r8692 := hand2 (x (-4) 1) (x (-4) 14)
        have b8693 := hb (x (-4) 14)
        have b8694 := hb (x (-4) 1 && x (-4) 14)
        clear * - r8692 b8693 b8694 d8686
        omega
      have d8695 : (x (-5) 1).toNat = 0 := by
        have r8696 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8697 := hb (x (-5) 1)
        have b8698 := hb (x (-4) 14)
        clear * - r8696 b8697 b8698 d8691
        omega
      have d8699 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
        have r8700 := hand1 (x (-5) 1) (x (-5) 14)
        have b8701 := hb (x (-5) 1)
        have b8702 := hb (x (-5) 1 && x (-5) 14)
        clear * - r8700 b8701 b8702 d8695
        omega
      have d8703 : (x (-6) 2).toNat = 1 := by
        have r8704 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8705 := hb (x (-6) 2)
        have b8706 := hb (x (-4) 13)
        have b8707 := hb (x (-5) 1 && x (-5) 14)
        clear * - r8704 b8705 b8706 b8707 d8670 d8699
        omega
      have d8708 : (x (-6) 14).toNat = 1 := by
        have r8709 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
        have b8710 := hb (x (-6) 2)
        have b8711 := hb (x (-6) 14)
        clear * - r8709 b8710 b8711 d8703
        omega
      have d8712 : (x (-7) 1).toNat = 0 := by
        have r8713 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8714 := hb (x (-7) 1)
        have b8715 := hb (x (-6) 14)
        clear * - r8713 b8714 b8715 d8708
        omega
      have d8716 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
        have r8717 := hand1 (x (-7) 1) (x (-7) 14)
        have b8718 := hb (x (-7) 1)
        have b8719 := hb (x (-7) 1 && x (-7) 14)
        clear * - r8717 b8718 b8719 d8712
        omega
      have d8720 : (x (-6) 13).toNat = 1 := by
        have r8721 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8722 := hb (x (-8) 2)
        have b8723 := hb (x (-6) 13)
        have b8724 := hb (x (-7) 1 && x (-7) 14)
        clear * - r8721 b8722 b8723 b8724 d8716 d8152
        omega
      have d8725 : (x (-6) 1).toNat = 1 := by
        have r8726 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
        have b8727 := hb (x (-6) 1)
        have b8728 := hb (x (-6) 13)
        clear * - r8726 b8727 b8728 d8720
        omega
      have d8729 : (x (-5) 14).toNat = 0 := by
        have r8730 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8731 := hb (x (-6) 1)
        have b8732 := hb (x (-5) 14)
        clear * - r8730 b8731 b8732 d8725
        omega
      have d8733 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
        have r8734 := hand2 (x (-5) 4) (x (-5) 14)
        have b8735 := hb (x (-5) 14)
        have b8736 := hb (x (-5) 4 && x (-5) 14)
        clear * - r8734 b8735 b8736 d8729
        omega
      have d8737 : (x (-6) 5).toNat = 1 := by
        have r8738 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8739 := hb (x (-6) 5)
        have b8740 := hb (x (-1) 10)
        have b8741 := hb (x (-2) 1 && x (-2) 11)
        have b8742 := hb (x (-3) 2 && x (-3) 12)
        have b8743 := hb (x (-4) 3 && x (-4) 13)
        have b8744 := hb (x (-5) 4 && x (-5) 14)
        clear * - r8738 b8739 b8740 b8741 b8742 b8743 b8744 g6 g48 d8093 d8109 d8733
        omega
      have d8745 : (x (-1) 8).toNat = 0 := by
        have r8746 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8747 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e8748 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e8749 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e8750 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e8751 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e8752 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b8753 := hb (x (-8) 7)
        have b8754 := hb (x (-7) 6)
        have b8755 := hb (x (-6) 5)
        have b8756 := hb (x (-5) 4)
        have b8757 := hb (x (-4) 11)
        have b8758 := hb (x (-3) 10)
        have b8759 := hb (x (-2) 9)
        have b8760 := hb (x (-1) 8)
        clear * - r8746 e8747 e8748 e8749 e8750 e8751 e8752 b8753 b8754 b8755 b8756 b8757 b8758 b8759 b8760 d8097 d8113 d8737
        omega
      have d8761 : (x (-2) 9).toNat = 0 := by
        have r8762 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8763 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e8764 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e8765 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e8766 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e8767 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e8768 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b8769 := hb (x (-8) 7)
        have b8770 := hb (x (-7) 6)
        have b8771 := hb (x (-6) 5)
        have b8772 := hb (x (-5) 4)
        have b8773 := hb (x (-4) 11)
        have b8774 := hb (x (-3) 10)
        have b8775 := hb (x (-2) 9)
        have b8776 := hb (x (-1) 8)
        clear * - r8762 e8763 e8764 e8765 e8766 e8767 e8768 b8769 b8770 b8771 b8772 b8773 b8774 b8775 b8776 d8745 d8097 d8113 d8737
        omega
      have d8777 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
        have r8778 := hand2 (x (-2) 3) (x (-2) 9)
        have b8779 := hb (x (-2) 9)
        have b8780 := hb (x (-2) 3 && x (-2) 9)
        clear * - r8778 b8779 b8780 d8761
        omega
      have d8781 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
        have r8782 := hand1 (x (-7) 1) (x (-7) 11)
        have b8783 := hb (x (-7) 1)
        have b8784 := hb (x (-7) 1 && x (-7) 11)
        clear * - r8782 b8783 b8784 d8712
        omega
      have d8785 : (x (-6) 10).toNat = 1 := by
        have r8786 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8787 := hb (x (-11) 5)
        have b8788 := hb (x (-6) 10)
        have b8789 := hb (x (-7) 1 && x (-7) 11)
        have b8790 := hb (x (-8) 2 && x (-8) 12)
        have b8791 := hb (x (-9) 3 && x (-9) 13)
        have b8792 := hb (x (-10) 4 && x (-10) 14)
        clear * - r8786 b8787 b8788 b8789 b8790 b8791 b8792 d8781 d8164 d8188 d8501 d8509
        omega
      have d8793 : (x (-4) 8).toNat = 0 := by
        have r8794 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8795 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e8796 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e8797 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e8798 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e8799 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e8800 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b8801 := hb (x (-11) 7)
        have b8802 := hb (x (-10) 6)
        have b8803 := hb (x (-9) 5)
        have b8804 := hb (x (-8) 4)
        have b8805 := hb (x (-7) 11)
        have b8806 := hb (x (-6) 10)
        have b8807 := hb (x (-5) 9)
        have b8808 := hb (x (-4) 8)
        clear * - r8794 e8795 e8796 e8797 e8798 e8799 e8800 b8801 b8802 b8803 b8804 b8805 b8806 b8807 b8808 d8785
        omega
      have d8809 : (x (-5) 9).toNat = 0 := by
        have r8810 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8811 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e8812 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e8813 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e8814 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e8815 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e8816 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b8817 := hb (x (-11) 7)
        have b8818 := hb (x (-10) 6)
        have b8819 := hb (x (-9) 5)
        have b8820 := hb (x (-8) 4)
        have b8821 := hb (x (-7) 11)
        have b8822 := hb (x (-6) 10)
        have b8823 := hb (x (-5) 9)
        have b8824 := hb (x (-4) 8)
        clear * - r8810 e8811 e8812 e8813 e8814 e8815 e8816 b8817 b8818 b8819 b8820 b8821 b8822 b8823 b8824 d8793 d8785
        omega
      have d8825 : (x (-7) 11).toNat = 0 := by
        have r8826 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8827 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e8828 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e8829 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e8830 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e8831 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e8832 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b8833 := hb (x (-11) 7)
        have b8834 := hb (x (-10) 6)
        have b8835 := hb (x (-9) 5)
        have b8836 := hb (x (-8) 4)
        have b8837 := hb (x (-7) 11)
        have b8838 := hb (x (-6) 10)
        have b8839 := hb (x (-5) 9)
        have b8840 := hb (x (-4) 8)
        clear * - r8826 e8827 e8828 e8829 e8830 e8831 e8832 b8833 b8834 b8835 b8836 b8837 b8838 b8839 b8840 d8793 d8809 d8785
        omega
      have d8841 : (x (-8) 4).toNat = 0 := by
        have r8842 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8843 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e8844 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e8845 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e8846 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e8847 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e8848 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b8849 := hb (x (-11) 7)
        have b8850 := hb (x (-10) 6)
        have b8851 := hb (x (-9) 5)
        have b8852 := hb (x (-8) 4)
        have b8853 := hb (x (-7) 11)
        have b8854 := hb (x (-6) 10)
        have b8855 := hb (x (-5) 9)
        have b8856 := hb (x (-4) 8)
        clear * - r8842 e8843 e8844 e8845 e8846 e8847 e8848 b8849 b8850 b8851 b8852 b8853 b8854 b8855 b8856 d8793 d8809 d8785 d8825
        omega
      have d8857 : (x (-8) 4 && x (-8) 11).toNat = 0 := by
        have r8858 := hand1 (x (-8) 4) (x (-8) 11)
        have b8859 := hb (x (-8) 4)
        have b8860 := hb (x (-8) 4 && x (-8) 11)
        clear * - r8858 b8859 b8860 d8841
        omega
      have d8861 : (x (-8) 4 && x (-8) 9).toNat = 0 := by
        have r8862 := hand1 (x (-8) 4) (x (-8) 9)
        have b8863 := hb (x (-8) 4)
        have b8864 := hb (x (-8) 4 && x (-8) 9)
        clear * - r8862 b8863 b8864 d8841
        omega
      have d8865 : (x (-9) 5).toNat = 0 := by
        have r8866 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8867 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e8868 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e8869 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e8870 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e8871 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e8872 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b8873 := hb (x (-11) 7)
        have b8874 := hb (x (-10) 6)
        have b8875 := hb (x (-9) 5)
        have b8876 := hb (x (-8) 4)
        have b8877 := hb (x (-7) 11)
        have b8878 := hb (x (-6) 10)
        have b8879 := hb (x (-5) 9)
        have b8880 := hb (x (-4) 8)
        clear * - r8866 e8867 e8868 e8869 e8870 e8871 e8872 b8873 b8874 b8875 b8876 b8877 b8878 b8879 b8880 d8793 d8809 d8785 d8825 d8841
        omega
      have d8881 : (x (-9) 5 && x (-9) 12).toNat = 0 := by
        have r8882 := hand1 (x (-9) 5) (x (-9) 12)
        have b8883 := hb (x (-9) 5)
        have b8884 := hb (x (-9) 5 && x (-9) 12)
        clear * - r8882 b8883 b8884 d8865
        omega
      have d8885 : (x (-9) 5 && x (-9) 10).toNat = 0 := by
        have r8886 := hand1 (x (-9) 5) (x (-9) 10)
        have b8887 := hb (x (-9) 5)
        have b8888 := hb (x (-9) 5 && x (-9) 10)
        clear * - r8886 b8887 b8888 d8865
        omega
      have d8889 : (x (-10) 6).toNat = 0 := by
        have r8890 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8891 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e8892 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e8893 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e8894 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e8895 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e8896 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b8897 := hb (x (-11) 7)
        have b8898 := hb (x (-10) 6)
        have b8899 := hb (x (-9) 5)
        have b8900 := hb (x (-8) 4)
        have b8901 := hb (x (-7) 11)
        have b8902 := hb (x (-6) 10)
        have b8903 := hb (x (-5) 9)
        have b8904 := hb (x (-4) 8)
        clear * - r8890 e8891 e8892 e8893 e8894 e8895 e8896 b8897 b8898 b8899 b8900 b8901 b8902 b8903 b8904 d8793 d8809 d8785 d8825 d8841 d8865
        omega
      have d8905 : (x (-10) 6 && x (-10) 11).toNat = 0 := by
        have r8906 := hand1 (x (-10) 6) (x (-10) 11)
        have b8907 := hb (x (-10) 6)
        have b8908 := hb (x (-10) 6 && x (-10) 11)
        clear * - r8906 b8907 b8908 d8889
        omega
      have d8909 : (x (-11) 7).toNat = 0 := by
        have r8910 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8911 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e8912 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e8913 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e8914 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e8915 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e8916 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b8917 := hb (x (-11) 7)
        have b8918 := hb (x (-10) 6)
        have b8919 := hb (x (-9) 5)
        have b8920 := hb (x (-8) 4)
        have b8921 := hb (x (-7) 11)
        have b8922 := hb (x (-6) 10)
        have b8923 := hb (x (-5) 9)
        have b8924 := hb (x (-4) 8)
        clear * - r8910 e8911 e8912 e8913 e8914 e8915 e8916 b8917 b8918 b8919 b8920 b8921 b8922 b8923 b8924 d8793 d8809 d8785 d8825 d8841 d8865 d8889
        omega
      have d8925 : (x (-11) 7 && x (-11) 14).toNat = 0 := by
        have r8926 := hand1 (x (-11) 7) (x (-11) 14)
        have b8927 := hb (x (-11) 7)
        have b8928 := hb (x (-11) 7 && x (-11) 14)
        clear * - r8926 b8927 b8928 d8909
        omega
      have d8929 : (x (-11) 7 && x (-11) 12).toNat = 0 := by
        have r8930 := hand1 (x (-11) 7) (x (-11) 12)
        have b8931 := hb (x (-11) 7)
        have b8932 := hb (x (-11) 7 && x (-11) 12)
        clear * - r8930 b8931 b8932 d8909
        omega
      have d8933 : (x (-4) 12).toNat = 0 := by
        have r8934 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8935 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e8936 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b8937 := hb (x (-7) 3)
        have b8938 := hb (x (-6) 2)
        have b8939 := hb (x (-5) 13)
        have b8940 := hb (x (-4) 12)
        clear * - r8934 e8935 e8936 b8937 b8938 b8939 b8940 d8703
        omega
      have d8941 : (x (-5) 13).toNat = 0 := by
        have r8942 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8943 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e8944 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b8945 := hb (x (-7) 3)
        have b8946 := hb (x (-6) 2)
        have b8947 := hb (x (-5) 13)
        have b8948 := hb (x (-4) 12)
        clear * - r8942 e8943 e8944 b8945 b8946 b8947 b8948 d8933 d8703
        omega
      have d8949 : (x (-7) 3).toNat = 0 := by
        have r8950 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8951 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e8952 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b8953 := hb (x (-7) 3)
        have b8954 := hb (x (-6) 2)
        have b8955 := hb (x (-5) 13)
        have b8956 := hb (x (-4) 12)
        clear * - r8950 e8951 e8952 b8953 b8954 b8955 b8956 d8933 d8941 d8703
        omega
      have d8957 : (x (-7) 3 && x (-7) 10).toNat = 0 := by
        have r8958 := hand1 (x (-7) 3) (x (-7) 10)
        have b8959 := hb (x (-7) 3)
        have b8960 := hb (x (-7) 3 && x (-7) 10)
        clear * - r8958 b8959 b8960 d8949
        omega
      have d8961 : (x (-12) 8).toNat = 1 := by
        have r8962 : 1 ≤ (x (-4) 7).toNat + (x (-5) 1 && x (-5) 8).toNat + (x (-6) 2 && x (-6) 9).toNat + (x (-7) 3 && x (-7) 10).toNat + (x (-8) 4 && x (-8) 11).toNat + (x (-9) 5 && x (-9) 12).toNat + (x (-10) 6 && x (-10) 13).toNat + (x (-11) 7 && x (-11) 14).toNat + (x (-12) 8).toNat := by have q := hcov7 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8963 := hb (x (-12) 8)
        have b8964 := hb (x (-4) 7)
        have b8965 := hb (x (-5) 1 && x (-5) 8)
        have b8966 := hb (x (-6) 2 && x (-6) 9)
        have b8967 := hb (x (-7) 3 && x (-7) 10)
        have b8968 := hb (x (-8) 4 && x (-8) 11)
        have b8969 := hb (x (-9) 5 && x (-9) 12)
        have b8970 := hb (x (-10) 6 && x (-10) 13)
        have b8971 := hb (x (-11) 7 && x (-11) 14)
        clear * - r8962 b8963 b8964 b8965 b8966 b8967 b8968 b8969 b8970 b8971 d8433 d8561 d8581 d8957 d8857 d8881 d8635 d8925
        omega
      have d8972 : (x (-13) 9).toNat = 0 := by
        have r8973 : (x (-12) 8).toNat + (x (-13) 1 && x (-13) 9).toNat + (x (-14) 2 && x (-14) 10).toNat + (x (-15) 3 && x (-15) 11).toNat + (x (-16) 4 && x (-16) 12).toNat + (x (-17) 5 && x (-17) 13).toNat + (x (-18) 6 && x (-18) 14).toNat + (x (-19) 7).toNat = 1 := by have q := hd8 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8974 : (x (-13) 1 && x (-13) 9).toNat = (x (-13) 9).toNat := handr _ _ (fun h => hp9 (-13) (h))
        have e8975 : (x (-14) 2 && x (-14) 10).toNat = (x (-14) 10).toNat := handr _ _ (fun h => hp10 (-14) (h))
        have e8976 : (x (-15) 3 && x (-15) 11).toNat = (x (-15) 11).toNat := handr _ _ (fun h => hp11 (-15) (h))
        have e8977 : (x (-16) 4 && x (-16) 12).toNat = (x (-16) 4).toNat := handl _ _ (fun h => hp4 (-16) (h))
        have e8978 : (x (-17) 5 && x (-17) 13).toNat = (x (-17) 5).toNat := handl _ _ (fun h => hp5 (-17) (h))
        have e8979 : (x (-18) 6 && x (-18) 14).toNat = (x (-18) 6).toNat := handl _ _ (fun h => hp6 (-18) (h))
        have b8980 := hb (x (-19) 7)
        have b8981 := hb (x (-18) 6)
        have b8982 := hb (x (-17) 5)
        have b8983 := hb (x (-16) 4)
        have b8984 := hb (x (-15) 11)
        have b8985 := hb (x (-14) 10)
        have b8986 := hb (x (-13) 9)
        have b8987 := hb (x (-12) 8)
        clear * - r8973 e8974 e8975 e8976 e8977 e8978 e8979 b8980 b8981 b8982 b8983 b8984 b8985 b8986 b8987 d8961
        omega
      have d8988 : (x (-13) 9 && x (-13) 14).toNat = 0 := by
        have r8989 := hand1 (x (-13) 9) (x (-13) 14)
        have b8990 := hb (x (-13) 9)
        have b8991 := hb (x (-13) 9 && x (-13) 14)
        clear * - r8989 b8990 b8991 d8972
        omega
      have d8992 : (x (-14) 10).toNat = 0 := by
        have r8993 : (x (-12) 8).toNat + (x (-13) 1 && x (-13) 9).toNat + (x (-14) 2 && x (-14) 10).toNat + (x (-15) 3 && x (-15) 11).toNat + (x (-16) 4 && x (-16) 12).toNat + (x (-17) 5 && x (-17) 13).toNat + (x (-18) 6 && x (-18) 14).toNat + (x (-19) 7).toNat = 1 := by have q := hd8 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8994 : (x (-13) 1 && x (-13) 9).toNat = (x (-13) 9).toNat := handr _ _ (fun h => hp9 (-13) (h))
        have e8995 : (x (-14) 2 && x (-14) 10).toNat = (x (-14) 10).toNat := handr _ _ (fun h => hp10 (-14) (h))
        have e8996 : (x (-15) 3 && x (-15) 11).toNat = (x (-15) 11).toNat := handr _ _ (fun h => hp11 (-15) (h))
        have e8997 : (x (-16) 4 && x (-16) 12).toNat = (x (-16) 4).toNat := handl _ _ (fun h => hp4 (-16) (h))
        have e8998 : (x (-17) 5 && x (-17) 13).toNat = (x (-17) 5).toNat := handl _ _ (fun h => hp5 (-17) (h))
        have e8999 : (x (-18) 6 && x (-18) 14).toNat = (x (-18) 6).toNat := handl _ _ (fun h => hp6 (-18) (h))
        have b9000 := hb (x (-19) 7)
        have b9001 := hb (x (-18) 6)
        have b9002 := hb (x (-17) 5)
        have b9003 := hb (x (-16) 4)
        have b9004 := hb (x (-15) 11)
        have b9005 := hb (x (-14) 10)
        have b9006 := hb (x (-13) 9)
        have b9007 := hb (x (-12) 8)
        clear * - r8993 e8994 e8995 e8996 e8997 e8998 e8999 b9000 b9001 b9002 b9003 b9004 b9005 b9006 b9007 d8961 d8972
        omega
      have d9008 : (x (-15) 11).toNat = 0 := by
        have r9009 : (x (-12) 8).toNat + (x (-13) 1 && x (-13) 9).toNat + (x (-14) 2 && x (-14) 10).toNat + (x (-15) 3 && x (-15) 11).toNat + (x (-16) 4 && x (-16) 12).toNat + (x (-17) 5 && x (-17) 13).toNat + (x (-18) 6 && x (-18) 14).toNat + (x (-19) 7).toNat = 1 := by have q := hd8 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9010 : (x (-13) 1 && x (-13) 9).toNat = (x (-13) 9).toNat := handr _ _ (fun h => hp9 (-13) (h))
        have e9011 : (x (-14) 2 && x (-14) 10).toNat = (x (-14) 10).toNat := handr _ _ (fun h => hp10 (-14) (h))
        have e9012 : (x (-15) 3 && x (-15) 11).toNat = (x (-15) 11).toNat := handr _ _ (fun h => hp11 (-15) (h))
        have e9013 : (x (-16) 4 && x (-16) 12).toNat = (x (-16) 4).toNat := handl _ _ (fun h => hp4 (-16) (h))
        have e9014 : (x (-17) 5 && x (-17) 13).toNat = (x (-17) 5).toNat := handl _ _ (fun h => hp5 (-17) (h))
        have e9015 : (x (-18) 6 && x (-18) 14).toNat = (x (-18) 6).toNat := handl _ _ (fun h => hp6 (-18) (h))
        have b9016 := hb (x (-19) 7)
        have b9017 := hb (x (-18) 6)
        have b9018 := hb (x (-17) 5)
        have b9019 := hb (x (-16) 4)
        have b9020 := hb (x (-15) 11)
        have b9021 := hb (x (-14) 10)
        have b9022 := hb (x (-13) 9)
        have b9023 := hb (x (-12) 8)
        clear * - r9009 e9010 e9011 e9012 e9013 e9014 e9015 b9016 b9017 b9018 b9019 b9020 b9021 b9022 b9023 d8961 d8972 d8992
        omega
      have d9024 : (x (-16) 4).toNat = 0 := by
        have r9025 : (x (-12) 8).toNat + (x (-13) 1 && x (-13) 9).toNat + (x (-14) 2 && x (-14) 10).toNat + (x (-15) 3 && x (-15) 11).toNat + (x (-16) 4 && x (-16) 12).toNat + (x (-17) 5 && x (-17) 13).toNat + (x (-18) 6 && x (-18) 14).toNat + (x (-19) 7).toNat = 1 := by have q := hd8 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9026 : (x (-13) 1 && x (-13) 9).toNat = (x (-13) 9).toNat := handr _ _ (fun h => hp9 (-13) (h))
        have e9027 : (x (-14) 2 && x (-14) 10).toNat = (x (-14) 10).toNat := handr _ _ (fun h => hp10 (-14) (h))
        have e9028 : (x (-15) 3 && x (-15) 11).toNat = (x (-15) 11).toNat := handr _ _ (fun h => hp11 (-15) (h))
        have e9029 : (x (-16) 4 && x (-16) 12).toNat = (x (-16) 4).toNat := handl _ _ (fun h => hp4 (-16) (h))
        have e9030 : (x (-17) 5 && x (-17) 13).toNat = (x (-17) 5).toNat := handl _ _ (fun h => hp5 (-17) (h))
        have e9031 : (x (-18) 6 && x (-18) 14).toNat = (x (-18) 6).toNat := handl _ _ (fun h => hp6 (-18) (h))
        have b9032 := hb (x (-19) 7)
        have b9033 := hb (x (-18) 6)
        have b9034 := hb (x (-17) 5)
        have b9035 := hb (x (-16) 4)
        have b9036 := hb (x (-15) 11)
        have b9037 := hb (x (-14) 10)
        have b9038 := hb (x (-13) 9)
        have b9039 := hb (x (-12) 8)
        clear * - r9025 e9026 e9027 e9028 e9029 e9030 e9031 b9032 b9033 b9034 b9035 b9036 b9037 b9038 b9039 d8961 d8972 d8992 d9008
        omega
      have d9040 : (x (-7) 3 && x (-7) 8).toNat = 0 := by
        have r9041 := hand1 (x (-7) 3) (x (-7) 8)
        have b9042 := hb (x (-7) 3)
        have b9043 := hb (x (-7) 3 && x (-7) 8)
        clear * - r9041 b9042 b9043 d8949
        omega
      have d9044 : (x (-12) 8 && x (-12) 13).toNat = 1 := by
        have r9045 : 1 ≤ (x (-4) 5).toNat + (x (-5) 1 && x (-5) 6).toNat + (x (-6) 2 && x (-6) 7).toNat + (x (-7) 3 && x (-7) 8).toNat + (x (-8) 4 && x (-8) 9).toNat + (x (-9) 5 && x (-9) 10).toNat + (x (-10) 6 && x (-10) 11).toNat + (x (-11) 7 && x (-11) 12).toNat + (x (-12) 8 && x (-12) 13).toNat + (x (-13) 9 && x (-13) 14).toNat + (x (-14) 10).toNat := by have q := hcov5 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9046 := hb (x (-14) 10)
        have b9047 := hb (x (-4) 5)
        have b9048 := hb (x (-5) 1 && x (-5) 6)
        have b9049 := hb (x (-6) 2 && x (-6) 7)
        have b9050 := hb (x (-7) 3 && x (-7) 8)
        have b9051 := hb (x (-8) 4 && x (-8) 9)
        have b9052 := hb (x (-9) 5 && x (-9) 10)
        have b9053 := hb (x (-10) 6 && x (-10) 11)
        have b9054 := hb (x (-11) 7 && x (-11) 12)
        have b9055 := hb (x (-12) 8 && x (-12) 13)
        have b9056 := hb (x (-13) 9 && x (-13) 14)
        clear * - r9045 b9046 b9047 b9048 b9049 b9050 b9051 b9052 b9053 b9054 b9055 b9056 g1 g25 g26 d9040 d8861 d8885 d8905 d8929 d8988 d8992
        omega
      have d9057 : (x (-12) 13).toNat = 1 := by
        have r9058 := hand2 (x (-12) 8) (x (-12) 13)
        have b9059 := hb (x (-12) 13)
        have b9060 := hb (x (-12) 8 && x (-12) 13)
        clear * - r9058 b9059 b9060 d9044
        omega
      have d9061 : (x (-12) 1).toNat = 1 := by
        have r9062 : (x (-12) 13).toNat ≤ (x (-12) 1).toNat := himp _ _ (hp13 (-12))
        have b9063 := hb (x (-12) 1)
        have b9064 := hb (x (-12) 13)
        clear * - r9062 b9063 b9064 d9057
        omega
      have d9065 : (x (-11) 14).toNat = 0 := by
        have r9066 : (x (-11) 14).toNat + (x (-12) 1).toNat = 1 := by have q := hd14 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9067 := hb (x (-12) 1)
        have b9068 := hb (x (-11) 14)
        clear * - r9066 b9067 b9068 d9061
        omega
      have d9069 : (x (-11) 1 && x (-11) 14).toNat = 0 := by
        have r9070 := hand2 (x (-11) 1) (x (-11) 14)
        have b9071 := hb (x (-11) 14)
        have b9072 := hb (x (-11) 1 && x (-11) 14)
        clear * - r9070 b9071 b9072 d9065
        omega
      have d9073 : (x (-12) 2).toNat = 1 := by
        have r9074 : 1 ≤ (x (-10) 13).toNat + (x (-11) 1 && x (-11) 14).toNat + (x (-12) 2).toNat := by have q := hcov13 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9075 := hb (x (-12) 2)
        have b9076 := hb (x (-10) 13)
        have b9077 := hb (x (-11) 1 && x (-11) 14)
        clear * - r9074 b9075 b9076 b9077 d8631 d9069
        omega
      have d9078 : (x (-12) 14).toNat = 1 := by
        have r9079 : (x (-12) 2).toNat ≤ (x (-12) 14).toNat := himp _ _ (hp2 (-12))
        have b9080 := hb (x (-12) 2)
        have b9081 := hb (x (-12) 14)
        clear * - r9079 b9080 b9081 d9073
        omega
      have d9082 : (x (-13) 1).toNat = 0 := by
        have r9083 : (x (-12) 14).toNat + (x (-13) 1).toNat = 1 := by have q := hd14 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9084 := hb (x (-13) 1)
        have b9085 := hb (x (-12) 14)
        clear * - r9083 b9084 b9085 d9078
        omega
      have d9086 : (x (-13) 1 && x (-13) 12).toNat = 0 := by
        have r9087 := hand1 (x (-13) 1) (x (-13) 12)
        have b9088 := hb (x (-13) 1)
        have b9089 := hb (x (-13) 1 && x (-13) 12)
        clear * - r9087 b9088 b9089 d9082
        omega
      have d9090 : (x (-13) 13).toNat = 0 := by
        have r9091 : (x (-13) 13).toNat ≤ (x (-13) 1).toNat := himp _ _ (hp13 (-13))
        have b9092 := hb (x (-13) 1)
        have b9093 := hb (x (-13) 13)
        clear * - r9091 b9092 b9093 d9082
        omega
      have d9094 : (x (-13) 5).toNat = 0 := by
        have r9095 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
        have b9096 := hb (x (-13) 5)
        have b9097 := hb (x (-13) 13)
        clear * - r9095 b9096 b9097 d9090
        omega
      have d9098 : (x (-10) 12).toNat = 0 := by
        have r9099 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9100 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
        have e9101 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
        have b9102 := hb (x (-13) 3)
        have b9103 := hb (x (-12) 2)
        have b9104 := hb (x (-11) 13)
        have b9105 := hb (x (-10) 12)
        clear * - r9099 e9100 e9101 b9102 b9103 b9104 b9105 d9073
        omega
      have d9106 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
        have r9107 := hand2 (x (-10) 2) (x (-10) 12)
        have b9108 := hb (x (-10) 12)
        have b9109 := hb (x (-10) 2 && x (-10) 12)
        clear * - r9107 b9108 b9109 d9098
        omega
      have d9110 : (x (-11) 13).toNat = 0 := by
        have r9111 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9112 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
        have e9113 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
        have b9114 := hb (x (-13) 3)
        have b9115 := hb (x (-12) 2)
        have b9116 := hb (x (-11) 13)
        have b9117 := hb (x (-10) 12)
        clear * - r9111 e9112 e9113 b9114 b9115 b9116 b9117 d9098 d9073
        omega
      have d9118 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
        have r9119 := hand2 (x (-11) 3) (x (-11) 13)
        have b9120 := hb (x (-11) 13)
        have b9121 := hb (x (-11) 3 && x (-11) 13)
        clear * - r9119 b9120 b9121 d9110
        omega
      have d9122 : (x (-12) 4 && x (-12) 14).toNat = 1 := by
        have r9123 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9124 := hb (x (-13) 5)
        have b9125 := hb (x (-8) 10)
        have b9126 := hb (x (-9) 1 && x (-9) 11)
        have b9127 := hb (x (-10) 2 && x (-10) 12)
        have b9128 := hb (x (-11) 3 && x (-11) 13)
        have b9129 := hb (x (-12) 4 && x (-12) 14)
        clear * - r9123 b9124 b9125 b9126 b9127 b9128 b9129 d8172 d8200 d9106 d9118 d9094
        omega
      have d9130 : (x (-12) 4).toNat = 1 := by
        have r9131 := hand1 (x (-12) 4) (x (-12) 14)
        have b9132 := hb (x (-12) 4)
        have b9133 := hb (x (-12) 4 && x (-12) 14)
        clear * - r9131 b9132 b9133 d9122
        omega
      have d9134 : (x (-12) 12).toNat = 1 := by
        have r9135 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
        have b9136 := hb (x (-12) 4)
        have b9137 := hb (x (-12) 12)
        clear * - r9135 b9136 b9137 d9130
        omega
      have d9138 : (x (-14) 2).toNat = 0 := by
        have r9139 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9140 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
        have e9141 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
        have b9142 := hb (x (-15) 3)
        have b9143 := hb (x (-14) 2)
        have b9144 := hb (x (-13) 13)
        have b9145 := hb (x (-12) 12)
        clear * - r9139 e9140 e9141 b9142 b9143 b9144 b9145 d9134 d9090
        omega
      have d9146 : (x (-14) 2 && x (-14) 13).toNat = 0 := by
        have r9147 := hand1 (x (-14) 2) (x (-14) 13)
        have b9148 := hb (x (-14) 2)
        have b9149 := hb (x (-14) 2 && x (-14) 13)
        clear * - r9147 b9148 b9149 d9138
        omega
      have d9150 : (x (-15) 3).toNat = 0 := by
        have r9151 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9152 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
        have e9153 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
        have b9154 := hb (x (-15) 3)
        have b9155 := hb (x (-14) 2)
        have b9156 := hb (x (-13) 13)
        have b9157 := hb (x (-12) 12)
        clear * - r9151 e9152 e9153 b9154 b9155 b9156 b9157 d9134 d9090 d9138
        omega
      have d9158 : (x (-15) 3 && x (-15) 14).toNat = 0 := by
        have r9159 := hand1 (x (-15) 3) (x (-15) 14)
        have b9160 := hb (x (-15) 3)
        have b9161 := hb (x (-15) 3 && x (-15) 14)
        clear * - r9159 b9160 b9161 d9150
        omega
      have d9162 : (x (-12) 11).toNat = 1 := by
        have r9163 : 1 ≤ (x (-12) 11).toNat + (x (-13) 1 && x (-13) 12).toNat + (x (-14) 2 && x (-14) 13).toNat + (x (-15) 3 && x (-15) 14).toNat + (x (-16) 4).toNat := by have q := hcov11 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9164 := hb (x (-16) 4)
        have b9165 := hb (x (-12) 11)
        have b9166 := hb (x (-13) 1 && x (-13) 12)
        have b9167 := hb (x (-14) 2 && x (-14) 13)
        have b9168 := hb (x (-15) 3 && x (-15) 14)
        clear * - r9163 b9164 b9165 b9166 b9167 b9168 d9086 d9146 d9158 d9024
        omega
      have d9169 : (x (-12) 3).toNat = 1 := by
        have r9170 : (x (-12) 11).toNat ≤ (x (-12) 3).toNat := himp _ _ (hp11 (-12))
        have b9171 := hb (x (-12) 3)
        have b9172 := hb (x (-12) 11)
        clear * - r9170 b9171 b9172 d9162
        omega
      have d9173 : (x (-9) 12).toNat = 0 := by
        have r9174 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9175 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
        have e9176 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
        have b9177 := hb (x (-12) 3)
        have b9178 := hb (x (-11) 2)
        have b9179 := hb (x (-10) 13)
        have b9180 := hb (x (-9) 12)
        clear * - r9174 e9175 e9176 b9177 b9178 b9179 b9180 d8631 d9169
        omega
      have d9181 : (x (-11) 2).toNat = 0 := by
        have r9182 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9183 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
        have e9184 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
        have b9185 := hb (x (-12) 3)
        have b9186 := hb (x (-11) 2)
        have b9187 := hb (x (-10) 13)
        have b9188 := hb (x (-9) 12)
        clear * - r9182 e9183 e9184 b9185 b9186 b9187 b9188 d9173 d8631 d9169
        omega
      have d9189 : (x (-9) 13).toNat = 1 := by
        have r9190 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9191 := hb (x (-11) 2)
        have b9192 := hb (x (-9) 13)
        have b9193 := hb (x (-10) 1 && x (-10) 14)
        clear * - r9190 b9191 b9192 b9193 d8627 d9181
        omega
      have d9194 : (x (-9) 1).toNat = 1 := by
        have r9195 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
        have b9196 := hb (x (-9) 1)
        have b9197 := hb (x (-9) 13)
        clear * - r9195 b9196 b9197 d9189
        omega
      have d9198 : (x (-8) 14).toNat = 0 := by
        have r9199 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9200 := hb (x (-9) 1)
        have b9201 := hb (x (-8) 14)
        clear * - r9199 b9200 b9201 d9194
        omega
      have d9202 : (x (-8) 9 && x (-8) 14).toNat = 0 := by
        have r9203 := hand2 (x (-8) 9) (x (-8) 14)
        have b9204 := hb (x (-8) 14)
        have b9205 := hb (x (-8) 9 && x (-8) 14)
        clear * - r9203 b9204 b9205 d9198
        omega
      have d9206 : (x (-9) 10).toNat = 1 := by
        have r9207 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9208 := hb (x (-9) 10)
        have b9209 := hb (x 1 5)
        have b9210 := hb (x 0 1 && x 0 6)
        have b9211 := hb (x (-1) 2 && x (-1) 7)
        have b9212 := hb (x (-2) 3 && x (-2) 8)
        have b9213 := hb (x (-3) 4 && x (-3) 9)
        have b9214 := hb (x (-4) 5 && x (-4) 10)
        have b9215 := hb (x (-5) 6 && x (-5) 11)
        have b9216 := hb (x (-6) 7 && x (-6) 12)
        have b9217 := hb (x (-7) 8 && x (-7) 13)
        have b9218 := hb (x (-8) 9 && x (-8) 14)
        clear * - r9207 b9208 b9209 b9210 b9211 b9212 b9213 b9214 b9215 b9216 b9217 b9218 g14 d7890 d7918 d8232 g27 g28 g29 g30 d8140 d9202
        omega
      have d9219 : (x (-7) 8).toNat = 0 := by
        have r9220 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9221 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e9222 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e9223 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e9224 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e9225 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e9226 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b9227 := hb (x (-14) 7)
        have b9228 := hb (x (-13) 6)
        have b9229 := hb (x (-12) 5)
        have b9230 := hb (x (-11) 4)
        have b9231 := hb (x (-10) 11)
        have b9232 := hb (x (-9) 10)
        have b9233 := hb (x (-8) 9)
        have b9234 := hb (x (-7) 8)
        clear * - r9220 e9221 e9222 e9223 e9224 e9225 e9226 b9227 b9228 b9229 b9230 b9231 b9232 b9233 b9234 d9206
        omega
      have d9235 : (x (-7) 8 && x (-7) 14).toNat = 0 := by
        have r9236 := hand1 (x (-7) 8) (x (-7) 14)
        have b9237 := hb (x (-7) 8)
        have b9238 := hb (x (-7) 8 && x (-7) 14)
        clear * - r9236 b9237 b9238 d9219
        omega
      have d9239 : (x (-8) 9).toNat = 1 := by
        have r9240 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9241 := hb (x (-8) 9)
        have b9242 := hb (x 1 6)
        have b9243 := hb (x 0 1 && x 0 7)
        have b9244 := hb (x (-1) 2 && x (-1) 8)
        have b9245 := hb (x (-2) 3 && x (-2) 9)
        have b9246 := hb (x (-3) 4 && x (-3) 10)
        have b9247 := hb (x (-4) 5 && x (-4) 11)
        have b9248 := hb (x (-5) 6 && x (-5) 12)
        have b9249 := hb (x (-6) 7 && x (-6) 13)
        have b9250 := hb (x (-7) 8 && x (-7) 14)
        clear * - r9240 b9241 b9242 b9243 b9244 b9245 b9246 b9247 b9248 b9249 b9250 g15 d7830 d8069 d8777 g33 g34 g35 g36 d9235
        omega
      have r9251 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9252 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e9253 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e9254 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e9255 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e9256 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e9257 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have b9258 := hb (x (-14) 7)
      have b9259 := hb (x (-13) 6)
      have b9260 := hb (x (-12) 5)
      have b9261 := hb (x (-11) 4)
      have b9262 := hb (x (-10) 11)
      have b9263 := hb (x (-9) 10)
      have b9264 := hb (x (-8) 9)
      have b9265 := hb (x (-7) 8)
      linarith only [r9251, e9252, e9253, e9254, e9255, e9256, e9257, b9258, b9259, b9260, b9261, b9262, b9263, b9264, b9265, d9219, d9239, d9206]
    · have f9266 : (x 0 10).toNat = 1 := by rw [h7932]; rfl
      have d9267 : (x 2 8).toNat = 0 := by
        have r9268 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9269 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e9270 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e9271 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e9272 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e9273 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e9274 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b9275 := hb (x (-5) 7)
        have b9276 := hb (x (-4) 6)
        have b9277 := hb (x (-3) 5)
        have b9278 := hb (x (-2) 4)
        have b9279 := hb (x (-1) 11)
        have b9280 := hb (x 0 10)
        have b9281 := hb (x 1 9)
        have b9282 := hb (x 2 8)
        clear * - r9268 e9269 e9270 e9271 e9272 e9273 e9274 b9275 b9276 b9277 b9278 b9279 b9280 b9281 b9282 d7682 f9266 g7
        omega
      have d9283 : (x (-2) 4).toNat = 0 := by
        have r9284 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9285 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e9286 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e9287 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e9288 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e9289 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e9290 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b9291 := hb (x (-5) 7)
        have b9292 := hb (x (-4) 6)
        have b9293 := hb (x (-3) 5)
        have b9294 := hb (x (-2) 4)
        have b9295 := hb (x (-1) 11)
        have b9296 := hb (x 0 10)
        have b9297 := hb (x 1 9)
        have b9298 := hb (x 2 8)
        clear * - r9284 e9285 e9286 e9287 e9288 e9289 e9290 b9291 b9292 b9293 b9294 b9295 b9296 b9297 b9298 d9267 d7682 f9266 g7
        omega
      have d9299 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
        have r9300 := hand1 (x (-2) 4) (x (-2) 14)
        have b9301 := hb (x (-2) 4)
        have b9302 := hb (x (-2) 4 && x (-2) 14)
        clear * - r9300 b9301 b9302 d9283
        omega
      have d9303 : (x (-3) 5).toNat = 0 := by
        have r9304 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9305 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e9306 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e9307 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e9308 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e9309 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e9310 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b9311 := hb (x (-5) 7)
        have b9312 := hb (x (-4) 6)
        have b9313 := hb (x (-3) 5)
        have b9314 := hb (x (-2) 4)
        have b9315 := hb (x (-1) 11)
        have b9316 := hb (x 0 10)
        have b9317 := hb (x 1 9)
        have b9318 := hb (x 2 8)
        clear * - r9304 e9305 e9306 e9307 e9308 e9309 e9310 b9311 b9312 b9313 b9314 b9315 b9316 b9317 b9318 d9267 d7682 f9266 g7 d9283
        omega
      have d9319 : (x 2 10).toNat = 1 := by
        have r9320 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9321 := hb (x (-3) 5)
        have b9322 := hb (x 2 10)
        have b9323 := hb (x 1 1 && x 1 11)
        have b9324 := hb (x 0 2 && x 0 12)
        have b9325 := hb (x (-1) 3 && x (-1) 13)
        have b9326 := hb (x (-2) 4 && x (-2) 14)
        clear * - r9320 b9321 b9322 b9323 b9324 b9325 b9326 d7678 d7928 g50 d9299 d9303
        omega
      have d9327 : (x 2 2).toNat = 1 := by
        have r9328 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
        have b9329 := hb (x 2 2)
        have b9330 := hb (x 2 10)
        clear * - r9328 b9329 b9330 d9319
        omega
      have d9331 : (x 4 12).toNat = 0 := by
        have r9332 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9333 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e9334 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b9335 := hb (x 1 3)
        have b9336 := hb (x 2 2)
        have b9337 := hb (x 3 13)
        have b9338 := hb (x 4 12)
        clear * - r9332 e9333 e9334 b9335 b9336 b9337 b9338 d7637 d9327
        omega
      have d9339 : (x 4 2 && x 4 12).toNat = 0 := by
        have r9340 := hand2 (x 4 2) (x 4 12)
        have b9341 := hb (x 4 12)
        have b9342 := hb (x 4 2 && x 4 12)
        clear * - r9340 b9341 b9342 d9331
        omega
      have d9343 : (x 4 3 && x 4 12).toNat = 0 := by
        have r9344 := hand2 (x 4 3) (x 4 12)
        have b9345 := hb (x 4 12)
        have b9346 := hb (x 4 3 && x 4 12)
        clear * - r9344 b9345 b9346 d9331
        omega
      have d9347 : (x 4 4).toNat = 0 := by
        have r9348 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b9349 := hb (x 4 4)
        have b9350 := hb (x 4 12)
        clear * - r9348 b9349 b9350 d9331
        omega
      have d9351 : (x 8 11).toNat = 1 := by
        have r9352 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9353 := hb (x 4 4)
        have b9354 := hb (x 8 11)
        have b9355 := hb (x 7 1 && x 7 12)
        have b9356 := hb (x 6 2 && x 6 13)
        have b9357 := hb (x 5 3 && x 5 14)
        clear * - r9352 b9353 b9354 b9355 b9356 b9357 d7524 d7556 d7754 d9347
        omega
      have d9358 : (x 8 3).toNat = 1 := by
        have r9359 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b9360 := hb (x 8 3)
        have b9361 := hb (x 8 11)
        clear * - r9359 b9360 b9361 d9351
        omega
      have d9362 : (x 11 12).toNat = 0 := by
        have r9363 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9364 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e9365 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b9366 := hb (x 8 3)
        have b9367 := hb (x 9 2)
        have b9368 := hb (x 10 13)
        have b9369 := hb (x 11 12)
        clear * - r9363 e9364 e9365 b9366 b9367 b9368 b9369 d9358
        omega
      have d9370 : (x 11 1 && x 11 12).toNat = 0 := by
        have r9371 := hand2 (x 11 1) (x 11 12)
        have b9372 := hb (x 11 12)
        have b9373 := hb (x 11 1 && x 11 12)
        clear * - r9371 b9372 b9373 d9362
        omega
      have d9374 : (x 11 2 && x 11 12).toNat = 0 := by
        have r9375 := hand2 (x 11 2) (x 11 12)
        have b9376 := hb (x 11 12)
        have b9377 := hb (x 11 2 && x 11 12)
        clear * - r9375 b9376 b9377 d9362
        omega
      have d9378 : (x 11 5 && x 11 12).toNat = 0 := by
        have r9379 := hand2 (x 11 5) (x 11 12)
        have b9380 := hb (x 11 12)
        have b9381 := hb (x 11 5 && x 11 12)
        clear * - r9379 b9380 b9381 d9362
        omega
      have d9382 : (x 11 4).toNat = 0 := by
        have r9383 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
        have b9384 := hb (x 11 4)
        have b9385 := hb (x 11 12)
        clear * - r9383 b9384 b9385 d9362
        omega
      have d9386 : (x 11 4 && x 11 14).toNat = 0 := by
        have r9387 := hand1 (x 11 4) (x 11 14)
        have b9388 := hb (x 11 4)
        have b9389 := hb (x 11 4 && x 11 14)
        clear * - r9387 b9388 b9389 d9382
        omega
      have d9390 : (x 11 4 && x 11 13).toNat = 0 := by
        have r9391 := hand1 (x 11 4) (x 11 13)
        have b9392 := hb (x 11 4)
        have b9393 := hb (x 11 4 && x 11 13)
        clear * - r9391 b9392 b9393 d9382
        omega
      have d9394 : (x 10 13).toNat = 0 := by
        have r9395 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9396 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e9397 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b9398 := hb (x 8 3)
        have b9399 := hb (x 9 2)
        have b9400 := hb (x 10 13)
        have b9401 := hb (x 11 12)
        clear * - r9395 e9396 e9397 b9398 b9399 b9400 b9401 d9362 d9358
        omega
      have d9402 : (x 10 2 && x 10 13).toNat = 0 := by
        have r9403 := hand2 (x 10 2) (x 10 13)
        have b9404 := hb (x 10 13)
        have b9405 := hb (x 10 2 && x 10 13)
        clear * - r9403 b9404 b9405 d9394
        omega
      have d9406 : (x 10 3 && x 10 13).toNat = 0 := by
        have r9407 := hand2 (x 10 3) (x 10 13)
        have b9408 := hb (x 10 13)
        have b9409 := hb (x 10 3 && x 10 13)
        clear * - r9407 b9408 b9409 d9394
        omega
      have d9410 : (x 10 6 && x 10 13).toNat = 0 := by
        have r9411 := hand2 (x 10 6) (x 10 13)
        have b9412 := hb (x 10 13)
        have b9413 := hb (x 10 6 && x 10 13)
        clear * - r9411 b9412 b9413 d9394
        omega
      have d9414 : (x 10 5).toNat = 0 := by
        have r9415 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
        have b9416 := hb (x 10 5)
        have b9417 := hb (x 10 13)
        clear * - r9415 b9416 b9417 d9394
        omega
      have d9418 : (x 10 5 && x 10 14).toNat = 0 := by
        have r9419 := hand1 (x 10 5) (x 10 14)
        have b9420 := hb (x 10 5)
        have b9421 := hb (x 10 5 && x 10 14)
        clear * - r9419 b9420 b9421 d9414
        omega
      have d9422 : (x 9 2).toNat = 0 := by
        have r9423 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9424 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e9425 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b9426 := hb (x 8 3)
        have b9427 := hb (x 9 2)
        have b9428 := hb (x 10 13)
        have b9429 := hb (x 11 12)
        clear * - r9423 e9424 e9425 b9426 b9427 b9428 b9429 d9362 d9394 d9358
        omega
      have d9430 : (x 9 2 && x 9 12).toNat = 0 := by
        have r9431 := hand1 (x 9 2) (x 9 12)
        have b9432 := hb (x 9 2)
        have b9433 := hb (x 9 2 && x 9 12)
        clear * - r9431 b9432 b9433 d9422
        omega
      have d9434 : (x 9 10).toNat = 0 := by
        have r9435 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
        have b9436 := hb (x 9 2)
        have b9437 := hb (x 9 10)
        clear * - r9435 b9436 b9437 d9422
        omega
      have d9438 : (x 1 3).toNat = 0 := by
        have r9439 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9440 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e9441 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b9442 := hb (x 1 3)
        have b9443 := hb (x 2 2)
        have b9444 := hb (x 3 13)
        have b9445 := hb (x 4 12)
        clear * - r9439 e9440 e9441 b9442 b9443 b9444 b9445 d9331 d7637 d9327
        omega
      have d9446 : (x 1 11).toNat = 0 := by
        have r9447 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b9448 := hb (x 1 3)
        have b9449 := hb (x 1 11)
        clear * - r9447 b9448 b9449 d9438
        omega
      have d9450 : (x (-2) 3 && x (-2) 14).toNat = 1 := by
        have r9451 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9452 := hb (x (-3) 4)
        have b9453 := hb (x 1 11)
        have b9454 := hb (x 0 1 && x 0 12)
        have b9455 := hb (x (-1) 2 && x (-1) 13)
        have b9456 := hb (x (-2) 3 && x (-2) 14)
        clear * - r9451 b9452 b9453 b9454 b9455 b9456 d9446 d7924 g58 g2
        omega
      have d9457 : (x (-2) 3).toNat = 1 := by
        have r9458 := hand1 (x (-2) 3) (x (-2) 14)
        have b9459 := hb (x (-2) 3)
        have b9460 := hb (x (-2) 3 && x (-2) 14)
        clear * - r9458 b9459 b9460 d9450
        omega
      have d9461 : (x 1 12).toNat = 0 := by
        have r9462 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9463 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e9464 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b9465 := hb (x (-2) 3)
        have b9466 := hb (x (-1) 2)
        have b9467 := hb (x 0 13)
        have b9468 := hb (x 1 12)
        clear * - r9462 e9463 e9464 b9465 b9466 b9467 b9468 d9457
        omega
      have d9469 : (x 0 13).toNat = 0 := by
        have r9470 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9471 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e9472 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b9473 := hb (x (-2) 3)
        have b9474 := hb (x (-1) 2)
        have b9475 := hb (x 0 13)
        have b9476 := hb (x 1 12)
        clear * - r9470 e9471 e9472 b9473 b9474 b9475 b9476 d9461 d9457
        omega
      have d9477 : (x 0 2 && x 0 13).toNat = 0 := by
        have r9478 := hand2 (x 0 2) (x 0 13)
        have b9479 := hb (x 0 13)
        have b9480 := hb (x 0 2 && x 0 13)
        clear * - r9478 b9479 b9480 d9469
        omega
      have d9481 : (x 2 11).toNat = 1 := by
        have r9482 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9483 := hb (x (-2) 4)
        have b9484 := hb (x 2 11)
        have b9485 := hb (x 1 1 && x 1 12)
        have b9486 := hb (x 0 2 && x 0 13)
        have b9487 := hb (x (-1) 3 && x (-1) 14)
        clear * - r9482 b9483 b9484 b9485 b9486 b9487 d7674 d9477 g59 d9283
        omega
      have d9488 : (x 2 3).toNat = 1 := by
        have r9489 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
        have b9490 := hb (x 2 3)
        have b9491 := hb (x 2 11)
        clear * - r9489 b9490 b9491 d9481
        omega
      have d9492 : (x 5 12).toNat = 0 := by
        have r9493 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9494 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e9495 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b9496 := hb (x 2 3)
        have b9497 := hb (x 3 2)
        have b9498 := hb (x 4 13)
        have b9499 := hb (x 5 12)
        clear * - r9493 e9494 e9495 b9496 b9497 b9498 b9499 d7702 d9488
        omega
      have d9500 : (x 5 1 && x 5 12).toNat = 0 := by
        have r9501 := hand2 (x 5 1) (x 5 12)
        have b9502 := hb (x 5 12)
        have b9503 := hb (x 5 1 && x 5 12)
        clear * - r9501 b9502 b9503 d9492
        omega
      have d9504 : (x 5 4).toNat = 0 := by
        have r9505 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b9506 := hb (x 5 4)
        have b9507 := hb (x 5 12)
        clear * - r9505 b9506 b9507 d9492
        omega
      have d9508 : (x 4 13).toNat = 0 := by
        have r9509 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9510 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e9511 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b9512 := hb (x 2 3)
        have b9513 := hb (x 3 2)
        have b9514 := hb (x 4 13)
        have b9515 := hb (x 5 12)
        clear * - r9509 e9510 e9511 b9512 b9513 b9514 b9515 d9492 d7702 d9488
        omega
      have d9516 : (x 4 2 && x 4 13).toNat = 0 := by
        have r9517 := hand2 (x 4 2) (x 4 13)
        have b9518 := hb (x 4 13)
        have b9519 := hb (x 4 2 && x 4 13)
        clear * - r9517 b9518 b9519 d9508
        omega
      have d9520 : (x 6 11).toNat = 1 := by
        have r9521 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9522 := hb (x 2 4)
        have b9523 := hb (x 6 11)
        have b9524 := hb (x 5 1 && x 5 12)
        have b9525 := hb (x 4 2 && x 4 13)
        have b9526 := hb (x 3 3 && x 3 14)
        clear * - r9521 b9522 b9523 b9524 b9525 b9526 d9500 d9516 d7694 g18
        omega
      have d9527 : (x 6 3).toNat = 1 := by
        have r9528 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
        have b9529 := hb (x 6 3)
        have b9530 := hb (x 6 11)
        clear * - r9528 b9529 b9530 d9520
        omega
      have d9531 : (x 9 12).toNat = 0 := by
        have r9532 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9533 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e9534 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b9535 := hb (x 6 3)
        have b9536 := hb (x 7 2)
        have b9537 := hb (x 8 13)
        have b9538 := hb (x 9 12)
        clear * - r9532 e9533 e9534 b9535 b9536 b9537 b9538 d9527
        omega
      have d9539 : (x 9 1 && x 9 12).toNat = 0 := by
        have r9540 := hand2 (x 9 1) (x 9 12)
        have b9541 := hb (x 9 12)
        have b9542 := hb (x 9 1 && x 9 12)
        clear * - r9540 b9541 b9542 d9531
        omega
      have d9543 : (x 9 4).toNat = 0 := by
        have r9544 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
        have b9545 := hb (x 9 4)
        have b9546 := hb (x 9 12)
        clear * - r9544 b9545 b9546 d9531
        omega
      have d9547 : (x 9 4 && x 9 14).toNat = 0 := by
        have r9548 := hand1 (x 9 4) (x 9 14)
        have b9549 := hb (x 9 4)
        have b9550 := hb (x 9 4 && x 9 14)
        clear * - r9548 b9549 b9550 d9543
        omega
      have d9551 : (x 8 13).toNat = 0 := by
        have r9552 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9553 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e9554 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b9555 := hb (x 6 3)
        have b9556 := hb (x 7 2)
        have b9557 := hb (x 8 13)
        have b9558 := hb (x 9 12)
        clear * - r9552 e9553 e9554 b9555 b9556 b9557 b9558 d9531 d9527
        omega
      have d9559 : (x 8 2 && x 8 13).toNat = 0 := by
        have r9560 := hand2 (x 8 2) (x 8 13)
        have b9561 := hb (x 8 13)
        have b9562 := hb (x 8 2 && x 8 13)
        clear * - r9560 b9561 b9562 d9551
        omega
      have d9563 : (x 8 3 && x 8 13).toNat = 0 := by
        have r9564 := hand2 (x 8 3) (x 8 13)
        have b9565 := hb (x 8 13)
        have b9566 := hb (x 8 3 && x 8 13)
        clear * - r9564 b9565 b9566 d9551
        omega
      have d9567 : (x 8 5).toNat = 0 := by
        have r9568 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
        have b9569 := hb (x 8 5)
        have b9570 := hb (x 8 13)
        clear * - r9568 b9569 b9570 d9551
        omega
      have d9571 : (x 7 2).toNat = 0 := by
        have r9572 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9573 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e9574 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b9575 := hb (x 6 3)
        have b9576 := hb (x 7 2)
        have b9577 := hb (x 8 13)
        have b9578 := hb (x 9 12)
        clear * - r9572 e9573 e9574 b9575 b9576 b9577 b9578 d9531 d9551 d9527
        omega
      have d9579 : (x 7 10).toNat = 0 := by
        have r9580 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
        have b9581 := hb (x 7 2)
        have b9582 := hb (x 7 10)
        clear * - r9580 b9581 b9582 d9571
        omega
      have d9583 : (x 9 8).toNat = 0 := by
        have r9584 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9585 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e9586 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e9587 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e9588 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e9589 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e9590 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b9591 := hb (x 2 7)
        have b9592 := hb (x 3 6)
        have b9593 := hb (x 4 5)
        have b9594 := hb (x 5 4)
        have b9595 := hb (x 6 11)
        have b9596 := hb (x 7 10)
        have b9597 := hb (x 8 9)
        have b9598 := hb (x 9 8)
        clear * - r9584 e9585 e9586 e9587 e9588 e9589 e9590 b9591 b9592 b9593 b9594 b9595 b9596 b9597 b9598 d9579 d9520 d9504 d7698
        omega
      have d9599 : (x 8 9).toNat = 0 := by
        have r9600 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9601 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e9602 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e9603 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e9604 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e9605 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e9606 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b9607 := hb (x 2 7)
        have b9608 := hb (x 3 6)
        have b9609 := hb (x 4 5)
        have b9610 := hb (x 5 4)
        have b9611 := hb (x 6 11)
        have b9612 := hb (x 7 10)
        have b9613 := hb (x 8 9)
        have b9614 := hb (x 9 8)
        clear * - r9600 e9601 e9602 e9603 e9604 e9605 e9606 b9607 b9608 b9609 b9610 b9611 b9612 b9613 b9614 d9583 d9579 d9520 d9504 d7698
        omega
      have d9615 : (x 4 5).toNat = 0 := by
        have r9616 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9617 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e9618 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e9619 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e9620 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e9621 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e9622 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b9623 := hb (x 2 7)
        have b9624 := hb (x 3 6)
        have b9625 := hb (x 4 5)
        have b9626 := hb (x 5 4)
        have b9627 := hb (x 6 11)
        have b9628 := hb (x 7 10)
        have b9629 := hb (x 8 9)
        have b9630 := hb (x 9 8)
        clear * - r9616 e9617 e9618 e9619 e9620 e9621 e9622 b9623 b9624 b9625 b9626 b9627 b9628 b9629 b9630 d9583 d9599 d9579 d9520 d9504 d7698
        omega
      have d9631 : (x 8 1 && x 8 11).toNat = 1 := by
        have r9632 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9633 := hb (x 4 5)
        have b9634 := hb (x 9 10)
        have b9635 := hb (x 8 1 && x 8 11)
        have b9636 := hb (x 7 2 && x 7 12)
        have b9637 := hb (x 6 3 && x 6 13)
        have b9638 := hb (x 5 4 && x 5 14)
        clear * - r9632 b9633 b9634 b9635 b9636 b9637 b9638 d9434 d7528 d7560 d7758 d9615
        omega
      have d9639 : (x 8 1).toNat = 1 := by
        have r9640 := hand1 (x 8 1) (x 8 11)
        have b9641 := hb (x 8 1)
        have b9642 := hb (x 8 1 && x 8 11)
        clear * - r9640 b9641 b9642 d9631
        omega
      have d9643 : (x 9 14).toNat = 0 := by
        have r9644 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9645 := hb (x 8 1)
        have b9646 := hb (x 9 14)
        clear * - r9644 b9645 b9646 d9639
        omega
      have d9647 : (x 9 1 && x 9 14).toNat = 0 := by
        have r9648 := hand2 (x 9 1) (x 9 14)
        have b9649 := hb (x 9 14)
        have b9650 := hb (x 9 1 && x 9 14)
        clear * - r9648 b9649 b9650 d9643
        omega
      have d9651 : (x 8 2).toNat = 1 := by
        have r9652 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9653 := hb (x 8 2)
        have b9654 := hb (x 10 13)
        have b9655 := hb (x 9 1 && x 9 14)
        clear * - r9652 b9653 b9654 b9655 d9394 d9647
        omega
      have d9656 : (x 8 14).toNat = 1 := by
        have r9657 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
        have b9658 := hb (x 8 2)
        have b9659 := hb (x 8 14)
        clear * - r9657 b9658 b9659 d9651
        omega
      have d9660 : (x 7 1).toNat = 0 := by
        have r9661 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9662 := hb (x 7 1)
        have b9663 := hb (x 8 14)
        clear * - r9661 b9662 b9663 d9656
        omega
      have d9664 : (x 7 1 && x 7 14).toNat = 0 := by
        have r9665 := hand1 (x 7 1) (x 7 14)
        have b9666 := hb (x 7 1)
        have b9667 := hb (x 7 1 && x 7 14)
        clear * - r9665 b9666 b9667 d9660
        omega
      have d9668 : (x 6 2).toNat = 1 := by
        have r9669 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9670 := hb (x 6 2)
        have b9671 := hb (x 8 13)
        have b9672 := hb (x 7 1 && x 7 14)
        clear * - r9669 b9670 b9671 b9672 d9551 d9664
        omega
      have d9673 : (x 6 14).toNat = 1 := by
        have r9674 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have b9675 := hb (x 6 2)
        have b9676 := hb (x 6 14)
        clear * - r9674 b9675 b9676 d9668
        omega
      have d9677 : (x 5 1).toNat = 0 := by
        have r9678 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9679 := hb (x 5 1)
        have b9680 := hb (x 6 14)
        clear * - r9678 b9679 b9680 d9673
        omega
      have d9681 : (x 5 1 && x 5 11).toNat = 0 := by
        have r9682 := hand1 (x 5 1) (x 5 11)
        have b9683 := hb (x 5 1)
        have b9684 := hb (x 5 1 && x 5 11)
        clear * - r9682 b9683 b9684 d9677
        omega
      have d9685 : (x 6 10).toNat = 1 := by
        have r9686 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9687 := hb (x 1 5)
        have b9688 := hb (x 6 10)
        have b9689 := hb (x 5 1 && x 5 11)
        have b9690 := hb (x 4 2 && x 4 12)
        have b9691 := hb (x 3 3 && x 3 13)
        have b9692 := hb (x 2 4 && x 2 14)
        clear * - r9686 b9687 b9688 b9689 b9690 b9691 b9692 d9681 d9339 d7641 g57 g14
        omega
      have d9693 : (x 8 8).toNat = 0 := by
        have r9694 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9695 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e9696 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e9697 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e9698 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e9699 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e9700 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b9701 := hb (x 1 7)
        have b9702 := hb (x 2 6)
        have b9703 := hb (x 3 5)
        have b9704 := hb (x 4 4)
        have b9705 := hb (x 5 11)
        have b9706 := hb (x 6 10)
        have b9707 := hb (x 7 9)
        have b9708 := hb (x 8 8)
        clear * - r9694 e9695 e9696 e9697 e9698 e9699 e9700 b9701 b9702 b9703 b9704 b9705 b9706 b9707 b9708 d9685 d9347 d7653
        omega
      have d9709 : (x 7 9).toNat = 0 := by
        have r9710 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9711 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e9712 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e9713 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e9714 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e9715 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e9716 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b9717 := hb (x 1 7)
        have b9718 := hb (x 2 6)
        have b9719 := hb (x 3 5)
        have b9720 := hb (x 4 4)
        have b9721 := hb (x 5 11)
        have b9722 := hb (x 6 10)
        have b9723 := hb (x 7 9)
        have b9724 := hb (x 8 8)
        clear * - r9710 e9711 e9712 e9713 e9714 e9715 e9716 b9717 b9718 b9719 b9720 b9721 b9722 b9723 b9724 d9693 d9685 d9347 d7653
        omega
      have d9725 : (x 6 1 && x 6 10).toNat = 1 := by
        have r9726 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9727 := hb (x 1 6)
        have b9728 := hb (x 7 9)
        have b9729 := hb (x 6 1 && x 6 10)
        have b9730 := hb (x 5 2 && x 5 11)
        have b9731 := hb (x 4 3 && x 4 12)
        have b9732 := hb (x 3 4 && x 3 13)
        have b9733 := hb (x 2 5 && x 2 14)
        clear * - r9726 b9727 b9728 b9729 b9730 b9731 b9732 b9733 d9709 d7584 d9343 g46 g47 g15
        omega
      have d9734 : (x 6 1).toNat = 1 := by
        have r9735 := hand1 (x 6 1) (x 6 10)
        have b9736 := hb (x 6 1)
        have b9737 := hb (x 6 1 && x 6 10)
        clear * - r9735 b9736 b9737 d9725
        omega
      have d9738 : (x 7 14).toNat = 0 := by
        have r9739 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9740 := hb (x 6 1)
        have b9741 := hb (x 7 14)
        clear * - r9739 b9740 b9741 d9734
        omega
      have d9742 : (x 7 3 && x 7 14).toNat = 0 := by
        have r9743 := hand2 (x 7 3) (x 7 14)
        have b9744 := hb (x 7 14)
        have b9745 := hb (x 7 3 && x 7 14)
        clear * - r9743 b9744 b9745 d9738
        omega
      have d9746 : (x 10 11).toNat = 1 := by
        have r9747 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9748 := hb (x 6 4)
        have b9749 := hb (x 10 11)
        have b9750 := hb (x 9 1 && x 9 12)
        have b9751 := hb (x 8 2 && x 8 13)
        have b9752 := hb (x 7 3 && x 7 14)
        clear * - r9747 b9748 b9749 b9750 b9751 b9752 d9539 d9559 d9742 d7718
        omega
      have d9753 : (x 10 3).toNat = 1 := by
        have r9754 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
        have b9755 := hb (x 10 3)
        have b9756 := hb (x 10 11)
        clear * - r9754 b9755 b9756 d9746
        omega
      have d9757 : (x 13 12).toNat = 0 := by
        have r9758 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9759 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e9760 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b9761 := hb (x 10 3)
        have b9762 := hb (x 11 2)
        have b9763 := hb (x 12 13)
        have b9764 := hb (x 13 12)
        clear * - r9758 e9759 e9760 b9761 b9762 b9763 b9764 d9753
        omega
      have d9765 : (x 13 2 && x 13 12).toNat = 0 := by
        have r9766 := hand2 (x 13 2) (x 13 12)
        have b9767 := hb (x 13 12)
        have b9768 := hb (x 13 2 && x 13 12)
        clear * - r9766 b9767 b9768 d9757
        omega
      have d9769 : (x 13 4).toNat = 0 := by
        have r9770 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b9771 := hb (x 13 4)
        have b9772 := hb (x 13 12)
        clear * - r9770 b9771 b9772 d9757
        omega
      have d9773 : (x 13 4 && x 13 14).toNat = 0 := by
        have r9774 := hand1 (x 13 4) (x 13 14)
        have b9775 := hb (x 13 4)
        have b9776 := hb (x 13 4 && x 13 14)
        clear * - r9774 b9775 b9776 d9769
        omega
      have d9777 : (x 12 13).toNat = 0 := by
        have r9778 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9779 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e9780 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b9781 := hb (x 10 3)
        have b9782 := hb (x 11 2)
        have b9783 := hb (x 12 13)
        have b9784 := hb (x 13 12)
        clear * - r9778 e9779 e9780 b9781 b9782 b9783 b9784 d9757 d9753
        omega
      have d9785 : (x 12 3 && x 12 13).toNat = 0 := by
        have r9786 := hand2 (x 12 3) (x 12 13)
        have b9787 := hb (x 12 13)
        have b9788 := hb (x 12 3 && x 12 13)
        clear * - r9786 b9787 b9788 d9777
        omega
      have d9789 : (x 12 5).toNat = 0 := by
        have r9790 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
        have b9791 := hb (x 12 5)
        have b9792 := hb (x 12 13)
        clear * - r9790 b9791 b9792 d9777
        omega
      have d9793 : (x 11 2).toNat = 0 := by
        have r9794 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9795 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e9796 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b9797 := hb (x 10 3)
        have b9798 := hb (x 11 2)
        have b9799 := hb (x 12 13)
        have b9800 := hb (x 13 12)
        clear * - r9794 e9795 e9796 b9797 b9798 b9799 b9800 d9757 d9777 d9753
        omega
      have d9801 : (x 11 10).toNat = 0 := by
        have r9802 : (x 11 10).toNat ≤ (x 11 2).toNat := himp _ _ (hp10 11)
        have b9803 := hb (x 11 2)
        have b9804 := hb (x 11 10)
        clear * - r9802 b9803 b9804 d9793
        omega
      have d9805 : (x 10 1 && x 10 11).toNat = 1 := by
        have r9806 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9807 := hb (x 6 5)
        have b9808 := hb (x 11 10)
        have b9809 := hb (x 10 1 && x 10 11)
        have b9810 := hb (x 9 2 && x 9 12)
        have b9811 := hb (x 8 3 && x 8 13)
        have b9812 := hb (x 7 4 && x 7 14)
        clear * - r9806 b9807 b9808 b9809 b9810 b9811 b9812 d9801 d9430 d9563 d7540 d7568
        omega
      have d9813 : (x 10 1).toNat = 1 := by
        have r9814 := hand1 (x 10 1) (x 10 11)
        have b9815 := hb (x 10 1)
        have b9816 := hb (x 10 1 && x 10 11)
        clear * - r9814 b9815 b9816 d9805
        omega
      have d9817 : (x 11 14).toNat = 0 := by
        have r9818 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9819 := hb (x 10 1)
        have b9820 := hb (x 11 14)
        clear * - r9818 b9819 b9820 d9813
        omega
      have d9821 : (x 11 1 && x 11 14).toNat = 0 := by
        have r9822 := hand2 (x 11 1) (x 11 14)
        have b9823 := hb (x 11 14)
        have b9824 := hb (x 11 1 && x 11 14)
        clear * - r9822 b9823 b9824 d9817
        omega
      have d9825 : (x 10 2).toNat = 1 := by
        have r9826 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9827 := hb (x 10 2)
        have b9828 := hb (x 12 13)
        have b9829 := hb (x 11 1 && x 11 14)
        clear * - r9826 b9827 b9828 b9829 d9777 d9821
        omega
      have d9830 : (x 12 12).toNat = 0 := by
        have r9831 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9832 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e9833 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b9834 := hb (x 9 3)
        have b9835 := hb (x 10 2)
        have b9836 := hb (x 11 13)
        have b9837 := hb (x 12 12)
        clear * - r9831 e9832 e9833 b9834 b9835 b9836 b9837 d9825
        omega
      have d9838 : (x 12 3 && x 12 12).toNat = 0 := by
        have r9839 := hand2 (x 12 3) (x 12 12)
        have b9840 := hb (x 12 12)
        have b9841 := hb (x 12 3 && x 12 12)
        clear * - r9839 b9840 b9841 d9830
        omega
      have d9842 : (x 12 4).toNat = 0 := by
        have r9843 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
        have b9844 := hb (x 12 4)
        have b9845 := hb (x 12 12)
        clear * - r9843 b9844 b9845 d9830
        omega
      have d9846 : (x 12 4 && x 12 11).toNat = 0 := by
        have r9847 := hand1 (x 12 4) (x 12 11)
        have b9848 := hb (x 12 4)
        have b9849 := hb (x 12 4 && x 12 11)
        clear * - r9847 b9848 b9849 d9842
        omega
      have d9850 : (x 11 13).toNat = 0 := by
        have r9851 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9852 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e9853 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b9854 := hb (x 9 3)
        have b9855 := hb (x 10 2)
        have b9856 := hb (x 11 13)
        have b9857 := hb (x 12 12)
        clear * - r9851 e9852 e9853 b9854 b9855 b9856 b9857 d9830 d9825
        omega
      have d9858 : (x 11 5).toNat = 0 := by
        have r9859 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
        have b9860 := hb (x 11 5)
        have b9861 := hb (x 11 13)
        clear * - r9859 b9860 b9861 d9850
        omega
      have d9862 : (x 9 3).toNat = 0 := by
        have r9863 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9864 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e9865 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b9866 := hb (x 9 3)
        have b9867 := hb (x 10 2)
        have b9868 := hb (x 11 13)
        have b9869 := hb (x 12 12)
        clear * - r9863 e9864 e9865 b9866 b9867 b9868 b9869 d9830 d9850 d9825
        omega
      have d9870 : (x 9 3 && x 9 14).toNat = 0 := by
        have r9871 := hand1 (x 9 3) (x 9 14)
        have b9872 := hb (x 9 3)
        have b9873 := hb (x 9 3 && x 9 14)
        clear * - r9871 b9872 b9873 d9862
        omega
      have d9874 : (x 8 12).toNat = 0 := by
        have r9875 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9876 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e9877 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b9878 := hb (x 5 3)
        have b9879 := hb (x 6 2)
        have b9880 := hb (x 7 13)
        have b9881 := hb (x 8 12)
        clear * - r9875 e9876 e9877 b9878 b9879 b9880 b9881 d9668
        omega
      have d9882 : (x 8 4).toNat = 0 := by
        have r9883 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b9884 := hb (x 8 4)
        have b9885 := hb (x 8 12)
        clear * - r9883 b9884 b9885 d9874
        omega
      have d9886 : (x 12 11).toNat = 1 := by
        have r9887 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9888 := hb (x 8 4)
        have b9889 := hb (x 12 11)
        have b9890 := hb (x 11 1 && x 11 12)
        have b9891 := hb (x 10 2 && x 10 13)
        have b9892 := hb (x 9 3 && x 9 14)
        clear * - r9887 b9888 b9889 b9890 b9891 b9892 d9370 d9402 d9870 d9882
        omega
      have d9893 : (x 12 3).toNat = 1 := by
        have r9894 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
        have b9895 := hb (x 12 3)
        have b9896 := hb (x 12 11)
        clear * - r9894 b9895 b9896 d9886
        omega
      have d9897 : (x 15 12).toNat = 0 := by
        have r9898 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9899 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e9900 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b9901 := hb (x 12 3)
        have b9902 := hb (x 13 2)
        have b9903 := hb (x 14 13)
        have b9904 := hb (x 15 12)
        clear * - r9898 e9899 e9900 b9901 b9902 b9903 b9904 d9893
        omega
      have d9905 : (x 15 1 && x 15 12).toNat = 0 := by
        have r9906 := hand2 (x 15 1) (x 15 12)
        have b9907 := hb (x 15 12)
        have b9908 := hb (x 15 1 && x 15 12)
        clear * - r9906 b9907 b9908 d9897
        omega
      have d9909 : (x 15 2 && x 15 12).toNat = 0 := by
        have r9910 := hand2 (x 15 2) (x 15 12)
        have b9911 := hb (x 15 12)
        have b9912 := hb (x 15 2 && x 15 12)
        clear * - r9910 b9911 b9912 d9897
        omega
      have d9913 : (x 14 13).toNat = 0 := by
        have r9914 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9915 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e9916 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b9917 := hb (x 12 3)
        have b9918 := hb (x 13 2)
        have b9919 := hb (x 14 13)
        have b9920 := hb (x 15 12)
        clear * - r9914 e9915 e9916 b9917 b9918 b9919 b9920 d9897 d9893
        omega
      have d9921 : (x 14 2 && x 14 13).toNat = 0 := by
        have r9922 := hand2 (x 14 2) (x 14 13)
        have b9923 := hb (x 14 13)
        have b9924 := hb (x 14 2 && x 14 13)
        clear * - r9922 b9923 b9924 d9913
        omega
      have d9925 : (x 14 3 && x 14 13).toNat = 0 := by
        have r9926 := hand2 (x 14 3) (x 14 13)
        have b9927 := hb (x 14 13)
        have b9928 := hb (x 14 3 && x 14 13)
        clear * - r9926 b9927 b9928 d9913
        omega
      have d9929 : (x 13 2).toNat = 0 := by
        have r9930 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9931 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e9932 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b9933 := hb (x 12 3)
        have b9934 := hb (x 13 2)
        have b9935 := hb (x 14 13)
        have b9936 := hb (x 15 12)
        clear * - r9930 e9931 e9932 b9933 b9934 b9935 b9936 d9897 d9913 d9893
        omega
      have d9937 : (x 13 2 && x 13 11).toNat = 0 := by
        have r9938 := hand1 (x 13 2) (x 13 11)
        have b9939 := hb (x 13 2)
        have b9940 := hb (x 13 2 && x 13 11)
        clear * - r9938 b9939 b9940 d9929
        omega
      have d9941 : (x 13 10).toNat = 0 := by
        have r9942 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
        have b9943 := hb (x 13 2)
        have b9944 := hb (x 13 10)
        clear * - r9942 b9943 b9944 d9929
        omega
      have d9945 : (x 13 3 && x 13 10).toNat = 0 := by
        have r9946 := hand2 (x 13 3) (x 13 10)
        have b9947 := hb (x 13 10)
        have b9948 := hb (x 13 3 && x 13 10)
        clear * - r9946 b9947 b9948 d9941
        omega
      have d9949 : (x 12 1 && x 12 11).toNat = 1 := by
        have r9950 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9951 := hb (x 8 5)
        have b9952 := hb (x 13 10)
        have b9953 := hb (x 12 1 && x 12 11)
        have b9954 := hb (x 11 2 && x 11 12)
        have b9955 := hb (x 10 3 && x 10 13)
        have b9956 := hb (x 9 4 && x 9 14)
        clear * - r9950 b9951 b9952 b9953 b9954 b9955 b9956 d9941 d9374 d9406 d9547 d9567
        omega
      have d9957 : (x 12 1).toNat = 1 := by
        have r9958 := hand1 (x 12 1) (x 12 11)
        have b9959 := hb (x 12 1)
        have b9960 := hb (x 12 1 && x 12 11)
        clear * - r9958 b9959 b9960 d9949
        omega
      have d9961 : (x 13 14).toNat = 0 := by
        have r9962 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9963 := hb (x 12 1)
        have b9964 := hb (x 13 14)
        clear * - r9962 b9963 b9964 d9957
        omega
      have d9965 : (x 13 3 && x 13 14).toNat = 0 := by
        have r9966 := hand2 (x 13 3) (x 13 14)
        have b9967 := hb (x 13 14)
        have b9968 := hb (x 13 3 && x 13 14)
        clear * - r9966 b9967 b9968 d9961
        omega
      have d9969 : (x 16 11).toNat = 1 := by
        have r9970 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b9971 := hb (x 12 4)
        have b9972 := hb (x 16 11)
        have b9973 := hb (x 15 1 && x 15 12)
        have b9974 := hb (x 14 2 && x 14 13)
        have b9975 := hb (x 13 3 && x 13 14)
        clear * - r9970 b9971 b9972 b9973 b9974 b9975 d9905 d9921 d9965 d9842
        omega
      have d9976 : (x 16 3).toNat = 1 := by
        have r9977 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
        have b9978 := hb (x 16 3)
        have b9979 := hb (x 16 11)
        clear * - r9977 b9978 b9979 d9969
        omega
      have d9980 : (x 19 12).toNat = 0 := by
        have r9981 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9982 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e9983 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b9984 := hb (x 16 3)
        have b9985 := hb (x 17 2)
        have b9986 := hb (x 18 13)
        have b9987 := hb (x 19 12)
        clear * - r9981 e9982 e9983 b9984 b9985 b9986 b9987 d9976
        omega
      have d9988 : (x 19 1 && x 19 12).toNat = 0 := by
        have r9989 := hand2 (x 19 1) (x 19 12)
        have b9990 := hb (x 19 12)
        have b9991 := hb (x 19 1 && x 19 12)
        clear * - r9989 b9990 b9991 d9980
        omega
      have d9992 : (x 19 4).toNat = 0 := by
        have r9993 : (x 19 4).toNat ≤ (x 19 12).toNat := himp _ _ (hp4 19)
        have b9994 := hb (x 19 4)
        have b9995 := hb (x 19 12)
        clear * - r9993 b9994 b9995 d9980
        omega
      have d9996 : (x 18 13).toNat = 0 := by
        have r9997 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e9998 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e9999 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b10000 := hb (x 16 3)
        have b10001 := hb (x 17 2)
        have b10002 := hb (x 18 13)
        have b10003 := hb (x 19 12)
        clear * - r9997 e9998 e9999 b10000 b10001 b10002 b10003 d9980 d9976
        omega
      have d10004 : (x 18 2 && x 18 13).toNat = 0 := by
        have r10005 := hand2 (x 18 2) (x 18 13)
        have b10006 := hb (x 18 13)
        have b10007 := hb (x 18 2 && x 18 13)
        clear * - r10005 b10006 b10007 d9996
        omega
      have d10008 : (x 18 5).toNat = 0 := by
        have r10009 : (x 18 5).toNat ≤ (x 18 13).toNat := himp _ _ (hp5 18)
        have b10010 := hb (x 18 5)
        have b10011 := hb (x 18 13)
        clear * - r10009 b10010 b10011 d9996
        omega
      have d10012 : (x 17 2).toNat = 0 := by
        have r10013 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10014 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e10015 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b10016 := hb (x 16 3)
        have b10017 := hb (x 17 2)
        have b10018 := hb (x 18 13)
        have b10019 := hb (x 19 12)
        clear * - r10013 e10014 e10015 b10016 b10017 b10018 b10019 d9980 d9996 d9976
        omega
      have d10020 : (x 17 10).toNat = 0 := by
        have r10021 : (x 17 10).toNat ≤ (x 17 2).toNat := himp _ _ (hp10 17)
        have b10022 := hb (x 17 2)
        have b10023 := hb (x 17 10)
        clear * - r10021 b10022 b10023 d10012
        omega
      have d10024 : (x 16 1 && x 16 11).toNat = 1 := by
        have r10025 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := by have q := hcov10 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10026 := hb (x 12 5)
        have b10027 := hb (x 17 10)
        have b10028 := hb (x 16 1 && x 16 11)
        have b10029 := hb (x 15 2 && x 15 12)
        have b10030 := hb (x 14 3 && x 14 13)
        have b10031 := hb (x 13 4 && x 13 14)
        clear * - r10025 b10026 b10027 b10028 b10029 b10030 b10031 d10020 d9909 d9925 d9773 d9789
        omega
      have d10032 : (x 16 1).toNat = 1 := by
        have r10033 := hand1 (x 16 1) (x 16 11)
        have b10034 := hb (x 16 1)
        have b10035 := hb (x 16 1 && x 16 11)
        clear * - r10033 b10034 b10035 d10024
        omega
      have d10036 : (x 17 14).toNat = 0 := by
        have r10037 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10038 := hb (x 16 1)
        have b10039 := hb (x 17 14)
        clear * - r10037 b10038 b10039 d10032
        omega
      have d10040 : (x 17 1 && x 17 14).toNat = 0 := by
        have r10041 := hand2 (x 17 1) (x 17 14)
        have b10042 := hb (x 17 14)
        have b10043 := hb (x 17 1 && x 17 14)
        clear * - r10041 b10042 b10043 d10036
        omega
      have d10044 : (x 16 2).toNat = 1 := by
        have r10045 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10046 := hb (x 16 2)
        have b10047 := hb (x 18 13)
        have b10048 := hb (x 17 1 && x 17 14)
        clear * - r10045 b10046 b10047 b10048 d9996 d10040
        omega
      have d10049 : (x 16 14).toNat = 1 := by
        have r10050 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
        have b10051 := hb (x 16 2)
        have b10052 := hb (x 16 14)
        clear * - r10050 b10051 b10052 d10044
        omega
      have d10053 : (x 15 1).toNat = 0 := by
        have r10054 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10055 := hb (x 15 1)
        have b10056 := hb (x 16 14)
        clear * - r10054 b10055 b10056 d10049
        omega
      have d10057 : (x 15 1 && x 15 14).toNat = 0 := by
        have r10058 := hand1 (x 15 1) (x 15 14)
        have b10059 := hb (x 15 1)
        have b10060 := hb (x 15 1 && x 15 14)
        clear * - r10058 b10059 b10060 d10053
        omega
      have d10061 : (x 15 1 && x 15 8).toNat = 0 := by
        have r10062 := hand1 (x 15 1) (x 15 8)
        have b10063 := hb (x 15 1)
        have b10064 := hb (x 15 1 && x 15 8)
        clear * - r10062 b10063 b10064 d10053
        omega
      have d10065 : (x 15 13).toNat = 0 := by
        have r10066 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
        have b10067 := hb (x 15 1)
        have b10068 := hb (x 15 13)
        clear * - r10066 b10067 b10068 d10053
        omega
      have d10069 : (x 15 9).toNat = 0 := by
        have r10070 : (x 15 9).toNat ≤ (x 15 1).toNat := himp _ _ (hp9 15)
        have b10071 := hb (x 15 1)
        have b10072 := hb (x 15 9)
        clear * - r10070 b10071 b10072 d10053
        omega
      have d10073 : (x 17 3 && x 17 14).toNat = 0 := by
        have r10074 := hand2 (x 17 3) (x 17 14)
        have b10075 := hb (x 17 14)
        have b10076 := hb (x 17 3 && x 17 14)
        clear * - r10074 b10075 b10076 d10036
        omega
      have d10077 : (x 17 6).toNat = 0 := by
        have r10078 : (x 17 6).toNat ≤ (x 17 14).toNat := himp _ _ (hp6 17)
        have b10079 := hb (x 17 6)
        have b10080 := hb (x 17 14)
        clear * - r10078 b10079 b10080 d10036
        omega
      have d10081 : (x 14 1 && x 14 14).toNat = 1 := by
        have r10082 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10083 := hb (x 13 2)
        have b10084 := hb (x 15 13)
        have b10085 := hb (x 14 1 && x 14 14)
        clear * - r10082 b10083 b10084 b10085 d10065 d9929
        omega
      have d10086 : (x 14 1).toNat = 1 := by
        have r10087 := hand1 (x 14 1) (x 14 14)
        have b10088 := hb (x 14 1)
        have b10089 := hb (x 14 1 && x 14 14)
        clear * - r10087 b10088 b10089 d10081
        omega
      have d10090 : (x 15 14).toNat = 0 := by
        have r10091 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10092 := hb (x 14 1)
        have b10093 := hb (x 15 14)
        clear * - r10091 b10092 b10093 d10086
        omega
      have d10094 : (x 15 2).toNat = 0 := by
        have r10095 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b10096 := hb (x 15 2)
        have b10097 := hb (x 15 14)
        clear * - r10095 b10096 b10097 d10090
        omega
      have d10098 : (x 15 10).toNat = 0 := by
        have r10099 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
        have b10100 := hb (x 15 2)
        have b10101 := hb (x 15 10)
        clear * - r10099 b10100 b10101 d10094
        omega
      have d10102 : (x 14 1 && x 14 11).toNat = 1 := by
        have r10103 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10104 := hb (x 10 5)
        have b10105 := hb (x 15 10)
        have b10106 := hb (x 14 1 && x 14 11)
        have b10107 := hb (x 13 2 && x 13 12)
        have b10108 := hb (x 12 3 && x 12 13)
        have b10109 := hb (x 11 4 && x 11 14)
        clear * - r10103 b10104 b10105 b10106 b10107 b10108 b10109 d10098 d9765 d9785 d9386 d9414
        omega
      have d10110 : (x 14 11).toNat = 1 := by
        have r10111 := hand2 (x 14 1) (x 14 11)
        have b10112 := hb (x 14 11)
        have b10113 := hb (x 14 1 && x 14 11)
        clear * - r10111 b10112 b10113 d10102
        omega
      have d10114 : (x 14 3).toNat = 1 := by
        have r10115 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
        have b10116 := hb (x 14 3)
        have b10117 := hb (x 14 11)
        clear * - r10115 b10116 b10117 d10110
        omega
      have d10118 : (x 17 12).toNat = 0 := by
        have r10119 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10120 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e10121 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b10122 := hb (x 14 3)
        have b10123 := hb (x 15 2)
        have b10124 := hb (x 16 13)
        have b10125 := hb (x 17 12)
        clear * - r10119 e10120 e10121 b10122 b10123 b10124 b10125 d10094 d10114
        omega
      have d10126 : (x 16 13).toNat = 0 := by
        have r10127 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10128 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e10129 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b10130 := hb (x 14 3)
        have b10131 := hb (x 15 2)
        have b10132 := hb (x 16 13)
        have b10133 := hb (x 17 12)
        clear * - r10127 e10128 e10129 b10130 b10131 b10132 b10133 d10118 d10094 d10114
        omega
      have d10134 : (x 14 2).toNat = 1 := by
        have r10135 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10136 := hb (x 14 2)
        have b10137 := hb (x 16 13)
        have b10138 := hb (x 15 1 && x 15 14)
        clear * - r10135 b10136 b10137 b10138 d10126 d10057
        omega
      have d10139 : (x 16 12).toNat = 0 := by
        have r10140 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10141 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e10142 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b10143 := hb (x 13 3)
        have b10144 := hb (x 14 2)
        have b10145 := hb (x 15 13)
        have b10146 := hb (x 16 12)
        clear * - r10140 e10141 e10142 b10143 b10144 b10145 b10146 d10065 d10134
        omega
      have d10147 : (x 16 4).toNat = 0 := by
        have r10148 : (x 16 4).toNat ≤ (x 16 12).toNat := himp _ _ (hp4 16)
        have b10149 := hb (x 16 4)
        have b10150 := hb (x 16 12)
        clear * - r10148 b10149 b10150 d10139
        omega
      have d10151 : (x 20 11).toNat = 1 := by
        have r10152 : 1 ≤ (x 20 11).toNat + (x 19 1 && x 19 12).toNat + (x 18 2 && x 18 13).toNat + (x 17 3 && x 17 14).toNat + (x 16 4).toNat := by have q := hcov11 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10153 := hb (x 16 4)
        have b10154 := hb (x 20 11)
        have b10155 := hb (x 19 1 && x 19 12)
        have b10156 := hb (x 18 2 && x 18 13)
        have b10157 := hb (x 17 3 && x 17 14)
        clear * - r10152 b10153 b10154 b10155 b10156 b10157 d9988 d10004 d10073 d10147
        omega
      have d10158 : (x 23 8).toNat = 0 := by
        have r10159 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10160 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
        have e10161 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
        have e10162 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
        have e10163 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
        have e10164 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
        have e10165 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
        have b10166 := hb (x 16 7)
        have b10167 := hb (x 17 6)
        have b10168 := hb (x 18 5)
        have b10169 := hb (x 19 4)
        have b10170 := hb (x 20 11)
        have b10171 := hb (x 21 10)
        have b10172 := hb (x 22 9)
        have b10173 := hb (x 23 8)
        clear * - r10159 e10160 e10161 e10162 e10163 e10164 e10165 b10166 b10167 b10168 b10169 b10170 b10171 b10172 b10173 d10151 d9992 d10008 d10077
        omega
      have d10174 : (x 22 9).toNat = 0 := by
        have r10175 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10176 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
        have e10177 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
        have e10178 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
        have e10179 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
        have e10180 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
        have e10181 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
        have b10182 := hb (x 16 7)
        have b10183 := hb (x 17 6)
        have b10184 := hb (x 18 5)
        have b10185 := hb (x 19 4)
        have b10186 := hb (x 20 11)
        have b10187 := hb (x 21 10)
        have b10188 := hb (x 22 9)
        have b10189 := hb (x 23 8)
        clear * - r10175 e10176 e10177 e10178 e10179 e10180 e10181 b10182 b10183 b10184 b10185 b10186 b10187 b10188 b10189 d10158 d10151 d9992 d10008 d10077
        omega
      have d10190 : (x 21 10).toNat = 0 := by
        have r10191 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10192 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
        have e10193 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
        have e10194 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
        have e10195 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
        have e10196 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
        have e10197 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
        have b10198 := hb (x 16 7)
        have b10199 := hb (x 17 6)
        have b10200 := hb (x 18 5)
        have b10201 := hb (x 19 4)
        have b10202 := hb (x 20 11)
        have b10203 := hb (x 21 10)
        have b10204 := hb (x 22 9)
        have b10205 := hb (x 23 8)
        clear * - r10191 e10192 e10193 e10194 e10195 e10196 e10197 b10198 b10199 b10200 b10201 b10202 b10203 b10204 b10205 d10158 d10174 d10151 d9992 d10008 d10077
        omega
      have d10206 : (x 16 7).toNat = 0 := by
        have r10207 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10208 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
        have e10209 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
        have e10210 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
        have e10211 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
        have e10212 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
        have e10213 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
        have b10214 := hb (x 16 7)
        have b10215 := hb (x 17 6)
        have b10216 := hb (x 18 5)
        have b10217 := hb (x 19 4)
        have b10218 := hb (x 20 11)
        have b10219 := hb (x 21 10)
        have b10220 := hb (x 22 9)
        have b10221 := hb (x 23 8)
        clear * - r10207 e10208 e10209 e10210 e10211 e10212 e10213 b10214 b10215 b10216 b10217 b10218 b10219 b10220 b10221 d10158 d10174 d10190 d10151 d9992 d10008 d10077
        omega
      have d10222 : (x 13 3).toNat = 0 := by
        have r10223 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10224 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e10225 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b10226 := hb (x 13 3)
        have b10227 := hb (x 14 2)
        have b10228 := hb (x 15 13)
        have b10229 := hb (x 16 12)
        clear * - r10223 e10224 e10225 b10226 b10227 b10228 b10229 d10139 d10065 d10134
        omega
      have d10230 : (x 13 11).toNat = 0 := by
        have r10231 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
        have b10232 := hb (x 13 3)
        have b10233 := hb (x 13 11)
        clear * - r10231 b10232 b10233 d10222
        omega
      have d10234 : (x 15 8).toNat = 0 := by
        have r10235 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10236 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e10237 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e10238 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e10239 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e10240 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e10241 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b10242 := hb (x 8 7)
        have b10243 := hb (x 9 6)
        have b10244 := hb (x 10 5)
        have b10245 := hb (x 11 4)
        have b10246 := hb (x 12 11)
        have b10247 := hb (x 13 10)
        have b10248 := hb (x 14 9)
        have b10249 := hb (x 15 8)
        clear * - r10235 e10236 e10237 e10238 e10239 e10240 e10241 b10242 b10243 b10244 b10245 b10246 b10247 b10248 b10249 d9941 d9886 d9382 d9414
        omega
      have d10250 : (x 14 9).toNat = 0 := by
        have r10251 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10252 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e10253 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e10254 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e10255 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e10256 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e10257 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b10258 := hb (x 8 7)
        have b10259 := hb (x 9 6)
        have b10260 := hb (x 10 5)
        have b10261 := hb (x 11 4)
        have b10262 := hb (x 12 11)
        have b10263 := hb (x 13 10)
        have b10264 := hb (x 14 9)
        have b10265 := hb (x 15 8)
        clear * - r10251 e10252 e10253 e10254 e10255 e10256 e10257 b10258 b10259 b10260 b10261 b10262 b10263 b10264 b10265 d10234 d9941 d9886 d9382 d9414
        omega
      have d10266 : (x 14 2 && x 14 9).toNat = 0 := by
        have r10267 := hand2 (x 14 2) (x 14 9)
        have b10268 := hb (x 14 9)
        have b10269 := hb (x 14 2 && x 14 9)
        clear * - r10267 b10268 b10269 d10250
        omega
      have d10270 : (x 9 6).toNat = 0 := by
        have r10271 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10272 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e10273 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e10274 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e10275 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e10276 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e10277 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b10278 := hb (x 8 7)
        have b10279 := hb (x 9 6)
        have b10280 := hb (x 10 5)
        have b10281 := hb (x 11 4)
        have b10282 := hb (x 12 11)
        have b10283 := hb (x 13 10)
        have b10284 := hb (x 14 9)
        have b10285 := hb (x 15 8)
        clear * - r10271 e10272 e10273 e10274 e10275 e10276 e10277 b10278 b10279 b10280 b10281 b10282 b10283 b10284 b10285 d10234 d10250 d9941 d9886 d9382 d9414
        omega
      have d10286 : (x 14 1 && x 14 10).toNat = 1 := by
        have r10287 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10288 := hb (x 9 6)
        have b10289 := hb (x 15 9)
        have b10290 := hb (x 14 1 && x 14 10)
        have b10291 := hb (x 13 2 && x 13 11)
        have b10292 := hb (x 12 3 && x 12 12)
        have b10293 := hb (x 11 4 && x 11 13)
        have b10294 := hb (x 10 5 && x 10 14)
        clear * - r10287 b10288 b10289 b10290 b10291 b10292 b10293 b10294 d10069 d9937 d9838 d9390 d9418 d10270
        omega
      have d10295 : (x 14 10).toNat = 1 := by
        have r10296 := hand2 (x 14 1) (x 14 10)
        have b10297 := hb (x 14 10)
        have b10298 := hb (x 14 1 && x 14 10)
        clear * - r10296 b10297 b10298 d10286
        omega
      have d10299 : (x 16 8).toNat = 0 := by
        have r10300 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10301 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e10302 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e10303 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e10304 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e10305 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e10306 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b10307 := hb (x 9 7)
        have b10308 := hb (x 10 6)
        have b10309 := hb (x 11 5)
        have b10310 := hb (x 12 4)
        have b10311 := hb (x 13 11)
        have b10312 := hb (x 14 10)
        have b10313 := hb (x 15 9)
        have b10314 := hb (x 16 8)
        clear * - r10300 e10301 e10302 e10303 e10304 e10305 e10306 b10307 b10308 b10309 b10310 b10311 b10312 b10313 b10314 d10069 d10295 d10230 d9842 d9858
        omega
      have d10315 : (x 10 6).toNat = 0 := by
        have r10316 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10317 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e10318 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e10319 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e10320 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e10321 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e10322 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b10323 := hb (x 9 7)
        have b10324 := hb (x 10 6)
        have b10325 := hb (x 11 5)
        have b10326 := hb (x 12 4)
        have b10327 := hb (x 13 11)
        have b10328 := hb (x 14 10)
        have b10329 := hb (x 15 9)
        have b10330 := hb (x 16 8)
        clear * - r10316 e10317 e10318 e10319 e10320 e10321 e10322 b10323 b10324 b10325 b10326 b10327 b10328 b10329 b10330 d10299 d10069 d10295 d10230 d9842 d9858
        omega
      have d10331 : (x 9 7).toNat = 0 := by
        have r10332 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10333 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e10334 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e10335 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e10336 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e10337 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e10338 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b10339 := hb (x 9 7)
        have b10340 := hb (x 10 6)
        have b10341 := hb (x 11 5)
        have b10342 := hb (x 12 4)
        have b10343 := hb (x 13 11)
        have b10344 := hb (x 14 10)
        have b10345 := hb (x 15 9)
        have b10346 := hb (x 16 8)
        clear * - r10332 e10333 e10334 e10335 e10336 e10337 e10338 b10339 b10340 b10341 b10342 b10343 b10344 b10345 b10346 d10299 d10069 d10295 d10230 d9842 d9858 d10315
        omega
      have d10347 : (x 9 7 && x 9 14).toNat = 0 := by
        have r10348 := hand1 (x 9 7) (x 9 14)
        have b10349 := hb (x 9 7)
        have b10350 := hb (x 9 7 && x 9 14)
        clear * - r10348 b10349 b10350 d10331
        omega
      have r10351 : 1 ≤ (x 16 7).toNat + (x 15 1 && x 15 8).toNat + (x 14 2 && x 14 9).toNat + (x 13 3 && x 13 10).toNat + (x 12 4 && x 12 11).toNat + (x 11 5 && x 11 12).toNat + (x 10 6 && x 10 13).toNat + (x 9 7 && x 9 14).toNat + (x 8 8).toNat := by have q := hcov7 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10352 := hb (x 8 8)
      have b10353 := hb (x 16 7)
      have b10354 := hb (x 15 1 && x 15 8)
      have b10355 := hb (x 14 2 && x 14 9)
      have b10356 := hb (x 13 3 && x 13 10)
      have b10357 := hb (x 12 4 && x 12 11)
      have b10358 := hb (x 11 5 && x 11 12)
      have b10359 := hb (x 10 6 && x 10 13)
      have b10360 := hb (x 9 7 && x 9 14)
      linarith only [r10351, b10352, b10353, b10354, b10355, b10356, b10357, b10358, b10359, b10360, d10206, d10061, d10266, d9945, d9846, d9378, d9410, d10347, d9693]
  · have f10361 : (x 0 12).toNat = 1 := by rw [h7922]; rfl
    have d10362 : (x (-2) 2).toNat = 0 := by
      have r10363 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10364 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e10365 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b10366 := hb (x (-3) 3)
      have b10367 := hb (x (-2) 2)
      have b10368 := hb (x (-1) 13)
      have b10369 := hb (x 0 12)
      clear * - r10363 e10364 e10365 b10366 b10367 b10368 b10369 f10361 g8
      omega
    have d10370 : (x (-2) 10).toNat = 0 := by
      have r10371 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
      have b10372 := hb (x (-2) 2)
      have b10373 := hb (x (-2) 10)
      clear * - r10371 b10372 b10373 d10362
      omega
    have d10374 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
      have r10375 := hand2 (x (-2) 1) (x (-2) 10)
      have b10376 := hb (x (-2) 10)
      have b10377 := hb (x (-2) 1 && x (-2) 10)
      clear * - r10375 b10376 b10377 d10370
      omega
    have d10378 : (x (-2) 3 && x (-2) 10).toNat = 0 := by
      have r10379 := hand2 (x (-2) 3) (x (-2) 10)
      have b10380 := hb (x (-2) 10)
      have b10381 := hb (x (-2) 3 && x (-2) 10)
      clear * - r10379 b10380 b10381 d10370
      omega
    have d10382 : (x 0 13).toNat = 1 := by
      have r10383 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10384 := hb (x (-2) 2)
      have b10385 := hb (x 0 13)
      have b10386 := hb (x (-1) 1 && x (-1) 14)
      clear * - r10383 b10384 b10385 b10386 g63 d10362
      omega
    have d10387 : (x 1 12).toNat = 0 := by
      have r10388 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10389 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e10390 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b10391 := hb (x (-2) 3)
      have b10392 := hb (x (-1) 2)
      have b10393 := hb (x 0 13)
      have b10394 := hb (x 1 12)
      clear * - r10388 e10389 e10390 b10391 b10392 b10393 b10394 d10382
      omega
    have d10395 : (x (-1) 2).toNat = 0 := by
      have r10396 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10397 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e10398 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b10399 := hb (x (-2) 3)
      have b10400 := hb (x (-1) 2)
      have b10401 := hb (x 0 13)
      have b10402 := hb (x 1 12)
      clear * - r10396 e10397 e10398 b10399 b10400 b10401 b10402 d10387 d10382
      omega
    have d10403 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
      have r10404 := hand1 (x (-1) 2) (x (-1) 12)
      have b10405 := hb (x (-1) 2)
      have b10406 := hb (x (-1) 2 && x (-1) 12)
      clear * - r10404 b10405 b10406 d10395
      omega
    have d10407 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
      have r10408 := hand1 (x (-1) 2) (x (-1) 8)
      have b10409 := hb (x (-1) 2)
      have b10410 := hb (x (-1) 2 && x (-1) 8)
      clear * - r10408 b10409 b10410 d10395
      omega
    have d10411 : (x (-2) 3).toNat = 0 := by
      have r10412 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10413 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e10414 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b10415 := hb (x (-2) 3)
      have b10416 := hb (x (-1) 2)
      have b10417 := hb (x 0 13)
      have b10418 := hb (x 1 12)
      clear * - r10412 e10413 e10414 b10415 b10416 b10417 b10418 d10387 d10382 d10395
      omega
    have d10419 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
      have r10420 := hand1 (x (-2) 3) (x (-2) 13)
      have b10421 := hb (x (-2) 3)
      have b10422 := hb (x (-2) 3 && x (-2) 13)
      clear * - r10420 b10421 b10422 d10411
      omega
    have d10423 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
      have r10424 := hand1 (x (-2) 3) (x (-2) 12)
      have b10425 := hb (x (-2) 3)
      have b10426 := hb (x (-2) 3 && x (-2) 12)
      clear * - r10424 b10425 b10426 d10411
      omega
    have d10427 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
      have r10428 := hand1 (x (-2) 3) (x (-2) 9)
      have b10429 := hb (x (-2) 3)
      have b10430 := hb (x (-2) 3 && x (-2) 9)
      clear * - r10428 b10429 b10430 d10411
      omega
    have d10431 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
      have r10432 := hand1 (x (-2) 3) (x (-2) 8)
      have b10433 := hb (x (-2) 3)
      have b10434 := hb (x (-2) 3 && x (-2) 8)
      clear * - r10432 b10433 b10434 d10411
      omega
    have d10435 : (x (-3) 3).toNat = 0 := by
      have r10436 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10437 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e10438 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b10439 := hb (x (-3) 3)
      have b10440 := hb (x (-2) 2)
      have b10441 := hb (x (-1) 13)
      have b10442 := hb (x 0 12)
      clear * - r10436 e10437 e10438 b10439 b10440 b10441 b10442 f10361 g8 d10362
      omega
    have d10443 : (x (-3) 11).toNat = 0 := by
      have r10444 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
      have b10445 := hb (x (-3) 3)
      have b10446 := hb (x (-3) 11)
      clear * - r10444 b10445 b10446 d10435
      omega
    have d10447 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
      have r10448 := hand2 (x (-3) 2) (x (-3) 11)
      have b10449 := hb (x (-3) 11)
      have b10450 := hb (x (-3) 2 && x (-3) 11)
      clear * - r10448 b10449 b10450 d10443
      omega
    have d10451 : (x 0 1 && x 0 11).toNat = 1 := by
      have r10452 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10453 := hb (x (-4) 5)
      have b10454 := hb (x 1 10)
      have b10455 := hb (x 0 1 && x 0 11)
      have b10456 := hb (x (-1) 2 && x (-1) 12)
      have b10457 := hb (x (-2) 3 && x (-2) 13)
      have b10458 := hb (x (-3) 4 && x (-3) 14)
      clear * - r10452 b10453 b10454 b10455 b10456 b10457 b10458 g17 d10403 d10419 g49 g1
      omega
    have d10459 : (x 0 11).toNat = 1 := by
      have r10460 := hand2 (x 0 1) (x 0 11)
      have b10461 := hb (x 0 11)
      have b10462 := hb (x 0 1 && x 0 11)
      clear * - r10460 b10461 b10462 d10451
      omega
    have d10463 : (x 0 1 && x 0 10).toNat = 1 := by
      have r10464 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b10465 := hb (x (-5) 6)
      have b10466 := hb (x 1 9)
      have b10467 := hb (x 0 1 && x 0 10)
      have b10468 := hb (x (-1) 2 && x (-1) 11)
      have b10469 := hb (x (-2) 3 && x (-2) 12)
      have b10470 := hb (x (-3) 4 && x (-3) 13)
      have b10471 := hb (x (-4) 5 && x (-4) 14)
      clear * - r10464 b10465 b10466 b10467 b10468 b10469 b10470 b10471 d7682 g43 d10423 g44 g45 g0
      omega
    have d10472 : (x 0 10).toNat = 1 := by
      have r10473 := hand2 (x 0 1) (x 0 10)
      have b10474 := hb (x 0 10)
      have b10475 := hb (x 0 1 && x 0 10)
      clear * - r10473 b10474 b10475 d10463
      omega
    have d10476 : (x 3 8).toNat = 0 := by
      have r10477 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10478 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e10479 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e10480 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e10481 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e10482 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e10483 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b10484 := hb (x (-4) 7)
      have b10485 := hb (x (-3) 6)
      have b10486 := hb (x (-2) 5)
      have b10487 := hb (x (-1) 4)
      have b10488 := hb (x 0 11)
      have b10489 := hb (x 1 10)
      have b10490 := hb (x 2 9)
      have b10491 := hb (x 3 8)
      clear * - r10477 e10478 e10479 e10480 e10481 e10482 e10483 b10484 b10485 b10486 b10487 b10488 b10489 b10490 b10491 g17 d10459
      omega
    have d10492 : (x 2 9).toNat = 0 := by
      have r10493 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10494 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e10495 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e10496 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e10497 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e10498 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e10499 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b10500 := hb (x (-4) 7)
      have b10501 := hb (x (-3) 6)
      have b10502 := hb (x (-2) 5)
      have b10503 := hb (x (-1) 4)
      have b10504 := hb (x 0 11)
      have b10505 := hb (x 1 10)
      have b10506 := hb (x 2 9)
      have b10507 := hb (x 3 8)
      clear * - r10493 e10494 e10495 e10496 e10497 e10498 e10499 b10500 b10501 b10502 b10503 b10504 b10505 b10506 b10507 d10476 g17 d10459
      omega
    have d10508 : (x 2 9 && x 2 14).toNat = 0 := by
      have r10509 := hand1 (x 2 9) (x 2 14)
      have b10510 := hb (x 2 9)
      have b10511 := hb (x 2 9 && x 2 14)
      clear * - r10509 b10510 b10511 d10492
      omega
    have d10512 : (x 2 8).toNat = 0 := by
      have r10513 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10514 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e10515 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e10516 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e10517 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e10518 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e10519 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b10520 := hb (x (-5) 7)
      have b10521 := hb (x (-4) 6)
      have b10522 := hb (x (-3) 5)
      have b10523 := hb (x (-2) 4)
      have b10524 := hb (x (-1) 11)
      have b10525 := hb (x 0 10)
      have b10526 := hb (x 1 9)
      have b10527 := hb (x 2 8)
      clear * - r10513 e10514 e10515 e10516 e10517 e10518 e10519 b10520 b10521 b10522 b10523 b10524 b10525 b10526 b10527 d7682 d10472 g7
      omega
    have d10528 : (x (-2) 4).toNat = 0 := by
      have r10529 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10530 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e10531 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e10532 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e10533 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e10534 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e10535 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b10536 := hb (x (-5) 7)
      have b10537 := hb (x (-4) 6)
      have b10538 := hb (x (-3) 5)
      have b10539 := hb (x (-2) 4)
      have b10540 := hb (x (-1) 11)
      have b10541 := hb (x 0 10)
      have b10542 := hb (x 1 9)
      have b10543 := hb (x 2 8)
      clear * - r10529 e10530 e10531 e10532 e10533 e10534 e10535 b10536 b10537 b10538 b10539 b10540 b10541 b10542 b10543 d10512 d7682 d10472 g7
      omega
    have d10544 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
      have r10545 := hand1 (x (-2) 4) (x (-2) 8)
      have b10546 := hb (x (-2) 4)
      have b10547 := hb (x (-2) 4 && x (-2) 8)
      clear * - r10545 b10546 b10547 d10528
      omega
    have d10548 : (x (-3) 5).toNat = 0 := by
      have r10549 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10550 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e10551 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e10552 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e10553 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e10554 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e10555 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b10556 := hb (x (-5) 7)
      have b10557 := hb (x (-4) 6)
      have b10558 := hb (x (-3) 5)
      have b10559 := hb (x (-2) 4)
      have b10560 := hb (x (-1) 11)
      have b10561 := hb (x 0 10)
      have b10562 := hb (x 1 9)
      have b10563 := hb (x 2 8)
      clear * - r10549 e10550 e10551 e10552 e10553 e10554 e10555 b10556 b10557 b10558 b10559 b10560 b10561 b10562 b10563 d10512 d7682 d10472 g7 d10528
      omega
    have d10564 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
      have r10565 := hand1 (x (-3) 5) (x (-3) 9)
      have b10566 := hb (x (-3) 5)
      have b10567 := hb (x (-3) 5 && x (-3) 9)
      clear * - r10565 b10566 b10567 d10548
      omega
    have d10568 : (x (-4) 6).toNat = 0 := by
      have r10569 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10570 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e10571 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e10572 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e10573 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e10574 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e10575 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b10576 := hb (x (-5) 7)
      have b10577 := hb (x (-4) 6)
      have b10578 := hb (x (-3) 5)
      have b10579 := hb (x (-2) 4)
      have b10580 := hb (x (-1) 11)
      have b10581 := hb (x 0 10)
      have b10582 := hb (x 1 9)
      have b10583 := hb (x 2 8)
      clear * - r10569 e10570 e10571 e10572 e10573 e10574 e10575 b10576 b10577 b10578 b10579 b10580 b10581 b10582 b10583 d10512 d7682 d10472 g7 d10528 d10548
      omega
    have d10584 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
      have r10585 := hand1 (x (-4) 6) (x (-4) 10)
      have b10586 := hb (x (-4) 6)
      have b10587 := hb (x (-4) 6 && x (-4) 10)
      clear * - r10585 b10586 b10587 d10568
      omega
    have d10588 : (x (-5) 7).toNat = 0 := by
      have r10589 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10590 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e10591 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e10592 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e10593 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e10594 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e10595 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b10596 := hb (x (-5) 7)
      have b10597 := hb (x (-4) 6)
      have b10598 := hb (x (-3) 5)
      have b10599 := hb (x (-2) 4)
      have b10600 := hb (x (-1) 11)
      have b10601 := hb (x 0 10)
      have b10602 := hb (x 1 9)
      have b10603 := hb (x 2 8)
      clear * - r10589 e10590 e10591 e10592 e10593 e10594 e10595 b10596 b10597 b10598 b10599 b10600 b10601 b10602 b10603 d10512 d7682 d10472 g7 d10528 d10548 d10568
      omega
    have d10604 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
      have r10605 := hand1 (x (-5) 7) (x (-5) 11)
      have b10606 := hb (x (-5) 7)
      have b10607 := hb (x (-5) 7 && x (-5) 11)
      clear * - r10605 b10606 b10607 d10588
      omega
    cases h10608 : x 1 7
    · have f10609 : (x 1 7).toNat = 0 := by rw [h10608]; rfl
      have d10610 : (x (-7) 8).toNat = 1 := by
        have r10611 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10612 := hb (x (-7) 8)
        have b10613 := hb (x 1 7)
        have b10614 := hb (x 0 1 && x 0 8)
        have b10615 := hb (x (-1) 2 && x (-1) 9)
        have b10616 := hb (x (-2) 3 && x (-2) 10)
        have b10617 := hb (x (-3) 4 && x (-3) 11)
        have b10618 := hb (x (-4) 5 && x (-4) 12)
        have b10619 := hb (x (-5) 6 && x (-5) 13)
        have b10620 := hb (x (-6) 7 && x (-6) 14)
        clear * - r10611 b10612 b10613 b10614 b10615 b10616 b10617 b10618 b10619 b10620 f10609 g37 g38 d10378 g39 g40 g41 g42
        omega
      have d10621 : (x (-8) 9).toNat = 0 := by
        have r10622 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10623 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e10624 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e10625 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e10626 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e10627 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e10628 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b10629 := hb (x (-14) 7)
        have b10630 := hb (x (-13) 6)
        have b10631 := hb (x (-12) 5)
        have b10632 := hb (x (-11) 4)
        have b10633 := hb (x (-10) 11)
        have b10634 := hb (x (-9) 10)
        have b10635 := hb (x (-8) 9)
        have b10636 := hb (x (-7) 8)
        clear * - r10622 e10623 e10624 e10625 e10626 e10627 e10628 b10629 b10630 b10631 b10632 b10633 b10634 b10635 b10636 d10610
        omega
      have d10637 : (x (-8) 9 && x (-8) 14).toNat = 0 := by
        have r10638 := hand1 (x (-8) 9) (x (-8) 14)
        have b10639 := hb (x (-8) 9)
        have b10640 := hb (x (-8) 9 && x (-8) 14)
        clear * - r10638 b10639 b10640 d10621
        omega
      have d10641 : (x (-9) 10).toNat = 0 := by
        have r10642 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10643 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e10644 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e10645 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e10646 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e10647 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e10648 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b10649 := hb (x (-14) 7)
        have b10650 := hb (x (-13) 6)
        have b10651 := hb (x (-12) 5)
        have b10652 := hb (x (-11) 4)
        have b10653 := hb (x (-10) 11)
        have b10654 := hb (x (-9) 10)
        have b10655 := hb (x (-8) 9)
        have b10656 := hb (x (-7) 8)
        clear * - r10642 e10643 e10644 e10645 e10646 e10647 e10648 b10649 b10650 b10651 b10652 b10653 b10654 b10655 b10656 d10610 d10621
        omega
      have d10657 : (x (-10) 11).toNat = 0 := by
        have r10658 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10659 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e10660 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e10661 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e10662 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e10663 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e10664 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b10665 := hb (x (-14) 7)
        have b10666 := hb (x (-13) 6)
        have b10667 := hb (x (-12) 5)
        have b10668 := hb (x (-11) 4)
        have b10669 := hb (x (-10) 11)
        have b10670 := hb (x (-9) 10)
        have b10671 := hb (x (-8) 9)
        have b10672 := hb (x (-7) 8)
        clear * - r10658 e10659 e10660 e10661 e10662 e10663 e10664 b10665 b10666 b10667 b10668 b10669 b10670 b10671 b10672 d10610 d10621 d10641
        omega
      have d10673 : (x (-11) 4).toNat = 0 := by
        have r10674 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10675 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e10676 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e10677 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e10678 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e10679 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e10680 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b10681 := hb (x (-14) 7)
        have b10682 := hb (x (-13) 6)
        have b10683 := hb (x (-12) 5)
        have b10684 := hb (x (-11) 4)
        have b10685 := hb (x (-10) 11)
        have b10686 := hb (x (-9) 10)
        have b10687 := hb (x (-8) 9)
        have b10688 := hb (x (-7) 8)
        clear * - r10674 e10675 e10676 e10677 e10678 e10679 e10680 b10681 b10682 b10683 b10684 b10685 b10686 b10687 b10688 d10610 d10621 d10641 d10657
        omega
      have d10689 : (x (-11) 4 && x (-11) 14).toNat = 0 := by
        have r10690 := hand1 (x (-11) 4) (x (-11) 14)
        have b10691 := hb (x (-11) 4)
        have b10692 := hb (x (-11) 4 && x (-11) 14)
        clear * - r10690 b10691 b10692 d10673
        omega
      have d10693 : (x (-12) 5).toNat = 0 := by
        have r10694 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10695 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e10696 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e10697 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e10698 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e10699 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e10700 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have b10701 := hb (x (-14) 7)
        have b10702 := hb (x (-13) 6)
        have b10703 := hb (x (-12) 5)
        have b10704 := hb (x (-11) 4)
        have b10705 := hb (x (-10) 11)
        have b10706 := hb (x (-9) 10)
        have b10707 := hb (x (-8) 9)
        have b10708 := hb (x (-7) 8)
        clear * - r10694 e10695 e10696 e10697 e10698 e10699 e10700 b10701 b10702 b10703 b10704 b10705 b10706 b10707 b10708 d10610 d10621 d10641 d10657 d10673
        omega
      have d10709 : (x (-7) 8 && x (-7) 14).toNat = 1 := by
        have r10710 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10711 := hb (x (-8) 9)
        have b10712 := hb (x 1 6)
        have b10713 := hb (x 0 1 && x 0 7)
        have b10714 := hb (x (-1) 2 && x (-1) 8)
        have b10715 := hb (x (-2) 3 && x (-2) 9)
        have b10716 := hb (x (-3) 4 && x (-3) 10)
        have b10717 := hb (x (-4) 5 && x (-4) 11)
        have b10718 := hb (x (-5) 6 && x (-5) 12)
        have b10719 := hb (x (-6) 7 && x (-6) 13)
        have b10720 := hb (x (-7) 8 && x (-7) 14)
        clear * - r10710 b10711 b10712 b10713 b10714 b10715 b10716 b10717 b10718 b10719 b10720 g15 d7830 d10407 d10427 g33 g34 g35 g36 d10621
        omega
      have d10721 : (x (-7) 14).toNat = 1 := by
        have r10722 := hand2 (x (-7) 8) (x (-7) 14)
        have b10723 := hb (x (-7) 14)
        have b10724 := hb (x (-7) 8 && x (-7) 14)
        clear * - r10722 b10723 b10724 d10709
        omega
      have d10725 : (x (-8) 1).toNat = 0 := by
        have r10726 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10727 := hb (x (-8) 1)
        have b10728 := hb (x (-7) 14)
        clear * - r10726 b10727 b10728 d10721
        omega
      have d10729 : (x (-8) 1 && x (-8) 11).toNat = 0 := by
        have r10730 := hand1 (x (-8) 1) (x (-8) 11)
        have b10731 := hb (x (-8) 1)
        have b10732 := hb (x (-8) 1 && x (-8) 11)
        clear * - r10730 b10731 b10732 d10725
        omega
      have d10733 : (x (-8) 13).toNat = 0 := by
        have r10734 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b10735 := hb (x (-8) 1)
        have b10736 := hb (x (-8) 13)
        clear * - r10734 b10735 b10736 d10725
        omega
      have d10737 : (x (-7) 8 && x (-7) 13).toNat = 1 := by
        have r10738 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10739 := hb (x (-9) 10)
        have b10740 := hb (x 1 5)
        have b10741 := hb (x 0 1 && x 0 6)
        have b10742 := hb (x (-1) 2 && x (-1) 7)
        have b10743 := hb (x (-2) 3 && x (-2) 8)
        have b10744 := hb (x (-3) 4 && x (-3) 9)
        have b10745 := hb (x (-4) 5 && x (-4) 10)
        have b10746 := hb (x (-5) 6 && x (-5) 11)
        have b10747 := hb (x (-6) 7 && x (-6) 12)
        have b10748 := hb (x (-7) 8 && x (-7) 13)
        have b10749 := hb (x (-8) 9 && x (-8) 14)
        clear * - r10738 b10739 b10740 b10741 b10742 b10743 b10744 b10745 b10746 b10747 b10748 b10749 g14 d7890 d7918 d10431 g27 g28 g29 g30 d10637 d10641
        omega
      have d10750 : (x (-7) 13).toNat = 1 := by
        have r10751 := hand2 (x (-7) 8) (x (-7) 13)
        have b10752 := hb (x (-7) 13)
        have b10753 := hb (x (-7) 8 && x (-7) 13)
        clear * - r10751 b10752 b10753 d10737
        omega
      have d10754 : (x (-7) 1).toNat = 1 := by
        have r10755 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
        have b10756 := hb (x (-7) 1)
        have b10757 := hb (x (-7) 13)
        clear * - r10755 b10756 b10757 d10750
        omega
      have d10758 : (x (-6) 14).toNat = 0 := by
        have r10759 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10760 := hb (x (-7) 1)
        have b10761 := hb (x (-6) 14)
        clear * - r10759 b10760 b10761 d10754
        omega
      have d10762 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
        have r10763 := hand2 (x (-6) 3) (x (-6) 14)
        have b10764 := hb (x (-6) 14)
        have b10765 := hb (x (-6) 3 && x (-6) 14)
        clear * - r10763 b10764 b10765 d10758
        omega
      have d10766 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
        have r10767 := hand2 (x (-6) 5) (x (-6) 14)
        have b10768 := hb (x (-6) 14)
        have b10769 := hb (x (-6) 5 && x (-6) 14)
        clear * - r10767 b10768 b10769 d10758
        omega
      have d10770 : (x (-6) 2).toNat = 0 := by
        have r10771 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
        have b10772 := hb (x (-6) 2)
        have b10773 := hb (x (-6) 14)
        clear * - r10771 b10772 b10773 d10758
        omega
      have d10774 : (x (-6) 10).toNat = 0 := by
        have r10775 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have b10776 := hb (x (-6) 2)
        have b10777 := hb (x (-6) 10)
        clear * - r10775 b10776 b10777 d10770
        omega
      have d10778 : (x (-6) 12).toNat = 0 := by
        have r10779 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10780 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e10781 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b10782 := hb (x (-9) 3)
        have b10783 := hb (x (-8) 2)
        have b10784 := hb (x (-7) 13)
        have b10785 := hb (x (-6) 12)
        clear * - r10779 e10780 e10781 b10782 b10783 b10784 b10785 d10750
        omega
      have d10786 : (x (-6) 8 && x (-6) 12).toNat = 0 := by
        have r10787 := hand2 (x (-6) 8) (x (-6) 12)
        have b10788 := hb (x (-6) 12)
        have b10789 := hb (x (-6) 8 && x (-6) 12)
        clear * - r10787 b10788 b10789 d10778
        omega
      have d10790 : (x (-8) 2).toNat = 0 := by
        have r10791 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10792 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e10793 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b10794 := hb (x (-9) 3)
        have b10795 := hb (x (-8) 2)
        have b10796 := hb (x (-7) 13)
        have b10797 := hb (x (-6) 12)
        clear * - r10791 e10792 e10793 b10794 b10795 b10796 b10797 d10778 d10750
        omega
      have d10798 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
        have r10799 := hand1 (x (-8) 2) (x (-8) 12)
        have b10800 := hb (x (-8) 2)
        have b10801 := hb (x (-8) 2 && x (-8) 12)
        clear * - r10799 b10800 b10801 d10790
        omega
      have d10802 : (x (-8) 10).toNat = 0 := by
        have r10803 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
        have b10804 := hb (x (-8) 2)
        have b10805 := hb (x (-8) 10)
        clear * - r10803 b10804 b10805 d10790
        omega
      have d10806 : (x (-9) 3).toNat = 0 := by
        have r10807 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10808 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e10809 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b10810 := hb (x (-9) 3)
        have b10811 := hb (x (-8) 2)
        have b10812 := hb (x (-7) 13)
        have b10813 := hb (x (-6) 12)
        clear * - r10807 e10808 e10809 b10810 b10811 b10812 b10813 d10778 d10750 d10790
        omega
      have d10814 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
        have r10815 := hand1 (x (-9) 3) (x (-9) 13)
        have b10816 := hb (x (-9) 3)
        have b10817 := hb (x (-9) 3 && x (-9) 13)
        clear * - r10815 b10816 b10817 d10806
        omega
      have d10818 : (x (-9) 11).toNat = 0 := by
        have r10819 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
        have b10820 := hb (x (-9) 3)
        have b10821 := hb (x (-9) 11)
        clear * - r10819 b10820 b10821 d10806
        omega
      have d10822 : (x (-7) 9 && x (-7) 13).toNat = 1 := by
        have r10823 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10824 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
        have e10825 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
        have b10826 := hb (x (-9) 11)
        have b10827 := hb (x (-8) 10)
        have b10828 := hb (x 1 5)
        have b10829 := hb (x 2 4)
        have b10830 := hb (x 0 2 && x 0 6)
        have b10831 := hb (x (-1) 3 && x (-1) 7)
        have b10832 := hb (x (-2) 4 && x (-2) 8)
        have b10833 := hb (x (-3) 5 && x (-3) 9)
        have b10834 := hb (x (-4) 6 && x (-4) 10)
        have b10835 := hb (x (-5) 7 && x (-5) 11)
        have b10836 := hb (x (-6) 8 && x (-6) 12)
        have b10837 := hb (x (-7) 9 && x (-7) 13)
        clear * - r10823 e10824 e10825 b10826 b10827 b10828 b10829 b10830 b10831 b10832 b10833 b10834 b10835 b10836 b10837 g18 g14 d7894 g21 d10544 d10564 d10584 d10604 d10786 d10802 d10818
        omega
      have d10838 : (x (-7) 9).toNat = 1 := by
        have r10839 := hand1 (x (-7) 9) (x (-7) 13)
        have b10840 := hb (x (-7) 9)
        have b10841 := hb (x (-7) 9 && x (-7) 13)
        clear * - r10839 b10840 b10841 d10822
        omega
      have d10842 : (x (-6) 8).toNat = 0 := by
        have r10843 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10844 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e10845 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e10846 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e10847 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e10848 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e10849 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have b10850 := hb (x (-13) 7)
        have b10851 := hb (x (-12) 6)
        have b10852 := hb (x (-11) 5)
        have b10853 := hb (x (-10) 4)
        have b10854 := hb (x (-9) 11)
        have b10855 := hb (x (-8) 10)
        have b10856 := hb (x (-7) 9)
        have b10857 := hb (x (-6) 8)
        clear * - r10843 e10844 e10845 e10846 e10847 e10848 e10849 b10850 b10851 b10852 b10853 b10854 b10855 b10856 b10857 d10838 d10802 d10818
        omega
      have d10858 : (x (-10) 4).toNat = 0 := by
        have r10859 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10860 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e10861 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e10862 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e10863 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e10864 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e10865 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have b10866 := hb (x (-13) 7)
        have b10867 := hb (x (-12) 6)
        have b10868 := hb (x (-11) 5)
        have b10869 := hb (x (-10) 4)
        have b10870 := hb (x (-9) 11)
        have b10871 := hb (x (-8) 10)
        have b10872 := hb (x (-7) 9)
        have b10873 := hb (x (-6) 8)
        clear * - r10859 e10860 e10861 e10862 e10863 e10864 e10865 b10866 b10867 b10868 b10869 b10870 b10871 b10872 b10873 d10842 d10838 d10802 d10818
        omega
      have d10874 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
        have r10875 := hand1 (x (-10) 4) (x (-10) 14)
        have b10876 := hb (x (-10) 4)
        have b10877 := hb (x (-10) 4 && x (-10) 14)
        clear * - r10875 b10876 b10877 d10858
        omega
      have d10878 : (x (-11) 5).toNat = 0 := by
        have r10879 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10880 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
        have e10881 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
        have e10882 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
        have e10883 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
        have e10884 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
        have e10885 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
        have b10886 := hb (x (-13) 7)
        have b10887 := hb (x (-12) 6)
        have b10888 := hb (x (-11) 5)
        have b10889 := hb (x (-10) 4)
        have b10890 := hb (x (-9) 11)
        have b10891 := hb (x (-8) 10)
        have b10892 := hb (x (-7) 9)
        have b10893 := hb (x (-6) 8)
        clear * - r10879 e10880 e10881 e10882 e10883 e10884 e10885 b10886 b10887 b10888 b10889 b10890 b10891 b10892 b10893 d10842 d10838 d10802 d10818 d10858
        omega
      have d10894 : (x (-7) 1 && x (-7) 11).toNat = 1 := by
        have r10895 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10896 := hb (x (-11) 5)
        have b10897 := hb (x (-6) 10)
        have b10898 := hb (x (-7) 1 && x (-7) 11)
        have b10899 := hb (x (-8) 2 && x (-8) 12)
        have b10900 := hb (x (-9) 3 && x (-9) 13)
        have b10901 := hb (x (-10) 4 && x (-10) 14)
        clear * - r10895 b10896 b10897 b10898 b10899 b10900 b10901 d10774 d10798 d10814 d10874 d10878
        omega
      have d10902 : (x (-7) 11).toNat = 1 := by
        have r10903 := hand2 (x (-7) 1) (x (-7) 11)
        have b10904 := hb (x (-7) 11)
        have b10905 := hb (x (-7) 1 && x (-7) 11)
        clear * - r10903 b10904 b10905 d10894
        omega
      have d10906 : (x (-7) 3).toNat = 1 := by
        have r10907 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have b10908 := hb (x (-7) 3)
        have b10909 := hb (x (-7) 11)
        clear * - r10907 b10908 b10909 d10902
        omega
      have d10910 : (x (-4) 12).toNat = 0 := by
        have r10911 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10912 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e10913 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b10914 := hb (x (-7) 3)
        have b10915 := hb (x (-6) 2)
        have b10916 := hb (x (-5) 13)
        have b10917 := hb (x (-4) 12)
        clear * - r10911 e10912 e10913 b10914 b10915 b10916 b10917 d10770 d10906
        omega
      have d10918 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
        have r10919 := hand2 (x (-4) 1) (x (-4) 12)
        have b10920 := hb (x (-4) 12)
        have b10921 := hb (x (-4) 1 && x (-4) 12)
        clear * - r10919 b10920 b10921 d10910
        omega
      have d10922 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
        have r10923 := hand2 (x (-4) 3) (x (-4) 12)
        have b10924 := hb (x (-4) 12)
        have b10925 := hb (x (-4) 3 && x (-4) 12)
        clear * - r10923 b10924 b10925 d10910
        omega
      have d10926 : (x (-5) 13).toNat = 0 := by
        have r10927 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10928 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e10929 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b10930 := hb (x (-7) 3)
        have b10931 := hb (x (-6) 2)
        have b10932 := hb (x (-5) 13)
        have b10933 := hb (x (-4) 12)
        clear * - r10927 e10928 e10929 b10930 b10931 b10932 b10933 d10910 d10770 d10906
        omega
      have d10934 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
        have r10935 := hand2 (x (-5) 2) (x (-5) 13)
        have b10936 := hb (x (-5) 13)
        have b10937 := hb (x (-5) 2 && x (-5) 13)
        clear * - r10935 b10936 b10937 d10926
        omega
      have d10938 : (x (-7) 4).toNat = 1 := by
        have r10939 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10940 := hb (x (-7) 4)
        have b10941 := hb (x (-3) 11)
        have b10942 := hb (x (-4) 1 && x (-4) 12)
        have b10943 := hb (x (-5) 2 && x (-5) 13)
        have b10944 := hb (x (-6) 3 && x (-6) 14)
        clear * - r10939 b10940 b10941 b10942 b10943 b10944 d10443 d10918 d10934 d10762
        omega
      have d10945 : (x (-7) 12).toNat = 1 := by
        have r10946 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
        have b10947 := hb (x (-7) 4)
        have b10948 := hb (x (-7) 12)
        clear * - r10946 b10947 b10948 d10938
        omega
      have d10949 : (x (-9) 2).toNat = 0 := by
        have r10950 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10951 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e10952 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b10953 := hb (x (-10) 3)
        have b10954 := hb (x (-9) 2)
        have b10955 := hb (x (-8) 13)
        have b10956 := hb (x (-7) 12)
        clear * - r10950 e10951 e10952 b10953 b10954 b10955 b10956 d10945 d10733
        omega
      have d10957 : (x (-9) 2 && x (-9) 12).toNat = 0 := by
        have r10958 := hand1 (x (-9) 2) (x (-9) 12)
        have b10959 := hb (x (-9) 2)
        have b10960 := hb (x (-9) 2 && x (-9) 12)
        clear * - r10958 b10959 b10960 d10949
        omega
      have d10961 : (x (-10) 3).toNat = 0 := by
        have r10962 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10963 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e10964 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b10965 := hb (x (-10) 3)
        have b10966 := hb (x (-9) 2)
        have b10967 := hb (x (-8) 13)
        have b10968 := hb (x (-7) 12)
        clear * - r10962 e10963 e10964 b10965 b10966 b10967 b10968 d10945 d10733 d10949
        omega
      have d10969 : (x (-10) 3 && x (-10) 13).toNat = 0 := by
        have r10970 := hand1 (x (-10) 3) (x (-10) 13)
        have b10971 := hb (x (-10) 3)
        have b10972 := hb (x (-10) 3 && x (-10) 13)
        clear * - r10970 b10971 b10972 d10961
        omega
      have d10973 : (x (-7) 10).toNat = 1 := by
        have r10974 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10975 := hb (x (-12) 5)
        have b10976 := hb (x (-7) 10)
        have b10977 := hb (x (-8) 1 && x (-8) 11)
        have b10978 := hb (x (-9) 2 && x (-9) 12)
        have b10979 := hb (x (-10) 3 && x (-10) 13)
        have b10980 := hb (x (-11) 4 && x (-11) 14)
        clear * - r10974 b10975 b10976 b10977 b10978 b10979 b10980 d10729 d10957 d10969 d10689 d10693
        omega
      have d10981 : (x (-7) 2).toNat = 1 := by
        have r10982 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
        have b10983 := hb (x (-7) 2)
        have b10984 := hb (x (-7) 10)
        clear * - r10982 b10983 b10984 d10973
        omega
      have d10985 : (x (-5) 12).toNat = 0 := by
        have r10986 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10987 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e10988 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b10989 := hb (x (-8) 3)
        have b10990 := hb (x (-7) 2)
        have b10991 := hb (x (-6) 13)
        have b10992 := hb (x (-5) 12)
        clear * - r10986 e10987 e10988 b10989 b10990 b10991 b10992 d10981
        omega
      have d10993 : (x (-5) 4).toNat = 0 := by
        have r10994 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have b10995 := hb (x (-5) 4)
        have b10996 := hb (x (-5) 12)
        clear * - r10994 b10995 b10996 d10985
        omega
      have d10997 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
        have r10998 := hand1 (x (-5) 4) (x (-5) 14)
        have b10999 := hb (x (-5) 4)
        have b11000 := hb (x (-5) 4 && x (-5) 14)
        clear * - r10998 b10999 b11000 d10993
        omega
      have d11001 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
        have r11002 := hand1 (x (-5) 4) (x (-5) 13)
        have b11003 := hb (x (-5) 4)
        have b11004 := hb (x (-5) 4 && x (-5) 13)
        clear * - r11002 b11003 b11004 d10993
        omega
      have d11005 : (x (-7) 6).toNat = 1 := by
        have r11006 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b11007 := hb (x (-7) 6)
        have b11008 := hb (x (-1) 9)
        have b11009 := hb (x (-2) 1 && x (-2) 10)
        have b11010 := hb (x (-3) 2 && x (-3) 11)
        have b11011 := hb (x (-4) 3 && x (-4) 12)
        have b11012 := hb (x (-5) 4 && x (-5) 13)
        have b11013 := hb (x (-6) 5 && x (-6) 14)
        clear * - r11006 b11007 b11008 b11009 b11010 b11011 b11012 b11013 g5 d10374 d10447 d10922 d11001 d10766
        omega
      have d11014 : (x (-1) 8).toNat = 0 := by
        have r11015 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11016 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e11017 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e11018 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e11019 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e11020 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e11021 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b11022 := hb (x (-8) 7)
        have b11023 := hb (x (-7) 6)
        have b11024 := hb (x (-6) 5)
        have b11025 := hb (x (-5) 4)
        have b11026 := hb (x (-4) 11)
        have b11027 := hb (x (-3) 10)
        have b11028 := hb (x (-2) 9)
        have b11029 := hb (x (-1) 8)
        clear * - r11015 e11016 e11017 e11018 e11019 e11020 e11021 b11022 b11023 b11024 b11025 b11026 b11027 b11028 b11029 d10993 d11005
        omega
      have d11030 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
        have r11031 := hand1 (x (-1) 8) (x (-1) 12)
        have b11032 := hb (x (-1) 8)
        have b11033 := hb (x (-1) 8 && x (-1) 12)
        clear * - r11031 b11032 b11033 d11014
        omega
      have d11034 : (x (-2) 9).toNat = 0 := by
        have r11035 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11036 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e11037 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e11038 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e11039 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e11040 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e11041 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b11042 := hb (x (-8) 7)
        have b11043 := hb (x (-7) 6)
        have b11044 := hb (x (-6) 5)
        have b11045 := hb (x (-5) 4)
        have b11046 := hb (x (-4) 11)
        have b11047 := hb (x (-3) 10)
        have b11048 := hb (x (-2) 9)
        have b11049 := hb (x (-1) 8)
        clear * - r11035 e11036 e11037 e11038 e11039 e11040 e11041 b11042 b11043 b11044 b11045 b11046 b11047 b11048 b11049 d11014 d10993 d11005
        omega
      have d11050 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
        have r11051 := hand1 (x (-2) 9) (x (-2) 13)
        have b11052 := hb (x (-2) 9)
        have b11053 := hb (x (-2) 9 && x (-2) 13)
        clear * - r11051 b11052 b11053 d11034
        omega
      have d11054 : (x (-3) 10).toNat = 0 := by
        have r11055 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11056 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e11057 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e11058 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e11059 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e11060 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e11061 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b11062 := hb (x (-8) 7)
        have b11063 := hb (x (-7) 6)
        have b11064 := hb (x (-6) 5)
        have b11065 := hb (x (-5) 4)
        have b11066 := hb (x (-4) 11)
        have b11067 := hb (x (-3) 10)
        have b11068 := hb (x (-2) 9)
        have b11069 := hb (x (-1) 8)
        clear * - r11055 e11056 e11057 e11058 e11059 e11060 e11061 b11062 b11063 b11064 b11065 b11066 b11067 b11068 b11069 d11014 d11034 d10993 d11005
        omega
      have d11070 : (x (-4) 11).toNat = 0 := by
        have r11071 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11072 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e11073 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e11074 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e11075 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e11076 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e11077 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b11078 := hb (x (-8) 7)
        have b11079 := hb (x (-7) 6)
        have b11080 := hb (x (-6) 5)
        have b11081 := hb (x (-5) 4)
        have b11082 := hb (x (-4) 11)
        have b11083 := hb (x (-3) 10)
        have b11084 := hb (x (-2) 9)
        have b11085 := hb (x (-1) 8)
        clear * - r11071 e11072 e11073 e11074 e11075 e11076 e11077 b11078 b11079 b11080 b11081 b11082 b11083 b11084 b11085 d11014 d11034 d11054 d10993 d11005
        omega
      have d11086 : (x (-6) 5).toNat = 0 := by
        have r11087 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11088 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e11089 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e11090 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e11091 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e11092 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e11093 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b11094 := hb (x (-8) 7)
        have b11095 := hb (x (-7) 6)
        have b11096 := hb (x (-6) 5)
        have b11097 := hb (x (-5) 4)
        have b11098 := hb (x (-4) 11)
        have b11099 := hb (x (-3) 10)
        have b11100 := hb (x (-2) 9)
        have b11101 := hb (x (-1) 8)
        clear * - r11087 e11088 e11089 e11090 e11091 e11092 e11093 b11094 b11095 b11096 b11097 b11098 b11099 b11100 b11101 d11014 d11034 d11054 d11070 d10993 d11005
        omega
      have d11102 : (x 4 3 && x 4 7).toNat = 1 := by
        have r11103 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11104 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
        have e11105 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
        have b11106 := hb (x (-4) 11)
        have b11107 := hb (x (-3) 10)
        have b11108 := hb (x 6 5)
        have b11109 := hb (x 7 4)
        have b11110 := hb (x 5 2 && x 5 6)
        have b11111 := hb (x 4 3 && x 4 7)
        have b11112 := hb (x 3 4 && x 3 8)
        have b11113 := hb (x 2 5 && x 2 9)
        have b11114 := hb (x 1 6 && x 1 10)
        have b11115 := hb (x 0 7 && x 0 11)
        have b11116 := hb (x (-1) 8 && x (-1) 12)
        have b11117 := hb (x (-2) 9 && x (-2) 13)
        clear * - r11103 e11104 e11105 b11106 b11107 b11108 b11109 b11110 b11111 b11112 b11113 b11114 b11115 b11116 b11117 d7536 d7568 d7588 g22 g23 g24 d7834 d11030 d11050 d11054 d11070
        omega
      have d11118 : (x 4 7).toNat = 1 := by
        have r11119 := hand2 (x 4 3) (x 4 7)
        have b11120 := hb (x 4 7)
        have b11121 := hb (x 4 3 && x 4 7)
        clear * - r11119 b11120 b11121 d11102
        omega
      have d11122 : (x 11 8).toNat = 0 := by
        have r11123 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11124 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e11125 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e11126 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e11127 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e11128 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e11129 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b11130 := hb (x 4 7)
        have b11131 := hb (x 5 6)
        have b11132 := hb (x 6 5)
        have b11133 := hb (x 7 4)
        have b11134 := hb (x 8 11)
        have b11135 := hb (x 9 10)
        have b11136 := hb (x 10 9)
        have b11137 := hb (x 11 8)
        clear * - r11123 e11124 e11125 e11126 e11127 e11128 e11129 b11130 b11131 b11132 b11133 b11134 b11135 b11136 b11137 d7536 d7568 d7762 d11118
        omega
      have d11138 : (x 10 9).toNat = 0 := by
        have r11139 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11140 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e11141 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e11142 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e11143 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e11144 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e11145 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b11146 := hb (x 4 7)
        have b11147 := hb (x 5 6)
        have b11148 := hb (x 6 5)
        have b11149 := hb (x 7 4)
        have b11150 := hb (x 8 11)
        have b11151 := hb (x 9 10)
        have b11152 := hb (x 10 9)
        have b11153 := hb (x 11 8)
        clear * - r11139 e11140 e11141 e11142 e11143 e11144 e11145 b11146 b11147 b11148 b11149 b11150 b11151 b11152 b11153 d11122 d7536 d7568 d7762 d11118
        omega
      have d11154 : (x 9 10).toNat = 0 := by
        have r11155 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11156 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e11157 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e11158 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e11159 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e11160 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e11161 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b11162 := hb (x 4 7)
        have b11163 := hb (x 5 6)
        have b11164 := hb (x 6 5)
        have b11165 := hb (x 7 4)
        have b11166 := hb (x 8 11)
        have b11167 := hb (x 9 10)
        have b11168 := hb (x 10 9)
        have b11169 := hb (x 11 8)
        clear * - r11155 e11156 e11157 e11158 e11159 e11160 e11161 b11162 b11163 b11164 b11165 b11166 b11167 b11168 b11169 d11122 d11138 d7536 d7568 d7762 d11118
        omega
      have d11170 : (x 9 1 && x 9 10).toNat = 0 := by
        have r11171 := hand2 (x 9 1) (x 9 10)
        have b11172 := hb (x 9 10)
        have b11173 := hb (x 9 1 && x 9 10)
        clear * - r11171 b11172 b11173 d11154
        omega
      have d11174 : (x 8 11).toNat = 0 := by
        have r11175 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11176 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e11177 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e11178 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e11179 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e11180 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e11181 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b11182 := hb (x 4 7)
        have b11183 := hb (x 5 6)
        have b11184 := hb (x 6 5)
        have b11185 := hb (x 7 4)
        have b11186 := hb (x 8 11)
        have b11187 := hb (x 9 10)
        have b11188 := hb (x 10 9)
        have b11189 := hb (x 11 8)
        clear * - r11175 e11176 e11177 e11178 e11179 e11180 e11181 b11182 b11183 b11184 b11185 b11186 b11187 b11188 b11189 d11122 d11138 d11154 d7536 d7568 d7762 d11118
        omega
      have d11190 : (x 8 1 && x 8 11).toNat = 0 := by
        have r11191 := hand2 (x 8 1) (x 8 11)
        have b11192 := hb (x 8 11)
        have b11193 := hb (x 8 1 && x 8 11)
        clear * - r11191 b11192 b11193 d11174
        omega
      have d11194 : (x 4 5).toNat = 1 := by
        have r11195 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b11196 := hb (x 4 5)
        have b11197 := hb (x 9 10)
        have b11198 := hb (x 8 1 && x 8 11)
        have b11199 := hb (x 7 2 && x 7 12)
        have b11200 := hb (x 6 3 && x 6 13)
        have b11201 := hb (x 5 4 && x 5 14)
        clear * - r11195 b11196 b11197 b11198 b11199 b11200 b11201 d11154 d11190 d7528 d7560 d7758
        omega
      have d11202 : (x 4 13).toNat = 1 := by
        have r11203 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
        have b11204 := hb (x 4 5)
        have b11205 := hb (x 4 13)
        clear * - r11203 b11204 b11205 d11194
        omega
      have d11206 : (x 5 12).toNat = 0 := by
        have r11207 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11208 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e11209 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b11210 := hb (x 2 3)
        have b11211 := hb (x 3 2)
        have b11212 := hb (x 4 13)
        have b11213 := hb (x 5 12)
        clear * - r11207 e11208 e11209 b11210 b11211 b11212 b11213 d11202 d7702
        omega
      have d11214 : (x 5 4).toNat = 0 := by
        have r11215 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b11216 := hb (x 5 4)
        have b11217 := hb (x 5 12)
        clear * - r11215 b11216 b11217 d11206
        omega
      have d11218 : (x 9 8).toNat = 0 := by
        have r11219 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11220 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e11221 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e11222 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e11223 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e11224 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e11225 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b11226 := hb (x 2 7)
        have b11227 := hb (x 3 6)
        have b11228 := hb (x 4 5)
        have b11229 := hb (x 5 4)
        have b11230 := hb (x 6 11)
        have b11231 := hb (x 7 10)
        have b11232 := hb (x 8 9)
        have b11233 := hb (x 9 8)
        clear * - r11219 e11220 e11221 e11222 e11223 e11224 e11225 b11226 b11227 b11228 b11229 b11230 b11231 b11232 b11233 d11214 d11194 d7698
        omega
      have d11234 : (x 8 9).toNat = 0 := by
        have r11235 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11236 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e11237 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e11238 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e11239 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e11240 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e11241 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b11242 := hb (x 2 7)
        have b11243 := hb (x 3 6)
        have b11244 := hb (x 4 5)
        have b11245 := hb (x 5 4)
        have b11246 := hb (x 6 11)
        have b11247 := hb (x 7 10)
        have b11248 := hb (x 8 9)
        have b11249 := hb (x 9 8)
        clear * - r11235 e11236 e11237 e11238 e11239 e11240 e11241 b11242 b11243 b11244 b11245 b11246 b11247 b11248 b11249 d11218 d11214 d11194 d7698
        omega
      have d11250 : (x 7 10).toNat = 0 := by
        have r11251 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11252 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e11253 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e11254 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e11255 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e11256 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e11257 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b11258 := hb (x 2 7)
        have b11259 := hb (x 3 6)
        have b11260 := hb (x 4 5)
        have b11261 := hb (x 5 4)
        have b11262 := hb (x 6 11)
        have b11263 := hb (x 7 10)
        have b11264 := hb (x 8 9)
        have b11265 := hb (x 9 8)
        clear * - r11251 e11252 e11253 e11254 e11255 e11256 e11257 b11258 b11259 b11260 b11261 b11262 b11263 b11264 b11265 d11218 d11234 d11214 d11194 d7698
        omega
      have d11266 : (x 6 11).toNat = 0 := by
        have r11267 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11268 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e11269 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e11270 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e11271 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e11272 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e11273 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b11274 := hb (x 2 7)
        have b11275 := hb (x 3 6)
        have b11276 := hb (x 4 5)
        have b11277 := hb (x 5 4)
        have b11278 := hb (x 6 11)
        have b11279 := hb (x 7 10)
        have b11280 := hb (x 8 9)
        have b11281 := hb (x 9 8)
        clear * - r11267 e11268 e11269 e11270 e11271 e11272 e11273 b11274 b11275 b11276 b11277 b11278 b11279 b11280 b11281 d11218 d11234 d11250 d11214 d11194 d7698
        omega
      have d11282 : (x 2 7).toNat = 0 := by
        have r11283 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11284 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e11285 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e11286 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e11287 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e11288 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e11289 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b11290 := hb (x 2 7)
        have b11291 := hb (x 3 6)
        have b11292 := hb (x 4 5)
        have b11293 := hb (x 5 4)
        have b11294 := hb (x 6 11)
        have b11295 := hb (x 7 10)
        have b11296 := hb (x 8 9)
        have b11297 := hb (x 9 8)
        clear * - r11283 e11284 e11285 e11286 e11287 e11288 e11289 b11290 b11291 b11292 b11293 b11294 b11295 b11296 b11297 d11218 d11234 d11250 d11266 d11214 d11194 d7698
        omega
      have d11298 : (x 8 2 && x 8 11).toNat = 0 := by
        have r11299 := hand2 (x 8 2) (x 8 11)
        have b11300 := hb (x 8 11)
        have b11301 := hb (x 8 2 && x 8 11)
        clear * - r11299 b11300 b11301 d11174
        omega
      have d11302 : (x 4 6).toNat = 1 := by
        have r11303 : 1 ≤ (x 10 9).toNat + (x 9 1 && x 9 10).toNat + (x 8 2 && x 8 11).toNat + (x 7 3 && x 7 12).toNat + (x 6 4 && x 6 13).toNat + (x 5 5 && x 5 14).toNat + (x 4 6).toNat := by have q := hcov9 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b11304 := hb (x 4 6)
        have b11305 := hb (x 10 9)
        have b11306 := hb (x 9 1 && x 9 10)
        have b11307 := hb (x 8 2 && x 8 11)
        have b11308 := hb (x 7 3 && x 7 12)
        have b11309 := hb (x 6 4 && x 6 13)
        have b11310 := hb (x 5 5 && x 5 14)
        clear * - r11303 b11304 b11305 b11306 b11307 b11308 b11309 b11310 d11138 d11170 d11298 d7532 d7564 d7734
        omega
      have d11311 : (x 10 8).toNat = 0 := by
        have r11312 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11313 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e11314 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e11315 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e11316 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e11317 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e11318 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b11319 := hb (x 3 7)
        have b11320 := hb (x 4 6)
        have b11321 := hb (x 5 5)
        have b11322 := hb (x 6 4)
        have b11323 := hb (x 7 11)
        have b11324 := hb (x 8 10)
        have b11325 := hb (x 9 9)
        have b11326 := hb (x 10 8)
        clear * - r11312 e11313 e11314 e11315 e11316 e11317 e11318 b11319 b11320 b11321 b11322 b11323 b11324 b11325 b11326 d7718 d7730 d11302
        omega
      have d11327 : (x 9 9).toNat = 0 := by
        have r11328 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11329 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e11330 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e11331 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e11332 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e11333 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e11334 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b11335 := hb (x 3 7)
        have b11336 := hb (x 4 6)
        have b11337 := hb (x 5 5)
        have b11338 := hb (x 6 4)
        have b11339 := hb (x 7 11)
        have b11340 := hb (x 8 10)
        have b11341 := hb (x 9 9)
        have b11342 := hb (x 10 8)
        clear * - r11328 e11329 e11330 e11331 e11332 e11333 e11334 b11335 b11336 b11337 b11338 b11339 b11340 b11341 b11342 d11311 d7718 d7730 d11302
        omega
      have d11343 : (x 8 10).toNat = 0 := by
        have r11344 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11345 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e11346 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e11347 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e11348 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e11349 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e11350 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b11351 := hb (x 3 7)
        have b11352 := hb (x 4 6)
        have b11353 := hb (x 5 5)
        have b11354 := hb (x 6 4)
        have b11355 := hb (x 7 11)
        have b11356 := hb (x 8 10)
        have b11357 := hb (x 9 9)
        have b11358 := hb (x 10 8)
        clear * - r11344 e11345 e11346 e11347 e11348 e11349 e11350 b11351 b11352 b11353 b11354 b11355 b11356 b11357 b11358 d11311 d11327 d7718 d7730 d11302
        omega
      have d11359 : (x 7 11).toNat = 0 := by
        have r11360 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11361 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e11362 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e11363 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e11364 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e11365 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e11366 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b11367 := hb (x 3 7)
        have b11368 := hb (x 4 6)
        have b11369 := hb (x 5 5)
        have b11370 := hb (x 6 4)
        have b11371 := hb (x 7 11)
        have b11372 := hb (x 8 10)
        have b11373 := hb (x 9 9)
        have b11374 := hb (x 10 8)
        clear * - r11360 e11361 e11362 e11363 e11364 e11365 e11366 b11367 b11368 b11369 b11370 b11371 b11372 b11373 b11374 d11311 d11327 d11343 d7718 d7730 d11302
        omega
      have d11375 : (x 3 7).toNat = 0 := by
        have r11376 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11377 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e11378 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e11379 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e11380 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e11381 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e11382 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b11383 := hb (x 3 7)
        have b11384 := hb (x 4 6)
        have b11385 := hb (x 5 5)
        have b11386 := hb (x 6 4)
        have b11387 := hb (x 7 11)
        have b11388 := hb (x 8 10)
        have b11389 := hb (x 9 9)
        have b11390 := hb (x 10 8)
        clear * - r11376 e11377 e11378 e11379 e11380 e11381 e11382 b11383 b11384 b11385 b11386 b11387 b11388 b11389 b11390 d11311 d11327 d11343 d11359 d7718 d7730 d11302
        omega
      have d11391 : (x (-6) 13).toNat = 0 := by
        have r11392 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11393 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e11394 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b11395 := hb (x (-8) 3)
        have b11396 := hb (x (-7) 2)
        have b11397 := hb (x (-6) 13)
        have b11398 := hb (x (-5) 12)
        clear * - r11392 e11393 e11394 b11395 b11396 b11397 b11398 d10985 d10981
        omega
      have d11399 : (x 6 1).toNat = 1 := by
        have r11400 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b11401 := hb (x (-7) 14)
        have b11402 := hb (x (-6) 13)
        have b11403 := hb (x (-5) 12)
        have b11404 := hb (x (-4) 11)
        have b11405 := hb (x (-3) 10)
        have b11406 := hb (x (-2) 9)
        have b11407 := hb (x (-1) 8)
        have b11408 := hb (x 0 7)
        have b11409 := hb (x 1 6)
        have b11410 := hb (x 2 5)
        have b11411 := hb (x 3 4)
        have b11412 := hb (x 4 3)
        have b11413 := hb (x 5 2)
        have b11414 := hb (x 6 1)
        clear * - r11400 b11401 b11402 b11403 b11404 b11405 b11406 b11407 b11408 b11409 b11410 b11411 b11412 b11413 b11414 d7576 d7512 g20 g19 g15 d7814 d11014 d11034 d11054 d11070 d10985 d11391 d10721
        omega
      have d11415 : (x 7 14).toNat = 0 := by
        have r11416 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b11417 := hb (x 6 1)
        have b11418 := hb (x 7 14)
        clear * - r11416 b11417 b11418 d11399
        omega
      have d11419 : (x 7 2).toNat = 0 := by
        have r11420 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b11421 := hb (x 7 2)
        have b11422 := hb (x 7 14)
        clear * - r11420 b11421 b11422 d11415
        omega
      have r11423 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r11424 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r11425 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r11426 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r11427 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r11428 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
      have r11429 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
      have r11430 := hand2 (x (-3) 2) (x (-3) 12)
      have r11431 := hand2 (x (-4) 3) (x (-4) 13)
      have r11432 := hand2 (x (-4) 1) (x (-4) 14)
      have r11433 := hand1 (x 8 1) (x 8 14)
      linarith only [r11423, r11424, r11425, r11426, r11427, r11428, r11429, r11430, r11431, r11432, r11433, d11086, g3, g6, g7, g12, d10472, g16, d7682, d11282, d10512, d7698, d11375, d11194, d11302, d11214, d7730, d7718, d11419, g48, d10997]
    · have f11471 : (x 1 7).toNat = 1 := by rw [h10608]; rfl
      have d11472 : (x 8 8).toNat = 0 := by
        have r11473 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11474 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e11475 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e11476 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e11477 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e11478 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e11479 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b11480 := hb (x 1 7)
        have b11481 := hb (x 2 6)
        have b11482 := hb (x 3 5)
        have b11483 := hb (x 4 4)
        have b11484 := hb (x 5 11)
        have b11485 := hb (x 6 10)
        have b11486 := hb (x 7 9)
        have b11487 := hb (x 8 8)
        clear * - r11473 e11474 e11475 e11476 e11477 e11478 e11479 b11480 b11481 b11482 b11483 b11484 b11485 b11486 b11487 d7653 f11471
        omega
      have d11488 : (x 8 1 && x 8 8).toNat = 0 := by
        have r11489 := hand2 (x 8 1) (x 8 8)
        have b11490 := hb (x 8 8)
        have b11491 := hb (x 8 1 && x 8 8)
        clear * - r11489 b11490 b11491 d11472
        omega
      have d11492 : (x 8 3 && x 8 8).toNat = 0 := by
        have r11493 := hand2 (x 8 3) (x 8 8)
        have b11494 := hb (x 8 8)
        have b11495 := hb (x 8 3 && x 8 8)
        clear * - r11493 b11494 b11495 d11472
        omega
      have d11496 : (x 7 9).toNat = 0 := by
        have r11497 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11498 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e11499 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e11500 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e11501 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e11502 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e11503 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b11504 := hb (x 1 7)
        have b11505 := hb (x 2 6)
        have b11506 := hb (x 3 5)
        have b11507 := hb (x 4 4)
        have b11508 := hb (x 5 11)
        have b11509 := hb (x 6 10)
        have b11510 := hb (x 7 9)
        have b11511 := hb (x 8 8)
        clear * - r11497 e11498 e11499 e11500 e11501 e11502 e11503 b11504 b11505 b11506 b11507 b11508 b11509 b11510 b11511 d11472 d7653 f11471
        omega
      have d11512 : (x 7 2 && x 7 9).toNat = 0 := by
        have r11513 := hand2 (x 7 2) (x 7 9)
        have b11514 := hb (x 7 9)
        have b11515 := hb (x 7 2 && x 7 9)
        clear * - r11513 b11514 b11515 d11496
        omega
      have d11516 : (x 6 10).toNat = 0 := by
        have r11517 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11518 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e11519 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e11520 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e11521 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e11522 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e11523 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b11524 := hb (x 1 7)
        have b11525 := hb (x 2 6)
        have b11526 := hb (x 3 5)
        have b11527 := hb (x 4 4)
        have b11528 := hb (x 5 11)
        have b11529 := hb (x 6 10)
        have b11530 := hb (x 7 9)
        have b11531 := hb (x 8 8)
        clear * - r11517 e11518 e11519 e11520 e11521 e11522 e11523 b11524 b11525 b11526 b11527 b11528 b11529 b11530 b11531 d11472 d11496 d7653 f11471
        omega
      have d11532 : (x 6 1 && x 6 10).toNat = 0 := by
        have r11533 := hand2 (x 6 1) (x 6 10)
        have b11534 := hb (x 6 10)
        have b11535 := hb (x 6 1 && x 6 10)
        clear * - r11533 b11534 b11535 d11516
        omega
      have d11536 : (x 4 3 && x 4 12).toNat = 1 := by
        have r11537 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b11538 := hb (x 1 6)
        have b11539 := hb (x 7 9)
        have b11540 := hb (x 6 1 && x 6 10)
        have b11541 := hb (x 5 2 && x 5 11)
        have b11542 := hb (x 4 3 && x 4 12)
        have b11543 := hb (x 3 4 && x 3 13)
        have b11544 := hb (x 2 5 && x 2 14)
        clear * - r11537 b11538 b11539 b11540 b11541 b11542 b11543 b11544 d11496 d11532 d7584 g46 g47 g15
        omega
      have d11545 : (x 4 12).toNat = 1 := by
        have r11546 := hand2 (x 4 3) (x 4 12)
        have b11547 := hb (x 4 12)
        have b11548 := hb (x 4 3 && x 4 12)
        clear * - r11546 b11547 b11548 d11536
        omega
      have d11549 : (x 2 2).toNat = 0 := by
        have r11550 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11551 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e11552 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b11553 := hb (x 1 3)
        have b11554 := hb (x 2 2)
        have b11555 := hb (x 3 13)
        have b11556 := hb (x 4 12)
        clear * - r11550 e11551 e11552 b11553 b11554 b11555 b11556 d11545 d7637
        omega
      have d11557 : (x 4 13).toNat = 1 := by
        have r11558 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b11559 := hb (x 2 2)
        have b11560 := hb (x 4 13)
        have b11561 := hb (x 3 1 && x 3 14)
        clear * - r11558 b11559 b11560 b11561 d7629 d11549
        omega
      have d11562 : (x 5 12).toNat = 0 := by
        have r11563 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11564 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e11565 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b11566 := hb (x 2 3)
        have b11567 := hb (x 3 2)
        have b11568 := hb (x 4 13)
        have b11569 := hb (x 5 12)
        clear * - r11563 e11564 e11565 b11566 b11567 b11568 b11569 d11557 d7702
        omega
      have d11570 : (x 5 3 && x 5 12).toNat = 0 := by
        have r11571 := hand2 (x 5 3) (x 5 12)
        have b11572 := hb (x 5 12)
        have b11573 := hb (x 5 3 && x 5 12)
        clear * - r11571 b11572 b11573 d11562
        omega
      have d11574 : (x 5 4).toNat = 0 := by
        have r11575 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b11576 := hb (x 5 4)
        have b11577 := hb (x 5 12)
        clear * - r11575 b11576 b11577 d11562
        omega
      have d11578 : (x 5 4 && x 5 11).toNat = 0 := by
        have r11579 := hand1 (x 5 4) (x 5 11)
        have b11580 := hb (x 5 4)
        have b11581 := hb (x 5 4 && x 5 11)
        clear * - r11579 b11580 b11581 d11574
        omega
      have d11582 : (x 6 3 && x 6 10).toNat = 0 := by
        have r11583 := hand2 (x 6 3) (x 6 10)
        have b11584 := hb (x 6 10)
        have b11585 := hb (x 6 3 && x 6 10)
        clear * - r11583 b11584 b11585 d11516
        omega
      have d11586 : (x 5 11).toNat = 0 := by
        have r11587 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11588 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e11589 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e11590 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e11591 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e11592 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e11593 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b11594 := hb (x 1 7)
        have b11595 := hb (x 2 6)
        have b11596 := hb (x 3 5)
        have b11597 := hb (x 4 4)
        have b11598 := hb (x 5 11)
        have b11599 := hb (x 6 10)
        have b11600 := hb (x 7 9)
        have b11601 := hb (x 8 8)
        clear * - r11587 e11588 e11589 e11590 e11591 e11592 e11593 b11594 b11595 b11596 b11597 b11598 b11599 b11600 b11601 d11472 d11496 d11516 d7653 f11471
        omega
      have d11602 : (x 4 4).toNat = 0 := by
        have r11603 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11604 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e11605 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e11606 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e11607 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e11608 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e11609 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b11610 := hb (x 1 7)
        have b11611 := hb (x 2 6)
        have b11612 := hb (x 3 5)
        have b11613 := hb (x 4 4)
        have b11614 := hb (x 5 11)
        have b11615 := hb (x 6 10)
        have b11616 := hb (x 7 9)
        have b11617 := hb (x 8 8)
        clear * - r11603 e11604 e11605 e11606 e11607 e11608 e11609 b11610 b11611 b11612 b11613 b11614 b11615 b11616 b11617 d11472 d11496 d11516 d11586 d7653 f11471
        omega
      have d11618 : (x 4 4 && x 4 13).toNat = 0 := by
        have r11619 := hand1 (x 4 4) (x 4 13)
        have b11620 := hb (x 4 4)
        have b11621 := hb (x 4 4 && x 4 13)
        clear * - r11619 b11620 b11621 d11602
        omega
      have d11622 : (x 8 11).toNat = 1 := by
        have r11623 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b11624 := hb (x 4 4)
        have b11625 := hb (x 8 11)
        have b11626 := hb (x 7 1 && x 7 12)
        have b11627 := hb (x 6 2 && x 6 13)
        have b11628 := hb (x 5 3 && x 5 14)
        clear * - r11623 b11624 b11625 b11626 b11627 b11628 d7524 d7556 d7754 d11602
        omega
      have d11629 : (x 8 3).toNat = 1 := by
        have r11630 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b11631 := hb (x 8 3)
        have b11632 := hb (x 8 11)
        clear * - r11630 b11631 b11632 d11622
        omega
      have d11633 : (x 11 12).toNat = 0 := by
        have r11634 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11635 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e11636 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b11637 := hb (x 8 3)
        have b11638 := hb (x 9 2)
        have b11639 := hb (x 10 13)
        have b11640 := hb (x 11 12)
        clear * - r11634 e11635 e11636 b11637 b11638 b11639 b11640 d11629
        omega
      have d11641 : (x 10 13).toNat = 0 := by
        have r11642 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11643 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e11644 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b11645 := hb (x 8 3)
        have b11646 := hb (x 9 2)
        have b11647 := hb (x 10 13)
        have b11648 := hb (x 11 12)
        clear * - r11642 e11643 e11644 b11645 b11646 b11647 b11648 d11633 d11629
        omega
      have d11649 : (x 9 2).toNat = 0 := by
        have r11650 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11651 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e11652 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b11653 := hb (x 8 3)
        have b11654 := hb (x 9 2)
        have b11655 := hb (x 10 13)
        have b11656 := hb (x 11 12)
        clear * - r11650 e11651 e11652 b11653 b11654 b11655 b11656 d11633 d11641 d11629
        omega
      have d11657 : (x 9 2 && x 9 7).toNat = 0 := by
        have r11658 := hand1 (x 9 2) (x 9 7)
        have b11659 := hb (x 9 2)
        have b11660 := hb (x 9 2 && x 9 7)
        clear * - r11658 b11659 b11660 d11649
        omega
      have d11661 : (x 9 10).toNat = 0 := by
        have r11662 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
        have b11663 := hb (x 9 2)
        have b11664 := hb (x 9 10)
        clear * - r11662 b11663 b11664 d11649
        omega
      have d11665 : (x 11 8).toNat = 0 := by
        have r11666 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11667 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e11668 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e11669 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e11670 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e11671 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e11672 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b11673 := hb (x 4 7)
        have b11674 := hb (x 5 6)
        have b11675 := hb (x 6 5)
        have b11676 := hb (x 7 4)
        have b11677 := hb (x 8 11)
        have b11678 := hb (x 9 10)
        have b11679 := hb (x 10 9)
        have b11680 := hb (x 11 8)
        clear * - r11666 e11667 e11668 e11669 e11670 e11671 e11672 b11673 b11674 b11675 b11676 b11677 b11678 b11679 b11680 d11661 d11622 d7536 d7568 d7762
        omega
      have d11681 : (x 10 9).toNat = 0 := by
        have r11682 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11683 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e11684 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e11685 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e11686 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e11687 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e11688 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b11689 := hb (x 4 7)
        have b11690 := hb (x 5 6)
        have b11691 := hb (x 6 5)
        have b11692 := hb (x 7 4)
        have b11693 := hb (x 8 11)
        have b11694 := hb (x 9 10)
        have b11695 := hb (x 10 9)
        have b11696 := hb (x 11 8)
        clear * - r11682 e11683 e11684 e11685 e11686 e11687 e11688 b11689 b11690 b11691 b11692 b11693 b11694 b11695 b11696 d11665 d11661 d11622 d7536 d7568 d7762
        omega
      have d11697 : (x 4 7).toNat = 0 := by
        have r11698 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11699 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e11700 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e11701 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e11702 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e11703 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e11704 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b11705 := hb (x 4 7)
        have b11706 := hb (x 5 6)
        have b11707 := hb (x 6 5)
        have b11708 := hb (x 7 4)
        have b11709 := hb (x 8 11)
        have b11710 := hb (x 9 10)
        have b11711 := hb (x 10 9)
        have b11712 := hb (x 11 8)
        clear * - r11698 e11699 e11700 e11701 e11702 e11703 e11704 b11705 b11706 b11707 b11708 b11709 b11710 b11711 b11712 d11665 d11681 d11661 d11622 d7536 d7568 d7762
        omega
      have d11713 : (x 4 7 && x 4 12).toNat = 0 := by
        have r11714 := hand1 (x 4 7) (x 4 12)
        have b11715 := hb (x 4 7)
        have b11716 := hb (x 4 7 && x 4 12)
        clear * - r11714 b11715 b11716 d11697
        omega
      have d11717 : (x 2 6).toNat = 0 := by
        have r11718 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e11719 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e11720 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e11721 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e11722 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e11723 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e11724 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b11725 := hb (x 1 7)
        have b11726 := hb (x 2 6)
        have b11727 := hb (x 3 5)
        have b11728 := hb (x 4 4)
        have b11729 := hb (x 5 11)
        have b11730 := hb (x 6 10)
        have b11731 := hb (x 7 9)
        have b11732 := hb (x 8 8)
        clear * - r11718 e11719 e11720 e11721 e11722 e11723 e11724 b11725 b11726 b11727 b11728 b11729 b11730 b11731 b11732 d11472 d11496 d11516 d11586 d11602 d7653 f11471
        omega
      have r11733 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e11734 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e11735 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e11736 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e11737 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e11738 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e11739 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have r11740 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e11741 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
      have e11742 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
      have e11743 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
      have e11744 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
      have e11745 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
      have e11746 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
      have r11747 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r11748 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r11749 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r11750 := hand2 (x 10 1) (x 10 6)
      have r11751 := hand1 (x 4 5) (x 4 12)
      have r11752 := hand1 (x 2 7) (x 2 14)
      have r11753 := hand2 (x 7 1) (x 7 10)
      have r11754 := hand2 (x 6 2) (x 6 11)
      linarith only [r11733, e11734, e11735, e11736, e11737, e11738, e11739, r11740, e11741, e11742, e11743, e11744, e11745, e11746, r11747, r11748, r11749, r11750, r11751, r11752, r11753, r11754, g16, g17, d11717, d7698, d11574, d11657, d11492, d7544, d7572, d7766, d11713, d7649, d10508, d11488, d11512, d11582, d11578, d7645, d11570, d11618, d7657]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 6).toNat = 0)
    (g1 : (x (-4) 5).toNat = 0)
    (g2 : (x (-3) 4).toNat = 0)
    (g3 : (x (-2) 11).toNat = 0)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 10).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x (-1) 13).toNat = 0)
    (g9 : (x 0 3).toNat = 1)
    (g10 : (x 0 4).toNat = 0)
    (g11 : (x 0 5).toNat = 0)
    (g12 : (x 0 9).toNat = 1)
    (g13 : (x 1 2).toNat = 0)
    (g14 : (x 1 5).toNat = 0)
    (g15 : (x 1 6).toNat = 0)
    (g16 : (x 1 8).toNat = 0)
    (g17 : (x 1 10).toNat = 0)
    (g18 : (x 2 4).toNat = 0)
    (g19 : (x 2 5).toNat = 0)
    (g20 : (x 3 4).toNat = 0)
    (g21 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g22 : (x 3 4 && x 3 8).toNat = 0)
    (g23 : (x 2 5 && x 2 9).toNat = 0)
    (g24 : (x 1 6 && x 1 10).toNat = 0)
    (g25 : (x (-5) 1 && x (-5) 6).toNat = 0)
    (g26 : (x (-6) 2 && x (-6) 7).toNat = 0)
    (g27 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g28 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g29 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g30 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g31 : (x 2 4 && x 2 9).toNat = 0)
    (g32 : (x 1 5 && x 1 10).toNat = 0)
    (g33 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g34 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g35 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g36 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g37 : (x 0 1 && x 0 8).toNat = 0)
    (g38 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g39 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g40 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g41 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g42 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g43 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g44 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g45 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g46 : (x 3 4 && x 3 13).toNat = 0)
    (g47 : (x 2 5 && x 2 14).toNat = 0)
    (g48 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g49 : (x (-3) 4 && x (-3) 14).toNat = 0)
    (g50 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g51 : (x 1 2 && x 1 12).toNat = 0)
    (g52 : (x 2 2 && x 2 12).toNat = 0)
    (g53 : (x 1 3 && x 1 13).toNat = 0)
    (g54 : (x 3 2 && x 3 12).toNat = 0)
    (g55 : (x 2 3 && x 2 13).toNat = 0)
    (g56 : (x 1 4 && x 1 14).toNat = 0)
    (g57 : (x 2 4 && x 2 14).toNat = 0)
    (g58 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g59 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g60 : (x 3 1 && x 3 12).toNat = 0)
    (g61 : (x 2 2 && x 2 13).toNat = 0)
    (g62 : (x 1 3 && x 1 14).toNat = 0)
    (g63 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63
