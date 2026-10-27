import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a001

Topic: combinatorics   Node: 04d5c87dac26

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_four_iff_five_core: under the layer-free tight-cover constraints for k = 15 and 54 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 2).toNat = 0)
    (g3 : (x (-2) 6).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 13).toNat = 0)
    (g7 : (x 0 3).toNat = 1)
    (g8 : (x 0 4).toNat = 1)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 10).toNat = 0)
    (g11 : (x 0 11).toNat = 0)
    (g12 : (x 0 12).toNat = 1)
    (g13 : (x 1 11).toNat = 0)
    (g14 : (x 2 10).toNat = 0)
    (g15 : (x 3 9).toNat = 0)
    (g16 : (x 4 8).toNat = 0)
    (g17 : (x 0 3 && x 0 5).toNat = 0)
    (g18 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g19 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g20 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g21 : (x 4 4 && x 4 8).toNat = 0)
    (g22 : (x 3 5 && x 3 9).toNat = 0)
    (g23 : (x 2 6 && x 2 10).toNat = 0)
    (g24 : (x 1 7 && x 1 11).toNat = 0)
    (g25 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g26 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g27 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g28 : (x (-1) 5 && x (-1) 10).toNat = 0)
    (g29 : (x (-2) 6 && x (-2) 11).toNat = 0)
    (g30 : (x (-3) 7 && x (-3) 12).toNat = 0)
    (g31 : (x 4 3 && x 4 8).toNat = 0)
    (g32 : (x 3 4 && x 3 9).toNat = 0)
    (g33 : (x 2 5 && x 2 10).toNat = 0)
    (g34 : (x 1 6 && x 1 11).toNat = 0)
    (g35 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g36 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g37 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g38 : (x 4 2 && x 4 8).toNat = 0)
    (g39 : (x 3 3 && x 3 9).toNat = 0)
    (g40 : (x 2 4 && x 2 10).toNat = 0)
    (g41 : (x 1 5 && x 1 11).toNat = 0)
    (g42 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g43 : (x 0 4 && x 0 11).toNat = 0)
    (g44 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g45 : (x (-2) 6 && x (-2) 13).toNat = 0)
    (g46 : (x (-3) 7 && x (-3) 14).toNat = 0)
    (g47 : (x 0 5 && x 0 14).toNat = 0)
    (g48 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g49 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g50 : (x 0 1 && x 0 11).toNat = 0)
    (g51 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g52 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g53 : (x (-1) 2 && x (-1) 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d16477 : (x 3 12).toNat = 0 := by
    have r16478 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16479 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e16480 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b16481 := hb (x 0 3)
    have b16482 := hb (x 1 2)
    have b16483 := hb (x 2 13)
    have b16484 := hb (x 3 12)
    clear * - r16478 e16479 e16480 b16481 b16482 b16483 b16484 g7
    omega
  have d16485 : (x 3 2 && x 3 12).toNat = 0 := by
    have r16486 := hand2 (x 3 2) (x 3 12)
    have b16487 := hb (x 3 12)
    have b16488 := hb (x 3 2 && x 3 12)
    clear * - r16486 b16487 b16488 d16477
    omega
  have d16489 : (x 3 3 && x 3 12).toNat = 0 := by
    have r16490 := hand2 (x 3 3) (x 3 12)
    have b16491 := hb (x 3 12)
    have b16492 := hb (x 3 3 && x 3 12)
    clear * - r16490 b16491 b16492 d16477
    omega
  have d16493 : (x 3 5 && x 3 12).toNat = 0 := by
    have r16494 := hand2 (x 3 5) (x 3 12)
    have b16495 := hb (x 3 12)
    have b16496 := hb (x 3 5 && x 3 12)
    clear * - r16494 b16495 b16496 d16477
    omega
  have d16497 : (x 3 4).toNat = 0 := by
    have r16498 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b16499 := hb (x 3 4)
    have b16500 := hb (x 3 12)
    clear * - r16498 b16499 b16500 d16477
    omega
  have d16501 : (x 3 4 && x 3 13).toNat = 0 := by
    have r16502 := hand1 (x 3 4) (x 3 13)
    have b16503 := hb (x 3 4)
    have b16504 := hb (x 3 4 && x 3 13)
    clear * - r16502 b16503 b16504 d16497
    omega
  have d16505 : (x 2 13).toNat = 0 := by
    have r16506 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16507 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e16508 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b16509 := hb (x 0 3)
    have b16510 := hb (x 1 2)
    have b16511 := hb (x 2 13)
    have b16512 := hb (x 3 12)
    clear * - r16506 e16507 e16508 b16509 b16510 b16511 b16512 d16477 g7
    omega
  have d16513 : (x 2 3 && x 2 13).toNat = 0 := by
    have r16514 := hand2 (x 2 3) (x 2 13)
    have b16515 := hb (x 2 13)
    have b16516 := hb (x 2 3 && x 2 13)
    clear * - r16514 b16515 b16516 d16505
    omega
  have d16517 : (x 2 4 && x 2 13).toNat = 0 := by
    have r16518 := hand2 (x 2 4) (x 2 13)
    have b16519 := hb (x 2 13)
    have b16520 := hb (x 2 4 && x 2 13)
    clear * - r16518 b16519 b16520 d16505
    omega
  have d16521 : (x 2 6 && x 2 13).toNat = 0 := by
    have r16522 := hand2 (x 2 6) (x 2 13)
    have b16523 := hb (x 2 13)
    have b16524 := hb (x 2 6 && x 2 13)
    clear * - r16522 b16523 b16524 d16505
    omega
  have d16525 : (x 2 5).toNat = 0 := by
    have r16526 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
    have b16527 := hb (x 2 5)
    have b16528 := hb (x 2 13)
    clear * - r16526 b16527 b16528 d16505
    omega
  have d16529 : (x 2 5 && x 2 14).toNat = 0 := by
    have r16530 := hand1 (x 2 5) (x 2 14)
    have b16531 := hb (x 2 5)
    have b16532 := hb (x 2 5 && x 2 14)
    clear * - r16530 b16531 b16532 d16525
    omega
  have d16533 : (x 1 2).toNat = 0 := by
    have r16534 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16535 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e16536 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b16537 := hb (x 0 3)
    have b16538 := hb (x 1 2)
    have b16539 := hb (x 2 13)
    have b16540 := hb (x 3 12)
    clear * - r16534 e16535 e16536 b16537 b16538 b16539 b16540 d16477 d16505 g7
    omega
  have d16541 : (x 1 2 && x 1 8).toNat = 0 := by
    have r16542 := hand1 (x 1 2) (x 1 8)
    have b16543 := hb (x 1 2)
    have b16544 := hb (x 1 2 && x 1 8)
    clear * - r16542 b16543 b16544 d16533
    omega
  have d16545 : (x 1 2 && x 1 6).toNat = 0 := by
    have r16546 := hand1 (x 1 2) (x 1 6)
    have b16547 := hb (x 1 2)
    have b16548 := hb (x 1 2 && x 1 6)
    clear * - r16546 b16547 b16548 d16533
    omega
  have d16549 : (x 1 2 && x 1 4).toNat = 0 := by
    have r16550 := hand1 (x 1 2) (x 1 4)
    have b16551 := hb (x 1 2)
    have b16552 := hb (x 1 2 && x 1 4)
    clear * - r16550 b16551 b16552 d16533
    omega
  have d16553 : (x 1 10).toNat = 0 := by
    have r16554 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b16555 := hb (x 1 2)
    have b16556 := hb (x 1 10)
    clear * - r16554 b16555 b16556 d16533
    omega
  have d16557 : (x 1 3 && x 1 10).toNat = 0 := by
    have r16558 := hand2 (x 1 3) (x 1 10)
    have b16559 := hb (x 1 10)
    have b16560 := hb (x 1 3 && x 1 10)
    clear * - r16558 b16559 b16560 d16553
    omega
  cases h16561 : x 0 1
  · have f16562 : (x 0 1).toNat = 0 := by rw [h16561]; rfl
    have d16563 : (x 0 1 && x 0 12).toNat = 0 := by
      have r16564 := hand1 (x 0 1) (x 0 12)
      have b16565 := hb (x 0 1)
      have b16566 := hb (x 0 1 && x 0 12)
      clear * - r16564 b16565 b16566 f16562
      omega
    have d16567 : (x 0 13).toNat = 0 := by
      have r16568 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
      have b16569 := hb (x 0 1)
      have b16570 := hb (x 0 13)
      clear * - r16568 b16569 b16570 f16562
      omega
    have d16571 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
      have r16572 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16573 := hb (x (-2) 2)
      have b16574 := hb (x 0 13)
      have b16575 := hb (x (-1) 1 && x (-1) 14)
      clear * - r16572 b16573 b16574 b16575 d16567 g2
      omega
    have d16576 : (x (-1) 14).toNat = 1 := by
      have r16577 := hand2 (x (-1) 1) (x (-1) 14)
      have b16578 := hb (x (-1) 14)
      have b16579 := hb (x (-1) 1 && x (-1) 14)
      clear * - r16577 b16578 b16579 d16571
      omega
    have d16580 : (x (-2) 1).toNat = 0 := by
      have r16581 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16582 := hb (x (-2) 1)
      have b16583 := hb (x (-1) 14)
      clear * - r16581 b16582 b16583 d16576
      omega
    have d16584 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r16585 := hand1 (x (-2) 1) (x (-2) 14)
      have b16586 := hb (x (-2) 1)
      have b16587 := hb (x (-2) 1 && x (-2) 14)
      clear * - r16585 b16586 b16587 d16580
      omega
    have d16588 : (x (-2) 13).toNat = 0 := by
      have r16589 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b16590 := hb (x (-2) 1)
      have b16591 := hb (x (-2) 13)
      clear * - r16589 b16590 b16591 d16580
      omega
    have d16592 : (x (-3) 2).toNat = 1 := by
      have r16593 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16594 := hb (x (-3) 2)
      have b16595 := hb (x (-1) 13)
      have b16596 := hb (x (-2) 1 && x (-2) 14)
      clear * - r16593 b16594 b16595 b16596 g6 d16584
      omega
    have d16597 : (x (-3) 14).toNat = 1 := by
      have r16598 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b16599 := hb (x (-3) 2)
      have b16600 := hb (x (-3) 14)
      clear * - r16598 b16599 b16600 d16592
      omega
    have d16601 : (x (-4) 1).toNat = 0 := by
      have r16602 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16603 := hb (x (-4) 1)
      have b16604 := hb (x (-3) 14)
      clear * - r16602 b16603 b16604 d16597
      omega
    have d16605 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
      have r16606 := hand1 (x (-4) 1) (x (-4) 14)
      have b16607 := hb (x (-4) 1)
      have b16608 := hb (x (-4) 1 && x (-4) 14)
      clear * - r16606 b16607 b16608 d16601
      omega
    have d16609 : (x (-4) 13).toNat = 0 := by
      have r16610 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b16611 := hb (x (-4) 1)
      have b16612 := hb (x (-4) 13)
      clear * - r16610 b16611 b16612 d16601
      omega
    have d16613 : (x (-1) 12).toNat = 0 := by
      have r16614 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16615 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e16616 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b16617 := hb (x (-4) 3)
      have b16618 := hb (x (-3) 2)
      have b16619 := hb (x (-2) 13)
      have b16620 := hb (x (-1) 12)
      clear * - r16614 e16615 e16616 b16617 b16618 b16619 b16620 d16588 d16592
      omega
    have d16621 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r16622 := hand2 (x (-1) 1) (x (-1) 12)
      have b16623 := hb (x (-1) 12)
      have b16624 := hb (x (-1) 1 && x (-1) 12)
      clear * - r16622 b16623 b16624 d16613
      omega
    have d16625 : (x (-4) 3).toNat = 0 := by
      have r16626 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16627 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e16628 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b16629 := hb (x (-4) 3)
      have b16630 := hb (x (-3) 2)
      have b16631 := hb (x (-2) 13)
      have b16632 := hb (x (-1) 12)
      clear * - r16626 e16627 e16628 b16629 b16630 b16631 b16632 d16613 d16588 d16592
      omega
    have d16633 : (x (-4) 11).toNat = 0 := by
      have r16634 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b16635 := hb (x (-4) 3)
      have b16636 := hb (x (-4) 11)
      clear * - r16634 b16635 b16636 d16625
      omega
    have d16637 : (x (-4) 4).toNat = 1 := by
      have r16638 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16639 := hb (x (-4) 4)
      have b16640 := hb (x 0 11)
      have b16641 := hb (x (-1) 1 && x (-1) 12)
      have b16642 := hb (x (-2) 2 && x (-2) 13)
      have b16643 := hb (x (-3) 3 && x (-3) 14)
      clear * - r16638 b16639 b16640 b16641 b16642 b16643 g11 d16621 g51 g52
      omega
    have d16644 : (x (-4) 12).toNat = 1 := by
      have r16645 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b16646 := hb (x (-4) 4)
      have b16647 := hb (x (-4) 12)
      clear * - r16645 b16646 b16647 d16637
      omega
    have d16648 : (x (-5) 13).toNat = 0 := by
      have r16649 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16650 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e16651 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b16652 := hb (x (-7) 3)
      have b16653 := hb (x (-6) 2)
      have b16654 := hb (x (-5) 13)
      have b16655 := hb (x (-4) 12)
      clear * - r16649 e16650 e16651 b16652 b16653 b16654 b16655 d16644
      omega
    have d16656 : (x (-6) 2).toNat = 0 := by
      have r16657 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16658 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e16659 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b16660 := hb (x (-7) 3)
      have b16661 := hb (x (-6) 2)
      have b16662 := hb (x (-5) 13)
      have b16663 := hb (x (-4) 12)
      clear * - r16657 e16658 e16659 b16660 b16661 b16662 b16663 d16644 d16648
      omega
    have d16664 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
      have r16665 := hand1 (x (-6) 2) (x (-6) 13)
      have b16666 := hb (x (-6) 2)
      have b16667 := hb (x (-6) 2 && x (-6) 13)
      clear * - r16665 b16666 b16667 d16656
      omega
    have d16668 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
      have r16669 := hand1 (x (-6) 2) (x (-6) 12)
      have b16670 := hb (x (-6) 2)
      have b16671 := hb (x (-6) 2 && x (-6) 12)
      clear * - r16669 b16670 b16671 d16656
      omega
    have d16672 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
      have r16673 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16674 := hb (x (-6) 2)
      have b16675 := hb (x (-4) 13)
      have b16676 := hb (x (-5) 1 && x (-5) 14)
      clear * - r16673 b16674 b16675 b16676 d16609 d16656
      omega
    have d16677 : (x (-5) 14).toNat = 1 := by
      have r16678 := hand2 (x (-5) 1) (x (-5) 14)
      have b16679 := hb (x (-5) 14)
      have b16680 := hb (x (-5) 1 && x (-5) 14)
      clear * - r16678 b16679 b16680 d16672
      omega
    have d16681 : (x (-6) 1).toNat = 0 := by
      have r16682 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16683 := hb (x (-6) 1)
      have b16684 := hb (x (-5) 14)
      clear * - r16682 b16683 b16684 d16677
      omega
    have d16685 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
      have r16686 := hand1 (x (-6) 1) (x (-6) 14)
      have b16687 := hb (x (-6) 1)
      have b16688 := hb (x (-6) 1 && x (-6) 14)
      clear * - r16686 b16687 b16688 d16681
      omega
    have d16689 : (x (-7) 2).toNat = 1 := by
      have r16690 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16691 := hb (x (-7) 2)
      have b16692 := hb (x (-5) 13)
      have b16693 := hb (x (-6) 1 && x (-6) 14)
      clear * - r16690 b16691 b16692 b16693 d16648 d16685
      omega
    have d16694 : (x (-7) 14).toNat = 1 := by
      have r16695 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
      have b16696 := hb (x (-7) 2)
      have b16697 := hb (x (-7) 14)
      clear * - r16695 b16696 b16697 d16689
      omega
    have d16698 : (x (-8) 1).toNat = 0 := by
      have r16699 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16700 := hb (x (-8) 1)
      have b16701 := hb (x (-7) 14)
      clear * - r16699 b16700 b16701 d16694
      omega
    have d16702 : (x (-8) 13).toNat = 0 := by
      have r16703 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
      have b16704 := hb (x (-8) 1)
      have b16705 := hb (x (-8) 13)
      clear * - r16703 b16704 b16705 d16698
      omega
    have d16706 : (x (-5) 12).toNat = 0 := by
      have r16707 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16708 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e16709 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b16710 := hb (x (-8) 3)
      have b16711 := hb (x (-7) 2)
      have b16712 := hb (x (-6) 13)
      have b16713 := hb (x (-5) 12)
      clear * - r16707 e16708 e16709 b16710 b16711 b16712 b16713 d16689
      omega
    have d16714 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
      have r16715 := hand2 (x (-5) 1) (x (-5) 12)
      have b16716 := hb (x (-5) 12)
      have b16717 := hb (x (-5) 1 && x (-5) 12)
      clear * - r16715 b16716 b16717 d16706
      omega
    have d16718 : (x (-5) 1).toNat = 1 := by
      have r16719 := hand1 (x (-5) 1) (x (-5) 14)
      have b16720 := hb (x (-5) 1)
      have b16721 := hb (x (-5) 1 && x (-5) 14)
      clear * - r16719 b16720 b16721 d16672
      omega
    have d16722 : (x (-4) 14).toNat = 0 := by
      have r16723 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16724 := hb (x (-5) 1)
      have b16725 := hb (x (-4) 14)
      clear * - r16723 b16724 b16725 d16718
      omega
    have d16726 : (x (-4) 2).toNat = 0 := by
      have r16727 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
      have b16728 := hb (x (-4) 2)
      have b16729 := hb (x (-4) 14)
      clear * - r16727 b16728 b16729 d16722
      omega
    have d16730 : (x (-4) 10).toNat = 0 := by
      have r16731 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
      have b16732 := hb (x (-4) 2)
      have b16733 := hb (x (-4) 10)
      clear * - r16731 b16732 b16733 d16726
      omega
    have d16734 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
      have r16735 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16736 := hb (x (-4) 2)
      have b16737 := hb (x (-2) 13)
      have b16738 := hb (x (-3) 1 && x (-3) 14)
      clear * - r16735 b16736 b16737 b16738 d16588 d16726
      omega
    have d16739 : (x (-3) 1).toNat = 1 := by
      have r16740 := hand1 (x (-3) 1) (x (-3) 14)
      have b16741 := hb (x (-3) 1)
      have b16742 := hb (x (-3) 1 && x (-3) 14)
      clear * - r16740 b16741 b16742 d16734
      omega
    have d16743 : (x (-2) 14).toNat = 0 := by
      have r16744 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16745 := hb (x (-3) 1)
      have b16746 := hb (x (-2) 14)
      clear * - r16744 b16745 b16746 d16739
      omega
    have d16747 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
      have r16748 := hand2 (x (-2) 3) (x (-2) 14)
      have b16749 := hb (x (-2) 14)
      have b16750 := hb (x (-2) 3 && x (-2) 14)
      clear * - r16748 b16749 b16750 d16743
      omega
    have d16751 : (x (-3) 4).toNat = 1 := by
      have r16752 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16753 := hb (x (-3) 4)
      have b16754 := hb (x 1 11)
      have b16755 := hb (x 0 1 && x 0 12)
      have b16756 := hb (x (-1) 2 && x (-1) 13)
      have b16757 := hb (x (-2) 3 && x (-2) 14)
      clear * - r16752 b16753 b16754 b16755 b16756 b16757 g13 d16563 g53 d16747
      omega
    have d16758 : (x (-3) 12).toNat = 1 := by
      have r16759 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b16760 := hb (x (-3) 4)
      have b16761 := hb (x (-3) 12)
      clear * - r16759 b16760 b16761 d16751
      omega
    have d16762 : (x (-5) 2).toNat = 0 := by
      have r16763 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16764 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e16765 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b16766 := hb (x (-6) 3)
      have b16767 := hb (x (-5) 2)
      have b16768 := hb (x (-4) 13)
      have b16769 := hb (x (-3) 12)
      clear * - r16763 e16764 e16765 b16766 b16767 b16768 b16769 d16758 d16609
      omega
    have d16770 : (x (-3) 13).toNat = 1 := by
      have r16771 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16772 := hb (x (-5) 2)
      have b16773 := hb (x (-3) 13)
      have b16774 := hb (x (-4) 1 && x (-4) 14)
      clear * - r16771 b16772 b16773 b16774 d16605 d16762
      omega
    have d16775 : (x (-2) 12).toNat = 0 := by
      have r16776 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16777 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e16778 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b16779 := hb (x (-5) 3)
      have b16780 := hb (x (-4) 2)
      have b16781 := hb (x (-3) 13)
      have b16782 := hb (x (-2) 12)
      clear * - r16776 e16777 e16778 b16779 b16780 b16781 b16782 d16770 d16726
      omega
    have d16783 : (x (-5) 3).toNat = 0 := by
      have r16784 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16785 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e16786 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b16787 := hb (x (-5) 3)
      have b16788 := hb (x (-4) 2)
      have b16789 := hb (x (-3) 13)
      have b16790 := hb (x (-2) 12)
      clear * - r16784 e16785 e16786 b16787 b16788 b16789 b16790 d16775 d16770 d16726
      omega
    have d16791 : (x (-5) 11).toNat = 0 := by
      have r16792 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b16793 := hb (x (-5) 3)
      have b16794 := hb (x (-5) 11)
      clear * - r16792 b16793 b16794 d16783
      omega
    have d16795 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
      have r16796 := hand2 (x (-5) 1) (x (-5) 11)
      have b16797 := hb (x (-5) 11)
      have b16798 := hb (x (-5) 1 && x (-5) 11)
      clear * - r16796 b16797 b16798 d16791
      omega
    have d16799 : (x (-7) 3).toNat = 0 := by
      have r16800 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16801 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e16802 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b16803 := hb (x (-7) 3)
      have b16804 := hb (x (-6) 2)
      have b16805 := hb (x (-5) 13)
      have b16806 := hb (x (-4) 12)
      clear * - r16800 e16801 e16802 b16803 b16804 b16805 b16806 d16644 d16648 d16656
      omega
    have d16807 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
      have r16808 := hand1 (x (-7) 3) (x (-7) 14)
      have b16809 := hb (x (-7) 3)
      have b16810 := hb (x (-7) 3 && x (-7) 14)
      clear * - r16808 b16809 b16810 d16799
      omega
    have d16811 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
      have r16812 := hand1 (x (-7) 3) (x (-7) 13)
      have b16813 := hb (x (-7) 3)
      have b16814 := hb (x (-7) 3 && x (-7) 13)
      clear * - r16812 b16813 b16814 d16799
      omega
    have d16815 : (x (-8) 4).toNat = 1 := by
      have r16816 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16817 := hb (x (-8) 4)
      have b16818 := hb (x (-4) 11)
      have b16819 := hb (x (-5) 1 && x (-5) 12)
      have b16820 := hb (x (-6) 2 && x (-6) 13)
      have b16821 := hb (x (-7) 3 && x (-7) 14)
      clear * - r16816 b16817 b16818 b16819 b16820 b16821 d16633 d16714 d16664 d16807
      omega
    have d16822 : (x (-8) 12).toNat = 1 := by
      have r16823 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
      have b16824 := hb (x (-8) 4)
      have b16825 := hb (x (-8) 12)
      clear * - r16823 b16824 b16825 d16815
      omega
    have d16826 : (x (-9) 13).toNat = 0 := by
      have r16827 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16828 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e16829 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b16830 := hb (x (-11) 3)
      have b16831 := hb (x (-10) 2)
      have b16832 := hb (x (-9) 13)
      have b16833 := hb (x (-8) 12)
      clear * - r16827 e16828 e16829 b16830 b16831 b16832 b16833 d16822
      omega
    have d16834 : (x (-9) 5).toNat = 0 := by
      have r16835 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
      have b16836 := hb (x (-9) 5)
      have b16837 := hb (x (-9) 13)
      clear * - r16835 b16836 b16837 d16826
      omega
    have d16838 : (x (-10) 2).toNat = 0 := by
      have r16839 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16840 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e16841 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b16842 := hb (x (-11) 3)
      have b16843 := hb (x (-10) 2)
      have b16844 := hb (x (-9) 13)
      have b16845 := hb (x (-8) 12)
      clear * - r16839 e16840 e16841 b16842 b16843 b16844 b16845 d16822 d16826
      omega
    have d16846 : (x (-9) 1 && x (-9) 14).toNat = 1 := by
      have r16847 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16848 := hb (x (-10) 2)
      have b16849 := hb (x (-8) 13)
      have b16850 := hb (x (-9) 1 && x (-9) 14)
      clear * - r16847 b16848 b16849 b16850 d16702 d16838
      omega
    have d16851 : (x (-9) 1).toNat = 1 := by
      have r16852 := hand1 (x (-9) 1) (x (-9) 14)
      have b16853 := hb (x (-9) 1)
      have b16854 := hb (x (-9) 1 && x (-9) 14)
      clear * - r16852 b16853 b16854 d16846
      omega
    have d16855 : (x (-8) 14).toNat = 0 := by
      have r16856 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16857 := hb (x (-9) 1)
      have b16858 := hb (x (-8) 14)
      clear * - r16856 b16857 b16858 d16851
      omega
    have d16859 : (x (-8) 4 && x (-8) 14).toNat = 0 := by
      have r16860 := hand2 (x (-8) 4) (x (-8) 14)
      have b16861 := hb (x (-8) 14)
      have b16862 := hb (x (-8) 4 && x (-8) 14)
      clear * - r16860 b16861 b16862 d16855
      omega
    have r16863 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16864 := hb (x (-9) 5)
    have b16865 := hb (x (-4) 10)
    have b16866 := hb (x (-5) 1 && x (-5) 11)
    have b16867 := hb (x (-6) 2 && x (-6) 12)
    have b16868 := hb (x (-7) 3 && x (-7) 13)
    have b16869 := hb (x (-8) 4 && x (-8) 14)
    linarith only [r16863, b16864, b16865, b16866, b16867, b16868, b16869, d16730, d16795, d16668, d16811, d16859, d16834]
  · have f16870 : (x 0 1).toNat = 1 := by rw [h16561]; rfl
    have d16871 : (x 1 14).toNat = 0 := by
      have r16872 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16873 := hb (x 0 1)
      have b16874 := hb (x 1 14)
      clear * - r16872 b16873 b16874 f16870
      omega
    have d16875 : (x 1 1 && x 1 14).toNat = 0 := by
      have r16876 := hand2 (x 1 1) (x 1 14)
      have b16877 := hb (x 1 14)
      have b16878 := hb (x 1 1 && x 1 14)
      clear * - r16876 b16877 b16878 d16871
      omega
    have d16879 : (x 1 4 && x 1 14).toNat = 0 := by
      have r16880 := hand2 (x 1 4) (x 1 14)
      have b16881 := hb (x 1 14)
      have b16882 := hb (x 1 4 && x 1 14)
      clear * - r16880 b16881 b16882 d16871
      omega
    have d16883 : (x 1 5 && x 1 14).toNat = 0 := by
      have r16884 := hand2 (x 1 5) (x 1 14)
      have b16885 := hb (x 1 14)
      have b16886 := hb (x 1 5 && x 1 14)
      clear * - r16884 b16885 b16886 d16871
      omega
    have d16887 : (x 1 7 && x 1 14).toNat = 0 := by
      have r16888 := hand2 (x 1 7) (x 1 14)
      have b16889 := hb (x 1 14)
      have b16890 := hb (x 1 7 && x 1 14)
      clear * - r16888 b16889 b16890 d16871
      omega
    have d16891 : (x 1 6).toNat = 0 := by
      have r16892 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
      have b16893 := hb (x 1 6)
      have b16894 := hb (x 1 14)
      clear * - r16892 b16893 b16894 d16871
      omega
    have d16895 : (x 0 2).toNat = 1 := by
      have r16896 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16897 := hb (x 0 2)
      have b16898 := hb (x 2 13)
      have b16899 := hb (x 1 1 && x 1 14)
      clear * - r16896 b16897 b16898 b16899 d16505 d16875
      omega
    have d16900 : (x 0 14).toNat = 1 := by
      have r16901 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b16902 := hb (x 0 2)
      have b16903 := hb (x 0 14)
      clear * - r16901 b16902 b16903 d16895
      omega
    have d16904 : (x (-1) 1).toNat = 0 := by
      have r16905 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16906 := hb (x (-1) 1)
      have b16907 := hb (x 0 14)
      clear * - r16905 b16906 b16907 d16900
      omega
    have d16908 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r16909 := hand1 (x (-1) 1) (x (-1) 14)
      have b16910 := hb (x (-1) 1)
      have b16911 := hb (x (-1) 1 && x (-1) 14)
      clear * - r16909 b16910 b16911 d16904
      omega
    have d16912 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r16913 := hand1 (x (-1) 1) (x (-1) 12)
      have b16914 := hb (x (-1) 1)
      have b16915 := hb (x (-1) 1 && x (-1) 12)
      clear * - r16913 b16914 b16915 d16904
      omega
    have d16916 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
      have r16917 := hand1 (x (-1) 1) (x (-1) 11)
      have b16918 := hb (x (-1) 1)
      have b16919 := hb (x (-1) 1 && x (-1) 11)
      clear * - r16917 b16918 b16919 d16904
      omega
    have d16920 : (x (-1) 9).toNat = 0 := by
      have r16921 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
      have b16922 := hb (x (-1) 1)
      have b16923 := hb (x (-1) 9)
      clear * - r16921 b16922 b16923 d16904
      omega
    have d16924 : (x (-1) 3 && x (-1) 9).toNat = 0 := by
      have r16925 := hand2 (x (-1) 3) (x (-1) 9)
      have b16926 := hb (x (-1) 9)
      have b16927 := hb (x (-1) 3 && x (-1) 9)
      clear * - r16925 b16926 b16927 d16920
      omega
    have d16928 : (x 0 13).toNat = 1 := by
      have r16929 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16930 := hb (x (-2) 2)
      have b16931 := hb (x 0 13)
      have b16932 := hb (x (-1) 1 && x (-1) 14)
      clear * - r16929 b16930 b16931 b16932 d16908 g2
      omega
    have d16933 : (x 2 12).toNat = 0 := by
      have r16934 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16935 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e16936 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b16937 := hb (x (-1) 3)
      have b16938 := hb (x 0 2)
      have b16939 := hb (x 1 13)
      have b16940 := hb (x 2 12)
      clear * - r16934 e16935 e16936 b16937 b16938 b16939 b16940 d16895
      omega
    have d16941 : (x 2 3 && x 2 12).toNat = 0 := by
      have r16942 := hand2 (x 2 3) (x 2 12)
      have b16943 := hb (x 2 12)
      have b16944 := hb (x 2 3 && x 2 12)
      clear * - r16942 b16943 b16944 d16933
      omega
    have d16945 : (x 2 4).toNat = 0 := by
      have r16946 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b16947 := hb (x 2 4)
      have b16948 := hb (x 2 12)
      clear * - r16946 b16947 b16948 d16933
      omega
    have d16949 : (x 2 4 && x 2 14).toNat = 0 := by
      have r16950 := hand1 (x 2 4) (x 2 14)
      have b16951 := hb (x 2 4)
      have b16952 := hb (x 2 4 && x 2 14)
      clear * - r16950 b16951 b16952 d16945
      omega
    have d16953 : (x 1 13).toNat = 0 := by
      have r16954 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16955 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e16956 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b16957 := hb (x (-1) 3)
      have b16958 := hb (x 0 2)
      have b16959 := hb (x 1 13)
      have b16960 := hb (x 2 12)
      clear * - r16954 e16955 e16956 b16957 b16958 b16959 b16960 d16933 d16895
      omega
    have d16961 : (x 1 4 && x 1 13).toNat = 0 := by
      have r16962 := hand2 (x 1 4) (x 1 13)
      have b16963 := hb (x 1 13)
      have b16964 := hb (x 1 4 && x 1 13)
      clear * - r16962 b16963 b16964 d16953
      omega
    have d16965 : (x 1 5).toNat = 0 := by
      have r16966 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b16967 := hb (x 1 5)
      have b16968 := hb (x 1 13)
      clear * - r16966 b16967 b16968 d16953
      omega
    have d16969 : (x (-1) 3).toNat = 0 := by
      have r16970 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16971 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e16972 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b16973 := hb (x (-1) 3)
      have b16974 := hb (x 0 2)
      have b16975 := hb (x 1 13)
      have b16976 := hb (x 2 12)
      clear * - r16970 e16971 e16972 b16973 b16974 b16975 b16976 d16933 d16953 d16895
      omega
    have d16977 : (x (-1) 11).toNat = 0 := by
      have r16978 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b16979 := hb (x (-1) 3)
      have b16980 := hb (x (-1) 11)
      clear * - r16978 b16979 b16980 d16969
      omega
    have d16981 : (x 1 12).toNat = 0 := by
      have r16982 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16983 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e16984 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b16985 := hb (x (-2) 3)
      have b16986 := hb (x (-1) 2)
      have b16987 := hb (x 0 13)
      have b16988 := hb (x 1 12)
      clear * - r16982 e16983 e16984 b16985 b16986 b16987 b16988 d16928
      omega
    have d16989 : (x 1 4).toNat = 0 := by
      have r16990 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
      have b16991 := hb (x 1 4)
      have b16992 := hb (x 1 12)
      clear * - r16990 b16991 b16992 d16981
      omega
    have d16993 : (x (-1) 2).toNat = 0 := by
      have r16994 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16995 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e16996 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b16997 := hb (x (-2) 3)
      have b16998 := hb (x (-1) 2)
      have b16999 := hb (x 0 13)
      have b17000 := hb (x 1 12)
      clear * - r16994 e16995 e16996 b16997 b16998 b16999 b17000 d16981 d16928
      omega
    have d17001 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
      have r17002 := hand1 (x (-1) 2) (x (-1) 12)
      have b17003 := hb (x (-1) 2)
      have b17004 := hb (x (-1) 2 && x (-1) 12)
      clear * - r17002 b17003 b17004 d16993
      omega
    have d17005 : (x (-1) 10).toNat = 0 := by
      have r17006 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
      have b17007 := hb (x (-1) 2)
      have b17008 := hb (x (-1) 10)
      clear * - r17006 b17007 b17008 d16993
      omega
    have d17009 : (x (-1) 4 && x (-1) 10).toNat = 0 := by
      have r17010 := hand2 (x (-1) 4) (x (-1) 10)
      have b17011 := hb (x (-1) 10)
      have b17012 := hb (x (-1) 4 && x (-1) 10)
      clear * - r17010 b17011 b17012 d17005
      omega
    have d17013 : (x (-2) 3).toNat = 0 := by
      have r17014 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17015 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e17016 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b17017 := hb (x (-2) 3)
      have b17018 := hb (x (-1) 2)
      have b17019 := hb (x 0 13)
      have b17020 := hb (x 1 12)
      clear * - r17014 e17015 e17016 b17017 b17018 b17019 b17020 d16981 d16928 d16993
      omega
    have d17021 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
      have r17022 := hand1 (x (-2) 3) (x (-2) 13)
      have b17023 := hb (x (-2) 3)
      have b17024 := hb (x (-2) 3 && x (-2) 13)
      clear * - r17022 b17023 b17024 d17013
      omega
    have d17025 : (x (-2) 11).toNat = 0 := by
      have r17026 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
      have b17027 := hb (x (-2) 3)
      have b17028 := hb (x (-2) 11)
      clear * - r17026 b17027 b17028 d17013
      omega
    have d17029 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
      have r17030 := hand2 (x (-2) 1) (x (-2) 11)
      have b17031 := hb (x (-2) 11)
      have b17032 := hb (x (-2) 1 && x (-2) 11)
      clear * - r17030 b17031 b17032 d17025
      omega
    have d17033 : (x (-2) 5 && x (-2) 11).toNat = 0 := by
      have r17034 := hand2 (x (-2) 5) (x (-2) 11)
      have b17035 := hb (x (-2) 11)
      have b17036 := hb (x (-2) 5 && x (-2) 11)
      clear * - r17034 b17035 b17036 d17025
      omega
    have d17037 : (x (-4) 4).toNat = 1 := by
      have r17038 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17039 := hb (x (-4) 4)
      have b17040 := hb (x 0 11)
      have b17041 := hb (x (-1) 1 && x (-1) 12)
      have b17042 := hb (x (-2) 2 && x (-2) 13)
      have b17043 := hb (x (-3) 3 && x (-3) 14)
      clear * - r17038 b17039 b17040 b17041 b17042 b17043 g11 d16912 g51 g52
      omega
    have d17044 : (x (-4) 12).toNat = 1 := by
      have r17045 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b17046 := hb (x (-4) 4)
      have b17047 := hb (x (-4) 12)
      clear * - r17045 b17046 b17047 d17037
      omega
    have d17048 : (x (-5) 13).toNat = 0 := by
      have r17049 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17050 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e17051 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b17052 := hb (x (-7) 3)
      have b17053 := hb (x (-6) 2)
      have b17054 := hb (x (-5) 13)
      have b17055 := hb (x (-4) 12)
      clear * - r17049 e17050 e17051 b17052 b17053 b17054 b17055 d17044
      omega
    have d17056 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
      have r17057 := hand2 (x (-5) 7) (x (-5) 13)
      have b17058 := hb (x (-5) 13)
      have b17059 := hb (x (-5) 7 && x (-5) 13)
      clear * - r17057 b17058 b17059 d17048
      omega
    have d17060 : (x (-5) 9 && x (-5) 13).toNat = 0 := by
      have r17061 := hand2 (x (-5) 9) (x (-5) 13)
      have b17062 := hb (x (-5) 13)
      have b17063 := hb (x (-5) 9 && x (-5) 13)
      clear * - r17061 b17062 b17063 d17048
      omega
    have d17064 : (x (-5) 5).toNat = 0 := by
      have r17065 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b17066 := hb (x (-5) 5)
      have b17067 := hb (x (-5) 13)
      clear * - r17065 b17066 b17067 d17048
      omega
    have d17068 : (x (-6) 2).toNat = 0 := by
      have r17069 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17070 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e17071 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b17072 := hb (x (-7) 3)
      have b17073 := hb (x (-6) 2)
      have b17074 := hb (x (-5) 13)
      have b17075 := hb (x (-4) 12)
      clear * - r17069 e17070 e17071 b17072 b17073 b17074 b17075 d17044 d17048
      omega
    have d17076 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
      have r17077 := hand1 (x (-6) 2) (x (-6) 13)
      have b17078 := hb (x (-6) 2)
      have b17079 := hb (x (-6) 2 && x (-6) 13)
      clear * - r17077 b17078 b17079 d17068
      omega
    have d17080 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
      have r17081 := hand1 (x (-6) 2) (x (-6) 12)
      have b17082 := hb (x (-6) 2)
      have b17083 := hb (x (-6) 2 && x (-6) 12)
      clear * - r17081 b17082 b17083 d17068
      omega
    have d17084 : (x (-6) 10).toNat = 0 := by
      have r17085 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
      have b17086 := hb (x (-6) 2)
      have b17087 := hb (x (-6) 10)
      clear * - r17085 b17086 b17087 d17068
      omega
    have d17088 : (x (-6) 1 && x (-6) 10).toNat = 0 := by
      have r17089 := hand2 (x (-6) 1) (x (-6) 10)
      have b17090 := hb (x (-6) 10)
      have b17091 := hb (x (-6) 1 && x (-6) 10)
      clear * - r17089 b17090 b17091 d17084
      omega
    have d17092 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
      have r17093 := hand2 (x (-6) 5) (x (-6) 10)
      have b17094 := hb (x (-6) 10)
      have b17095 := hb (x (-6) 5 && x (-6) 10)
      clear * - r17093 b17094 b17095 d17084
      omega
    have d17096 : (x (-7) 3).toNat = 0 := by
      have r17097 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17098 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e17099 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b17100 := hb (x (-7) 3)
      have b17101 := hb (x (-6) 2)
      have b17102 := hb (x (-5) 13)
      have b17103 := hb (x (-4) 12)
      clear * - r17097 e17098 e17099 b17100 b17101 b17102 b17103 d17044 d17048 d17068
      omega
    have d17104 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
      have r17105 := hand1 (x (-7) 3) (x (-7) 14)
      have b17106 := hb (x (-7) 3)
      have b17107 := hb (x (-7) 3 && x (-7) 14)
      clear * - r17105 b17106 b17107 d17096
      omega
    have d17108 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
      have r17109 := hand1 (x (-7) 3) (x (-7) 13)
      have b17110 := hb (x (-7) 3)
      have b17111 := hb (x (-7) 3 && x (-7) 13)
      clear * - r17109 b17110 b17111 d17096
      omega
    have d17112 : (x (-7) 11).toNat = 0 := by
      have r17113 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have b17114 := hb (x (-7) 3)
      have b17115 := hb (x (-7) 11)
      clear * - r17113 b17114 b17115 d17096
      omega
    have d17116 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
      have r17117 := hand2 (x (-7) 1) (x (-7) 11)
      have b17118 := hb (x (-7) 11)
      have b17119 := hb (x (-7) 1 && x (-7) 11)
      clear * - r17117 b17118 b17119 d17112
      omega
    have d17120 : (x (-7) 2 && x (-7) 11).toNat = 0 := by
      have r17121 := hand2 (x (-7) 2) (x (-7) 11)
      have b17122 := hb (x (-7) 11)
      have b17123 := hb (x (-7) 2 && x (-7) 11)
      clear * - r17121 b17122 b17123 d17112
      omega
    have d17124 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
      have r17125 := hand2 (x (-7) 6) (x (-7) 11)
      have b17126 := hb (x (-7) 11)
      have b17127 := hb (x (-7) 6 && x (-7) 11)
      clear * - r17125 b17126 b17127 d17112
      omega
    have d17128 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
      have r17129 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17130 := hb (x (-5) 5)
      have b17131 := hb (x 0 10)
      have b17132 := hb (x (-1) 1 && x (-1) 11)
      have b17133 := hb (x (-2) 2 && x (-2) 12)
      have b17134 := hb (x (-3) 3 && x (-3) 13)
      have b17135 := hb (x (-4) 4 && x (-4) 14)
      clear * - r17129 b17130 b17131 b17132 b17133 b17134 b17135 g10 d16916 g48 g49 d17064
      omega
    have d17136 : (x (-4) 14).toNat = 1 := by
      have r17137 := hand2 (x (-4) 4) (x (-4) 14)
      have b17138 := hb (x (-4) 14)
      have b17139 := hb (x (-4) 4 && x (-4) 14)
      clear * - r17137 b17138 b17139 d17128
      omega
    have d17140 : (x (-5) 1).toNat = 0 := by
      have r17141 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17142 := hb (x (-5) 1)
      have b17143 := hb (x (-4) 14)
      clear * - r17141 b17142 b17143 d17136
      omega
    have d17144 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
      have r17145 := hand1 (x (-5) 1) (x (-5) 14)
      have b17146 := hb (x (-5) 1)
      have b17147 := hb (x (-5) 1 && x (-5) 14)
      clear * - r17145 b17146 b17147 d17140
      omega
    have d17148 : (x (-4) 13).toNat = 1 := by
      have r17149 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17150 := hb (x (-6) 2)
      have b17151 := hb (x (-4) 13)
      have b17152 := hb (x (-5) 1 && x (-5) 14)
      clear * - r17149 b17150 b17151 b17152 d17144 d17068
      omega
    have d17153 : (x (-4) 1).toNat = 1 := by
      have r17154 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b17155 := hb (x (-4) 1)
      have b17156 := hb (x (-4) 13)
      clear * - r17154 b17155 b17156 d17148
      omega
    have d17157 : (x (-3) 14).toNat = 0 := by
      have r17158 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17159 := hb (x (-4) 1)
      have b17160 := hb (x (-3) 14)
      clear * - r17158 b17159 b17160 d17153
      omega
    have d17161 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
      have r17162 := hand2 (x (-3) 1) (x (-3) 14)
      have b17163 := hb (x (-3) 14)
      have b17164 := hb (x (-3) 1 && x (-3) 14)
      clear * - r17162 b17163 b17164 d17157
      omega
    have d17165 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
      have r17166 := hand2 (x (-3) 4) (x (-3) 14)
      have b17167 := hb (x (-3) 14)
      have b17168 := hb (x (-3) 4 && x (-3) 14)
      clear * - r17166 b17167 b17168 d17157
      omega
    have d17169 : (x (-4) 5).toNat = 1 := by
      have r17170 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17171 := hb (x (-4) 5)
      have b17172 := hb (x 1 10)
      have b17173 := hb (x 0 1 && x 0 11)
      have b17174 := hb (x (-1) 2 && x (-1) 12)
      have b17175 := hb (x (-2) 3 && x (-2) 13)
      have b17176 := hb (x (-3) 4 && x (-3) 14)
      clear * - r17170 b17171 b17172 b17173 b17174 b17175 b17176 d16553 g50 d17001 d17021 d17165
      omega
    have d17177 : (x (-3) 6).toNat = 0 := by
      have r17178 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
      have b17179 := hb (x (-3) 6)
      have b17180 := hb (x (-3) 14)
      clear * - r17178 b17179 b17180 d17157
      omega
    have d17181 : (x (-3) 6 && x (-3) 12).toNat = 0 := by
      have r17182 := hand1 (x (-3) 6) (x (-3) 12)
      have b17183 := hb (x (-3) 6)
      have b17184 := hb (x (-3) 6 && x (-3) 12)
      clear * - r17182 b17183 b17184 d17177
      omega
    have d17185 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
      have r17186 := hand1 (x (-3) 6) (x (-3) 10)
      have b17187 := hb (x (-3) 6)
      have b17188 := hb (x (-3) 6 && x (-3) 10)
      clear * - r17186 b17187 b17188 d17177
      omega
    have d17189 : (x (-3) 6 && x (-3) 8).toNat = 0 := by
      have r17190 := hand1 (x (-3) 6) (x (-3) 8)
      have b17191 := hb (x (-3) 6)
      have b17192 := hb (x (-3) 6 && x (-3) 8)
      clear * - r17190 b17191 b17192 d17177
      omega
    have d17193 : (x (-3) 2).toNat = 0 := by
      have r17194 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b17195 := hb (x (-3) 2)
      have b17196 := hb (x (-3) 14)
      clear * - r17194 b17195 b17196 d17157
      omega
    have d17197 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
      have r17198 := hand1 (x (-3) 2) (x (-3) 13)
      have b17199 := hb (x (-3) 2)
      have b17200 := hb (x (-3) 2 && x (-3) 13)
      clear * - r17198 b17199 b17200 d17193
      omega
    have d17201 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
      have r17202 := hand1 (x (-3) 2) (x (-3) 12)
      have b17203 := hb (x (-3) 2)
      have b17204 := hb (x (-3) 2 && x (-3) 12)
      clear * - r17202 b17203 b17204 d17193
      omega
    have d17205 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
      have r17206 := hand1 (x (-3) 2) (x (-3) 9)
      have b17207 := hb (x (-3) 2)
      have b17208 := hb (x (-3) 2 && x (-3) 9)
      clear * - r17206 b17207 b17208 d17193
      omega
    have d17209 : (x (-3) 10).toNat = 0 := by
      have r17210 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
      have b17211 := hb (x (-3) 2)
      have b17212 := hb (x (-3) 10)
      clear * - r17210 b17211 b17212 d17193
      omega
    have d17213 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
      have r17214 := hand2 (x (-3) 1) (x (-3) 10)
      have b17215 := hb (x (-3) 10)
      have b17216 := hb (x (-3) 1 && x (-3) 10)
      clear * - r17214 b17215 b17216 d17209
      omega
    have d17217 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
      have r17218 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17219 := hb (x (-3) 2)
      have b17220 := hb (x (-1) 13)
      have b17221 := hb (x (-2) 1 && x (-2) 14)
      clear * - r17218 b17219 b17220 b17221 g6 d17193
      omega
    have d17222 : (x (-2) 14).toNat = 1 := by
      have r17223 := hand2 (x (-2) 1) (x (-2) 14)
      have b17224 := hb (x (-2) 14)
      have b17225 := hb (x (-2) 1 && x (-2) 14)
      clear * - r17223 b17224 b17225 d17217
      omega
    have d17226 : (x (-3) 1).toNat = 0 := by
      have r17227 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17228 := hb (x (-3) 1)
      have b17229 := hb (x (-2) 14)
      clear * - r17227 b17228 b17229 d17222
      omega
    have d17230 : (x (-3) 13).toNat = 0 := by
      have r17231 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b17232 := hb (x (-3) 1)
      have b17233 := hb (x (-3) 13)
      clear * - r17231 b17232 b17233 d17226
      omega
    have d17234 : (x (-3) 5).toNat = 0 := by
      have r17235 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have b17236 := hb (x (-3) 5)
      have b17237 := hb (x (-3) 13)
      clear * - r17235 b17236 b17237 d17230
      omega
    have d17238 : (x (-3) 9).toNat = 0 := by
      have r17239 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
      have b17240 := hb (x (-3) 1)
      have b17241 := hb (x (-3) 9)
      clear * - r17239 b17240 b17241 d17226
      omega
    have d17242 : (x (-2) 1).toNat = 1 := by
      have r17243 := hand1 (x (-2) 1) (x (-2) 14)
      have b17244 := hb (x (-2) 1)
      have b17245 := hb (x (-2) 1 && x (-2) 14)
      clear * - r17243 b17244 b17245 d17217
      omega
    have d17246 : (x (-1) 14).toNat = 0 := by
      have r17247 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17248 := hb (x (-2) 1)
      have b17249 := hb (x (-1) 14)
      clear * - r17247 b17248 b17249 d17242
      omega
    have d17250 : (x (-1) 6).toNat = 0 := by
      have r17251 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
      have b17252 := hb (x (-1) 6)
      have b17253 := hb (x (-1) 14)
      clear * - r17251 b17252 b17253 d17246
      omega
    have d17254 : (x (-1) 4 && x (-1) 6).toNat = 0 := by
      have r17255 := hand2 (x (-1) 4) (x (-1) 6)
      have b17256 := hb (x (-1) 6)
      have b17257 := hb (x (-1) 4 && x (-1) 6)
      clear * - r17255 b17256 b17257 d17250
      omega
    have d17258 : (x (-3) 12).toNat = 0 := by
      have r17259 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17260 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e17261 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b17262 := hb (x (-6) 3)
      have b17263 := hb (x (-5) 2)
      have b17264 := hb (x (-4) 13)
      have b17265 := hb (x (-3) 12)
      clear * - r17259 e17260 e17261 b17262 b17263 b17264 b17265 d17148
      omega
    have d17266 : (x (-3) 4).toNat = 0 := by
      have r17267 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b17268 := hb (x (-3) 4)
      have b17269 := hb (x (-3) 12)
      clear * - r17267 b17268 b17269 d17258
      omega
    have d17270 : (x (-5) 2).toNat = 0 := by
      have r17271 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17272 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e17273 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b17274 := hb (x (-6) 3)
      have b17275 := hb (x (-5) 2)
      have b17276 := hb (x (-4) 13)
      have b17277 := hb (x (-3) 12)
      clear * - r17271 e17272 e17273 b17274 b17275 b17276 b17277 d17258 d17148
      omega
    have d17278 : (x (-5) 10).toNat = 0 := by
      have r17279 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
      have b17280 := hb (x (-5) 2)
      have b17281 := hb (x (-5) 10)
      clear * - r17279 b17280 b17281 d17270
      omega
    have d17282 : (x (-5) 8 && x (-5) 10).toNat = 0 := by
      have r17283 := hand2 (x (-5) 8) (x (-5) 10)
      have b17284 := hb (x (-5) 10)
      have b17285 := hb (x (-5) 8 && x (-5) 10)
      clear * - r17283 b17284 b17285 d17278
      omega
    have d17286 : (x (-6) 3).toNat = 0 := by
      have r17287 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17288 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e17289 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b17290 := hb (x (-6) 3)
      have b17291 := hb (x (-5) 2)
      have b17292 := hb (x (-4) 13)
      have b17293 := hb (x (-3) 12)
      clear * - r17287 e17288 e17289 b17290 b17291 b17292 b17293 d17258 d17148 d17270
      omega
    have d17294 : (x (-6) 11).toNat = 0 := by
      have r17295 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
      have b17296 := hb (x (-6) 3)
      have b17297 := hb (x (-6) 11)
      clear * - r17295 b17296 b17297 d17286
      omega
    have d17298 : (x (-6) 9 && x (-6) 11).toNat = 0 := by
      have r17299 := hand2 (x (-6) 9) (x (-6) 11)
      have b17300 := hb (x (-6) 11)
      have b17301 := hb (x (-6) 9 && x (-6) 11)
      clear * - r17299 b17300 b17301 d17294
      omega
    have d17302 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
      have r17303 := hand1 (x (-5) 1) (x (-5) 12)
      have b17304 := hb (x (-5) 1)
      have b17305 := hb (x (-5) 1 && x (-5) 12)
      clear * - r17303 b17304 b17305 d17140
      omega
    have d17306 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
      have r17307 := hand1 (x (-5) 1) (x (-5) 11)
      have b17308 := hb (x (-5) 1)
      have b17309 := hb (x (-5) 1 && x (-5) 11)
      clear * - r17307 b17308 b17309 d17140
      omega
    have d17310 : (x (-5) 9).toNat = 0 := by
      have r17311 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
      have b17312 := hb (x (-5) 1)
      have b17313 := hb (x (-5) 9)
      clear * - r17311 b17312 b17313 d17140
      omega
    have d17314 : (x (-5) 9 && x (-5) 14).toNat = 0 := by
      have r17315 := hand1 (x (-5) 9) (x (-5) 14)
      have b17316 := hb (x (-5) 9)
      have b17317 := hb (x (-5) 9 && x (-5) 14)
      clear * - r17315 b17316 b17317 d17310
      omega
    have d17318 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
      have r17319 := hand2 (x (-5) 4) (x (-5) 9)
      have b17320 := hb (x (-5) 9)
      have b17321 := hb (x (-5) 4 && x (-5) 9)
      clear * - r17319 b17320 b17321 d17310
      omega
    have d17322 : (x 1 8).toNat = 0 := by
      have r17323 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17324 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e17325 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e17326 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e17327 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e17328 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e17329 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b17330 := hb (x (-6) 7)
      have b17331 := hb (x (-5) 6)
      have b17332 := hb (x (-4) 5)
      have b17333 := hb (x (-3) 4)
      have b17334 := hb (x (-2) 11)
      have b17335 := hb (x (-1) 10)
      have b17336 := hb (x 0 9)
      have b17337 := hb (x 1 8)
      clear * - r17323 e17324 e17325 e17326 e17327 e17328 e17329 b17330 b17331 b17332 b17333 b17334 b17335 b17336 b17337 d17005 d17025 d17266 d17169
      omega
    have d17338 : (x 1 3 && x 1 8).toNat = 0 := by
      have r17339 := hand2 (x 1 3) (x 1 8)
      have b17340 := hb (x 1 8)
      have b17341 := hb (x 1 3 && x 1 8)
      clear * - r17339 b17340 b17341 d17322
      omega
    have d17342 : (x 0 9).toNat = 0 := by
      have r17343 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17344 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e17345 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e17346 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e17347 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e17348 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e17349 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b17350 := hb (x (-6) 7)
      have b17351 := hb (x (-5) 6)
      have b17352 := hb (x (-4) 5)
      have b17353 := hb (x (-3) 4)
      have b17354 := hb (x (-2) 11)
      have b17355 := hb (x (-1) 10)
      have b17356 := hb (x 0 9)
      have b17357 := hb (x 1 8)
      clear * - r17343 e17344 e17345 e17346 e17347 e17348 e17349 b17350 b17351 b17352 b17353 b17354 b17355 b17356 b17357 d17322 d17005 d17025 d17266 d17169
      omega
    have d17358 : (x 0 3 && x 0 9).toNat = 0 := by
      have r17359 := hand2 (x 0 3) (x 0 9)
      have b17360 := hb (x 0 9)
      have b17361 := hb (x 0 3 && x 0 9)
      clear * - r17359 b17360 b17361 d17342
      omega
    have d17362 : (x 0 4 && x 0 9).toNat = 0 := by
      have r17363 := hand2 (x 0 4) (x 0 9)
      have b17364 := hb (x 0 9)
      have b17365 := hb (x 0 4 && x 0 9)
      clear * - r17363 b17364 b17365 d17342
      omega
    have d17366 : (x (-5) 6).toNat = 0 := by
      have r17367 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17368 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e17369 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e17370 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e17371 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e17372 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e17373 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b17374 := hb (x (-6) 7)
      have b17375 := hb (x (-5) 6)
      have b17376 := hb (x (-4) 5)
      have b17377 := hb (x (-3) 4)
      have b17378 := hb (x (-2) 11)
      have b17379 := hb (x (-1) 10)
      have b17380 := hb (x 0 9)
      have b17381 := hb (x 1 8)
      clear * - r17367 e17368 e17369 e17370 e17371 e17372 e17373 b17374 b17375 b17376 b17377 b17378 b17379 b17380 b17381 d17322 d17342 d17005 d17025 d17266 d17169
      omega
    have d17382 : (x (-6) 7).toNat = 0 := by
      have r17383 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17384 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e17385 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e17386 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e17387 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e17388 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e17389 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b17390 := hb (x (-6) 7)
      have b17391 := hb (x (-5) 6)
      have b17392 := hb (x (-4) 5)
      have b17393 := hb (x (-3) 4)
      have b17394 := hb (x (-2) 11)
      have b17395 := hb (x (-1) 10)
      have b17396 := hb (x 0 9)
      have b17397 := hb (x 1 8)
      clear * - r17383 e17384 e17385 e17386 e17387 e17388 e17389 b17390 b17391 b17392 b17393 b17394 b17395 b17396 b17397 d17322 d17342 d17005 d17025 d17266 d17169 d17366
      omega
    have d17398 : (x 0 8).toNat = 0 := by
      have r17399 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17400 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e17401 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e17402 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e17403 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e17404 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e17405 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b17406 := hb (x (-7) 7)
      have b17407 := hb (x (-6) 6)
      have b17408 := hb (x (-5) 5)
      have b17409 := hb (x (-4) 4)
      have b17410 := hb (x (-3) 11)
      have b17411 := hb (x (-2) 10)
      have b17412 := hb (x (-1) 9)
      have b17413 := hb (x 0 8)
      clear * - r17399 e17400 e17401 e17402 e17403 e17404 e17405 b17406 b17407 b17408 b17409 b17410 b17411 b17412 b17413 d16920 g4 g1 d17037 d17064
      omega
    have d17414 : (x 0 2 && x 0 8).toNat = 0 := by
      have r17415 := hand2 (x 0 2) (x 0 8)
      have b17416 := hb (x 0 8)
      have b17417 := hb (x 0 2 && x 0 8)
      clear * - r17415 b17416 b17417 d17398
      omega
    have d17418 : (x 0 8 && x 0 12).toNat = 0 := by
      have r17419 := hand1 (x 0 8) (x 0 12)
      have b17420 := hb (x 0 8)
      have b17421 := hb (x 0 8 && x 0 12)
      clear * - r17419 b17420 b17421 d17398
      omega
    have d17422 : (x 0 4 && x 0 8).toNat = 0 := by
      have r17423 := hand2 (x 0 4) (x 0 8)
      have b17424 := hb (x 0 8)
      have b17425 := hb (x 0 4 && x 0 8)
      clear * - r17423 b17424 b17425 d17398
      omega
    cases h17426 : x 0 6
    · have f17427 : (x 0 6).toNat = 0 := by rw [h17426]; rfl
      have d17428 : (x 0 6 && x 0 12).toNat = 0 := by
        have r17429 := hand1 (x 0 6) (x 0 12)
        have b17430 := hb (x 0 6)
        have b17431 := hb (x 0 6 && x 0 12)
        clear * - r17429 b17430 b17431 f17427
        omega
      cases h17432 : x 0 7
      · have f17433 : (x 0 7).toNat = 0 := by rw [h17432]; rfl
        have d17434 : (x 0 7 && x 0 12).toNat = 0 := by
          have r17435 := hand1 (x 0 7) (x 0 12)
          have b17436 := hb (x 0 7)
          have b17437 := hb (x 0 7 && x 0 12)
          clear * - r17435 b17436 b17437 f17433
          omega
        have d17438 : (x 0 3 && x 0 7).toNat = 0 := by
          have r17439 := hand2 (x 0 3) (x 0 7)
          have b17440 := hb (x 0 7)
          have b17441 := hb (x 0 3 && x 0 7)
          clear * - r17439 b17440 b17441 f17433
          omega
        cases h17442 : x 1 1
        · have f17443 : (x 1 1).toNat = 0 := by rw [h17442]; rfl
          cases h17444 : x 1 3
          · have f17445 : (x 1 3).toNat = 0 := by rw [h17444]; rfl
            have d17446 : (x 1 3 && x 1 7).toNat = 0 := by
              have r17447 := hand1 (x 1 3) (x 1 7)
              have b17448 := hb (x 1 3)
              have b17449 := hb (x 1 3 && x 1 7)
              clear * - r17447 b17448 b17449 f17445
              omega
            cases h17450 : x (-1) 4
            · have f17451 : (x (-1) 4).toNat = 0 := by rw [h17450]; rfl
              have d17452 : (x (-1) 4 && x (-1) 8).toNat = 0 := by
                have r17453 := hand1 (x (-1) 4) (x (-1) 8)
                have b17454 := hb (x (-1) 4)
                have b17455 := hb (x (-1) 4 && x (-1) 8)
                clear * - r17453 b17454 b17455 f17451
                omega
              cases h17456 : x (-1) 7
              · have f17457 : (x (-1) 7).toNat = 0 := by rw [h17456]; rfl
                cases h17458 : x 1 7
                · have f17459 : (x 1 7).toNat = 0 := by rw [h17458]; rfl
                  cases h17460 : x (-1) 8
                  · have f17461 : (x (-1) 8).toNat = 0 := by rw [h17460]; rfl
                    cases h17462 : x 2 1
                    · have f17463 : (x 2 1).toNat = 0 := by rw [h17462]; rfl
                      have d17464 : (x 2 1 && x 2 14).toNat = 0 := by
                        have r17465 := hand1 (x 2 1) (x 2 14)
                        have b17466 := hb (x 2 1)
                        have b17467 := hb (x 2 1 && x 2 14)
                        clear * - r17465 b17466 b17467 f17463
                        omega
                      have d17468 : (x 3 13).toNat = 1 := by
                        have r17469 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b17470 := hb (x 1 2)
                        have b17471 := hb (x 3 13)
                        have b17472 := hb (x 2 1 && x 2 14)
                        clear * - r17469 b17470 b17471 b17472 d17464 d16533
                        omega
                      have d17473 : (x 3 1).toNat = 1 := by
                        have r17474 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                        have b17475 := hb (x 3 1)
                        have b17476 := hb (x 3 13)
                        clear * - r17474 b17475 b17476 d17468
                        omega
                      have d17477 : (x 4 12).toNat = 0 := by
                        have r17478 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e17479 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                        have e17480 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                        have b17481 := hb (x 1 3)
                        have b17482 := hb (x 2 2)
                        have b17483 := hb (x 3 13)
                        have b17484 := hb (x 4 12)
                        clear * - r17478 e17479 e17480 b17481 b17482 b17483 b17484 d17468 f17445
                        omega
                      have d17485 : (x 4 3 && x 4 12).toNat = 0 := by
                        have r17486 := hand2 (x 4 3) (x 4 12)
                        have b17487 := hb (x 4 12)
                        have b17488 := hb (x 4 3 && x 4 12)
                        clear * - r17486 b17487 b17488 d17477
                        omega
                      have d17489 : (x 4 4).toNat = 0 := by
                        have r17490 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                        have b17491 := hb (x 4 4)
                        have b17492 := hb (x 4 12)
                        clear * - r17490 b17491 b17492 d17477
                        omega
                      have d17493 : (x 2 2).toNat = 0 := by
                        have r17494 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e17495 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                        have e17496 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                        have b17497 := hb (x 1 3)
                        have b17498 := hb (x 2 2)
                        have b17499 := hb (x 3 13)
                        have b17500 := hb (x 4 12)
                        clear * - r17494 e17495 e17496 b17497 b17498 b17499 b17500 d17477 d17468 f17445
                        omega
                      have d17501 : (x 2 2 && x 2 6).toNat = 0 := by
                        have r17502 := hand1 (x 2 2) (x 2 6)
                        have b17503 := hb (x 2 2)
                        have b17504 := hb (x 2 2 && x 2 6)
                        clear * - r17502 b17503 b17504 d17493
                        omega
                      have r17505 : (x (-5) 1).toNat + (x (-6) 2).toNat + (x (-7) 3).toNat + (x (-8) 4).toNat + (x (-9) 5).toNat + (x (-10) 6).toNat + (x (-11) 7).toNat + (x (-12) 8).toNat + (x (-13) 9).toNat + (x (-14) 10).toNat + (x (-15) 11).toNat + (x (-16) 12).toNat + (x (-17) 13).toNat + (x (-18) 14).toNat = 3 := by have q := hcount (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17506 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17507 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17508 : (x (-12) 8).toNat + (x (-13) 1 && x (-13) 9).toNat + (x (-14) 2 && x (-14) 10).toNat + (x (-15) 3 && x (-15) 11).toNat + (x (-16) 4 && x (-16) 12).toNat + (x (-17) 5 && x (-17) 13).toNat + (x (-18) 6 && x (-18) 14).toNat + (x (-19) 7).toNat = 1 := by have q := hd8 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17509 : (x (-13) 1 && x (-13) 9).toNat = (x (-13) 9).toNat := handr _ _ (fun h => hp9 (-13) (h))
                      have e17510 : (x (-14) 2 && x (-14) 10).toNat = (x (-14) 10).toNat := handr _ _ (fun h => hp10 (-14) (h))
                      have e17511 : (x (-15) 3 && x (-15) 11).toNat = (x (-15) 11).toNat := handr _ _ (fun h => hp11 (-15) (h))
                      have e17512 : (x (-16) 4 && x (-16) 12).toNat = (x (-16) 4).toNat := handl _ _ (fun h => hp4 (-16) (h))
                      have e17513 : (x (-17) 5 && x (-17) 13).toNat = (x (-17) 5).toNat := handl _ _ (fun h => hp5 (-17) (h))
                      have e17514 : (x (-18) 6 && x (-18) 14).toNat = (x (-18) 6).toNat := handl _ _ (fun h => hp6 (-18) (h))
                      have r17515 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17516 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                      have e17517 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                      have e17518 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                      have e17519 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                      have e17520 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                      have e17521 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                      have r17522 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17523 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e17524 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e17525 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e17526 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e17527 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e17528 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have r17529 : (x (-16) 12).toNat + (x (-17) 1 && x (-17) 13).toNat + (x (-18) 2 && x (-18) 14).toNat + (x (-19) 3).toNat = 1 := by have q := hd12 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17530 : (x (-17) 1 && x (-17) 13).toNat = (x (-17) 13).toNat := handr _ _ (fun h => hp13 (-17) (h))
                      have e17531 : (x (-18) 2 && x (-18) 14).toNat = (x (-18) 2).toNat := handl _ _ (fun h => hp2 (-18) (h))
                      have r17532 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17533 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
                      have e17534 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
                      have r17535 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17536 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
                      have e17537 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
                      have r17538 : (x (-11) 14).toNat + (x (-12) 1).toNat = 1 := by have q := hd14 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17539 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17540 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                      have e17541 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                      have r17542 : 1 ≤ (x (-12) 9).toNat + (x (-13) 1 && x (-13) 10).toNat + (x (-14) 2 && x (-14) 11).toNat + (x (-15) 3 && x (-15) 12).toNat + (x (-16) 4 && x (-16) 13).toNat + (x (-17) 5 && x (-17) 14).toNat + (x (-18) 6).toNat := by have q := hcov9 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17543 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17544 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17545 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17546 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17547 : (x (-14) 11).toNat ≤ (x (-14) 3).toNat := himp _ _ (hp11 (-14))
                      have r17548 : (x (-13) 10).toNat ≤ (x (-13) 2).toNat := himp _ _ (hp10 (-13))
                      have r17549 : (x (-12) 9).toNat ≤ (x (-12) 1).toNat := himp _ _ (hp9 (-12))
                      have r17550 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
                      have r17551 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
                      have r17552 := hand1 (x (-4) 8) (x (-4) 12)
                      have r17553 := hand2 (x (-13) 1) (x (-13) 10)
                      have r17554 := hand2 (x (-14) 2) (x (-14) 11)
                      have r17555 := hand1 (x (-15) 3) (x (-15) 12)
                      have r17556 := hand1 (x (-16) 4) (x (-16) 13)
                      have r17557 := hand1 (x (-17) 5) (x (-17) 14)
                      have r17558 := hand2 (x 6 1) (x 6 10)
                      have r17559 := hand2 (x 5 2) (x 5 11)
                      have r17560 := hand2 (x (-8) 1) (x (-8) 12)
                      have r17561 := hand2 (x (-9) 2) (x (-9) 13)
                      have r17562 := hand2 (x (-10) 3) (x (-10) 14)
                      have r17563 := hand2 (x (-13) 1) (x (-13) 14)
                      have r17564 := hand2 (x (-10) 1) (x (-10) 14)
                      have b17569 := hb (x (-18) 14)
                      linarith only [r17505, r17506, r17507, r17508, e17509, e17510, e17511, e17512, e17513, e17514, r17515, e17516, e17517, e17518, e17519, e17520, e17521, r17522, e17523, e17524, e17525, e17526, e17527, e17528, r17529, e17530, e17531, r17532, e17533, e17534, r17535, e17536, e17537, r17538, r17539, e17540, e17541, r17542, r17543, r17544, r17545, r17546, r17547, r17548, r17549, r17550, r17551, r17552, r17553, r17554, r17555, r17556, r17557, r17558, r17559, r17560, r17561, r17562, r17563, r17564, b17569, d17096, d17112, d17068, d17382, d17084, d17140, d17366, d17310, d17169, d17266, g0, d17013, g3, d16993, g5, f16870, g8, f17445, d16891, f17459, d17493, d17473, d17489, d17501, d17446, d17422, g18, g19, g20, d17060, d17485, d16501, d16529]
                    · have f17658 : (x 2 1).toNat = 1 := by rw [h17462]; rfl
                      have d17659 : (x 3 14).toNat = 0 := by
                        have r17660 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b17661 := hb (x 2 1)
                        have b17662 := hb (x 3 14)
                        clear * - r17660 b17661 b17662 f17658
                        omega
                      have d17663 : (x 3 1 && x 3 14).toNat = 0 := by
                        have r17664 := hand2 (x 3 1) (x 3 14)
                        have b17665 := hb (x 3 14)
                        have b17666 := hb (x 3 1 && x 3 14)
                        clear * - r17664 b17665 b17666 d17659
                        omega
                      have d17667 : (x 3 6).toNat = 0 := by
                        have r17668 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
                        have b17669 := hb (x 3 6)
                        have b17670 := hb (x 3 14)
                        clear * - r17668 b17669 b17670 d17659
                        omega
                      have d17671 : (x 3 1 && x 3 6).toNat = 0 := by
                        have r17672 := hand2 (x 3 1) (x 3 6)
                        have b17673 := hb (x 3 6)
                        have b17674 := hb (x 3 1 && x 3 6)
                        clear * - r17672 b17673 b17674 d17667
                        omega
                      have d17675 : (x 3 2).toNat = 0 := by
                        have r17676 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                        have b17677 := hb (x 3 2)
                        have b17678 := hb (x 3 14)
                        clear * - r17676 b17677 b17678 d17659
                        omega
                      have r17679 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17680 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17681 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17682 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e17683 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e17684 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e17685 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e17686 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e17687 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have r17688 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17689 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e17690 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e17691 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e17692 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e17693 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e17694 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have r17695 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17696 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                      have e17697 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                      have e17698 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                      have e17699 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                      have e17700 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                      have e17701 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                      have r17702 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17703 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                      have e17704 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                      have e17705 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                      have e17706 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                      have e17707 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                      have e17708 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                      have r17709 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17710 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                      have e17711 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                      have r17712 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17713 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                      have e17714 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                      have r17715 : 1 ≤ (x 3 2).toNat + (x 2 1 && x 2 3).toNat + (x 1 2 && x 1 4).toNat + (x 0 3 && x 0 5).toNat + (x (-1) 4 && x (-1) 6).toNat + (x (-2) 5 && x (-2) 7).toNat + (x (-3) 6 && x (-3) 8).toNat + (x (-4) 7 && x (-4) 9).toNat + (x (-5) 8 && x (-5) 10).toNat + (x (-6) 9 && x (-6) 11).toNat + (x (-7) 10 && x (-7) 12).toNat + (x (-8) 11 && x (-8) 13).toNat + (x (-9) 12 && x (-9) 14).toNat + (x (-10) 13).toNat := by have q := hcov2 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17716 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17717 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                      have e17718 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                      have r17719 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17720 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                      have e17721 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                      have r17722 : 1 ≤ (x 4 5).toNat + (x 3 1 && x 3 6).toNat + (x 2 2 && x 2 7).toNat + (x 1 3 && x 1 8).toNat + (x 0 4 && x 0 9).toNat + (x (-1) 5 && x (-1) 10).toNat + (x (-2) 6 && x (-2) 11).toNat + (x (-3) 7 && x (-3) 12).toNat + (x (-4) 8 && x (-4) 13).toNat + (x (-5) 9 && x (-5) 14).toNat + (x (-6) 10).toNat := by have q := hcov5 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17723 : 1 ≤ (x 7 5).toNat + (x 6 1 && x 6 6).toNat + (x 5 2 && x 5 7).toNat + (x 4 3 && x 4 8).toNat + (x 3 4 && x 3 9).toNat + (x 2 5 && x 2 10).toNat + (x 1 6 && x 1 11).toNat + (x 0 7 && x 0 12).toNat + (x (-1) 8 && x (-1) 13).toNat + (x (-2) 9 && x (-2) 14).toNat + (x (-3) 10).toNat := by have q := hcov5 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17724 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17725 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17726 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17727 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17728 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17729 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r17730 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
                      have r17731 : (x (-11) 6).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp6 (-11))
                      have r17732 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
                      have r17733 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
                      have r17734 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                      have r17735 := hand2 (x 2 1) (x 2 3)
                      have r17736 := hand1 (x (-2) 5) (x (-2) 7)
                      have r17737 := hand1 (x (-4) 7) (x (-4) 9)
                      have r17738 := hand1 (x (-7) 10) (x (-7) 12)
                      have r17739 := hand1 (x (-8) 11) (x (-8) 13)
                      have r17740 := hand1 (x (-9) 12) (x (-9) 14)
                      have r17741 := hand1 (x (-2) 5) (x (-2) 9)
                      have r17742 := hand1 (x (-4) 7) (x (-4) 11)
                      have r17743 := hand2 (x (-4) 7) (x (-4) 11)
                      have r17744 := hand1 (x (-5) 8) (x (-5) 12)
                      have r17745 := hand1 (x (-6) 9) (x (-6) 13)
                      have r17746 := hand1 (x 6 2) (x 6 6)
                      have r17747 := hand1 (x 5 3) (x 5 7)
                      have r17748 := hand1 (x 2 2) (x 2 7)
                      have r17749 := hand1 (x (-4) 8) (x (-4) 13)
                      have r17750 := hand2 (x 6 1) (x 6 6)
                      have r17751 := hand2 (x 5 2) (x 5 7)
                      have r17752 := hand1 (x (-2) 9) (x (-2) 14)
                      have r17753 := hand2 (x 2 1) (x 2 7)
                      have r17754 := hand1 (x (-4) 7) (x (-4) 13)
                      have r17755 := hand1 (x (-5) 8) (x (-5) 14)
                      have r17756 := hand1 (x 3 1) (x 3 8)
                      have r17757 := hand1 (x 2 2) (x 2 9)
                      have r17758 := hand2 (x (-8) 3) (x (-8) 12)
                      have r17759 := hand1 (x (-9) 4) (x (-9) 13)
                      have r17760 := hand1 (x (-10) 5) (x (-10) 14)
                      have r17761 := hand2 (x 10 1) (x 10 10)
                      have r17762 := hand2 (x 9 2) (x 9 11)
                      have r17763 := hand2 (x 8 3) (x 8 12)
                      have r17764 := hand1 (x 7 4) (x 7 13)
                      have r17765 := hand1 (x 6 5) (x 6 14)
                      have r17766 := hand2 (x (-10) 1) (x (-10) 14)
                      linarith only [r17679, r17680, r17681, e17682, e17683, e17684, e17685, e17686, e17687, r17688, e17689, e17690, e17691, e17692, e17693, e17694, r17695, e17696, e17697, e17698, e17699, e17700, e17701, r17702, e17703, e17704, e17705, e17706, e17707, e17708, r17709, e17710, e17711, r17712, e17713, e17714, r17715, r17716, e17717, e17718, r17719, e17720, e17721, r17722, r17723, r17724, r17725, r17726, r17727, r17728, r17729, r17730, r17731, r17732, r17733, r17734, r17735, r17736, r17737, r17738, r17739, r17740, r17741, r17742, r17743, r17744, r17745, r17746, r17747, r17748, r17749, r17750, r17751, r17752, r17753, r17754, r17755, r17756, r17757, r17758, r17759, r17760, r17761, r17762, r17763, r17764, r17765, r17766, d17112, d17084, d17310, d17177, g0, d17209, g1, g3, g4, f17451, g5, f17461, g7, g8, d16533, f17445, f17658, d16525, d17675, d16497, d17667, d16549, g17, d17254, d17189, d17282, d17298, d16545, d17438, d17452, d17185, g21, g22, g23, g24, d17418, g25, d17671, d17338, d17362, g28, g29, g30, d17314, g31, g32, g33, g34, d17434, g35, d16541, d17358, d17009, d17033, d17181, d16557, g43, g44, g45, g46, d17088, d17120, d17663]
                  · have f17916 : (x (-1) 8).toNat = 1 := by rw [h17460]; rfl
                    have d17917 : (x (-2) 9).toNat = 0 := by
                      have r17918 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17919 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e17920 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e17921 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e17922 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e17923 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e17924 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b17925 := hb (x (-8) 7)
                      have b17926 := hb (x (-7) 6)
                      have b17927 := hb (x (-6) 5)
                      have b17928 := hb (x (-5) 4)
                      have b17929 := hb (x (-4) 11)
                      have b17930 := hb (x (-3) 10)
                      have b17931 := hb (x (-2) 9)
                      have b17932 := hb (x (-1) 8)
                      clear * - r17918 e17919 e17920 e17921 e17922 e17923 e17924 b17925 b17926 b17927 b17928 b17929 b17930 b17931 b17932 f17916 d17209
                      omega
                    have d17933 : (x (-4) 11).toNat = 0 := by
                      have r17934 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17935 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e17936 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e17937 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e17938 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e17939 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e17940 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b17941 := hb (x (-8) 7)
                      have b17942 := hb (x (-7) 6)
                      have b17943 := hb (x (-6) 5)
                      have b17944 := hb (x (-5) 4)
                      have b17945 := hb (x (-4) 11)
                      have b17946 := hb (x (-3) 10)
                      have b17947 := hb (x (-2) 9)
                      have b17948 := hb (x (-1) 8)
                      clear * - r17934 e17935 e17936 e17937 e17938 e17939 e17940 b17941 b17942 b17943 b17944 b17945 b17946 b17947 b17948 f17916 d17917 d17209
                      omega
                    have d17949 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
                      have r17950 := hand2 (x (-4) 2) (x (-4) 11)
                      have b17951 := hb (x (-4) 11)
                      have b17952 := hb (x (-4) 2 && x (-4) 11)
                      clear * - r17950 b17951 b17952 d17933
                      omega
                    have d17953 : (x (-8) 4).toNat = 1 := by
                      have r17954 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b17955 := hb (x (-8) 4)
                      have b17956 := hb (x (-4) 11)
                      have b17957 := hb (x (-5) 1 && x (-5) 12)
                      have b17958 := hb (x (-6) 2 && x (-6) 13)
                      have b17959 := hb (x (-7) 3 && x (-7) 14)
                      clear * - r17954 b17955 b17956 b17957 b17958 b17959 d17933 d17302 d17076 d17104
                      omega
                    have d17960 : (x (-8) 12).toNat = 1 := by
                      have r17961 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                      have b17962 := hb (x (-8) 4)
                      have b17963 := hb (x (-8) 12)
                      clear * - r17961 b17962 b17963 d17953
                      omega
                    have d17964 : (x (-9) 13).toNat = 0 := by
                      have r17965 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17966 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                      have e17967 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                      have b17968 := hb (x (-11) 3)
                      have b17969 := hb (x (-10) 2)
                      have b17970 := hb (x (-9) 13)
                      have b17971 := hb (x (-8) 12)
                      clear * - r17965 e17966 e17967 b17968 b17969 b17970 b17971 d17960
                      omega
                    have d17972 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
                      have r17973 := hand2 (x (-9) 8) (x (-9) 13)
                      have b17974 := hb (x (-9) 13)
                      have b17975 := hb (x (-9) 8 && x (-9) 13)
                      clear * - r17973 b17974 b17975 d17964
                      omega
                    have d17976 : (x (-9) 5).toNat = 0 := by
                      have r17977 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
                      have b17978 := hb (x (-9) 5)
                      have b17979 := hb (x (-9) 13)
                      clear * - r17977 b17978 b17979 d17964
                      omega
                    have d17980 : (x (-5) 4).toNat = 0 := by
                      have r17981 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e17982 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e17983 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e17984 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e17985 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e17986 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e17987 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b17988 := hb (x (-8) 7)
                      have b17989 := hb (x (-7) 6)
                      have b17990 := hb (x (-6) 5)
                      have b17991 := hb (x (-5) 4)
                      have b17992 := hb (x (-4) 11)
                      have b17993 := hb (x (-3) 10)
                      have b17994 := hb (x (-2) 9)
                      have b17995 := hb (x (-1) 8)
                      clear * - r17981 e17982 e17983 e17984 e17985 e17986 e17987 b17988 b17989 b17990 b17991 b17992 b17993 b17994 b17995 f17916 d17917 d17209 d17933
                      omega
                    have d17996 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                      have r17997 := hand1 (x (-5) 4) (x (-5) 14)
                      have b17998 := hb (x (-5) 4)
                      have b17999 := hb (x (-5) 4 && x (-5) 14)
                      clear * - r17997 b17998 b17999 d17980
                      omega
                    have d18000 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
                      have r18001 := hand1 (x (-5) 4) (x (-5) 11)
                      have b18002 := hb (x (-5) 4)
                      have b18003 := hb (x (-5) 4 && x (-5) 11)
                      clear * - r18001 b18002 b18003 d17980
                      omega
                    have d18004 : (x (-6) 5).toNat = 0 := by
                      have r18005 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18006 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18007 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18008 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18009 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18010 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18011 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18012 := hb (x (-8) 7)
                      have b18013 := hb (x (-7) 6)
                      have b18014 := hb (x (-6) 5)
                      have b18015 := hb (x (-5) 4)
                      have b18016 := hb (x (-4) 11)
                      have b18017 := hb (x (-3) 10)
                      have b18018 := hb (x (-2) 9)
                      have b18019 := hb (x (-1) 8)
                      clear * - r18005 e18006 e18007 e18008 e18009 e18010 e18011 b18012 b18013 b18014 b18015 b18016 b18017 b18018 b18019 f17916 d17917 d17209 d17933 d17980
                      omega
                    have d18020 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
                      have r18021 := hand1 (x (-6) 5) (x (-6) 12)
                      have b18022 := hb (x (-6) 5)
                      have b18023 := hb (x (-6) 5 && x (-6) 12)
                      clear * - r18021 b18022 b18023 d18004
                      omega
                    have d18024 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
                      have r18025 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b18026 := hb (x (-6) 5)
                      have b18027 := hb (x (-1) 10)
                      have b18028 := hb (x (-2) 1 && x (-2) 11)
                      have b18029 := hb (x (-3) 2 && x (-3) 12)
                      have b18030 := hb (x (-4) 3 && x (-4) 13)
                      have b18031 := hb (x (-5) 4 && x (-5) 14)
                      clear * - r18025 b18026 b18027 b18028 b18029 b18030 b18031 d17005 d17029 d17201 d17996 d18004
                      omega
                    have d18032 : (x (-4) 3).toNat = 1 := by
                      have r18033 := hand1 (x (-4) 3) (x (-4) 13)
                      have b18034 := hb (x (-4) 3)
                      have b18035 := hb (x (-4) 3 && x (-4) 13)
                      clear * - r18033 b18034 b18035 d18024
                      omega
                    have d18036 : (x (-1) 12).toNat = 0 := by
                      have r18037 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18038 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e18039 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b18040 := hb (x (-4) 3)
                      have b18041 := hb (x (-3) 2)
                      have b18042 := hb (x (-2) 13)
                      have b18043 := hb (x (-1) 12)
                      clear * - r18037 e18038 e18039 b18040 b18041 b18042 b18043 d17193 d18032
                      omega
                    have d18044 : (x (-2) 13).toNat = 0 := by
                      have r18045 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18046 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e18047 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b18048 := hb (x (-4) 3)
                      have b18049 := hb (x (-3) 2)
                      have b18050 := hb (x (-2) 13)
                      have b18051 := hb (x (-1) 12)
                      clear * - r18045 e18046 e18047 b18048 b18049 b18050 b18051 d18036 d17193 d18032
                      omega
                    have d18052 : (x (-4) 2).toNat = 1 := by
                      have r18053 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b18054 := hb (x (-4) 2)
                      have b18055 := hb (x (-2) 13)
                      have b18056 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r18053 b18054 b18055 b18056 d18044 d17161
                      omega
                    have d18057 : (x (-2) 12).toNat = 0 := by
                      have r18058 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18059 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e18060 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b18061 := hb (x (-5) 3)
                      have b18062 := hb (x (-4) 2)
                      have b18063 := hb (x (-3) 13)
                      have b18064 := hb (x (-2) 12)
                      clear * - r18058 e18059 e18060 b18061 b18062 b18063 b18064 d17230 d18052
                      omega
                    have d18065 : (x (-5) 3).toNat = 0 := by
                      have r18066 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18067 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e18068 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b18069 := hb (x (-5) 3)
                      have b18070 := hb (x (-4) 2)
                      have b18071 := hb (x (-3) 13)
                      have b18072 := hb (x (-2) 12)
                      clear * - r18066 e18067 e18068 b18069 b18070 b18071 b18072 d18057 d17230 d18052
                      omega
                    have d18073 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
                      have r18074 := hand1 (x (-5) 3) (x (-5) 12)
                      have b18075 := hb (x (-5) 3)
                      have b18076 := hb (x (-5) 3 && x (-5) 12)
                      clear * - r18074 b18075 b18076 d18065
                      omega
                    have d18077 : (x (-5) 11).toNat = 0 := by
                      have r18078 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                      have b18079 := hb (x (-5) 3)
                      have b18080 := hb (x (-5) 11)
                      clear * - r18078 b18079 b18080 d18065
                      omega
                    have d18081 : (x (-7) 6).toNat = 0 := by
                      have r18082 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18083 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18084 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18085 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18086 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18087 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18088 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18089 := hb (x (-8) 7)
                      have b18090 := hb (x (-7) 6)
                      have b18091 := hb (x (-6) 5)
                      have b18092 := hb (x (-5) 4)
                      have b18093 := hb (x (-4) 11)
                      have b18094 := hb (x (-3) 10)
                      have b18095 := hb (x (-2) 9)
                      have b18096 := hb (x (-1) 8)
                      clear * - r18082 e18083 e18084 e18085 e18086 e18087 e18088 b18089 b18090 b18091 b18092 b18093 b18094 b18095 b18096 f17916 d17917 d17209 d17933 d17980 d18004
                      omega
                    have d18097 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
                      have r18098 := hand1 (x (-7) 6) (x (-7) 13)
                      have b18099 := hb (x (-7) 6)
                      have b18100 := hb (x (-7) 6 && x (-7) 13)
                      clear * - r18098 b18099 b18100 d18081
                      omega
                    have d18101 : (x (-8) 7).toNat = 0 := by
                      have r18102 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18103 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e18104 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e18105 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e18106 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e18107 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e18108 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b18109 := hb (x (-8) 7)
                      have b18110 := hb (x (-7) 6)
                      have b18111 := hb (x (-6) 5)
                      have b18112 := hb (x (-5) 4)
                      have b18113 := hb (x (-4) 11)
                      have b18114 := hb (x (-3) 10)
                      have b18115 := hb (x (-2) 9)
                      have b18116 := hb (x (-1) 8)
                      clear * - r18102 e18103 e18104 e18105 e18106 e18107 e18108 b18109 b18110 b18111 b18112 b18113 b18114 b18115 b18116 f17916 d17917 d17209 d17933 d17980 d18004 d18081
                      omega
                    have d18117 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
                      have r18118 := hand1 (x (-8) 7) (x (-8) 14)
                      have b18119 := hb (x (-8) 7)
                      have b18120 := hb (x (-8) 7 && x (-8) 14)
                      clear * - r18118 b18119 b18120 d18101
                      omega
                    have d18121 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
                      have r18122 := hand1 (x (-8) 7) (x (-8) 12)
                      have b18123 := hb (x (-8) 7)
                      have b18124 := hb (x (-8) 7 && x (-8) 12)
                      clear * - r18122 b18123 b18124 d18101
                      omega
                    have d18125 : (x (-4) 8).toNat = 0 := by
                      have r18126 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e18127 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                      have e18128 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                      have e18129 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                      have e18130 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                      have e18131 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                      have e18132 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                      have b18133 := hb (x (-11) 7)
                      have b18134 := hb (x (-10) 6)
                      have b18135 := hb (x (-9) 5)
                      have b18136 := hb (x (-8) 4)
                      have b18137 := hb (x (-7) 11)
                      have b18138 := hb (x (-6) 10)
                      have b18139 := hb (x (-5) 9)
                      have b18140 := hb (x (-4) 8)
                      clear * - r18126 e18127 e18128 e18129 e18130 e18131 e18132 b18133 b18134 b18135 b18136 b18137 b18138 b18139 b18140 d17310 d17084 d17112 d17953 d17976
                      omega
                    have d18141 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
                      have r18142 := hand2 (x (-4) 3) (x (-4) 8)
                      have b18143 := hb (x (-4) 8)
                      have b18144 := hb (x (-4) 3 && x (-4) 8)
                      clear * - r18142 b18143 b18144 d18125
                      omega
                    have r18145 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18146 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                    have e18147 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                    have e18148 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                    have e18149 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                    have e18150 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                    have e18151 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                    have r18152 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18153 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e18154 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e18155 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e18156 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e18157 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e18158 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have r18159 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r18160 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r18161 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r18162 := hand1 (x (-10) 9) (x (-10) 14)
                    have r18163 := hand2 (x (-2) 1) (x (-2) 8)
                    have r18164 := hand2 (x (-4) 3) (x (-4) 10)
                    have r18165 := hand1 (x (-6) 4) (x (-6) 13)
                    have r18166 := hand1 (x (-7) 5) (x (-7) 14)
                    linarith only [r18145, e18146, e18147, e18148, e18149, e18150, e18151, r18152, e18153, e18154, e18155, e18156, e18157, e18158, r18159, r18160, r18161, r18162, r18163, r18164, r18165, r18166, d18077, d17238, d17917, g5, f17457, g26, g27, d18141, d17318, d17092, d17124, d18121, d17972, d17205, d18000, d18020, d18097, d18117, d17213, d17949, d18073]
                · have f18207 : (x 1 7).toNat = 1 := by rw [h17458]; rfl
                  have d18208 : (x 8 8).toNat = 0 := by
                    have r18209 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18210 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18211 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18212 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18213 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18214 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18215 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18216 := hb (x 1 7)
                    have b18217 := hb (x 2 6)
                    have b18218 := hb (x 3 5)
                    have b18219 := hb (x 4 4)
                    have b18220 := hb (x 5 11)
                    have b18221 := hb (x 6 10)
                    have b18222 := hb (x 7 9)
                    have b18223 := hb (x 8 8)
                    clear * - r18209 e18210 e18211 e18212 e18213 e18214 e18215 b18216 b18217 b18218 b18219 b18220 b18221 b18222 b18223 f18207
                    omega
                  have d18224 : (x 7 9).toNat = 0 := by
                    have r18225 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18226 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18227 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18228 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18229 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18230 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18231 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18232 := hb (x 1 7)
                    have b18233 := hb (x 2 6)
                    have b18234 := hb (x 3 5)
                    have b18235 := hb (x 4 4)
                    have b18236 := hb (x 5 11)
                    have b18237 := hb (x 6 10)
                    have b18238 := hb (x 7 9)
                    have b18239 := hb (x 8 8)
                    clear * - r18225 e18226 e18227 e18228 e18229 e18230 e18231 b18232 b18233 b18234 b18235 b18236 b18237 b18238 b18239 d18208 f18207
                    omega
                  have d18240 : (x 6 10).toNat = 0 := by
                    have r18241 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18242 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18243 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18244 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18245 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18246 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18247 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18248 := hb (x 1 7)
                    have b18249 := hb (x 2 6)
                    have b18250 := hb (x 3 5)
                    have b18251 := hb (x 4 4)
                    have b18252 := hb (x 5 11)
                    have b18253 := hb (x 6 10)
                    have b18254 := hb (x 7 9)
                    have b18255 := hb (x 8 8)
                    clear * - r18241 e18242 e18243 e18244 e18245 e18246 e18247 b18248 b18249 b18250 b18251 b18252 b18253 b18254 b18255 d18208 d18224 f18207
                    omega
                  have d18256 : (x 6 1 && x 6 10).toNat = 0 := by
                    have r18257 := hand2 (x 6 1) (x 6 10)
                    have b18258 := hb (x 6 10)
                    have b18259 := hb (x 6 1 && x 6 10)
                    clear * - r18257 b18258 b18259 d18240
                    omega
                  have d18260 : (x 5 11).toNat = 0 := by
                    have r18261 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18262 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18263 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18264 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18265 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18266 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18267 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18268 := hb (x 1 7)
                    have b18269 := hb (x 2 6)
                    have b18270 := hb (x 3 5)
                    have b18271 := hb (x 4 4)
                    have b18272 := hb (x 5 11)
                    have b18273 := hb (x 6 10)
                    have b18274 := hb (x 7 9)
                    have b18275 := hb (x 8 8)
                    clear * - r18261 e18262 e18263 e18264 e18265 e18266 e18267 b18268 b18269 b18270 b18271 b18272 b18273 b18274 b18275 d18208 d18224 d18240 f18207
                    omega
                  have d18276 : (x 5 1 && x 5 11).toNat = 0 := by
                    have r18277 := hand2 (x 5 1) (x 5 11)
                    have b18278 := hb (x 5 11)
                    have b18279 := hb (x 5 1 && x 5 11)
                    clear * - r18277 b18278 b18279 d18260
                    omega
                  have d18280 : (x 5 2 && x 5 11).toNat = 0 := by
                    have r18281 := hand2 (x 5 2) (x 5 11)
                    have b18282 := hb (x 5 11)
                    have b18283 := hb (x 5 2 && x 5 11)
                    clear * - r18281 b18282 b18283 d18260
                    omega
                  have d18284 : (x 4 3 && x 4 12).toNat = 1 := by
                    have r18285 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18286 := hb (x 1 6)
                    have b18287 := hb (x 7 9)
                    have b18288 := hb (x 6 1 && x 6 10)
                    have b18289 := hb (x 5 2 && x 5 11)
                    have b18290 := hb (x 4 3 && x 4 12)
                    have b18291 := hb (x 3 4 && x 3 13)
                    have b18292 := hb (x 2 5 && x 2 14)
                    clear * - r18285 b18286 b18287 b18288 b18289 b18290 b18291 b18292 d18224 d18256 d18280 d16501 d16529 d16891
                    omega
                  have d18293 : (x 4 12).toNat = 1 := by
                    have r18294 := hand2 (x 4 3) (x 4 12)
                    have b18295 := hb (x 4 12)
                    have b18296 := hb (x 4 3 && x 4 12)
                    clear * - r18294 b18295 b18296 d18284
                    omega
                  have d18297 : (x 3 13).toNat = 0 := by
                    have r18298 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18299 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e18300 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b18301 := hb (x 1 3)
                    have b18302 := hb (x 2 2)
                    have b18303 := hb (x 3 13)
                    have b18304 := hb (x 4 12)
                    clear * - r18298 e18299 e18300 b18301 b18302 b18303 b18304 d18293 f17445
                    omega
                  have d18305 : (x 3 3 && x 3 13).toNat = 0 := by
                    have r18306 := hand2 (x 3 3) (x 3 13)
                    have b18307 := hb (x 3 13)
                    have b18308 := hb (x 3 3 && x 3 13)
                    clear * - r18306 b18307 b18308 d18297
                    omega
                  have d18309 : (x 4 2 && x 4 12).toNat = 1 := by
                    have r18310 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18311 := hb (x 1 5)
                    have b18312 := hb (x 6 10)
                    have b18313 := hb (x 5 1 && x 5 11)
                    have b18314 := hb (x 4 2 && x 4 12)
                    have b18315 := hb (x 3 3 && x 3 13)
                    have b18316 := hb (x 2 4 && x 2 14)
                    clear * - r18310 b18311 b18312 b18313 b18314 b18315 b18316 d18240 d18276 d18305 d16949 d16965
                    omega
                  have d18317 : (x 4 2).toNat = 1 := by
                    have r18318 := hand1 (x 4 2) (x 4 12)
                    have b18319 := hb (x 4 2)
                    have b18320 := hb (x 4 2 && x 4 12)
                    clear * - r18318 b18319 b18320 d18309
                    omega
                  have d18321 : (x 4 14).toNat = 1 := by
                    have r18322 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                    have b18323 := hb (x 4 2)
                    have b18324 := hb (x 4 14)
                    clear * - r18322 b18323 b18324 d18317
                    omega
                  have d18325 : (x 3 1).toNat = 0 := by
                    have r18326 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18327 := hb (x 3 1)
                    have b18328 := hb (x 4 14)
                    clear * - r18326 b18327 b18328 d18321
                    omega
                  have d18329 : (x 3 1 && x 3 8).toNat = 0 := by
                    have r18330 := hand1 (x 3 1) (x 3 8)
                    have b18331 := hb (x 3 1)
                    have b18332 := hb (x 3 1 && x 3 8)
                    clear * - r18330 b18331 b18332 d18325
                    omega
                  have d18333 : (x 6 12).toNat = 0 := by
                    have r18334 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18335 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e18336 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b18337 := hb (x 3 3)
                    have b18338 := hb (x 4 2)
                    have b18339 := hb (x 5 13)
                    have b18340 := hb (x 6 12)
                    clear * - r18334 e18335 e18336 b18337 b18338 b18339 b18340 d18317
                    omega
                  have d18341 : (x 5 13).toNat = 0 := by
                    have r18342 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18343 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e18344 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b18345 := hb (x 3 3)
                    have b18346 := hb (x 4 2)
                    have b18347 := hb (x 5 13)
                    have b18348 := hb (x 6 12)
                    clear * - r18342 e18343 e18344 b18345 b18346 b18347 b18348 d18333 d18317
                    omega
                  have d18349 : (x 3 5).toNat = 0 := by
                    have r18350 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                    have b18351 := hb (x 3 5)
                    have b18352 := hb (x 3 13)
                    clear * - r18350 b18351 b18352 d18297
                    omega
                  have d18353 : (x 2 1 && x 2 14).toNat = 1 := by
                    have r18354 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18355 := hb (x 1 2)
                    have b18356 := hb (x 3 13)
                    have b18357 := hb (x 2 1 && x 2 14)
                    clear * - r18354 b18355 b18356 b18357 d18297 d16533
                    omega
                  have d18358 : (x 2 1).toNat = 1 := by
                    have r18359 := hand1 (x 2 1) (x 2 14)
                    have b18360 := hb (x 2 1)
                    have b18361 := hb (x 2 1 && x 2 14)
                    clear * - r18359 b18360 b18361 d18353
                    omega
                  have d18362 : (x 3 14).toNat = 0 := by
                    have r18363 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18364 := hb (x 2 1)
                    have b18365 := hb (x 3 14)
                    clear * - r18363 b18364 b18365 d18358
                    omega
                  have d18366 : (x 3 2).toNat = 0 := by
                    have r18367 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                    have b18368 := hb (x 3 2)
                    have b18369 := hb (x 3 14)
                    clear * - r18367 b18368 b18369 d18362
                    omega
                  have d18370 : (x 4 1 && x 4 14).toNat = 1 := by
                    have r18371 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18372 := hb (x 3 2)
                    have b18373 := hb (x 5 13)
                    have b18374 := hb (x 4 1 && x 4 14)
                    clear * - r18371 b18372 b18373 b18374 d18341 d18366
                    omega
                  have d18375 : (x 4 1).toNat = 1 := by
                    have r18376 := hand1 (x 4 1) (x 4 14)
                    have b18377 := hb (x 4 1)
                    have b18378 := hb (x 4 1 && x 4 14)
                    clear * - r18376 b18377 b18378 d18370
                    omega
                  have d18379 : (x 5 14).toNat = 0 := by
                    have r18380 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18381 := hb (x 4 1)
                    have b18382 := hb (x 5 14)
                    clear * - r18380 b18381 b18382 d18375
                    omega
                  have d18383 : (x 5 3 && x 5 14).toNat = 0 := by
                    have r18384 := hand2 (x 5 3) (x 5 14)
                    have b18385 := hb (x 5 14)
                    have b18386 := hb (x 5 3 && x 5 14)
                    clear * - r18384 b18385 b18386 d18379
                    omega
                  have d18387 : (x 5 6).toNat = 0 := by
                    have r18388 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                    have b18389 := hb (x 5 6)
                    have b18390 := hb (x 5 14)
                    clear * - r18388 b18389 b18390 d18379
                    omega
                  have d18391 : (x 5 2).toNat = 0 := by
                    have r18392 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                    have b18393 := hb (x 5 2)
                    have b18394 := hb (x 5 14)
                    clear * - r18392 b18393 b18394 d18379
                    omega
                  have d18395 : (x 5 10).toNat = 0 := by
                    have r18396 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                    have b18397 := hb (x 5 2)
                    have b18398 := hb (x 5 10)
                    clear * - r18396 b18397 b18398 d18391
                    omega
                  have d18399 : (x 5 3 && x 5 10).toNat = 0 := by
                    have r18400 := hand2 (x 5 3) (x 5 10)
                    have b18401 := hb (x 5 10)
                    have b18402 := hb (x 5 3 && x 5 10)
                    clear * - r18400 b18401 b18402 d18395
                    omega
                  have d18403 : (x 4 1 && x 4 11).toNat = 1 := by
                    have r18404 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18405 := hb (x 0 5)
                    have b18406 := hb (x 5 10)
                    have b18407 := hb (x 4 1 && x 4 11)
                    have b18408 := hb (x 3 2 && x 3 12)
                    have b18409 := hb (x 2 3 && x 2 13)
                    have b18410 := hb (x 1 4 && x 1 14)
                    clear * - r18404 b18405 b18406 b18407 b18408 b18409 b18410 d18395 d16485 d16513 d16879 g9
                    omega
                  have d18411 : (x 4 11).toNat = 1 := by
                    have r18412 := hand2 (x 4 1) (x 4 11)
                    have b18413 := hb (x 4 11)
                    have b18414 := hb (x 4 1 && x 4 11)
                    clear * - r18412 b18413 b18414 d18403
                    omega
                  have d18415 : (x 4 3).toNat = 1 := by
                    have r18416 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                    have b18417 := hb (x 4 3)
                    have b18418 := hb (x 4 11)
                    clear * - r18416 b18417 b18418 d18411
                    omega
                  have d18419 : (x 7 12).toNat = 0 := by
                    have r18420 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18421 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                    have e18422 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                    have b18423 := hb (x 4 3)
                    have b18424 := hb (x 5 2)
                    have b18425 := hb (x 6 13)
                    have b18426 := hb (x 7 12)
                    clear * - r18420 e18421 e18422 b18423 b18424 b18425 b18426 d18391 d18415
                    omega
                  have d18427 : (x 7 1 && x 7 12).toNat = 0 := by
                    have r18428 := hand2 (x 7 1) (x 7 12)
                    have b18429 := hb (x 7 12)
                    have b18430 := hb (x 7 1 && x 7 12)
                    clear * - r18428 b18429 b18430 d18419
                    omega
                  have d18431 : (x 7 4).toNat = 0 := by
                    have r18432 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                    have b18433 := hb (x 7 4)
                    have b18434 := hb (x 7 12)
                    clear * - r18432 b18433 b18434 d18419
                    omega
                  have d18435 : (x 6 13).toNat = 0 := by
                    have r18436 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18437 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                    have e18438 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                    have b18439 := hb (x 4 3)
                    have b18440 := hb (x 5 2)
                    have b18441 := hb (x 6 13)
                    have b18442 := hb (x 7 12)
                    clear * - r18436 e18437 e18438 b18439 b18440 b18441 b18442 d18419 d18391 d18415
                    omega
                  have d18443 : (x 6 2 && x 6 13).toNat = 0 := by
                    have r18444 := hand2 (x 6 2) (x 6 13)
                    have b18445 := hb (x 6 13)
                    have b18446 := hb (x 6 2 && x 6 13)
                    clear * - r18444 b18445 b18446 d18435
                    omega
                  have d18447 : (x 6 5).toNat = 0 := by
                    have r18448 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                    have b18449 := hb (x 6 5)
                    have b18450 := hb (x 6 13)
                    clear * - r18448 b18449 b18450 d18435
                    omega
                  have d18451 : (x 2 2).toNat = 0 := by
                    have r18452 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18453 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e18454 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b18455 := hb (x 1 3)
                    have b18456 := hb (x 2 2)
                    have b18457 := hb (x 3 13)
                    have b18458 := hb (x 4 12)
                    clear * - r18452 e18453 e18454 b18455 b18456 b18457 b18458 d18293 d18297 f17445
                    omega
                  have d18459 : (x 2 2 && x 2 9).toNat = 0 := by
                    have r18460 := hand1 (x 2 2) (x 2 9)
                    have b18461 := hb (x 2 2)
                    have b18462 := hb (x 2 2 && x 2 9)
                    clear * - r18460 b18461 b18462 d18451
                    omega
                  have d18463 : (x 4 4).toNat = 0 := by
                    have r18464 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18465 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e18466 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e18467 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e18468 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e18469 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e18470 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b18471 := hb (x 1 7)
                    have b18472 := hb (x 2 6)
                    have b18473 := hb (x 3 5)
                    have b18474 := hb (x 4 4)
                    have b18475 := hb (x 5 11)
                    have b18476 := hb (x 6 10)
                    have b18477 := hb (x 7 9)
                    have b18478 := hb (x 8 8)
                    clear * - r18464 e18465 e18466 e18467 e18468 e18469 e18470 b18471 b18472 b18473 b18474 b18475 b18476 b18477 b18478 d18208 d18224 d18240 d18260 d18349 f18207
                    omega
                  have d18479 : (x 4 4 && x 4 11).toNat = 0 := by
                    have r18480 := hand1 (x 4 4) (x 4 11)
                    have b18481 := hb (x 4 4)
                    have b18482 := hb (x 4 4 && x 4 11)
                    clear * - r18480 b18481 b18482 d18463
                    omega
                  have d18483 : (x 8 11).toNat = 1 := by
                    have r18484 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18485 := hb (x 4 4)
                    have b18486 := hb (x 8 11)
                    have b18487 := hb (x 7 1 && x 7 12)
                    have b18488 := hb (x 6 2 && x 6 13)
                    have b18489 := hb (x 5 3 && x 5 14)
                    clear * - r18484 b18485 b18486 b18487 b18488 b18489 d18427 d18443 d18383 d18463
                    omega
                  have d18490 : (x 8 3).toNat = 1 := by
                    have r18491 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                    have b18492 := hb (x 8 3)
                    have b18493 := hb (x 8 11)
                    clear * - r18491 b18492 b18493 d18483
                    omega
                  have d18494 : (x 11 12).toNat = 0 := by
                    have r18495 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18496 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e18497 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b18498 := hb (x 8 3)
                    have b18499 := hb (x 9 2)
                    have b18500 := hb (x 10 13)
                    have b18501 := hb (x 11 12)
                    clear * - r18495 e18496 e18497 b18498 b18499 b18500 b18501 d18490
                    omega
                  have d18502 : (x 11 1 && x 11 12).toNat = 0 := by
                    have r18503 := hand2 (x 11 1) (x 11 12)
                    have b18504 := hb (x 11 12)
                    have b18505 := hb (x 11 1 && x 11 12)
                    clear * - r18503 b18504 b18505 d18494
                    omega
                  have d18506 : (x 11 4).toNat = 0 := by
                    have r18507 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                    have b18508 := hb (x 11 4)
                    have b18509 := hb (x 11 12)
                    clear * - r18507 b18508 b18509 d18494
                    omega
                  have d18510 : (x 10 13).toNat = 0 := by
                    have r18511 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18512 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e18513 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b18514 := hb (x 8 3)
                    have b18515 := hb (x 9 2)
                    have b18516 := hb (x 10 13)
                    have b18517 := hb (x 11 12)
                    clear * - r18511 e18512 e18513 b18514 b18515 b18516 b18517 d18494 d18490
                    omega
                  have d18518 : (x 10 2 && x 10 13).toNat = 0 := by
                    have r18519 := hand2 (x 10 2) (x 10 13)
                    have b18520 := hb (x 10 13)
                    have b18521 := hb (x 10 2 && x 10 13)
                    clear * - r18519 b18520 b18521 d18510
                    omega
                  have d18522 : (x 10 5).toNat = 0 := by
                    have r18523 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
                    have b18524 := hb (x 10 5)
                    have b18525 := hb (x 10 13)
                    clear * - r18523 b18524 b18525 d18510
                    omega
                  have d18526 : (x 9 2).toNat = 0 := by
                    have r18527 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18528 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e18529 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b18530 := hb (x 8 3)
                    have b18531 := hb (x 9 2)
                    have b18532 := hb (x 10 13)
                    have b18533 := hb (x 11 12)
                    clear * - r18527 e18528 e18529 b18530 b18531 b18532 b18533 d18494 d18510 d18490
                    omega
                  have d18534 : (x 9 10).toNat = 0 := by
                    have r18535 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                    have b18536 := hb (x 9 2)
                    have b18537 := hb (x 9 10)
                    clear * - r18535 b18536 b18537 d18526
                    omega
                  have d18538 : (x 11 8).toNat = 0 := by
                    have r18539 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18540 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                    have e18541 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                    have e18542 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                    have e18543 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                    have e18544 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                    have e18545 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                    have b18546 := hb (x 4 7)
                    have b18547 := hb (x 5 6)
                    have b18548 := hb (x 6 5)
                    have b18549 := hb (x 7 4)
                    have b18550 := hb (x 8 11)
                    have b18551 := hb (x 9 10)
                    have b18552 := hb (x 10 9)
                    have b18553 := hb (x 11 8)
                    clear * - r18539 e18540 e18541 e18542 e18543 e18544 e18545 b18546 b18547 b18548 b18549 b18550 b18551 b18552 b18553 d18534 d18483 d18431 d18447 d18387
                    omega
                  have d18554 : (x 10 9).toNat = 0 := by
                    have r18555 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18556 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                    have e18557 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                    have e18558 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                    have e18559 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                    have e18560 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                    have e18561 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                    have b18562 := hb (x 4 7)
                    have b18563 := hb (x 5 6)
                    have b18564 := hb (x 6 5)
                    have b18565 := hb (x 7 4)
                    have b18566 := hb (x 8 11)
                    have b18567 := hb (x 9 10)
                    have b18568 := hb (x 10 9)
                    have b18569 := hb (x 11 8)
                    clear * - r18555 e18556 e18557 e18558 e18559 e18560 e18561 b18562 b18563 b18564 b18565 b18566 b18567 b18568 b18569 d18538 d18534 d18483 d18431 d18447 d18387
                    omega
                  have d18570 : (x 4 7).toNat = 0 := by
                    have r18571 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18572 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                    have e18573 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                    have e18574 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                    have e18575 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                    have e18576 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                    have e18577 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                    have b18578 := hb (x 4 7)
                    have b18579 := hb (x 5 6)
                    have b18580 := hb (x 6 5)
                    have b18581 := hb (x 7 4)
                    have b18582 := hb (x 8 11)
                    have b18583 := hb (x 9 10)
                    have b18584 := hb (x 10 9)
                    have b18585 := hb (x 11 8)
                    clear * - r18571 e18572 e18573 e18574 e18575 e18576 e18577 b18578 b18579 b18580 b18581 b18582 b18583 b18584 b18585 d18538 d18554 d18534 d18483 d18431 d18447 d18387
                    omega
                  have d18586 : (x 7 8).toNat = 0 := by
                    have r18587 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18588 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                    have e18589 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                    have e18590 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                    have e18591 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                    have e18592 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                    have e18593 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                    have b18594 := hb (x 0 7)
                    have b18595 := hb (x 1 6)
                    have b18596 := hb (x 2 5)
                    have b18597 := hb (x 3 4)
                    have b18598 := hb (x 4 11)
                    have b18599 := hb (x 5 10)
                    have b18600 := hb (x 6 9)
                    have b18601 := hb (x 7 8)
                    clear * - r18587 e18588 e18589 e18590 e18591 e18592 e18593 b18594 b18595 b18596 b18597 b18598 b18599 b18600 b18601 d18395 d18411 d16497 d16525 d16891 f17433
                    omega
                  have d18602 : (x 7 1 && x 7 8).toNat = 0 := by
                    have r18603 := hand2 (x 7 1) (x 7 8)
                    have b18604 := hb (x 7 8)
                    have b18605 := hb (x 7 1 && x 7 8)
                    clear * - r18603 b18604 b18605 d18586
                    omega
                  have d18606 : (x 6 9).toNat = 0 := by
                    have r18607 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18608 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                    have e18609 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                    have e18610 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                    have e18611 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                    have e18612 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                    have e18613 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                    have b18614 := hb (x 0 7)
                    have b18615 := hb (x 1 6)
                    have b18616 := hb (x 2 5)
                    have b18617 := hb (x 3 4)
                    have b18618 := hb (x 4 11)
                    have b18619 := hb (x 5 10)
                    have b18620 := hb (x 6 9)
                    have b18621 := hb (x 7 8)
                    clear * - r18607 e18608 e18609 e18610 e18611 e18612 e18613 b18614 b18615 b18616 b18617 b18618 b18619 b18620 b18621 d18586 d18395 d18411 d16497 d16525 d16891 f17433
                    omega
                  have d18622 : (x 6 2 && x 6 9).toNat = 0 := by
                    have r18623 := hand2 (x 6 2) (x 6 9)
                    have b18624 := hb (x 6 9)
                    have b18625 := hb (x 6 2 && x 6 9)
                    clear * - r18623 b18624 b18625 d18606
                    omega
                  have d18626 : (x 8 7).toNat = 1 := by
                    have r18627 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18628 := hb (x 0 8)
                    have b18629 := hb (x 8 7)
                    have b18630 := hb (x 7 1 && x 7 8)
                    have b18631 := hb (x 6 2 && x 6 9)
                    have b18632 := hb (x 5 3 && x 5 10)
                    have b18633 := hb (x 4 4 && x 4 11)
                    have b18634 := hb (x 3 5 && x 3 12)
                    have b18635 := hb (x 2 6 && x 2 13)
                    have b18636 := hb (x 1 7 && x 1 14)
                    clear * - r18627 b18628 b18629 b18630 b18631 b18632 b18633 b18634 b18635 b18636 d18602 d18622 d18399 d18479 d16493 d16521 d16887 d17398
                    omega
                  have d18637 : (x 15 8).toNat = 0 := by
                    have r18638 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18639 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e18640 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e18641 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e18642 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e18643 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e18644 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b18645 := hb (x 8 7)
                    have b18646 := hb (x 9 6)
                    have b18647 := hb (x 10 5)
                    have b18648 := hb (x 11 4)
                    have b18649 := hb (x 12 11)
                    have b18650 := hb (x 13 10)
                    have b18651 := hb (x 14 9)
                    have b18652 := hb (x 15 8)
                    clear * - r18638 e18639 e18640 e18641 e18642 e18643 e18644 b18645 b18646 b18647 b18648 b18649 b18650 b18651 b18652 d18506 d18522 d18626
                    omega
                  have d18653 : (x 14 9).toNat = 0 := by
                    have r18654 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18655 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e18656 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e18657 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e18658 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e18659 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e18660 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b18661 := hb (x 8 7)
                    have b18662 := hb (x 9 6)
                    have b18663 := hb (x 10 5)
                    have b18664 := hb (x 11 4)
                    have b18665 := hb (x 12 11)
                    have b18666 := hb (x 13 10)
                    have b18667 := hb (x 14 9)
                    have b18668 := hb (x 15 8)
                    clear * - r18654 e18655 e18656 e18657 e18658 e18659 e18660 b18661 b18662 b18663 b18664 b18665 b18666 b18667 b18668 d18637 d18506 d18522 d18626
                    omega
                  have d18669 : (x 13 10).toNat = 0 := by
                    have r18670 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18671 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e18672 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e18673 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e18674 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e18675 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e18676 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b18677 := hb (x 8 7)
                    have b18678 := hb (x 9 6)
                    have b18679 := hb (x 10 5)
                    have b18680 := hb (x 11 4)
                    have b18681 := hb (x 12 11)
                    have b18682 := hb (x 13 10)
                    have b18683 := hb (x 14 9)
                    have b18684 := hb (x 15 8)
                    clear * - r18670 e18671 e18672 e18673 e18674 e18675 e18676 b18677 b18678 b18679 b18680 b18681 b18682 b18683 b18684 d18637 d18653 d18506 d18522 d18626
                    omega
                  have d18685 : (x 12 11).toNat = 0 := by
                    have r18686 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18687 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e18688 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e18689 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e18690 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e18691 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e18692 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b18693 := hb (x 8 7)
                    have b18694 := hb (x 9 6)
                    have b18695 := hb (x 10 5)
                    have b18696 := hb (x 11 4)
                    have b18697 := hb (x 12 11)
                    have b18698 := hb (x 13 10)
                    have b18699 := hb (x 14 9)
                    have b18700 := hb (x 15 8)
                    clear * - r18686 e18687 e18688 e18689 e18690 e18691 e18692 b18693 b18694 b18695 b18696 b18697 b18698 b18699 b18700 d18637 d18653 d18669 d18506 d18522 d18626
                    omega
                  have d18701 : (x (-4) 8).toNat = 1 := by
                    have r18702 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18703 := hb (x (-4) 8)
                    have b18704 := hb (x 4 7)
                    have b18705 := hb (x 3 1 && x 3 8)
                    have b18706 := hb (x 2 2 && x 2 9)
                    have b18707 := hb (x 1 3 && x 1 10)
                    have b18708 := hb (x 0 4 && x 0 11)
                    have b18709 := hb (x (-1) 5 && x (-1) 12)
                    have b18710 := hb (x (-2) 6 && x (-2) 13)
                    have b18711 := hb (x (-3) 7 && x (-3) 14)
                    clear * - r18702 b18703 b18704 b18705 b18706 b18707 b18708 b18709 b18710 b18711 d18570 d18329 d18459 d16557 g43 g44 g45 g46
                    omega
                  have d18712 : (x (-8) 4).toNat = 0 := by
                    have r18713 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18714 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                    have e18715 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                    have e18716 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                    have e18717 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                    have e18718 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                    have e18719 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                    have b18720 := hb (x (-11) 7)
                    have b18721 := hb (x (-10) 6)
                    have b18722 := hb (x (-9) 5)
                    have b18723 := hb (x (-8) 4)
                    have b18724 := hb (x (-7) 11)
                    have b18725 := hb (x (-6) 10)
                    have b18726 := hb (x (-5) 9)
                    have b18727 := hb (x (-4) 8)
                    clear * - r18713 e18714 e18715 e18716 e18717 e18718 e18719 b18720 b18721 b18722 b18723 b18724 b18725 b18726 b18727 d18701 d17310 d17084 d17112
                    omega
                  have d18728 : (x (-8) 4 && x (-8) 14).toNat = 0 := by
                    have r18729 := hand1 (x (-8) 4) (x (-8) 14)
                    have b18730 := hb (x (-8) 4)
                    have b18731 := hb (x (-8) 4 && x (-8) 14)
                    clear * - r18729 b18730 b18731 d18712
                    omega
                  have d18732 : (x (-4) 11).toNat = 1 := by
                    have r18733 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18734 := hb (x (-8) 4)
                    have b18735 := hb (x (-4) 11)
                    have b18736 := hb (x (-5) 1 && x (-5) 12)
                    have b18737 := hb (x (-6) 2 && x (-6) 13)
                    have b18738 := hb (x (-7) 3 && x (-7) 14)
                    clear * - r18733 b18734 b18735 b18736 b18737 b18738 d17302 d17076 d17104 d18712
                    omega
                  have d18739 : (x (-4) 3).toNat = 1 := by
                    have r18740 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                    have b18741 := hb (x (-4) 3)
                    have b18742 := hb (x (-4) 11)
                    clear * - r18740 b18741 b18742 d18732
                    omega
                  have d18743 : (x (-1) 12).toNat = 0 := by
                    have r18744 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18745 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e18746 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b18747 := hb (x (-4) 3)
                    have b18748 := hb (x (-3) 2)
                    have b18749 := hb (x (-2) 13)
                    have b18750 := hb (x (-1) 12)
                    clear * - r18744 e18745 e18746 b18747 b18748 b18749 b18750 d17193 d18739
                    omega
                  have d18751 : (x (-2) 13).toNat = 0 := by
                    have r18752 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18753 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e18754 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b18755 := hb (x (-4) 3)
                    have b18756 := hb (x (-3) 2)
                    have b18757 := hb (x (-2) 13)
                    have b18758 := hb (x (-1) 12)
                    clear * - r18752 e18753 e18754 b18755 b18756 b18757 b18758 d18743 d17193 d18739
                    omega
                  have d18759 : (x (-4) 2).toNat = 1 := by
                    have r18760 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18761 := hb (x (-4) 2)
                    have b18762 := hb (x (-2) 13)
                    have b18763 := hb (x (-3) 1 && x (-3) 14)
                    clear * - r18760 b18761 b18762 b18763 d18751 d17161
                    omega
                  have d18764 : (x (-2) 12).toNat = 0 := by
                    have r18765 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18766 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e18767 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b18768 := hb (x (-5) 3)
                    have b18769 := hb (x (-4) 2)
                    have b18770 := hb (x (-3) 13)
                    have b18771 := hb (x (-2) 12)
                    clear * - r18765 e18766 e18767 b18768 b18769 b18770 b18771 d17230 d18759
                    omega
                  have d18772 : (x (-5) 3).toNat = 0 := by
                    have r18773 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18774 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e18775 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b18776 := hb (x (-5) 3)
                    have b18777 := hb (x (-4) 2)
                    have b18778 := hb (x (-3) 13)
                    have b18779 := hb (x (-2) 12)
                    clear * - r18773 e18774 e18775 b18776 b18777 b18778 b18779 d18764 d17230 d18759
                    omega
                  have d18780 : (x (-5) 11).toNat = 0 := by
                    have r18781 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                    have b18782 := hb (x (-5) 3)
                    have b18783 := hb (x (-5) 11)
                    clear * - r18781 b18782 b18783 d18772
                    omega
                  have d18784 : (x (-9) 5).toNat = 0 := by
                    have r18785 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18786 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                    have e18787 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                    have e18788 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                    have e18789 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                    have e18790 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                    have e18791 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                    have b18792 := hb (x (-11) 7)
                    have b18793 := hb (x (-10) 6)
                    have b18794 := hb (x (-9) 5)
                    have b18795 := hb (x (-8) 4)
                    have b18796 := hb (x (-7) 11)
                    have b18797 := hb (x (-6) 10)
                    have b18798 := hb (x (-5) 9)
                    have b18799 := hb (x (-4) 8)
                    clear * - r18785 e18786 e18787 e18788 e18789 e18790 e18791 b18792 b18793 b18794 b18795 b18796 b18797 b18798 b18799 d18701 d17310 d17084 d17112 d18712
                    omega
                  have d18800 : (x (-4) 10).toNat = 1 := by
                    have r18801 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b18802 := hb (x (-9) 5)
                    have b18803 := hb (x (-4) 10)
                    have b18804 := hb (x (-5) 1 && x (-5) 11)
                    have b18805 := hb (x (-6) 2 && x (-6) 12)
                    have b18806 := hb (x (-7) 3 && x (-7) 13)
                    have b18807 := hb (x (-8) 4 && x (-8) 14)
                    clear * - r18801 b18802 b18803 b18804 b18805 b18806 b18807 d17306 d17080 d17108 d18728 d18784
                    omega
                  have d18808 : (x (-2) 8).toNat = 0 := by
                    have r18809 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e18810 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e18811 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e18812 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e18813 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e18814 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e18815 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b18816 := hb (x (-9) 7)
                    have b18817 := hb (x (-8) 6)
                    have b18818 := hb (x (-7) 5)
                    have b18819 := hb (x (-6) 4)
                    have b18820 := hb (x (-5) 11)
                    have b18821 := hb (x (-4) 10)
                    have b18822 := hb (x (-3) 9)
                    have b18823 := hb (x (-2) 8)
                    clear * - r18809 e18810 e18811 e18812 e18813 e18814 e18815 b18816 b18817 b18818 b18819 b18820 b18821 b18822 b18823 d17238 d18800 d18780
                    omega
                  have d18824 : (x (-2) 8 && x (-2) 14).toNat = 0 := by
                    have r18825 := hand1 (x (-2) 8) (x (-2) 14)
                    have b18826 := hb (x (-2) 8)
                    have b18827 := hb (x (-2) 8 && x (-2) 14)
                    clear * - r18825 b18826 b18827 d18808
                    omega
                  have r18828 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r18829 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r18830 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r18831 := hand2 (x 5 1) (x 5 7)
                  have r18832 := hand1 (x 9 3) (x 9 14)
                  linarith only [r18828, r18829, r18830, r18831, r18832, d17238, d17222, g6, g12, g13, g14, g15, g16, d18685, g38, g39, g40, g41, d17428, g42, d18824, d18502, d18518]
              · have f18860 : (x (-1) 7).toNat = 1 := by rw [h17456]; rfl
                have d18861 : (x 6 8).toNat = 0 := by
                  have r18862 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e18863 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e18864 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e18865 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e18866 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e18867 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e18868 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b18869 := hb (x (-1) 7)
                  have b18870 := hb (x 0 6)
                  have b18871 := hb (x 1 5)
                  have b18872 := hb (x 2 4)
                  have b18873 := hb (x 3 11)
                  have b18874 := hb (x 4 10)
                  have b18875 := hb (x 5 9)
                  have b18876 := hb (x 6 8)
                  clear * - r18862 e18863 e18864 e18865 e18866 e18867 e18868 b18869 b18870 b18871 b18872 b18873 b18874 b18875 b18876 d16945 d16965 f17427 f18860
                  omega
                have d18877 : (x 5 9).toNat = 0 := by
                  have r18878 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e18879 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e18880 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e18881 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e18882 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e18883 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e18884 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b18885 := hb (x (-1) 7)
                  have b18886 := hb (x 0 6)
                  have b18887 := hb (x 1 5)
                  have b18888 := hb (x 2 4)
                  have b18889 := hb (x 3 11)
                  have b18890 := hb (x 4 10)
                  have b18891 := hb (x 5 9)
                  have b18892 := hb (x 6 8)
                  clear * - r18878 e18879 e18880 e18881 e18882 e18883 e18884 b18885 b18886 b18887 b18888 b18889 b18890 b18891 b18892 d18861 d16945 d16965 f17427 f18860
                  omega
                have d18893 : (x 4 10).toNat = 0 := by
                  have r18894 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e18895 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e18896 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e18897 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e18898 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e18899 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e18900 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b18901 := hb (x (-1) 7)
                  have b18902 := hb (x 0 6)
                  have b18903 := hb (x 1 5)
                  have b18904 := hb (x 2 4)
                  have b18905 := hb (x 3 11)
                  have b18906 := hb (x 4 10)
                  have b18907 := hb (x 5 9)
                  have b18908 := hb (x 6 8)
                  clear * - r18894 e18895 e18896 e18897 e18898 e18899 e18900 b18901 b18902 b18903 b18904 b18905 b18906 b18907 b18908 d18861 d18877 d16945 d16965 f17427 f18860
                  omega
                have d18909 : (x 4 1 && x 4 10).toNat = 0 := by
                  have r18910 := hand2 (x 4 1) (x 4 10)
                  have b18911 := hb (x 4 10)
                  have b18912 := hb (x 4 1 && x 4 10)
                  clear * - r18910 b18911 b18912 d18893
                  omega
                have d18913 : (x 3 2 && x 3 11).toNat = 1 := by
                  have r18914 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b18915 := hb (x (-1) 6)
                  have b18916 := hb (x 5 9)
                  have b18917 := hb (x 4 1 && x 4 10)
                  have b18918 := hb (x 3 2 && x 3 11)
                  have b18919 := hb (x 2 3 && x 2 12)
                  have b18920 := hb (x 1 4 && x 1 13)
                  have b18921 := hb (x 0 5 && x 0 14)
                  clear * - r18914 b18915 b18916 b18917 b18918 b18919 b18920 b18921 d18877 d18909 d16941 d16961 g47 d17250
                  omega
                have d18922 : (x 3 11).toNat = 1 := by
                  have r18923 := hand2 (x 3 2) (x 3 11)
                  have b18924 := hb (x 3 11)
                  have b18925 := hb (x 3 2 && x 3 11)
                  clear * - r18923 b18924 b18925 d18913
                  omega
                have r18926 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e18927 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e18928 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e18929 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e18930 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e18931 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e18932 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b18933 := hb (x (-1) 7)
                have b18934 := hb (x 0 6)
                have b18935 := hb (x 1 5)
                have b18936 := hb (x 2 4)
                have b18937 := hb (x 3 11)
                have b18938 := hb (x 4 10)
                have b18939 := hb (x 5 9)
                have b18940 := hb (x 6 8)
                linarith only [r18926, e18927, e18928, e18929, e18930, e18931, e18932, b18933, b18934, b18935, b18936, b18937, b18938, b18939, b18940, d18861, d18877, d18893, d18922, d16945, d16965, f17427, f18860]
            · have f18941 : (x (-1) 4).toNat = 1 := by rw [h17450]; rfl
              have d18942 : (x (-1) 12).toNat = 1 := by
                have r18943 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                have b18944 := hb (x (-1) 4)
                have b18945 := hb (x (-1) 12)
                clear * - r18943 b18944 b18945 f18941
                omega
              have d18946 : (x (-2) 13).toNat = 0 := by
                have r18947 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e18948 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e18949 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b18950 := hb (x (-4) 3)
                have b18951 := hb (x (-3) 2)
                have b18952 := hb (x (-2) 13)
                have b18953 := hb (x (-1) 12)
                clear * - r18947 e18948 e18949 b18950 b18951 b18952 b18953 d18942 d17193
                omega
              have d18954 : (x (-4) 2).toNat = 1 := by
                have r18955 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b18956 := hb (x (-4) 2)
                have b18957 := hb (x (-2) 13)
                have b18958 := hb (x (-3) 1 && x (-3) 14)
                clear * - r18955 b18956 b18957 b18958 d18946 d17161
                omega
              have d18959 : (x (-4) 3).toNat = 0 := by
                have r18960 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e18961 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e18962 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b18963 := hb (x (-4) 3)
                have b18964 := hb (x (-3) 2)
                have b18965 := hb (x (-2) 13)
                have b18966 := hb (x (-1) 12)
                clear * - r18960 e18961 e18962 b18963 b18964 b18965 b18966 d18942 d18946 d17193
                omega
              have d18967 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                have r18968 := hand1 (x (-4) 3) (x (-4) 14)
                have b18969 := hb (x (-4) 3)
                have b18970 := hb (x (-4) 3 && x (-4) 14)
                clear * - r18968 b18969 b18970 d18959
                omega
              have d18971 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                have r18972 := hand1 (x (-4) 3) (x (-4) 13)
                have b18973 := hb (x (-4) 3)
                have b18974 := hb (x (-4) 3 && x (-4) 13)
                clear * - r18972 b18973 b18974 d18959
                omega
              have d18975 : (x (-2) 12).toNat = 0 := by
                have r18976 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e18977 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e18978 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b18979 := hb (x (-5) 3)
                have b18980 := hb (x (-4) 2)
                have b18981 := hb (x (-3) 13)
                have b18982 := hb (x (-2) 12)
                clear * - r18976 e18977 e18978 b18979 b18980 b18981 b18982 d17230 d18954
                omega
              have d18983 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                have r18984 := hand2 (x (-2) 1) (x (-2) 12)
                have b18985 := hb (x (-2) 12)
                have b18986 := hb (x (-2) 1 && x (-2) 12)
                clear * - r18984 b18985 b18986 d18975
                omega
              have d18987 : (x (-5) 4).toNat = 1 := by
                have r18988 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b18989 := hb (x (-5) 4)
                have b18990 := hb (x (-1) 11)
                have b18991 := hb (x (-2) 1 && x (-2) 12)
                have b18992 := hb (x (-3) 2 && x (-3) 13)
                have b18993 := hb (x (-4) 3 && x (-4) 14)
                clear * - r18988 b18989 b18990 b18991 b18992 b18993 d16977 d18983 d17197 d18967
                omega
              have d18994 : (x (-5) 12).toNat = 1 := by
                have r18995 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                have b18996 := hb (x (-5) 4)
                have b18997 := hb (x (-5) 12)
                clear * - r18995 b18996 b18997 d18987
                omega
              have d18998 : (x (-6) 13).toNat = 0 := by
                have r18999 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e19000 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e19001 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b19002 := hb (x (-8) 3)
                have b19003 := hb (x (-7) 2)
                have b19004 := hb (x (-6) 13)
                have b19005 := hb (x (-5) 12)
                clear * - r18999 e19000 e19001 b19002 b19003 b19004 b19005 d18994
                omega
              have d19006 : (x (-6) 5).toNat = 0 := by
                have r19007 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                have b19008 := hb (x (-6) 5)
                have b19009 := hb (x (-6) 13)
                clear * - r19007 b19008 b19009 d18998
                omega
              have d19010 : (x (-7) 2).toNat = 0 := by
                have r19011 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e19012 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e19013 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b19014 := hb (x (-8) 3)
                have b19015 := hb (x (-7) 2)
                have b19016 := hb (x (-6) 13)
                have b19017 := hb (x (-5) 12)
                clear * - r19011 e19012 e19013 b19014 b19015 b19016 b19017 d18994 d18998
                omega
              have d19018 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                have r19019 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b19020 := hb (x (-7) 2)
                have b19021 := hb (x (-5) 13)
                have b19022 := hb (x (-6) 1 && x (-6) 14)
                clear * - r19019 b19020 b19021 b19022 d17048 d19010
                omega
              have d19023 : (x (-6) 1).toNat = 1 := by
                have r19024 := hand1 (x (-6) 1) (x (-6) 14)
                have b19025 := hb (x (-6) 1)
                have b19026 := hb (x (-6) 1 && x (-6) 14)
                clear * - r19024 b19025 b19026 d19018
                omega
              have d19027 : (x (-5) 14).toNat = 0 := by
                have r19028 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b19029 := hb (x (-6) 1)
                have b19030 := hb (x (-5) 14)
                clear * - r19028 b19029 b19030 d19023
                omega
              have d19031 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                have r19032 := hand2 (x (-5) 4) (x (-5) 14)
                have b19033 := hb (x (-5) 14)
                have b19034 := hb (x (-5) 4 && x (-5) 14)
                clear * - r19032 b19033 b19034 d19027
                omega
              have r19035 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19036 := hb (x (-6) 5)
              have b19037 := hb (x (-1) 10)
              have b19038 := hb (x (-2) 1 && x (-2) 11)
              have b19039 := hb (x (-3) 2 && x (-3) 12)
              have b19040 := hb (x (-4) 3 && x (-4) 13)
              have b19041 := hb (x (-5) 4 && x (-5) 14)
              linarith only [r19035, b19036, b19037, b19038, b19039, b19040, b19041, d17005, d17029, d17201, d18971, d19031, d19006]
          · have f19042 : (x 1 3).toNat = 1 := by rw [h17444]; rfl
            have d19043 : (x 4 12).toNat = 0 := by
              have r19044 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19045 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e19046 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b19047 := hb (x 1 3)
              have b19048 := hb (x 2 2)
              have b19049 := hb (x 3 13)
              have b19050 := hb (x 4 12)
              clear * - r19044 e19045 e19046 b19047 b19048 b19049 b19050 f19042
              omega
            have d19051 : (x 4 1 && x 4 12).toNat = 0 := by
              have r19052 := hand2 (x 4 1) (x 4 12)
              have b19053 := hb (x 4 12)
              have b19054 := hb (x 4 1 && x 4 12)
              clear * - r19052 b19053 b19054 d19043
              omega
            have d19055 : (x 4 4).toNat = 0 := by
              have r19056 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b19057 := hb (x 4 4)
              have b19058 := hb (x 4 12)
              clear * - r19056 b19057 b19058 d19043
              omega
            have d19059 : (x 3 13).toNat = 0 := by
              have r19060 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19061 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e19062 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b19063 := hb (x 1 3)
              have b19064 := hb (x 2 2)
              have b19065 := hb (x 3 13)
              have b19066 := hb (x 4 12)
              clear * - r19060 e19061 e19062 b19063 b19064 b19065 b19066 d19043 f19042
              omega
            have d19067 : (x 3 2 && x 3 13).toNat = 0 := by
              have r19068 := hand2 (x 3 2) (x 3 13)
              have b19069 := hb (x 3 13)
              have b19070 := hb (x 3 2 && x 3 13)
              clear * - r19068 b19069 b19070 d19059
              omega
            have d19071 : (x 2 1 && x 2 14).toNat = 1 := by
              have r19072 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19073 := hb (x 1 2)
              have b19074 := hb (x 3 13)
              have b19075 := hb (x 2 1 && x 2 14)
              clear * - r19072 b19073 b19074 b19075 d19059 d16533
              omega
            have d19076 : (x 2 1).toNat = 1 := by
              have r19077 := hand1 (x 2 1) (x 2 14)
              have b19078 := hb (x 2 1)
              have b19079 := hb (x 2 1 && x 2 14)
              clear * - r19077 b19078 b19079 d19071
              omega
            have d19080 : (x 3 14).toNat = 0 := by
              have r19081 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19082 := hb (x 2 1)
              have b19083 := hb (x 3 14)
              clear * - r19081 b19082 b19083 d19076
              omega
            have d19084 : (x 3 1 && x 3 14).toNat = 0 := by
              have r19085 := hand2 (x 3 1) (x 3 14)
              have b19086 := hb (x 3 14)
              have b19087 := hb (x 3 1 && x 3 14)
              clear * - r19085 b19086 b19087 d19080
              omega
            have d19088 : (x 3 2).toNat = 0 := by
              have r19089 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
              have b19090 := hb (x 3 2)
              have b19091 := hb (x 3 14)
              clear * - r19089 b19090 b19091 d19080
              omega
            have d19092 : (x 2 2).toNat = 0 := by
              have r19093 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19094 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e19095 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b19096 := hb (x 1 3)
              have b19097 := hb (x 2 2)
              have b19098 := hb (x 3 13)
              have b19099 := hb (x 4 12)
              clear * - r19093 e19094 e19095 b19096 b19097 b19098 b19099 d19043 d19059 f19042
              omega
            have d19100 : (x 4 13).toNat = 1 := by
              have r19101 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19102 := hb (x 2 2)
              have b19103 := hb (x 4 13)
              have b19104 := hb (x 3 1 && x 3 14)
              clear * - r19101 b19102 b19103 b19104 d19084 d19092
              omega
            have d19105 : (x 4 1).toNat = 1 := by
              have r19106 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
              have b19107 := hb (x 4 1)
              have b19108 := hb (x 4 13)
              clear * - r19106 b19107 b19108 d19100
              omega
            have d19109 : (x 5 14).toNat = 0 := by
              have r19110 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19111 := hb (x 4 1)
              have b19112 := hb (x 5 14)
              clear * - r19110 b19111 b19112 d19105
              omega
            have d19113 : (x 5 3 && x 5 14).toNat = 0 := by
              have r19114 := hand2 (x 5 3) (x 5 14)
              have b19115 := hb (x 5 14)
              have b19116 := hb (x 5 3 && x 5 14)
              clear * - r19114 b19115 b19116 d19109
              omega
            have d19117 : (x 5 2).toNat = 0 := by
              have r19118 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b19119 := hb (x 5 2)
              have b19120 := hb (x 5 14)
              clear * - r19118 b19119 b19120 d19109
              omega
            have d19121 : (x 5 12).toNat = 0 := by
              have r19122 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19123 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e19124 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b19125 := hb (x 2 3)
              have b19126 := hb (x 3 2)
              have b19127 := hb (x 4 13)
              have b19128 := hb (x 5 12)
              clear * - r19122 e19123 e19124 b19125 b19126 b19127 b19128 d19100 d19088
              omega
            have d19129 : (x 5 4).toNat = 0 := by
              have r19130 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b19131 := hb (x 5 4)
              have b19132 := hb (x 5 12)
              clear * - r19130 b19131 b19132 d19121
              omega
            have d19133 : (x 2 3).toNat = 0 := by
              have r19134 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19135 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e19136 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b19137 := hb (x 2 3)
              have b19138 := hb (x 3 2)
              have b19139 := hb (x 4 13)
              have b19140 := hb (x 5 12)
              clear * - r19134 e19135 e19136 b19137 b19138 b19139 b19140 d19121 d19100 d19088
              omega
            have d19141 : (x 2 3 && x 2 14).toNat = 0 := by
              have r19142 := hand1 (x 2 3) (x 2 14)
              have b19143 := hb (x 2 3)
              have b19144 := hb (x 2 3 && x 2 14)
              clear * - r19142 b19143 b19144 d19133
              omega
            have d19145 : (x 5 11).toNat = 1 := by
              have r19146 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19147 := hb (x 1 4)
              have b19148 := hb (x 5 11)
              have b19149 := hb (x 4 1 && x 4 12)
              have b19150 := hb (x 3 2 && x 3 13)
              have b19151 := hb (x 2 3 && x 2 14)
              clear * - r19146 b19147 b19148 b19149 b19150 b19151 d19051 d19067 d19141 d16989
              omega
            have d19152 : (x 5 3).toNat = 1 := by
              have r19153 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have b19154 := hb (x 5 3)
              have b19155 := hb (x 5 11)
              clear * - r19153 b19154 b19155 d19145
              omega
            have d19156 : (x 8 12).toNat = 0 := by
              have r19157 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19158 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e19159 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b19160 := hb (x 5 3)
              have b19161 := hb (x 6 2)
              have b19162 := hb (x 7 13)
              have b19163 := hb (x 8 12)
              clear * - r19157 e19158 e19159 b19160 b19161 b19162 b19163 d19152
              omega
            have d19164 : (x 8 1 && x 8 12).toNat = 0 := by
              have r19165 := hand2 (x 8 1) (x 8 12)
              have b19166 := hb (x 8 12)
              have b19167 := hb (x 8 1 && x 8 12)
              clear * - r19165 b19166 b19167 d19156
              omega
            have d19168 : (x 8 4).toNat = 0 := by
              have r19169 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have b19170 := hb (x 8 4)
              have b19171 := hb (x 8 12)
              clear * - r19169 b19170 b19171 d19156
              omega
            have d19172 : (x 7 13).toNat = 0 := by
              have r19173 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19174 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e19175 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b19176 := hb (x 5 3)
              have b19177 := hb (x 6 2)
              have b19178 := hb (x 7 13)
              have b19179 := hb (x 8 12)
              clear * - r19173 e19174 e19175 b19176 b19177 b19178 b19179 d19156 d19152
              omega
            have d19180 : (x 7 2 && x 7 13).toNat = 0 := by
              have r19181 := hand2 (x 7 2) (x 7 13)
              have b19182 := hb (x 7 13)
              have b19183 := hb (x 7 2 && x 7 13)
              clear * - r19181 b19182 b19183 d19172
              omega
            have d19184 : (x 6 1 && x 6 14).toNat = 1 := by
              have r19185 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19186 := hb (x 5 2)
              have b19187 := hb (x 7 13)
              have b19188 := hb (x 6 1 && x 6 14)
              clear * - r19185 b19186 b19187 b19188 d19172 d19117
              omega
            have d19189 : (x 6 1).toNat = 1 := by
              have r19190 := hand1 (x 6 1) (x 6 14)
              have b19191 := hb (x 6 1)
              have b19192 := hb (x 6 1 && x 6 14)
              clear * - r19190 b19191 b19192 d19184
              omega
            have d19193 : (x 7 14).toNat = 0 := by
              have r19194 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19195 := hb (x 6 1)
              have b19196 := hb (x 7 14)
              clear * - r19194 b19195 b19196 d19189
              omega
            have d19197 : (x 7 1 && x 7 14).toNat = 0 := by
              have r19198 := hand2 (x 7 1) (x 7 14)
              have b19199 := hb (x 7 14)
              have b19200 := hb (x 7 1 && x 7 14)
              clear * - r19198 b19199 b19200 d19193
              omega
            have d19201 : (x 7 2).toNat = 0 := by
              have r19202 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b19203 := hb (x 7 2)
              have b19204 := hb (x 7 14)
              clear * - r19202 b19203 b19204 d19193
              omega
            have d19205 : (x 6 2).toNat = 0 := by
              have r19206 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19207 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e19208 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b19209 := hb (x 5 3)
              have b19210 := hb (x 6 2)
              have b19211 := hb (x 7 13)
              have b19212 := hb (x 8 12)
              clear * - r19206 e19207 e19208 b19209 b19210 b19211 b19212 d19156 d19172 d19152
              omega
            have d19213 : (x 6 2 && x 6 13).toNat = 0 := by
              have r19214 := hand1 (x 6 2) (x 6 13)
              have b19215 := hb (x 6 2)
              have b19216 := hb (x 6 2 && x 6 13)
              clear * - r19214 b19215 b19216 d19205
              omega
            have d19217 : (x 8 13).toNat = 1 := by
              have r19218 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19219 := hb (x 6 2)
              have b19220 := hb (x 8 13)
              have b19221 := hb (x 7 1 && x 7 14)
              clear * - r19218 b19219 b19220 b19221 d19197 d19205
              omega
            have d19222 : (x 8 1).toNat = 1 := by
              have r19223 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
              have b19224 := hb (x 8 1)
              have b19225 := hb (x 8 13)
              clear * - r19223 b19224 b19225 d19217
              omega
            have d19226 : (x 9 14).toNat = 0 := by
              have r19227 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19228 := hb (x 8 1)
              have b19229 := hb (x 9 14)
              clear * - r19227 b19228 b19229 d19222
              omega
            have d19230 : (x 9 3 && x 9 14).toNat = 0 := by
              have r19231 := hand2 (x 9 3) (x 9 14)
              have b19232 := hb (x 9 14)
              have b19233 := hb (x 9 3 && x 9 14)
              clear * - r19231 b19232 b19233 d19226
              omega
            have d19234 : (x 9 2).toNat = 0 := by
              have r19235 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
              have b19236 := hb (x 9 2)
              have b19237 := hb (x 9 14)
              clear * - r19235 b19236 b19237 d19226
              omega
            have d19238 : (x 9 12).toNat = 0 := by
              have r19239 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19240 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e19241 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b19242 := hb (x 6 3)
              have b19243 := hb (x 7 2)
              have b19244 := hb (x 8 13)
              have b19245 := hb (x 9 12)
              clear * - r19239 e19240 e19241 b19242 b19243 b19244 b19245 d19217 d19201
              omega
            have d19246 : (x 9 4).toNat = 0 := by
              have r19247 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
              have b19248 := hb (x 9 4)
              have b19249 := hb (x 9 12)
              clear * - r19247 b19248 b19249 d19238
              omega
            have d19250 : (x 6 3).toNat = 0 := by
              have r19251 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19252 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e19253 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b19254 := hb (x 6 3)
              have b19255 := hb (x 7 2)
              have b19256 := hb (x 8 13)
              have b19257 := hb (x 9 12)
              clear * - r19251 e19252 e19253 b19254 b19255 b19256 b19257 d19238 d19217 d19201
              omega
            have d19258 : (x 6 3 && x 6 14).toNat = 0 := by
              have r19259 := hand1 (x 6 3) (x 6 14)
              have b19260 := hb (x 6 3)
              have b19261 := hb (x 6 3 && x 6 14)
              clear * - r19259 b19260 b19261 d19250
              omega
            have d19262 : (x 9 11).toNat = 1 := by
              have r19263 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19264 := hb (x 5 4)
              have b19265 := hb (x 9 11)
              have b19266 := hb (x 8 1 && x 8 12)
              have b19267 := hb (x 7 2 && x 7 13)
              have b19268 := hb (x 6 3 && x 6 14)
              clear * - r19263 b19264 b19265 b19266 b19267 b19268 d19164 d19180 d19258 d19129
              omega
            have d19269 : (x 9 3).toNat = 1 := by
              have r19270 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
              have b19271 := hb (x 9 3)
              have b19272 := hb (x 9 11)
              clear * - r19270 b19271 b19272 d19262
              omega
            have d19273 : (x 12 12).toNat = 0 := by
              have r19274 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19275 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e19276 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b19277 := hb (x 9 3)
              have b19278 := hb (x 10 2)
              have b19279 := hb (x 11 13)
              have b19280 := hb (x 12 12)
              clear * - r19274 e19275 e19276 b19277 b19278 b19279 b19280 d19269
              omega
            have d19281 : (x 12 1 && x 12 12).toNat = 0 := by
              have r19282 := hand2 (x 12 1) (x 12 12)
              have b19283 := hb (x 12 12)
              have b19284 := hb (x 12 1 && x 12 12)
              clear * - r19282 b19283 b19284 d19273
              omega
            have d19285 : (x 12 4).toNat = 0 := by
              have r19286 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
              have b19287 := hb (x 12 4)
              have b19288 := hb (x 12 12)
              clear * - r19286 b19287 b19288 d19273
              omega
            have d19289 : (x 11 13).toNat = 0 := by
              have r19290 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19291 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e19292 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b19293 := hb (x 9 3)
              have b19294 := hb (x 10 2)
              have b19295 := hb (x 11 13)
              have b19296 := hb (x 12 12)
              clear * - r19290 e19291 e19292 b19293 b19294 b19295 b19296 d19273 d19269
              omega
            have d19297 : (x 11 2 && x 11 13).toNat = 0 := by
              have r19298 := hand2 (x 11 2) (x 11 13)
              have b19299 := hb (x 11 13)
              have b19300 := hb (x 11 2 && x 11 13)
              clear * - r19298 b19299 b19300 d19289
              omega
            have d19301 : (x 10 1 && x 10 14).toNat = 1 := by
              have r19302 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19303 := hb (x 9 2)
              have b19304 := hb (x 11 13)
              have b19305 := hb (x 10 1 && x 10 14)
              clear * - r19302 b19303 b19304 b19305 d19289 d19234
              omega
            have d19306 : (x 10 14).toNat = 1 := by
              have r19307 := hand2 (x 10 1) (x 10 14)
              have b19308 := hb (x 10 14)
              have b19309 := hb (x 10 1 && x 10 14)
              clear * - r19307 b19308 b19309 d19301
              omega
            have d19310 : (x 9 1).toNat = 0 := by
              have r19311 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19312 := hb (x 9 1)
              have b19313 := hb (x 10 14)
              clear * - r19311 b19312 b19313 d19306
              omega
            have d19314 : (x 9 13).toNat = 0 := by
              have r19315 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
              have b19316 := hb (x 9 1)
              have b19317 := hb (x 9 13)
              clear * - r19315 b19316 b19317 d19310
              omega
            have d19318 : (x 8 1 && x 8 14).toNat = 1 := by
              have r19319 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19320 := hb (x 7 2)
              have b19321 := hb (x 9 13)
              have b19322 := hb (x 8 1 && x 8 14)
              clear * - r19319 b19320 b19321 b19322 d19314 d19201
              omega
            have d19323 : (x 8 14).toNat = 1 := by
              have r19324 := hand2 (x 8 1) (x 8 14)
              have b19325 := hb (x 8 14)
              have b19326 := hb (x 8 1 && x 8 14)
              clear * - r19324 b19325 b19326 d19318
              omega
            have d19327 : (x 7 1).toNat = 0 := by
              have r19328 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19329 := hb (x 7 1)
              have b19330 := hb (x 8 14)
              clear * - r19328 b19329 b19330 d19323
              omega
            have d19331 : (x 7 1 && x 7 12).toNat = 0 := by
              have r19332 := hand1 (x 7 1) (x 7 12)
              have b19333 := hb (x 7 1)
              have b19334 := hb (x 7 1 && x 7 12)
              clear * - r19332 b19333 b19334 d19327
              omega
            have d19335 : (x 8 11).toNat = 1 := by
              have r19336 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19337 := hb (x 4 4)
              have b19338 := hb (x 8 11)
              have b19339 := hb (x 7 1 && x 7 12)
              have b19340 := hb (x 6 2 && x 6 13)
              have b19341 := hb (x 5 3 && x 5 14)
              clear * - r19336 b19337 b19338 b19339 b19340 b19341 d19331 d19213 d19113 d19055
              omega
            have d19342 : (x 8 3).toNat = 1 := by
              have r19343 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
              have b19344 := hb (x 8 3)
              have b19345 := hb (x 8 11)
              clear * - r19343 b19344 b19345 d19335
              omega
            have d19346 : (x 11 12).toNat = 0 := by
              have r19347 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19348 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e19349 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b19350 := hb (x 8 3)
              have b19351 := hb (x 9 2)
              have b19352 := hb (x 10 13)
              have b19353 := hb (x 11 12)
              clear * - r19347 e19348 e19349 b19350 b19351 b19352 b19353 d19234 d19342
              omega
            have d19354 : (x 11 1 && x 11 12).toNat = 0 := by
              have r19355 := hand2 (x 11 1) (x 11 12)
              have b19356 := hb (x 11 12)
              have b19357 := hb (x 11 1 && x 11 12)
              clear * - r19355 b19356 b19357 d19346
              omega
            have d19358 : (x 10 13).toNat = 0 := by
              have r19359 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19360 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e19361 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b19362 := hb (x 8 3)
              have b19363 := hb (x 9 2)
              have b19364 := hb (x 10 13)
              have b19365 := hb (x 11 12)
              clear * - r19359 e19360 e19361 b19362 b19363 b19364 b19365 d19346 d19234 d19342
              omega
            have d19366 : (x 10 2 && x 10 13).toNat = 0 := by
              have r19367 := hand2 (x 10 2) (x 10 13)
              have b19368 := hb (x 10 13)
              have b19369 := hb (x 10 2 && x 10 13)
              clear * - r19367 b19368 b19369 d19358
              omega
            have d19370 : (x 12 11).toNat = 1 := by
              have r19371 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19372 := hb (x 8 4)
              have b19373 := hb (x 12 11)
              have b19374 := hb (x 11 1 && x 11 12)
              have b19375 := hb (x 10 2 && x 10 13)
              have b19376 := hb (x 9 3 && x 9 14)
              clear * - r19371 b19372 b19373 b19374 b19375 b19376 d19354 d19366 d19230 d19168
              omega
            have d19377 : (x 12 3).toNat = 1 := by
              have r19378 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
              have b19379 := hb (x 12 3)
              have b19380 := hb (x 12 11)
              clear * - r19378 b19379 b19380 d19370
              omega
            have d19381 : (x 15 12).toNat = 0 := by
              have r19382 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19383 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e19384 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b19385 := hb (x 12 3)
              have b19386 := hb (x 13 2)
              have b19387 := hb (x 14 13)
              have b19388 := hb (x 15 12)
              clear * - r19382 e19383 e19384 b19385 b19386 b19387 b19388 d19377
              omega
            have d19389 : (x 15 1 && x 15 12).toNat = 0 := by
              have r19390 := hand2 (x 15 1) (x 15 12)
              have b19391 := hb (x 15 12)
              have b19392 := hb (x 15 1 && x 15 12)
              clear * - r19390 b19391 b19392 d19381
              omega
            have d19393 : (x 14 13).toNat = 0 := by
              have r19394 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19395 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e19396 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b19397 := hb (x 12 3)
              have b19398 := hb (x 13 2)
              have b19399 := hb (x 14 13)
              have b19400 := hb (x 15 12)
              clear * - r19394 e19395 e19396 b19397 b19398 b19399 b19400 d19381 d19377
              omega
            have d19401 : (x 14 2 && x 14 13).toNat = 0 := by
              have r19402 := hand2 (x 14 2) (x 14 13)
              have b19403 := hb (x 14 13)
              have b19404 := hb (x 14 2 && x 14 13)
              clear * - r19402 b19403 b19404 d19393
              omega
            have d19405 : (x 13 2).toNat = 0 := by
              have r19406 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19407 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e19408 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b19409 := hb (x 12 3)
              have b19410 := hb (x 13 2)
              have b19411 := hb (x 14 13)
              have b19412 := hb (x 15 12)
              clear * - r19406 e19407 e19408 b19409 b19410 b19411 b19412 d19381 d19393 d19377
              omega
            have d19413 : (x 10 1).toNat = 1 := by
              have r19414 := hand1 (x 10 1) (x 10 14)
              have b19415 := hb (x 10 1)
              have b19416 := hb (x 10 1 && x 10 14)
              clear * - r19414 b19415 b19416 d19301
              omega
            have d19417 : (x 11 14).toNat = 0 := by
              have r19418 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19419 := hb (x 10 1)
              have b19420 := hb (x 11 14)
              clear * - r19418 b19419 b19420 d19413
              omega
            have d19421 : (x 11 1 && x 11 14).toNat = 0 := by
              have r19422 := hand2 (x 11 1) (x 11 14)
              have b19423 := hb (x 11 14)
              have b19424 := hb (x 11 1 && x 11 14)
              clear * - r19422 b19423 b19424 d19417
              omega
            have d19425 : (x 11 2).toNat = 0 := by
              have r19426 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
              have b19427 := hb (x 11 2)
              have b19428 := hb (x 11 14)
              clear * - r19426 b19427 b19428 d19417
              omega
            have d19429 : (x 10 2).toNat = 0 := by
              have r19430 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19431 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e19432 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b19433 := hb (x 9 3)
              have b19434 := hb (x 10 2)
              have b19435 := hb (x 11 13)
              have b19436 := hb (x 12 12)
              clear * - r19430 e19431 e19432 b19433 b19434 b19435 b19436 d19273 d19289 d19269
              omega
            have d19437 : (x 12 13).toNat = 1 := by
              have r19438 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19439 := hb (x 10 2)
              have b19440 := hb (x 12 13)
              have b19441 := hb (x 11 1 && x 11 14)
              clear * - r19438 b19439 b19440 b19441 d19421 d19429
              omega
            have d19442 : (x 12 1).toNat = 1 := by
              have r19443 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
              have b19444 := hb (x 12 1)
              have b19445 := hb (x 12 13)
              clear * - r19443 b19444 b19445 d19437
              omega
            have d19446 : (x 13 14).toNat = 0 := by
              have r19447 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19448 := hb (x 12 1)
              have b19449 := hb (x 13 14)
              clear * - r19447 b19448 b19449 d19442
              omega
            have d19450 : (x 13 1 && x 13 14).toNat = 0 := by
              have r19451 := hand2 (x 13 1) (x 13 14)
              have b19452 := hb (x 13 14)
              have b19453 := hb (x 13 1 && x 13 14)
              clear * - r19451 b19452 b19453 d19446
              omega
            have d19454 : (x 12 2).toNat = 1 := by
              have r19455 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19456 := hb (x 12 2)
              have b19457 := hb (x 14 13)
              have b19458 := hb (x 13 1 && x 13 14)
              clear * - r19455 b19456 b19457 b19458 d19393 d19450
              omega
            have d19459 : (x 14 12).toNat = 0 := by
              have r19460 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19461 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e19462 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b19463 := hb (x 11 3)
              have b19464 := hb (x 12 2)
              have b19465 := hb (x 13 13)
              have b19466 := hb (x 14 12)
              clear * - r19460 e19461 e19462 b19463 b19464 b19465 b19466 d19454
              omega
            have d19467 : (x 14 4).toNat = 0 := by
              have r19468 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
              have b19469 := hb (x 14 4)
              have b19470 := hb (x 14 12)
              clear * - r19468 b19469 b19470 d19459
              omega
            have d19471 : (x 14 4 && x 14 14).toNat = 0 := by
              have r19472 := hand1 (x 14 4) (x 14 14)
              have b19473 := hb (x 14 4)
              have b19474 := hb (x 14 4 && x 14 14)
              clear * - r19472 b19473 b19474 d19467
              omega
            have d19475 : (x 13 13).toNat = 0 := by
              have r19476 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19477 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e19478 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b19479 := hb (x 11 3)
              have b19480 := hb (x 12 2)
              have b19481 := hb (x 13 13)
              have b19482 := hb (x 14 12)
              clear * - r19476 e19477 e19478 b19479 b19480 b19481 b19482 d19459 d19454
              omega
            have d19483 : (x 13 5).toNat = 0 := by
              have r19484 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
              have b19485 := hb (x 13 5)
              have b19486 := hb (x 13 13)
              clear * - r19484 b19485 b19486 d19475
              omega
            have d19487 : (x 13 3 && x 13 14).toNat = 0 := by
              have r19488 := hand2 (x 13 3) (x 13 14)
              have b19489 := hb (x 13 14)
              have b19490 := hb (x 13 3 && x 13 14)
              clear * - r19488 b19489 b19490 d19446
              omega
            have d19491 : (x 16 11).toNat = 1 := by
              have r19492 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19493 := hb (x 12 4)
              have b19494 := hb (x 16 11)
              have b19495 := hb (x 15 1 && x 15 12)
              have b19496 := hb (x 14 2 && x 14 13)
              have b19497 := hb (x 13 3 && x 13 14)
              clear * - r19492 b19493 b19494 b19495 b19496 b19497 d19389 d19401 d19487 d19285
              omega
            have d19498 : (x 16 3).toNat = 1 := by
              have r19499 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
              have b19500 := hb (x 16 3)
              have b19501 := hb (x 16 11)
              clear * - r19499 b19500 b19501 d19491
              omega
            have d19502 : (x 19 12).toNat = 0 := by
              have r19503 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19504 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e19505 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b19506 := hb (x 16 3)
              have b19507 := hb (x 17 2)
              have b19508 := hb (x 18 13)
              have b19509 := hb (x 19 12)
              clear * - r19503 e19504 e19505 b19506 b19507 b19508 b19509 d19498
              omega
            have d19510 : (x 18 13).toNat = 0 := by
              have r19511 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19512 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e19513 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b19514 := hb (x 16 3)
              have b19515 := hb (x 17 2)
              have b19516 := hb (x 18 13)
              have b19517 := hb (x 19 12)
              clear * - r19511 e19512 e19513 b19514 b19515 b19516 b19517 d19502 d19498
              omega
            have d19518 : (x 17 2).toNat = 0 := by
              have r19519 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19520 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e19521 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b19522 := hb (x 16 3)
              have b19523 := hb (x 17 2)
              have b19524 := hb (x 18 13)
              have b19525 := hb (x 19 12)
              clear * - r19519 e19520 e19521 b19522 b19523 b19524 b19525 d19502 d19510 d19498
              omega
            have d19526 : (x 13 12).toNat = 0 := by
              have r19527 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19528 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e19529 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b19530 := hb (x 10 3)
              have b19531 := hb (x 11 2)
              have b19532 := hb (x 12 13)
              have b19533 := hb (x 13 12)
              clear * - r19527 e19528 e19529 b19530 b19531 b19532 b19533 d19437 d19425
              omega
            have d19534 : (x 13 4).toNat = 0 := by
              have r19535 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
              have b19536 := hb (x 13 4)
              have b19537 := hb (x 13 12)
              clear * - r19535 b19536 b19537 d19526
              omega
            have d19538 : (x 10 3).toNat = 0 := by
              have r19539 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19540 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e19541 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b19542 := hb (x 10 3)
              have b19543 := hb (x 11 2)
              have b19544 := hb (x 12 13)
              have b19545 := hb (x 13 12)
              clear * - r19539 e19540 e19541 b19542 b19543 b19544 b19545 d19526 d19437 d19425
              omega
            have d19546 : (x 10 3 && x 10 14).toNat = 0 := by
              have r19547 := hand1 (x 10 3) (x 10 14)
              have b19548 := hb (x 10 3)
              have b19549 := hb (x 10 3 && x 10 14)
              clear * - r19547 b19548 b19549 d19538
              omega
            have d19550 : (x 13 11).toNat = 1 := by
              have r19551 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19552 := hb (x 9 4)
              have b19553 := hb (x 13 11)
              have b19554 := hb (x 12 1 && x 12 12)
              have b19555 := hb (x 11 2 && x 11 13)
              have b19556 := hb (x 10 3 && x 10 14)
              clear * - r19551 b19552 b19553 b19554 b19555 b19556 d19281 d19297 d19546 d19246
              omega
            have d19557 : (x 13 3).toNat = 1 := by
              have r19558 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
              have b19559 := hb (x 13 3)
              have b19560 := hb (x 13 11)
              clear * - r19558 b19559 b19560 d19550
              omega
            have d19561 : (x 16 12).toNat = 0 := by
              have r19562 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19563 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e19564 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b19565 := hb (x 13 3)
              have b19566 := hb (x 14 2)
              have b19567 := hb (x 15 13)
              have b19568 := hb (x 16 12)
              clear * - r19562 e19563 e19564 b19565 b19566 b19567 b19568 d19557
              omega
            have d19569 : (x 16 1 && x 16 12).toNat = 0 := by
              have r19570 := hand2 (x 16 1) (x 16 12)
              have b19571 := hb (x 16 12)
              have b19572 := hb (x 16 1 && x 16 12)
              clear * - r19570 b19571 b19572 d19561
              omega
            have d19573 : (x 16 2 && x 16 12).toNat = 0 := by
              have r19574 := hand2 (x 16 2) (x 16 12)
              have b19575 := hb (x 16 12)
              have b19576 := hb (x 16 2 && x 16 12)
              clear * - r19574 b19575 b19576 d19561
              omega
            have d19577 : (x 15 13).toNat = 0 := by
              have r19578 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19579 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e19580 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b19581 := hb (x 13 3)
              have b19582 := hb (x 14 2)
              have b19583 := hb (x 15 13)
              have b19584 := hb (x 16 12)
              clear * - r19578 e19579 e19580 b19581 b19582 b19583 b19584 d19561 d19557
              omega
            have d19585 : (x 15 2 && x 15 13).toNat = 0 := by
              have r19586 := hand2 (x 15 2) (x 15 13)
              have b19587 := hb (x 15 13)
              have b19588 := hb (x 15 2 && x 15 13)
              clear * - r19586 b19587 b19588 d19577
              omega
            have d19589 : (x 15 3 && x 15 13).toNat = 0 := by
              have r19590 := hand2 (x 15 3) (x 15 13)
              have b19591 := hb (x 15 13)
              have b19592 := hb (x 15 3 && x 15 13)
              clear * - r19590 b19591 b19592 d19577
              omega
            have d19593 : (x 14 1 && x 14 14).toNat = 1 := by
              have r19594 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19595 := hb (x 13 2)
              have b19596 := hb (x 15 13)
              have b19597 := hb (x 14 1 && x 14 14)
              clear * - r19594 b19595 b19596 b19597 d19577 d19405
              omega
            have d19598 : (x 14 1).toNat = 1 := by
              have r19599 := hand1 (x 14 1) (x 14 14)
              have b19600 := hb (x 14 1)
              have b19601 := hb (x 14 1 && x 14 14)
              clear * - r19599 b19600 b19601 d19593
              omega
            have d19602 : (x 15 14).toNat = 0 := by
              have r19603 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19604 := hb (x 14 1)
              have b19605 := hb (x 15 14)
              clear * - r19603 b19604 b19605 d19598
              omega
            have d19606 : (x 15 1 && x 15 14).toNat = 0 := by
              have r19607 := hand2 (x 15 1) (x 15 14)
              have b19608 := hb (x 15 14)
              have b19609 := hb (x 15 1 && x 15 14)
              clear * - r19607 b19608 b19609 d19602
              omega
            have d19610 : (x 15 2).toNat = 0 := by
              have r19611 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
              have b19612 := hb (x 15 2)
              have b19613 := hb (x 15 14)
              clear * - r19611 b19612 b19613 d19602
              omega
            have d19614 : (x 14 2).toNat = 0 := by
              have r19615 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19616 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e19617 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b19618 := hb (x 13 3)
              have b19619 := hb (x 14 2)
              have b19620 := hb (x 15 13)
              have b19621 := hb (x 16 12)
              clear * - r19615 e19616 e19617 b19618 b19619 b19620 b19621 d19561 d19577 d19557
              omega
            have d19622 : (x 16 13).toNat = 1 := by
              have r19623 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19624 := hb (x 14 2)
              have b19625 := hb (x 16 13)
              have b19626 := hb (x 15 1 && x 15 14)
              clear * - r19623 b19624 b19625 b19626 d19606 d19614
              omega
            have d19627 : (x 17 12).toNat = 0 := by
              have r19628 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19629 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e19630 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b19631 := hb (x 14 3)
              have b19632 := hb (x 15 2)
              have b19633 := hb (x 16 13)
              have b19634 := hb (x 17 12)
              clear * - r19628 e19629 e19630 b19631 b19632 b19633 b19634 d19622 d19610
              omega
            have d19635 : (x 14 3).toNat = 0 := by
              have r19636 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19637 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e19638 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b19639 := hb (x 14 3)
              have b19640 := hb (x 15 2)
              have b19641 := hb (x 16 13)
              have b19642 := hb (x 17 12)
              clear * - r19636 e19637 e19638 b19639 b19640 b19641 b19642 d19627 d19622 d19610
              omega
            have d19643 : (x 14 3 && x 14 14).toNat = 0 := by
              have r19644 := hand1 (x 14 3) (x 14 14)
              have b19645 := hb (x 14 3)
              have b19646 := hb (x 14 3 && x 14 14)
              clear * - r19644 b19645 b19646 d19635
              omega
            have d19647 : (x 17 11).toNat = 1 := by
              have r19648 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19649 := hb (x 13 4)
              have b19650 := hb (x 17 11)
              have b19651 := hb (x 16 1 && x 16 12)
              have b19652 := hb (x 15 2 && x 15 13)
              have b19653 := hb (x 14 3 && x 14 14)
              clear * - r19648 b19649 b19650 b19651 b19652 b19653 d19569 d19585 d19643 d19534
              omega
            have d19654 : (x 17 3).toNat = 1 := by
              have r19655 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
              have b19656 := hb (x 17 3)
              have b19657 := hb (x 17 11)
              clear * - r19655 b19656 b19657 d19647
              omega
            have d19658 : (x 20 12).toNat = 0 := by
              have r19659 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19660 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e19661 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b19662 := hb (x 17 3)
              have b19663 := hb (x 18 2)
              have b19664 := hb (x 19 13)
              have b19665 := hb (x 20 12)
              clear * - r19659 e19660 e19661 b19662 b19663 b19664 b19665 d19654
              omega
            have d19666 : (x 19 13).toNat = 0 := by
              have r19667 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19668 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e19669 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b19670 := hb (x 17 3)
              have b19671 := hb (x 18 2)
              have b19672 := hb (x 19 13)
              have b19673 := hb (x 20 12)
              clear * - r19667 e19668 e19669 b19670 b19671 b19672 b19673 d19658 d19654
              omega
            have d19674 : (x 18 1 && x 18 14).toNat = 1 := by
              have r19675 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19676 := hb (x 17 2)
              have b19677 := hb (x 19 13)
              have b19678 := hb (x 18 1 && x 18 14)
              clear * - r19675 b19676 b19677 b19678 d19666 d19518
              omega
            have d19679 : (x 18 14).toNat = 1 := by
              have r19680 := hand2 (x 18 1) (x 18 14)
              have b19681 := hb (x 18 14)
              have b19682 := hb (x 18 1 && x 18 14)
              clear * - r19680 b19681 b19682 d19674
              omega
            have d19683 : (x 17 1).toNat = 0 := by
              have r19684 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19685 := hb (x 17 1)
              have b19686 := hb (x 18 14)
              clear * - r19684 b19685 b19686 d19679
              omega
            have d19687 : (x 17 1 && x 17 11).toNat = 0 := by
              have r19688 := hand1 (x 17 1) (x 17 11)
              have b19689 := hb (x 17 1)
              have b19690 := hb (x 17 1 && x 17 11)
              clear * - r19688 b19689 b19690 d19683
              omega
            have d19691 : (x 18 2).toNat = 0 := by
              have r19692 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19693 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e19694 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b19695 := hb (x 17 3)
              have b19696 := hb (x 18 2)
              have b19697 := hb (x 19 13)
              have b19698 := hb (x 20 12)
              clear * - r19692 e19693 e19694 b19695 b19696 b19697 b19698 d19658 d19666 d19654
              omega
            have d19699 : (x 18 10).toNat = 0 := by
              have r19700 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
              have b19701 := hb (x 18 2)
              have b19702 := hb (x 18 10)
              clear * - r19700 b19701 b19702 d19691
              omega
            have r19703 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19704 := hb (x 13 5)
            have b19705 := hb (x 18 10)
            have b19706 := hb (x 17 1 && x 17 11)
            have b19707 := hb (x 16 2 && x 16 12)
            have b19708 := hb (x 15 3 && x 15 13)
            have b19709 := hb (x 14 4 && x 14 14)
            linarith only [r19703, b19704, b19705, b19706, b19707, b19708, b19709, d19699, d19687, d19573, d19589, d19471, d19483]
        · have f19710 : (x 1 1).toNat = 1 := by rw [h17442]; rfl
          have d19711 : (x 2 14).toNat = 0 := by
            have r19712 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19713 := hb (x 1 1)
            have b19714 := hb (x 2 14)
            clear * - r19712 b19713 b19714 f19710
            omega
          have d19715 : (x 2 1 && x 2 14).toNat = 0 := by
            have r19716 := hand2 (x 2 1) (x 2 14)
            have b19717 := hb (x 2 14)
            have b19718 := hb (x 2 1 && x 2 14)
            clear * - r19716 b19717 b19718 d19711
            omega
          have d19719 : (x 2 6).toNat = 0 := by
            have r19720 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
            have b19721 := hb (x 2 6)
            have b19722 := hb (x 2 14)
            clear * - r19720 b19721 b19722 d19711
            omega
          have d19723 : (x 2 2 && x 2 6).toNat = 0 := by
            have r19724 := hand2 (x 2 2) (x 2 6)
            have b19725 := hb (x 2 6)
            have b19726 := hb (x 2 2 && x 2 6)
            clear * - r19724 b19725 b19726 d19719
            omega
          have d19727 : (x 2 2).toNat = 0 := by
            have r19728 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
            have b19729 := hb (x 2 2)
            have b19730 := hb (x 2 14)
            clear * - r19728 b19729 b19730 d19711
            omega
          have d19731 : (x 3 13).toNat = 1 := by
            have r19732 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19733 := hb (x 1 2)
            have b19734 := hb (x 3 13)
            have b19735 := hb (x 2 1 && x 2 14)
            clear * - r19732 b19733 b19734 b19735 d19715 d16533
            omega
          have d19736 : (x 3 1).toNat = 1 := by
            have r19737 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
            have b19738 := hb (x 3 1)
            have b19739 := hb (x 3 13)
            clear * - r19737 b19738 b19739 d19731
            omega
          have d19740 : (x 4 12).toNat = 0 := by
            have r19741 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19742 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e19743 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b19744 := hb (x 1 3)
            have b19745 := hb (x 2 2)
            have b19746 := hb (x 3 13)
            have b19747 := hb (x 4 12)
            clear * - r19741 e19742 e19743 b19744 b19745 b19746 b19747 d19731 d19727
            omega
          have d19748 : (x 4 3 && x 4 12).toNat = 0 := by
            have r19749 := hand2 (x 4 3) (x 4 12)
            have b19750 := hb (x 4 12)
            have b19751 := hb (x 4 3 && x 4 12)
            clear * - r19749 b19750 b19751 d19740
            omega
          have d19752 : (x 4 4).toNat = 0 := by
            have r19753 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b19754 := hb (x 4 4)
            have b19755 := hb (x 4 12)
            clear * - r19753 b19754 b19755 d19740
            omega
          have d19756 : (x 1 3).toNat = 0 := by
            have r19757 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19758 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e19759 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b19760 := hb (x 1 3)
            have b19761 := hb (x 2 2)
            have b19762 := hb (x 3 13)
            have b19763 := hb (x 4 12)
            clear * - r19757 e19758 e19759 b19760 b19761 b19762 b19763 d19740 d19731 d19727
            omega
          have d19764 : (x 1 3 && x 1 7).toNat = 0 := by
            have r19765 := hand1 (x 1 3) (x 1 7)
            have b19766 := hb (x 1 3)
            have b19767 := hb (x 1 3 && x 1 7)
            clear * - r19765 b19766 b19767 d19756
            omega
          have r19768 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19769 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19770 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19771 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e19772 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e19773 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e19774 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e19775 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e19776 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r19777 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19778 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
          have e19779 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
          have r19780 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19781 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19782 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r19783 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
          have r19784 := hand1 (x (-4) 8) (x (-4) 12)
          have r19785 := hand2 (x 1 1) (x 1 7)
          have r19786 := hand1 (x (-4) 6) (x (-4) 12)
          have r19787 := hand1 (x (-6) 8) (x (-6) 14)
          have r19788 := hand2 (x 6 1) (x 6 10)
          have r19789 := hand2 (x 5 2) (x 5 11)
          have r19790 := hand2 (x (-8) 2) (x (-8) 12)
          have r19791 := hand2 (x (-9) 3) (x (-9) 13)
          have r19792 := hand2 (x (-10) 4) (x (-10) 14)
          linarith only [r19768, r19769, r19770, e19771, e19772, e19773, e19774, e19775, e19776, r19777, e19778, e19779, r19780, r19781, r19782, r19783, r19784, r19785, r19786, r19787, r19788, r19789, r19790, r19791, r19792, d17112, d17084, d17310, d17234, g0, g3, d16969, g5, d16895, g8, f19710, d19756, d16891, d19727, d19719, d19736, d19752, d19723, d19764, d17422, g18, g19, g20, d17060, d17414, d16924, g36, g37, d17056, d19748, d16501, d16529, d17116]
      · have f19856 : (x 0 7).toNat = 1 := by rw [h17432]; rfl
        have d19857 : (x 7 8).toNat = 0 := by
          have r19858 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19859 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e19860 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e19861 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e19862 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e19863 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e19864 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b19865 := hb (x 0 7)
          have b19866 := hb (x 1 6)
          have b19867 := hb (x 2 5)
          have b19868 := hb (x 3 4)
          have b19869 := hb (x 4 11)
          have b19870 := hb (x 5 10)
          have b19871 := hb (x 6 9)
          have b19872 := hb (x 7 8)
          clear * - r19858 e19859 e19860 e19861 e19862 e19863 e19864 b19865 b19866 b19867 b19868 b19869 b19870 b19871 b19872 d16497 d16525 d16891 f19856
          omega
        have d19873 : (x 6 9).toNat = 0 := by
          have r19874 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19875 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e19876 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e19877 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e19878 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e19879 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e19880 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b19881 := hb (x 0 7)
          have b19882 := hb (x 1 6)
          have b19883 := hb (x 2 5)
          have b19884 := hb (x 3 4)
          have b19885 := hb (x 4 11)
          have b19886 := hb (x 5 10)
          have b19887 := hb (x 6 9)
          have b19888 := hb (x 7 8)
          clear * - r19874 e19875 e19876 e19877 e19878 e19879 e19880 b19881 b19882 b19883 b19884 b19885 b19886 b19887 b19888 d19857 d16497 d16525 d16891 f19856
          omega
        have d19889 : (x 5 10).toNat = 0 := by
          have r19890 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19891 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e19892 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e19893 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e19894 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e19895 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e19896 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b19897 := hb (x 0 7)
          have b19898 := hb (x 1 6)
          have b19899 := hb (x 2 5)
          have b19900 := hb (x 3 4)
          have b19901 := hb (x 4 11)
          have b19902 := hb (x 5 10)
          have b19903 := hb (x 6 9)
          have b19904 := hb (x 7 8)
          clear * - r19890 e19891 e19892 e19893 e19894 e19895 e19896 b19897 b19898 b19899 b19900 b19901 b19902 b19903 b19904 d19857 d19873 d16497 d16525 d16891 f19856
          omega
        have d19905 : (x 5 1 && x 5 10).toNat = 0 := by
          have r19906 := hand2 (x 5 1) (x 5 10)
          have b19907 := hb (x 5 10)
          have b19908 := hb (x 5 1 && x 5 10)
          clear * - r19906 b19907 b19908 d19889
          omega
        have d19909 : (x 4 2 && x 4 11).toNat = 1 := by
          have r19910 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19911 := hb (x 0 6)
          have b19912 := hb (x 6 9)
          have b19913 := hb (x 5 1 && x 5 10)
          have b19914 := hb (x 4 2 && x 4 11)
          have b19915 := hb (x 3 3 && x 3 12)
          have b19916 := hb (x 2 4 && x 2 13)
          have b19917 := hb (x 1 5 && x 1 14)
          clear * - r19910 b19911 b19912 b19913 b19914 b19915 b19916 b19917 d19873 d19905 d16489 d16517 d16883 f17427
          omega
        have d19918 : (x 4 11).toNat = 1 := by
          have r19919 := hand2 (x 4 2) (x 4 11)
          have b19920 := hb (x 4 11)
          have b19921 := hb (x 4 2 && x 4 11)
          clear * - r19919 b19920 b19921 d19909
          omega
        have r19922 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19923 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e19924 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e19925 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e19926 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e19927 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e19928 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b19929 := hb (x 0 7)
        have b19930 := hb (x 1 6)
        have b19931 := hb (x 2 5)
        have b19932 := hb (x 3 4)
        have b19933 := hb (x 4 11)
        have b19934 := hb (x 5 10)
        have b19935 := hb (x 6 9)
        have b19936 := hb (x 7 8)
        linarith only [r19922, e19923, e19924, e19925, e19926, e19927, e19928, b19929, b19930, b19931, b19932, b19933, b19934, b19935, b19936, d19857, d19873, d19889, d19918, d16497, d16525, d16891, f19856]
    · have f19937 : (x 0 6).toNat = 1 := by rw [h17426]; rfl
      have d19938 : (x 6 8).toNat = 0 := by
        have r19939 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19940 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e19941 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e19942 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e19943 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e19944 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e19945 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b19946 := hb (x (-1) 7)
        have b19947 := hb (x 0 6)
        have b19948 := hb (x 1 5)
        have b19949 := hb (x 2 4)
        have b19950 := hb (x 3 11)
        have b19951 := hb (x 4 10)
        have b19952 := hb (x 5 9)
        have b19953 := hb (x 6 8)
        clear * - r19939 e19940 e19941 e19942 e19943 e19944 e19945 b19946 b19947 b19948 b19949 b19950 b19951 b19952 b19953 d16945 d16965 f19937
        omega
      have d19954 : (x 5 9).toNat = 0 := by
        have r19955 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19956 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e19957 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e19958 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e19959 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e19960 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e19961 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b19962 := hb (x (-1) 7)
        have b19963 := hb (x 0 6)
        have b19964 := hb (x 1 5)
        have b19965 := hb (x 2 4)
        have b19966 := hb (x 3 11)
        have b19967 := hb (x 4 10)
        have b19968 := hb (x 5 9)
        have b19969 := hb (x 6 8)
        clear * - r19955 e19956 e19957 e19958 e19959 e19960 e19961 b19962 b19963 b19964 b19965 b19966 b19967 b19968 b19969 d19938 d16945 d16965 f19937
        omega
      have d19970 : (x 4 10).toNat = 0 := by
        have r19971 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19972 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e19973 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e19974 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e19975 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e19976 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e19977 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b19978 := hb (x (-1) 7)
        have b19979 := hb (x 0 6)
        have b19980 := hb (x 1 5)
        have b19981 := hb (x 2 4)
        have b19982 := hb (x 3 11)
        have b19983 := hb (x 4 10)
        have b19984 := hb (x 5 9)
        have b19985 := hb (x 6 8)
        clear * - r19971 e19972 e19973 e19974 e19975 e19976 e19977 b19978 b19979 b19980 b19981 b19982 b19983 b19984 b19985 d19938 d19954 d16945 d16965 f19937
        omega
      have d19986 : (x 4 1 && x 4 10).toNat = 0 := by
        have r19987 := hand2 (x 4 1) (x 4 10)
        have b19988 := hb (x 4 10)
        have b19989 := hb (x 4 1 && x 4 10)
        clear * - r19987 b19988 b19989 d19970
        omega
      have d19990 : (x 3 2 && x 3 11).toNat = 1 := by
        have r19991 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b19992 := hb (x (-1) 6)
        have b19993 := hb (x 5 9)
        have b19994 := hb (x 4 1 && x 4 10)
        have b19995 := hb (x 3 2 && x 3 11)
        have b19996 := hb (x 2 3 && x 2 12)
        have b19997 := hb (x 1 4 && x 1 13)
        have b19998 := hb (x 0 5 && x 0 14)
        clear * - r19991 b19992 b19993 b19994 b19995 b19996 b19997 b19998 d19954 d19986 d16941 d16961 g47 d17250
        omega
      have d19999 : (x 3 11).toNat = 1 := by
        have r20000 := hand2 (x 3 2) (x 3 11)
        have b20001 := hb (x 3 11)
        have b20002 := hb (x 3 2 && x 3 11)
        clear * - r20000 b20001 b20002 d19990
        omega
      have r20003 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e20004 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e20005 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e20006 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e20007 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e20008 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e20009 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b20010 := hb (x (-1) 7)
      have b20011 := hb (x 0 6)
      have b20012 := hb (x 1 5)
      have b20013 := hb (x 2 4)
      have b20014 := hb (x 3 11)
      have b20015 := hb (x 4 10)
      have b20016 := hb (x 5 9)
      have b20017 := hb (x 6 8)
      linarith only [r20003, e20004, e20005, e20006, e20007, e20008, e20009, b20010, b20011, b20012, b20013, b20014, b20015, b20016, b20017, d19938, d19954, d19970, d19999, d16945, d16965, f19937]

theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 7).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-2) 2).toNat = 0)
    (g3 : (x (-2) 6).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 13).toNat = 0)
    (g7 : (x 0 3).toNat = 1)
    (g8 : (x 0 4).toNat = 1)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 10).toNat = 0)
    (g11 : (x 0 11).toNat = 0)
    (g12 : (x 0 12).toNat = 1)
    (g13 : (x 1 11).toNat = 0)
    (g14 : (x 2 10).toNat = 0)
    (g15 : (x 3 9).toNat = 0)
    (g16 : (x 4 8).toNat = 0)
    (g17 : (x 0 3 && x 0 5).toNat = 0)
    (g18 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g19 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g20 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g21 : (x 4 4 && x 4 8).toNat = 0)
    (g22 : (x 3 5 && x 3 9).toNat = 0)
    (g23 : (x 2 6 && x 2 10).toNat = 0)
    (g24 : (x 1 7 && x 1 11).toNat = 0)
    (g25 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g26 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g27 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g28 : (x (-1) 5 && x (-1) 10).toNat = 0)
    (g29 : (x (-2) 6 && x (-2) 11).toNat = 0)
    (g30 : (x (-3) 7 && x (-3) 12).toNat = 0)
    (g31 : (x 4 3 && x 4 8).toNat = 0)
    (g32 : (x 3 4 && x 3 9).toNat = 0)
    (g33 : (x 2 5 && x 2 10).toNat = 0)
    (g34 : (x 1 6 && x 1 11).toNat = 0)
    (g35 : (x (-1) 8 && x (-1) 13).toNat = 0)
    (g36 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g37 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g38 : (x 4 2 && x 4 8).toNat = 0)
    (g39 : (x 3 3 && x 3 9).toNat = 0)
    (g40 : (x 2 4 && x 2 10).toNat = 0)
    (g41 : (x 1 5 && x 1 11).toNat = 0)
    (g42 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g43 : (x 0 4 && x 0 11).toNat = 0)
    (g44 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g45 : (x (-2) 6 && x (-2) 13).toNat = 0)
    (g46 : (x (-3) 7 && x (-3) 14).toNat = 0)
    (g47 : (x 0 5 && x 0 14).toNat = 0)
    (g48 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g49 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g50 : (x 0 1 && x 0 11).toNat = 0)
    (g51 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g52 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g53 : (x (-1) 2 && x (-1) 13).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53
