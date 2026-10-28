import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b1110

Topic: combinatorics   Node: ccd3aa8d079a

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 68 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b110.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b110 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 6).toNat = 0)
    (g2 : (x (-1) 5).toNat = 0)
    (g3 : (x (-1) 9).toNat = 0)
    (g4 : (x (-1) 11).toNat = 0)
    (g5 : (x (-1) 13).toNat = 0)
    (g6 : (x 0 4).toNat = 0)
    (g7 : (x 0 14).toNat = 1)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 5).toNat = 0)
    (g10 : (x 1 6).toNat = 0)
    (g11 : (x 1 13).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 5).toNat = 0)
    (g14 : (x 2 12).toNat = 0)
    (g15 : (x 3 4).toNat = 0)
    (g16 : (x 4 9).toNat = 0)
    (g17 : (x 0 8 && x 0 12).toNat = 0)
    (g18 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g19 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g20 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g21 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g22 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g23 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g24 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g25 : (x 0 2 && x 0 8).toNat = 0)
    (g26 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g27 : (x 2 4 && x 2 10).toNat = 0)
    (g28 : (x 1 5 && x 1 11).toNat = 0)
    (g29 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g30 : (x 2 6 && x 2 12).toNat = 0)
    (g31 : (x 1 7 && x 1 13).toNat = 0)
    (g32 : (x 0 8 && x 0 14).toNat = 0)
    (g33 : (x 0 1 && x 0 8).toNat = 0)
    (g34 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g35 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g36 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g37 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g38 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g39 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g40 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g41 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g42 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g43 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g44 : (x 1 2 && x 1 11).toNat = 0)
    (g45 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g46 : (x (-2) 5 && x (-2) 14).toNat = 0)
    (g47 : (x 3 1 && x 3 10).toNat = 0)
    (g48 : (x 2 2 && x 2 11).toNat = 0)
    (g49 : (x 1 3 && x 1 12).toNat = 0)
    (g50 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g51 : (x 3 3 && x 3 12).toNat = 0)
    (g52 : (x 2 4 && x 2 13).toNat = 0)
    (g53 : (x 1 5 && x 1 14).toNat = 0)
    (g54 : (x 2 2 && x 2 12).toNat = 0)
    (g55 : (x 1 3 && x 1 13).toNat = 0)
    (g56 : (x 3 1 && x 3 12).toNat = 0)
    (g57 : (x 2 2 && x 2 13).toNat = 0)
    (g58 : (x 1 3 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d15405 : (x 0 4 && x 0 14).toNat = 0 := by
    have r15406 := hand1 (x 0 4) (x 0 14)
    have b15407 := hb (x 0 4)
    have b15408 := hb (x 0 4 && x 0 14)
    clear * - r15406 b15407 b15408 g6
    omega
  have d15409 : (x 0 4 && x 0 13).toNat = 0 := by
    have r15410 := hand1 (x 0 4) (x 0 13)
    have b15411 := hb (x 0 4)
    have b15412 := hb (x 0 4 && x 0 13)
    clear * - r15410 b15411 b15412 g6
    omega
  have d15413 : (x 4 11).toNat = 1 := by
    have r15414 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15415 := hb (x 0 4)
    have b15416 := hb (x 4 11)
    have b15417 := hb (x 3 1 && x 3 12)
    have b15418 := hb (x 2 2 && x 2 13)
    have b15419 := hb (x 1 3 && x 1 14)
    clear * - r15414 b15415 b15416 b15417 b15418 b15419 g56 g57 g58 g6
    omega
  have d15420 : (x 4 3).toNat = 1 := by
    have r15421 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b15422 := hb (x 4 3)
    have b15423 := hb (x 4 11)
    clear * - r15421 b15422 b15423 d15413
    omega
  have d15424 : (x 7 12).toNat = 0 := by
    have r15425 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15426 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e15427 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b15428 := hb (x 4 3)
    have b15429 := hb (x 5 2)
    have b15430 := hb (x 6 13)
    have b15431 := hb (x 7 12)
    clear * - r15425 e15426 e15427 b15428 b15429 b15430 b15431 d15420
    omega
  have d15432 : (x 7 1 && x 7 12).toNat = 0 := by
    have r15433 := hand2 (x 7 1) (x 7 12)
    have b15434 := hb (x 7 12)
    have b15435 := hb (x 7 1 && x 7 12)
    clear * - r15433 b15434 b15435 d15424
    omega
  have d15436 : (x 7 2 && x 7 12).toNat = 0 := by
    have r15437 := hand2 (x 7 2) (x 7 12)
    have b15438 := hb (x 7 12)
    have b15439 := hb (x 7 2 && x 7 12)
    clear * - r15437 b15438 b15439 d15424
    omega
  have d15440 : (x 7 4).toNat = 0 := by
    have r15441 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b15442 := hb (x 7 4)
    have b15443 := hb (x 7 12)
    clear * - r15441 b15442 b15443 d15424
    omega
  have d15444 : (x 7 4 && x 7 13).toNat = 0 := by
    have r15445 := hand1 (x 7 4) (x 7 13)
    have b15446 := hb (x 7 4)
    have b15447 := hb (x 7 4 && x 7 13)
    clear * - r15445 b15446 b15447 d15440
    omega
  have d15448 : (x 6 13).toNat = 0 := by
    have r15449 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15450 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e15451 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b15452 := hb (x 4 3)
    have b15453 := hb (x 5 2)
    have b15454 := hb (x 6 13)
    have b15455 := hb (x 7 12)
    clear * - r15449 e15450 e15451 b15452 b15453 b15454 b15455 d15424 d15420
    omega
  have d15456 : (x 6 2 && x 6 13).toNat = 0 := by
    have r15457 := hand2 (x 6 2) (x 6 13)
    have b15458 := hb (x 6 13)
    have b15459 := hb (x 6 2 && x 6 13)
    clear * - r15457 b15458 b15459 d15448
    omega
  have d15460 : (x 6 3 && x 6 13).toNat = 0 := by
    have r15461 := hand2 (x 6 3) (x 6 13)
    have b15462 := hb (x 6 13)
    have b15463 := hb (x 6 3 && x 6 13)
    clear * - r15461 b15462 b15463 d15448
    omega
  have d15464 : (x 6 5).toNat = 0 := by
    have r15465 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
    have b15466 := hb (x 6 5)
    have b15467 := hb (x 6 13)
    clear * - r15465 b15466 b15467 d15448
    omega
  have d15468 : (x 6 5 && x 6 14).toNat = 0 := by
    have r15469 := hand1 (x 6 5) (x 6 14)
    have b15470 := hb (x 6 5)
    have b15471 := hb (x 6 5 && x 6 14)
    clear * - r15469 b15470 b15471 d15464
    omega
  have d15472 : (x 5 2).toNat = 0 := by
    have r15473 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15474 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e15475 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b15476 := hb (x 4 3)
    have b15477 := hb (x 5 2)
    have b15478 := hb (x 6 13)
    have b15479 := hb (x 7 12)
    clear * - r15473 e15474 e15475 b15476 b15477 b15478 b15479 d15424 d15448 d15420
    omega
  have d15480 : (x 5 2 && x 5 13).toNat = 0 := by
    have r15481 := hand1 (x 5 2) (x 5 13)
    have b15482 := hb (x 5 2)
    have b15483 := hb (x 5 2 && x 5 13)
    clear * - r15481 b15482 b15483 d15472
    omega
  have d15484 : (x 5 10).toNat = 0 := by
    have r15485 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b15486 := hb (x 5 2)
    have b15487 := hb (x 5 10)
    clear * - r15485 b15486 b15487 d15472
    omega
  have d15488 : (x 5 1 && x 5 10).toNat = 0 := by
    have r15489 := hand2 (x 5 1) (x 5 10)
    have b15490 := hb (x 5 10)
    have b15491 := hb (x 5 1 && x 5 10)
    clear * - r15489 b15490 b15491 d15484
    omega
  have d15492 : (x (-2) 6).toNat = 1 := by
    have r15493 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15494 := hb (x (-2) 6)
    have b15495 := hb (x 4 9)
    have b15496 := hb (x 3 1 && x 3 10)
    have b15497 := hb (x 2 2 && x 2 11)
    have b15498 := hb (x 1 3 && x 1 12)
    have b15499 := hb (x 0 4 && x 0 13)
    have b15500 := hb (x (-1) 5 && x (-1) 14)
    clear * - r15493 b15494 b15495 b15496 b15497 b15498 b15499 b15500 g16 g47 g48 g49 d15409 g50
    omega
  have d15501 : (x (-2) 14).toNat = 1 := by
    have r15502 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b15503 := hb (x (-2) 6)
    have b15504 := hb (x (-2) 14)
    clear * - r15502 b15503 b15504 d15492
    omega
  have d15505 : (x (-3) 1).toNat = 0 := by
    have r15506 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15507 := hb (x (-3) 1)
    have b15508 := hb (x (-2) 14)
    clear * - r15506 b15507 b15508 d15501
    omega
  have d15509 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
    have r15510 := hand1 (x (-3) 1) (x (-3) 11)
    have b15511 := hb (x (-3) 1)
    have b15512 := hb (x (-3) 1 && x (-3) 11)
    clear * - r15510 b15511 b15512 d15505
    omega
  have d15513 : (x (-3) 13).toNat = 0 := by
    have r15514 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b15515 := hb (x (-3) 1)
    have b15516 := hb (x (-3) 13)
    clear * - r15514 b15515 b15516 d15505
    omega
  have d15517 : (x (-3) 5).toNat = 0 := by
    have r15518 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b15519 := hb (x (-3) 5)
    have b15520 := hb (x (-3) 13)
    clear * - r15518 b15519 b15520 d15513
    omega
  have d15521 : (x (-3) 5 && x (-3) 11).toNat = 0 := by
    have r15522 := hand1 (x (-3) 5) (x (-3) 11)
    have b15523 := hb (x (-3) 5)
    have b15524 := hb (x (-3) 5 && x (-3) 11)
    clear * - r15522 b15523 b15524 d15517
    omega
  have d15525 : (x (-3) 9).toNat = 0 := by
    have r15526 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b15527 := hb (x (-3) 1)
    have b15528 := hb (x (-3) 9)
    clear * - r15526 b15527 b15528 d15505
    omega
  have d15529 : (x 7 8).toNat = 0 := by
    have r15530 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15531 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15532 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15533 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15534 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15535 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15536 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15537 := hb (x 0 7)
    have b15538 := hb (x 1 6)
    have b15539 := hb (x 2 5)
    have b15540 := hb (x 3 4)
    have b15541 := hb (x 4 11)
    have b15542 := hb (x 5 10)
    have b15543 := hb (x 6 9)
    have b15544 := hb (x 7 8)
    clear * - r15530 e15531 e15532 e15533 e15534 e15535 e15536 b15537 b15538 b15539 b15540 b15541 b15542 b15543 b15544 d15484 d15413 g15 g13 g10
    omega
  have d15545 : (x 6 9).toNat = 0 := by
    have r15546 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15547 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15548 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15549 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15550 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15551 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15552 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15553 := hb (x 0 7)
    have b15554 := hb (x 1 6)
    have b15555 := hb (x 2 5)
    have b15556 := hb (x 3 4)
    have b15557 := hb (x 4 11)
    have b15558 := hb (x 5 10)
    have b15559 := hb (x 6 9)
    have b15560 := hb (x 7 8)
    clear * - r15546 e15547 e15548 e15549 e15550 e15551 e15552 b15553 b15554 b15555 b15556 b15557 b15558 b15559 b15560 d15529 d15484 d15413 g15 g13 g10
    omega
  have d15561 : (x 4 8).toNat = 0 := by
    have r15562 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15563 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e15564 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e15565 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e15566 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e15567 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e15568 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b15569 := hb (x (-3) 7)
    have b15570 := hb (x (-2) 6)
    have b15571 := hb (x (-1) 5)
    have b15572 := hb (x 0 4)
    have b15573 := hb (x 1 11)
    have b15574 := hb (x 2 10)
    have b15575 := hb (x 3 9)
    have b15576 := hb (x 4 8)
    clear * - r15562 e15563 e15564 e15565 e15566 e15567 e15568 b15569 b15570 b15571 b15572 b15573 b15574 b15575 b15576 g6 g2 d15492
    omega
  have d15577 : (x 4 2 && x 4 8).toNat = 0 := by
    have r15578 := hand2 (x 4 2) (x 4 8)
    have b15579 := hb (x 4 8)
    have b15580 := hb (x 4 2 && x 4 8)
    clear * - r15578 b15579 b15580 d15561
    omega
  have d15581 : (x 4 4 && x 4 8).toNat = 0 := by
    have r15582 := hand2 (x 4 4) (x 4 8)
    have b15583 := hb (x 4 8)
    have b15584 := hb (x 4 4 && x 4 8)
    clear * - r15582 b15583 b15584 d15561
    omega
  have d15585 : (x 3 9).toNat = 0 := by
    have r15586 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15587 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e15588 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e15589 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e15590 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e15591 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e15592 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b15593 := hb (x (-3) 7)
    have b15594 := hb (x (-2) 6)
    have b15595 := hb (x (-1) 5)
    have b15596 := hb (x 0 4)
    have b15597 := hb (x 1 11)
    have b15598 := hb (x 2 10)
    have b15599 := hb (x 3 9)
    have b15600 := hb (x 4 8)
    clear * - r15586 e15587 e15588 e15589 e15590 e15591 e15592 b15593 b15594 b15595 b15596 b15597 b15598 b15599 b15600 d15561 g6 g2 d15492
    omega
  have d15601 : (x 3 3 && x 3 9).toNat = 0 := by
    have r15602 := hand2 (x 3 3) (x 3 9)
    have b15603 := hb (x 3 9)
    have b15604 := hb (x 3 3 && x 3 9)
    clear * - r15602 b15603 b15604 d15585
    omega
  have d15605 : (x 3 5 && x 3 9).toNat = 0 := by
    have r15606 := hand2 (x 3 5) (x 3 9)
    have b15607 := hb (x 3 9)
    have b15608 := hb (x 3 5 && x 3 9)
    clear * - r15606 b15607 b15608 d15585
    omega
  have d15609 : (x 2 10).toNat = 0 := by
    have r15610 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15611 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e15612 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e15613 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e15614 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e15615 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e15616 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b15617 := hb (x (-3) 7)
    have b15618 := hb (x (-2) 6)
    have b15619 := hb (x (-1) 5)
    have b15620 := hb (x 0 4)
    have b15621 := hb (x 1 11)
    have b15622 := hb (x 2 10)
    have b15623 := hb (x 3 9)
    have b15624 := hb (x 4 8)
    clear * - r15610 e15611 e15612 e15613 e15614 e15615 e15616 b15617 b15618 b15619 b15620 b15621 b15622 b15623 b15624 d15561 d15585 g6 g2 d15492
    omega
  have d15625 : (x 2 1 && x 2 10).toNat = 0 := by
    have r15626 := hand2 (x 2 1) (x 2 10)
    have b15627 := hb (x 2 10)
    have b15628 := hb (x 2 1 && x 2 10)
    clear * - r15626 b15627 b15628 d15609
    omega
  have d15629 : (x 0 3 && x 0 12).toNat = 1 := by
    have r15630 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15631 := hb (x (-3) 6)
    have b15632 := hb (x 3 9)
    have b15633 := hb (x 2 1 && x 2 10)
    have b15634 := hb (x 1 2 && x 1 11)
    have b15635 := hb (x 0 3 && x 0 12)
    have b15636 := hb (x (-1) 4 && x (-1) 13)
    have b15637 := hb (x (-2) 5 && x (-2) 14)
    clear * - r15630 b15631 b15632 b15633 b15634 b15635 b15636 b15637 d15585 d15625 g44 g45 g46 g1
    omega
  have d15638 : (x 0 12).toNat = 1 := by
    have r15639 := hand2 (x 0 3) (x 0 12)
    have b15640 := hb (x 0 12)
    have b15641 := hb (x 0 3 && x 0 12)
    clear * - r15639 b15640 b15641 d15629
    omega
  have d15642 : (x (-2) 2).toNat = 0 := by
    have r15643 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15644 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e15645 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b15646 := hb (x (-3) 3)
    have b15647 := hb (x (-2) 2)
    have b15648 := hb (x (-1) 13)
    have b15649 := hb (x 0 12)
    clear * - r15643 e15644 e15645 b15646 b15647 b15648 b15649 d15638 g5
    omega
  have d15650 : (x (-2) 10).toNat = 0 := by
    have r15651 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b15652 := hb (x (-2) 2)
    have b15653 := hb (x (-2) 10)
    clear * - r15651 b15652 b15653 d15642
    omega
  have d15654 : (x (-2) 4 && x (-2) 10).toNat = 0 := by
    have r15655 := hand2 (x (-2) 4) (x (-2) 10)
    have b15656 := hb (x (-2) 10)
    have b15657 := hb (x (-2) 4 && x (-2) 10)
    clear * - r15655 b15656 b15657 d15650
    omega
  have d15658 : (x (-3) 3).toNat = 0 := by
    have r15659 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15660 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e15661 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b15662 := hb (x (-3) 3)
    have b15663 := hb (x (-2) 2)
    have b15664 := hb (x (-1) 13)
    have b15665 := hb (x 0 12)
    clear * - r15659 e15660 e15661 b15662 b15663 b15664 b15665 d15638 g5 d15642
    omega
  have d15666 : (x (-3) 11).toNat = 0 := by
    have r15667 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b15668 := hb (x (-3) 3)
    have b15669 := hb (x (-3) 11)
    clear * - r15667 b15668 b15669 d15658
    omega
  have d15670 : (x 2 6 && x 2 10).toNat = 0 := by
    have r15671 := hand2 (x 2 6) (x 2 10)
    have b15672 := hb (x 2 10)
    have b15673 := hb (x 2 6 && x 2 10)
    clear * - r15671 b15672 b15673 d15609
    omega
  have d15674 : (x 1 11).toNat = 0 := by
    have r15675 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15676 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e15677 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e15678 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e15679 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e15680 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e15681 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b15682 := hb (x (-3) 7)
    have b15683 := hb (x (-2) 6)
    have b15684 := hb (x (-1) 5)
    have b15685 := hb (x 0 4)
    have b15686 := hb (x 1 11)
    have b15687 := hb (x 2 10)
    have b15688 := hb (x 3 9)
    have b15689 := hb (x 4 8)
    clear * - r15675 e15676 e15677 e15678 e15679 e15680 e15681 b15682 b15683 b15684 b15685 b15686 b15687 b15688 b15689 d15561 d15585 d15609 g6 g2 d15492
    omega
  have d15690 : (x 1 7 && x 1 11).toNat = 0 := by
    have r15691 := hand2 (x 1 7) (x 1 11)
    have b15692 := hb (x 1 11)
    have b15693 := hb (x 1 7 && x 1 11)
    clear * - r15691 b15692 b15693 d15674
    omega
  cases h15694 : x 0 6
  · have f15695 : (x 0 6).toNat = 0 := by rw [h15694]; rfl
    have d15696 : (x 0 6 && x 0 12).toNat = 0 := by
      have r15697 := hand1 (x 0 6) (x 0 12)
      have b15698 := hb (x 0 6)
      have b15699 := hb (x 0 6 && x 0 12)
      clear * - r15697 b15698 b15699 f15695
      omega
    have d15700 : (x 0 1 && x 0 6).toNat = 0 := by
      have r15701 := hand2 (x 0 1) (x 0 6)
      have b15702 := hb (x 0 6)
      have b15703 := hb (x 0 1 && x 0 6)
      clear * - r15701 b15702 b15703 f15695
      omega
    have d15704 : (x 4 2 && x 4 11).toNat = 1 := by
      have r15705 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15706 := hb (x 0 6)
      have b15707 := hb (x 6 9)
      have b15708 := hb (x 5 1 && x 5 10)
      have b15709 := hb (x 4 2 && x 4 11)
      have b15710 := hb (x 3 3 && x 3 12)
      have b15711 := hb (x 2 4 && x 2 13)
      have b15712 := hb (x 1 5 && x 1 14)
      clear * - r15705 b15706 b15707 b15708 b15709 b15710 b15711 b15712 d15545 d15488 g51 g52 g53 f15695
      omega
    have d15713 : (x 4 2).toNat = 1 := by
      have r15714 := hand1 (x 4 2) (x 4 11)
      have b15715 := hb (x 4 2)
      have b15716 := hb (x 4 2 && x 4 11)
      clear * - r15714 b15715 b15716 d15704
      omega
    have d15717 : (x 4 14).toNat = 1 := by
      have r15718 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b15719 := hb (x 4 2)
      have b15720 := hb (x 4 14)
      clear * - r15718 b15719 b15720 d15713
      omega
    have d15721 : (x 3 1).toNat = 0 := by
      have r15722 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15723 := hb (x 3 1)
      have b15724 := hb (x 4 14)
      clear * - r15722 b15723 b15724 d15717
      omega
    have d15725 : (x 3 1 && x 3 11).toNat = 0 := by
      have r15726 := hand1 (x 3 1) (x 3 11)
      have b15727 := hb (x 3 1)
      have b15728 := hb (x 3 1 && x 3 11)
      clear * - r15726 b15727 b15728 d15721
      omega
    have d15729 : (x 4 10).toNat = 1 := by
      have r15730 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15731 := hb (x (-1) 5)
      have b15732 := hb (x 4 10)
      have b15733 := hb (x 3 1 && x 3 11)
      have b15734 := hb (x 2 2 && x 2 12)
      have b15735 := hb (x 1 3 && x 1 13)
      have b15736 := hb (x 0 4 && x 0 14)
      clear * - r15730 b15731 b15732 b15733 b15734 b15735 b15736 d15725 g54 g55 d15405 g2
      omega
    have d15737 : (x 3 13).toNat = 0 := by
      have r15738 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b15739 := hb (x 3 1)
      have b15740 := hb (x 3 13)
      clear * - r15738 b15739 b15740 d15721
      omega
    have d15741 : (x 3 7 && x 3 13).toNat = 0 := by
      have r15742 := hand2 (x 3 7) (x 3 13)
      have b15743 := hb (x 3 13)
      have b15744 := hb (x 3 7 && x 3 13)
      clear * - r15742 b15743 b15744 d15737
      omega
    have d15745 : (x 3 5).toNat = 0 := by
      have r15746 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b15747 := hb (x 3 5)
      have b15748 := hb (x 3 13)
      clear * - r15746 b15747 b15748 d15737
      omega
    have d15749 : (x 3 5 && x 3 11).toNat = 0 := by
      have r15750 := hand1 (x 3 5) (x 3 11)
      have b15751 := hb (x 3 5)
      have b15752 := hb (x 3 5 && x 3 11)
      clear * - r15750 b15751 b15752 d15745
      omega
    have d15753 : (x 2 1 && x 2 14).toNat = 1 := by
      have r15754 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15755 := hb (x 1 2)
      have b15756 := hb (x 3 13)
      have b15757 := hb (x 2 1 && x 2 14)
      clear * - r15754 b15755 b15756 b15757 d15737 g8
      omega
    have d15758 : (x 2 14).toNat = 1 := by
      have r15759 := hand2 (x 2 1) (x 2 14)
      have b15760 := hb (x 2 14)
      have b15761 := hb (x 2 1 && x 2 14)
      clear * - r15759 b15760 b15761 d15753
      omega
    have d15762 : (x 1 1).toNat = 0 := by
      have r15763 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15764 := hb (x 1 1)
      have b15765 := hb (x 2 14)
      clear * - r15763 b15764 b15765 d15758
      omega
    have d15766 : (x 1 1 && x 1 7).toNat = 0 := by
      have r15767 := hand1 (x 1 1) (x 1 7)
      have b15768 := hb (x 1 1)
      have b15769 := hb (x 1 1 && x 1 7)
      clear * - r15767 b15768 b15769 d15762
      omega
    have d15770 : (x 1 9).toNat = 0 := by
      have r15771 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b15772 := hb (x 1 1)
      have b15773 := hb (x 1 9)
      clear * - r15771 b15772 b15773 d15762
      omega
    have d15774 : (x 2 1).toNat = 1 := by
      have r15775 := hand1 (x 2 1) (x 2 14)
      have b15776 := hb (x 2 1)
      have b15777 := hb (x 2 1 && x 2 14)
      clear * - r15775 b15776 b15777 d15753
      omega
    have d15778 : (x 3 14).toNat = 0 := by
      have r15779 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15780 := hb (x 2 1)
      have b15781 := hb (x 3 14)
      clear * - r15779 b15780 b15781 d15774
      omega
    have d15782 : (x 3 2).toNat = 0 := by
      have r15783 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b15784 := hb (x 3 2)
      have b15785 := hb (x 3 14)
      clear * - r15783 b15784 b15785 d15778
      omega
    have d15786 : (x 6 12).toNat = 0 := by
      have r15787 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15788 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e15789 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b15790 := hb (x 3 3)
      have b15791 := hb (x 4 2)
      have b15792 := hb (x 5 13)
      have b15793 := hb (x 6 12)
      clear * - r15787 e15788 e15789 b15790 b15791 b15792 b15793 d15713
      omega
    have d15794 : (x 6 2 && x 6 12).toNat = 0 := by
      have r15795 := hand2 (x 6 2) (x 6 12)
      have b15796 := hb (x 6 12)
      have b15797 := hb (x 6 2 && x 6 12)
      clear * - r15795 b15796 b15797 d15786
      omega
    have d15798 : (x 6 4).toNat = 0 := by
      have r15799 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b15800 := hb (x 6 4)
      have b15801 := hb (x 6 12)
      clear * - r15799 b15800 b15801 d15786
      omega
    have d15802 : (x 6 4 && x 6 10).toNat = 0 := by
      have r15803 := hand1 (x 6 4) (x 6 10)
      have b15804 := hb (x 6 4)
      have b15805 := hb (x 6 4 && x 6 10)
      clear * - r15803 b15804 b15805 d15798
      omega
    have d15806 : (x 5 13).toNat = 0 := by
      have r15807 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15808 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e15809 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b15810 := hb (x 3 3)
      have b15811 := hb (x 4 2)
      have b15812 := hb (x 5 13)
      have b15813 := hb (x 6 12)
      clear * - r15807 e15808 e15809 b15810 b15811 b15812 b15813 d15786 d15713
      omega
    have d15814 : (x 5 3 && x 5 13).toNat = 0 := by
      have r15815 := hand2 (x 5 3) (x 5 13)
      have b15816 := hb (x 5 13)
      have b15817 := hb (x 5 3 && x 5 13)
      clear * - r15815 b15816 b15817 d15806
      omega
    have d15818 : (x 5 5).toNat = 0 := by
      have r15819 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
      have b15820 := hb (x 5 5)
      have b15821 := hb (x 5 13)
      clear * - r15819 b15820 b15821 d15806
      omega
    have d15822 : (x 5 5 && x 5 11).toNat = 0 := by
      have r15823 := hand1 (x 5 5) (x 5 11)
      have b15824 := hb (x 5 5)
      have b15825 := hb (x 5 5 && x 5 11)
      clear * - r15823 b15824 b15825 d15818
      omega
    have d15826 : (x 4 1 && x 4 14).toNat = 1 := by
      have r15827 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15828 := hb (x 3 2)
      have b15829 := hb (x 5 13)
      have b15830 := hb (x 4 1 && x 4 14)
      clear * - r15827 b15828 b15829 b15830 d15806 d15782
      omega
    have d15831 : (x 4 1).toNat = 1 := by
      have r15832 := hand1 (x 4 1) (x 4 14)
      have b15833 := hb (x 4 1)
      have b15834 := hb (x 4 1 && x 4 14)
      clear * - r15832 b15833 b15834 d15826
      omega
    have d15835 : (x 5 14).toNat = 0 := by
      have r15836 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15837 := hb (x 4 1)
      have b15838 := hb (x 5 14)
      clear * - r15836 b15837 b15838 d15831
      omega
    have d15839 : (x 5 6).toNat = 0 := by
      have r15840 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
      have b15841 := hb (x 5 6)
      have b15842 := hb (x 5 14)
      clear * - r15840 b15841 b15842 d15835
      omega
    have d15843 : (x 3 3).toNat = 0 := by
      have r15844 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15845 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e15846 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b15847 := hb (x 3 3)
      have b15848 := hb (x 4 2)
      have b15849 := hb (x 5 13)
      have b15850 := hb (x 6 12)
      clear * - r15844 e15845 e15846 b15847 b15848 b15849 b15850 d15786 d15806 d15713
      omega
    have d15851 : (x 3 11).toNat = 0 := by
      have r15852 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b15853 := hb (x 3 3)
      have b15854 := hb (x 3 11)
      clear * - r15852 b15853 b15854 d15843
      omega
    have d15855 : (x 0 1 && x 0 10).toNat = 1 := by
      have r15856 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b15857 := hb (x (-5) 6)
      have b15858 := hb (x 1 9)
      have b15859 := hb (x 0 1 && x 0 10)
      have b15860 := hb (x (-1) 2 && x (-1) 11)
      have b15861 := hb (x (-2) 3 && x (-2) 12)
      have b15862 := hb (x (-3) 4 && x (-3) 13)
      have b15863 := hb (x (-4) 5 && x (-4) 14)
      clear * - r15856 b15857 b15858 b15859 b15860 b15861 b15862 b15863 d15770 g40 g41 g42 g43 g0
      omega
    have d15864 : (x 0 10).toNat = 1 := by
      have r15865 := hand2 (x 0 1) (x 0 10)
      have b15866 := hb (x 0 10)
      have b15867 := hb (x 0 1 && x 0 10)
      clear * - r15865 b15866 b15867 d15855
      omega
    have d15868 : (x 6 8).toNat = 0 := by
      have r15869 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15870 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e15871 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e15872 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e15873 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e15874 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e15875 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b15876 := hb (x (-1) 7)
      have b15877 := hb (x 0 6)
      have b15878 := hb (x 1 5)
      have b15879 := hb (x 2 4)
      have b15880 := hb (x 3 11)
      have b15881 := hb (x 4 10)
      have b15882 := hb (x 5 9)
      have b15883 := hb (x 6 8)
      clear * - r15869 e15870 e15871 e15872 e15873 e15874 e15875 b15876 b15877 b15878 b15879 b15880 b15881 b15882 b15883 d15729 d15851 g12 g9 f15695
      omega
    have d15884 : (x 6 2 && x 6 8).toNat = 0 := by
      have r15885 := hand2 (x 6 2) (x 6 8)
      have b15886 := hb (x 6 8)
      have b15887 := hb (x 6 2 && x 6 8)
      clear * - r15885 b15886 b15887 d15868
      omega
    have d15888 : (x 5 9).toNat = 0 := by
      have r15889 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15890 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e15891 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e15892 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e15893 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e15894 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e15895 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b15896 := hb (x (-1) 7)
      have b15897 := hb (x 0 6)
      have b15898 := hb (x 1 5)
      have b15899 := hb (x 2 4)
      have b15900 := hb (x 3 11)
      have b15901 := hb (x 4 10)
      have b15902 := hb (x 5 9)
      have b15903 := hb (x 6 8)
      clear * - r15889 e15890 e15891 e15892 e15893 e15894 e15895 b15896 b15897 b15898 b15899 b15900 b15901 b15902 b15903 d15868 d15729 d15851 g12 g9 f15695
      omega
    have d15904 : (x 5 3 && x 5 9).toNat = 0 := by
      have r15905 := hand2 (x 5 3) (x 5 9)
      have b15906 := hb (x 5 9)
      have b15907 := hb (x 5 3 && x 5 9)
      clear * - r15905 b15906 b15907 d15888
      omega
    have d15908 : (x 2 8).toNat = 0 := by
      have r15909 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15910 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e15911 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e15912 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e15913 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e15914 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e15915 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b15916 := hb (x (-5) 7)
      have b15917 := hb (x (-4) 6)
      have b15918 := hb (x (-3) 5)
      have b15919 := hb (x (-2) 4)
      have b15920 := hb (x (-1) 11)
      have b15921 := hb (x 0 10)
      have b15922 := hb (x 1 9)
      have b15923 := hb (x 2 8)
      clear * - r15909 e15910 e15911 e15912 e15913 e15914 e15915 b15916 b15917 b15918 b15919 b15920 b15921 b15922 b15923 d15770 d15864 g4 d15517
      omega
    have d15924 : (x 2 8 && x 2 14).toNat = 0 := by
      have r15925 := hand1 (x 2 8) (x 2 14)
      have b15926 := hb (x 2 8)
      have b15927 := hb (x 2 8 && x 2 14)
      clear * - r15925 b15926 b15927 d15908
      omega
    have d15928 : (x (-2) 4).toNat = 0 := by
      have r15929 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15930 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e15931 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e15932 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e15933 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e15934 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e15935 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b15936 := hb (x (-5) 7)
      have b15937 := hb (x (-4) 6)
      have b15938 := hb (x (-3) 5)
      have b15939 := hb (x (-2) 4)
      have b15940 := hb (x (-1) 11)
      have b15941 := hb (x 0 10)
      have b15942 := hb (x 1 9)
      have b15943 := hb (x 2 8)
      clear * - r15929 e15930 e15931 e15932 e15933 e15934 e15935 b15936 b15937 b15938 b15939 b15940 b15941 b15942 b15943 d15908 d15770 d15864 g4 d15517
      omega
    have d15944 : (x (-4) 6).toNat = 0 := by
      have r15945 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15946 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e15947 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e15948 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e15949 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e15950 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e15951 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b15952 := hb (x (-5) 7)
      have b15953 := hb (x (-4) 6)
      have b15954 := hb (x (-3) 5)
      have b15955 := hb (x (-2) 4)
      have b15956 := hb (x (-1) 11)
      have b15957 := hb (x 0 10)
      have b15958 := hb (x 1 9)
      have b15959 := hb (x 2 8)
      clear * - r15945 e15946 e15947 e15948 e15949 e15950 e15951 b15952 b15953 b15954 b15955 b15956 b15957 b15958 b15959 d15908 d15770 d15864 g4 d15928 d15517
      omega
    have d15960 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
      have r15961 := hand1 (x (-4) 6) (x (-4) 12)
      have b15962 := hb (x (-4) 6)
      have b15963 := hb (x (-4) 6 && x (-4) 12)
      clear * - r15961 b15962 b15963 d15944
      omega
    have d15964 : (x (-5) 7).toNat = 0 := by
      have r15965 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e15966 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e15967 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e15968 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e15969 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e15970 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e15971 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b15972 := hb (x (-5) 7)
      have b15973 := hb (x (-4) 6)
      have b15974 := hb (x (-3) 5)
      have b15975 := hb (x (-2) 4)
      have b15976 := hb (x (-1) 11)
      have b15977 := hb (x 0 10)
      have b15978 := hb (x 1 9)
      have b15979 := hb (x 2 8)
      clear * - r15965 e15966 e15967 e15968 e15969 e15970 e15971 b15972 b15973 b15974 b15975 b15976 b15977 b15978 b15979 d15908 d15770 d15864 g4 d15928 d15517 d15944
      omega
    have d15980 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
      have r15981 := hand1 (x (-5) 7) (x (-5) 13)
      have b15982 := hb (x (-5) 7)
      have b15983 := hb (x (-5) 7 && x (-5) 13)
      clear * - r15981 b15982 b15983 d15964
      omega
    have r15984 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r15985 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15986 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
    have e15987 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
    have e15988 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
    have e15989 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
    have e15990 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
    have e15991 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
    have r15992 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15993 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
    have e15994 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
    have e15995 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
    have e15996 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
    have e15997 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
    have e15998 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
    have r15999 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16000 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e16001 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e16002 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e16003 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e16004 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e16005 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have r16006 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16007 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e16008 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e16009 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e16010 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e16011 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e16012 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have r16013 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16014 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e16015 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e16016 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e16017 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e16018 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e16019 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have r16020 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16021 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e16022 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e16023 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e16024 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e16025 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e16026 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have r16027 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16028 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e16029 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e16030 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e16031 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e16032 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e16033 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have r16034 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16035 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
    have e16036 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
    have r16037 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16038 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e16039 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have r16040 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16041 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e16042 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have r16043 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16044 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
    have e16045 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
    have r16046 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16047 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16048 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16049 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16050 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16051 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16052 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16053 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16054 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16055 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16056 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r16057 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have r16058 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
    have r16059 := hand1 (x 6 2) (x 6 6)
    have r16060 := hand1 (x 5 3) (x 5 7)
    have r16061 := hand2 (x (-7) 8) (x (-7) 13)
    have r16062 := hand1 (x (-8) 9) (x (-8) 14)
    have r16063 := hand1 (x (-6) 8) (x (-6) 14)
    have r16064 := hand2 (x 5 1) (x 5 7)
    have r16065 := hand1 (x (-2) 8) (x (-2) 14)
    have r16066 := hand2 (x 7 1) (x 7 7)
    have r16067 := hand1 (x 4 4) (x 4 10)
    have r16068 := hand2 (x 9 1) (x 9 7)
    have r16069 := hand2 (x 8 2) (x 8 8)
    have r16070 := hand2 (x 7 3) (x 7 9)
    have r16071 := hand1 (x 4 6) (x 4 12)
    have r16072 := hand2 (x 10 1) (x 10 10)
    have r16073 := hand2 (x 9 2) (x 9 11)
    have r16074 := hand2 (x 8 3) (x 8 12)
    have r16075 := hand2 (x (-7) 1) (x (-7) 11)
    have r16076 := hand1 (x (-8) 2) (x (-8) 12)
    have r16077 := hand1 (x (-9) 3) (x (-9) 13)
    have r16078 := hand1 (x (-10) 4) (x (-10) 14)
    have r16079 := hand2 (x (-4) 2) (x (-4) 12)
    have r16080 := hand2 (x (-5) 3) (x (-5) 13)
    have r16081 := hand1 (x (-6) 4) (x (-6) 14)
    have r16082 := hand2 (x 7 1) (x 7 11)
    have r16083 := hand1 (x 4 4) (x 4 14)
    have r16084 := hand1 (x 13 1) (x 13 11)
    have r16085 := hand1 (x 12 2) (x 12 12)
    have r16086 := hand1 (x 11 3) (x 11 13)
    have r16087 := hand1 (x 10 4) (x 10 14)
    linarith only [r15984, r15985, e15986, e15987, e15988, e15989, e15990, e15991, r15992, e15993, e15994, e15995, e15996, e15997, e15998, r15999, e16000, e16001, e16002, e16003, e16004, e16005, r16006, e16007, e16008, e16009, e16010, e16011, e16012, r16013, e16014, e16015, e16016, e16017, e16018, e16019, r16020, e16021, e16022, e16023, e16024, e16025, e16026, r16027, e16028, e16029, e16030, e16031, e16032, e16033, r16034, e16035, e16036, r16037, e16038, e16039, r16040, e16041, e16042, r16043, e16044, e16045, r16046, r16047, r16048, r16049, r16050, r16051, r16052, r16053, r16054, r16055, r16056, r16057, r16058, r16059, r16060, r16061, r16062, r16063, r16064, r16065, r16066, r16067, r16068, r16069, r16070, r16071, r16072, r16073, r16074, r16075, r16076, r16077, r16078, r16079, r16080, r16081, r16082, r16083, r16084, r16085, r16086, r16087, d15525, d15666, d15650, g3, g7, g9, d15770, g11, g14, d15745, d15851, d15729, d15818, d15839, d15888, d15798, d15868, d15581, d15605, d15670, d15690, g17, g18, d15700, g19, g20, g21, g22, g23, g24, d15766, g25, g26, d15654, d15521, d15960, d15980, d15577, d15601, g27, g28, d15696, g29, d15884, d15904, d15749, g30, g31, g32, d15802, d15822, d15741, d15924, g33, g34, g35, g36, g37, g38, g39, d15444, d15468, d15509, d15794, d15814]
  · have f16255 : (x 0 6).toNat = 1 := by rw [h15694]; rfl
    have d16256 : (x 6 8).toNat = 0 := by
      have r16257 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16258 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e16259 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e16260 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e16261 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e16262 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e16263 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b16264 := hb (x (-1) 7)
      have b16265 := hb (x 0 6)
      have b16266 := hb (x 1 5)
      have b16267 := hb (x 2 4)
      have b16268 := hb (x 3 11)
      have b16269 := hb (x 4 10)
      have b16270 := hb (x 5 9)
      have b16271 := hb (x 6 8)
      clear * - r16257 e16258 e16259 e16260 e16261 e16262 e16263 b16264 b16265 b16266 b16267 b16268 b16269 b16270 b16271 g12 g9 f16255
      omega
    have d16272 : (x 5 9).toNat = 0 := by
      have r16273 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16274 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e16275 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e16276 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e16277 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e16278 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e16279 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b16280 := hb (x (-1) 7)
      have b16281 := hb (x 0 6)
      have b16282 := hb (x 1 5)
      have b16283 := hb (x 2 4)
      have b16284 := hb (x 3 11)
      have b16285 := hb (x 4 10)
      have b16286 := hb (x 5 9)
      have b16287 := hb (x 6 8)
      clear * - r16273 e16274 e16275 e16276 e16277 e16278 e16279 b16280 b16281 b16282 b16283 b16284 b16285 b16286 b16287 d16256 g12 g9 f16255
      omega
    have d16288 : (x 4 10).toNat = 0 := by
      have r16289 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16290 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e16291 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e16292 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e16293 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e16294 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e16295 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b16296 := hb (x (-1) 7)
      have b16297 := hb (x 0 6)
      have b16298 := hb (x 1 5)
      have b16299 := hb (x 2 4)
      have b16300 := hb (x 3 11)
      have b16301 := hb (x 4 10)
      have b16302 := hb (x 5 9)
      have b16303 := hb (x 6 8)
      clear * - r16289 e16290 e16291 e16292 e16293 e16294 e16295 b16296 b16297 b16298 b16299 b16300 b16301 b16302 b16303 d16256 d16272 g12 g9 f16255
      omega
    have d16304 : (x 3 1 && x 3 11).toNat = 1 := by
      have r16305 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16306 := hb (x (-1) 5)
      have b16307 := hb (x 4 10)
      have b16308 := hb (x 3 1 && x 3 11)
      have b16309 := hb (x 2 2 && x 2 12)
      have b16310 := hb (x 1 3 && x 1 13)
      have b16311 := hb (x 0 4 && x 0 14)
      clear * - r16305 b16306 b16307 b16308 b16309 b16310 b16311 d16288 g54 g55 d15405 g2
      omega
    have d16312 : (x 3 11).toNat = 1 := by
      have r16313 := hand2 (x 3 1) (x 3 11)
      have b16314 := hb (x 3 11)
      have b16315 := hb (x 3 1 && x 3 11)
      clear * - r16313 b16314 b16315 d16304
      omega
    have d16316 : (x 3 3).toNat = 1 := by
      have r16317 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b16318 := hb (x 3 3)
      have b16319 := hb (x 3 11)
      clear * - r16317 b16318 b16319 d16312
      omega
    have d16320 : (x 6 12).toNat = 0 := by
      have r16321 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16322 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e16323 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b16324 := hb (x 3 3)
      have b16325 := hb (x 4 2)
      have b16326 := hb (x 5 13)
      have b16327 := hb (x 6 12)
      clear * - r16321 e16322 e16323 b16324 b16325 b16326 b16327 d16316
      omega
    have d16328 : (x 6 1 && x 6 12).toNat = 0 := by
      have r16329 := hand2 (x 6 1) (x 6 12)
      have b16330 := hb (x 6 12)
      have b16331 := hb (x 6 1 && x 6 12)
      clear * - r16329 b16330 b16331 d16320
      omega
    have d16332 : (x 5 13).toNat = 0 := by
      have r16333 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16334 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e16335 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b16336 := hb (x 3 3)
      have b16337 := hb (x 4 2)
      have b16338 := hb (x 5 13)
      have b16339 := hb (x 6 12)
      clear * - r16333 e16334 e16335 b16336 b16337 b16338 b16339 d16320 d16316
      omega
    have d16340 : (x 4 2).toNat = 0 := by
      have r16341 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16342 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e16343 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b16344 := hb (x 3 3)
      have b16345 := hb (x 4 2)
      have b16346 := hb (x 5 13)
      have b16347 := hb (x 6 12)
      clear * - r16341 e16342 e16343 b16344 b16345 b16346 b16347 d16320 d16332 d16316
      omega
    have d16348 : (x 5 1 && x 5 14).toNat = 1 := by
      have r16349 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16350 := hb (x 4 2)
      have b16351 := hb (x 6 13)
      have b16352 := hb (x 5 1 && x 5 14)
      clear * - r16349 b16350 b16351 b16352 d15448 d16340
      omega
    have d16353 : (x 5 14).toNat = 1 := by
      have r16354 := hand2 (x 5 1) (x 5 14)
      have b16355 := hb (x 5 14)
      have b16356 := hb (x 5 1 && x 5 14)
      clear * - r16354 b16355 b16356 d16348
      omega
    have d16357 : (x 4 1).toNat = 0 := by
      have r16358 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16359 := hb (x 4 1)
      have b16360 := hb (x 5 14)
      clear * - r16358 b16359 b16360 d16353
      omega
    have d16361 : (x 4 1 && x 4 14).toNat = 0 := by
      have r16362 := hand1 (x 4 1) (x 4 14)
      have b16363 := hb (x 4 1)
      have b16364 := hb (x 4 1 && x 4 14)
      clear * - r16362 b16363 b16364 d16357
      omega
    have d16365 : (x 3 2).toNat = 1 := by
      have r16366 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16367 := hb (x 3 2)
      have b16368 := hb (x 5 13)
      have b16369 := hb (x 4 1 && x 4 14)
      clear * - r16366 b16367 b16368 b16369 d16332 d16361
      omega
    have d16370 : (x 3 14).toNat = 1 := by
      have r16371 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b16372 := hb (x 3 2)
      have b16373 := hb (x 3 14)
      clear * - r16371 b16372 b16373 d16365
      omega
    have d16374 : (x 2 1).toNat = 0 := by
      have r16375 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16376 := hb (x 2 1)
      have b16377 := hb (x 3 14)
      clear * - r16375 b16376 b16377 d16370
      omega
    have d16378 : (x 2 1 && x 2 14).toNat = 0 := by
      have r16379 := hand1 (x 2 1) (x 2 14)
      have b16380 := hb (x 2 1)
      have b16381 := hb (x 2 1 && x 2 14)
      clear * - r16379 b16380 b16381 d16374
      omega
    have d16382 : (x 3 13).toNat = 1 := by
      have r16383 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16384 := hb (x 1 2)
      have b16385 := hb (x 3 13)
      have b16386 := hb (x 2 1 && x 2 14)
      clear * - r16383 b16384 b16385 b16386 d16378 g8
      omega
    have d16387 : (x 3 1).toNat = 1 := by
      have r16388 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b16389 := hb (x 3 1)
      have b16390 := hb (x 3 13)
      clear * - r16388 b16389 b16390 d16382
      omega
    have d16391 : (x 4 14).toNat = 0 := by
      have r16392 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16393 := hb (x 3 1)
      have b16394 := hb (x 4 14)
      clear * - r16392 b16393 b16394 d16387
      omega
    have d16395 : (x 4 3 && x 4 14).toNat = 0 := by
      have r16396 := hand2 (x 4 3) (x 4 14)
      have b16397 := hb (x 4 14)
      have b16398 := hb (x 4 3 && x 4 14)
      clear * - r16396 b16397 b16398 d16391
      omega
    have d16399 : (x 7 11).toNat = 1 := by
      have r16400 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16401 := hb (x 3 4)
      have b16402 := hb (x 7 11)
      have b16403 := hb (x 6 1 && x 6 12)
      have b16404 := hb (x 5 2 && x 5 13)
      have b16405 := hb (x 4 3 && x 4 14)
      clear * - r16400 b16401 b16402 b16403 b16404 b16405 d16328 d15480 d16395 g15
      omega
    have d16406 : (x 7 3).toNat = 1 := by
      have r16407 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b16408 := hb (x 7 3)
      have b16409 := hb (x 7 11)
      clear * - r16407 b16408 b16409 d16399
      omega
    have d16410 : (x 10 12).toNat = 0 := by
      have r16411 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16412 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e16413 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b16414 := hb (x 7 3)
      have b16415 := hb (x 8 2)
      have b16416 := hb (x 9 13)
      have b16417 := hb (x 10 12)
      clear * - r16411 e16412 e16413 b16414 b16415 b16416 b16417 d16406
      omega
    have d16418 : (x 9 13).toNat = 0 := by
      have r16419 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16420 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e16421 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b16422 := hb (x 7 3)
      have b16423 := hb (x 8 2)
      have b16424 := hb (x 9 13)
      have b16425 := hb (x 10 12)
      clear * - r16419 e16420 e16421 b16422 b16423 b16424 b16425 d16410 d16406
      omega
    have d16426 : (x 8 2).toNat = 0 := by
      have r16427 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16428 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e16429 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b16430 := hb (x 7 3)
      have b16431 := hb (x 8 2)
      have b16432 := hb (x 9 13)
      have b16433 := hb (x 10 12)
      clear * - r16427 e16428 e16429 b16430 b16431 b16432 b16433 d16410 d16418 d16406
      omega
    have d16434 : (x 4 12).toNat = 0 := by
      have r16435 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16436 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e16437 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b16438 := hb (x 1 3)
      have b16439 := hb (x 2 2)
      have b16440 := hb (x 3 13)
      have b16441 := hb (x 4 12)
      clear * - r16435 e16436 e16437 b16438 b16439 b16440 b16441 d16382
      omega
    have d16442 : (x 4 4).toNat = 0 := by
      have r16443 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b16444 := hb (x 4 4)
      have b16445 := hb (x 4 12)
      clear * - r16443 b16444 b16445 d16434
      omega
    have d16446 : (x 5 12).toNat = 0 := by
      have r16447 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16448 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e16449 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b16450 := hb (x 2 3)
      have b16451 := hb (x 3 2)
      have b16452 := hb (x 4 13)
      have b16453 := hb (x 5 12)
      clear * - r16447 e16448 e16449 b16450 b16451 b16452 b16453 d16365
      omega
    have d16454 : (x 5 4).toNat = 0 := by
      have r16455 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b16456 := hb (x 5 4)
      have b16457 := hb (x 5 12)
      clear * - r16455 b16456 b16457 d16446
      omega
    have d16458 : (x 5 4 && x 5 14).toNat = 0 := by
      have r16459 := hand1 (x 5 4) (x 5 14)
      have b16460 := hb (x 5 4)
      have b16461 := hb (x 5 4 && x 5 14)
      clear * - r16459 b16460 b16461 d16454
      omega
    have d16462 : (x 4 13).toNat = 0 := by
      have r16463 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16464 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e16465 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b16466 := hb (x 2 3)
      have b16467 := hb (x 3 2)
      have b16468 := hb (x 4 13)
      have b16469 := hb (x 5 12)
      clear * - r16463 e16464 e16465 b16466 b16467 b16468 b16469 d16446 d16365
      omega
    have d16470 : (x 4 5).toNat = 0 := by
      have r16471 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
      have b16472 := hb (x 4 5)
      have b16473 := hb (x 4 13)
      clear * - r16471 b16472 b16473 d16462
      omega
    have d16474 : (x 5 1).toNat = 1 := by
      have r16475 := hand1 (x 5 1) (x 5 14)
      have b16476 := hb (x 5 1)
      have b16477 := hb (x 5 1 && x 5 14)
      clear * - r16475 b16476 b16477 d16348
      omega
    have d16478 : (x 6 14).toNat = 0 := by
      have r16479 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16480 := hb (x 5 1)
      have b16481 := hb (x 6 14)
      clear * - r16479 b16480 b16481 d16474
      omega
    have d16482 : (x 6 1 && x 6 14).toNat = 0 := by
      have r16483 := hand2 (x 6 1) (x 6 14)
      have b16484 := hb (x 6 14)
      have b16485 := hb (x 6 1 && x 6 14)
      clear * - r16483 b16484 b16485 d16478
      omega
    have d16486 : (x 7 13).toNat = 1 := by
      have r16487 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16488 := hb (x 5 2)
      have b16489 := hb (x 7 13)
      have b16490 := hb (x 6 1 && x 6 14)
      clear * - r16487 b16488 b16489 b16490 d16482 d15472
      omega
    have d16491 : (x 8 12).toNat = 0 := by
      have r16492 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16493 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e16494 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b16495 := hb (x 5 3)
      have b16496 := hb (x 6 2)
      have b16497 := hb (x 7 13)
      have b16498 := hb (x 8 12)
      clear * - r16492 e16493 e16494 b16495 b16496 b16497 b16498 d16486
      omega
    have d16499 : (x 6 2).toNat = 0 := by
      have r16500 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16501 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e16502 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b16503 := hb (x 5 3)
      have b16504 := hb (x 6 2)
      have b16505 := hb (x 7 13)
      have b16506 := hb (x 8 12)
      clear * - r16500 e16501 e16502 b16503 b16504 b16505 b16506 d16491 d16486
      omega
    have d16507 : (x 5 3).toNat = 0 := by
      have r16508 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16509 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e16510 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b16511 := hb (x 5 3)
      have b16512 := hb (x 6 2)
      have b16513 := hb (x 7 13)
      have b16514 := hb (x 8 12)
      clear * - r16508 e16509 e16510 b16511 b16512 b16513 b16514 d16491 d16486 d16499
      omega
    have d16515 : (x 5 3 && x 5 14).toNat = 0 := by
      have r16516 := hand1 (x 5 3) (x 5 14)
      have b16517 := hb (x 5 3)
      have b16518 := hb (x 5 3 && x 5 14)
      clear * - r16516 b16517 b16518 d16507
      omega
    have d16519 : (x 8 11).toNat = 1 := by
      have r16520 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16521 := hb (x 4 4)
      have b16522 := hb (x 8 11)
      have b16523 := hb (x 7 1 && x 7 12)
      have b16524 := hb (x 6 2 && x 6 13)
      have b16525 := hb (x 5 3 && x 5 14)
      clear * - r16520 b16521 b16522 b16523 b16524 b16525 d15432 d15456 d16515 d16442
      omega
    have d16526 : (x 8 3).toNat = 1 := by
      have r16527 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b16528 := hb (x 8 3)
      have b16529 := hb (x 8 11)
      clear * - r16527 b16528 b16529 d16519
      omega
    have d16530 : (x 11 12).toNat = 0 := by
      have r16531 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16532 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e16533 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b16534 := hb (x 8 3)
      have b16535 := hb (x 9 2)
      have b16536 := hb (x 10 13)
      have b16537 := hb (x 11 12)
      clear * - r16531 e16532 e16533 b16534 b16535 b16536 b16537 d16526
      omega
    have d16538 : (x 10 13).toNat = 0 := by
      have r16539 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16540 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e16541 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b16542 := hb (x 8 3)
      have b16543 := hb (x 9 2)
      have b16544 := hb (x 10 13)
      have b16545 := hb (x 11 12)
      clear * - r16539 e16540 e16541 b16542 b16543 b16544 b16545 d16530 d16526
      omega
    have d16546 : (x 9 1 && x 9 14).toNat = 1 := by
      have r16547 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16548 := hb (x 8 2)
      have b16549 := hb (x 10 13)
      have b16550 := hb (x 9 1 && x 9 14)
      clear * - r16547 b16548 b16549 b16550 d16538 d16426
      omega
    have d16551 : (x 9 14).toNat = 1 := by
      have r16552 := hand2 (x 9 1) (x 9 14)
      have b16553 := hb (x 9 14)
      have b16554 := hb (x 9 1 && x 9 14)
      clear * - r16552 b16553 b16554 d16546
      omega
    have d16555 : (x 8 1).toNat = 0 := by
      have r16556 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16557 := hb (x 8 1)
      have b16558 := hb (x 9 14)
      clear * - r16556 b16557 b16558 d16551
      omega
    have d16559 : (x 8 1 && x 8 11).toNat = 0 := by
      have r16560 := hand1 (x 8 1) (x 8 11)
      have b16561 := hb (x 8 1)
      have b16562 := hb (x 8 1 && x 8 11)
      clear * - r16560 b16561 b16562 d16555
      omega
    have d16563 : (x 9 10).toNat = 1 := by
      have r16564 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b16565 := hb (x 4 5)
      have b16566 := hb (x 9 10)
      have b16567 := hb (x 8 1 && x 8 11)
      have b16568 := hb (x 7 2 && x 7 12)
      have b16569 := hb (x 6 3 && x 6 13)
      have b16570 := hb (x 5 4 && x 5 14)
      clear * - r16564 b16565 b16566 b16567 b16568 b16569 b16570 d16559 d15436 d15460 d16458 d16470
      omega
    have d16571 : (x 9 2).toNat = 1 := by
      have r16572 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
      have b16573 := hb (x 9 2)
      have b16574 := hb (x 9 10)
      clear * - r16572 b16573 b16574 d16563
      omega
    have r16575 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16576 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e16577 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b16578 := hb (x 8 3)
    have b16579 := hb (x 9 2)
    have b16580 := hb (x 10 13)
    have b16581 := hb (x 11 12)
    linarith only [r16575, e16576, e16577, b16578, b16579, b16580, b16581, d16530, d16538, d16571, d16526]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b1110_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 7).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 6).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 9).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x 0 4).toNat = 1)
    (g9 : (x 0 6).toNat = 0)
    (g10 : (x 0 8).toNat = 0)
    (g11 : (x 1 2).toNat = 0)
    (g12 : (x 1 4).toNat = 0)
    (g13 : (x 1 5).toNat = 0)
    (g14 : (x 1 6).toNat = 0)
    (g15 : (x 1 8).toNat = 0)
    (g16 : (x 1 10).toNat = 0)
    (g17 : (x 2 4).toNat = 0)
    (g18 : (x 2 5).toNat = 0)
    (g19 : (x 3 4).toNat = 0)
    (g20 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g21 : (x 0 4 && x 0 8).toNat = 0)
    (g22 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g23 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g24 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g25 : (x 2 4 && x 2 8).toNat = 0)
    (g26 : (x 1 5 && x 1 9).toNat = 0)
    (g27 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g28 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g29 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g30 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g31 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g32 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g33 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g34 : (x 3 8 && x 3 13).toNat = 0)
    (g35 : (x 2 9 && x 2 14).toNat = 0)
    (g36 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g37 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g38 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g39 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g40 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g41 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g42 : (x 4 2 && x 4 8).toNat = 0)
    (g43 : (x 3 3 && x 3 9).toNat = 0)
    (g44 : (x 2 4 && x 2 10).toNat = 0)
    (g45 : (x 1 5 && x 1 11).toNat = 0)
    (g46 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g47 : (x 0 1 && x 0 8).toNat = 0)
    (g48 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g49 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g50 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g51 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g52 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g53 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g54 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g55 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g56 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g57 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g58 : (x 3 3 && x 3 12).toNat = 0)
    (g59 : (x 2 4 && x 2 13).toNat = 0)
    (g60 : (x 1 5 && x 1 14).toNat = 0)
    (g61 : (x 3 4 && x 3 13).toNat = 0)
    (g62 : (x 2 5 && x 2 14).toNat = 0)
    (g63 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g64 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g65 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g66 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g67 : (x 2 4 && x 2 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d16777 : (x 0 6 && x 0 12).toNat = 0 := by
    have r16778 := hand1 (x 0 6) (x 0 12)
    have b16779 := hb (x 0 6)
    have b16780 := hb (x 0 6 && x 0 12)
    clear * - r16778 b16779 b16780 g9
    omega
  have d16781 : (x 0 1 && x 0 6).toNat = 0 := by
    have r16782 := hand2 (x 0 1) (x 0 6)
    have b16783 := hb (x 0 6)
    have b16784 := hb (x 0 1 && x 0 6)
    clear * - r16782 b16783 b16784 g9
    omega
  have d16785 : (x 0 6 && x 0 10).toNat = 0 := by
    have r16786 := hand1 (x 0 6) (x 0 10)
    have b16787 := hb (x 0 6)
    have b16788 := hb (x 0 6 && x 0 10)
    clear * - r16786 b16787 b16788 g9
    omega
  have d16789 : (x 0 2 && x 0 6).toNat = 0 := by
    have r16790 := hand2 (x 0 2) (x 0 6)
    have b16791 := hb (x 0 6)
    have b16792 := hb (x 0 2 && x 0 6)
    clear * - r16790 b16791 b16792 g9
    omega
  cases h16793 : x 0 7
  · have f16794 : (x 0 7).toNat = 0 := by rw [h16793]; rfl
    have d16795 : (x 0 1 && x 0 7).toNat = 0 := by
      have r16796 := hand2 (x 0 1) (x 0 7)
      have b16797 := hb (x 0 7)
      have b16798 := hb (x 0 1 && x 0 7)
      clear * - r16796 b16797 b16798 f16794
      omega
    cases h16799 : x 0 10
    · have f16800 : (x 0 10).toNat = 0 := by rw [h16799]; rfl
      have d16801 : (x 0 1 && x 0 10).toNat = 0 := by
        have r16802 := hand2 (x 0 1) (x 0 10)
        have b16803 := hb (x 0 10)
        have b16804 := hb (x 0 1 && x 0 10)
        clear * - r16802 b16803 b16804 f16800
        omega
      have d16805 : (x 1 9).toNat = 1 := by
        have r16806 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b16807 := hb (x (-5) 6)
        have b16808 := hb (x 1 9)
        have b16809 := hb (x 0 1 && x 0 10)
        have b16810 := hb (x (-1) 2 && x (-1) 11)
        have b16811 := hb (x (-2) 3 && x (-2) 12)
        have b16812 := hb (x (-3) 4 && x (-3) 13)
        have b16813 := hb (x (-4) 5 && x (-4) 14)
        clear * - r16806 b16807 b16808 b16809 b16810 b16811 b16812 b16813 d16801 g54 g55 g56 g57 g0
        omega
      have d16814 : (x 1 1).toNat = 1 := by
        have r16815 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
        have b16816 := hb (x 1 1)
        have b16817 := hb (x 1 9)
        clear * - r16815 b16816 b16817 d16805
        omega
      have d16818 : (x 2 14).toNat = 0 := by
        have r16819 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b16820 := hb (x 1 1)
        have b16821 := hb (x 2 14)
        clear * - r16819 b16820 b16821 d16814
        omega
      have d16822 : (x 2 1 && x 2 14).toNat = 0 := by
        have r16823 := hand2 (x 2 1) (x 2 14)
        have b16824 := hb (x 2 14)
        have b16825 := hb (x 2 1 && x 2 14)
        clear * - r16823 b16824 b16825 d16818
        omega
      have d16826 : (x 3 13).toNat = 1 := by
        have r16827 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b16828 := hb (x 1 2)
        have b16829 := hb (x 3 13)
        have b16830 := hb (x 2 1 && x 2 14)
        clear * - r16827 b16828 b16829 b16830 d16822 g11
        omega
      have d16831 : (x 4 12).toNat = 0 := by
        have r16832 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16833 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e16834 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b16835 := hb (x 1 3)
        have b16836 := hb (x 2 2)
        have b16837 := hb (x 3 13)
        have b16838 := hb (x 4 12)
        clear * - r16832 e16833 e16834 b16835 b16836 b16837 b16838 d16826
        omega
      have d16839 : (x 4 3 && x 4 12).toNat = 0 := by
        have r16840 := hand2 (x 4 3) (x 4 12)
        have b16841 := hb (x 4 12)
        have b16842 := hb (x 4 3 && x 4 12)
        clear * - r16840 b16841 b16842 d16831
        omega
      have d16843 : (x 4 4).toNat = 0 := by
        have r16844 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b16845 := hb (x 4 4)
        have b16846 := hb (x 4 12)
        clear * - r16844 b16845 b16846 d16831
        omega
      have d16847 : (x 2 6).toNat = 0 := by
        have r16848 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
        have b16849 := hb (x 2 6)
        have b16850 := hb (x 2 14)
        clear * - r16848 b16849 b16850 d16818
        omega
      have d16851 : (x 2 8).toNat = 0 := by
        have r16852 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16853 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e16854 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e16855 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e16856 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e16857 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e16858 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b16859 := hb (x (-5) 7)
        have b16860 := hb (x (-4) 6)
        have b16861 := hb (x (-3) 5)
        have b16862 := hb (x (-2) 4)
        have b16863 := hb (x (-1) 11)
        have b16864 := hb (x 0 10)
        have b16865 := hb (x 1 9)
        have b16866 := hb (x 2 8)
        clear * - r16852 e16853 e16854 e16855 e16856 e16857 e16858 b16859 b16860 b16861 b16862 b16863 b16864 b16865 b16866 d16805 f16800 g7
        omega
      have d16867 : (x (-2) 4).toNat = 0 := by
        have r16868 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16869 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e16870 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e16871 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e16872 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e16873 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e16874 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b16875 := hb (x (-5) 7)
        have b16876 := hb (x (-4) 6)
        have b16877 := hb (x (-3) 5)
        have b16878 := hb (x (-2) 4)
        have b16879 := hb (x (-1) 11)
        have b16880 := hb (x 0 10)
        have b16881 := hb (x 1 9)
        have b16882 := hb (x 2 8)
        clear * - r16868 e16869 e16870 e16871 e16872 e16873 e16874 b16875 b16876 b16877 b16878 b16879 b16880 b16881 b16882 d16851 d16805 f16800 g7
        omega
      have d16883 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
        have r16884 := hand1 (x (-2) 4) (x (-2) 8)
        have b16885 := hb (x (-2) 4)
        have b16886 := hb (x (-2) 4 && x (-2) 8)
        clear * - r16884 b16885 b16886 d16867
        omega
      have d16887 : (x (-3) 5).toNat = 0 := by
        have r16888 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16889 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e16890 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e16891 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e16892 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e16893 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e16894 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b16895 := hb (x (-5) 7)
        have b16896 := hb (x (-4) 6)
        have b16897 := hb (x (-3) 5)
        have b16898 := hb (x (-2) 4)
        have b16899 := hb (x (-1) 11)
        have b16900 := hb (x 0 10)
        have b16901 := hb (x 1 9)
        have b16902 := hb (x 2 8)
        clear * - r16888 e16889 e16890 e16891 e16892 e16893 e16894 b16895 b16896 b16897 b16898 b16899 b16900 b16901 b16902 d16851 d16805 f16800 g7 d16867
        omega
      have d16903 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
        have r16904 := hand1 (x (-3) 5) (x (-3) 9)
        have b16905 := hb (x (-3) 5)
        have b16906 := hb (x (-3) 5 && x (-3) 9)
        clear * - r16904 b16905 b16906 d16887
        omega
      have d16907 : (x (-4) 6).toNat = 0 := by
        have r16908 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16909 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e16910 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e16911 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e16912 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e16913 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e16914 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b16915 := hb (x (-5) 7)
        have b16916 := hb (x (-4) 6)
        have b16917 := hb (x (-3) 5)
        have b16918 := hb (x (-2) 4)
        have b16919 := hb (x (-1) 11)
        have b16920 := hb (x 0 10)
        have b16921 := hb (x 1 9)
        have b16922 := hb (x 2 8)
        clear * - r16908 e16909 e16910 e16911 e16912 e16913 e16914 b16915 b16916 b16917 b16918 b16919 b16920 b16921 b16922 d16851 d16805 f16800 g7 d16867 d16887
        omega
      have d16923 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
        have r16924 := hand1 (x (-4) 6) (x (-4) 10)
        have b16925 := hb (x (-4) 6)
        have b16926 := hb (x (-4) 6 && x (-4) 10)
        clear * - r16924 b16925 b16926 d16907
        omega
      have d16927 : (x (-5) 7).toNat = 0 := by
        have r16928 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e16929 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e16930 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e16931 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e16932 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e16933 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e16934 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b16935 := hb (x (-5) 7)
        have b16936 := hb (x (-4) 6)
        have b16937 := hb (x (-3) 5)
        have b16938 := hb (x (-2) 4)
        have b16939 := hb (x (-1) 11)
        have b16940 := hb (x 0 10)
        have b16941 := hb (x 1 9)
        have b16942 := hb (x 2 8)
        clear * - r16928 e16929 e16930 e16931 e16932 e16933 e16934 b16935 b16936 b16937 b16938 b16939 b16940 b16941 b16942 d16851 d16805 f16800 g7 d16867 d16887 d16907
        omega
      have d16943 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
        have r16944 := hand1 (x (-5) 7) (x (-5) 11)
        have b16945 := hb (x (-5) 7)
        have b16946 := hb (x (-5) 7 && x (-5) 11)
        clear * - r16944 b16945 b16946 d16927
        omega
      have r16947 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16948 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e16949 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e16950 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e16951 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e16952 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e16953 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have r16954 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16955 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e16956 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e16957 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e16958 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e16959 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e16960 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have r16961 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16962 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e16963 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e16964 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e16965 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e16966 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e16967 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r16968 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16969 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e16970 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have r16971 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16972 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e16973 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have r16974 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e16975 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
      have e16976 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
      have r16977 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r16978 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r16979 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r16980 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r16981 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r16982 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have r16983 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
      have r16984 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have r16985 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have r16986 := hand1 (x (-6) 8) (x (-6) 12)
      have r16987 := hand1 (x (-7) 9) (x (-7) 13)
      have r16988 := hand2 (x (-7) 8) (x (-7) 13)
      have r16989 := hand1 (x (-8) 9) (x (-8) 14)
      have r16990 := hand2 (x 6 1) (x 6 10)
      have r16991 := hand2 (x 5 2) (x 5 11)
      have r16992 := hand2 (x (-7) 1) (x (-7) 11)
      have r16993 := hand1 (x (-8) 2) (x (-8) 12)
      have r16994 := hand1 (x (-9) 3) (x (-9) 13)
      have r16995 := hand1 (x (-10) 4) (x (-10) 14)
      have r16996 := hand1 (x (-4) 4) (x (-4) 14)
      linarith only [r16947, e16948, e16949, e16950, e16951, e16952, e16953, r16954, e16955, e16956, e16957, e16958, e16959, e16960, r16961, e16962, e16963, e16964, e16965, e16966, e16967, r16968, e16969, e16970, r16971, e16972, e16973, r16974, e16975, e16976, r16977, r16978, r16979, r16980, r16981, r16982, r16983, r16984, r16985, r16986, r16987, r16988, r16989, r16990, r16991, r16992, r16993, r16994, r16995, r16996, f16800, g13, g14, g17, d16847, d16843, d16789, g20, d16883, d16903, d16923, d16943, d16781, g28, g29, g30, g31, g32, g33, g47, g48, g49, g50, g51, g52, g53, d16839, g61, g62, g64, g65, g66]
    · have f17074 : (x 0 10).toNat = 1 := by rw [h16799]; rfl
      have d17075 : (x 2 8).toNat = 0 := by
        have r17076 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17077 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e17078 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e17079 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e17080 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e17081 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e17082 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b17083 := hb (x (-5) 7)
        have b17084 := hb (x (-4) 6)
        have b17085 := hb (x (-3) 5)
        have b17086 := hb (x (-2) 4)
        have b17087 := hb (x (-1) 11)
        have b17088 := hb (x 0 10)
        have b17089 := hb (x 1 9)
        have b17090 := hb (x 2 8)
        clear * - r17076 e17077 e17078 e17079 e17080 e17081 e17082 b17083 b17084 b17085 b17086 b17087 b17088 b17089 b17090 f17074 g7
        omega
      have d17091 : (x 1 9).toNat = 0 := by
        have r17092 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17093 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e17094 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e17095 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e17096 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e17097 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e17098 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b17099 := hb (x (-5) 7)
        have b17100 := hb (x (-4) 6)
        have b17101 := hb (x (-3) 5)
        have b17102 := hb (x (-2) 4)
        have b17103 := hb (x (-1) 11)
        have b17104 := hb (x 0 10)
        have b17105 := hb (x 1 9)
        have b17106 := hb (x 2 8)
        clear * - r17092 e17093 e17094 e17095 e17096 e17097 e17098 b17099 b17100 b17101 b17102 b17103 b17104 b17105 b17106 d17075 f17074 g7
        omega
      have d17107 : (x (-2) 4).toNat = 0 := by
        have r17108 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17109 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e17110 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e17111 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e17112 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e17113 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e17114 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b17115 := hb (x (-5) 7)
        have b17116 := hb (x (-4) 6)
        have b17117 := hb (x (-3) 5)
        have b17118 := hb (x (-2) 4)
        have b17119 := hb (x (-1) 11)
        have b17120 := hb (x 0 10)
        have b17121 := hb (x 1 9)
        have b17122 := hb (x 2 8)
        clear * - r17108 e17109 e17110 e17111 e17112 e17113 e17114 b17115 b17116 b17117 b17118 b17119 b17120 b17121 b17122 d17075 d17091 f17074 g7
        omega
      have d17123 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
        have r17124 := hand1 (x (-2) 4) (x (-2) 8)
        have b17125 := hb (x (-2) 4)
        have b17126 := hb (x (-2) 4 && x (-2) 8)
        clear * - r17124 b17125 b17126 d17107
        omega
      have d17127 : (x (-3) 5).toNat = 0 := by
        have r17128 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17129 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e17130 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e17131 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e17132 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e17133 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e17134 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b17135 := hb (x (-5) 7)
        have b17136 := hb (x (-4) 6)
        have b17137 := hb (x (-3) 5)
        have b17138 := hb (x (-2) 4)
        have b17139 := hb (x (-1) 11)
        have b17140 := hb (x 0 10)
        have b17141 := hb (x 1 9)
        have b17142 := hb (x 2 8)
        clear * - r17128 e17129 e17130 e17131 e17132 e17133 e17134 b17135 b17136 b17137 b17138 b17139 b17140 b17141 b17142 d17075 d17091 f17074 g7 d17107
        omega
      have d17143 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
        have r17144 := hand1 (x (-3) 5) (x (-3) 9)
        have b17145 := hb (x (-3) 5)
        have b17146 := hb (x (-3) 5 && x (-3) 9)
        clear * - r17144 b17145 b17146 d17127
        omega
      have d17147 : (x (-4) 6).toNat = 0 := by
        have r17148 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17149 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e17150 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e17151 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e17152 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e17153 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e17154 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b17155 := hb (x (-5) 7)
        have b17156 := hb (x (-4) 6)
        have b17157 := hb (x (-3) 5)
        have b17158 := hb (x (-2) 4)
        have b17159 := hb (x (-1) 11)
        have b17160 := hb (x 0 10)
        have b17161 := hb (x 1 9)
        have b17162 := hb (x 2 8)
        clear * - r17148 e17149 e17150 e17151 e17152 e17153 e17154 b17155 b17156 b17157 b17158 b17159 b17160 b17161 b17162 d17075 d17091 f17074 g7 d17107 d17127
        omega
      have d17163 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
        have r17164 := hand1 (x (-4) 6) (x (-4) 10)
        have b17165 := hb (x (-4) 6)
        have b17166 := hb (x (-4) 6 && x (-4) 10)
        clear * - r17164 b17165 b17166 d17147
        omega
      have d17167 : (x (-5) 7).toNat = 0 := by
        have r17168 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e17169 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e17170 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e17171 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e17172 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e17173 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e17174 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b17175 := hb (x (-5) 7)
        have b17176 := hb (x (-4) 6)
        have b17177 := hb (x (-3) 5)
        have b17178 := hb (x (-2) 4)
        have b17179 := hb (x (-1) 11)
        have b17180 := hb (x 0 10)
        have b17181 := hb (x 1 9)
        have b17182 := hb (x 2 8)
        clear * - r17168 e17169 e17170 e17171 e17172 e17173 e17174 b17175 b17176 b17177 b17178 b17179 b17180 b17181 b17182 d17075 d17091 f17074 g7 d17107 d17127 d17147
        omega
      have d17183 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
        have r17184 := hand1 (x (-5) 7) (x (-5) 11)
        have b17185 := hb (x (-5) 7)
        have b17186 := hb (x (-5) 7 && x (-5) 11)
        clear * - r17184 b17185 b17186 d17167
        omega
      cases h17187 : x 1 1
      · have f17188 : (x 1 1).toNat = 0 := by rw [h17187]; rfl
        have d17189 : (x 2 14).toNat = 1 := by
          have r17190 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b17191 := hb (x 1 1)
          have b17192 := hb (x 2 14)
          clear * - r17190 b17191 b17192 f17188
          omega
        cases h17193 : x 1 3
        · have f17194 : (x 1 3).toNat = 0 := by rw [h17193]; rfl
          cases h17195 : x 1 7
          · have f17196 : (x 1 7).toNat = 0 := by rw [h17195]; rfl
            have d17197 : (x (-7) 8).toNat = 1 := by
              have r17198 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17199 := hb (x (-7) 8)
              have b17200 := hb (x 1 7)
              have b17201 := hb (x 0 1 && x 0 8)
              have b17202 := hb (x (-1) 2 && x (-1) 9)
              have b17203 := hb (x (-2) 3 && x (-2) 10)
              have b17204 := hb (x (-3) 4 && x (-3) 11)
              have b17205 := hb (x (-4) 5 && x (-4) 12)
              have b17206 := hb (x (-5) 6 && x (-5) 13)
              have b17207 := hb (x (-6) 7 && x (-6) 14)
              clear * - r17198 b17199 b17200 b17201 b17202 b17203 b17204 b17205 b17206 b17207 f17196 g47 g48 g49 g50 g51 g52 g53
              omega
            have d17208 : (x (-8) 9).toNat = 0 := by
              have r17209 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17210 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e17211 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e17212 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e17213 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e17214 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e17215 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have b17216 := hb (x (-14) 7)
              have b17217 := hb (x (-13) 6)
              have b17218 := hb (x (-12) 5)
              have b17219 := hb (x (-11) 4)
              have b17220 := hb (x (-10) 11)
              have b17221 := hb (x (-9) 10)
              have b17222 := hb (x (-8) 9)
              have b17223 := hb (x (-7) 8)
              clear * - r17209 e17210 e17211 e17212 e17213 e17214 e17215 b17216 b17217 b17218 b17219 b17220 b17221 b17222 b17223 d17197
              omega
            have d17224 : (x (-8) 9 && x (-8) 14).toNat = 0 := by
              have r17225 := hand1 (x (-8) 9) (x (-8) 14)
              have b17226 := hb (x (-8) 9)
              have b17227 := hb (x (-8) 9 && x (-8) 14)
              clear * - r17225 b17226 b17227 d17208
              omega
            have d17228 : (x (-9) 10).toNat = 0 := by
              have r17229 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17230 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e17231 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e17232 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e17233 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e17234 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e17235 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have b17236 := hb (x (-14) 7)
              have b17237 := hb (x (-13) 6)
              have b17238 := hb (x (-12) 5)
              have b17239 := hb (x (-11) 4)
              have b17240 := hb (x (-10) 11)
              have b17241 := hb (x (-9) 10)
              have b17242 := hb (x (-8) 9)
              have b17243 := hb (x (-7) 8)
              clear * - r17229 e17230 e17231 e17232 e17233 e17234 e17235 b17236 b17237 b17238 b17239 b17240 b17241 b17242 b17243 d17197 d17208
              omega
            have d17244 : (x (-10) 11).toNat = 0 := by
              have r17245 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17246 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e17247 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e17248 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e17249 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e17250 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e17251 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have b17252 := hb (x (-14) 7)
              have b17253 := hb (x (-13) 6)
              have b17254 := hb (x (-12) 5)
              have b17255 := hb (x (-11) 4)
              have b17256 := hb (x (-10) 11)
              have b17257 := hb (x (-9) 10)
              have b17258 := hb (x (-8) 9)
              have b17259 := hb (x (-7) 8)
              clear * - r17245 e17246 e17247 e17248 e17249 e17250 e17251 b17252 b17253 b17254 b17255 b17256 b17257 b17258 b17259 d17197 d17208 d17228
              omega
            have d17260 : (x (-11) 4).toNat = 0 := by
              have r17261 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17262 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e17263 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e17264 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e17265 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e17266 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e17267 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have b17268 := hb (x (-14) 7)
              have b17269 := hb (x (-13) 6)
              have b17270 := hb (x (-12) 5)
              have b17271 := hb (x (-11) 4)
              have b17272 := hb (x (-10) 11)
              have b17273 := hb (x (-9) 10)
              have b17274 := hb (x (-8) 9)
              have b17275 := hb (x (-7) 8)
              clear * - r17261 e17262 e17263 e17264 e17265 e17266 e17267 b17268 b17269 b17270 b17271 b17272 b17273 b17274 b17275 d17197 d17208 d17228 d17244
              omega
            have d17276 : (x (-11) 4 && x (-11) 14).toNat = 0 := by
              have r17277 := hand1 (x (-11) 4) (x (-11) 14)
              have b17278 := hb (x (-11) 4)
              have b17279 := hb (x (-11) 4 && x (-11) 14)
              clear * - r17277 b17278 b17279 d17260
              omega
            have d17280 : (x (-12) 5).toNat = 0 := by
              have r17281 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17282 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e17283 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e17284 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e17285 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e17286 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e17287 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have b17288 := hb (x (-14) 7)
              have b17289 := hb (x (-13) 6)
              have b17290 := hb (x (-12) 5)
              have b17291 := hb (x (-11) 4)
              have b17292 := hb (x (-10) 11)
              have b17293 := hb (x (-9) 10)
              have b17294 := hb (x (-8) 9)
              have b17295 := hb (x (-7) 8)
              clear * - r17281 e17282 e17283 e17284 e17285 e17286 e17287 b17288 b17289 b17290 b17291 b17292 b17293 b17294 b17295 d17197 d17208 d17228 d17244 d17260
              omega
            have d17296 : (x (-7) 8 && x (-7) 14).toNat = 1 := by
              have r17297 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17298 := hb (x (-8) 9)
              have b17299 := hb (x 1 6)
              have b17300 := hb (x 0 1 && x 0 7)
              have b17301 := hb (x (-1) 2 && x (-1) 8)
              have b17302 := hb (x (-2) 3 && x (-2) 9)
              have b17303 := hb (x (-3) 4 && x (-3) 10)
              have b17304 := hb (x (-4) 5 && x (-4) 11)
              have b17305 := hb (x (-5) 6 && x (-5) 12)
              have b17306 := hb (x (-6) 7 && x (-6) 13)
              have b17307 := hb (x (-7) 8 && x (-7) 14)
              clear * - r17297 b17298 b17299 b17300 b17301 b17302 b17303 b17304 b17305 b17306 b17307 g14 d16795 g36 g37 g38 g39 g40 g41 d17208
              omega
            have d17308 : (x (-7) 14).toNat = 1 := by
              have r17309 := hand2 (x (-7) 8) (x (-7) 14)
              have b17310 := hb (x (-7) 14)
              have b17311 := hb (x (-7) 8 && x (-7) 14)
              clear * - r17309 b17310 b17311 d17296
              omega
            have d17312 : (x (-8) 1).toNat = 0 := by
              have r17313 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17314 := hb (x (-8) 1)
              have b17315 := hb (x (-7) 14)
              clear * - r17313 b17314 b17315 d17308
              omega
            have d17316 : (x (-8) 1 && x (-8) 11).toNat = 0 := by
              have r17317 := hand1 (x (-8) 1) (x (-8) 11)
              have b17318 := hb (x (-8) 1)
              have b17319 := hb (x (-8) 1 && x (-8) 11)
              clear * - r17317 b17318 b17319 d17312
              omega
            have d17320 : (x (-8) 13).toNat = 0 := by
              have r17321 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
              have b17322 := hb (x (-8) 1)
              have b17323 := hb (x (-8) 13)
              clear * - r17321 b17322 b17323 d17312
              omega
            have d17324 : (x (-7) 8 && x (-7) 13).toNat = 1 := by
              have r17325 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17326 := hb (x (-9) 10)
              have b17327 := hb (x 1 5)
              have b17328 := hb (x 0 1 && x 0 6)
              have b17329 := hb (x (-1) 2 && x (-1) 7)
              have b17330 := hb (x (-2) 3 && x (-2) 8)
              have b17331 := hb (x (-3) 4 && x (-3) 9)
              have b17332 := hb (x (-4) 5 && x (-4) 10)
              have b17333 := hb (x (-5) 6 && x (-5) 11)
              have b17334 := hb (x (-6) 7 && x (-6) 12)
              have b17335 := hb (x (-7) 8 && x (-7) 13)
              have b17336 := hb (x (-8) 9 && x (-8) 14)
              clear * - r17325 b17326 b17327 b17328 b17329 b17330 b17331 b17332 b17333 b17334 b17335 b17336 g13 d16781 g28 g29 g30 g31 g32 g33 d17224 d17228
              omega
            have d17337 : (x (-7) 13).toNat = 1 := by
              have r17338 := hand2 (x (-7) 8) (x (-7) 13)
              have b17339 := hb (x (-7) 13)
              have b17340 := hb (x (-7) 8 && x (-7) 13)
              clear * - r17338 b17339 b17340 d17324
              omega
            have d17341 : (x (-7) 1).toNat = 1 := by
              have r17342 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
              have b17343 := hb (x (-7) 1)
              have b17344 := hb (x (-7) 13)
              clear * - r17342 b17343 b17344 d17337
              omega
            have d17345 : (x (-6) 14).toNat = 0 := by
              have r17346 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17347 := hb (x (-7) 1)
              have b17348 := hb (x (-6) 14)
              clear * - r17346 b17347 b17348 d17341
              omega
            have d17349 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
              have r17350 := hand2 (x (-6) 3) (x (-6) 14)
              have b17351 := hb (x (-6) 14)
              have b17352 := hb (x (-6) 3 && x (-6) 14)
              clear * - r17350 b17351 b17352 d17345
              omega
            have d17353 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
              have r17354 := hand2 (x (-6) 4) (x (-6) 14)
              have b17355 := hb (x (-6) 14)
              have b17356 := hb (x (-6) 4 && x (-6) 14)
              clear * - r17354 b17355 b17356 d17345
              omega
            have d17357 : (x (-6) 2).toNat = 0 := by
              have r17358 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
              have b17359 := hb (x (-6) 2)
              have b17360 := hb (x (-6) 14)
              clear * - r17358 b17359 b17360 d17345
              omega
            have d17361 : (x (-6) 10).toNat = 0 := by
              have r17362 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
              have b17363 := hb (x (-6) 2)
              have b17364 := hb (x (-6) 10)
              clear * - r17362 b17363 b17364 d17357
              omega
            have d17365 : (x (-6) 12).toNat = 0 := by
              have r17366 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17367 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e17368 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b17369 := hb (x (-9) 3)
              have b17370 := hb (x (-8) 2)
              have b17371 := hb (x (-7) 13)
              have b17372 := hb (x (-6) 12)
              clear * - r17366 e17367 e17368 b17369 b17370 b17371 b17372 d17337
              omega
            have d17373 : (x (-6) 8 && x (-6) 12).toNat = 0 := by
              have r17374 := hand2 (x (-6) 8) (x (-6) 12)
              have b17375 := hb (x (-6) 12)
              have b17376 := hb (x (-6) 8 && x (-6) 12)
              clear * - r17374 b17375 b17376 d17365
              omega
            have d17377 : (x (-6) 4).toNat = 0 := by
              have r17378 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
              have b17379 := hb (x (-6) 4)
              have b17380 := hb (x (-6) 12)
              clear * - r17378 b17379 b17380 d17365
              omega
            have d17381 : (x (-8) 2).toNat = 0 := by
              have r17382 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17383 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e17384 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b17385 := hb (x (-9) 3)
              have b17386 := hb (x (-8) 2)
              have b17387 := hb (x (-7) 13)
              have b17388 := hb (x (-6) 12)
              clear * - r17382 e17383 e17384 b17385 b17386 b17387 b17388 d17365 d17337
              omega
            have d17389 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
              have r17390 := hand1 (x (-8) 2) (x (-8) 12)
              have b17391 := hb (x (-8) 2)
              have b17392 := hb (x (-8) 2 && x (-8) 12)
              clear * - r17390 b17391 b17392 d17381
              omega
            have d17393 : (x (-8) 10).toNat = 0 := by
              have r17394 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
              have b17395 := hb (x (-8) 2)
              have b17396 := hb (x (-8) 10)
              clear * - r17394 b17395 b17396 d17381
              omega
            have d17397 : (x (-9) 3).toNat = 0 := by
              have r17398 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17399 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e17400 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b17401 := hb (x (-9) 3)
              have b17402 := hb (x (-8) 2)
              have b17403 := hb (x (-7) 13)
              have b17404 := hb (x (-6) 12)
              clear * - r17398 e17399 e17400 b17401 b17402 b17403 b17404 d17365 d17337 d17381
              omega
            have d17405 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
              have r17406 := hand1 (x (-9) 3) (x (-9) 13)
              have b17407 := hb (x (-9) 3)
              have b17408 := hb (x (-9) 3 && x (-9) 13)
              clear * - r17406 b17407 b17408 d17397
              omega
            have d17409 : (x (-9) 11).toNat = 0 := by
              have r17410 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
              have b17411 := hb (x (-9) 3)
              have b17412 := hb (x (-9) 11)
              clear * - r17410 b17411 b17412 d17397
              omega
            have d17413 : (x (-7) 9 && x (-7) 13).toNat = 1 := by
              have r17414 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17415 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
              have e17416 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
              have b17417 := hb (x (-9) 11)
              have b17418 := hb (x (-8) 10)
              have b17419 := hb (x 1 5)
              have b17420 := hb (x 2 4)
              have b17421 := hb (x 0 2 && x 0 6)
              have b17422 := hb (x (-1) 3 && x (-1) 7)
              have b17423 := hb (x (-2) 4 && x (-2) 8)
              have b17424 := hb (x (-3) 5 && x (-3) 9)
              have b17425 := hb (x (-4) 6 && x (-4) 10)
              have b17426 := hb (x (-5) 7 && x (-5) 11)
              have b17427 := hb (x (-6) 8 && x (-6) 12)
              have b17428 := hb (x (-7) 9 && x (-7) 13)
              clear * - r17414 e17415 e17416 b17417 b17418 b17419 b17420 b17421 b17422 b17423 b17424 b17425 b17426 b17427 b17428 g17 g13 d16789 g20 d17123 d17143 d17163 d17183 d17373 d17393 d17409
              omega
            have d17429 : (x (-7) 9).toNat = 1 := by
              have r17430 := hand1 (x (-7) 9) (x (-7) 13)
              have b17431 := hb (x (-7) 9)
              have b17432 := hb (x (-7) 9 && x (-7) 13)
              clear * - r17430 b17431 b17432 d17413
              omega
            have d17433 : (x (-6) 8).toNat = 0 := by
              have r17434 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17435 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
              have e17436 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
              have e17437 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
              have e17438 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
              have e17439 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
              have e17440 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
              have b17441 := hb (x (-13) 7)
              have b17442 := hb (x (-12) 6)
              have b17443 := hb (x (-11) 5)
              have b17444 := hb (x (-10) 4)
              have b17445 := hb (x (-9) 11)
              have b17446 := hb (x (-8) 10)
              have b17447 := hb (x (-7) 9)
              have b17448 := hb (x (-6) 8)
              clear * - r17434 e17435 e17436 e17437 e17438 e17439 e17440 b17441 b17442 b17443 b17444 b17445 b17446 b17447 b17448 d17429 d17393 d17409
              omega
            have d17449 : (x (-10) 4).toNat = 0 := by
              have r17450 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17451 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
              have e17452 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
              have e17453 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
              have e17454 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
              have e17455 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
              have e17456 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
              have b17457 := hb (x (-13) 7)
              have b17458 := hb (x (-12) 6)
              have b17459 := hb (x (-11) 5)
              have b17460 := hb (x (-10) 4)
              have b17461 := hb (x (-9) 11)
              have b17462 := hb (x (-8) 10)
              have b17463 := hb (x (-7) 9)
              have b17464 := hb (x (-6) 8)
              clear * - r17450 e17451 e17452 e17453 e17454 e17455 e17456 b17457 b17458 b17459 b17460 b17461 b17462 b17463 b17464 d17433 d17429 d17393 d17409
              omega
            have d17465 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
              have r17466 := hand1 (x (-10) 4) (x (-10) 14)
              have b17467 := hb (x (-10) 4)
              have b17468 := hb (x (-10) 4 && x (-10) 14)
              clear * - r17466 b17467 b17468 d17449
              omega
            have d17469 : (x (-11) 5).toNat = 0 := by
              have r17470 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17471 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
              have e17472 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
              have e17473 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
              have e17474 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
              have e17475 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
              have e17476 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
              have b17477 := hb (x (-13) 7)
              have b17478 := hb (x (-12) 6)
              have b17479 := hb (x (-11) 5)
              have b17480 := hb (x (-10) 4)
              have b17481 := hb (x (-9) 11)
              have b17482 := hb (x (-8) 10)
              have b17483 := hb (x (-7) 9)
              have b17484 := hb (x (-6) 8)
              clear * - r17470 e17471 e17472 e17473 e17474 e17475 e17476 b17477 b17478 b17479 b17480 b17481 b17482 b17483 b17484 d17433 d17429 d17393 d17409 d17449
              omega
            have d17485 : (x (-7) 1 && x (-7) 11).toNat = 1 := by
              have r17486 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17487 := hb (x (-11) 5)
              have b17488 := hb (x (-6) 10)
              have b17489 := hb (x (-7) 1 && x (-7) 11)
              have b17490 := hb (x (-8) 2 && x (-8) 12)
              have b17491 := hb (x (-9) 3 && x (-9) 13)
              have b17492 := hb (x (-10) 4 && x (-10) 14)
              clear * - r17486 b17487 b17488 b17489 b17490 b17491 b17492 d17361 d17389 d17405 d17465 d17469
              omega
            have d17493 : (x (-7) 11).toNat = 1 := by
              have r17494 := hand2 (x (-7) 1) (x (-7) 11)
              have b17495 := hb (x (-7) 11)
              have b17496 := hb (x (-7) 1 && x (-7) 11)
              clear * - r17494 b17495 b17496 d17485
              omega
            have d17497 : (x (-7) 3).toNat = 1 := by
              have r17498 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
              have b17499 := hb (x (-7) 3)
              have b17500 := hb (x (-7) 11)
              clear * - r17498 b17499 b17500 d17493
              omega
            have d17501 : (x (-4) 12).toNat = 0 := by
              have r17502 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17503 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e17504 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b17505 := hb (x (-7) 3)
              have b17506 := hb (x (-6) 2)
              have b17507 := hb (x (-5) 13)
              have b17508 := hb (x (-4) 12)
              clear * - r17502 e17503 e17504 b17505 b17506 b17507 b17508 d17357 d17497
              omega
            have d17509 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
              have r17510 := hand2 (x (-4) 1) (x (-4) 12)
              have b17511 := hb (x (-4) 12)
              have b17512 := hb (x (-4) 1 && x (-4) 12)
              clear * - r17510 b17511 b17512 d17501
              omega
            have d17513 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
              have r17514 := hand2 (x (-4) 2) (x (-4) 12)
              have b17515 := hb (x (-4) 12)
              have b17516 := hb (x (-4) 2 && x (-4) 12)
              clear * - r17514 b17515 b17516 d17501
              omega
            have d17517 : (x (-5) 13).toNat = 0 := by
              have r17518 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17519 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e17520 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b17521 := hb (x (-7) 3)
              have b17522 := hb (x (-6) 2)
              have b17523 := hb (x (-5) 13)
              have b17524 := hb (x (-4) 12)
              clear * - r17518 e17519 e17520 b17521 b17522 b17523 b17524 d17501 d17357 d17497
              omega
            have d17525 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
              have r17526 := hand2 (x (-5) 2) (x (-5) 13)
              have b17527 := hb (x (-5) 13)
              have b17528 := hb (x (-5) 2 && x (-5) 13)
              clear * - r17526 b17527 b17528 d17517
              omega
            have d17529 : (x (-7) 4).toNat = 1 := by
              have r17530 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17531 := hb (x (-7) 4)
              have b17532 := hb (x (-3) 11)
              have b17533 := hb (x (-4) 1 && x (-4) 12)
              have b17534 := hb (x (-5) 2 && x (-5) 13)
              have b17535 := hb (x (-6) 3 && x (-6) 14)
              clear * - r17530 b17531 b17532 b17533 b17534 b17535 g2 d17509 d17525 d17349
              omega
            have d17536 : (x (-7) 12).toNat = 1 := by
              have r17537 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
              have b17538 := hb (x (-7) 4)
              have b17539 := hb (x (-7) 12)
              clear * - r17537 b17538 b17539 d17529
              omega
            have d17540 : (x (-9) 2).toNat = 0 := by
              have r17541 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17542 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e17543 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b17544 := hb (x (-10) 3)
              have b17545 := hb (x (-9) 2)
              have b17546 := hb (x (-8) 13)
              have b17547 := hb (x (-7) 12)
              clear * - r17541 e17542 e17543 b17544 b17545 b17546 b17547 d17536 d17320
              omega
            have d17548 : (x (-9) 2 && x (-9) 12).toNat = 0 := by
              have r17549 := hand1 (x (-9) 2) (x (-9) 12)
              have b17550 := hb (x (-9) 2)
              have b17551 := hb (x (-9) 2 && x (-9) 12)
              clear * - r17549 b17550 b17551 d17540
              omega
            have d17552 : (x (-10) 3).toNat = 0 := by
              have r17553 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17554 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e17555 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b17556 := hb (x (-10) 3)
              have b17557 := hb (x (-9) 2)
              have b17558 := hb (x (-8) 13)
              have b17559 := hb (x (-7) 12)
              clear * - r17553 e17554 e17555 b17556 b17557 b17558 b17559 d17536 d17320 d17540
              omega
            have d17560 : (x (-10) 3 && x (-10) 13).toNat = 0 := by
              have r17561 := hand1 (x (-10) 3) (x (-10) 13)
              have b17562 := hb (x (-10) 3)
              have b17563 := hb (x (-10) 3 && x (-10) 13)
              clear * - r17561 b17562 b17563 d17552
              omega
            have d17564 : (x (-7) 10).toNat = 1 := by
              have r17565 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17566 := hb (x (-12) 5)
              have b17567 := hb (x (-7) 10)
              have b17568 := hb (x (-8) 1 && x (-8) 11)
              have b17569 := hb (x (-9) 2 && x (-9) 12)
              have b17570 := hb (x (-10) 3 && x (-10) 13)
              have b17571 := hb (x (-11) 4 && x (-11) 14)
              clear * - r17565 b17566 b17567 b17568 b17569 b17570 b17571 d17316 d17548 d17560 d17276 d17280
              omega
            have d17572 : (x (-7) 2).toNat = 1 := by
              have r17573 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
              have b17574 := hb (x (-7) 2)
              have b17575 := hb (x (-7) 10)
              clear * - r17573 b17574 b17575 d17564
              omega
            have d17576 : (x (-5) 12).toNat = 0 := by
              have r17577 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17578 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e17579 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b17580 := hb (x (-8) 3)
              have b17581 := hb (x (-7) 2)
              have b17582 := hb (x (-6) 13)
              have b17583 := hb (x (-5) 12)
              clear * - r17577 e17578 e17579 b17580 b17581 b17582 b17583 d17572
              omega
            have d17584 : (x (-5) 4).toNat = 0 := by
              have r17585 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
              have b17586 := hb (x (-5) 4)
              have b17587 := hb (x (-5) 12)
              clear * - r17585 b17586 b17587 d17576
              omega
            have d17588 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
              have r17589 := hand2 (x (-5) 3) (x (-5) 13)
              have b17590 := hb (x (-5) 13)
              have b17591 := hb (x (-5) 3 && x (-5) 13)
              clear * - r17589 b17590 b17591 d17517
              omega
            have d17592 : (x (-7) 5).toNat = 1 := by
              have r17593 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17594 := hb (x (-7) 5)
              have b17595 := hb (x (-2) 10)
              have b17596 := hb (x (-3) 1 && x (-3) 11)
              have b17597 := hb (x (-4) 2 && x (-4) 12)
              have b17598 := hb (x (-5) 3 && x (-5) 13)
              have b17599 := hb (x (-6) 4 && x (-6) 14)
              clear * - r17593 b17594 b17595 b17596 b17597 b17598 b17599 g4 g63 d17513 d17588 d17353
              omega
            have d17600 : (x (-2) 8).toNat = 0 := by
              have r17601 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17602 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e17603 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e17604 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e17605 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e17606 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e17607 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b17608 := hb (x (-9) 7)
              have b17609 := hb (x (-8) 6)
              have b17610 := hb (x (-7) 5)
              have b17611 := hb (x (-6) 4)
              have b17612 := hb (x (-5) 11)
              have b17613 := hb (x (-4) 10)
              have b17614 := hb (x (-3) 9)
              have b17615 := hb (x (-2) 8)
              clear * - r17601 e17602 e17603 e17604 e17605 e17606 e17607 b17608 b17609 b17610 b17611 b17612 b17613 b17614 b17615 d17377 d17592
              omega
            have d17616 : (x (-2) 8 && x (-2) 14).toNat = 0 := by
              have r17617 := hand1 (x (-2) 8) (x (-2) 14)
              have b17618 := hb (x (-2) 8)
              have b17619 := hb (x (-2) 8 && x (-2) 14)
              clear * - r17617 b17618 b17619 d17600
              omega
            have d17620 : (x (-2) 8 && x (-2) 12).toNat = 0 := by
              have r17621 := hand1 (x (-2) 8) (x (-2) 12)
              have b17622 := hb (x (-2) 8)
              have b17623 := hb (x (-2) 8 && x (-2) 12)
              clear * - r17621 b17622 b17623 d17600
              omega
            have d17624 : (x (-3) 9).toNat = 0 := by
              have r17625 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17626 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e17627 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e17628 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e17629 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e17630 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e17631 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b17632 := hb (x (-9) 7)
              have b17633 := hb (x (-8) 6)
              have b17634 := hb (x (-7) 5)
              have b17635 := hb (x (-6) 4)
              have b17636 := hb (x (-5) 11)
              have b17637 := hb (x (-4) 10)
              have b17638 := hb (x (-3) 9)
              have b17639 := hb (x (-2) 8)
              clear * - r17625 e17626 e17627 e17628 e17629 e17630 e17631 b17632 b17633 b17634 b17635 b17636 b17637 b17638 b17639 d17600 d17377 d17592
              omega
            have d17640 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
              have r17641 := hand1 (x (-3) 9) (x (-3) 13)
              have b17642 := hb (x (-3) 9)
              have b17643 := hb (x (-3) 9 && x (-3) 13)
              clear * - r17641 b17642 b17643 d17624
              omega
            have d17644 : (x (-4) 10).toNat = 0 := by
              have r17645 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17646 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e17647 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e17648 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e17649 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e17650 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e17651 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b17652 := hb (x (-9) 7)
              have b17653 := hb (x (-8) 6)
              have b17654 := hb (x (-7) 5)
              have b17655 := hb (x (-6) 4)
              have b17656 := hb (x (-5) 11)
              have b17657 := hb (x (-4) 10)
              have b17658 := hb (x (-3) 9)
              have b17659 := hb (x (-2) 8)
              clear * - r17645 e17646 e17647 e17648 e17649 e17650 e17651 b17652 b17653 b17654 b17655 b17656 b17657 b17658 b17659 d17600 d17624 d17377 d17592
              omega
            have d17660 : (x (-5) 11).toNat = 0 := by
              have r17661 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17662 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e17663 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e17664 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e17665 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e17666 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e17667 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b17668 := hb (x (-9) 7)
              have b17669 := hb (x (-8) 6)
              have b17670 := hb (x (-7) 5)
              have b17671 := hb (x (-6) 4)
              have b17672 := hb (x (-5) 11)
              have b17673 := hb (x (-4) 10)
              have b17674 := hb (x (-3) 9)
              have b17675 := hb (x (-2) 8)
              clear * - r17661 e17662 e17663 e17664 e17665 e17666 e17667 b17668 b17669 b17670 b17671 b17672 b17673 b17674 b17675 d17600 d17624 d17644 d17377 d17592
              omega
            have r17676 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r17677 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r17678 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e17679 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e17680 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e17681 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e17682 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e17683 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e17684 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have r17685 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e17686 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
            have e17687 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
            have e17688 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
            have e17689 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
            have e17690 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
            have e17691 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
            have r17692 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e17693 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e17694 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have r17695 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e17696 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e17697 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have r17698 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e17699 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
            have e17700 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
            have r17701 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r17702 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r17703 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r17704 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r17705 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
            have r17706 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
            have r17707 := hand2 (x 4 2) (x 4 6)
            have r17708 := hand2 (x 3 3) (x 3 7)
            have r17709 := hand2 (x 5 1) (x 5 7)
            have r17710 := hand2 (x 5 1) (x 5 11)
            have r17711 := hand1 (x 4 2) (x 4 12)
            have r17712 := hand1 (x 3 3) (x 3 13)
            have r17713 := hand2 (x 9 1) (x 9 11)
            have r17714 := hand2 (x 8 2) (x 8 12)
            have r17715 := hand1 (x 7 3) (x 7 13)
            have r17716 := hand1 (x 6 4) (x 6 14)
            have r17717 := hand2 (x (-2) 1) (x (-2) 12)
            have r17718 := hand2 (x (-3) 2) (x (-3) 13)
            have r17719 := hand2 (x (-4) 3) (x (-4) 14)
            have b17757 := hb (x 7 1)
            linarith only [r17676, r17677, r17678, e17679, e17680, e17681, e17682, e17683, e17684, r17685, e17686, e17687, e17688, e17689, e17690, e17691, r17692, e17693, e17694, r17695, e17696, e17697, r17698, e17699, e17700, r17701, r17702, r17703, r17704, r17705, r17706, r17707, r17708, r17709, r17710, r17711, r17712, r17713, r17714, r17715, r17716, r17717, r17718, r17719, b17757, d17345, d17584, d17660, d17517, d17644, d17501, d17624, g2, g4, g6, g7, g10, f17074, g13, f17196, d17091, d17075, g25, g26, d16785, g27, d17620, d17640, g42, g43, g44, g45, d16777, g46, d17616, g67]
          · have f17798 : (x 1 7).toNat = 1 := by rw [h17195]; rfl
            have d17799 : (x 8 8).toNat = 0 := by
              have r17800 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17801 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e17802 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e17803 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e17804 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e17805 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e17806 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b17807 := hb (x 1 7)
              have b17808 := hb (x 2 6)
              have b17809 := hb (x 3 5)
              have b17810 := hb (x 4 4)
              have b17811 := hb (x 5 11)
              have b17812 := hb (x 6 10)
              have b17813 := hb (x 7 9)
              have b17814 := hb (x 8 8)
              clear * - r17800 e17801 e17802 e17803 e17804 e17805 e17806 b17807 b17808 b17809 b17810 b17811 b17812 b17813 b17814 f17798
              omega
            have d17815 : (x 8 1 && x 8 8).toNat = 0 := by
              have r17816 := hand2 (x 8 1) (x 8 8)
              have b17817 := hb (x 8 8)
              have b17818 := hb (x 8 1 && x 8 8)
              clear * - r17816 b17817 b17818 d17799
              omega
            have d17819 : (x 8 3 && x 8 8).toNat = 0 := by
              have r17820 := hand2 (x 8 3) (x 8 8)
              have b17821 := hb (x 8 8)
              have b17822 := hb (x 8 3 && x 8 8)
              clear * - r17820 b17821 b17822 d17799
              omega
            have d17823 : (x 7 9).toNat = 0 := by
              have r17824 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17825 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e17826 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e17827 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e17828 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e17829 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e17830 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b17831 := hb (x 1 7)
              have b17832 := hb (x 2 6)
              have b17833 := hb (x 3 5)
              have b17834 := hb (x 4 4)
              have b17835 := hb (x 5 11)
              have b17836 := hb (x 6 10)
              have b17837 := hb (x 7 9)
              have b17838 := hb (x 8 8)
              clear * - r17824 e17825 e17826 e17827 e17828 e17829 e17830 b17831 b17832 b17833 b17834 b17835 b17836 b17837 b17838 d17799 f17798
              omega
            have d17839 : (x 7 2 && x 7 9).toNat = 0 := by
              have r17840 := hand2 (x 7 2) (x 7 9)
              have b17841 := hb (x 7 9)
              have b17842 := hb (x 7 2 && x 7 9)
              clear * - r17840 b17841 b17842 d17823
              omega
            have d17843 : (x 7 4 && x 7 9).toNat = 0 := by
              have r17844 := hand2 (x 7 4) (x 7 9)
              have b17845 := hb (x 7 9)
              have b17846 := hb (x 7 4 && x 7 9)
              clear * - r17844 b17845 b17846 d17823
              omega
            have d17847 : (x 6 10).toNat = 0 := by
              have r17848 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17849 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e17850 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e17851 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e17852 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e17853 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e17854 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b17855 := hb (x 1 7)
              have b17856 := hb (x 2 6)
              have b17857 := hb (x 3 5)
              have b17858 := hb (x 4 4)
              have b17859 := hb (x 5 11)
              have b17860 := hb (x 6 10)
              have b17861 := hb (x 7 9)
              have b17862 := hb (x 8 8)
              clear * - r17848 e17849 e17850 e17851 e17852 e17853 e17854 b17855 b17856 b17857 b17858 b17859 b17860 b17861 b17862 d17799 d17823 f17798
              omega
            have d17863 : (x 6 1 && x 6 10).toNat = 0 := by
              have r17864 := hand2 (x 6 1) (x 6 10)
              have b17865 := hb (x 6 10)
              have b17866 := hb (x 6 1 && x 6 10)
              clear * - r17864 b17865 b17866 d17847
              omega
            have d17867 : (x 6 3 && x 6 10).toNat = 0 := by
              have r17868 := hand2 (x 6 3) (x 6 10)
              have b17869 := hb (x 6 10)
              have b17870 := hb (x 6 3 && x 6 10)
              clear * - r17868 b17869 b17870 d17847
              omega
            have d17871 : (x 6 5 && x 6 10).toNat = 0 := by
              have r17872 := hand2 (x 6 5) (x 6 10)
              have b17873 := hb (x 6 10)
              have b17874 := hb (x 6 5 && x 6 10)
              clear * - r17872 b17873 b17874 d17847
              omega
            have d17875 : (x 5 11).toNat = 0 := by
              have r17876 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17877 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e17878 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e17879 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e17880 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e17881 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e17882 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b17883 := hb (x 1 7)
              have b17884 := hb (x 2 6)
              have b17885 := hb (x 3 5)
              have b17886 := hb (x 4 4)
              have b17887 := hb (x 5 11)
              have b17888 := hb (x 6 10)
              have b17889 := hb (x 7 9)
              have b17890 := hb (x 8 8)
              clear * - r17876 e17877 e17878 e17879 e17880 e17881 e17882 b17883 b17884 b17885 b17886 b17887 b17888 b17889 b17890 d17799 d17823 d17847 f17798
              omega
            have d17891 : (x 5 1 && x 5 11).toNat = 0 := by
              have r17892 := hand2 (x 5 1) (x 5 11)
              have b17893 := hb (x 5 11)
              have b17894 := hb (x 5 1 && x 5 11)
              clear * - r17892 b17893 b17894 d17875
              omega
            have d17895 : (x 5 2 && x 5 11).toNat = 0 := by
              have r17896 := hand2 (x 5 2) (x 5 11)
              have b17897 := hb (x 5 11)
              have b17898 := hb (x 5 2 && x 5 11)
              clear * - r17896 b17897 b17898 d17875
              omega
            have d17899 : (x 4 3 && x 4 12).toNat = 1 := by
              have r17900 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17901 := hb (x 1 6)
              have b17902 := hb (x 7 9)
              have b17903 := hb (x 6 1 && x 6 10)
              have b17904 := hb (x 5 2 && x 5 11)
              have b17905 := hb (x 4 3 && x 4 12)
              have b17906 := hb (x 3 4 && x 3 13)
              have b17907 := hb (x 2 5 && x 2 14)
              clear * - r17900 b17901 b17902 b17903 b17904 b17905 b17906 b17907 d17823 d17863 d17895 g61 g62 g14
              omega
            have d17908 : (x 4 12).toNat = 1 := by
              have r17909 := hand2 (x 4 3) (x 4 12)
              have b17910 := hb (x 4 12)
              have b17911 := hb (x 4 3 && x 4 12)
              clear * - r17909 b17910 b17911 d17899
              omega
            have d17912 : (x 3 13).toNat = 0 := by
              have r17913 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17914 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e17915 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b17916 := hb (x 1 3)
              have b17917 := hb (x 2 2)
              have b17918 := hb (x 3 13)
              have b17919 := hb (x 4 12)
              clear * - r17913 e17914 e17915 b17916 b17917 b17918 b17919 d17908 f17194
              omega
            have d17920 : (x 3 3 && x 3 13).toNat = 0 := by
              have r17921 := hand2 (x 3 3) (x 3 13)
              have b17922 := hb (x 3 13)
              have b17923 := hb (x 3 3 && x 3 13)
              clear * - r17921 b17922 b17923 d17912
              omega
            have d17924 : (x 4 2 && x 4 12).toNat = 1 := by
              have r17925 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17926 := hb (x 1 5)
              have b17927 := hb (x 6 10)
              have b17928 := hb (x 5 1 && x 5 11)
              have b17929 := hb (x 4 2 && x 4 12)
              have b17930 := hb (x 3 3 && x 3 13)
              have b17931 := hb (x 2 4 && x 2 14)
              clear * - r17925 b17926 b17927 b17928 b17929 b17930 b17931 d17847 d17891 d17920 g67 g13
              omega
            have d17932 : (x 4 2).toNat = 1 := by
              have r17933 := hand1 (x 4 2) (x 4 12)
              have b17934 := hb (x 4 2)
              have b17935 := hb (x 4 2 && x 4 12)
              clear * - r17933 b17934 b17935 d17924
              omega
            have d17936 : (x 4 14).toNat = 1 := by
              have r17937 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
              have b17938 := hb (x 4 2)
              have b17939 := hb (x 4 14)
              clear * - r17937 b17938 b17939 d17932
              omega
            have d17940 : (x 3 1).toNat = 0 := by
              have r17941 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17942 := hb (x 3 1)
              have b17943 := hb (x 4 14)
              clear * - r17941 b17942 b17943 d17936
              omega
            have d17944 : (x 3 1 && x 3 14).toNat = 0 := by
              have r17945 := hand1 (x 3 1) (x 3 14)
              have b17946 := hb (x 3 1)
              have b17947 := hb (x 3 1 && x 3 14)
              clear * - r17945 b17946 b17947 d17940
              omega
            have d17948 : (x 6 12).toNat = 0 := by
              have r17949 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17950 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e17951 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b17952 := hb (x 3 3)
              have b17953 := hb (x 4 2)
              have b17954 := hb (x 5 13)
              have b17955 := hb (x 6 12)
              clear * - r17949 e17950 e17951 b17952 b17953 b17954 b17955 d17932
              omega
            have d17956 : (x 5 13).toNat = 0 := by
              have r17957 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e17958 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e17959 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b17960 := hb (x 3 3)
              have b17961 := hb (x 4 2)
              have b17962 := hb (x 5 13)
              have b17963 := hb (x 6 12)
              clear * - r17957 e17958 e17959 b17960 b17961 b17962 b17963 d17948 d17932
              omega
            have d17964 : (x 3 6 && x 3 13).toNat = 0 := by
              have r17965 := hand2 (x 3 6) (x 3 13)
              have b17966 := hb (x 3 13)
              have b17967 := hb (x 3 6 && x 3 13)
              clear * - r17965 b17966 b17967 d17912
              omega
            have d17968 : (x 3 5).toNat = 0 := by
              have r17969 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
              have b17970 := hb (x 3 5)
              have b17971 := hb (x 3 13)
              clear * - r17969 b17970 b17971 d17912
              omega
            have d17972 : (x 3 5 && x 3 14).toNat = 0 := by
              have r17973 := hand1 (x 3 5) (x 3 14)
              have b17974 := hb (x 3 5)
              have b17975 := hb (x 3 5 && x 3 14)
              clear * - r17973 b17974 b17975 d17968
              omega
            have d17976 : (x 2 1 && x 2 14).toNat = 1 := by
              have r17977 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17978 := hb (x 1 2)
              have b17979 := hb (x 3 13)
              have b17980 := hb (x 2 1 && x 2 14)
              clear * - r17977 b17978 b17979 b17980 d17912 g11
              omega
            have d17981 : (x 2 1).toNat = 1 := by
              have r17982 := hand1 (x 2 1) (x 2 14)
              have b17983 := hb (x 2 1)
              have b17984 := hb (x 2 1 && x 2 14)
              clear * - r17982 b17983 b17984 d17976
              omega
            have d17985 : (x 3 14).toNat = 0 := by
              have r17986 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17987 := hb (x 2 1)
              have b17988 := hb (x 3 14)
              clear * - r17986 b17987 b17988 d17981
              omega
            have d17989 : (x 3 6).toNat = 0 := by
              have r17990 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
              have b17991 := hb (x 3 6)
              have b17992 := hb (x 3 14)
              clear * - r17990 b17991 b17992 d17985
              omega
            have d17993 : (x 3 2).toNat = 0 := by
              have r17994 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
              have b17995 := hb (x 3 2)
              have b17996 := hb (x 3 14)
              clear * - r17994 b17995 b17996 d17985
              omega
            have d17997 : (x 4 1 && x 4 14).toNat = 1 := by
              have r17998 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b17999 := hb (x 3 2)
              have b18000 := hb (x 5 13)
              have b18001 := hb (x 4 1 && x 4 14)
              clear * - r17998 b17999 b18000 b18001 d17956 d17993
              omega
            have d18002 : (x 4 1).toNat = 1 := by
              have r18003 := hand1 (x 4 1) (x 4 14)
              have b18004 := hb (x 4 1)
              have b18005 := hb (x 4 1 && x 4 14)
              clear * - r18003 b18004 b18005 d17997
              omega
            have d18006 : (x 5 14).toNat = 0 := by
              have r18007 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b18008 := hb (x 4 1)
              have b18009 := hb (x 5 14)
              clear * - r18007 b18008 b18009 d18002
              omega
            have d18010 : (x 5 3 && x 5 14).toNat = 0 := by
              have r18011 := hand2 (x 5 3) (x 5 14)
              have b18012 := hb (x 5 14)
              have b18013 := hb (x 5 3 && x 5 14)
              clear * - r18011 b18012 b18013 d18006
              omega
            have d18014 : (x 5 6).toNat = 0 := by
              have r18015 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
              have b18016 := hb (x 5 6)
              have b18017 := hb (x 5 14)
              clear * - r18015 b18016 b18017 d18006
              omega
            have d18018 : (x 5 6 && x 5 11).toNat = 0 := by
              have r18019 := hand1 (x 5 6) (x 5 11)
              have b18020 := hb (x 5 6)
              have b18021 := hb (x 5 6 && x 5 11)
              clear * - r18019 b18020 b18021 d18014
              omega
            have d18022 : (x 5 2).toNat = 0 := by
              have r18023 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b18024 := hb (x 5 2)
              have b18025 := hb (x 5 14)
              clear * - r18023 b18024 b18025 d18006
              omega
            have d18026 : (x 2 2).toNat = 0 := by
              have r18027 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18028 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e18029 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b18030 := hb (x 1 3)
              have b18031 := hb (x 2 2)
              have b18032 := hb (x 3 13)
              have b18033 := hb (x 4 12)
              clear * - r18027 e18028 e18029 b18030 b18031 b18032 b18033 d17908 d17912 f17194
              omega
            have d18034 : (x 4 13).toNat = 1 := by
              have r18035 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b18036 := hb (x 2 2)
              have b18037 := hb (x 4 13)
              have b18038 := hb (x 3 1 && x 3 14)
              clear * - r18035 b18036 b18037 b18038 d17944 d18026
              omega
            have d18039 : (x 5 12).toNat = 0 := by
              have r18040 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18041 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e18042 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b18043 := hb (x 2 3)
              have b18044 := hb (x 3 2)
              have b18045 := hb (x 4 13)
              have b18046 := hb (x 5 12)
              clear * - r18040 e18041 e18042 b18043 b18044 b18045 b18046 d18034 d17993
              omega
            have d18047 : (x 5 3 && x 5 12).toNat = 0 := by
              have r18048 := hand2 (x 5 3) (x 5 12)
              have b18049 := hb (x 5 12)
              have b18050 := hb (x 5 3 && x 5 12)
              clear * - r18048 b18049 b18050 d18039
              omega
            have d18051 : (x 5 4).toNat = 0 := by
              have r18052 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b18053 := hb (x 5 4)
              have b18054 := hb (x 5 12)
              clear * - r18052 b18053 b18054 d18039
              omega
            have d18055 : (x 5 4 && x 5 11).toNat = 0 := by
              have r18056 := hand1 (x 5 4) (x 5 11)
              have b18057 := hb (x 5 4)
              have b18058 := hb (x 5 4 && x 5 11)
              clear * - r18056 b18057 b18058 d18051
              omega
            have d18059 : (x 4 3).toNat = 1 := by
              have r18060 := hand1 (x 4 3) (x 4 12)
              have b18061 := hb (x 4 3)
              have b18062 := hb (x 4 3 && x 4 12)
              clear * - r18060 b18061 b18062 d17899
              omega
            have d18063 : (x 7 12).toNat = 0 := by
              have r18064 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18065 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e18066 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b18067 := hb (x 4 3)
              have b18068 := hb (x 5 2)
              have b18069 := hb (x 6 13)
              have b18070 := hb (x 7 12)
              clear * - r18064 e18065 e18066 b18067 b18068 b18069 b18070 d18022 d18059
              omega
            have d18071 : (x 7 1 && x 7 12).toNat = 0 := by
              have r18072 := hand2 (x 7 1) (x 7 12)
              have b18073 := hb (x 7 12)
              have b18074 := hb (x 7 1 && x 7 12)
              clear * - r18072 b18073 b18074 d18063
              omega
            have d18075 : (x 7 4).toNat = 0 := by
              have r18076 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
              have b18077 := hb (x 7 4)
              have b18078 := hb (x 7 12)
              clear * - r18076 b18077 b18078 d18063
              omega
            have d18079 : (x 6 13).toNat = 0 := by
              have r18080 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18081 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e18082 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b18083 := hb (x 4 3)
              have b18084 := hb (x 5 2)
              have b18085 := hb (x 6 13)
              have b18086 := hb (x 7 12)
              clear * - r18080 e18081 e18082 b18083 b18084 b18085 b18086 d18063 d18022 d18059
              omega
            have d18087 : (x 6 2 && x 6 13).toNat = 0 := by
              have r18088 := hand2 (x 6 2) (x 6 13)
              have b18089 := hb (x 6 13)
              have b18090 := hb (x 6 2 && x 6 13)
              clear * - r18088 b18089 b18090 d18079
              omega
            have d18091 : (x 6 5).toNat = 0 := by
              have r18092 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
              have b18093 := hb (x 6 5)
              have b18094 := hb (x 6 13)
              clear * - r18092 b18093 b18094 d18079
              omega
            have d18095 : (x 4 4).toNat = 0 := by
              have r18096 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18097 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e18098 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e18099 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e18100 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e18101 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e18102 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b18103 := hb (x 1 7)
              have b18104 := hb (x 2 6)
              have b18105 := hb (x 3 5)
              have b18106 := hb (x 4 4)
              have b18107 := hb (x 5 11)
              have b18108 := hb (x 6 10)
              have b18109 := hb (x 7 9)
              have b18110 := hb (x 8 8)
              clear * - r18096 e18097 e18098 e18099 e18100 e18101 e18102 b18103 b18104 b18105 b18106 b18107 b18108 b18109 b18110 d17799 d17823 d17847 d17875 d17968 f17798
              omega
            have d18111 : (x 4 4 && x 4 13).toNat = 0 := by
              have r18112 := hand1 (x 4 4) (x 4 13)
              have b18113 := hb (x 4 4)
              have b18114 := hb (x 4 4 && x 4 13)
              clear * - r18112 b18113 b18114 d18095
              omega
            have d18115 : (x 8 11).toNat = 1 := by
              have r18116 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b18117 := hb (x 4 4)
              have b18118 := hb (x 8 11)
              have b18119 := hb (x 7 1 && x 7 12)
              have b18120 := hb (x 6 2 && x 6 13)
              have b18121 := hb (x 5 3 && x 5 14)
              clear * - r18116 b18117 b18118 b18119 b18120 b18121 d18071 d18087 d18010 d18095
              omega
            have d18122 : (x 8 3).toNat = 1 := by
              have r18123 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
              have b18124 := hb (x 8 3)
              have b18125 := hb (x 8 11)
              clear * - r18123 b18124 b18125 d18115
              omega
            have d18126 : (x 11 12).toNat = 0 := by
              have r18127 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18128 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e18129 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b18130 := hb (x 8 3)
              have b18131 := hb (x 9 2)
              have b18132 := hb (x 10 13)
              have b18133 := hb (x 11 12)
              clear * - r18127 e18128 e18129 b18130 b18131 b18132 b18133 d18122
              omega
            have d18134 : (x 10 13).toNat = 0 := by
              have r18135 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18136 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e18137 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b18138 := hb (x 8 3)
              have b18139 := hb (x 9 2)
              have b18140 := hb (x 10 13)
              have b18141 := hb (x 11 12)
              clear * - r18135 e18136 e18137 b18138 b18139 b18140 b18141 d18126 d18122
              omega
            have d18142 : (x 9 2).toNat = 0 := by
              have r18143 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18144 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e18145 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b18146 := hb (x 8 3)
              have b18147 := hb (x 9 2)
              have b18148 := hb (x 10 13)
              have b18149 := hb (x 11 12)
              clear * - r18143 e18144 e18145 b18146 b18147 b18148 b18149 d18126 d18134 d18122
              omega
            have d18150 : (x 9 2 && x 9 7).toNat = 0 := by
              have r18151 := hand1 (x 9 2) (x 9 7)
              have b18152 := hb (x 9 2)
              have b18153 := hb (x 9 2 && x 9 7)
              clear * - r18151 b18152 b18153 d18142
              omega
            have d18154 : (x 9 10).toNat = 0 := by
              have r18155 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
              have b18156 := hb (x 9 2)
              have b18157 := hb (x 9 10)
              clear * - r18155 b18156 b18157 d18142
              omega
            have d18158 : (x 11 8).toNat = 0 := by
              have r18159 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18160 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e18161 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e18162 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e18163 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e18164 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e18165 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b18166 := hb (x 4 7)
              have b18167 := hb (x 5 6)
              have b18168 := hb (x 6 5)
              have b18169 := hb (x 7 4)
              have b18170 := hb (x 8 11)
              have b18171 := hb (x 9 10)
              have b18172 := hb (x 10 9)
              have b18173 := hb (x 11 8)
              clear * - r18159 e18160 e18161 e18162 e18163 e18164 e18165 b18166 b18167 b18168 b18169 b18170 b18171 b18172 b18173 d18154 d18115 d18075 d18091 d18014
              omega
            have d18174 : (x 10 9).toNat = 0 := by
              have r18175 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18176 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e18177 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e18178 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e18179 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e18180 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e18181 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b18182 := hb (x 4 7)
              have b18183 := hb (x 5 6)
              have b18184 := hb (x 6 5)
              have b18185 := hb (x 7 4)
              have b18186 := hb (x 8 11)
              have b18187 := hb (x 9 10)
              have b18188 := hb (x 10 9)
              have b18189 := hb (x 11 8)
              clear * - r18175 e18176 e18177 e18178 e18179 e18180 e18181 b18182 b18183 b18184 b18185 b18186 b18187 b18188 b18189 d18158 d18154 d18115 d18075 d18091 d18014
              omega
            have d18190 : (x 4 7).toNat = 0 := by
              have r18191 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18192 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e18193 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e18194 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e18195 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e18196 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e18197 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b18198 := hb (x 4 7)
              have b18199 := hb (x 5 6)
              have b18200 := hb (x 6 5)
              have b18201 := hb (x 7 4)
              have b18202 := hb (x 8 11)
              have b18203 := hb (x 9 10)
              have b18204 := hb (x 10 9)
              have b18205 := hb (x 11 8)
              clear * - r18191 e18192 e18193 e18194 e18195 e18196 e18197 b18198 b18199 b18200 b18201 b18202 b18203 b18204 b18205 d18158 d18174 d18154 d18115 d18075 d18091 d18014
              omega
            have d18206 : (x 4 7 && x 4 12).toNat = 0 := by
              have r18207 := hand1 (x 4 7) (x 4 12)
              have b18208 := hb (x 4 7)
              have b18209 := hb (x 4 7 && x 4 12)
              clear * - r18207 b18208 b18209 d18190
              omega
            have d18210 : (x 2 6).toNat = 0 := by
              have r18211 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e18212 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e18213 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e18214 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e18215 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e18216 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e18217 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b18218 := hb (x 1 7)
              have b18219 := hb (x 2 6)
              have b18220 := hb (x 3 5)
              have b18221 := hb (x 4 4)
              have b18222 := hb (x 5 11)
              have b18223 := hb (x 6 10)
              have b18224 := hb (x 7 9)
              have b18225 := hb (x 8 8)
              clear * - r18211 e18212 e18213 e18214 e18215 e18216 e18217 b18218 b18219 b18220 b18221 b18222 b18223 b18224 b18225 d17799 d17823 d17847 d17875 d18095 d17968 f17798
              omega
            have r18226 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r18227 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18228 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e18229 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e18230 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e18231 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e18232 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e18233 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have r18234 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r18235 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r18236 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r18237 := hand2 (x 10 1) (x 10 6)
            have r18238 := hand1 (x 4 5) (x 4 12)
            have r18239 := hand1 (x 2 7) (x 2 14)
            have r18240 := hand2 (x 7 1) (x 7 10)
            have r18241 := hand2 (x 6 2) (x 6 11)
            linarith only [r18226, r18227, e18228, e18229, e18230, e18231, e18232, e18233, r18234, r18235, r18236, r18237, r18238, r18239, r18240, r18241, g15, g16, d18210, d17189, d17989, d17912, d17908, d18051, d17875, d17847, d17823, d17799, d18150, d17819, d17843, d17871, d18018, d18206, g34, g35, d17815, d17839, d17867, d18055, d17964, d18047, d18111, d17972]
        · have f18288 : (x 1 3).toNat = 1 := by rw [h17193]; rfl
          have d18289 : (x 4 12).toNat = 0 := by
            have r18290 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18291 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e18292 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b18293 := hb (x 1 3)
            have b18294 := hb (x 2 2)
            have b18295 := hb (x 3 13)
            have b18296 := hb (x 4 12)
            clear * - r18290 e18291 e18292 b18293 b18294 b18295 b18296 f18288
            omega
          have d18297 : (x 4 1 && x 4 12).toNat = 0 := by
            have r18298 := hand2 (x 4 1) (x 4 12)
            have b18299 := hb (x 4 12)
            have b18300 := hb (x 4 1 && x 4 12)
            clear * - r18298 b18299 b18300 d18289
            omega
          have d18301 : (x 4 4).toNat = 0 := by
            have r18302 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b18303 := hb (x 4 4)
            have b18304 := hb (x 4 12)
            clear * - r18302 b18303 b18304 d18289
            omega
          have d18305 : (x 3 13).toNat = 0 := by
            have r18306 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18307 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e18308 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b18309 := hb (x 1 3)
            have b18310 := hb (x 2 2)
            have b18311 := hb (x 3 13)
            have b18312 := hb (x 4 12)
            clear * - r18306 e18307 e18308 b18309 b18310 b18311 b18312 d18289 f18288
            omega
          have d18313 : (x 3 2 && x 3 13).toNat = 0 := by
            have r18314 := hand2 (x 3 2) (x 3 13)
            have b18315 := hb (x 3 13)
            have b18316 := hb (x 3 2 && x 3 13)
            clear * - r18314 b18315 b18316 d18305
            omega
          have d18317 : (x 2 1 && x 2 14).toNat = 1 := by
            have r18318 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18319 := hb (x 1 2)
            have b18320 := hb (x 3 13)
            have b18321 := hb (x 2 1 && x 2 14)
            clear * - r18318 b18319 b18320 b18321 d18305 g11
            omega
          have d18322 : (x 2 1).toNat = 1 := by
            have r18323 := hand1 (x 2 1) (x 2 14)
            have b18324 := hb (x 2 1)
            have b18325 := hb (x 2 1 && x 2 14)
            clear * - r18323 b18324 b18325 d18317
            omega
          have d18326 : (x 3 14).toNat = 0 := by
            have r18327 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18328 := hb (x 2 1)
            have b18329 := hb (x 3 14)
            clear * - r18327 b18328 b18329 d18322
            omega
          have d18330 : (x 3 1 && x 3 14).toNat = 0 := by
            have r18331 := hand2 (x 3 1) (x 3 14)
            have b18332 := hb (x 3 14)
            have b18333 := hb (x 3 1 && x 3 14)
            clear * - r18331 b18332 b18333 d18326
            omega
          have d18334 : (x 3 2).toNat = 0 := by
            have r18335 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b18336 := hb (x 3 2)
            have b18337 := hb (x 3 14)
            clear * - r18335 b18336 b18337 d18326
            omega
          have d18338 : (x 2 2).toNat = 0 := by
            have r18339 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18340 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e18341 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b18342 := hb (x 1 3)
            have b18343 := hb (x 2 2)
            have b18344 := hb (x 3 13)
            have b18345 := hb (x 4 12)
            clear * - r18339 e18340 e18341 b18342 b18343 b18344 b18345 d18289 d18305 f18288
            omega
          have d18346 : (x 4 13).toNat = 1 := by
            have r18347 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18348 := hb (x 2 2)
            have b18349 := hb (x 4 13)
            have b18350 := hb (x 3 1 && x 3 14)
            clear * - r18347 b18348 b18349 b18350 d18330 d18338
            omega
          have d18351 : (x 4 1).toNat = 1 := by
            have r18352 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
            have b18353 := hb (x 4 1)
            have b18354 := hb (x 4 13)
            clear * - r18352 b18353 b18354 d18346
            omega
          have d18355 : (x 5 14).toNat = 0 := by
            have r18356 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18357 := hb (x 4 1)
            have b18358 := hb (x 5 14)
            clear * - r18356 b18357 b18358 d18351
            omega
          have d18359 : (x 5 3 && x 5 14).toNat = 0 := by
            have r18360 := hand2 (x 5 3) (x 5 14)
            have b18361 := hb (x 5 14)
            have b18362 := hb (x 5 3 && x 5 14)
            clear * - r18360 b18361 b18362 d18355
            omega
          have d18363 : (x 5 2).toNat = 0 := by
            have r18364 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b18365 := hb (x 5 2)
            have b18366 := hb (x 5 14)
            clear * - r18364 b18365 b18366 d18355
            omega
          have d18367 : (x 5 12).toNat = 0 := by
            have r18368 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18369 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e18370 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b18371 := hb (x 2 3)
            have b18372 := hb (x 3 2)
            have b18373 := hb (x 4 13)
            have b18374 := hb (x 5 12)
            clear * - r18368 e18369 e18370 b18371 b18372 b18373 b18374 d18346 d18334
            omega
          have d18375 : (x 5 4).toNat = 0 := by
            have r18376 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b18377 := hb (x 5 4)
            have b18378 := hb (x 5 12)
            clear * - r18376 b18377 b18378 d18367
            omega
          have d18379 : (x 2 3).toNat = 0 := by
            have r18380 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18381 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e18382 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b18383 := hb (x 2 3)
            have b18384 := hb (x 3 2)
            have b18385 := hb (x 4 13)
            have b18386 := hb (x 5 12)
            clear * - r18380 e18381 e18382 b18383 b18384 b18385 b18386 d18367 d18346 d18334
            omega
          have d18387 : (x 2 3 && x 2 14).toNat = 0 := by
            have r18388 := hand1 (x 2 3) (x 2 14)
            have b18389 := hb (x 2 3)
            have b18390 := hb (x 2 3 && x 2 14)
            clear * - r18388 b18389 b18390 d18379
            omega
          have d18391 : (x 5 11).toNat = 1 := by
            have r18392 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18393 := hb (x 1 4)
            have b18394 := hb (x 5 11)
            have b18395 := hb (x 4 1 && x 4 12)
            have b18396 := hb (x 3 2 && x 3 13)
            have b18397 := hb (x 2 3 && x 2 14)
            clear * - r18392 b18393 b18394 b18395 b18396 b18397 d18297 d18313 d18387 g12
            omega
          have d18398 : (x 5 3).toNat = 1 := by
            have r18399 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
            have b18400 := hb (x 5 3)
            have b18401 := hb (x 5 11)
            clear * - r18399 b18400 b18401 d18391
            omega
          have d18402 : (x 8 12).toNat = 0 := by
            have r18403 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18404 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e18405 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b18406 := hb (x 5 3)
            have b18407 := hb (x 6 2)
            have b18408 := hb (x 7 13)
            have b18409 := hb (x 8 12)
            clear * - r18403 e18404 e18405 b18406 b18407 b18408 b18409 d18398
            omega
          have d18410 : (x 8 1 && x 8 12).toNat = 0 := by
            have r18411 := hand2 (x 8 1) (x 8 12)
            have b18412 := hb (x 8 12)
            have b18413 := hb (x 8 1 && x 8 12)
            clear * - r18411 b18412 b18413 d18402
            omega
          have d18414 : (x 8 4).toNat = 0 := by
            have r18415 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
            have b18416 := hb (x 8 4)
            have b18417 := hb (x 8 12)
            clear * - r18415 b18416 b18417 d18402
            omega
          have d18418 : (x 7 13).toNat = 0 := by
            have r18419 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18420 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e18421 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b18422 := hb (x 5 3)
            have b18423 := hb (x 6 2)
            have b18424 := hb (x 7 13)
            have b18425 := hb (x 8 12)
            clear * - r18419 e18420 e18421 b18422 b18423 b18424 b18425 d18402 d18398
            omega
          have d18426 : (x 7 2 && x 7 13).toNat = 0 := by
            have r18427 := hand2 (x 7 2) (x 7 13)
            have b18428 := hb (x 7 13)
            have b18429 := hb (x 7 2 && x 7 13)
            clear * - r18427 b18428 b18429 d18418
            omega
          have d18430 : (x 6 1 && x 6 14).toNat = 1 := by
            have r18431 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18432 := hb (x 5 2)
            have b18433 := hb (x 7 13)
            have b18434 := hb (x 6 1 && x 6 14)
            clear * - r18431 b18432 b18433 b18434 d18418 d18363
            omega
          have d18435 : (x 6 1).toNat = 1 := by
            have r18436 := hand1 (x 6 1) (x 6 14)
            have b18437 := hb (x 6 1)
            have b18438 := hb (x 6 1 && x 6 14)
            clear * - r18436 b18437 b18438 d18430
            omega
          have d18439 : (x 7 14).toNat = 0 := by
            have r18440 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18441 := hb (x 6 1)
            have b18442 := hb (x 7 14)
            clear * - r18440 b18441 b18442 d18435
            omega
          have d18443 : (x 7 1 && x 7 14).toNat = 0 := by
            have r18444 := hand2 (x 7 1) (x 7 14)
            have b18445 := hb (x 7 14)
            have b18446 := hb (x 7 1 && x 7 14)
            clear * - r18444 b18445 b18446 d18439
            omega
          have d18447 : (x 7 2).toNat = 0 := by
            have r18448 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b18449 := hb (x 7 2)
            have b18450 := hb (x 7 14)
            clear * - r18448 b18449 b18450 d18439
            omega
          have d18451 : (x 6 2).toNat = 0 := by
            have r18452 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18453 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e18454 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b18455 := hb (x 5 3)
            have b18456 := hb (x 6 2)
            have b18457 := hb (x 7 13)
            have b18458 := hb (x 8 12)
            clear * - r18452 e18453 e18454 b18455 b18456 b18457 b18458 d18402 d18418 d18398
            omega
          have d18459 : (x 6 2 && x 6 13).toNat = 0 := by
            have r18460 := hand1 (x 6 2) (x 6 13)
            have b18461 := hb (x 6 2)
            have b18462 := hb (x 6 2 && x 6 13)
            clear * - r18460 b18461 b18462 d18451
            omega
          have d18463 : (x 8 13).toNat = 1 := by
            have r18464 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18465 := hb (x 6 2)
            have b18466 := hb (x 8 13)
            have b18467 := hb (x 7 1 && x 7 14)
            clear * - r18464 b18465 b18466 b18467 d18443 d18451
            omega
          have d18468 : (x 8 1).toNat = 1 := by
            have r18469 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
            have b18470 := hb (x 8 1)
            have b18471 := hb (x 8 13)
            clear * - r18469 b18470 b18471 d18463
            omega
          have d18472 : (x 9 14).toNat = 0 := by
            have r18473 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18474 := hb (x 8 1)
            have b18475 := hb (x 9 14)
            clear * - r18473 b18474 b18475 d18468
            omega
          have d18476 : (x 9 3 && x 9 14).toNat = 0 := by
            have r18477 := hand2 (x 9 3) (x 9 14)
            have b18478 := hb (x 9 14)
            have b18479 := hb (x 9 3 && x 9 14)
            clear * - r18477 b18478 b18479 d18472
            omega
          have d18480 : (x 9 2).toNat = 0 := by
            have r18481 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
            have b18482 := hb (x 9 2)
            have b18483 := hb (x 9 14)
            clear * - r18481 b18482 b18483 d18472
            omega
          have d18484 : (x 9 12).toNat = 0 := by
            have r18485 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18486 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e18487 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b18488 := hb (x 6 3)
            have b18489 := hb (x 7 2)
            have b18490 := hb (x 8 13)
            have b18491 := hb (x 9 12)
            clear * - r18485 e18486 e18487 b18488 b18489 b18490 b18491 d18463 d18447
            omega
          have d18492 : (x 9 4).toNat = 0 := by
            have r18493 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
            have b18494 := hb (x 9 4)
            have b18495 := hb (x 9 12)
            clear * - r18493 b18494 b18495 d18484
            omega
          have d18496 : (x 6 3).toNat = 0 := by
            have r18497 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18498 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e18499 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b18500 := hb (x 6 3)
            have b18501 := hb (x 7 2)
            have b18502 := hb (x 8 13)
            have b18503 := hb (x 9 12)
            clear * - r18497 e18498 e18499 b18500 b18501 b18502 b18503 d18484 d18463 d18447
            omega
          have d18504 : (x 6 3 && x 6 14).toNat = 0 := by
            have r18505 := hand1 (x 6 3) (x 6 14)
            have b18506 := hb (x 6 3)
            have b18507 := hb (x 6 3 && x 6 14)
            clear * - r18505 b18506 b18507 d18496
            omega
          have d18508 : (x 9 11).toNat = 1 := by
            have r18509 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18510 := hb (x 5 4)
            have b18511 := hb (x 9 11)
            have b18512 := hb (x 8 1 && x 8 12)
            have b18513 := hb (x 7 2 && x 7 13)
            have b18514 := hb (x 6 3 && x 6 14)
            clear * - r18509 b18510 b18511 b18512 b18513 b18514 d18410 d18426 d18504 d18375
            omega
          have d18515 : (x 9 3).toNat = 1 := by
            have r18516 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
            have b18517 := hb (x 9 3)
            have b18518 := hb (x 9 11)
            clear * - r18516 b18517 b18518 d18508
            omega
          have d18519 : (x 12 12).toNat = 0 := by
            have r18520 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18521 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e18522 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b18523 := hb (x 9 3)
            have b18524 := hb (x 10 2)
            have b18525 := hb (x 11 13)
            have b18526 := hb (x 12 12)
            clear * - r18520 e18521 e18522 b18523 b18524 b18525 b18526 d18515
            omega
          have d18527 : (x 12 1 && x 12 12).toNat = 0 := by
            have r18528 := hand2 (x 12 1) (x 12 12)
            have b18529 := hb (x 12 12)
            have b18530 := hb (x 12 1 && x 12 12)
            clear * - r18528 b18529 b18530 d18519
            omega
          have d18531 : (x 12 4).toNat = 0 := by
            have r18532 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
            have b18533 := hb (x 12 4)
            have b18534 := hb (x 12 12)
            clear * - r18532 b18533 b18534 d18519
            omega
          have d18535 : (x 11 13).toNat = 0 := by
            have r18536 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18537 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e18538 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b18539 := hb (x 9 3)
            have b18540 := hb (x 10 2)
            have b18541 := hb (x 11 13)
            have b18542 := hb (x 12 12)
            clear * - r18536 e18537 e18538 b18539 b18540 b18541 b18542 d18519 d18515
            omega
          have d18543 : (x 11 2 && x 11 13).toNat = 0 := by
            have r18544 := hand2 (x 11 2) (x 11 13)
            have b18545 := hb (x 11 13)
            have b18546 := hb (x 11 2 && x 11 13)
            clear * - r18544 b18545 b18546 d18535
            omega
          have d18547 : (x 10 1 && x 10 14).toNat = 1 := by
            have r18548 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18549 := hb (x 9 2)
            have b18550 := hb (x 11 13)
            have b18551 := hb (x 10 1 && x 10 14)
            clear * - r18548 b18549 b18550 b18551 d18535 d18480
            omega
          have d18552 : (x 10 14).toNat = 1 := by
            have r18553 := hand2 (x 10 1) (x 10 14)
            have b18554 := hb (x 10 14)
            have b18555 := hb (x 10 1 && x 10 14)
            clear * - r18553 b18554 b18555 d18547
            omega
          have d18556 : (x 9 1).toNat = 0 := by
            have r18557 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18558 := hb (x 9 1)
            have b18559 := hb (x 10 14)
            clear * - r18557 b18558 b18559 d18552
            omega
          have d18560 : (x 9 13).toNat = 0 := by
            have r18561 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
            have b18562 := hb (x 9 1)
            have b18563 := hb (x 9 13)
            clear * - r18561 b18562 b18563 d18556
            omega
          have d18564 : (x 8 1 && x 8 14).toNat = 1 := by
            have r18565 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18566 := hb (x 7 2)
            have b18567 := hb (x 9 13)
            have b18568 := hb (x 8 1 && x 8 14)
            clear * - r18565 b18566 b18567 b18568 d18560 d18447
            omega
          have d18569 : (x 8 14).toNat = 1 := by
            have r18570 := hand2 (x 8 1) (x 8 14)
            have b18571 := hb (x 8 14)
            have b18572 := hb (x 8 1 && x 8 14)
            clear * - r18570 b18571 b18572 d18564
            omega
          have d18573 : (x 7 1).toNat = 0 := by
            have r18574 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18575 := hb (x 7 1)
            have b18576 := hb (x 8 14)
            clear * - r18574 b18575 b18576 d18569
            omega
          have d18577 : (x 7 1 && x 7 12).toNat = 0 := by
            have r18578 := hand1 (x 7 1) (x 7 12)
            have b18579 := hb (x 7 1)
            have b18580 := hb (x 7 1 && x 7 12)
            clear * - r18578 b18579 b18580 d18573
            omega
          have d18581 : (x 8 11).toNat = 1 := by
            have r18582 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18583 := hb (x 4 4)
            have b18584 := hb (x 8 11)
            have b18585 := hb (x 7 1 && x 7 12)
            have b18586 := hb (x 6 2 && x 6 13)
            have b18587 := hb (x 5 3 && x 5 14)
            clear * - r18582 b18583 b18584 b18585 b18586 b18587 d18577 d18459 d18359 d18301
            omega
          have d18588 : (x 8 3).toNat = 1 := by
            have r18589 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
            have b18590 := hb (x 8 3)
            have b18591 := hb (x 8 11)
            clear * - r18589 b18590 b18591 d18581
            omega
          have d18592 : (x 11 12).toNat = 0 := by
            have r18593 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18594 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e18595 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b18596 := hb (x 8 3)
            have b18597 := hb (x 9 2)
            have b18598 := hb (x 10 13)
            have b18599 := hb (x 11 12)
            clear * - r18593 e18594 e18595 b18596 b18597 b18598 b18599 d18480 d18588
            omega
          have d18600 : (x 11 1 && x 11 12).toNat = 0 := by
            have r18601 := hand2 (x 11 1) (x 11 12)
            have b18602 := hb (x 11 12)
            have b18603 := hb (x 11 1 && x 11 12)
            clear * - r18601 b18602 b18603 d18592
            omega
          have d18604 : (x 10 13).toNat = 0 := by
            have r18605 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18606 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e18607 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b18608 := hb (x 8 3)
            have b18609 := hb (x 9 2)
            have b18610 := hb (x 10 13)
            have b18611 := hb (x 11 12)
            clear * - r18605 e18606 e18607 b18608 b18609 b18610 b18611 d18592 d18480 d18588
            omega
          have d18612 : (x 10 2 && x 10 13).toNat = 0 := by
            have r18613 := hand2 (x 10 2) (x 10 13)
            have b18614 := hb (x 10 13)
            have b18615 := hb (x 10 2 && x 10 13)
            clear * - r18613 b18614 b18615 d18604
            omega
          have d18616 : (x 12 11).toNat = 1 := by
            have r18617 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18618 := hb (x 8 4)
            have b18619 := hb (x 12 11)
            have b18620 := hb (x 11 1 && x 11 12)
            have b18621 := hb (x 10 2 && x 10 13)
            have b18622 := hb (x 9 3 && x 9 14)
            clear * - r18617 b18618 b18619 b18620 b18621 b18622 d18600 d18612 d18476 d18414
            omega
          have d18623 : (x 12 3).toNat = 1 := by
            have r18624 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
            have b18625 := hb (x 12 3)
            have b18626 := hb (x 12 11)
            clear * - r18624 b18625 b18626 d18616
            omega
          have d18627 : (x 15 12).toNat = 0 := by
            have r18628 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18629 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e18630 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b18631 := hb (x 12 3)
            have b18632 := hb (x 13 2)
            have b18633 := hb (x 14 13)
            have b18634 := hb (x 15 12)
            clear * - r18628 e18629 e18630 b18631 b18632 b18633 b18634 d18623
            omega
          have d18635 : (x 15 1 && x 15 12).toNat = 0 := by
            have r18636 := hand2 (x 15 1) (x 15 12)
            have b18637 := hb (x 15 12)
            have b18638 := hb (x 15 1 && x 15 12)
            clear * - r18636 b18637 b18638 d18627
            omega
          have d18639 : (x 14 13).toNat = 0 := by
            have r18640 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18641 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e18642 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b18643 := hb (x 12 3)
            have b18644 := hb (x 13 2)
            have b18645 := hb (x 14 13)
            have b18646 := hb (x 15 12)
            clear * - r18640 e18641 e18642 b18643 b18644 b18645 b18646 d18627 d18623
            omega
          have d18647 : (x 14 2 && x 14 13).toNat = 0 := by
            have r18648 := hand2 (x 14 2) (x 14 13)
            have b18649 := hb (x 14 13)
            have b18650 := hb (x 14 2 && x 14 13)
            clear * - r18648 b18649 b18650 d18639
            omega
          have d18651 : (x 13 2).toNat = 0 := by
            have r18652 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18653 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e18654 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b18655 := hb (x 12 3)
            have b18656 := hb (x 13 2)
            have b18657 := hb (x 14 13)
            have b18658 := hb (x 15 12)
            clear * - r18652 e18653 e18654 b18655 b18656 b18657 b18658 d18627 d18639 d18623
            omega
          have d18659 : (x 10 1).toNat = 1 := by
            have r18660 := hand1 (x 10 1) (x 10 14)
            have b18661 := hb (x 10 1)
            have b18662 := hb (x 10 1 && x 10 14)
            clear * - r18660 b18661 b18662 d18547
            omega
          have d18663 : (x 11 14).toNat = 0 := by
            have r18664 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18665 := hb (x 10 1)
            have b18666 := hb (x 11 14)
            clear * - r18664 b18665 b18666 d18659
            omega
          have d18667 : (x 11 1 && x 11 14).toNat = 0 := by
            have r18668 := hand2 (x 11 1) (x 11 14)
            have b18669 := hb (x 11 14)
            have b18670 := hb (x 11 1 && x 11 14)
            clear * - r18668 b18669 b18670 d18663
            omega
          have d18671 : (x 11 2).toNat = 0 := by
            have r18672 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
            have b18673 := hb (x 11 2)
            have b18674 := hb (x 11 14)
            clear * - r18672 b18673 b18674 d18663
            omega
          have d18675 : (x 10 2).toNat = 0 := by
            have r18676 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18677 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e18678 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b18679 := hb (x 9 3)
            have b18680 := hb (x 10 2)
            have b18681 := hb (x 11 13)
            have b18682 := hb (x 12 12)
            clear * - r18676 e18677 e18678 b18679 b18680 b18681 b18682 d18519 d18535 d18515
            omega
          have d18683 : (x 12 13).toNat = 1 := by
            have r18684 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18685 := hb (x 10 2)
            have b18686 := hb (x 12 13)
            have b18687 := hb (x 11 1 && x 11 14)
            clear * - r18684 b18685 b18686 b18687 d18667 d18675
            omega
          have d18688 : (x 12 1).toNat = 1 := by
            have r18689 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
            have b18690 := hb (x 12 1)
            have b18691 := hb (x 12 13)
            clear * - r18689 b18690 b18691 d18683
            omega
          have d18692 : (x 13 14).toNat = 0 := by
            have r18693 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18694 := hb (x 12 1)
            have b18695 := hb (x 13 14)
            clear * - r18693 b18694 b18695 d18688
            omega
          have d18696 : (x 13 1 && x 13 14).toNat = 0 := by
            have r18697 := hand2 (x 13 1) (x 13 14)
            have b18698 := hb (x 13 14)
            have b18699 := hb (x 13 1 && x 13 14)
            clear * - r18697 b18698 b18699 d18692
            omega
          have d18700 : (x 12 2).toNat = 1 := by
            have r18701 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18702 := hb (x 12 2)
            have b18703 := hb (x 14 13)
            have b18704 := hb (x 13 1 && x 13 14)
            clear * - r18701 b18702 b18703 b18704 d18639 d18696
            omega
          have d18705 : (x 14 12).toNat = 0 := by
            have r18706 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18707 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e18708 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b18709 := hb (x 11 3)
            have b18710 := hb (x 12 2)
            have b18711 := hb (x 13 13)
            have b18712 := hb (x 14 12)
            clear * - r18706 e18707 e18708 b18709 b18710 b18711 b18712 d18700
            omega
          have d18713 : (x 14 4).toNat = 0 := by
            have r18714 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
            have b18715 := hb (x 14 4)
            have b18716 := hb (x 14 12)
            clear * - r18714 b18715 b18716 d18705
            omega
          have d18717 : (x 14 4 && x 14 14).toNat = 0 := by
            have r18718 := hand1 (x 14 4) (x 14 14)
            have b18719 := hb (x 14 4)
            have b18720 := hb (x 14 4 && x 14 14)
            clear * - r18718 b18719 b18720 d18713
            omega
          have d18721 : (x 13 13).toNat = 0 := by
            have r18722 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18723 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e18724 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b18725 := hb (x 11 3)
            have b18726 := hb (x 12 2)
            have b18727 := hb (x 13 13)
            have b18728 := hb (x 14 12)
            clear * - r18722 e18723 e18724 b18725 b18726 b18727 b18728 d18705 d18700
            omega
          have d18729 : (x 13 5).toNat = 0 := by
            have r18730 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
            have b18731 := hb (x 13 5)
            have b18732 := hb (x 13 13)
            clear * - r18730 b18731 b18732 d18721
            omega
          have d18733 : (x 13 3 && x 13 14).toNat = 0 := by
            have r18734 := hand2 (x 13 3) (x 13 14)
            have b18735 := hb (x 13 14)
            have b18736 := hb (x 13 3 && x 13 14)
            clear * - r18734 b18735 b18736 d18692
            omega
          have d18737 : (x 16 11).toNat = 1 := by
            have r18738 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18739 := hb (x 12 4)
            have b18740 := hb (x 16 11)
            have b18741 := hb (x 15 1 && x 15 12)
            have b18742 := hb (x 14 2 && x 14 13)
            have b18743 := hb (x 13 3 && x 13 14)
            clear * - r18738 b18739 b18740 b18741 b18742 b18743 d18635 d18647 d18733 d18531
            omega
          have d18744 : (x 16 3).toNat = 1 := by
            have r18745 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
            have b18746 := hb (x 16 3)
            have b18747 := hb (x 16 11)
            clear * - r18745 b18746 b18747 d18737
            omega
          have d18748 : (x 19 12).toNat = 0 := by
            have r18749 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18750 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e18751 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b18752 := hb (x 16 3)
            have b18753 := hb (x 17 2)
            have b18754 := hb (x 18 13)
            have b18755 := hb (x 19 12)
            clear * - r18749 e18750 e18751 b18752 b18753 b18754 b18755 d18744
            omega
          have d18756 : (x 18 13).toNat = 0 := by
            have r18757 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18758 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e18759 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b18760 := hb (x 16 3)
            have b18761 := hb (x 17 2)
            have b18762 := hb (x 18 13)
            have b18763 := hb (x 19 12)
            clear * - r18757 e18758 e18759 b18760 b18761 b18762 b18763 d18748 d18744
            omega
          have d18764 : (x 17 2).toNat = 0 := by
            have r18765 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18766 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e18767 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b18768 := hb (x 16 3)
            have b18769 := hb (x 17 2)
            have b18770 := hb (x 18 13)
            have b18771 := hb (x 19 12)
            clear * - r18765 e18766 e18767 b18768 b18769 b18770 b18771 d18748 d18756 d18744
            omega
          have d18772 : (x 13 12).toNat = 0 := by
            have r18773 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18774 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e18775 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b18776 := hb (x 10 3)
            have b18777 := hb (x 11 2)
            have b18778 := hb (x 12 13)
            have b18779 := hb (x 13 12)
            clear * - r18773 e18774 e18775 b18776 b18777 b18778 b18779 d18683 d18671
            omega
          have d18780 : (x 13 4).toNat = 0 := by
            have r18781 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
            have b18782 := hb (x 13 4)
            have b18783 := hb (x 13 12)
            clear * - r18781 b18782 b18783 d18772
            omega
          have d18784 : (x 10 3).toNat = 0 := by
            have r18785 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18786 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e18787 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b18788 := hb (x 10 3)
            have b18789 := hb (x 11 2)
            have b18790 := hb (x 12 13)
            have b18791 := hb (x 13 12)
            clear * - r18785 e18786 e18787 b18788 b18789 b18790 b18791 d18772 d18683 d18671
            omega
          have d18792 : (x 10 3 && x 10 14).toNat = 0 := by
            have r18793 := hand1 (x 10 3) (x 10 14)
            have b18794 := hb (x 10 3)
            have b18795 := hb (x 10 3 && x 10 14)
            clear * - r18793 b18794 b18795 d18784
            omega
          have d18796 : (x 13 11).toNat = 1 := by
            have r18797 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18798 := hb (x 9 4)
            have b18799 := hb (x 13 11)
            have b18800 := hb (x 12 1 && x 12 12)
            have b18801 := hb (x 11 2 && x 11 13)
            have b18802 := hb (x 10 3 && x 10 14)
            clear * - r18797 b18798 b18799 b18800 b18801 b18802 d18527 d18543 d18792 d18492
            omega
          have d18803 : (x 13 3).toNat = 1 := by
            have r18804 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
            have b18805 := hb (x 13 3)
            have b18806 := hb (x 13 11)
            clear * - r18804 b18805 b18806 d18796
            omega
          have d18807 : (x 16 12).toNat = 0 := by
            have r18808 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18809 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e18810 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b18811 := hb (x 13 3)
            have b18812 := hb (x 14 2)
            have b18813 := hb (x 15 13)
            have b18814 := hb (x 16 12)
            clear * - r18808 e18809 e18810 b18811 b18812 b18813 b18814 d18803
            omega
          have d18815 : (x 16 1 && x 16 12).toNat = 0 := by
            have r18816 := hand2 (x 16 1) (x 16 12)
            have b18817 := hb (x 16 12)
            have b18818 := hb (x 16 1 && x 16 12)
            clear * - r18816 b18817 b18818 d18807
            omega
          have d18819 : (x 16 2 && x 16 12).toNat = 0 := by
            have r18820 := hand2 (x 16 2) (x 16 12)
            have b18821 := hb (x 16 12)
            have b18822 := hb (x 16 2 && x 16 12)
            clear * - r18820 b18821 b18822 d18807
            omega
          have d18823 : (x 15 13).toNat = 0 := by
            have r18824 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18825 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e18826 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b18827 := hb (x 13 3)
            have b18828 := hb (x 14 2)
            have b18829 := hb (x 15 13)
            have b18830 := hb (x 16 12)
            clear * - r18824 e18825 e18826 b18827 b18828 b18829 b18830 d18807 d18803
            omega
          have d18831 : (x 15 2 && x 15 13).toNat = 0 := by
            have r18832 := hand2 (x 15 2) (x 15 13)
            have b18833 := hb (x 15 13)
            have b18834 := hb (x 15 2 && x 15 13)
            clear * - r18832 b18833 b18834 d18823
            omega
          have d18835 : (x 15 3 && x 15 13).toNat = 0 := by
            have r18836 := hand2 (x 15 3) (x 15 13)
            have b18837 := hb (x 15 13)
            have b18838 := hb (x 15 3 && x 15 13)
            clear * - r18836 b18837 b18838 d18823
            omega
          have d18839 : (x 14 1 && x 14 14).toNat = 1 := by
            have r18840 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18841 := hb (x 13 2)
            have b18842 := hb (x 15 13)
            have b18843 := hb (x 14 1 && x 14 14)
            clear * - r18840 b18841 b18842 b18843 d18823 d18651
            omega
          have d18844 : (x 14 1).toNat = 1 := by
            have r18845 := hand1 (x 14 1) (x 14 14)
            have b18846 := hb (x 14 1)
            have b18847 := hb (x 14 1 && x 14 14)
            clear * - r18845 b18846 b18847 d18839
            omega
          have d18848 : (x 15 14).toNat = 0 := by
            have r18849 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18850 := hb (x 14 1)
            have b18851 := hb (x 15 14)
            clear * - r18849 b18850 b18851 d18844
            omega
          have d18852 : (x 15 1 && x 15 14).toNat = 0 := by
            have r18853 := hand2 (x 15 1) (x 15 14)
            have b18854 := hb (x 15 14)
            have b18855 := hb (x 15 1 && x 15 14)
            clear * - r18853 b18854 b18855 d18848
            omega
          have d18856 : (x 15 2).toNat = 0 := by
            have r18857 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
            have b18858 := hb (x 15 2)
            have b18859 := hb (x 15 14)
            clear * - r18857 b18858 b18859 d18848
            omega
          have d18860 : (x 14 2).toNat = 0 := by
            have r18861 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18862 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e18863 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b18864 := hb (x 13 3)
            have b18865 := hb (x 14 2)
            have b18866 := hb (x 15 13)
            have b18867 := hb (x 16 12)
            clear * - r18861 e18862 e18863 b18864 b18865 b18866 b18867 d18807 d18823 d18803
            omega
          have d18868 : (x 16 13).toNat = 1 := by
            have r18869 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18870 := hb (x 14 2)
            have b18871 := hb (x 16 13)
            have b18872 := hb (x 15 1 && x 15 14)
            clear * - r18869 b18870 b18871 b18872 d18852 d18860
            omega
          have d18873 : (x 17 12).toNat = 0 := by
            have r18874 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18875 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e18876 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b18877 := hb (x 14 3)
            have b18878 := hb (x 15 2)
            have b18879 := hb (x 16 13)
            have b18880 := hb (x 17 12)
            clear * - r18874 e18875 e18876 b18877 b18878 b18879 b18880 d18868 d18856
            omega
          have d18881 : (x 14 3).toNat = 0 := by
            have r18882 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18883 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e18884 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b18885 := hb (x 14 3)
            have b18886 := hb (x 15 2)
            have b18887 := hb (x 16 13)
            have b18888 := hb (x 17 12)
            clear * - r18882 e18883 e18884 b18885 b18886 b18887 b18888 d18873 d18868 d18856
            omega
          have d18889 : (x 14 3 && x 14 14).toNat = 0 := by
            have r18890 := hand1 (x 14 3) (x 14 14)
            have b18891 := hb (x 14 3)
            have b18892 := hb (x 14 3 && x 14 14)
            clear * - r18890 b18891 b18892 d18881
            omega
          have d18893 : (x 17 11).toNat = 1 := by
            have r18894 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18895 := hb (x 13 4)
            have b18896 := hb (x 17 11)
            have b18897 := hb (x 16 1 && x 16 12)
            have b18898 := hb (x 15 2 && x 15 13)
            have b18899 := hb (x 14 3 && x 14 14)
            clear * - r18894 b18895 b18896 b18897 b18898 b18899 d18815 d18831 d18889 d18780
            omega
          have d18900 : (x 17 3).toNat = 1 := by
            have r18901 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
            have b18902 := hb (x 17 3)
            have b18903 := hb (x 17 11)
            clear * - r18901 b18902 b18903 d18893
            omega
          have d18904 : (x 20 12).toNat = 0 := by
            have r18905 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18906 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e18907 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b18908 := hb (x 17 3)
            have b18909 := hb (x 18 2)
            have b18910 := hb (x 19 13)
            have b18911 := hb (x 20 12)
            clear * - r18905 e18906 e18907 b18908 b18909 b18910 b18911 d18900
            omega
          have d18912 : (x 19 13).toNat = 0 := by
            have r18913 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18914 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e18915 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b18916 := hb (x 17 3)
            have b18917 := hb (x 18 2)
            have b18918 := hb (x 19 13)
            have b18919 := hb (x 20 12)
            clear * - r18913 e18914 e18915 b18916 b18917 b18918 b18919 d18904 d18900
            omega
          have d18920 : (x 18 1 && x 18 14).toNat = 1 := by
            have r18921 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18922 := hb (x 17 2)
            have b18923 := hb (x 19 13)
            have b18924 := hb (x 18 1 && x 18 14)
            clear * - r18921 b18922 b18923 b18924 d18912 d18764
            omega
          have d18925 : (x 18 14).toNat = 1 := by
            have r18926 := hand2 (x 18 1) (x 18 14)
            have b18927 := hb (x 18 14)
            have b18928 := hb (x 18 1 && x 18 14)
            clear * - r18926 b18927 b18928 d18920
            omega
          have d18929 : (x 17 1).toNat = 0 := by
            have r18930 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b18931 := hb (x 17 1)
            have b18932 := hb (x 18 14)
            clear * - r18930 b18931 b18932 d18925
            omega
          have d18933 : (x 17 1 && x 17 11).toNat = 0 := by
            have r18934 := hand1 (x 17 1) (x 17 11)
            have b18935 := hb (x 17 1)
            have b18936 := hb (x 17 1 && x 17 11)
            clear * - r18934 b18935 b18936 d18929
            omega
          have d18937 : (x 18 2).toNat = 0 := by
            have r18938 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e18939 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e18940 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b18941 := hb (x 17 3)
            have b18942 := hb (x 18 2)
            have b18943 := hb (x 19 13)
            have b18944 := hb (x 20 12)
            clear * - r18938 e18939 e18940 b18941 b18942 b18943 b18944 d18904 d18912 d18900
            omega
          have d18945 : (x 18 10).toNat = 0 := by
            have r18946 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
            have b18947 := hb (x 18 2)
            have b18948 := hb (x 18 10)
            clear * - r18946 b18947 b18948 d18937
            omega
          have r18949 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b18950 := hb (x 13 5)
          have b18951 := hb (x 18 10)
          have b18952 := hb (x 17 1 && x 17 11)
          have b18953 := hb (x 16 2 && x 16 12)
          have b18954 := hb (x 15 3 && x 15 13)
          have b18955 := hb (x 14 4 && x 14 14)
          linarith only [r18949, b18950, b18951, b18952, b18953, b18954, b18955, d18945, d18933, d18819, d18835, d18717, d18729]
      · have f18956 : (x 1 1).toNat = 1 := by rw [h17187]; rfl
        have d18957 : (x 2 14).toNat = 0 := by
          have r18958 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b18959 := hb (x 1 1)
          have b18960 := hb (x 2 14)
          clear * - r18958 b18959 b18960 f18956
          omega
        have d18961 : (x 2 1 && x 2 14).toNat = 0 := by
          have r18962 := hand2 (x 2 1) (x 2 14)
          have b18963 := hb (x 2 14)
          have b18964 := hb (x 2 1 && x 2 14)
          clear * - r18962 b18963 b18964 d18957
          omega
        have d18965 : (x 2 6).toNat = 0 := by
          have r18966 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
          have b18967 := hb (x 2 6)
          have b18968 := hb (x 2 14)
          clear * - r18966 b18967 b18968 d18957
          omega
        have d18969 : (x 2 2 && x 2 6).toNat = 0 := by
          have r18970 := hand2 (x 2 2) (x 2 6)
          have b18971 := hb (x 2 6)
          have b18972 := hb (x 2 2 && x 2 6)
          clear * - r18970 b18971 b18972 d18965
          omega
        have d18973 : (x 2 2).toNat = 0 := by
          have r18974 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b18975 := hb (x 2 2)
          have b18976 := hb (x 2 14)
          clear * - r18974 b18975 b18976 d18957
          omega
        have d18977 : (x 3 13).toNat = 1 := by
          have r18978 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b18979 := hb (x 1 2)
          have b18980 := hb (x 3 13)
          have b18981 := hb (x 2 1 && x 2 14)
          clear * - r18978 b18979 b18980 b18981 d18961 g11
          omega
        have d18982 : (x 3 1).toNat = 1 := by
          have r18983 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b18984 := hb (x 3 1)
          have b18985 := hb (x 3 13)
          clear * - r18983 b18984 b18985 d18977
          omega
        have d18986 : (x 4 12).toNat = 0 := by
          have r18987 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e18988 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e18989 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b18990 := hb (x 1 3)
          have b18991 := hb (x 2 2)
          have b18992 := hb (x 3 13)
          have b18993 := hb (x 4 12)
          clear * - r18987 e18988 e18989 b18990 b18991 b18992 b18993 d18977 d18973
          omega
        have d18994 : (x 4 3 && x 4 12).toNat = 0 := by
          have r18995 := hand2 (x 4 3) (x 4 12)
          have b18996 := hb (x 4 12)
          have b18997 := hb (x 4 3 && x 4 12)
          clear * - r18995 b18996 b18997 d18986
          omega
        have d18998 : (x 4 4).toNat = 0 := by
          have r18999 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b19000 := hb (x 4 4)
          have b19001 := hb (x 4 12)
          clear * - r18999 b19000 b19001 d18986
          omega
        have d19002 : (x 1 3).toNat = 0 := by
          have r19003 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19004 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e19005 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b19006 := hb (x 1 3)
          have b19007 := hb (x 2 2)
          have b19008 := hb (x 3 13)
          have b19009 := hb (x 4 12)
          clear * - r19003 e19004 e19005 b19006 b19007 b19008 b19009 d18986 d18977 d18973
          omega
        have d19010 : (x 1 3 && x 1 7).toNat = 0 := by
          have r19011 := hand1 (x 1 3) (x 1 7)
          have b19012 := hb (x 1 3)
          have b19013 := hb (x 1 3 && x 1 7)
          clear * - r19011 b19012 b19013 d19002
          omega
        have r19014 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r19015 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r19016 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19017 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
        have e19018 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
        have e19019 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
        have e19020 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
        have e19021 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
        have e19022 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
        have r19023 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19024 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e19025 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e19026 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e19027 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e19028 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e19029 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r19030 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19031 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e19032 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have r19033 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19034 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e19035 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have r19036 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r19037 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19038 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
        have e19039 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
        have r19040 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r19041 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r19042 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r19043 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r19044 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have r19045 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
        have r19046 := hand1 (x (-4) 8) (x (-4) 12)
        have r19047 := hand1 (x (-5) 9) (x (-5) 13)
        have r19048 := hand2 (x (-7) 8) (x (-7) 13)
        have r19049 := hand1 (x (-8) 9) (x (-8) 14)
        have r19050 := hand2 (x 6 1) (x 6 10)
        have r19051 := hand2 (x 5 2) (x 5 11)
        have r19052 := hand2 (x (-8) 1) (x (-8) 12)
        have r19053 := hand2 (x (-9) 2) (x (-9) 13)
        have r19054 := hand2 (x (-10) 3) (x (-10) 14)
        have b19098 := hb (x 7 1)
        linarith only [r19014, r19015, r19016, e19017, e19018, e19019, e19020, e19021, e19022, r19023, e19024, e19025, e19026, e19027, e19028, e19029, r19030, e19031, e19032, r19033, e19034, e19035, r19036, r19037, e19038, e19039, r19040, r19041, r19042, r19043, r19044, r19045, r19046, r19047, r19048, r19049, r19050, r19051, r19052, r19053, r19054, b19098, g1, g2, g3, g4, g5, g6, g8, g10, d19002, g13, g14, d18973, d18965, d18982, d18998, d18969, d19010, g21, g22, g23, g24, d16781, g28, g29, g30, g31, g32, g33, g47, g48, g49, g50, g51, g52, g53, d18994, g61, g62]
  · have f19135 : (x 0 7).toNat = 1 := by rw [h16793]; rfl
    have d19136 : (x 7 8).toNat = 0 := by
      have r19137 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19138 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e19139 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e19140 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e19141 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e19142 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e19143 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b19144 := hb (x 0 7)
      have b19145 := hb (x 1 6)
      have b19146 := hb (x 2 5)
      have b19147 := hb (x 3 4)
      have b19148 := hb (x 4 11)
      have b19149 := hb (x 5 10)
      have b19150 := hb (x 6 9)
      have b19151 := hb (x 7 8)
      clear * - r19137 e19138 e19139 e19140 e19141 e19142 e19143 b19144 b19145 b19146 b19147 b19148 b19149 b19150 b19151 g19 g18 g14 f19135
      omega
    have d19152 : (x 6 9).toNat = 0 := by
      have r19153 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19154 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e19155 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e19156 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e19157 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e19158 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e19159 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b19160 := hb (x 0 7)
      have b19161 := hb (x 1 6)
      have b19162 := hb (x 2 5)
      have b19163 := hb (x 3 4)
      have b19164 := hb (x 4 11)
      have b19165 := hb (x 5 10)
      have b19166 := hb (x 6 9)
      have b19167 := hb (x 7 8)
      clear * - r19153 e19154 e19155 e19156 e19157 e19158 e19159 b19160 b19161 b19162 b19163 b19164 b19165 b19166 b19167 d19136 g19 g18 g14 f19135
      omega
    have d19168 : (x 5 10).toNat = 0 := by
      have r19169 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19170 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e19171 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e19172 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e19173 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e19174 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e19175 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b19176 := hb (x 0 7)
      have b19177 := hb (x 1 6)
      have b19178 := hb (x 2 5)
      have b19179 := hb (x 3 4)
      have b19180 := hb (x 4 11)
      have b19181 := hb (x 5 10)
      have b19182 := hb (x 6 9)
      have b19183 := hb (x 7 8)
      clear * - r19169 e19170 e19171 e19172 e19173 e19174 e19175 b19176 b19177 b19178 b19179 b19180 b19181 b19182 b19183 d19136 d19152 g19 g18 g14 f19135
      omega
    have d19184 : (x 5 1 && x 5 10).toNat = 0 := by
      have r19185 := hand2 (x 5 1) (x 5 10)
      have b19186 := hb (x 5 10)
      have b19187 := hb (x 5 1 && x 5 10)
      clear * - r19185 b19186 b19187 d19168
      omega
    have d19188 : (x 4 2 && x 4 11).toNat = 1 := by
      have r19189 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19190 := hb (x 0 6)
      have b19191 := hb (x 6 9)
      have b19192 := hb (x 5 1 && x 5 10)
      have b19193 := hb (x 4 2 && x 4 11)
      have b19194 := hb (x 3 3 && x 3 12)
      have b19195 := hb (x 2 4 && x 2 13)
      have b19196 := hb (x 1 5 && x 1 14)
      clear * - r19189 b19190 b19191 b19192 b19193 b19194 b19195 b19196 d19152 d19184 g58 g59 g60 g9
      omega
    have d19197 : (x 4 11).toNat = 1 := by
      have r19198 := hand2 (x 4 2) (x 4 11)
      have b19199 := hb (x 4 11)
      have b19200 := hb (x 4 2 && x 4 11)
      clear * - r19198 b19199 b19200 d19188
      omega
    have r19201 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19202 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e19203 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e19204 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e19205 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e19206 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e19207 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b19208 := hb (x 0 7)
    have b19209 := hb (x 1 6)
    have b19210 := hb (x 2 5)
    have b19211 := hb (x 3 4)
    have b19212 := hb (x 4 11)
    have b19213 := hb (x 5 10)
    have b19214 := hb (x 6 9)
    have b19215 := hb (x 7 8)
    linarith only [r19201, e19202, e19203, e19204, e19205, e19206, e19207, b19208, b19209, b19210, b19211, b19212, b19213, b19214, b19215, d19136, d19152, d19168, d19197, g19, g18, g14, f19135]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b1110 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 7).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 6).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 9).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x 0 4).toNat = 1)
    (g9 : (x 0 6).toNat = 0)
    (g10 : (x 0 8).toNat = 0)
    (g11 : (x 1 2).toNat = 0)
    (g12 : (x 1 4).toNat = 0)
    (g13 : (x 1 5).toNat = 0)
    (g14 : (x 1 6).toNat = 0)
    (g15 : (x 1 8).toNat = 0)
    (g16 : (x 1 10).toNat = 0)
    (g17 : (x 2 4).toNat = 0)
    (g18 : (x 2 5).toNat = 0)
    (g19 : (x 3 4).toNat = 0)
    (g20 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g21 : (x 0 4 && x 0 8).toNat = 0)
    (g22 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g23 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g24 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g25 : (x 2 4 && x 2 8).toNat = 0)
    (g26 : (x 1 5 && x 1 9).toNat = 0)
    (g27 : (x (-1) 7 && x (-1) 11).toNat = 0)
    (g28 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g29 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g30 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g31 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g32 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g33 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g34 : (x 3 8 && x 3 13).toNat = 0)
    (g35 : (x 2 9 && x 2 14).toNat = 0)
    (g36 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g37 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g38 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g39 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g40 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g41 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g42 : (x 4 2 && x 4 8).toNat = 0)
    (g43 : (x 3 3 && x 3 9).toNat = 0)
    (g44 : (x 2 4 && x 2 10).toNat = 0)
    (g45 : (x 1 5 && x 1 11).toNat = 0)
    (g46 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g47 : (x 0 1 && x 0 8).toNat = 0)
    (g48 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g49 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g50 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g51 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g52 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g53 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g54 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g55 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g56 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g57 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g58 : (x 3 3 && x 3 12).toNat = 0)
    (g59 : (x 2 4 && x 2 13).toNat = 0)
    (g60 : (x 1 5 && x 1 14).toNat = 0)
    (g61 : (x 3 4 && x 3 13).toNat = 0)
    (g62 : (x 2 5 && x 2 14).toNat = 0)
    (g63 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g64 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g65 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g66 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g67 : (x 2 4 && x 2 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b1110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67
