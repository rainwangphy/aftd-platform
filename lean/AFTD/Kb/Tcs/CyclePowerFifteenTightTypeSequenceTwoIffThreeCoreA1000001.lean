import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000001

Topic: combinatorics   Node: 3b58ea58a282

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 21 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000001_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-1) 5).toNat = 0)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 9).toNat = 1)
    (g5 : (x 1 2).toNat = 0)
    (g6 : (x 1 10).toNat = 0)
    (g7 : (x 0 1 && x 0 11).toNat = 0)
    (g8 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g9 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g10 : (x 0 2 && x 0 12).toNat = 0)
    (g11 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g12 : (x 2 2 && x 2 12).toNat = 0)
    (g13 : (x 1 3 && x 1 13).toNat = 0)
    (g14 : (x 0 4 && x 0 14).toNat = 0)
    (g15 : (x 0 1 && x 0 12).toNat = 0)
    (g16 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g17 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g18 : (x 2 1 && x 2 12).toNat = 0)
    (g19 : (x 1 2 && x 1 13).toNat = 0)
    (g20 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d14405 : (x 1 8).toNat = 0 := by
    have r14406 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14407 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e14408 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e14409 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e14410 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e14411 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e14412 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b14413 := hb (x (-6) 7)
    have b14414 := hb (x (-5) 6)
    have b14415 := hb (x (-4) 5)
    have b14416 := hb (x (-3) 4)
    have b14417 := hb (x (-2) 11)
    have b14418 := hb (x (-1) 10)
    have b14419 := hb (x 0 9)
    have b14420 := hb (x 1 8)
    clear * - r14406 e14407 e14408 e14409 e14410 e14411 e14412 b14413 b14414 b14415 b14416 b14417 b14418 b14419 b14420 g4 g2 g0
    omega
  have d14421 : (x (-3) 4).toNat = 0 := by
    have r14422 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14423 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e14424 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e14425 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e14426 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e14427 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e14428 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b14429 := hb (x (-6) 7)
    have b14430 := hb (x (-5) 6)
    have b14431 := hb (x (-4) 5)
    have b14432 := hb (x (-3) 4)
    have b14433 := hb (x (-2) 11)
    have b14434 := hb (x (-1) 10)
    have b14435 := hb (x 0 9)
    have b14436 := hb (x 1 8)
    clear * - r14422 e14423 e14424 e14425 e14426 e14427 e14428 b14429 b14430 b14431 b14432 b14433 b14434 b14435 b14436 d14405 g4 g2 g0
    omega
  have d14437 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
    have r14438 := hand1 (x (-3) 4) (x (-3) 14)
    have b14439 := hb (x (-3) 4)
    have b14440 := hb (x (-3) 4 && x (-3) 14)
    clear * - r14438 b14439 b14440 d14421
    omega
  have d14441 : (x (-4) 5).toNat = 1 := by
    have r14442 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14443 := hb (x (-4) 5)
    have b14444 := hb (x 1 10)
    have b14445 := hb (x 0 1 && x 0 11)
    have b14446 := hb (x (-1) 2 && x (-1) 12)
    have b14447 := hb (x (-2) 3 && x (-2) 13)
    have b14448 := hb (x (-3) 4 && x (-3) 14)
    clear * - r14442 b14443 b14444 b14445 b14446 b14447 b14448 g6 g7 g8 g9 d14437
    omega
  have d14449 : (x (-4) 13).toNat = 1 := by
    have r14450 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b14451 := hb (x (-4) 5)
    have b14452 := hb (x (-4) 13)
    clear * - r14450 b14451 b14452 d14441
    omega
  have d14453 : (x (-4) 1).toNat = 1 := by
    have r14454 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b14455 := hb (x (-4) 1)
    have b14456 := hb (x (-4) 13)
    clear * - r14454 b14455 b14456 d14449
    omega
  have d14457 : (x (-3) 14).toNat = 0 := by
    have r14458 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14459 := hb (x (-4) 1)
    have b14460 := hb (x (-3) 14)
    clear * - r14458 b14459 b14460 d14453
    omega
  have d14461 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r14462 := hand2 (x (-3) 1) (x (-3) 14)
    have b14463 := hb (x (-3) 14)
    have b14464 := hb (x (-3) 1 && x (-3) 14)
    clear * - r14462 b14463 b14464 d14457
    omega
  have d14465 : (x (-3) 2).toNat = 0 := by
    have r14466 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b14467 := hb (x (-3) 2)
    have b14468 := hb (x (-3) 14)
    clear * - r14466 b14467 b14468 d14457
    omega
  have d14469 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
    have r14470 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14471 := hb (x (-3) 2)
    have b14472 := hb (x (-1) 13)
    have b14473 := hb (x (-2) 1 && x (-2) 14)
    clear * - r14470 b14471 b14472 b14473 g3 d14465
    omega
  have d14474 : (x (-2) 14).toNat = 1 := by
    have r14475 := hand2 (x (-2) 1) (x (-2) 14)
    have b14476 := hb (x (-2) 14)
    have b14477 := hb (x (-2) 1 && x (-2) 14)
    clear * - r14475 b14476 b14477 d14469
    omega
  have d14478 : (x (-3) 1).toNat = 0 := by
    have r14479 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14480 := hb (x (-3) 1)
    have b14481 := hb (x (-2) 14)
    clear * - r14479 b14480 b14481 d14474
    omega
  have d14482 : (x (-3) 13).toNat = 0 := by
    have r14483 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b14484 := hb (x (-3) 1)
    have b14485 := hb (x (-3) 13)
    clear * - r14483 b14484 b14485 d14478
    omega
  have d14486 : (x (-3) 5).toNat = 0 := by
    have r14487 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b14488 := hb (x (-3) 5)
    have b14489 := hb (x (-3) 13)
    clear * - r14487 b14488 b14489 d14482
    omega
  have d14490 : (x 1 11).toNat = 1 := by
    have r14491 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14492 := hb (x (-3) 4)
    have b14493 := hb (x 1 11)
    have b14494 := hb (x 0 1 && x 0 12)
    have b14495 := hb (x (-1) 2 && x (-1) 13)
    have b14496 := hb (x (-2) 3 && x (-2) 14)
    clear * - r14491 b14492 b14493 b14494 b14495 b14496 g15 g16 g17 d14421
    omega
  have d14497 : (x 1 3).toNat = 1 := by
    have r14498 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b14499 := hb (x 1 3)
    have b14500 := hb (x 1 11)
    clear * - r14498 b14499 b14500 d14490
    omega
  have d14501 : (x 4 12).toNat = 0 := by
    have r14502 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14503 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e14504 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b14505 := hb (x 1 3)
    have b14506 := hb (x 2 2)
    have b14507 := hb (x 3 13)
    have b14508 := hb (x 4 12)
    clear * - r14502 e14503 e14504 b14505 b14506 b14507 b14508 d14497
    omega
  have d14509 : (x 3 13).toNat = 0 := by
    have r14510 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14511 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e14512 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b14513 := hb (x 1 3)
    have b14514 := hb (x 2 2)
    have b14515 := hb (x 3 13)
    have b14516 := hb (x 4 12)
    clear * - r14510 e14511 e14512 b14513 b14514 b14515 b14516 d14501 d14497
    omega
  have d14517 : (x 2 1 && x 2 14).toNat = 1 := by
    have r14518 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14519 := hb (x 1 2)
    have b14520 := hb (x 3 13)
    have b14521 := hb (x 2 1 && x 2 14)
    clear * - r14518 b14519 b14520 b14521 d14509 g5
    omega
  have d14522 : (x 2 14).toNat = 1 := by
    have r14523 := hand2 (x 2 1) (x 2 14)
    have b14524 := hb (x 2 14)
    have b14525 := hb (x 2 1 && x 2 14)
    clear * - r14523 b14524 b14525 d14517
    omega
  have d14526 : (x 1 1).toNat = 0 := by
    have r14527 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14528 := hb (x 1 1)
    have b14529 := hb (x 2 14)
    clear * - r14527 b14528 b14529 d14522
    omega
  have d14530 : (x 1 1 && x 1 11).toNat = 0 := by
    have r14531 := hand1 (x 1 1) (x 1 11)
    have b14532 := hb (x 1 1)
    have b14533 := hb (x 1 1 && x 1 11)
    clear * - r14531 b14532 b14533 d14526
    omega
  have d14534 : (x 2 1).toNat = 1 := by
    have r14535 := hand1 (x 2 1) (x 2 14)
    have b14536 := hb (x 2 1)
    have b14537 := hb (x 2 1 && x 2 14)
    clear * - r14535 b14536 b14537 d14517
    omega
  have d14538 : (x 3 14).toNat = 0 := by
    have r14539 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14540 := hb (x 2 1)
    have b14541 := hb (x 3 14)
    clear * - r14539 b14540 b14541 d14534
    omega
  have d14542 : (x 3 2).toNat = 0 := by
    have r14543 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b14544 := hb (x 3 2)
    have b14545 := hb (x 3 14)
    clear * - r14543 b14544 b14545 d14538
    omega
  have d14546 : (x 2 2).toNat = 0 := by
    have r14547 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14548 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e14549 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b14550 := hb (x 1 3)
    have b14551 := hb (x 2 2)
    have b14552 := hb (x 3 13)
    have b14553 := hb (x 4 12)
    clear * - r14547 e14548 e14549 b14550 b14551 b14552 b14553 d14501 d14509 d14497
    omega
  have d14554 : (x 2 10).toNat = 0 := by
    have r14555 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
    have b14556 := hb (x 2 2)
    have b14557 := hb (x 2 10)
    clear * - r14555 b14556 b14557 d14546
    omega
  have d14558 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
    have r14559 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14560 := hb (x (-3) 5)
    have b14561 := hb (x 2 10)
    have b14562 := hb (x 1 1 && x 1 11)
    have b14563 := hb (x 0 2 && x 0 12)
    have b14564 := hb (x (-1) 3 && x (-1) 13)
    have b14565 := hb (x (-2) 4 && x (-2) 14)
    clear * - r14559 b14560 b14561 b14562 b14563 b14564 b14565 d14554 d14530 g10 g11 d14486
    omega
  have d14566 : (x (-2) 4).toNat = 1 := by
    have r14567 := hand1 (x (-2) 4) (x (-2) 14)
    have b14568 := hb (x (-2) 4)
    have b14569 := hb (x (-2) 4 && x (-2) 14)
    clear * - r14567 b14568 b14569 d14558
    omega
  have d14570 : (x (-2) 12).toNat = 1 := by
    have r14571 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b14572 := hb (x (-2) 4)
    have b14573 := hb (x (-2) 12)
    clear * - r14571 b14572 b14573 d14566
    omega
  have d14574 : (x (-4) 2).toNat = 0 := by
    have r14575 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14576 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e14577 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b14578 := hb (x (-5) 3)
    have b14579 := hb (x (-4) 2)
    have b14580 := hb (x (-3) 13)
    have b14581 := hb (x (-2) 12)
    clear * - r14575 e14576 e14577 b14578 b14579 b14580 b14581 d14570 d14482
    omega
  have d14582 : (x (-2) 13).toNat = 1 := by
    have r14583 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14584 := hb (x (-4) 2)
    have b14585 := hb (x (-2) 13)
    have b14586 := hb (x (-3) 1 && x (-3) 14)
    clear * - r14583 b14584 b14585 b14586 d14461 d14574
    omega
  have d14587 : (x (-1) 12).toNat = 0 := by
    have r14588 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14589 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e14590 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b14591 := hb (x (-4) 3)
    have b14592 := hb (x (-3) 2)
    have b14593 := hb (x (-2) 13)
    have b14594 := hb (x (-1) 12)
    clear * - r14588 e14589 e14590 b14591 b14592 b14593 b14594 d14582 d14465
    omega
  have d14595 : (x (-1) 4).toNat = 0 := by
    have r14596 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b14597 := hb (x (-1) 4)
    have b14598 := hb (x (-1) 12)
    clear * - r14596 b14597 b14598 d14587
    omega
  have d14599 : (x 3 11).toNat = 1 := by
    have r14600 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14601 := hb (x (-1) 4)
    have b14602 := hb (x 3 11)
    have b14603 := hb (x 2 1 && x 2 12)
    have b14604 := hb (x 1 2 && x 1 13)
    have b14605 := hb (x 0 3 && x 0 14)
    clear * - r14600 b14601 b14602 b14603 b14604 b14605 g18 g19 g20 d14595
    omega
  have d14606 : (x 3 3).toNat = 1 := by
    have r14607 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b14608 := hb (x 3 3)
    have b14609 := hb (x 3 11)
    clear * - r14607 b14608 b14609 d14599
    omega
  have d14610 : (x 6 12).toNat = 0 := by
    have r14611 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14612 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e14613 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b14614 := hb (x 3 3)
    have b14615 := hb (x 4 2)
    have b14616 := hb (x 5 13)
    have b14617 := hb (x 6 12)
    clear * - r14611 e14612 e14613 b14614 b14615 b14616 b14617 d14606
    omega
  have d14618 : (x 5 13).toNat = 0 := by
    have r14619 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14620 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e14621 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b14622 := hb (x 3 3)
    have b14623 := hb (x 4 2)
    have b14624 := hb (x 5 13)
    have b14625 := hb (x 6 12)
    clear * - r14619 e14620 e14621 b14622 b14623 b14624 b14625 d14610 d14606
    omega
  have d14626 : (x 4 1 && x 4 14).toNat = 1 := by
    have r14627 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14628 := hb (x 3 2)
    have b14629 := hb (x 5 13)
    have b14630 := hb (x 4 1 && x 4 14)
    clear * - r14627 b14628 b14629 b14630 d14618 d14542
    omega
  have d14631 : (x 4 14).toNat = 1 := by
    have r14632 := hand2 (x 4 1) (x 4 14)
    have b14633 := hb (x 4 14)
    have b14634 := hb (x 4 1 && x 4 14)
    clear * - r14632 b14633 b14634 d14626
    omega
  have d14635 : (x 3 1).toNat = 0 := by
    have r14636 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14637 := hb (x 3 1)
    have b14638 := hb (x 4 14)
    clear * - r14636 b14637 b14638 d14631
    omega
  have d14639 : (x 3 1 && x 3 11).toNat = 0 := by
    have r14640 := hand1 (x 3 1) (x 3 11)
    have b14641 := hb (x 3 1)
    have b14642 := hb (x 3 1 && x 3 11)
    clear * - r14640 b14641 b14642 d14635
    omega
  have d14643 : (x 4 10).toNat = 1 := by
    have r14644 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14645 := hb (x (-1) 5)
    have b14646 := hb (x 4 10)
    have b14647 := hb (x 3 1 && x 3 11)
    have b14648 := hb (x 2 2 && x 2 12)
    have b14649 := hb (x 1 3 && x 1 13)
    have b14650 := hb (x 0 4 && x 0 14)
    clear * - r14644 b14645 b14646 b14647 b14648 b14649 b14650 d14639 g12 g13 g14 g1
    omega
  have d14651 : (x 4 2).toNat = 1 := by
    have r14652 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b14653 := hb (x 4 2)
    have b14654 := hb (x 4 10)
    clear * - r14652 b14653 b14654 d14643
    omega
  have r14655 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e14656 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
  have e14657 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
  have b14658 := hb (x 3 3)
  have b14659 := hb (x 4 2)
  have b14660 := hb (x 5 13)
  have b14661 := hb (x 6 12)
  linarith only [r14655, e14656, e14657, b14658, b14659, b14660, b14661, d14610, d14618, d14651, d14606]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000001 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-1) 5).toNat = 0)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 9).toNat = 1)
    (g5 : (x 1 2).toNat = 0)
    (g6 : (x 1 10).toNat = 0)
    (g7 : (x 0 1 && x 0 11).toNat = 0)
    (g8 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g9 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g10 : (x 0 2 && x 0 12).toNat = 0)
    (g11 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g12 : (x 2 2 && x 2 12).toNat = 0)
    (g13 : (x 1 3 && x 1 13).toNat = 0)
    (g14 : (x 0 4 && x 0 14).toNat = 0)
    (g15 : (x 0 1 && x 0 12).toNat = 0)
    (g16 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g17 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g18 : (x 2 1 && x 2 12).toNat = 0)
    (g19 : (x 1 2 && x 1 13).toNat = 0)
    (g20 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1000001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20
