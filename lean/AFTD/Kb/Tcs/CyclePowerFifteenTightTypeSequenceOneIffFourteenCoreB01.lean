import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b01

Topic: combinatorics   Node: c5f5a1879c0c

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 33 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b01_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-3) 13).toNat = 0)
    (g3 : (x (-2) 14).toNat = 1)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 13).toNat = 0)
    (g7 : (x 0 2).toNat = 0)
    (g8 : (x 0 4).toNat = 0)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 7).toNat = 1)
    (g11 : (x 0 9).toNat = 0)
    (g12 : (x 0 10).toNat = 0)
    (g13 : (x 0 12).toNat = 0)
    (g14 : (x 0 13).toNat = 0)
    (g15 : (x 0 14).toNat = 1)
    (g16 : (x 0 8 && x 0 12).toNat = 0)
    (g17 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g18 : (x 0 9 && x 0 14).toNat = 0)
    (g19 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g20 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g21 : (x 0 5 && x 0 14).toNat = 0)
    (g22 : (x 0 2 && x 0 12).toNat = 0)
    (g23 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g24 : (x 0 4 && x 0 14).toNat = 0)
    (g25 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g26 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g27 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g28 : (x 0 1 && x 0 12).toNat = 0)
    (g29 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g30 : (x 0 2 && x 0 13).toNat = 0)
    (g31 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g32 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d15405 : (x 7 8).toNat = 0 := by
    have r15406 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e15407 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15408 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15409 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15410 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15411 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15412 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15413 := hb (x 0 7)
    have b15414 := hb (x 1 6)
    have b15415 := hb (x 2 5)
    have b15416 := hb (x 3 4)
    have b15417 := hb (x 4 11)
    have b15418 := hb (x 5 10)
    have b15419 := hb (x 6 9)
    have b15420 := hb (x 7 8)
    clear * - r15406 e15407 e15408 e15409 e15410 e15411 e15412 b15413 b15414 b15415 b15416 b15417 b15418 b15419 b15420 g10
    omega
  have d15421 : (x 7 1 && x 7 8).toNat = 0 := by
    have r15422 := hand2 (x 7 1) (x 7 8)
    have b15423 := hb (x 7 8)
    have b15424 := hb (x 7 1 && x 7 8)
    clear * - r15422 b15423 b15424 d15405
    omega
  have d15425 : (x 7 5 && x 7 8).toNat = 0 := by
    have r15426 := hand2 (x 7 5) (x 7 8)
    have b15427 := hb (x 7 8)
    have b15428 := hb (x 7 5 && x 7 8)
    clear * - r15426 b15427 b15428 d15405
    omega
  have d15429 : (x 6 9).toNat = 0 := by
    have r15430 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e15431 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15432 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15433 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15434 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15435 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15436 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15437 := hb (x 0 7)
    have b15438 := hb (x 1 6)
    have b15439 := hb (x 2 5)
    have b15440 := hb (x 3 4)
    have b15441 := hb (x 4 11)
    have b15442 := hb (x 5 10)
    have b15443 := hb (x 6 9)
    have b15444 := hb (x 7 8)
    clear * - r15430 e15431 e15432 e15433 e15434 e15435 e15436 b15437 b15438 b15439 b15440 b15441 b15442 b15443 b15444 d15405 g10
    omega
  have d15445 : (x 6 2 && x 6 9).toNat = 0 := by
    have r15446 := hand2 (x 6 2) (x 6 9)
    have b15447 := hb (x 6 9)
    have b15448 := hb (x 6 2 && x 6 9)
    clear * - r15446 b15447 b15448 d15429
    omega
  have d15449 : (x 6 6 && x 6 9).toNat = 0 := by
    have r15450 := hand2 (x 6 6) (x 6 9)
    have b15451 := hb (x 6 9)
    have b15452 := hb (x 6 6 && x 6 9)
    clear * - r15450 b15451 b15452 d15429
    omega
  have d15453 : (x 5 10).toNat = 0 := by
    have r15454 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e15455 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15456 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15457 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15458 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15459 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15460 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15461 := hb (x 0 7)
    have b15462 := hb (x 1 6)
    have b15463 := hb (x 2 5)
    have b15464 := hb (x 3 4)
    have b15465 := hb (x 4 11)
    have b15466 := hb (x 5 10)
    have b15467 := hb (x 6 9)
    have b15468 := hb (x 7 8)
    clear * - r15454 e15455 e15456 e15457 e15458 e15459 e15460 b15461 b15462 b15463 b15464 b15465 b15466 b15467 b15468 d15405 d15429 g10
    omega
  have d15469 : (x 5 1 && x 5 10).toNat = 0 := by
    have r15470 := hand2 (x 5 1) (x 5 10)
    have b15471 := hb (x 5 10)
    have b15472 := hb (x 5 1 && x 5 10)
    clear * - r15470 b15471 b15472 d15453
    omega
  have d15473 : (x 5 3 && x 5 10).toNat = 0 := by
    have r15474 := hand2 (x 5 3) (x 5 10)
    have b15475 := hb (x 5 10)
    have b15476 := hb (x 5 3 && x 5 10)
    clear * - r15474 b15475 b15476 d15453
    omega
  have d15477 : (x 5 7 && x 5 10).toNat = 0 := by
    have r15478 := hand2 (x 5 7) (x 5 10)
    have b15479 := hb (x 5 10)
    have b15480 := hb (x 5 7 && x 5 10)
    clear * - r15478 b15479 b15480 d15453
    omega
  have d15481 : (x 4 11).toNat = 0 := by
    have r15482 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e15483 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15484 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15485 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15486 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15487 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15488 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15489 := hb (x 0 7)
    have b15490 := hb (x 1 6)
    have b15491 := hb (x 2 5)
    have b15492 := hb (x 3 4)
    have b15493 := hb (x 4 11)
    have b15494 := hb (x 5 10)
    have b15495 := hb (x 6 9)
    have b15496 := hb (x 7 8)
    clear * - r15482 e15483 e15484 e15485 e15486 e15487 e15488 b15489 b15490 b15491 b15492 b15493 b15494 b15495 b15496 d15405 d15429 d15453 g10
    omega
  have d15497 : (x 4 1 && x 4 11).toNat = 0 := by
    have r15498 := hand2 (x 4 1) (x 4 11)
    have b15499 := hb (x 4 11)
    have b15500 := hb (x 4 1 && x 4 11)
    clear * - r15498 b15499 b15500 d15481
    omega
  have d15501 : (x 4 2 && x 4 11).toNat = 0 := by
    have r15502 := hand2 (x 4 2) (x 4 11)
    have b15503 := hb (x 4 11)
    have b15504 := hb (x 4 2 && x 4 11)
    clear * - r15502 b15503 b15504 d15481
    omega
  have d15505 : (x 4 4 && x 4 11).toNat = 0 := by
    have r15506 := hand2 (x 4 4) (x 4 11)
    have b15507 := hb (x 4 11)
    have b15508 := hb (x 4 4 && x 4 11)
    clear * - r15506 b15507 b15508 d15481
    omega
  have d15509 : (x 4 8 && x 4 11).toNat = 0 := by
    have r15510 := hand2 (x 4 8) (x 4 11)
    have b15511 := hb (x 4 11)
    have b15512 := hb (x 4 8 && x 4 11)
    clear * - r15510 b15511 b15512 d15481
    omega
  have d15513 : (x 3 4).toNat = 0 := by
    have r15514 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e15515 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15516 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15517 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15518 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15519 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15520 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15521 := hb (x 0 7)
    have b15522 := hb (x 1 6)
    have b15523 := hb (x 2 5)
    have b15524 := hb (x 3 4)
    have b15525 := hb (x 4 11)
    have b15526 := hb (x 5 10)
    have b15527 := hb (x 6 9)
    have b15528 := hb (x 7 8)
    clear * - r15514 e15515 e15516 e15517 e15518 e15519 e15520 b15521 b15522 b15523 b15524 b15525 b15526 b15527 b15528 d15405 d15429 d15453 d15481 g10
    omega
  have d15529 : (x 3 4 && x 3 14).toNat = 0 := by
    have r15530 := hand1 (x 3 4) (x 3 14)
    have b15531 := hb (x 3 4)
    have b15532 := hb (x 3 4 && x 3 14)
    clear * - r15530 b15531 b15532 d15513
    omega
  have d15533 : (x 3 4 && x 3 13).toNat = 0 := by
    have r15534 := hand1 (x 3 4) (x 3 13)
    have b15535 := hb (x 3 4)
    have b15536 := hb (x 3 4 && x 3 13)
    clear * - r15534 b15535 b15536 d15513
    omega
  have d15537 : (x 2 5).toNat = 0 := by
    have r15538 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e15539 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15540 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15541 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15542 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15543 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15544 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15545 := hb (x 0 7)
    have b15546 := hb (x 1 6)
    have b15547 := hb (x 2 5)
    have b15548 := hb (x 3 4)
    have b15549 := hb (x 4 11)
    have b15550 := hb (x 5 10)
    have b15551 := hb (x 6 9)
    have b15552 := hb (x 7 8)
    clear * - r15538 e15539 e15540 e15541 e15542 e15543 e15544 b15545 b15546 b15547 b15548 b15549 b15550 b15551 b15552 d15405 d15429 d15453 d15481 d15513 g10
    omega
  have d15553 : (x 2 5 && x 2 14).toNat = 0 := by
    have r15554 := hand1 (x 2 5) (x 2 14)
    have b15555 := hb (x 2 5)
    have b15556 := hb (x 2 5 && x 2 14)
    clear * - r15554 b15555 b15556 d15537
    omega
  have d15557 : (x 1 6).toNat = 0 := by
    have r15558 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e15559 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15560 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15561 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15562 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15563 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15564 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15565 := hb (x 0 7)
    have b15566 := hb (x 1 6)
    have b15567 := hb (x 2 5)
    have b15568 := hb (x 3 4)
    have b15569 := hb (x 4 11)
    have b15570 := hb (x 5 10)
    have b15571 := hb (x 6 9)
    have b15572 := hb (x 7 8)
    clear * - r15558 e15559 e15560 e15561 e15562 e15563 e15564 b15565 b15566 b15567 b15568 b15569 b15570 b15571 b15572 d15405 d15429 d15453 d15481 d15513 d15537 g10
    omega
  cases h15573 : x 0 3
  · have f15574 : (x 0 3).toNat = 0 := by rw [h15573]; rfl
    have d15575 : (x 0 3 && x 0 14).toNat = 0 := by
      have r15576 := hand1 (x 0 3) (x 0 14)
      have b15577 := hb (x 0 3)
      have b15578 := hb (x 0 3 && x 0 14)
      clear * - r15576 b15577 b15578 f15574
      omega
    have d15579 : (x 0 11).toNat = 0 := by
      have r15580 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
      have b15581 := hb (x 0 3)
      have b15582 := hb (x 0 11)
      clear * - r15580 b15581 b15582 f15574
      omega
    cases h15583 : x 0 6
    · have f15584 : (x 0 6).toNat = 0 := by rw [h15583]; rfl
      cases h15585 : x 0 8
      · have f15586 : (x 0 8).toNat = 0 := by rw [h15585]; rfl
        have d15587 : (x 0 8 && x 0 14).toNat = 0 := by
          have r15588 := hand1 (x 0 8) (x 0 14)
          have b15589 := hb (x 0 8)
          have b15590 := hb (x 0 8 && x 0 14)
          clear * - r15588 b15589 b15590 f15586
          omega
        cases h15591 : x 1 1
        · have f15592 : (x 1 1).toNat = 0 := by rw [h15591]; rfl
          have d15593 : (x 1 1 && x 1 14).toNat = 0 := by
            have r15594 := hand1 (x 1 1) (x 1 14)
            have b15595 := hb (x 1 1)
            have b15596 := hb (x 1 1 && x 1 14)
            clear * - r15594 b15595 b15596 f15592
            omega
          have d15597 : (x 1 1 && x 1 12).toNat = 0 := by
            have r15598 := hand1 (x 1 1) (x 1 12)
            have b15599 := hb (x 1 1)
            have b15600 := hb (x 1 1 && x 1 12)
            clear * - r15598 b15599 b15600 f15592
            omega
          have d15601 : (x 1 13).toNat = 0 := by
            have r15602 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
            have b15603 := hb (x 1 1)
            have b15604 := hb (x 1 13)
            clear * - r15602 b15603 b15604 f15592
            omega
          have d15605 : (x 1 2 && x 1 13).toNat = 0 := by
            have r15606 := hand2 (x 1 2) (x 1 13)
            have b15607 := hb (x 1 13)
            have b15608 := hb (x 1 2 && x 1 13)
            clear * - r15606 b15607 b15608 d15601
            omega
          have d15609 : (x 2 13).toNat = 1 := by
            have r15610 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := hcov13 2
            have b15611 := hb (x 0 2)
            have b15612 := hb (x 2 13)
            have b15613 := hb (x 1 1 && x 1 14)
            clear * - r15610 b15611 b15612 b15613 d15593 g7
            omega
          have d15614 : (x 2 1).toNat = 1 := by
            have r15615 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
            have b15616 := hb (x 2 1)
            have b15617 := hb (x 2 13)
            clear * - r15615 b15616 b15617 d15609
            omega
          have d15618 : (x 3 14).toNat = 0 := by
            have r15619 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
            have b15620 := hb (x 2 1)
            have b15621 := hb (x 3 14)
            clear * - r15619 b15620 b15621 d15614
            omega
          have d15622 : (x 3 1 && x 3 14).toNat = 0 := by
            have r15623 := hand2 (x 3 1) (x 3 14)
            have b15624 := hb (x 3 14)
            have b15625 := hb (x 3 1 && x 3 14)
            clear * - r15623 b15624 b15625 d15618
            omega
          have d15626 : (x 3 2).toNat = 0 := by
            have r15627 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b15628 := hb (x 3 2)
            have b15629 := hb (x 3 14)
            clear * - r15627 b15628 b15629 d15618
            omega
          have d15630 : (x 3 2 && x 3 13).toNat = 0 := by
            have r15631 := hand1 (x 3 2) (x 3 13)
            have b15632 := hb (x 3 2)
            have b15633 := hb (x 3 2 && x 3 13)
            clear * - r15631 b15632 b15633 d15626
            omega
          have d15634 : (x (-1) 2).toNat = 1 := by
            have r15635 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
            have b15636 := hb (x (-1) 2)
            have b15637 := hb (x 1 13)
            have b15638 := hb (x 0 1 && x 0 14)
            clear * - r15635 b15636 b15637 b15638 d15601 g32
            omega
          have d15639 : (x (-1) 14).toNat = 1 := by
            have r15640 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
            have b15641 := hb (x (-1) 2)
            have b15642 := hb (x (-1) 14)
            clear * - r15640 b15641 b15642 d15634
            omega
          have d15643 : (x (-2) 1).toNat = 0 := by
            have r15644 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
            have b15645 := hb (x (-2) 1)
            have b15646 := hb (x (-1) 14)
            clear * - r15644 b15645 b15646 d15639
            omega
          have d15647 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r15648 := hand1 (x (-2) 1) (x (-2) 14)
            have b15649 := hb (x (-2) 1)
            have b15650 := hb (x (-2) 1 && x (-2) 14)
            clear * - r15648 b15649 b15650 d15643
            omega
          have d15651 : (x (-2) 13).toNat = 0 := by
            have r15652 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b15653 := hb (x (-2) 1)
            have b15654 := hb (x (-2) 13)
            clear * - r15652 b15653 b15654 d15643
            omega
          have d15655 : (x (-3) 2).toNat = 1 := by
            have r15656 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
            have b15657 := hb (x (-3) 2)
            have b15658 := hb (x (-1) 13)
            have b15659 := hb (x (-2) 1 && x (-2) 14)
            clear * - r15656 b15657 b15658 b15659 g6 d15647
            omega
          have d15660 : (x (-3) 14).toNat = 1 := by
            have r15661 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b15662 := hb (x (-3) 2)
            have b15663 := hb (x (-3) 14)
            clear * - r15661 b15662 b15663 d15655
            omega
          have d15664 : (x (-4) 1).toNat = 0 := by
            have r15665 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
            have b15666 := hb (x (-4) 1)
            have b15667 := hb (x (-3) 14)
            clear * - r15665 b15666 b15667 d15660
            omega
          have d15668 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
            have r15669 := hand1 (x (-4) 1) (x (-4) 14)
            have b15670 := hb (x (-4) 1)
            have b15671 := hb (x (-4) 1 && x (-4) 14)
            clear * - r15669 b15670 b15671 d15664
            omega
          have d15672 : (x (-4) 13).toNat = 0 := by
            have r15673 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b15674 := hb (x (-4) 1)
            have b15675 := hb (x (-4) 13)
            clear * - r15673 b15674 b15675 d15664
            omega
          have d15676 : (x (-4) 2).toNat = 1 := by
            have r15677 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
            have b15678 := hb (x (-4) 2)
            have b15679 := hb (x (-2) 13)
            have b15680 := hb (x (-3) 1 && x (-3) 14)
            clear * - r15677 b15678 b15679 b15680 d15651 g31
            omega
          have d15681 : (x (-5) 2).toNat = 1 := by
            have r15682 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
            have b15683 := hb (x (-5) 2)
            have b15684 := hb (x (-3) 13)
            have b15685 := hb (x (-4) 1 && x (-4) 14)
            clear * - r15682 b15683 b15684 b15685 g2 d15668
            omega
          have d15686 : (x 1 12).toNat = 0 := by
            have r15687 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
            have e15688 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e15689 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b15690 := hb (x (-2) 3)
            have b15691 := hb (x (-1) 2)
            have b15692 := hb (x 0 13)
            have b15693 := hb (x 1 12)
            clear * - r15687 e15688 e15689 b15690 b15691 b15692 b15693 g14 d15634
            omega
          have d15694 : (x 1 4).toNat = 0 := by
            have r15695 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
            have b15696 := hb (x 1 4)
            have b15697 := hb (x 1 12)
            clear * - r15695 b15696 b15697 d15686
            omega
          have d15698 : (x (-2) 3).toNat = 0 := by
            have r15699 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
            have e15700 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e15701 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b15702 := hb (x (-2) 3)
            have b15703 := hb (x (-1) 2)
            have b15704 := hb (x 0 13)
            have b15705 := hb (x 1 12)
            clear * - r15699 e15700 e15701 b15702 b15703 b15704 b15705 d15686 g14 d15634
            omega
          have d15706 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
            have r15707 := hand1 (x (-2) 3) (x (-2) 14)
            have b15708 := hb (x (-2) 3)
            have b15709 := hb (x (-2) 3 && x (-2) 14)
            clear * - r15707 b15708 b15709 d15698
            omega
          have d15710 : (x (-1) 12).toNat = 0 := by
            have r15711 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
            have e15712 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e15713 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b15714 := hb (x (-4) 3)
            have b15715 := hb (x (-3) 2)
            have b15716 := hb (x (-2) 13)
            have b15717 := hb (x (-1) 12)
            clear * - r15711 e15712 e15713 b15714 b15715 b15716 b15717 d15651 d15655
            omega
          have d15718 : (x (-1) 4).toNat = 0 := by
            have r15719 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b15720 := hb (x (-1) 4)
            have b15721 := hb (x (-1) 12)
            clear * - r15719 b15720 b15721 d15710
            omega
          have d15722 : (x (-2) 12).toNat = 0 := by
            have r15723 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
            have e15724 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e15725 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b15726 := hb (x (-5) 3)
            have b15727 := hb (x (-4) 2)
            have b15728 := hb (x (-3) 13)
            have b15729 := hb (x (-2) 12)
            clear * - r15723 e15724 e15725 b15726 b15727 b15728 b15729 g2 d15676
            omega
          have d15730 : (x (-2) 4).toNat = 0 := by
            have r15731 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
            have b15732 := hb (x (-2) 4)
            have b15733 := hb (x (-2) 12)
            clear * - r15731 b15732 b15733 d15722
            omega
          have d15734 : (x (-3) 12).toNat = 0 := by
            have r15735 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
            have e15736 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e15737 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b15738 := hb (x (-6) 3)
            have b15739 := hb (x (-5) 2)
            have b15740 := hb (x (-4) 13)
            have b15741 := hb (x (-3) 12)
            clear * - r15735 e15736 e15737 b15738 b15739 b15740 b15741 d15672 d15681
            omega
          have d15742 : (x (-3) 4).toNat = 0 := by
            have r15743 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have b15744 := hb (x (-3) 4)
            have b15745 := hb (x (-3) 12)
            clear * - r15743 b15744 b15745 d15734
            omega
          have d15746 : (x 1 11).toNat = 1 := by
            have r15747 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
            have b15748 := hb (x (-3) 4)
            have b15749 := hb (x 1 11)
            have b15750 := hb (x 0 1 && x 0 12)
            have b15751 := hb (x (-1) 2 && x (-1) 13)
            have b15752 := hb (x (-2) 3 && x (-2) 14)
            clear * - r15747 b15748 b15749 b15750 b15751 b15752 g28 g29 d15706 d15742
            omega
          have d15753 : (x 1 3).toNat = 1 := by
            have r15754 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
            have b15755 := hb (x 1 3)
            have b15756 := hb (x 1 11)
            clear * - r15754 b15755 b15756 d15746
            omega
          have d15757 : (x 4 12).toNat = 0 := by
            have r15758 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e15759 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e15760 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b15761 := hb (x 1 3)
            have b15762 := hb (x 2 2)
            have b15763 := hb (x 3 13)
            have b15764 := hb (x 4 12)
            clear * - r15758 e15759 e15760 b15761 b15762 b15763 b15764 d15753
            omega
          have d15765 : (x 4 1 && x 4 12).toNat = 0 := by
            have r15766 := hand2 (x 4 1) (x 4 12)
            have b15767 := hb (x 4 12)
            have b15768 := hb (x 4 1 && x 4 12)
            clear * - r15766 b15767 b15768 d15757
            omega
          have d15769 : (x 4 4).toNat = 0 := by
            have r15770 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b15771 := hb (x 4 4)
            have b15772 := hb (x 4 12)
            clear * - r15770 b15771 b15772 d15757
            omega
          have d15773 : (x 3 13).toNat = 0 := by
            have r15774 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e15775 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e15776 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b15777 := hb (x 1 3)
            have b15778 := hb (x 2 2)
            have b15779 := hb (x 3 13)
            have b15780 := hb (x 4 12)
            clear * - r15774 e15775 e15776 b15777 b15778 b15779 b15780 d15757 d15753
            omega
          have d15781 : (x 2 2).toNat = 0 := by
            have r15782 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e15783 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e15784 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b15785 := hb (x 1 3)
            have b15786 := hb (x 2 2)
            have b15787 := hb (x 3 13)
            have b15788 := hb (x 4 12)
            clear * - r15782 e15783 e15784 b15785 b15786 b15787 b15788 d15757 d15773 d15753
            omega
          have d15789 : (x 4 13).toNat = 1 := by
            have r15790 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
            have b15791 := hb (x 2 2)
            have b15792 := hb (x 4 13)
            have b15793 := hb (x 3 1 && x 3 14)
            clear * - r15790 b15791 b15792 b15793 d15622 d15781
            omega
          have d15794 : (x 4 1).toNat = 1 := by
            have r15795 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
            have b15796 := hb (x 4 1)
            have b15797 := hb (x 4 13)
            clear * - r15795 b15796 b15797 d15789
            omega
          have d15798 : (x 5 14).toNat = 0 := by
            have r15799 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
            have b15800 := hb (x 4 1)
            have b15801 := hb (x 5 14)
            clear * - r15799 b15800 b15801 d15794
            omega
          have d15802 : (x 5 1 && x 5 14).toNat = 0 := by
            have r15803 := hand2 (x 5 1) (x 5 14)
            have b15804 := hb (x 5 14)
            have b15805 := hb (x 5 1 && x 5 14)
            clear * - r15803 b15804 b15805 d15798
            omega
          have d15806 : (x 5 3 && x 5 14).toNat = 0 := by
            have r15807 := hand2 (x 5 3) (x 5 14)
            have b15808 := hb (x 5 14)
            have b15809 := hb (x 5 3 && x 5 14)
            clear * - r15807 b15808 b15809 d15798
            omega
          have d15810 : (x 5 2).toNat = 0 := by
            have r15811 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b15812 := hb (x 5 2)
            have b15813 := hb (x 5 14)
            clear * - r15811 b15812 b15813 d15798
            omega
          have d15814 : (x 5 2 && x 5 13).toNat = 0 := by
            have r15815 := hand1 (x 5 2) (x 5 13)
            have b15816 := hb (x 5 2)
            have b15817 := hb (x 5 2 && x 5 13)
            clear * - r15815 b15816 b15817 d15810
            omega
          have d15818 : (x 5 12).toNat = 0 := by
            have r15819 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e15820 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e15821 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b15822 := hb (x 2 3)
            have b15823 := hb (x 3 2)
            have b15824 := hb (x 4 13)
            have b15825 := hb (x 5 12)
            clear * - r15819 e15820 e15821 b15822 b15823 b15824 b15825 d15789 d15626
            omega
          have d15826 : (x 5 4).toNat = 0 := by
            have r15827 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b15828 := hb (x 5 4)
            have b15829 := hb (x 5 12)
            clear * - r15827 b15828 b15829 d15818
            omega
          have d15830 : (x 2 3).toNat = 0 := by
            have r15831 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e15832 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e15833 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b15834 := hb (x 2 3)
            have b15835 := hb (x 3 2)
            have b15836 := hb (x 4 13)
            have b15837 := hb (x 5 12)
            clear * - r15831 e15832 e15833 b15834 b15835 b15836 b15837 d15818 d15789 d15626
            omega
          have d15838 : (x 2 3 && x 2 14).toNat = 0 := by
            have r15839 := hand1 (x 2 3) (x 2 14)
            have b15840 := hb (x 2 3)
            have b15841 := hb (x 2 3 && x 2 14)
            clear * - r15839 b15840 b15841 d15830
            omega
          have d15842 : (x 5 11).toNat = 1 := by
            have r15843 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
            have b15844 := hb (x 1 4)
            have b15845 := hb (x 5 11)
            have b15846 := hb (x 4 1 && x 4 12)
            have b15847 := hb (x 3 2 && x 3 13)
            have b15848 := hb (x 2 3 && x 2 14)
            clear * - r15843 b15844 b15845 b15846 b15847 b15848 d15765 d15630 d15838 d15694
            omega
          have d15849 : (x 5 3).toNat = 1 := by
            have r15850 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
            have b15851 := hb (x 5 3)
            have b15852 := hb (x 5 11)
            clear * - r15850 b15851 b15852 d15842
            omega
          have d15853 : (x 8 12).toNat = 0 := by
            have r15854 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
            have e15855 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e15856 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b15857 := hb (x 5 3)
            have b15858 := hb (x 6 2)
            have b15859 := hb (x 7 13)
            have b15860 := hb (x 8 12)
            clear * - r15854 e15855 e15856 b15857 b15858 b15859 b15860 d15849
            omega
          have d15861 : (x 8 1 && x 8 12).toNat = 0 := by
            have r15862 := hand2 (x 8 1) (x 8 12)
            have b15863 := hb (x 8 12)
            have b15864 := hb (x 8 1 && x 8 12)
            clear * - r15862 b15863 b15864 d15853
            omega
          have d15865 : (x 7 13).toNat = 0 := by
            have r15866 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
            have e15867 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e15868 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b15869 := hb (x 5 3)
            have b15870 := hb (x 6 2)
            have b15871 := hb (x 7 13)
            have b15872 := hb (x 8 12)
            clear * - r15866 e15867 e15868 b15869 b15870 b15871 b15872 d15853 d15849
            omega
          have d15873 : (x 7 2 && x 7 13).toNat = 0 := by
            have r15874 := hand2 (x 7 2) (x 7 13)
            have b15875 := hb (x 7 13)
            have b15876 := hb (x 7 2 && x 7 13)
            clear * - r15874 b15875 b15876 d15865
            omega
          have d15877 : (x 6 1 && x 6 14).toNat = 1 := by
            have r15878 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
            have b15879 := hb (x 5 2)
            have b15880 := hb (x 7 13)
            have b15881 := hb (x 6 1 && x 6 14)
            clear * - r15878 b15879 b15880 b15881 d15865 d15810
            omega
          have d15882 : (x 6 14).toNat = 1 := by
            have r15883 := hand2 (x 6 1) (x 6 14)
            have b15884 := hb (x 6 14)
            have b15885 := hb (x 6 1 && x 6 14)
            clear * - r15883 b15884 b15885 d15877
            omega
          have d15886 : (x 5 1).toNat = 0 := by
            have r15887 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
            have b15888 := hb (x 5 1)
            have b15889 := hb (x 6 14)
            clear * - r15887 b15888 b15889 d15882
            omega
          have d15890 : (x 5 13).toNat = 0 := by
            have r15891 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
            have b15892 := hb (x 5 1)
            have b15893 := hb (x 5 13)
            clear * - r15891 b15892 b15893 d15886
            omega
          have d15894 : (x 6 1).toNat = 1 := by
            have r15895 := hand1 (x 6 1) (x 6 14)
            have b15896 := hb (x 6 1)
            have b15897 := hb (x 6 1 && x 6 14)
            clear * - r15895 b15896 b15897 d15877
            omega
          have d15898 : (x 7 14).toNat = 0 := by
            have r15899 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
            have b15900 := hb (x 6 1)
            have b15901 := hb (x 7 14)
            clear * - r15899 b15900 b15901 d15894
            omega
          have d15902 : (x 7 1 && x 7 14).toNat = 0 := by
            have r15903 := hand2 (x 7 1) (x 7 14)
            have b15904 := hb (x 7 14)
            have b15905 := hb (x 7 1 && x 7 14)
            clear * - r15903 b15904 b15905 d15898
            omega
          have d15906 : (x 7 2).toNat = 0 := by
            have r15907 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b15908 := hb (x 7 2)
            have b15909 := hb (x 7 14)
            clear * - r15907 b15908 b15909 d15898
            omega
          have d15910 : (x 6 2).toNat = 0 := by
            have r15911 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
            have e15912 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e15913 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b15914 := hb (x 5 3)
            have b15915 := hb (x 6 2)
            have b15916 := hb (x 7 13)
            have b15917 := hb (x 8 12)
            clear * - r15911 e15912 e15913 b15914 b15915 b15916 b15917 d15853 d15865 d15849
            omega
          have d15918 : (x 6 2 && x 6 13).toNat = 0 := by
            have r15919 := hand1 (x 6 2) (x 6 13)
            have b15920 := hb (x 6 2)
            have b15921 := hb (x 6 2 && x 6 13)
            clear * - r15919 b15920 b15921 d15910
            omega
          have d15922 : (x 8 13).toNat = 1 := by
            have r15923 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
            have b15924 := hb (x 6 2)
            have b15925 := hb (x 8 13)
            have b15926 := hb (x 7 1 && x 7 14)
            clear * - r15923 b15924 b15925 b15926 d15902 d15910
            omega
          have d15927 : (x 8 1).toNat = 1 := by
            have r15928 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
            have b15929 := hb (x 8 1)
            have b15930 := hb (x 8 13)
            clear * - r15928 b15929 b15930 d15922
            omega
          have d15931 : (x 9 14).toNat = 0 := by
            have r15932 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
            have b15933 := hb (x 8 1)
            have b15934 := hb (x 9 14)
            clear * - r15932 b15933 b15934 d15927
            omega
          have d15935 : (x 9 1 && x 9 14).toNat = 0 := by
            have r15936 := hand2 (x 9 1) (x 9 14)
            have b15937 := hb (x 9 14)
            have b15938 := hb (x 9 1 && x 9 14)
            clear * - r15936 b15937 b15938 d15931
            omega
          have d15939 : (x 9 2).toNat = 0 := by
            have r15940 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
            have b15941 := hb (x 9 2)
            have b15942 := hb (x 9 14)
            clear * - r15940 b15941 b15942 d15931
            omega
          have d15943 : (x 9 12).toNat = 0 := by
            have r15944 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
            have e15945 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e15946 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b15947 := hb (x 6 3)
            have b15948 := hb (x 7 2)
            have b15949 := hb (x 8 13)
            have b15950 := hb (x 9 12)
            clear * - r15944 e15945 e15946 b15947 b15948 b15949 b15950 d15922 d15906
            omega
          have d15951 : (x 6 3).toNat = 0 := by
            have r15952 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
            have e15953 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e15954 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b15955 := hb (x 6 3)
            have b15956 := hb (x 7 2)
            have b15957 := hb (x 8 13)
            have b15958 := hb (x 9 12)
            clear * - r15952 e15953 e15954 b15955 b15956 b15957 b15958 d15943 d15922 d15906
            omega
          have d15959 : (x 6 3 && x 6 14).toNat = 0 := by
            have r15960 := hand1 (x 6 3) (x 6 14)
            have b15961 := hb (x 6 3)
            have b15962 := hb (x 6 3 && x 6 14)
            clear * - r15960 b15961 b15962 d15951
            omega
          have d15963 : (x 9 11).toNat = 1 := by
            have r15964 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := hcov11 9
            have b15965 := hb (x 5 4)
            have b15966 := hb (x 9 11)
            have b15967 := hb (x 8 1 && x 8 12)
            have b15968 := hb (x 7 2 && x 7 13)
            have b15969 := hb (x 6 3 && x 6 14)
            clear * - r15964 b15965 b15966 b15967 b15968 b15969 d15861 d15873 d15959 d15826
            omega
          have d15970 : (x 9 3).toNat = 1 := by
            have r15971 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
            have b15972 := hb (x 9 3)
            have b15973 := hb (x 9 11)
            clear * - r15971 b15972 b15973 d15963
            omega
          have d15974 : (x 12 12).toNat = 0 := by
            have r15975 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
            have e15976 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e15977 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b15978 := hb (x 9 3)
            have b15979 := hb (x 10 2)
            have b15980 := hb (x 11 13)
            have b15981 := hb (x 12 12)
            clear * - r15975 e15976 e15977 b15978 b15979 b15980 b15981 d15970
            omega
          have d15982 : (x 11 13).toNat = 0 := by
            have r15983 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
            have e15984 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e15985 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b15986 := hb (x 9 3)
            have b15987 := hb (x 10 2)
            have b15988 := hb (x 11 13)
            have b15989 := hb (x 12 12)
            clear * - r15983 e15984 e15985 b15986 b15987 b15988 b15989 d15974 d15970
            omega
          have d15990 : (x 10 1 && x 10 14).toNat = 1 := by
            have r15991 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
            have b15992 := hb (x 9 2)
            have b15993 := hb (x 11 13)
            have b15994 := hb (x 10 1 && x 10 14)
            clear * - r15991 b15992 b15993 b15994 d15982 d15939
            omega
          have d15995 : (x 10 14).toNat = 1 := by
            have r15996 := hand2 (x 10 1) (x 10 14)
            have b15997 := hb (x 10 14)
            have b15998 := hb (x 10 1 && x 10 14)
            clear * - r15996 b15997 b15998 d15990
            omega
          have d15999 : (x 9 1).toNat = 0 := by
            have r16000 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
            have b16001 := hb (x 9 1)
            have b16002 := hb (x 10 14)
            clear * - r16000 b16001 b16002 d15995
            omega
          have d16003 : (x 9 13).toNat = 0 := by
            have r16004 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
            have b16005 := hb (x 9 1)
            have b16006 := hb (x 9 13)
            clear * - r16004 b16005 b16006 d15999
            omega
          have d16007 : (x 8 1 && x 8 14).toNat = 1 := by
            have r16008 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
            have b16009 := hb (x 7 2)
            have b16010 := hb (x 9 13)
            have b16011 := hb (x 8 1 && x 8 14)
            clear * - r16008 b16009 b16010 b16011 d16003 d15906
            omega
          have d16012 : (x 8 14).toNat = 1 := by
            have r16013 := hand2 (x 8 1) (x 8 14)
            have b16014 := hb (x 8 14)
            have b16015 := hb (x 8 1 && x 8 14)
            clear * - r16013 b16014 b16015 d16007
            omega
          have d16016 : (x 7 1).toNat = 0 := by
            have r16017 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
            have b16018 := hb (x 7 1)
            have b16019 := hb (x 8 14)
            clear * - r16017 b16018 b16019 d16012
            omega
          have d16020 : (x 7 1 && x 7 12).toNat = 0 := by
            have r16021 := hand1 (x 7 1) (x 7 12)
            have b16022 := hb (x 7 1)
            have b16023 := hb (x 7 1 && x 7 12)
            clear * - r16021 b16022 b16023 d16016
            omega
          have d16024 : (x 8 11).toNat = 1 := by
            have r16025 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
            have b16026 := hb (x 4 4)
            have b16027 := hb (x 8 11)
            have b16028 := hb (x 7 1 && x 7 12)
            have b16029 := hb (x 6 2 && x 6 13)
            have b16030 := hb (x 5 3 && x 5 14)
            clear * - r16025 b16026 b16027 b16028 b16029 b16030 d16020 d15918 d15806 d15769
            omega
          have d16031 : (x 8 3).toNat = 1 := by
            have r16032 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
            have b16033 := hb (x 8 3)
            have b16034 := hb (x 8 11)
            clear * - r16032 b16033 b16034 d16024
            omega
          have d16035 : (x 11 12).toNat = 0 := by
            have r16036 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
            have e16037 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e16038 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b16039 := hb (x 8 3)
            have b16040 := hb (x 9 2)
            have b16041 := hb (x 10 13)
            have b16042 := hb (x 11 12)
            clear * - r16036 e16037 e16038 b16039 b16040 b16041 b16042 d15939 d16031
            omega
          have d16043 : (x 10 13).toNat = 0 := by
            have r16044 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
            have e16045 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e16046 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b16047 := hb (x 8 3)
            have b16048 := hb (x 9 2)
            have b16049 := hb (x 10 13)
            have b16050 := hb (x 11 12)
            clear * - r16044 e16045 e16046 b16047 b16048 b16049 b16050 d16035 d15939 d16031
            omega
          have d16051 : (x 8 2).toNat = 1 := by
            have r16052 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
            have b16053 := hb (x 8 2)
            have b16054 := hb (x 10 13)
            have b16055 := hb (x 9 1 && x 9 14)
            clear * - r16052 b16053 b16054 b16055 d16043 d15935
            omega
          have d16056 : (x 10 12).toNat = 0 := by
            have r16057 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
            have e16058 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e16059 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b16060 := hb (x 7 3)
            have b16061 := hb (x 8 2)
            have b16062 := hb (x 9 13)
            have b16063 := hb (x 10 12)
            clear * - r16057 e16058 e16059 b16060 b16061 b16062 b16063 d16003 d16051
            omega
          have d16064 : (x 7 3).toNat = 0 := by
            have r16065 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
            have e16066 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e16067 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b16068 := hb (x 7 3)
            have b16069 := hb (x 8 2)
            have b16070 := hb (x 9 13)
            have b16071 := hb (x 10 12)
            clear * - r16065 e16066 e16067 b16068 b16069 b16070 b16071 d16056 d16003 d16051
            omega
          have d16072 : (x 7 11).toNat = 0 := by
            have r16073 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
            have b16074 := hb (x 7 3)
            have b16075 := hb (x 7 11)
            clear * - r16073 b16074 b16075 d16064
            omega
          have d16076 : (x 2 11).toNat = 0 := by
            have r16077 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
            have b16078 := hb (x 2 3)
            have b16079 := hb (x 2 11)
            clear * - r16077 b16078 b16079 d15830
            omega
          have d16080 : (x (-1) 3 && x (-1) 14).toNat = 1 := by
            have r16081 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := hcov11 2
            have b16082 := hb (x (-2) 4)
            have b16083 := hb (x 2 11)
            have b16084 := hb (x 1 1 && x 1 12)
            have b16085 := hb (x 0 2 && x 0 13)
            have b16086 := hb (x (-1) 3 && x (-1) 14)
            clear * - r16081 b16082 b16083 b16084 b16085 b16086 d16076 d15597 g30 d15730
            omega
          have d16087 : (x (-1) 3).toNat = 1 := by
            have r16088 := hand1 (x (-1) 3) (x (-1) 14)
            have b16089 := hb (x (-1) 3)
            have b16090 := hb (x (-1) 3 && x (-1) 14)
            clear * - r16088 b16089 b16090 d16080
            omega
          have d16091 : (x 2 12).toNat = 0 := by
            have r16092 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
            have e16093 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e16094 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b16095 := hb (x (-1) 3)
            have b16096 := hb (x 0 2)
            have b16097 := hb (x 1 13)
            have b16098 := hb (x 2 12)
            clear * - r16092 e16093 e16094 b16095 b16096 b16097 b16098 d15601 g7 d16087
            omega
          have d16099 : (x 2 1 && x 2 12).toNat = 0 := by
            have r16100 := hand2 (x 2 1) (x 2 12)
            have b16101 := hb (x 2 12)
            have b16102 := hb (x 2 1 && x 2 12)
            clear * - r16100 b16101 b16102 d16091
            omega
          have d16103 : (x 3 11).toNat = 1 := by
            have r16104 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
            have b16105 := hb (x (-1) 4)
            have b16106 := hb (x 3 11)
            have b16107 := hb (x 2 1 && x 2 12)
            have b16108 := hb (x 1 2 && x 1 13)
            have b16109 := hb (x 0 3 && x 0 14)
            clear * - r16104 b16105 b16106 b16107 b16108 b16109 d16099 d15605 d15575 d15718
            omega
          have d16110 : (x 3 3).toNat = 1 := by
            have r16111 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
            have b16112 := hb (x 3 3)
            have b16113 := hb (x 3 11)
            clear * - r16111 b16112 b16113 d16103
            omega
          have d16114 : (x 6 12).toNat = 0 := by
            have r16115 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
            have e16116 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e16117 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b16118 := hb (x 3 3)
            have b16119 := hb (x 4 2)
            have b16120 := hb (x 5 13)
            have b16121 := hb (x 6 12)
            clear * - r16115 e16116 e16117 b16118 b16119 b16120 b16121 d15890 d16110
            omega
          have d16122 : (x 6 1 && x 6 12).toNat = 0 := by
            have r16123 := hand2 (x 6 1) (x 6 12)
            have b16124 := hb (x 6 12)
            have b16125 := hb (x 6 1 && x 6 12)
            clear * - r16123 b16124 b16125 d16114
            omega
          have d16126 : (x 4 3 && x 4 14).toNat = 1 := by
            have r16127 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
            have b16128 := hb (x 3 4)
            have b16129 := hb (x 7 11)
            have b16130 := hb (x 6 1 && x 6 12)
            have b16131 := hb (x 5 2 && x 5 13)
            have b16132 := hb (x 4 3 && x 4 14)
            clear * - r16127 b16128 b16129 b16130 b16131 b16132 d16072 d16122 d15814 d15513
            omega
          have d16133 : (x 4 3).toNat = 1 := by
            have r16134 := hand1 (x 4 3) (x 4 14)
            have b16135 := hb (x 4 3)
            have b16136 := hb (x 4 3 && x 4 14)
            clear * - r16134 b16135 b16136 d16126
            omega
          have d16137 : (x 7 12).toNat = 0 := by
            have r16138 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
            have e16139 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e16140 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b16141 := hb (x 4 3)
            have b16142 := hb (x 5 2)
            have b16143 := hb (x 6 13)
            have b16144 := hb (x 7 12)
            clear * - r16138 e16139 e16140 b16141 b16142 b16143 b16144 d15810 d16133
            omega
          have d16145 : (x 6 13).toNat = 0 := by
            have r16146 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
            have e16147 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e16148 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b16149 := hb (x 4 3)
            have b16150 := hb (x 5 2)
            have b16151 := hb (x 6 13)
            have b16152 := hb (x 7 12)
            clear * - r16146 e16147 e16148 b16149 b16150 b16151 b16152 d16137 d15810 d16133
            omega
          have d16153 : (x 4 2).toNat = 1 := by
            have r16154 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
            have b16155 := hb (x 4 2)
            have b16156 := hb (x 6 13)
            have b16157 := hb (x 5 1 && x 5 14)
            clear * - r16154 b16155 b16156 b16157 d16145 d15802
            omega
          have r16158 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
          have e16159 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e16160 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b16161 := hb (x 3 3)
          have b16162 := hb (x 4 2)
          have b16163 := hb (x 5 13)
          have b16164 := hb (x 6 12)
          linarith only [r16158, e16159, e16160, b16161, b16162, b16163, b16164, d16114, d15890, d16153, d16110]
        · have f16165 : (x 1 1).toNat = 1 := by rw [h15591]; rfl
          have d16166 : (x 2 14).toNat = 0 := by
            have r16167 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
            have b16168 := hb (x 1 1)
            have b16169 := hb (x 2 14)
            clear * - r16167 b16168 b16169 f16165
            omega
          have d16170 : (x 2 1 && x 2 14).toNat = 0 := by
            have r16171 := hand2 (x 2 1) (x 2 14)
            have b16172 := hb (x 2 14)
            have b16173 := hb (x 2 1 && x 2 14)
            clear * - r16171 b16172 b16173 d16166
            omega
          have d16174 : (x 2 6).toNat = 0 := by
            have r16175 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
            have b16176 := hb (x 2 6)
            have b16177 := hb (x 2 14)
            clear * - r16175 b16176 b16177 d16166
            omega
          have d16178 : (x 2 6 && x 2 13).toNat = 0 := by
            have r16179 := hand1 (x 2 6) (x 2 13)
            have b16180 := hb (x 2 6)
            have b16181 := hb (x 2 6 && x 2 13)
            clear * - r16179 b16180 b16181 d16174
            omega
          have d16182 : (x 2 6 && x 2 12).toNat = 0 := by
            have r16183 := hand1 (x 2 6) (x 2 12)
            have b16184 := hb (x 2 6)
            have b16185 := hb (x 2 6 && x 2 12)
            clear * - r16183 b16184 b16185 d16174
            omega
          have d16186 : (x 2 6 && x 2 10).toNat = 0 := by
            have r16187 := hand1 (x 2 6) (x 2 10)
            have b16188 := hb (x 2 6)
            have b16189 := hb (x 2 6 && x 2 10)
            clear * - r16187 b16188 b16189 d16174
            omega
          have d16190 : (x 2 2).toNat = 0 := by
            have r16191 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
            have b16192 := hb (x 2 2)
            have b16193 := hb (x 2 14)
            clear * - r16191 b16192 b16193 d16166
            omega
          have d16194 : (x 2 2 && x 2 13).toNat = 0 := by
            have r16195 := hand1 (x 2 2) (x 2 13)
            have b16196 := hb (x 2 2)
            have b16197 := hb (x 2 2 && x 2 13)
            clear * - r16195 b16196 b16197 d16190
            omega
          have d16198 : (x 2 2 && x 2 12).toNat = 0 := by
            have r16199 := hand1 (x 2 2) (x 2 12)
            have b16200 := hb (x 2 2)
            have b16201 := hb (x 2 2 && x 2 12)
            clear * - r16199 b16200 b16201 d16190
            omega
          have d16202 : (x 2 10).toNat = 0 := by
            have r16203 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
            have b16204 := hb (x 2 2)
            have b16205 := hb (x 2 10)
            clear * - r16203 b16204 b16205 d16190
            omega
          cases h16206 : x (-1) 2
          · have f16207 : (x (-1) 2).toNat = 0 := by rw [h16206]; rfl
            have d16208 : (x (-1) 10).toNat = 0 := by
              have r16209 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
              have b16210 := hb (x (-1) 2)
              have b16211 := hb (x (-1) 10)
              clear * - r16209 b16210 b16211 f16207
              omega
            have d16212 : (x 1 13).toNat = 1 := by
              have r16213 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
              have b16214 := hb (x (-1) 2)
              have b16215 := hb (x 1 13)
              have b16216 := hb (x 0 1 && x 0 14)
              clear * - r16213 b16214 b16215 b16216 g32 f16207
              omega
            have d16217 : (x 2 12).toNat = 0 := by
              have r16218 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
              have e16219 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
              have e16220 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
              have b16221 := hb (x (-1) 3)
              have b16222 := hb (x 0 2)
              have b16223 := hb (x 1 13)
              have b16224 := hb (x 2 12)
              clear * - r16218 e16219 e16220 b16221 b16222 b16223 b16224 d16212 g7
              omega
            have d16225 : (x 2 8 && x 2 12).toNat = 0 := by
              have r16226 := hand2 (x 2 8) (x 2 12)
              have b16227 := hb (x 2 12)
              have b16228 := hb (x 2 8 && x 2 12)
              clear * - r16226 b16227 b16228 d16217
              omega
            have d16229 : (x 2 4).toNat = 0 := by
              have r16230 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
              have b16231 := hb (x 2 4)
              have b16232 := hb (x 2 12)
              clear * - r16230 b16231 b16232 d16217
              omega
            have d16233 : (x 2 4 && x 2 13).toNat = 0 := by
              have r16234 := hand1 (x 2 4) (x 2 13)
              have b16235 := hb (x 2 4)
              have b16236 := hb (x 2 4 && x 2 13)
              clear * - r16234 b16235 b16236 d16229
              omega
            have d16237 : (x (-1) 3).toNat = 0 := by
              have r16238 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
              have e16239 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
              have e16240 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
              have b16241 := hb (x (-1) 3)
              have b16242 := hb (x 0 2)
              have b16243 := hb (x 1 13)
              have b16244 := hb (x 2 12)
              clear * - r16238 e16239 e16240 b16241 b16242 b16243 b16244 d16217 d16212 g7
              omega
            have d16245 : (x (-1) 11).toNat = 0 := by
              have r16246 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
              have b16247 := hb (x (-1) 3)
              have b16248 := hb (x (-1) 11)
              clear * - r16246 b16247 b16248 d16237
              omega
            cases h16249 : x 1 2
            · have f16250 : (x 1 2).toNat = 0 := by rw [h16249]; rfl
              have d16251 : (x 3 13).toNat = 1 := by
                have r16252 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
                have b16253 := hb (x 1 2)
                have b16254 := hb (x 3 13)
                have b16255 := hb (x 2 1 && x 2 14)
                clear * - r16252 b16253 b16254 b16255 d16170 f16250
                omega
              have d16256 : (x 3 1).toNat = 1 := by
                have r16257 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                have b16258 := hb (x 3 1)
                have b16259 := hb (x 3 13)
                clear * - r16257 b16258 b16259 d16251
                omega
              have d16260 : (x 4 14).toNat = 0 := by
                have r16261 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
                have b16262 := hb (x 3 1)
                have b16263 := hb (x 4 14)
                clear * - r16261 b16262 b16263 d16256
                omega
              have d16264 : (x 4 3 && x 4 14).toNat = 0 := by
                have r16265 := hand2 (x 4 3) (x 4 14)
                have b16266 := hb (x 4 14)
                have b16267 := hb (x 4 3 && x 4 14)
                clear * - r16265 b16266 b16267 d16260
                omega
              have d16268 : (x 4 6).toNat = 0 := by
                have r16269 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
                have b16270 := hb (x 4 6)
                have b16271 := hb (x 4 14)
                clear * - r16269 b16270 b16271 d16260
                omega
              have d16272 : (x 4 6 && x 4 10).toNat = 0 := by
                have r16273 := hand1 (x 4 6) (x 4 10)
                have b16274 := hb (x 4 6)
                have b16275 := hb (x 4 6 && x 4 10)
                clear * - r16273 b16274 b16275 d16268
                omega
              have d16276 : (x 4 2).toNat = 0 := by
                have r16277 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                have b16278 := hb (x 4 2)
                have b16279 := hb (x 4 14)
                clear * - r16277 b16278 b16279 d16260
                omega
              have d16280 : (x 4 10).toNat = 0 := by
                have r16281 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                have b16282 := hb (x 4 2)
                have b16283 := hb (x 4 10)
                clear * - r16281 b16282 b16283 d16276
                omega
              have d16284 : (x 4 12).toNat = 0 := by
                have r16285 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
                have e16286 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e16287 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b16288 := hb (x 1 3)
                have b16289 := hb (x 2 2)
                have b16290 := hb (x 3 13)
                have b16291 := hb (x 4 12)
                clear * - r16285 e16286 e16287 b16288 b16289 b16290 b16291 d16251 d16190
                omega
              have d16292 : (x 1 3).toNat = 0 := by
                have r16293 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
                have e16294 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e16295 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b16296 := hb (x 1 3)
                have b16297 := hb (x 2 2)
                have b16298 := hb (x 3 13)
                have b16299 := hb (x 4 12)
                clear * - r16293 e16294 e16295 b16296 b16297 b16298 b16299 d16284 d16251 d16190
                omega
              have d16300 : (x 1 3 && x 1 13).toNat = 0 := by
                have r16301 := hand1 (x 1 3) (x 1 13)
                have b16302 := hb (x 1 3)
                have b16303 := hb (x 1 3 && x 1 13)
                clear * - r16301 b16302 b16303 d16292
                omega
              have d16304 : (x 1 11).toNat = 0 := by
                have r16305 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                have b16306 := hb (x 1 3)
                have b16307 := hb (x 1 11)
                clear * - r16305 b16306 b16307 d16292
                omega
              have d16308 : (x 1 1 && x 1 11).toNat = 0 := by
                have r16309 := hand2 (x 1 1) (x 1 11)
                have b16310 := hb (x 1 11)
                have b16311 := hb (x 1 1 && x 1 11)
                clear * - r16309 b16310 b16311 d16304
                omega
              have d16312 : (x 3 1 && x 3 11).toNat = 1 := by
                have r16313 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := hcov10 4
                have b16314 := hb (x (-1) 5)
                have b16315 := hb (x 4 10)
                have b16316 := hb (x 3 1 && x 3 11)
                have b16317 := hb (x 2 2 && x 2 12)
                have b16318 := hb (x 1 3 && x 1 13)
                have b16319 := hb (x 0 4 && x 0 14)
                clear * - r16313 b16314 b16315 b16316 b16317 b16318 b16319 d16280 d16198 d16300 g24 g4
                omega
              have d16320 : (x 3 11).toNat = 1 := by
                have r16321 := hand2 (x 3 1) (x 3 11)
                have b16322 := hb (x 3 11)
                have b16323 := hb (x 3 1 && x 3 11)
                clear * - r16321 b16322 b16323 d16312
                omega
              have d16324 : (x 3 3).toNat = 1 := by
                have r16325 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                have b16326 := hb (x 3 3)
                have b16327 := hb (x 3 11)
                clear * - r16325 b16326 b16327 d16320
                omega
              have d16328 : (x 6 12).toNat = 0 := by
                have r16329 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
                have e16330 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e16331 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b16332 := hb (x 3 3)
                have b16333 := hb (x 4 2)
                have b16334 := hb (x 5 13)
                have b16335 := hb (x 6 12)
                clear * - r16329 e16330 e16331 b16332 b16333 b16334 b16335 d16276 d16324
                omega
              have d16336 : (x 6 1 && x 6 12).toNat = 0 := by
                have r16337 := hand2 (x 6 1) (x 6 12)
                have b16338 := hb (x 6 12)
                have b16339 := hb (x 6 1 && x 6 12)
                clear * - r16337 b16338 b16339 d16328
                omega
              have d16340 : (x 6 4).toNat = 0 := by
                have r16341 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                have b16342 := hb (x 6 4)
                have b16343 := hb (x 6 12)
                clear * - r16341 b16342 b16343 d16328
                omega
              have d16344 : (x 6 4 && x 6 8).toNat = 0 := by
                have r16345 := hand1 (x 6 4) (x 6 8)
                have b16346 := hb (x 6 4)
                have b16347 := hb (x 6 4 && x 6 8)
                clear * - r16345 b16346 b16347 d16340
                omega
              have d16348 : (x 5 13).toNat = 0 := by
                have r16349 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
                have e16350 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e16351 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b16352 := hb (x 3 3)
                have b16353 := hb (x 4 2)
                have b16354 := hb (x 5 13)
                have b16355 := hb (x 6 12)
                clear * - r16349 e16350 e16351 b16352 b16353 b16354 b16355 d16328 d16276 d16324
                omega
              have d16356 : (x 5 2 && x 5 13).toNat = 0 := by
                have r16357 := hand2 (x 5 2) (x 5 13)
                have b16358 := hb (x 5 13)
                have b16359 := hb (x 5 2 && x 5 13)
                clear * - r16357 b16358 b16359 d16348
                omega
              have d16360 : (x 7 11).toNat = 1 := by
                have r16361 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
                have b16362 := hb (x 3 4)
                have b16363 := hb (x 7 11)
                have b16364 := hb (x 6 1 && x 6 12)
                have b16365 := hb (x 5 2 && x 5 13)
                have b16366 := hb (x 4 3 && x 4 14)
                clear * - r16361 b16362 b16363 b16364 b16365 b16366 d16336 d16356 d16264 d15513
                omega
              have d16367 : (x 7 3).toNat = 1 := by
                have r16368 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                have b16369 := hb (x 7 3)
                have b16370 := hb (x 7 11)
                clear * - r16368 b16369 b16370 d16360
                omega
              have d16371 : (x 10 12).toNat = 0 := by
                have r16372 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e16373 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e16374 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b16375 := hb (x 7 3)
                have b16376 := hb (x 8 2)
                have b16377 := hb (x 9 13)
                have b16378 := hb (x 10 12)
                clear * - r16372 e16373 e16374 b16375 b16376 b16377 b16378 d16367
                omega
              have d16379 : (x 10 4).toNat = 0 := by
                have r16380 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                have b16381 := hb (x 10 4)
                have b16382 := hb (x 10 12)
                clear * - r16380 b16381 b16382 d16371
                omega
              have d16383 : (x 9 13).toNat = 0 := by
                have r16384 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e16385 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e16386 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b16387 := hb (x 7 3)
                have b16388 := hb (x 8 2)
                have b16389 := hb (x 9 13)
                have b16390 := hb (x 10 12)
                clear * - r16384 e16385 e16386 b16387 b16388 b16389 b16390 d16371 d16367
                omega
              have d16391 : (x 9 5).toNat = 0 := by
                have r16392 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
                have b16393 := hb (x 9 5)
                have b16394 := hb (x 9 13)
                clear * - r16392 b16393 b16394 d16383
                omega
              have d16395 : (x 8 2).toNat = 0 := by
                have r16396 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
                have e16397 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e16398 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b16399 := hb (x 7 3)
                have b16400 := hb (x 8 2)
                have b16401 := hb (x 9 13)
                have b16402 := hb (x 10 12)
                clear * - r16396 e16397 e16398 b16399 b16400 b16401 b16402 d16371 d16383 d16367
                omega
              have d16403 : (x 8 2 && x 8 6).toNat = 0 := by
                have r16404 := hand1 (x 8 2) (x 8 6)
                have b16405 := hb (x 8 2)
                have b16406 := hb (x 8 2 && x 8 6)
                clear * - r16404 b16405 b16406 d16395
                omega
              have d16407 : (x 8 10).toNat = 0 := by
                have r16408 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                have b16409 := hb (x 8 2)
                have b16410 := hb (x 8 10)
                clear * - r16408 b16409 b16410 d16395
                omega
              have d16411 : (x 5 5).toNat = 0 := by
                have r16412 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                have b16413 := hb (x 5 5)
                have b16414 := hb (x 5 13)
                clear * - r16412 b16413 b16414 d16348
                omega
              have d16415 : (x 5 5 && x 5 9).toNat = 0 := by
                have r16416 := hand1 (x 5 5) (x 5 9)
                have b16417 := hb (x 5 5)
                have b16418 := hb (x 5 5 && x 5 9)
                clear * - r16416 b16417 b16418 d16411
                omega
              have d16419 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
                have r16420 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := hcov10 2
                have b16421 := hb (x (-3) 5)
                have b16422 := hb (x 2 10)
                have b16423 := hb (x 1 1 && x 1 11)
                have b16424 := hb (x 0 2 && x 0 12)
                have b16425 := hb (x (-1) 3 && x (-1) 13)
                have b16426 := hb (x (-2) 4 && x (-2) 14)
                clear * - r16420 b16421 b16422 b16423 b16424 b16425 b16426 d16202 d16308 g22 g23 g0
                omega
              have d16427 : (x (-2) 4).toNat = 1 := by
                have r16428 := hand1 (x (-2) 4) (x (-2) 14)
                have b16429 := hb (x (-2) 4)
                have b16430 := hb (x (-2) 4 && x (-2) 14)
                clear * - r16428 b16429 b16430 d16419
                omega
              have d16431 : (x 10 8).toNat = 0 := by
                have r16432 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
                have e16433 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e16434 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e16435 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e16436 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e16437 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e16438 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b16439 := hb (x 3 7)
                have b16440 := hb (x 4 6)
                have b16441 := hb (x 5 5)
                have b16442 := hb (x 6 4)
                have b16443 := hb (x 7 11)
                have b16444 := hb (x 8 10)
                have b16445 := hb (x 9 9)
                have b16446 := hb (x 10 8)
                clear * - r16432 e16433 e16434 e16435 e16436 e16437 e16438 b16439 b16440 b16441 b16442 b16443 b16444 b16445 b16446 d16407 d16360 d16340 d16411 d16268
                omega
              have d16447 : (x 9 9).toNat = 0 := by
                have r16448 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
                have e16449 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e16450 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e16451 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e16452 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e16453 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e16454 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b16455 := hb (x 3 7)
                have b16456 := hb (x 4 6)
                have b16457 := hb (x 5 5)
                have b16458 := hb (x 6 4)
                have b16459 := hb (x 7 11)
                have b16460 := hb (x 8 10)
                have b16461 := hb (x 9 9)
                have b16462 := hb (x 10 8)
                clear * - r16448 e16449 e16450 e16451 e16452 e16453 e16454 b16455 b16456 b16457 b16458 b16459 b16460 b16461 b16462 d16431 d16407 d16360 d16340 d16411 d16268
                omega
              have d16463 : (x 3 7).toNat = 0 := by
                have r16464 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
                have e16465 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                have e16466 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                have e16467 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                have e16468 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                have e16469 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                have e16470 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                have b16471 := hb (x 3 7)
                have b16472 := hb (x 4 6)
                have b16473 := hb (x 5 5)
                have b16474 := hb (x 6 4)
                have b16475 := hb (x 7 11)
                have b16476 := hb (x 8 10)
                have b16477 := hb (x 9 9)
                have b16478 := hb (x 10 8)
                clear * - r16464 e16465 e16466 e16467 e16468 e16469 e16470 b16471 b16472 b16473 b16474 b16475 b16476 b16477 b16478 d16431 d16447 d16407 d16360 d16340 d16411 d16268
                omega
              have d16479 : (x 3 7 && x 3 11).toNat = 0 := by
                have r16480 := hand1 (x 3 7) (x 3 11)
                have b16481 := hb (x 3 7)
                have b16482 := hb (x 3 7 && x 3 11)
                clear * - r16480 b16481 b16482 d16463
                omega
              have d16483 : (x 6 8).toNat = 0 := by
                have r16484 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e16485 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e16486 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e16487 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e16488 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e16489 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e16490 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b16491 := hb (x (-1) 7)
                have b16492 := hb (x 0 6)
                have b16493 := hb (x 1 5)
                have b16494 := hb (x 2 4)
                have b16495 := hb (x 3 11)
                have b16496 := hb (x 4 10)
                have b16497 := hb (x 5 9)
                have b16498 := hb (x 6 8)
                clear * - r16484 e16485 e16486 e16487 e16488 e16489 e16490 b16491 b16492 b16493 b16494 b16495 b16496 b16497 b16498 d16280 d16320 d16229 f15584
                omega
              have d16499 : (x 5 9).toNat = 0 := by
                have r16500 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e16501 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e16502 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e16503 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e16504 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e16505 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e16506 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b16507 := hb (x (-1) 7)
                have b16508 := hb (x 0 6)
                have b16509 := hb (x 1 5)
                have b16510 := hb (x 2 4)
                have b16511 := hb (x 3 11)
                have b16512 := hb (x 4 10)
                have b16513 := hb (x 5 9)
                have b16514 := hb (x 6 8)
                clear * - r16500 e16501 e16502 e16503 e16504 e16505 e16506 b16507 b16508 b16509 b16510 b16511 b16512 b16513 b16514 d16483 d16280 d16320 d16229 f15584
                omega
              have d16515 : (x 2 8).toNat = 0 := by
                have r16516 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                have e16517 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                have e16518 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                have e16519 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                have e16520 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                have e16521 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                have e16522 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                have b16523 := hb (x (-5) 7)
                have b16524 := hb (x (-4) 6)
                have b16525 := hb (x (-3) 5)
                have b16526 := hb (x (-2) 4)
                have b16527 := hb (x (-1) 11)
                have b16528 := hb (x 0 10)
                have b16529 := hb (x 1 9)
                have b16530 := hb (x 2 8)
                clear * - r16516 e16517 e16518 e16519 e16520 e16521 e16522 b16523 b16524 b16525 b16526 b16527 b16528 b16529 b16530 g12 d16245 d16427 g0
                omega
              have d16531 : (x 1 9).toNat = 0 := by
                have r16532 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                have e16533 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                have e16534 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                have e16535 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                have e16536 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                have e16537 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                have e16538 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                have b16539 := hb (x (-5) 7)
                have b16540 := hb (x (-4) 6)
                have b16541 := hb (x (-3) 5)
                have b16542 := hb (x (-2) 4)
                have b16543 := hb (x (-1) 11)
                have b16544 := hb (x 0 10)
                have b16545 := hb (x 1 9)
                have b16546 := hb (x 2 8)
                clear * - r16532 e16533 e16534 e16535 e16536 e16537 e16538 b16539 b16540 b16541 b16542 b16543 b16544 b16545 b16546 d16515 g12 d16245 d16427 g0
                omega
              have d16547 : (x 1 9 && x 1 13).toNat = 0 := by
                have r16548 := hand1 (x 1 9) (x 1 13)
                have b16549 := hb (x 1 9)
                have b16550 := hb (x 1 9 && x 1 13)
                clear * - r16548 b16549 b16550 d16531
                omega
              have d16551 : (x 7 3 && x 7 7).toNat = 1 := by
                have r16552 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := hcov4 10
                have e16553 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
                have e16554 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
                have b16555 := hb (x (-1) 11)
                have b16556 := hb (x 0 10)
                have b16557 := hb (x 9 5)
                have b16558 := hb (x 10 4)
                have b16559 := hb (x 8 2 && x 8 6)
                have b16560 := hb (x 7 3 && x 7 7)
                have b16561 := hb (x 6 4 && x 6 8)
                have b16562 := hb (x 5 5 && x 5 9)
                have b16563 := hb (x 4 6 && x 4 10)
                have b16564 := hb (x 3 7 && x 3 11)
                have b16565 := hb (x 2 8 && x 2 12)
                have b16566 := hb (x 1 9 && x 1 13)
                clear * - r16552 e16553 e16554 b16555 b16556 b16557 b16558 b16559 b16560 b16561 b16562 b16563 b16564 b16565 b16566 d16379 d16391 d16403 d16344 d16415 d16272 d16479 d16225 d16547 g12 d16245
                omega
              have d16567 : (x 7 7).toNat = 1 := by
                have r16568 := hand2 (x 7 3) (x 7 7)
                have b16569 := hb (x 7 7)
                have b16570 := hb (x 7 3 && x 7 7)
                clear * - r16568 b16569 b16570 d16551
                omega
              have d16571 : (x 14 8).toNat = 0 := by
                have r16572 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e16573 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e16574 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e16575 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e16576 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e16577 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e16578 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b16579 := hb (x 7 7)
                have b16580 := hb (x 8 6)
                have b16581 := hb (x 9 5)
                have b16582 := hb (x 10 4)
                have b16583 := hb (x 11 11)
                have b16584 := hb (x 12 10)
                have b16585 := hb (x 13 9)
                have b16586 := hb (x 14 8)
                clear * - r16572 e16573 e16574 e16575 e16576 e16577 e16578 b16579 b16580 b16581 b16582 b16583 b16584 b16585 b16586 d16379 d16391 d16567
                omega
              have d16587 : (x 13 9).toNat = 0 := by
                have r16588 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e16589 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e16590 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e16591 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e16592 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e16593 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e16594 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b16595 := hb (x 7 7)
                have b16596 := hb (x 8 6)
                have b16597 := hb (x 9 5)
                have b16598 := hb (x 10 4)
                have b16599 := hb (x 11 11)
                have b16600 := hb (x 12 10)
                have b16601 := hb (x 13 9)
                have b16602 := hb (x 14 8)
                clear * - r16588 e16589 e16590 e16591 e16592 e16593 e16594 b16595 b16596 b16597 b16598 b16599 b16600 b16601 b16602 d16571 d16379 d16391 d16567
                omega
              have d16603 : (x 12 10).toNat = 0 := by
                have r16604 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e16605 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e16606 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e16607 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e16608 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e16609 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e16610 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b16611 := hb (x 7 7)
                have b16612 := hb (x 8 6)
                have b16613 := hb (x 9 5)
                have b16614 := hb (x 10 4)
                have b16615 := hb (x 11 11)
                have b16616 := hb (x 12 10)
                have b16617 := hb (x 13 9)
                have b16618 := hb (x 14 8)
                clear * - r16604 e16605 e16606 e16607 e16608 e16609 e16610 b16611 b16612 b16613 b16614 b16615 b16616 b16617 b16618 d16571 d16587 d16379 d16391 d16567
                omega
              have d16619 : (x 11 11).toNat = 0 := by
                have r16620 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e16621 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e16622 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e16623 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e16624 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e16625 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e16626 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b16627 := hb (x 7 7)
                have b16628 := hb (x 8 6)
                have b16629 := hb (x 9 5)
                have b16630 := hb (x 10 4)
                have b16631 := hb (x 11 11)
                have b16632 := hb (x 12 10)
                have b16633 := hb (x 13 9)
                have b16634 := hb (x 14 8)
                clear * - r16620 e16621 e16622 e16623 e16624 e16625 e16626 b16627 b16628 b16629 b16630 b16631 b16632 b16633 b16634 d16571 d16587 d16603 d16379 d16391 d16567
                omega
              have d16635 : (x 8 6).toNat = 0 := by
                have r16636 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
                have e16637 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e16638 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e16639 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e16640 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e16641 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e16642 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have b16643 := hb (x 7 7)
                have b16644 := hb (x 8 6)
                have b16645 := hb (x 9 5)
                have b16646 := hb (x 10 4)
                have b16647 := hb (x 11 11)
                have b16648 := hb (x 12 10)
                have b16649 := hb (x 13 9)
                have b16650 := hb (x 14 8)
                clear * - r16636 e16637 e16638 e16639 e16640 e16641 e16642 b16643 b16644 b16645 b16646 b16647 b16648 b16649 b16650 d16571 d16587 d16603 d16619 d16379 d16391 d16567
                omega
              have r16651 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
              have b16652 := hb (x 0 14)
              have b16653 := hb (x 1 13)
              have b16654 := hb (x 2 12)
              have b16655 := hb (x 3 11)
              have b16656 := hb (x 4 10)
              have b16657 := hb (x 5 9)
              have b16658 := hb (x 6 8)
              have b16659 := hb (x 7 7)
              have b16660 := hb (x 8 6)
              have b16661 := hb (x 9 5)
              have b16662 := hb (x 10 4)
              have b16663 := hb (x 11 3)
              have b16664 := hb (x 12 2)
              have b16665 := hb (x 13 1)
              linarith only [r16651, b16652, b16653, b16654, b16655, b16656, b16657, b16658, b16659, b16660, b16661, b16662, b16663, b16664, b16665, d16379, d16391, d16635, d16567, d16483, d16499, d16280, d16320, d16217, d16212, g15]
            · have f16666 : (x 1 2).toNat = 1 := by rw [h16249]; rfl
              have d16667 : (x 3 12).toNat = 0 := by
                have r16668 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
                have e16669 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                have e16670 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                have b16671 := hb (x 0 3)
                have b16672 := hb (x 1 2)
                have b16673 := hb (x 2 13)
                have b16674 := hb (x 3 12)
                clear * - r16668 e16669 e16670 b16671 b16672 b16673 b16674 f16666 f15574
                omega
              have d16675 : (x 3 1 && x 3 12).toNat = 0 := by
                have r16676 := hand2 (x 3 1) (x 3 12)
                have b16677 := hb (x 3 12)
                have b16678 := hb (x 3 1 && x 3 12)
                clear * - r16676 b16677 b16678 d16667
                omega
              have d16679 : (x 3 2 && x 3 12).toNat = 0 := by
                have r16680 := hand2 (x 3 2) (x 3 12)
                have b16681 := hb (x 3 12)
                have b16682 := hb (x 3 2 && x 3 12)
                clear * - r16680 b16681 b16682 d16667
                omega
              have d16683 : (x 3 3 && x 3 12).toNat = 0 := by
                have r16684 := hand2 (x 3 3) (x 3 12)
                have b16685 := hb (x 3 12)
                have b16686 := hb (x 3 3 && x 3 12)
                clear * - r16684 b16685 b16686 d16667
                omega
              have d16687 : (x 3 5 && x 3 12).toNat = 0 := by
                have r16688 := hand2 (x 3 5) (x 3 12)
                have b16689 := hb (x 3 12)
                have b16690 := hb (x 3 5 && x 3 12)
                clear * - r16688 b16689 b16690 d16667
                omega
              have d16691 : (x 2 13).toNat = 0 := by
                have r16692 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
                have e16693 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                have e16694 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                have b16695 := hb (x 0 3)
                have b16696 := hb (x 1 2)
                have b16697 := hb (x 2 13)
                have b16698 := hb (x 3 12)
                clear * - r16692 e16693 e16694 b16695 b16696 b16697 b16698 d16667 f16666 f15574
                omega
              have d16699 : (x 2 3 && x 2 13).toNat = 0 := by
                have r16700 := hand2 (x 2 3) (x 2 13)
                have b16701 := hb (x 2 13)
                have b16702 := hb (x 2 3 && x 2 13)
                clear * - r16700 b16701 b16702 d16691
                omega
              have d16703 : (x 1 3 && x 1 14).toNat = 1 := by
                have r16704 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
                have b16705 := hb (x 0 4)
                have b16706 := hb (x 4 11)
                have b16707 := hb (x 3 1 && x 3 12)
                have b16708 := hb (x 2 2 && x 2 13)
                have b16709 := hb (x 1 3 && x 1 14)
                clear * - r16704 b16705 b16706 b16707 b16708 b16709 d15481 d16675 d16194 g8
                omega
              have d16710 : (x 1 3).toNat = 1 := by
                have r16711 := hand1 (x 1 3) (x 1 14)
                have b16712 := hb (x 1 3)
                have b16713 := hb (x 1 3 && x 1 14)
                clear * - r16711 b16712 b16713 d16703
                omega
              have d16714 : (x 4 12).toNat = 0 := by
                have r16715 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
                have e16716 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e16717 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b16718 := hb (x 1 3)
                have b16719 := hb (x 2 2)
                have b16720 := hb (x 3 13)
                have b16721 := hb (x 4 12)
                clear * - r16715 e16716 e16717 b16718 b16719 b16720 b16721 d16190 d16710
                omega
              have d16722 : (x 4 3 && x 4 12).toNat = 0 := by
                have r16723 := hand2 (x 4 3) (x 4 12)
                have b16724 := hb (x 4 12)
                have b16725 := hb (x 4 3 && x 4 12)
                clear * - r16723 b16724 b16725 d16714
                omega
              have d16726 : (x 4 4).toNat = 0 := by
                have r16727 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b16728 := hb (x 4 4)
                have b16729 := hb (x 4 12)
                clear * - r16727 b16728 b16729 d16714
                omega
              have d16730 : (x 4 4 && x 4 10).toNat = 0 := by
                have r16731 := hand1 (x 4 4) (x 4 10)
                have b16732 := hb (x 4 4)
                have b16733 := hb (x 4 4 && x 4 10)
                clear * - r16731 b16732 b16733 d16726
                omega
              have d16734 : (x 4 4 && x 4 8).toNat = 0 := by
                have r16735 := hand1 (x 4 4) (x 4 8)
                have b16736 := hb (x 4 4)
                have b16737 := hb (x 4 4 && x 4 8)
                clear * - r16735 b16736 b16737 d16726
                omega
              have d16738 : (x 3 13).toNat = 0 := by
                have r16739 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
                have e16740 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e16741 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b16742 := hb (x 1 3)
                have b16743 := hb (x 2 2)
                have b16744 := hb (x 3 13)
                have b16745 := hb (x 4 12)
                clear * - r16739 e16740 e16741 b16742 b16743 b16744 b16745 d16714 d16190 d16710
                omega
              have d16746 : (x 3 5).toNat = 0 := by
                have r16747 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                have b16748 := hb (x 3 5)
                have b16749 := hb (x 3 13)
                clear * - r16747 b16748 b16749 d16738
                omega
              have d16750 : (x 3 5 && x 3 11).toNat = 0 := by
                have r16751 := hand1 (x 3 5) (x 3 11)
                have b16752 := hb (x 3 5)
                have b16753 := hb (x 3 5 && x 3 11)
                clear * - r16751 b16752 b16753 d16746
                omega
              have d16754 : (x 3 5 && x 3 9).toNat = 0 := by
                have r16755 := hand1 (x 3 5) (x 3 9)
                have b16756 := hb (x 3 5)
                have b16757 := hb (x 3 5 && x 3 9)
                clear * - r16755 b16756 b16757 d16746
                omega
              have d16758 : (x 1 4 && x 1 14).toNat = 1 := by
                have r16759 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
                have b16760 := hb (x 0 5)
                have b16761 := hb (x 5 10)
                have b16762 := hb (x 4 1 && x 4 11)
                have b16763 := hb (x 3 2 && x 3 12)
                have b16764 := hb (x 2 3 && x 2 13)
                have b16765 := hb (x 1 4 && x 1 14)
                clear * - r16759 b16760 b16761 b16762 b16763 b16764 b16765 d15453 d15497 d16679 d16699 g9
                omega
              have d16766 : (x 1 4).toNat = 1 := by
                have r16767 := hand1 (x 1 4) (x 1 14)
                have b16768 := hb (x 1 4)
                have b16769 := hb (x 1 4 && x 1 14)
                clear * - r16767 b16768 b16769 d16758
                omega
              have d16770 : (x 1 12).toNat = 1 := by
                have r16771 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                have b16772 := hb (x 1 4)
                have b16773 := hb (x 1 12)
                clear * - r16771 b16772 b16773 d16766
                omega
              have d16774 : (x (-2) 3).toNat = 0 := by
                have r16775 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
                have e16776 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                have e16777 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                have b16778 := hb (x (-2) 3)
                have b16779 := hb (x (-1) 2)
                have b16780 := hb (x 0 13)
                have b16781 := hb (x 1 12)
                clear * - r16775 e16776 e16777 b16778 b16779 b16780 b16781 d16770 g14 f16207
                omega
              have d16782 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                have r16783 := hand1 (x (-2) 3) (x (-2) 14)
                have b16784 := hb (x (-2) 3)
                have b16785 := hb (x (-2) 3 && x (-2) 14)
                clear * - r16783 b16784 b16785 d16774
                omega
              have d16786 : (x (-2) 11).toNat = 0 := by
                have r16787 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
                have b16788 := hb (x (-2) 3)
                have b16789 := hb (x (-2) 11)
                clear * - r16787 b16788 b16789 d16774
                omega
              have d16790 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
                have r16791 := hand2 (x (-2) 1) (x (-2) 11)
                have b16792 := hb (x (-2) 11)
                have b16793 := hb (x (-2) 1 && x (-2) 11)
                clear * - r16791 b16792 b16793 d16786
                omega
              have d16794 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
                have r16795 := hand2 (x (-2) 2) (x (-2) 11)
                have b16796 := hb (x (-2) 11)
                have b16797 := hb (x (-2) 2 && x (-2) 11)
                clear * - r16795 b16796 b16797 d16786
                omega
              have d16798 : (x 1 5 && x 1 14).toNat = 1 := by
                have r16799 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
                have b16800 := hb (x 0 6)
                have b16801 := hb (x 6 9)
                have b16802 := hb (x 5 1 && x 5 10)
                have b16803 := hb (x 4 2 && x 4 11)
                have b16804 := hb (x 3 3 && x 3 12)
                have b16805 := hb (x 2 4 && x 2 13)
                have b16806 := hb (x 1 5 && x 1 14)
                clear * - r16799 b16800 b16801 b16802 b16803 b16804 b16805 b16806 d15429 d15469 d15501 d16683 d16233 f15584
                omega
              have d16807 : (x 1 5).toNat = 1 := by
                have r16808 := hand1 (x 1 5) (x 1 14)
                have b16809 := hb (x 1 5)
                have b16810 := hb (x 1 5 && x 1 14)
                clear * - r16808 b16809 b16810 d16798
                omega
              have d16811 : (x 6 8).toNat = 0 := by
                have r16812 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e16813 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e16814 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e16815 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e16816 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e16817 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e16818 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b16819 := hb (x (-1) 7)
                have b16820 := hb (x 0 6)
                have b16821 := hb (x 1 5)
                have b16822 := hb (x 2 4)
                have b16823 := hb (x 3 11)
                have b16824 := hb (x 4 10)
                have b16825 := hb (x 5 9)
                have b16826 := hb (x 6 8)
                clear * - r16812 e16813 e16814 e16815 e16816 e16817 e16818 b16819 b16820 b16821 b16822 b16823 b16824 b16825 b16826 d16229 d16807 f15584
                omega
              have d16827 : (x 6 2 && x 6 8).toNat = 0 := by
                have r16828 := hand2 (x 6 2) (x 6 8)
                have b16829 := hb (x 6 8)
                have b16830 := hb (x 6 2 && x 6 8)
                clear * - r16828 b16829 b16830 d16811
                omega
              have d16831 : (x 5 9).toNat = 0 := by
                have r16832 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e16833 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e16834 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e16835 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e16836 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e16837 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e16838 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b16839 := hb (x (-1) 7)
                have b16840 := hb (x 0 6)
                have b16841 := hb (x 1 5)
                have b16842 := hb (x 2 4)
                have b16843 := hb (x 3 11)
                have b16844 := hb (x 4 10)
                have b16845 := hb (x 5 9)
                have b16846 := hb (x 6 8)
                clear * - r16832 e16833 e16834 e16835 e16836 e16837 e16838 b16839 b16840 b16841 b16842 b16843 b16844 b16845 b16846 d16811 d16229 d16807 f15584
                omega
              have d16847 : (x 5 3 && x 5 9).toNat = 0 := by
                have r16848 := hand2 (x 5 3) (x 5 9)
                have b16849 := hb (x 5 9)
                have b16850 := hb (x 5 3 && x 5 9)
                clear * - r16848 b16849 b16850 d16831
                omega
              have d16851 : (x 4 10).toNat = 0 := by
                have r16852 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e16853 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e16854 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e16855 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e16856 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e16857 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e16858 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b16859 := hb (x (-1) 7)
                have b16860 := hb (x 0 6)
                have b16861 := hb (x 1 5)
                have b16862 := hb (x 2 4)
                have b16863 := hb (x 3 11)
                have b16864 := hb (x 4 10)
                have b16865 := hb (x 5 9)
                have b16866 := hb (x 6 8)
                clear * - r16852 e16853 e16854 e16855 e16856 e16857 e16858 b16859 b16860 b16861 b16862 b16863 b16864 b16865 b16866 d16811 d16831 d16229 d16807 f15584
                omega
              have d16867 : (x 3 11).toNat = 0 := by
                have r16868 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e16869 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e16870 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e16871 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e16872 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e16873 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e16874 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b16875 := hb (x (-1) 7)
                have b16876 := hb (x 0 6)
                have b16877 := hb (x 1 5)
                have b16878 := hb (x 2 4)
                have b16879 := hb (x 3 11)
                have b16880 := hb (x 4 10)
                have b16881 := hb (x 5 9)
                have b16882 := hb (x 6 8)
                clear * - r16868 e16869 e16870 e16871 e16872 e16873 e16874 b16875 b16876 b16877 b16878 b16879 b16880 b16881 b16882 d16811 d16831 d16851 d16229 d16807 f15584
                omega
              cases h16883 : x (-1) 4
              · have f16884 : (x (-1) 4).toNat = 0 := by rw [h16883]; rfl
                cases h16885 : x 1 7
                · have f16886 : (x 1 7).toNat = 0 := by rw [h16885]; rfl
                  have d16887 : (x 1 7 && x 1 14).toNat = 0 := by
                    have r16888 := hand1 (x 1 7) (x 1 14)
                    have b16889 := hb (x 1 7)
                    have b16890 := hb (x 1 7 && x 1 14)
                    clear * - r16888 b16889 b16890 f16886
                    omega
                  have d16891 : (x 1 7 && x 1 13).toNat = 0 := by
                    have r16892 := hand1 (x 1 7) (x 1 13)
                    have b16893 := hb (x 1 7)
                    have b16894 := hb (x 1 7 && x 1 13)
                    clear * - r16892 b16893 b16894 f16886
                    omega
                  have d16895 : (x 1 7 && x 1 11).toNat = 0 := by
                    have r16896 := hand1 (x 1 7) (x 1 11)
                    have b16897 := hb (x 1 7)
                    have b16898 := hb (x 1 7 && x 1 11)
                    clear * - r16896 b16897 b16898 f16886
                    omega
                  have d16899 : (x 8 7).toNat = 1 := by
                    have r16900 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := hcov7 8
                    have b16901 := hb (x 0 8)
                    have b16902 := hb (x 8 7)
                    have b16903 := hb (x 7 1 && x 7 8)
                    have b16904 := hb (x 6 2 && x 6 9)
                    have b16905 := hb (x 5 3 && x 5 10)
                    have b16906 := hb (x 4 4 && x 4 11)
                    have b16907 := hb (x 3 5 && x 3 12)
                    have b16908 := hb (x 2 6 && x 2 13)
                    have b16909 := hb (x 1 7 && x 1 14)
                    clear * - r16900 b16901 b16902 b16903 b16904 b16905 b16906 b16907 b16908 b16909 d15421 d15445 d15473 d15505 d16687 d16178 d16887 f15586
                    omega
                  have d16910 : (x 15 8).toNat = 0 := by
                    have r16911 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                    have e16912 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e16913 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e16914 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e16915 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e16916 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e16917 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b16918 := hb (x 8 7)
                    have b16919 := hb (x 9 6)
                    have b16920 := hb (x 10 5)
                    have b16921 := hb (x 11 4)
                    have b16922 := hb (x 12 11)
                    have b16923 := hb (x 13 10)
                    have b16924 := hb (x 14 9)
                    have b16925 := hb (x 15 8)
                    clear * - r16911 e16912 e16913 e16914 e16915 e16916 e16917 b16918 b16919 b16920 b16921 b16922 b16923 b16924 b16925 d16899
                    omega
                  have d16926 : (x 14 9).toNat = 0 := by
                    have r16927 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                    have e16928 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e16929 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e16930 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e16931 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e16932 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e16933 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b16934 := hb (x 8 7)
                    have b16935 := hb (x 9 6)
                    have b16936 := hb (x 10 5)
                    have b16937 := hb (x 11 4)
                    have b16938 := hb (x 12 11)
                    have b16939 := hb (x 13 10)
                    have b16940 := hb (x 14 9)
                    have b16941 := hb (x 15 8)
                    clear * - r16927 e16928 e16929 e16930 e16931 e16932 e16933 b16934 b16935 b16936 b16937 b16938 b16939 b16940 b16941 d16910 d16899
                    omega
                  have d16942 : (x 13 10).toNat = 0 := by
                    have r16943 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                    have e16944 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e16945 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e16946 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e16947 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e16948 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e16949 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b16950 := hb (x 8 7)
                    have b16951 := hb (x 9 6)
                    have b16952 := hb (x 10 5)
                    have b16953 := hb (x 11 4)
                    have b16954 := hb (x 12 11)
                    have b16955 := hb (x 13 10)
                    have b16956 := hb (x 14 9)
                    have b16957 := hb (x 15 8)
                    clear * - r16943 e16944 e16945 e16946 e16947 e16948 e16949 b16950 b16951 b16952 b16953 b16954 b16955 b16956 b16957 d16910 d16926 d16899
                    omega
                  have d16958 : (x 13 1 && x 13 10).toNat = 0 := by
                    have r16959 := hand2 (x 13 1) (x 13 10)
                    have b16960 := hb (x 13 10)
                    have b16961 := hb (x 13 1 && x 13 10)
                    clear * - r16959 b16960 b16961 d16942
                    omega
                  have d16962 : (x 12 11).toNat = 0 := by
                    have r16963 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                    have e16964 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e16965 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e16966 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e16967 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e16968 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e16969 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b16970 := hb (x 8 7)
                    have b16971 := hb (x 9 6)
                    have b16972 := hb (x 10 5)
                    have b16973 := hb (x 11 4)
                    have b16974 := hb (x 12 11)
                    have b16975 := hb (x 13 10)
                    have b16976 := hb (x 14 9)
                    have b16977 := hb (x 15 8)
                    clear * - r16963 e16964 e16965 e16966 e16967 e16968 e16969 b16970 b16971 b16972 b16973 b16974 b16975 b16976 b16977 d16910 d16926 d16942 d16899
                    omega
                  have d16978 : (x 12 2 && x 12 11).toNat = 0 := by
                    have r16979 := hand2 (x 12 2) (x 12 11)
                    have b16980 := hb (x 12 11)
                    have b16981 := hb (x 12 2 && x 12 11)
                    clear * - r16979 b16980 b16981 d16962
                    omega
                  have r16982 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := hcount 8
                  have r16983 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
                  have r16984 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
                  have r16985 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                  have e16986 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                  have e16987 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                  have e16988 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                  have e16989 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                  have e16990 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                  have e16991 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                  have r16992 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
                  have e16993 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e16994 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have r16995 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
                  have e16996 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                  have e16997 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                  have r16998 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
                  have e16999 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                  have e17000 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                  have r17001 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
                  have r17002 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
                  have r17003 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := hcov4 8
                  have e17004 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                  have e17005 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                  have r17006 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := hcov6 8
                  have r17007 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
                  have r17008 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := hcov9 14
                  have r17009 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
                  have r17010 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
                  have r17011 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
                  have r17012 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
                  have r17013 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                  have r17014 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                  have r17015 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
                  have r17016 := hand2 (x 6 2) (x 6 6)
                  have r17017 := hand2 (x 5 3) (x 5 7)
                  have r17018 := hand2 (x 7 1) (x 7 7)
                  have r17019 := hand1 (x (-4) 4) (x (-4) 13)
                  have r17020 := hand1 (x (-5) 5) (x (-5) 14)
                  have r17021 := hand1 (x 11 3) (x 11 12)
                  have r17022 := hand1 (x 10 4) (x 10 13)
                  have r17023 := hand1 (x 9 5) (x 9 14)
                  have r17024 := hand1 (x 11 1) (x 11 12)
                  have r17025 := hand1 (x 10 2) (x 10 13)
                  have r17026 := hand1 (x 9 3) (x 9 14)
                  have r17027 := hand1 (x (-5) 1) (x (-5) 14)
                  have r17028 := hand2 (x (-4) 1) (x (-4) 14)
                  have b17029 := hb (x (-7) 3)
                  have b17030 := hb (x (-7) 7)
                  have b17031 := hb (x (-6) 2)
                  have b17032 := hb (x (-6) 3)
                  have b17033 := hb (x (-6) 6)
                  have b17034 := hb (x (-6) 14)
                  have b17035 := hb (x (-5) 1)
                  have b17036 := hb (x (-5) 2)
                  have b17037 := hb (x (-5) 5)
                  have b17038 := hb (x (-5) 13)
                  have b17039 := hb (x (-4) 4)
                  have b17040 := hb (x (-4) 12)
                  have b17041 := hb (x (-4) 13)
                  have b17042 := hb (x (-4) 14)
                  have b17043 := hb (x (-3) 4)
                  have b17044 := hb (x (-3) 11)
                  have b17045 := hb (x (-3) 12)
                  have b17046 := hb (x (-3) 13)
                  have b17047 := hb (x (-2) 10)
                  have b17048 := hb (x (-2) 14)
                  have b17049 := hb (x (-1) 9)
                  have b17050 := hb (x (-1) 13)
                  have b17051 := hb (x 0 8)
                  have b17052 := hb (x 0 9)
                  have b17053 := hb (x 0 12)
                  have b17054 := hb (x 0 14)
                  have b17055 := hb (x 1 7)
                  have b17056 := hb (x 1 11)
                  have b17057 := hb (x 1 13)
                  have b17058 := hb (x 2 6)
                  have b17059 := hb (x 2 10)
                  have b17060 := hb (x 2 12)
                  have b17061 := hb (x 3 5)
                  have b17062 := hb (x 3 9)
                  have b17063 := hb (x 3 11)
                  have b17064 := hb (x 4 4)
                  have b17065 := hb (x 4 8)
                  have b17066 := hb (x 4 10)
                  have b17067 := hb (x 5 3)
                  have b17068 := hb (x 5 7)
                  have b17069 := hb (x 5 9)
                  have b17070 := hb (x 6 2)
                  have b17071 := hb (x 6 6)
                  have b17072 := hb (x 6 8)
                  have b17073 := hb (x 7 1)
                  have b17074 := hb (x 7 5)
                  have b17075 := hb (x 7 7)
                  have b17076 := hb (x 7 13)
                  have b17077 := hb (x 8 4)
                  have b17078 := hb (x 8 6)
                  have b17079 := hb (x 8 12)
                  have b17080 := hb (x 8 14)
                  have b17081 := hb (x 9 3)
                  have b17082 := hb (x 9 5)
                  have b17083 := hb (x 10 2)
                  have b17084 := hb (x 10 4)
                  have b17085 := hb (x 11 1)
                  have b17086 := hb (x 11 3)
                  have b17087 := hb (x 12 2)
                  have b17088 := hb (x 12 11)
                  have b17089 := hb (x 13 1)
                  have b17090 := hb (x 14 9)
                  have b17091 := hb (x 6 2 && x 6 6)
                  have b17092 := hb (x 5 3 && x 5 7)
                  have b17093 := hb (x 4 4 && x 4 8)
                  have b17094 := hb (x 3 5 && x 3 9)
                  have b17095 := hb (x 2 6 && x 2 10)
                  have b17096 := hb (x 1 7 && x 1 11)
                  have b17097 := hb (x 0 8 && x 0 12)
                  have b17098 := hb (x (-1) 9 && x (-1) 13)
                  have b17099 := hb (x 7 1 && x 7 7)
                  have b17100 := hb (x 6 2 && x 6 8)
                  have b17101 := hb (x 5 3 && x 5 9)
                  have b17102 := hb (x 4 4 && x 4 10)
                  have b17103 := hb (x 3 5 && x 3 11)
                  have b17104 := hb (x 2 6 && x 2 12)
                  have b17105 := hb (x 1 7 && x 1 13)
                  have b17106 := hb (x 0 8 && x 0 14)
                  have b17107 := hb (x (-1) 1 && x (-1) 10)
                  have b17108 := hb (x (-2) 2 && x (-2) 11)
                  have b17109 := hb (x (-3) 3 && x (-3) 12)
                  have b17110 := hb (x (-4) 4 && x (-4) 13)
                  have b17111 := hb (x (-5) 5 && x (-5) 14)
                  have b17112 := hb (x 13 1 && x 13 10)
                  have b17113 := hb (x 12 2 && x 12 11)
                  have b17114 := hb (x 11 3 && x 11 12)
                  have b17115 := hb (x 10 4 && x 10 13)
                  have b17116 := hb (x 9 5 && x 9 14)
                  have b17117 := hb (x 0 1 && x 0 12)
                  have b17118 := hb (x (-1) 2 && x (-1) 13)
                  have b17119 := hb (x (-2) 3 && x (-2) 14)
                  have b17120 := hb (x 11 1 && x 11 12)
                  have b17121 := hb (x 10 2 && x 10 13)
                  have b17122 := hb (x 9 3 && x 9 14)
                  have b17123 := hb (x (-5) 1 && x (-5) 14)
                  have b17124 := hb (x (-4) 1 && x (-4) 14)
                  linarith only [r16982, r16983, r16984, r16985, e16986, e16987, e16988, e16989, e16990, e16991, r16992, e16993, e16994, r16995, e16996, e16997, r16998, e16999, e17000, r17001, r17002, r17003, e17004, e17005, r17006, r17007, r17008, r17009, r17010, r17011, r17012, r17013, r17014, r17015, r17016, r17017, r17018, r17019, r17020, r17021, r17022, r17023, r17024, r17025, r17026, r17027, r17028, b17029, b17030, b17031, b17032, b17033, b17034, b17035, b17036, b17037, b17038, b17039, b17040, b17041, b17042, b17043, b17044, b17045, b17046, b17047, b17048, b17049, b17050, b17051, b17052, b17053, b17054, b17055, b17056, b17057, b17058, b17059, b17060, b17061, b17062, b17063, b17064, b17065, b17066, b17067, b17068, b17069, b17070, b17071, b17072, b17073, b17074, b17075, b17076, b17077, b17078, b17079, b17080, b17081, b17082, b17083, b17084, b17085, b17086, b17087, b17088, b17089, b17090, b17091, b17092, b17093, b17094, b17095, b17096, b17097, b17098, b17099, b17100, b17101, b17102, b17103, b17104, b17105, b17106, b17107, b17108, b17109, b17110, b17111, b17112, b17113, b17114, b17115, b17116, b17117, b17118, b17119, b17120, b17121, b17122, b17123, b17124, g1, g2, g3, g5, g6, f15586, g11, g13, g15, f16886, d16212, d16174, d16202, d16217, d16746, d16867, d16726, d16851, d16831, d16811, d16962, d16926, d16734, d16754, d16186, d16895, g16, g17, d16827, d16847, d16730, d16750, d16182, d16891, d15587, g19, d16794, g20, d16958, d16978, g28, g29, d16782]
                · have f17125 : (x 1 7).toNat = 1 := by rw [h16885]; rfl
                  have d17126 : (x 8 8).toNat = 0 := by
                    have r17127 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                    have e17128 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e17129 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e17130 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e17131 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e17132 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e17133 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b17134 := hb (x 1 7)
                    have b17135 := hb (x 2 6)
                    have b17136 := hb (x 3 5)
                    have b17137 := hb (x 4 4)
                    have b17138 := hb (x 5 11)
                    have b17139 := hb (x 6 10)
                    have b17140 := hb (x 7 9)
                    have b17141 := hb (x 8 8)
                    clear * - r17127 e17128 e17129 e17130 e17131 e17132 e17133 b17134 b17135 b17136 b17137 b17138 b17139 b17140 b17141 d16726 d16746 d16174 f17125
                    omega
                  have d17142 : (x 7 9).toNat = 0 := by
                    have r17143 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                    have e17144 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e17145 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e17146 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e17147 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e17148 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e17149 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b17150 := hb (x 1 7)
                    have b17151 := hb (x 2 6)
                    have b17152 := hb (x 3 5)
                    have b17153 := hb (x 4 4)
                    have b17154 := hb (x 5 11)
                    have b17155 := hb (x 6 10)
                    have b17156 := hb (x 7 9)
                    have b17157 := hb (x 8 8)
                    clear * - r17143 e17144 e17145 e17146 e17147 e17148 e17149 b17150 b17151 b17152 b17153 b17154 b17155 b17156 b17157 d17126 d16726 d16746 d16174 f17125
                    omega
                  have d17158 : (x 6 10).toNat = 0 := by
                    have r17159 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                    have e17160 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e17161 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e17162 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e17163 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e17164 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e17165 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b17166 := hb (x 1 7)
                    have b17167 := hb (x 2 6)
                    have b17168 := hb (x 3 5)
                    have b17169 := hb (x 4 4)
                    have b17170 := hb (x 5 11)
                    have b17171 := hb (x 6 10)
                    have b17172 := hb (x 7 9)
                    have b17173 := hb (x 8 8)
                    clear * - r17159 e17160 e17161 e17162 e17163 e17164 e17165 b17166 b17167 b17168 b17169 b17170 b17171 b17172 b17173 d17126 d17142 d16726 d16746 d16174 f17125
                    omega
                  have d17174 : (x 6 1 && x 6 10).toNat = 0 := by
                    have r17175 := hand2 (x 6 1) (x 6 10)
                    have b17176 := hb (x 6 10)
                    have b17177 := hb (x 6 1 && x 6 10)
                    clear * - r17175 b17176 b17177 d17158
                    omega
                  have d17178 : (x 5 2 && x 5 11).toNat = 1 := by
                    have r17179 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := hcov9 7
                    have b17180 := hb (x 1 6)
                    have b17181 := hb (x 7 9)
                    have b17182 := hb (x 6 1 && x 6 10)
                    have b17183 := hb (x 5 2 && x 5 11)
                    have b17184 := hb (x 4 3 && x 4 12)
                    have b17185 := hb (x 3 4 && x 3 13)
                    have b17186 := hb (x 2 5 && x 2 14)
                    clear * - r17179 b17180 b17181 b17182 b17183 b17184 b17185 b17186 d17142 d17174 d16722 d15533 d15553 d15557
                    omega
                  have d17187 : (x 5 11).toNat = 1 := by
                    have r17188 := hand2 (x 5 2) (x 5 11)
                    have b17189 := hb (x 5 11)
                    have b17190 := hb (x 5 2 && x 5 11)
                    clear * - r17188 b17189 b17190 d17178
                    omega
                  have r17191 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                  have e17192 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e17193 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e17194 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e17195 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e17196 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e17197 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b17198 := hb (x 1 7)
                  have b17199 := hb (x 2 6)
                  have b17200 := hb (x 3 5)
                  have b17201 := hb (x 4 4)
                  have b17202 := hb (x 5 11)
                  have b17203 := hb (x 6 10)
                  have b17204 := hb (x 7 9)
                  have b17205 := hb (x 8 8)
                  linarith only [r17191, e17192, e17193, e17194, e17195, e17196, e17197, b17198, b17199, b17200, b17201, b17202, b17203, b17204, b17205, d17126, d17142, d17158, d17187, d16726, d16746, d16174, f17125]
              · have f17206 : (x (-1) 4).toNat = 1 := by rw [h16883]; rfl
                have d17207 : (x (-1) 12).toNat = 1 := by
                  have r17208 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                  have b17209 := hb (x (-1) 4)
                  have b17210 := hb (x (-1) 12)
                  clear * - r17208 b17209 b17210 f17206
                  omega
                have d17211 : (x (-2) 13).toNat = 0 := by
                  have r17212 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                  have e17213 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e17214 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b17215 := hb (x (-4) 3)
                  have b17216 := hb (x (-3) 2)
                  have b17217 := hb (x (-2) 13)
                  have b17218 := hb (x (-1) 12)
                  clear * - r17212 e17213 e17214 b17215 b17216 b17217 b17218 d17207
                  omega
                have d17219 : (x (-4) 2).toNat = 1 := by
                  have r17220 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
                  have b17221 := hb (x (-4) 2)
                  have b17222 := hb (x (-2) 13)
                  have b17223 := hb (x (-3) 1 && x (-3) 14)
                  clear * - r17220 b17221 b17222 b17223 d17211 g31
                  omega
                have d17224 : (x (-4) 14).toNat = 1 := by
                  have r17225 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                  have b17226 := hb (x (-4) 2)
                  have b17227 := hb (x (-4) 14)
                  clear * - r17225 b17226 b17227 d17219
                  omega
                have d17228 : (x (-5) 1).toNat = 0 := by
                  have r17229 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
                  have b17230 := hb (x (-5) 1)
                  have b17231 := hb (x (-4) 14)
                  clear * - r17229 b17230 b17231 d17224
                  omega
                have d17232 : (x (-5) 13).toNat = 0 := by
                  have r17233 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                  have b17234 := hb (x (-5) 1)
                  have b17235 := hb (x (-5) 13)
                  clear * - r17233 b17234 b17235 d17228
                  omega
                have d17236 : (x (-3) 2).toNat = 0 := by
                  have r17237 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                  have e17238 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e17239 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b17240 := hb (x (-4) 3)
                  have b17241 := hb (x (-3) 2)
                  have b17242 := hb (x (-2) 13)
                  have b17243 := hb (x (-1) 12)
                  clear * - r17237 e17238 e17239 b17240 b17241 b17242 b17243 d17207 d17211
                  omega
                have d17244 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                  have r17245 := hand1 (x (-3) 2) (x (-3) 12)
                  have b17246 := hb (x (-3) 2)
                  have b17247 := hb (x (-3) 2 && x (-3) 12)
                  clear * - r17245 b17246 b17247 d17236
                  omega
                have d17248 : (x (-4) 3).toNat = 0 := by
                  have r17249 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                  have e17250 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e17251 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b17252 := hb (x (-4) 3)
                  have b17253 := hb (x (-3) 2)
                  have b17254 := hb (x (-2) 13)
                  have b17255 := hb (x (-1) 12)
                  clear * - r17249 e17250 e17251 b17252 b17253 b17254 b17255 d17207 d17211 d17236
                  omega
                have d17256 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                  have r17257 := hand1 (x (-4) 3) (x (-4) 14)
                  have b17258 := hb (x (-4) 3)
                  have b17259 := hb (x (-4) 3 && x (-4) 14)
                  clear * - r17257 b17258 b17259 d17248
                  omega
                have d17260 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                  have r17261 := hand1 (x (-4) 3) (x (-4) 13)
                  have b17262 := hb (x (-4) 3)
                  have b17263 := hb (x (-4) 3 && x (-4) 13)
                  clear * - r17261 b17262 b17263 d17248
                  omega
                have d17264 : (x (-2) 12).toNat = 0 := by
                  have r17265 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
                  have e17266 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e17267 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have b17268 := hb (x (-5) 3)
                  have b17269 := hb (x (-4) 2)
                  have b17270 := hb (x (-3) 13)
                  have b17271 := hb (x (-2) 12)
                  clear * - r17265 e17266 e17267 b17268 b17269 b17270 b17271 g2 d17219
                  omega
                have d17272 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                  have r17273 := hand2 (x (-2) 1) (x (-2) 12)
                  have b17274 := hb (x (-2) 12)
                  have b17275 := hb (x (-2) 1 && x (-2) 12)
                  clear * - r17273 b17274 b17275 d17264
                  omega
                have d17276 : (x (-5) 4).toNat = 1 := by
                  have r17277 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := hcov11 (-1)
                  have b17278 := hb (x (-5) 4)
                  have b17279 := hb (x (-1) 11)
                  have b17280 := hb (x (-2) 1 && x (-2) 12)
                  have b17281 := hb (x (-3) 2 && x (-3) 13)
                  have b17282 := hb (x (-4) 3 && x (-4) 14)
                  clear * - r17277 b17278 b17279 b17280 b17281 b17282 d16245 d17272 g25 d17256
                  omega
                have d17283 : (x (-5) 12).toNat = 1 := by
                  have r17284 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                  have b17285 := hb (x (-5) 4)
                  have b17286 := hb (x (-5) 12)
                  clear * - r17284 b17285 b17286 d17276
                  omega
                have d17287 : (x (-6) 13).toNat = 0 := by
                  have r17288 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
                  have e17289 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                  have e17290 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                  have b17291 := hb (x (-8) 3)
                  have b17292 := hb (x (-7) 2)
                  have b17293 := hb (x (-6) 13)
                  have b17294 := hb (x (-5) 12)
                  clear * - r17288 e17289 e17290 b17291 b17292 b17293 b17294 d17283
                  omega
                have d17295 : (x (-6) 5).toNat = 0 := by
                  have r17296 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                  have b17297 := hb (x (-6) 5)
                  have b17298 := hb (x (-6) 13)
                  clear * - r17296 b17297 b17298 d17287
                  omega
                have d17299 : (x (-7) 2).toNat = 0 := by
                  have r17300 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
                  have e17301 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                  have e17302 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                  have b17303 := hb (x (-8) 3)
                  have b17304 := hb (x (-7) 2)
                  have b17305 := hb (x (-6) 13)
                  have b17306 := hb (x (-5) 12)
                  clear * - r17300 e17301 e17302 b17303 b17304 b17305 b17306 d17283 d17287
                  omega
                have d17307 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                  have r17308 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
                  have b17309 := hb (x (-7) 2)
                  have b17310 := hb (x (-5) 13)
                  have b17311 := hb (x (-6) 1 && x (-6) 14)
                  clear * - r17308 b17309 b17310 b17311 d17232 d17299
                  omega
                have d17312 : (x (-6) 1).toNat = 1 := by
                  have r17313 := hand1 (x (-6) 1) (x (-6) 14)
                  have b17314 := hb (x (-6) 1)
                  have b17315 := hb (x (-6) 1 && x (-6) 14)
                  clear * - r17313 b17314 b17315 d17307
                  omega
                have d17316 : (x (-5) 14).toNat = 0 := by
                  have r17317 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
                  have b17318 := hb (x (-6) 1)
                  have b17319 := hb (x (-5) 14)
                  clear * - r17317 b17318 b17319 d17312
                  omega
                have d17320 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                  have r17321 := hand2 (x (-5) 4) (x (-5) 14)
                  have b17322 := hb (x (-5) 14)
                  have b17323 := hb (x (-5) 4 && x (-5) 14)
                  clear * - r17321 b17322 b17323 d17316
                  omega
                have r17324 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
                have b17325 := hb (x (-6) 5)
                have b17326 := hb (x (-1) 10)
                have b17327 := hb (x (-2) 1 && x (-2) 11)
                have b17328 := hb (x (-3) 2 && x (-3) 12)
                have b17329 := hb (x (-4) 3 && x (-4) 13)
                have b17330 := hb (x (-5) 4 && x (-5) 14)
                linarith only [r17324, b17325, b17326, b17327, b17328, b17329, b17330, d16208, d16790, d17244, d17260, d17320, d17295]
          · have f17331 : (x (-1) 2).toNat = 1 := by rw [h16206]; rfl
            have d17332 : (x (-1) 14).toNat = 1 := by
              have r17333 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
              have b17334 := hb (x (-1) 2)
              have b17335 := hb (x (-1) 14)
              clear * - r17333 b17334 b17335 f17331
              omega
            have d17336 : (x (-2) 1).toNat = 0 := by
              have r17337 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
              have b17338 := hb (x (-2) 1)
              have b17339 := hb (x (-1) 14)
              clear * - r17337 b17338 b17339 d17332
              omega
            have d17340 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
              have r17341 := hand1 (x (-2) 1) (x (-2) 14)
              have b17342 := hb (x (-2) 1)
              have b17343 := hb (x (-2) 1 && x (-2) 14)
              clear * - r17341 b17342 b17343 d17336
              omega
            have d17344 : (x (-2) 13).toNat = 0 := by
              have r17345 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b17346 := hb (x (-2) 1)
              have b17347 := hb (x (-2) 13)
              clear * - r17345 b17346 b17347 d17336
              omega
            have d17348 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
              have r17349 := hand2 (x (-2) 2) (x (-2) 13)
              have b17350 := hb (x (-2) 13)
              have b17351 := hb (x (-2) 2 && x (-2) 13)
              clear * - r17349 b17350 b17351 d17344
              omega
            have d17352 : (x (-3) 2).toNat = 1 := by
              have r17353 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
              have b17354 := hb (x (-3) 2)
              have b17355 := hb (x (-1) 13)
              have b17356 := hb (x (-2) 1 && x (-2) 14)
              clear * - r17353 b17354 b17355 b17356 g6 d17340
              omega
            have d17357 : (x (-3) 14).toNat = 1 := by
              have r17358 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
              have b17359 := hb (x (-3) 2)
              have b17360 := hb (x (-3) 14)
              clear * - r17358 b17359 b17360 d17352
              omega
            have d17361 : (x (-4) 1).toNat = 0 := by
              have r17362 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
              have b17363 := hb (x (-4) 1)
              have b17364 := hb (x (-3) 14)
              clear * - r17362 b17363 b17364 d17357
              omega
            have d17365 : (x (-4) 13).toNat = 0 := by
              have r17366 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
              have b17367 := hb (x (-4) 1)
              have b17368 := hb (x (-4) 13)
              clear * - r17366 b17367 b17368 d17361
              omega
            have d17369 : (x (-4) 2).toNat = 1 := by
              have r17370 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
              have b17371 := hb (x (-4) 2)
              have b17372 := hb (x (-2) 13)
              have b17373 := hb (x (-3) 1 && x (-3) 14)
              clear * - r17370 b17371 b17372 b17373 d17344 g31
              omega
            have d17374 : (x (-4) 14).toNat = 1 := by
              have r17375 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
              have b17376 := hb (x (-4) 2)
              have b17377 := hb (x (-4) 14)
              clear * - r17375 b17376 b17377 d17369
              omega
            have d17378 : (x (-5) 1).toNat = 0 := by
              have r17379 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
              have b17380 := hb (x (-5) 1)
              have b17381 := hb (x (-4) 14)
              clear * - r17379 b17380 b17381 d17374
              omega
            have d17382 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
              have r17383 := hand1 (x (-5) 1) (x (-5) 14)
              have b17384 := hb (x (-5) 1)
              have b17385 := hb (x (-5) 1 && x (-5) 14)
              clear * - r17383 b17384 b17385 d17378
              omega
            have d17386 : (x (-5) 13).toNat = 0 := by
              have r17387 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
              have b17388 := hb (x (-5) 1)
              have b17389 := hb (x (-5) 13)
              clear * - r17387 b17388 b17389 d17378
              omega
            have d17390 : (x (-6) 2).toNat = 1 := by
              have r17391 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
              have b17392 := hb (x (-6) 2)
              have b17393 := hb (x (-4) 13)
              have b17394 := hb (x (-5) 1 && x (-5) 14)
              clear * - r17391 b17392 b17393 b17394 d17365 d17382
              omega
            have d17395 : (x (-4) 12).toNat = 0 := by
              have r17396 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
              have e17397 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e17398 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b17399 := hb (x (-7) 3)
              have b17400 := hb (x (-6) 2)
              have b17401 := hb (x (-5) 13)
              have b17402 := hb (x (-4) 12)
              clear * - r17396 e17397 e17398 b17399 b17400 b17401 b17402 d17386 d17390
              omega
            have d17403 : (x (-4) 4).toNat = 0 := by
              have r17404 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
              have b17405 := hb (x (-4) 4)
              have b17406 := hb (x (-4) 12)
              clear * - r17404 b17405 b17406 d17395
              omega
            have r17407 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
            have b17408 := hb (x (-4) 4)
            have b17409 := hb (x 0 11)
            have b17410 := hb (x (-1) 1 && x (-1) 12)
            have b17411 := hb (x (-2) 2 && x (-2) 13)
            have b17412 := hb (x (-3) 3 && x (-3) 14)
            linarith only [r17407, b17408, b17409, b17410, b17411, b17412, d15579, g26, d17348, g27, d17403]
      · have f17413 : (x 0 8).toNat = 1 := by rw [h15585]; rfl
        have d17414 : (x (-2) 10).toNat = 0 := by
          have r17415 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e17416 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e17417 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e17418 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e17419 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e17420 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e17421 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b17422 := hb (x (-7) 7)
          have b17423 := hb (x (-6) 6)
          have b17424 := hb (x (-5) 5)
          have b17425 := hb (x (-4) 4)
          have b17426 := hb (x (-3) 11)
          have b17427 := hb (x (-2) 10)
          have b17428 := hb (x (-1) 9)
          have b17429 := hb (x 0 8)
          clear * - r17415 e17416 e17417 e17418 e17419 e17420 e17421 b17422 b17423 b17424 b17425 b17426 b17427 b17428 b17429 f17413 g5 g1
          omega
        have d17430 : (x (-4) 4).toNat = 0 := by
          have r17431 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e17432 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e17433 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e17434 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e17435 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e17436 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e17437 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b17438 := hb (x (-7) 7)
          have b17439 := hb (x (-6) 6)
          have b17440 := hb (x (-5) 5)
          have b17441 := hb (x (-4) 4)
          have b17442 := hb (x (-3) 11)
          have b17443 := hb (x (-2) 10)
          have b17444 := hb (x (-1) 9)
          have b17445 := hb (x 0 8)
          clear * - r17431 e17432 e17433 e17434 e17435 e17436 e17437 b17438 b17439 b17440 b17441 b17442 b17443 b17444 b17445 f17413 g5 d17414 g1
          omega
        have d17446 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
          have r17447 := hand1 (x (-4) 4) (x (-4) 13)
          have b17448 := hb (x (-4) 4)
          have b17449 := hb (x (-4) 4 && x (-4) 13)
          clear * - r17447 b17448 b17449 d17430
          omega
        have d17450 : (x (-2) 2 && x (-2) 13).toNat = 1 := by
          have r17451 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
          have b17452 := hb (x (-4) 4)
          have b17453 := hb (x 0 11)
          have b17454 := hb (x (-1) 1 && x (-1) 12)
          have b17455 := hb (x (-2) 2 && x (-2) 13)
          have b17456 := hb (x (-3) 3 && x (-3) 14)
          clear * - r17451 b17452 b17453 b17454 b17455 b17456 d15579 g26 g27 d17430
          omega
        have d17457 : (x (-2) 13).toNat = 1 := by
          have r17458 := hand2 (x (-2) 2) (x (-2) 13)
          have b17459 := hb (x (-2) 13)
          have b17460 := hb (x (-2) 2 && x (-2) 13)
          clear * - r17458 b17459 b17460 d17450
          omega
        have d17461 : (x (-2) 1).toNat = 1 := by
          have r17462 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b17463 := hb (x (-2) 1)
          have b17464 := hb (x (-2) 13)
          clear * - r17462 b17463 b17464 d17457
          omega
        have d17465 : (x (-1) 14).toNat = 0 := by
          have r17466 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
          have b17467 := hb (x (-2) 1)
          have b17468 := hb (x (-1) 14)
          clear * - r17466 b17467 b17468 d17461
          omega
        have d17469 : (x (-1) 6).toNat = 0 := by
          have r17470 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
          have b17471 := hb (x (-1) 6)
          have b17472 := hb (x (-1) 14)
          clear * - r17470 b17471 b17472 d17465
          omega
        have d17473 : (x (-1) 2).toNat = 0 := by
          have r17474 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b17475 := hb (x (-1) 2)
          have b17476 := hb (x (-1) 14)
          clear * - r17474 b17475 b17476 d17465
          omega
        have d17477 : (x (-1) 10).toNat = 0 := by
          have r17478 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
          have b17479 := hb (x (-1) 2)
          have b17480 := hb (x (-1) 10)
          clear * - r17478 b17479 b17480 d17473
          omega
        have d17481 : (x 1 13).toNat = 1 := by
          have r17482 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
          have b17483 := hb (x (-1) 2)
          have b17484 := hb (x 1 13)
          have b17485 := hb (x 0 1 && x 0 14)
          clear * - r17482 b17483 b17484 b17485 g32 d17473
          omega
        have d17486 : (x 2 12).toNat = 0 := by
          have r17487 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
          have e17488 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e17489 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b17490 := hb (x (-1) 3)
          have b17491 := hb (x 0 2)
          have b17492 := hb (x 1 13)
          have b17493 := hb (x 2 12)
          clear * - r17487 e17488 e17489 b17490 b17491 b17492 b17493 d17481 g7
          omega
        have d17494 : (x 2 3 && x 2 12).toNat = 0 := by
          have r17495 := hand2 (x 2 3) (x 2 12)
          have b17496 := hb (x 2 12)
          have b17497 := hb (x 2 3 && x 2 12)
          clear * - r17495 b17496 b17497 d17486
          omega
        have d17498 : (x 2 7 && x 2 12).toNat = 0 := by
          have r17499 := hand2 (x 2 7) (x 2 12)
          have b17500 := hb (x 2 12)
          have b17501 := hb (x 2 7 && x 2 12)
          clear * - r17499 b17500 b17501 d17486
          omega
        have d17502 : (x (-5) 5).toNat = 0 := by
          have r17503 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e17504 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e17505 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e17506 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e17507 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e17508 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e17509 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b17510 := hb (x (-7) 7)
          have b17511 := hb (x (-6) 6)
          have b17512 := hb (x (-5) 5)
          have b17513 := hb (x (-4) 4)
          have b17514 := hb (x (-3) 11)
          have b17515 := hb (x (-2) 10)
          have b17516 := hb (x (-1) 9)
          have b17517 := hb (x 0 8)
          clear * - r17503 e17504 e17505 e17506 e17507 e17508 e17509 b17510 b17511 b17512 b17513 b17514 b17515 b17516 b17517 f17413 g5 d17414 g1 d17430
          omega
        have d17518 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
          have r17519 := hand1 (x (-5) 5) (x (-5) 14)
          have b17520 := hb (x (-5) 5)
          have b17521 := hb (x (-5) 5 && x (-5) 14)
          clear * - r17519 b17520 b17521 d17502
          omega
        have d17522 : (x (-6) 6).toNat = 0 := by
          have r17523 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e17524 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e17525 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e17526 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e17527 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e17528 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e17529 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b17530 := hb (x (-7) 7)
          have b17531 := hb (x (-6) 6)
          have b17532 := hb (x (-5) 5)
          have b17533 := hb (x (-4) 4)
          have b17534 := hb (x (-3) 11)
          have b17535 := hb (x (-2) 10)
          have b17536 := hb (x (-1) 9)
          have b17537 := hb (x 0 8)
          clear * - r17523 e17524 e17525 e17526 e17527 e17528 e17529 b17530 b17531 b17532 b17533 b17534 b17535 b17536 b17537 f17413 g5 d17414 g1 d17430 d17502
          omega
        have d17538 : (x (-2) 2 && x (-2) 11).toNat = 1 := by
          have r17539 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
          have b17540 := hb (x (-6) 6)
          have b17541 := hb (x 0 9)
          have b17542 := hb (x (-1) 1 && x (-1) 10)
          have b17543 := hb (x (-2) 2 && x (-2) 11)
          have b17544 := hb (x (-3) 3 && x (-3) 12)
          have b17545 := hb (x (-4) 4 && x (-4) 13)
          have b17546 := hb (x (-5) 5 && x (-5) 14)
          clear * - r17539 b17540 b17541 b17542 b17543 b17544 b17545 b17546 g11 g19 g20 d17446 d17518 d17522
          omega
        have d17547 : (x (-2) 11).toNat = 1 := by
          have r17548 := hand2 (x (-2) 2) (x (-2) 11)
          have b17549 := hb (x (-2) 11)
          have b17550 := hb (x (-2) 2 && x (-2) 11)
          clear * - r17548 b17549 b17550 d17538
          omega
        have d17551 : (x (-2) 3).toNat = 1 := by
          have r17552 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
          have b17553 := hb (x (-2) 3)
          have b17554 := hb (x (-2) 11)
          clear * - r17552 b17553 b17554 d17547
          omega
        have d17555 : (x 1 12).toNat = 0 := by
          have r17556 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
          have e17557 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e17558 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b17559 := hb (x (-2) 3)
          have b17560 := hb (x (-1) 2)
          have b17561 := hb (x 0 13)
          have b17562 := hb (x 1 12)
          clear * - r17556 e17557 e17558 b17559 b17560 b17561 b17562 g14 d17473 d17551
          omega
        have d17563 : (x 1 4).toNat = 0 := by
          have r17564 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b17565 := hb (x 1 4)
          have b17566 := hb (x 1 12)
          clear * - r17564 b17565 b17566 d17555
          omega
        have d17567 : (x 1 4 && x 1 14).toNat = 0 := by
          have r17568 := hand1 (x 1 4) (x 1 14)
          have b17569 := hb (x 1 4)
          have b17570 := hb (x 1 4 && x 1 14)
          clear * - r17568 b17569 b17570 d17563
          omega
        have d17571 : (x 1 4 && x 1 13).toNat = 0 := by
          have r17572 := hand1 (x 1 4) (x 1 13)
          have b17573 := hb (x 1 4)
          have b17574 := hb (x 1 4 && x 1 13)
          clear * - r17572 b17573 b17574 d17563
          omega
        have d17575 : (x 1 8).toNat = 0 := by
          have r17576 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
          have e17577 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e17578 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e17579 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e17580 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e17581 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e17582 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b17583 := hb (x (-6) 7)
          have b17584 := hb (x (-5) 6)
          have b17585 := hb (x (-4) 5)
          have b17586 := hb (x (-3) 4)
          have b17587 := hb (x (-2) 11)
          have b17588 := hb (x (-1) 10)
          have b17589 := hb (x 0 9)
          have b17590 := hb (x 1 8)
          clear * - r17576 e17577 e17578 e17579 e17580 e17581 e17582 b17583 b17584 b17585 b17586 b17587 b17588 b17589 b17590 g11 d17477 d17547
          omega
        have d17591 : (x 1 8 && x 1 13).toNat = 0 := by
          have r17592 := hand1 (x 1 8) (x 1 13)
          have b17593 := hb (x 1 8)
          have b17594 := hb (x 1 8 && x 1 13)
          clear * - r17592 b17593 b17594 d17575
          omega
        have r17595 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
        have r17596 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
        have e17597 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e17598 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e17599 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e17600 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e17601 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e17602 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have r17603 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
        have e17604 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e17605 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have r17606 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := hcov5 9
        have r17607 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := hcov9 5
        have r17608 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
        have r17609 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := hcov10 7
        have r17610 := hand2 (x 8 1) (x 8 6)
        have r17611 := hand2 (x 7 2) (x 7 7)
        have r17612 := hand2 (x 6 3) (x 6 8)
        have r17613 := hand1 (x 5 4) (x 5 9)
        have r17614 := hand1 (x 4 5) (x 4 10)
        have r17615 := hand1 (x 3 6) (x 3 11)
        have r17616 := hand2 (x 4 1) (x 4 10)
        have r17617 := hand2 (x 3 2) (x 3 11)
        have r17618 := hand1 (x 3 2) (x 3 12)
        have r17619 := hand1 (x 2 3) (x 2 13)
        have r17620 := hand2 (x 6 1) (x 6 11)
        have r17621 := hand2 (x 5 2) (x 5 12)
        have r17622 := hand2 (x 4 3) (x 4 13)
        have b17623 := hb (x (-1) 6)
        have b17624 := hb (x (-1) 10)
        have b17625 := hb (x 0 5)
        have b17626 := hb (x 0 14)
        have b17627 := hb (x 1 13)
        have b17628 := hb (x 2 3)
        have b17629 := hb (x 2 5)
        have b17630 := hb (x 2 7)
        have b17631 := hb (x 2 12)
        have b17632 := hb (x 3 2)
        have b17633 := hb (x 3 6)
        have b17634 := hb (x 3 11)
        have b17635 := hb (x 4 5)
        have b17636 := hb (x 4 10)
        have b17637 := hb (x 4 13)
        have b17638 := hb (x 5 4)
        have b17639 := hb (x 5 9)
        have b17640 := hb (x 5 10)
        have b17641 := hb (x 5 12)
        have b17642 := hb (x 6 8)
        have b17643 := hb (x 6 11)
        have b17644 := hb (x 7 7)
        have b17645 := hb (x 7 10)
        have b17646 := hb (x 8 6)
        have b17647 := hb (x 8 9)
        have b17648 := hb (x 9 5)
        have b17649 := hb (x 9 8)
        have b17650 := hb (x 10 4)
        have b17651 := hb (x 11 3)
        have b17652 := hb (x 12 2)
        have b17653 := hb (x 13 1)
        have b17654 := hb (x 8 1 && x 8 6)
        have b17655 := hb (x 7 2 && x 7 7)
        have b17656 := hb (x 6 3 && x 6 8)
        have b17657 := hb (x 5 4 && x 5 9)
        have b17658 := hb (x 4 5 && x 4 10)
        have b17659 := hb (x 3 6 && x 3 11)
        have b17660 := hb (x 2 7 && x 2 12)
        have b17661 := hb (x 1 8 && x 1 13)
        have b17662 := hb (x 0 9 && x 0 14)
        have b17663 := hb (x 4 1 && x 4 10)
        have b17664 := hb (x 3 2 && x 3 11)
        have b17665 := hb (x 2 3 && x 2 12)
        have b17666 := hb (x 1 4 && x 1 13)
        have b17667 := hb (x 0 5 && x 0 14)
        have b17668 := hb (x 4 1 && x 4 11)
        have b17669 := hb (x 3 2 && x 3 12)
        have b17670 := hb (x 2 3 && x 2 13)
        have b17671 := hb (x 1 4 && x 1 14)
        have b17672 := hb (x 6 1 && x 6 11)
        have b17673 := hb (x 5 2 && x 5 12)
        have b17674 := hb (x 4 3 && x 4 13)
        have b17675 := hb (x 3 4 && x 3 14)
        linarith only [r17595, r17596, e17597, e17598, e17599, e17600, e17601, e17602, r17603, e17604, e17605, r17606, r17607, r17608, r17609, r17610, r17611, r17612, r17613, r17614, r17615, r17616, r17617, r17618, r17619, r17620, r17621, r17622, b17623, b17624, b17625, b17626, b17627, b17628, b17629, b17630, b17631, b17632, b17633, b17634, b17635, b17636, b17637, b17638, b17639, b17640, b17641, b17642, b17643, b17644, b17645, b17646, b17647, b17648, b17649, b17650, b17651, b17652, b17653, b17654, b17655, b17656, b17657, b17658, b17659, b17660, b17661, b17662, b17663, b17664, b17665, b17666, b17667, b17668, b17669, b17670, b17671, b17672, b17673, b17674, b17675, d17469, d17477, g9, g15, d17481, d15537, d17486, d15453, d17498, d17591, g18, d17494, d17571, g21, d15497, d17567, d15529]
    · have f17676 : (x 0 6).toNat = 1 := by rw [h15583]; rfl
      have d17677 : (x 6 8).toNat = 0 := by
        have r17678 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
        have e17679 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e17680 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e17681 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e17682 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e17683 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e17684 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b17685 := hb (x (-1) 7)
        have b17686 := hb (x 0 6)
        have b17687 := hb (x 1 5)
        have b17688 := hb (x 2 4)
        have b17689 := hb (x 3 11)
        have b17690 := hb (x 4 10)
        have b17691 := hb (x 5 9)
        have b17692 := hb (x 6 8)
        clear * - r17678 e17679 e17680 e17681 e17682 e17683 e17684 b17685 b17686 b17687 b17688 b17689 b17690 b17691 b17692 f17676
        omega
      have d17693 : (x 5 9).toNat = 0 := by
        have r17694 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
        have e17695 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e17696 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e17697 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e17698 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e17699 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e17700 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b17701 := hb (x (-1) 7)
        have b17702 := hb (x 0 6)
        have b17703 := hb (x 1 5)
        have b17704 := hb (x 2 4)
        have b17705 := hb (x 3 11)
        have b17706 := hb (x 4 10)
        have b17707 := hb (x 5 9)
        have b17708 := hb (x 6 8)
        clear * - r17694 e17695 e17696 e17697 e17698 e17699 e17700 b17701 b17702 b17703 b17704 b17705 b17706 b17707 b17708 d17677 f17676
        omega
      have d17709 : (x 4 10).toNat = 0 := by
        have r17710 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
        have e17711 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e17712 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e17713 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e17714 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e17715 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e17716 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b17717 := hb (x (-1) 7)
        have b17718 := hb (x 0 6)
        have b17719 := hb (x 1 5)
        have b17720 := hb (x 2 4)
        have b17721 := hb (x 3 11)
        have b17722 := hb (x 4 10)
        have b17723 := hb (x 5 9)
        have b17724 := hb (x 6 8)
        clear * - r17710 e17711 e17712 e17713 e17714 e17715 e17716 b17717 b17718 b17719 b17720 b17721 b17722 b17723 b17724 d17677 d17693 f17676
        omega
      have d17725 : (x 3 11).toNat = 0 := by
        have r17726 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
        have e17727 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e17728 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e17729 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e17730 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e17731 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e17732 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b17733 := hb (x (-1) 7)
        have b17734 := hb (x 0 6)
        have b17735 := hb (x 1 5)
        have b17736 := hb (x 2 4)
        have b17737 := hb (x 3 11)
        have b17738 := hb (x 4 10)
        have b17739 := hb (x 5 9)
        have b17740 := hb (x 6 8)
        clear * - r17726 e17727 e17728 e17729 e17730 e17731 e17732 b17733 b17734 b17735 b17736 b17737 b17738 b17739 b17740 d17677 d17693 d17709 f17676
        omega
      have d17741 : (x 3 1 && x 3 11).toNat = 0 := by
        have r17742 := hand2 (x 3 1) (x 3 11)
        have b17743 := hb (x 3 11)
        have b17744 := hb (x 3 1 && x 3 11)
        clear * - r17742 b17743 b17744 d17725
        omega
      have d17745 : (x 2 4).toNat = 0 := by
        have r17746 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
        have e17747 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e17748 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e17749 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e17750 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e17751 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e17752 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b17753 := hb (x (-1) 7)
        have b17754 := hb (x 0 6)
        have b17755 := hb (x 1 5)
        have b17756 := hb (x 2 4)
        have b17757 := hb (x 3 11)
        have b17758 := hb (x 4 10)
        have b17759 := hb (x 5 9)
        have b17760 := hb (x 6 8)
        clear * - r17746 e17747 e17748 e17749 e17750 e17751 e17752 b17753 b17754 b17755 b17756 b17757 b17758 b17759 b17760 d17677 d17693 d17709 d17725 f17676
        omega
      have d17761 : (x 2 4 && x 2 14).toNat = 0 := by
        have r17762 := hand1 (x 2 4) (x 2 14)
        have b17763 := hb (x 2 4)
        have b17764 := hb (x 2 4 && x 2 14)
        clear * - r17762 b17763 b17764 d17745
        omega
      have d17765 : (x 1 5).toNat = 0 := by
        have r17766 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
        have e17767 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e17768 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e17769 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e17770 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e17771 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e17772 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b17773 := hb (x (-1) 7)
        have b17774 := hb (x 0 6)
        have b17775 := hb (x 1 5)
        have b17776 := hb (x 2 4)
        have b17777 := hb (x 3 11)
        have b17778 := hb (x 4 10)
        have b17779 := hb (x 5 9)
        have b17780 := hb (x 6 8)
        clear * - r17766 e17767 e17768 e17769 e17770 e17771 e17772 b17773 b17774 b17775 b17776 b17777 b17778 b17779 b17780 d17677 d17693 d17709 d17725 d17745 f17676
        omega
      cases h17781 : x 0 8
      · have f17782 : (x 0 8).toNat = 0 := by rw [h17781]; rfl
        cases h17783 : x 1 1
        · have f17784 : (x 1 1).toNat = 0 := by rw [h17783]; rfl
          have d17785 : (x 1 1 && x 1 14).toNat = 0 := by
            have r17786 := hand1 (x 1 1) (x 1 14)
            have b17787 := hb (x 1 1)
            have b17788 := hb (x 1 1 && x 1 14)
            clear * - r17786 b17787 b17788 f17784
            omega
          have d17789 : (x 1 1 && x 1 12).toNat = 0 := by
            have r17790 := hand1 (x 1 1) (x 1 12)
            have b17791 := hb (x 1 1)
            have b17792 := hb (x 1 1 && x 1 12)
            clear * - r17790 b17791 b17792 f17784
            omega
          have d17793 : (x 1 13).toNat = 0 := by
            have r17794 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
            have b17795 := hb (x 1 1)
            have b17796 := hb (x 1 13)
            clear * - r17794 b17795 b17796 f17784
            omega
          have d17797 : (x 1 2 && x 1 13).toNat = 0 := by
            have r17798 := hand2 (x 1 2) (x 1 13)
            have b17799 := hb (x 1 13)
            have b17800 := hb (x 1 2 && x 1 13)
            clear * - r17798 b17799 b17800 d17793
            omega
          have d17801 : (x 2 13).toNat = 1 := by
            have r17802 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := hcov13 2
            have b17803 := hb (x 0 2)
            have b17804 := hb (x 2 13)
            have b17805 := hb (x 1 1 && x 1 14)
            clear * - r17802 b17803 b17804 b17805 d17785 g7
            omega
          have d17806 : (x 2 1).toNat = 1 := by
            have r17807 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
            have b17808 := hb (x 2 1)
            have b17809 := hb (x 2 13)
            clear * - r17807 b17808 b17809 d17801
            omega
          have d17810 : (x 3 14).toNat = 0 := by
            have r17811 : (x 3 14).toNat + (x 2 1).toNat = 1 := hd14 3
            have b17812 := hb (x 2 1)
            have b17813 := hb (x 3 14)
            clear * - r17811 b17812 b17813 d17806
            omega
          have d17814 : (x 3 1 && x 3 14).toNat = 0 := by
            have r17815 := hand2 (x 3 1) (x 3 14)
            have b17816 := hb (x 3 14)
            have b17817 := hb (x 3 1 && x 3 14)
            clear * - r17815 b17816 b17817 d17810
            omega
          have d17818 : (x 3 2).toNat = 0 := by
            have r17819 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b17820 := hb (x 3 2)
            have b17821 := hb (x 3 14)
            clear * - r17819 b17820 b17821 d17810
            omega
          have d17822 : (x (-1) 2).toNat = 1 := by
            have r17823 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
            have b17824 := hb (x (-1) 2)
            have b17825 := hb (x 1 13)
            have b17826 := hb (x 0 1 && x 0 14)
            clear * - r17823 b17824 b17825 b17826 d17793 g32
            omega
          have d17827 : (x (-1) 14).toNat = 1 := by
            have r17828 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
            have b17829 := hb (x (-1) 2)
            have b17830 := hb (x (-1) 14)
            clear * - r17828 b17829 b17830 d17822
            omega
          have d17831 : (x (-2) 1).toNat = 0 := by
            have r17832 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
            have b17833 := hb (x (-2) 1)
            have b17834 := hb (x (-1) 14)
            clear * - r17832 b17833 b17834 d17827
            omega
          have d17835 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r17836 := hand1 (x (-2) 1) (x (-2) 14)
            have b17837 := hb (x (-2) 1)
            have b17838 := hb (x (-2) 1 && x (-2) 14)
            clear * - r17836 b17837 b17838 d17831
            omega
          have d17839 : (x (-2) 13).toNat = 0 := by
            have r17840 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b17841 := hb (x (-2) 1)
            have b17842 := hb (x (-2) 13)
            clear * - r17840 b17841 b17842 d17831
            omega
          have d17843 : (x (-3) 2).toNat = 1 := by
            have r17844 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
            have b17845 := hb (x (-3) 2)
            have b17846 := hb (x (-1) 13)
            have b17847 := hb (x (-2) 1 && x (-2) 14)
            clear * - r17844 b17845 b17846 b17847 g6 d17835
            omega
          have d17848 : (x (-3) 14).toNat = 1 := by
            have r17849 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b17850 := hb (x (-3) 2)
            have b17851 := hb (x (-3) 14)
            clear * - r17849 b17850 b17851 d17843
            omega
          have d17852 : (x (-4) 1).toNat = 0 := by
            have r17853 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
            have b17854 := hb (x (-4) 1)
            have b17855 := hb (x (-3) 14)
            clear * - r17853 b17854 b17855 d17848
            omega
          have d17856 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
            have r17857 := hand1 (x (-4) 1) (x (-4) 14)
            have b17858 := hb (x (-4) 1)
            have b17859 := hb (x (-4) 1 && x (-4) 14)
            clear * - r17857 b17858 b17859 d17852
            omega
          have d17860 : (x (-4) 13).toNat = 0 := by
            have r17861 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
            have b17862 := hb (x (-4) 1)
            have b17863 := hb (x (-4) 13)
            clear * - r17861 b17862 b17863 d17852
            omega
          have d17864 : (x (-4) 2).toNat = 1 := by
            have r17865 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
            have b17866 := hb (x (-4) 2)
            have b17867 := hb (x (-2) 13)
            have b17868 := hb (x (-3) 1 && x (-3) 14)
            clear * - r17865 b17866 b17867 b17868 d17839 g31
            omega
          have d17869 : (x (-5) 2).toNat = 1 := by
            have r17870 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := hcov13 (-3)
            have b17871 := hb (x (-5) 2)
            have b17872 := hb (x (-3) 13)
            have b17873 := hb (x (-4) 1 && x (-4) 14)
            clear * - r17870 b17871 b17872 b17873 g2 d17856
            omega
          have d17874 : (x 1 12).toNat = 0 := by
            have r17875 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
            have e17876 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e17877 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b17878 := hb (x (-2) 3)
            have b17879 := hb (x (-1) 2)
            have b17880 := hb (x 0 13)
            have b17881 := hb (x 1 12)
            clear * - r17875 e17876 e17877 b17878 b17879 b17880 b17881 g14 d17822
            omega
          have d17882 : (x (-2) 3).toNat = 0 := by
            have r17883 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
            have e17884 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e17885 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b17886 := hb (x (-2) 3)
            have b17887 := hb (x (-1) 2)
            have b17888 := hb (x 0 13)
            have b17889 := hb (x 1 12)
            clear * - r17883 e17884 e17885 b17886 b17887 b17888 b17889 d17874 g14 d17822
            omega
          have d17890 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
            have r17891 := hand1 (x (-2) 3) (x (-2) 14)
            have b17892 := hb (x (-2) 3)
            have b17893 := hb (x (-2) 3 && x (-2) 14)
            clear * - r17891 b17892 b17893 d17882
            omega
          have d17894 : (x (-1) 12).toNat = 0 := by
            have r17895 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
            have e17896 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e17897 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b17898 := hb (x (-4) 3)
            have b17899 := hb (x (-3) 2)
            have b17900 := hb (x (-2) 13)
            have b17901 := hb (x (-1) 12)
            clear * - r17895 e17896 e17897 b17898 b17899 b17900 b17901 d17839 d17843
            omega
          have d17902 : (x (-1) 4).toNat = 0 := by
            have r17903 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b17904 := hb (x (-1) 4)
            have b17905 := hb (x (-1) 12)
            clear * - r17903 b17904 b17905 d17894
            omega
          have d17906 : (x (-2) 12).toNat = 0 := by
            have r17907 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
            have e17908 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e17909 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b17910 := hb (x (-5) 3)
            have b17911 := hb (x (-4) 2)
            have b17912 := hb (x (-3) 13)
            have b17913 := hb (x (-2) 12)
            clear * - r17907 e17908 e17909 b17910 b17911 b17912 b17913 g2 d17864
            omega
          have d17914 : (x (-2) 4).toNat = 0 := by
            have r17915 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
            have b17916 := hb (x (-2) 4)
            have b17917 := hb (x (-2) 12)
            clear * - r17915 b17916 b17917 d17906
            omega
          have d17918 : (x (-3) 12).toNat = 0 := by
            have r17919 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
            have e17920 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e17921 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b17922 := hb (x (-6) 3)
            have b17923 := hb (x (-5) 2)
            have b17924 := hb (x (-4) 13)
            have b17925 := hb (x (-3) 12)
            clear * - r17919 e17920 e17921 b17922 b17923 b17924 b17925 d17860 d17869
            omega
          have d17926 : (x (-3) 4).toNat = 0 := by
            have r17927 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have b17928 := hb (x (-3) 4)
            have b17929 := hb (x (-3) 12)
            clear * - r17927 b17928 b17929 d17918
            omega
          have d17930 : (x 2 1 && x 2 12).toNat = 1 := by
            have r17931 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
            have b17932 := hb (x (-1) 4)
            have b17933 := hb (x 3 11)
            have b17934 := hb (x 2 1 && x 2 12)
            have b17935 := hb (x 1 2 && x 1 13)
            have b17936 := hb (x 0 3 && x 0 14)
            clear * - r17931 b17932 b17933 b17934 b17935 b17936 d17725 d17797 d15575 d17902
            omega
          have d17937 : (x 2 12).toNat = 1 := by
            have r17938 := hand2 (x 2 1) (x 2 12)
            have b17939 := hb (x 2 12)
            have b17940 := hb (x 2 1 && x 2 12)
            clear * - r17938 b17939 b17940 d17930
            omega
          have d17941 : (x (-1) 3).toNat = 0 := by
            have r17942 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
            have e17943 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e17944 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b17945 := hb (x (-1) 3)
            have b17946 := hb (x 0 2)
            have b17947 := hb (x 1 13)
            have b17948 := hb (x 2 12)
            clear * - r17942 e17943 e17944 b17945 b17946 b17947 b17948 d17937 d17793 g7
            omega
          have d17949 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
            have r17950 := hand1 (x (-1) 3) (x (-1) 14)
            have b17951 := hb (x (-1) 3)
            have b17952 := hb (x (-1) 3 && x (-1) 14)
            clear * - r17950 b17951 b17952 d17941
            omega
          have d17953 : (x 2 11).toNat = 1 := by
            have r17954 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := hcov11 2
            have b17955 := hb (x (-2) 4)
            have b17956 := hb (x 2 11)
            have b17957 := hb (x 1 1 && x 1 12)
            have b17958 := hb (x 0 2 && x 0 13)
            have b17959 := hb (x (-1) 3 && x (-1) 14)
            clear * - r17954 b17955 b17956 b17957 b17958 b17959 d17789 g30 d17949 d17914
            omega
          have d17960 : (x 2 3).toNat = 1 := by
            have r17961 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
            have b17962 := hb (x 2 3)
            have b17963 := hb (x 2 11)
            clear * - r17961 b17962 b17963 d17953
            omega
          have d17964 : (x 5 12).toNat = 0 := by
            have r17965 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e17966 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e17967 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b17968 := hb (x 2 3)
            have b17969 := hb (x 3 2)
            have b17970 := hb (x 4 13)
            have b17971 := hb (x 5 12)
            clear * - r17965 e17966 e17967 b17968 b17969 b17970 b17971 d17818 d17960
            omega
          have d17972 : (x 4 13).toNat = 0 := by
            have r17973 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e17974 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e17975 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b17976 := hb (x 2 3)
            have b17977 := hb (x 3 2)
            have b17978 := hb (x 4 13)
            have b17979 := hb (x 5 12)
            clear * - r17973 e17974 e17975 b17976 b17977 b17978 b17979 d17964 d17818 d17960
            omega
          have d17980 : (x 2 2).toNat = 1 := by
            have r17981 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
            have b17982 := hb (x 2 2)
            have b17983 := hb (x 4 13)
            have b17984 := hb (x 3 1 && x 3 14)
            clear * - r17981 b17982 b17983 b17984 d17972 d17814
            omega
          have d17985 : (x 4 12).toNat = 0 := by
            have r17986 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e17987 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e17988 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b17989 := hb (x 1 3)
            have b17990 := hb (x 2 2)
            have b17991 := hb (x 3 13)
            have b17992 := hb (x 4 12)
            clear * - r17986 e17987 e17988 b17989 b17990 b17991 b17992 d17980
            omega
          have d17993 : (x 3 13).toNat = 0 := by
            have r17994 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e17995 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e17996 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b17997 := hb (x 1 3)
            have b17998 := hb (x 2 2)
            have b17999 := hb (x 3 13)
            have b18000 := hb (x 4 12)
            clear * - r17994 e17995 e17996 b17997 b17998 b17999 b18000 d17985 d17980
            omega
          have d18001 : (x 1 3).toNat = 0 := by
            have r18002 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e18003 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e18004 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b18005 := hb (x 1 3)
            have b18006 := hb (x 2 2)
            have b18007 := hb (x 3 13)
            have b18008 := hb (x 4 12)
            clear * - r18002 e18003 e18004 b18005 b18006 b18007 b18008 d17985 d17993 d17980
            omega
          have d18009 : (x 1 11).toNat = 0 := by
            have r18010 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
            have b18011 := hb (x 1 3)
            have b18012 := hb (x 1 11)
            clear * - r18010 b18011 b18012 d18001
            omega
          have r18013 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := hcov11 1
          have b18014 := hb (x (-3) 4)
          have b18015 := hb (x 1 11)
          have b18016 := hb (x 0 1 && x 0 12)
          have b18017 := hb (x (-1) 2 && x (-1) 13)
          have b18018 := hb (x (-2) 3 && x (-2) 14)
          linarith only [r18013, b18014, b18015, b18016, b18017, b18018, d18009, g28, g29, d17890, d17926]
        · have f18019 : (x 1 1).toNat = 1 := by rw [h17783]; rfl
          have d18020 : (x 2 14).toNat = 0 := by
            have r18021 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
            have b18022 := hb (x 1 1)
            have b18023 := hb (x 2 14)
            clear * - r18021 b18022 b18023 f18019
            omega
          have d18024 : (x 2 1 && x 2 14).toNat = 0 := by
            have r18025 := hand2 (x 2 1) (x 2 14)
            have b18026 := hb (x 2 14)
            have b18027 := hb (x 2 1 && x 2 14)
            clear * - r18025 b18026 b18027 d18020
            omega
          have d18028 : (x 2 6).toNat = 0 := by
            have r18029 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
            have b18030 := hb (x 2 6)
            have b18031 := hb (x 2 14)
            clear * - r18029 b18030 b18031 d18020
            omega
          have d18032 : (x 2 6 && x 2 13).toNat = 0 := by
            have r18033 := hand1 (x 2 6) (x 2 13)
            have b18034 := hb (x 2 6)
            have b18035 := hb (x 2 6 && x 2 13)
            clear * - r18033 b18034 b18035 d18028
            omega
          have d18036 : (x 2 6 && x 2 10).toNat = 0 := by
            have r18037 := hand1 (x 2 6) (x 2 10)
            have b18038 := hb (x 2 6)
            have b18039 := hb (x 2 6 && x 2 10)
            clear * - r18037 b18038 b18039 d18028
            omega
          have d18040 : (x 2 2).toNat = 0 := by
            have r18041 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
            have b18042 := hb (x 2 2)
            have b18043 := hb (x 2 14)
            clear * - r18041 b18042 b18043 d18020
            omega
          have d18044 : (x 2 2 && x 2 12).toNat = 0 := by
            have r18045 := hand1 (x 2 2) (x 2 12)
            have b18046 := hb (x 2 2)
            have b18047 := hb (x 2 2 && x 2 12)
            clear * - r18045 b18046 b18047 d18040
            omega
          have d18048 : (x 2 10).toNat = 0 := by
            have r18049 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
            have b18050 := hb (x 2 2)
            have b18051 := hb (x 2 10)
            clear * - r18049 b18050 b18051 d18040
            omega
          have d18052 : (x 2 10 && x 2 13).toNat = 0 := by
            have r18053 := hand1 (x 2 10) (x 2 13)
            have b18054 := hb (x 2 10)
            have b18055 := hb (x 2 10 && x 2 13)
            clear * - r18053 b18054 b18055 d18048
            omega
          have d18056 : (x 1 3 && x 1 13).toNat = 1 := by
            have r18057 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := hcov10 4
            have b18058 := hb (x (-1) 5)
            have b18059 := hb (x 4 10)
            have b18060 := hb (x 3 1 && x 3 11)
            have b18061 := hb (x 2 2 && x 2 12)
            have b18062 := hb (x 1 3 && x 1 13)
            have b18063 := hb (x 0 4 && x 0 14)
            clear * - r18057 b18058 b18059 b18060 b18061 b18062 b18063 d17709 d17741 d18044 g24 g4
            omega
          have d18064 : (x 1 13).toNat = 1 := by
            have r18065 := hand2 (x 1 3) (x 1 13)
            have b18066 := hb (x 1 13)
            have b18067 := hb (x 1 3 && x 1 13)
            clear * - r18065 b18066 b18067 d18056
            omega
          have d18068 : (x 2 12).toNat = 0 := by
            have r18069 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
            have e18070 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e18071 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b18072 := hb (x (-1) 3)
            have b18073 := hb (x 0 2)
            have b18074 := hb (x 1 13)
            have b18075 := hb (x 2 12)
            clear * - r18069 e18070 e18071 b18072 b18073 b18074 b18075 d18064 g7
            omega
          have d18076 : (x (-1) 3).toNat = 0 := by
            have r18077 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
            have e18078 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e18079 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b18080 := hb (x (-1) 3)
            have b18081 := hb (x 0 2)
            have b18082 := hb (x 1 13)
            have b18083 := hb (x 2 12)
            clear * - r18077 e18078 e18079 b18080 b18081 b18082 b18083 d18068 d18064 g7
            omega
          have d18084 : (x (-1) 11).toNat = 0 := by
            have r18085 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
            have b18086 := hb (x (-1) 3)
            have b18087 := hb (x (-1) 11)
            clear * - r18085 b18086 b18087 d18076
            omega
          have d18088 : (x 1 3).toNat = 1 := by
            have r18089 := hand1 (x 1 3) (x 1 13)
            have b18090 := hb (x 1 3)
            have b18091 := hb (x 1 3 && x 1 13)
            clear * - r18089 b18090 b18091 d18056
            omega
          have d18092 : (x 4 12).toNat = 0 := by
            have r18093 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e18094 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e18095 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b18096 := hb (x 1 3)
            have b18097 := hb (x 2 2)
            have b18098 := hb (x 3 13)
            have b18099 := hb (x 4 12)
            clear * - r18093 e18094 e18095 b18096 b18097 b18098 b18099 d18040 d18088
            omega
          have d18100 : (x 4 2 && x 4 12).toNat = 0 := by
            have r18101 := hand2 (x 4 2) (x 4 12)
            have b18102 := hb (x 4 12)
            have b18103 := hb (x 4 2 && x 4 12)
            clear * - r18101 b18102 b18103 d18092
            omega
          have d18104 : (x 4 3 && x 4 12).toNat = 0 := by
            have r18105 := hand2 (x 4 3) (x 4 12)
            have b18106 := hb (x 4 12)
            have b18107 := hb (x 4 3 && x 4 12)
            clear * - r18105 b18106 b18107 d18092
            omega
          have d18108 : (x 4 4).toNat = 0 := by
            have r18109 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b18110 := hb (x 4 4)
            have b18111 := hb (x 4 12)
            clear * - r18109 b18110 b18111 d18092
            omega
          have d18112 : (x 4 4 && x 4 8).toNat = 0 := by
            have r18113 := hand1 (x 4 4) (x 4 8)
            have b18114 := hb (x 4 4)
            have b18115 := hb (x 4 4 && x 4 8)
            clear * - r18113 b18114 b18115 d18108
            omega
          have d18116 : (x 3 13).toNat = 0 := by
            have r18117 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e18118 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e18119 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b18120 := hb (x 1 3)
            have b18121 := hb (x 2 2)
            have b18122 := hb (x 3 13)
            have b18123 := hb (x 4 12)
            clear * - r18117 e18118 e18119 b18120 b18121 b18122 b18123 d18092 d18040 d18088
            omega
          have d18124 : (x 3 3 && x 3 13).toNat = 0 := by
            have r18125 := hand2 (x 3 3) (x 3 13)
            have b18126 := hb (x 3 13)
            have b18127 := hb (x 3 3 && x 3 13)
            clear * - r18125 b18126 b18127 d18116
            omega
          have d18128 : (x 3 5).toNat = 0 := by
            have r18129 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
            have b18130 := hb (x 3 5)
            have b18131 := hb (x 3 13)
            clear * - r18129 b18130 b18131 d18116
            omega
          have d18132 : (x 3 5 && x 3 12).toNat = 0 := by
            have r18133 := hand1 (x 3 5) (x 3 12)
            have b18134 := hb (x 3 5)
            have b18135 := hb (x 3 5 && x 3 12)
            clear * - r18133 b18134 b18135 d18128
            omega
          have d18136 : (x 3 5 && x 3 9).toNat = 0 := by
            have r18137 := hand1 (x 3 5) (x 3 9)
            have b18138 := hb (x 3 5)
            have b18139 := hb (x 3 5 && x 3 9)
            clear * - r18137 b18138 b18139 d18128
            omega
          have d18140 : (x 1 2).toNat = 1 := by
            have r18141 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
            have b18142 := hb (x 1 2)
            have b18143 := hb (x 3 13)
            have b18144 := hb (x 2 1 && x 2 14)
            clear * - r18141 b18142 b18143 b18144 d18116 d18024
            omega
          have d18145 : (x 3 12).toNat = 0 := by
            have r18146 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
            have e18147 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
            have e18148 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
            have b18149 := hb (x 0 3)
            have b18150 := hb (x 1 2)
            have b18151 := hb (x 2 13)
            have b18152 := hb (x 3 12)
            clear * - r18146 e18147 e18148 b18149 b18150 b18151 b18152 d18140 f15574
            omega
          have d18153 : (x 3 2 && x 3 12).toNat = 0 := by
            have r18154 := hand2 (x 3 2) (x 3 12)
            have b18155 := hb (x 3 12)
            have b18156 := hb (x 3 2 && x 3 12)
            clear * - r18154 b18155 b18156 d18145
            omega
          have d18157 : (x 3 9 && x 3 12).toNat = 0 := by
            have r18158 := hand2 (x 3 9) (x 3 12)
            have b18159 := hb (x 3 12)
            have b18160 := hb (x 3 9 && x 3 12)
            clear * - r18158 b18159 b18160 d18145
            omega
          have d18161 : (x 2 13).toNat = 0 := by
            have r18162 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
            have e18163 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
            have e18164 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
            have b18165 := hb (x 0 3)
            have b18166 := hb (x 1 2)
            have b18167 := hb (x 2 13)
            have b18168 := hb (x 3 12)
            clear * - r18162 e18163 e18164 b18165 b18166 b18167 b18168 d18145 d18140 f15574
            omega
          have d18169 : (x 2 3 && x 2 13).toNat = 0 := by
            have r18170 := hand2 (x 2 3) (x 2 13)
            have b18171 := hb (x 2 13)
            have b18172 := hb (x 2 3 && x 2 13)
            clear * - r18170 b18171 b18172 d18161
            omega
          have d18173 : (x 1 4 && x 1 14).toNat = 1 := by
            have r18174 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
            have b18175 := hb (x 0 5)
            have b18176 := hb (x 5 10)
            have b18177 := hb (x 4 1 && x 4 11)
            have b18178 := hb (x 3 2 && x 3 12)
            have b18179 := hb (x 2 3 && x 2 13)
            have b18180 := hb (x 1 4 && x 1 14)
            clear * - r18174 b18175 b18176 b18177 b18178 b18179 b18180 d15453 d15497 d18153 d18169 g9
            omega
          have d18181 : (x 1 4).toNat = 1 := by
            have r18182 := hand1 (x 1 4) (x 1 14)
            have b18183 := hb (x 1 4)
            have b18184 := hb (x 1 4 && x 1 14)
            clear * - r18182 b18183 b18184 d18173
            omega
          have d18185 : (x 1 12).toNat = 1 := by
            have r18186 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
            have b18187 := hb (x 1 4)
            have b18188 := hb (x 1 12)
            clear * - r18186 b18187 b18188 d18181
            omega
          have d18189 : (x (-1) 2).toNat = 0 := by
            have r18190 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
            have e18191 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e18192 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b18193 := hb (x (-2) 3)
            have b18194 := hb (x (-1) 2)
            have b18195 := hb (x 0 13)
            have b18196 := hb (x 1 12)
            clear * - r18190 e18191 e18192 b18193 b18194 b18195 b18196 d18185 g14
            omega
          have d18197 : (x (-1) 10).toNat = 0 := by
            have r18198 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
            have b18199 := hb (x (-1) 2)
            have b18200 := hb (x (-1) 10)
            clear * - r18198 b18199 b18200 d18189
            omega
          have d18201 : (x (-2) 3).toNat = 0 := by
            have r18202 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
            have e18203 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e18204 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b18205 := hb (x (-2) 3)
            have b18206 := hb (x (-1) 2)
            have b18207 := hb (x 0 13)
            have b18208 := hb (x 1 12)
            clear * - r18202 e18203 e18204 b18205 b18206 b18207 b18208 d18185 g14 d18189
            omega
          have d18209 : (x (-2) 11).toNat = 0 := by
            have r18210 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
            have b18211 := hb (x (-2) 3)
            have b18212 := hb (x (-2) 11)
            clear * - r18210 b18211 b18212 d18201
            omega
          have d18213 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
            have r18214 := hand2 (x (-2) 1) (x (-2) 11)
            have b18215 := hb (x (-2) 11)
            have b18216 := hb (x (-2) 1 && x (-2) 11)
            clear * - r18214 b18215 b18216 d18209
            omega
          have d18217 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
            have r18218 := hand2 (x (-2) 2) (x (-2) 11)
            have b18219 := hb (x (-2) 11)
            have b18220 := hb (x (-2) 2 && x (-2) 11)
            clear * - r18218 b18219 b18220 d18209
            omega
          cases h18221 : x (-1) 4
          · have f18222 : (x (-1) 4).toNat = 0 := by rw [h18221]; rfl
            cases h18223 : x 1 7
            · have f18224 : (x 1 7).toNat = 0 := by rw [h18223]; rfl
              have d18225 : (x 1 7 && x 1 14).toNat = 0 := by
                have r18226 := hand1 (x 1 7) (x 1 14)
                have b18227 := hb (x 1 7)
                have b18228 := hb (x 1 7 && x 1 14)
                clear * - r18226 b18227 b18228 f18224
                omega
              have d18229 : (x 1 7 && x 1 11).toNat = 0 := by
                have r18230 := hand1 (x 1 7) (x 1 11)
                have b18231 := hb (x 1 7)
                have b18232 := hb (x 1 7 && x 1 11)
                clear * - r18230 b18231 b18232 f18224
                omega
              have d18233 : (x 8 7).toNat = 1 := by
                have r18234 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := hcov7 8
                have b18235 := hb (x 0 8)
                have b18236 := hb (x 8 7)
                have b18237 := hb (x 7 1 && x 7 8)
                have b18238 := hb (x 6 2 && x 6 9)
                have b18239 := hb (x 5 3 && x 5 10)
                have b18240 := hb (x 4 4 && x 4 11)
                have b18241 := hb (x 3 5 && x 3 12)
                have b18242 := hb (x 2 6 && x 2 13)
                have b18243 := hb (x 1 7 && x 1 14)
                clear * - r18234 b18235 b18236 b18237 b18238 b18239 b18240 b18241 b18242 b18243 d15421 d15445 d15473 d15505 d18132 d18032 d18225 f17782
                omega
              have d18244 : (x 15 8).toNat = 0 := by
                have r18245 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e18246 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e18247 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e18248 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e18249 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e18250 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e18251 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b18252 := hb (x 8 7)
                have b18253 := hb (x 9 6)
                have b18254 := hb (x 10 5)
                have b18255 := hb (x 11 4)
                have b18256 := hb (x 12 11)
                have b18257 := hb (x 13 10)
                have b18258 := hb (x 14 9)
                have b18259 := hb (x 15 8)
                clear * - r18245 e18246 e18247 e18248 e18249 e18250 e18251 b18252 b18253 b18254 b18255 b18256 b18257 b18258 b18259 d18233
                omega
              have d18260 : (x 14 9).toNat = 0 := by
                have r18261 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e18262 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e18263 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e18264 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e18265 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e18266 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e18267 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b18268 := hb (x 8 7)
                have b18269 := hb (x 9 6)
                have b18270 := hb (x 10 5)
                have b18271 := hb (x 11 4)
                have b18272 := hb (x 12 11)
                have b18273 := hb (x 13 10)
                have b18274 := hb (x 14 9)
                have b18275 := hb (x 15 8)
                clear * - r18261 e18262 e18263 e18264 e18265 e18266 e18267 b18268 b18269 b18270 b18271 b18272 b18273 b18274 b18275 d18244 d18233
                omega
              have d18276 : (x 13 10).toNat = 0 := by
                have r18277 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e18278 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e18279 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e18280 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e18281 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e18282 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e18283 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b18284 := hb (x 8 7)
                have b18285 := hb (x 9 6)
                have b18286 := hb (x 10 5)
                have b18287 := hb (x 11 4)
                have b18288 := hb (x 12 11)
                have b18289 := hb (x 13 10)
                have b18290 := hb (x 14 9)
                have b18291 := hb (x 15 8)
                clear * - r18277 e18278 e18279 e18280 e18281 e18282 e18283 b18284 b18285 b18286 b18287 b18288 b18289 b18290 b18291 d18244 d18260 d18233
                omega
              have d18292 : (x 13 1 && x 13 10).toNat = 0 := by
                have r18293 := hand2 (x 13 1) (x 13 10)
                have b18294 := hb (x 13 10)
                have b18295 := hb (x 13 1 && x 13 10)
                clear * - r18293 b18294 b18295 d18276
                omega
              have d18296 : (x 12 11).toNat = 0 := by
                have r18297 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e18298 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e18299 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e18300 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e18301 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e18302 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e18303 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b18304 := hb (x 8 7)
                have b18305 := hb (x 9 6)
                have b18306 := hb (x 10 5)
                have b18307 := hb (x 11 4)
                have b18308 := hb (x 12 11)
                have b18309 := hb (x 13 10)
                have b18310 := hb (x 14 9)
                have b18311 := hb (x 15 8)
                clear * - r18297 e18298 e18299 e18300 e18301 e18302 e18303 b18304 b18305 b18306 b18307 b18308 b18309 b18310 b18311 d18244 d18260 d18276 d18233
                omega
              have d18312 : (x 12 2 && x 12 11).toNat = 0 := by
                have r18313 := hand2 (x 12 2) (x 12 11)
                have b18314 := hb (x 12 11)
                have b18315 := hb (x 12 2 && x 12 11)
                clear * - r18313 b18314 b18315 d18296
                omega
              have d18316 : (x 11 4).toNat = 0 := by
                have r18317 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e18318 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e18319 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e18320 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e18321 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e18322 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e18323 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b18324 := hb (x 8 7)
                have b18325 := hb (x 9 6)
                have b18326 := hb (x 10 5)
                have b18327 := hb (x 11 4)
                have b18328 := hb (x 12 11)
                have b18329 := hb (x 13 10)
                have b18330 := hb (x 14 9)
                have b18331 := hb (x 15 8)
                clear * - r18317 e18318 e18319 e18320 e18321 e18322 e18323 b18324 b18325 b18326 b18327 b18328 b18329 b18330 b18331 d18244 d18260 d18276 d18296 d18233
                omega
              have d18332 : (x 11 1 && x 11 4).toNat = 0 := by
                have r18333 := hand2 (x 11 1) (x 11 4)
                have b18334 := hb (x 11 4)
                have b18335 := hb (x 11 1 && x 11 4)
                clear * - r18333 b18334 b18335 d18316
                omega
              have d18336 : (x 10 5).toNat = 0 := by
                have r18337 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e18338 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e18339 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e18340 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e18341 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e18342 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e18343 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b18344 := hb (x 8 7)
                have b18345 := hb (x 9 6)
                have b18346 := hb (x 10 5)
                have b18347 := hb (x 11 4)
                have b18348 := hb (x 12 11)
                have b18349 := hb (x 13 10)
                have b18350 := hb (x 14 9)
                have b18351 := hb (x 15 8)
                clear * - r18337 e18338 e18339 e18340 e18341 e18342 e18343 b18344 b18345 b18346 b18347 b18348 b18349 b18350 b18351 d18244 d18260 d18276 d18296 d18316 d18233
                omega
              have d18352 : (x 10 2 && x 10 5).toNat = 0 := by
                have r18353 := hand2 (x 10 2) (x 10 5)
                have b18354 := hb (x 10 5)
                have b18355 := hb (x 10 2 && x 10 5)
                clear * - r18353 b18354 b18355 d18336
                omega
              have d18356 : (x 9 6).toNat = 0 := by
                have r18357 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                have e18358 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                have e18359 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                have e18360 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                have e18361 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                have e18362 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                have e18363 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                have b18364 := hb (x 8 7)
                have b18365 := hb (x 9 6)
                have b18366 := hb (x 10 5)
                have b18367 := hb (x 11 4)
                have b18368 := hb (x 12 11)
                have b18369 := hb (x 13 10)
                have b18370 := hb (x 14 9)
                have b18371 := hb (x 15 8)
                clear * - r18357 e18358 e18359 e18360 e18361 e18362 e18363 b18364 b18365 b18366 b18367 b18368 b18369 b18370 b18371 d18244 d18260 d18276 d18296 d18316 d18336 d18233
                omega
              have d18372 : (x 9 3 && x 9 6).toNat = 0 := by
                have r18373 := hand2 (x 9 3) (x 9 6)
                have b18374 := hb (x 9 6)
                have b18375 := hb (x 9 3 && x 9 6)
                clear * - r18373 b18374 b18375 d18356
                omega
              have r18376 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
              have r18377 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
              have r18378 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
              have e18379 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e18380 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e18381 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e18382 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e18383 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e18384 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have r18385 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
              have e18386 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e18387 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have r18388 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e18389 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e18390 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have r18391 : 1 ≤ (x 12 3).toNat + (x 11 1 && x 11 4).toNat + (x 10 2 && x 10 5).toNat + (x 9 3 && x 9 6).toNat + (x 8 4 && x 8 7).toNat + (x 7 5 && x 7 8).toNat + (x 6 6 && x 6 9).toNat + (x 5 7 && x 5 10).toNat + (x 4 8 && x 4 11).toNat + (x 3 9 && x 3 12).toNat + (x 2 10 && x 2 13).toNat + (x 1 11 && x 1 14).toNat + (x 0 12).toNat := hcov3 12
              have r18392 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := hcov4 8
              have e18393 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
              have e18394 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
              have r18395 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
              have r18396 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := hcov9 14
              have r18397 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
              have r18398 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
              have r18399 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
              have r18400 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have r18401 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
              have r18402 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have r18403 := hand1 (x 8 4) (x 8 7)
              have r18404 := hand1 (x 1 11) (x 1 14)
              have r18405 := hand2 (x 6 2) (x 6 6)
              have r18406 := hand2 (x 5 3) (x 5 7)
              have r18407 := hand1 (x (-4) 4) (x (-4) 13)
              have r18408 := hand1 (x (-5) 5) (x (-5) 14)
              have r18409 := hand1 (x 11 3) (x 11 12)
              have r18410 := hand1 (x 10 4) (x 10 13)
              have r18411 := hand1 (x 9 5) (x 9 14)
              have r18412 := hand2 (x 5 1) (x 5 11)
              have r18413 := hand1 (x 11 1) (x 11 12)
              have r18414 := hand1 (x 10 2) (x 10 13)
              have r18415 := hand1 (x 9 3) (x 9 14)
              have r18416 := hand1 (x 13 1) (x 13 14)
              have b18417 := hb (x (-7) 7)
              have b18418 := hb (x (-6) 6)
              have b18419 := hb (x (-5) 5)
              have b18420 := hb (x (-4) 4)
              have b18421 := hb (x (-3) 11)
              have b18422 := hb (x (-2) 10)
              have b18423 := hb (x (-2) 14)
              have b18424 := hb (x (-1) 9)
              have b18425 := hb (x (-1) 13)
              have b18426 := hb (x 0 8)
              have b18427 := hb (x 0 9)
              have b18428 := hb (x 0 12)
              have b18429 := hb (x 0 14)
              have b18430 := hb (x 1 5)
              have b18431 := hb (x 1 11)
              have b18432 := hb (x 1 13)
              have b18433 := hb (x 2 10)
              have b18434 := hb (x 2 12)
              have b18435 := hb (x 3 9)
              have b18436 := hb (x 3 11)
              have b18437 := hb (x 4 8)
              have b18438 := hb (x 4 10)
              have b18439 := hb (x 5 3)
              have b18440 := hb (x 5 7)
              have b18441 := hb (x 5 9)
              have b18442 := hb (x 5 11)
              have b18443 := hb (x 6 2)
              have b18444 := hb (x 6 6)
              have b18445 := hb (x 6 8)
              have b18446 := hb (x 6 10)
              have b18447 := hb (x 7 5)
              have b18448 := hb (x 7 7)
              have b18449 := hb (x 7 13)
              have b18450 := hb (x 8 4)
              have b18451 := hb (x 8 6)
              have b18452 := hb (x 8 12)
              have b18453 := hb (x 9 3)
              have b18454 := hb (x 9 5)
              have b18455 := hb (x 10 2)
              have b18456 := hb (x 10 4)
              have b18457 := hb (x 11 1)
              have b18458 := hb (x 11 3)
              have b18459 := hb (x 12 2)
              have b18460 := hb (x 12 3)
              have b18461 := hb (x 12 11)
              have b18462 := hb (x 13 1)
              have b18463 := hb (x 13 2)
              have b18464 := hb (x 14 9)
              have b18465 := hb (x 14 13)
              have b18466 := hb (x 15 12)
              have b18467 := hb (x 11 1 && x 11 4)
              have b18468 := hb (x 10 2 && x 10 5)
              have b18469 := hb (x 9 3 && x 9 6)
              have b18470 := hb (x 8 4 && x 8 7)
              have b18471 := hb (x 7 5 && x 7 8)
              have b18472 := hb (x 6 6 && x 6 9)
              have b18473 := hb (x 5 7 && x 5 10)
              have b18474 := hb (x 4 8 && x 4 11)
              have b18475 := hb (x 3 9 && x 3 12)
              have b18476 := hb (x 2 10 && x 2 13)
              have b18477 := hb (x 1 11 && x 1 14)
              have b18478 := hb (x 6 2 && x 6 6)
              have b18479 := hb (x 5 3 && x 5 7)
              have b18480 := hb (x 4 4 && x 4 8)
              have b18481 := hb (x 3 5 && x 3 9)
              have b18482 := hb (x 2 6 && x 2 10)
              have b18483 := hb (x 1 7 && x 1 11)
              have b18484 := hb (x 0 8 && x 0 12)
              have b18485 := hb (x (-1) 9 && x (-1) 13)
              have b18486 := hb (x (-1) 1 && x (-1) 10)
              have b18487 := hb (x (-2) 2 && x (-2) 11)
              have b18488 := hb (x (-3) 3 && x (-3) 12)
              have b18489 := hb (x (-4) 4 && x (-4) 13)
              have b18490 := hb (x (-5) 5 && x (-5) 14)
              have b18491 := hb (x 13 1 && x 13 10)
              have b18492 := hb (x 12 2 && x 12 11)
              have b18493 := hb (x 11 3 && x 11 12)
              have b18494 := hb (x 10 4 && x 10 13)
              have b18495 := hb (x 9 5 && x 9 14)
              have b18496 := hb (x 5 1 && x 5 11)
              have b18497 := hb (x 4 2 && x 4 12)
              have b18498 := hb (x 3 3 && x 3 13)
              have b18499 := hb (x 2 4 && x 2 14)
              have b18500 := hb (x 11 1 && x 11 12)
              have b18501 := hb (x 10 2 && x 10 13)
              have b18502 := hb (x 9 3 && x 9 14)
              have b18503 := hb (x 13 1 && x 13 14)
              linarith only [r18376, r18377, r18378, e18379, e18380, e18381, e18382, e18383, e18384, r18385, e18386, e18387, r18388, e18389, e18390, r18391, r18392, e18393, e18394, r18395, r18396, r18397, r18398, r18399, r18400, r18401, r18402, r18403, r18404, r18405, r18406, r18407, r18408, r18409, r18410, r18411, r18412, r18413, r18414, r18415, r18416, b18417, b18418, b18419, b18420, b18421, b18422, b18423, b18424, b18425, b18426, b18427, b18428, b18429, b18430, b18431, b18432, b18433, b18434, b18435, b18436, b18437, b18438, b18439, b18440, b18441, b18442, b18443, b18444, b18445, b18446, b18447, b18448, b18449, b18450, b18451, b18452, b18453, b18454, b18455, b18456, b18457, b18458, b18459, b18460, b18461, b18462, b18463, b18464, b18465, b18466, b18467, b18468, b18469, b18470, b18471, b18472, b18473, b18474, b18475, b18476, b18477, b18478, b18479, b18480, b18481, b18482, b18483, b18484, b18485, b18486, b18487, b18488, b18489, b18490, b18491, b18492, b18493, b18494, b18495, b18496, b18497, b18498, b18499, b18500, b18501, b18502, b18503, g1, g3, g5, g6, f17782, g11, g13, g15, d17765, d18064, d18048, d18068, d17725, d17709, d17693, d17677, d18296, d18260, d18332, d18352, d18372, d15425, d15449, d15477, d15509, d18157, d18052, d18112, d18136, d18036, d18229, g16, g17, g19, d18217, g20, d18292, d18312, d18100, d18124, d17761]
            · have f18504 : (x 1 7).toNat = 1 := by rw [h18223]; rfl
              have d18505 : (x 8 8).toNat = 0 := by
                have r18506 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                have e18507 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e18508 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e18509 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e18510 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e18511 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e18512 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b18513 := hb (x 1 7)
                have b18514 := hb (x 2 6)
                have b18515 := hb (x 3 5)
                have b18516 := hb (x 4 4)
                have b18517 := hb (x 5 11)
                have b18518 := hb (x 6 10)
                have b18519 := hb (x 7 9)
                have b18520 := hb (x 8 8)
                clear * - r18506 e18507 e18508 e18509 e18510 e18511 e18512 b18513 b18514 b18515 b18516 b18517 b18518 b18519 b18520 d18108 d18128 d18028 f18504
                omega
              have d18521 : (x 7 9).toNat = 0 := by
                have r18522 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                have e18523 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e18524 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e18525 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e18526 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e18527 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e18528 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b18529 := hb (x 1 7)
                have b18530 := hb (x 2 6)
                have b18531 := hb (x 3 5)
                have b18532 := hb (x 4 4)
                have b18533 := hb (x 5 11)
                have b18534 := hb (x 6 10)
                have b18535 := hb (x 7 9)
                have b18536 := hb (x 8 8)
                clear * - r18522 e18523 e18524 e18525 e18526 e18527 e18528 b18529 b18530 b18531 b18532 b18533 b18534 b18535 b18536 d18505 d18108 d18128 d18028 f18504
                omega
              have d18537 : (x 6 10).toNat = 0 := by
                have r18538 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                have e18539 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e18540 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e18541 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e18542 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e18543 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e18544 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b18545 := hb (x 1 7)
                have b18546 := hb (x 2 6)
                have b18547 := hb (x 3 5)
                have b18548 := hb (x 4 4)
                have b18549 := hb (x 5 11)
                have b18550 := hb (x 6 10)
                have b18551 := hb (x 7 9)
                have b18552 := hb (x 8 8)
                clear * - r18538 e18539 e18540 e18541 e18542 e18543 e18544 b18545 b18546 b18547 b18548 b18549 b18550 b18551 b18552 d18505 d18521 d18108 d18128 d18028 f18504
                omega
              have d18553 : (x 6 1 && x 6 10).toNat = 0 := by
                have r18554 := hand2 (x 6 1) (x 6 10)
                have b18555 := hb (x 6 10)
                have b18556 := hb (x 6 1 && x 6 10)
                clear * - r18554 b18555 b18556 d18537
                omega
              have d18557 : (x 5 2 && x 5 11).toNat = 1 := by
                have r18558 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := hcov9 7
                have b18559 := hb (x 1 6)
                have b18560 := hb (x 7 9)
                have b18561 := hb (x 6 1 && x 6 10)
                have b18562 := hb (x 5 2 && x 5 11)
                have b18563 := hb (x 4 3 && x 4 12)
                have b18564 := hb (x 3 4 && x 3 13)
                have b18565 := hb (x 2 5 && x 2 14)
                clear * - r18558 b18559 b18560 b18561 b18562 b18563 b18564 b18565 d18521 d18553 d18104 d15533 d15553 d15557
                omega
              have d18566 : (x 5 11).toNat = 1 := by
                have r18567 := hand2 (x 5 2) (x 5 11)
                have b18568 := hb (x 5 11)
                have b18569 := hb (x 5 2 && x 5 11)
                clear * - r18567 b18568 b18569 d18557
                omega
              have r18570 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
              have e18571 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e18572 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e18573 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e18574 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e18575 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e18576 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b18577 := hb (x 1 7)
              have b18578 := hb (x 2 6)
              have b18579 := hb (x 3 5)
              have b18580 := hb (x 4 4)
              have b18581 := hb (x 5 11)
              have b18582 := hb (x 6 10)
              have b18583 := hb (x 7 9)
              have b18584 := hb (x 8 8)
              linarith only [r18570, e18571, e18572, e18573, e18574, e18575, e18576, b18577, b18578, b18579, b18580, b18581, b18582, b18583, b18584, d18505, d18521, d18537, d18566, d18108, d18128, d18028, f18504]
          · have f18585 : (x (-1) 4).toNat = 1 := by rw [h18221]; rfl
            have d18586 : (x (-1) 12).toNat = 1 := by
              have r18587 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
              have b18588 := hb (x (-1) 4)
              have b18589 := hb (x (-1) 12)
              clear * - r18587 b18588 b18589 f18585
              omega
            have d18590 : (x (-2) 13).toNat = 0 := by
              have r18591 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e18592 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e18593 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b18594 := hb (x (-4) 3)
              have b18595 := hb (x (-3) 2)
              have b18596 := hb (x (-2) 13)
              have b18597 := hb (x (-1) 12)
              clear * - r18591 e18592 e18593 b18594 b18595 b18596 b18597 d18586
              omega
            have d18598 : (x (-4) 2).toNat = 1 := by
              have r18599 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
              have b18600 := hb (x (-4) 2)
              have b18601 := hb (x (-2) 13)
              have b18602 := hb (x (-3) 1 && x (-3) 14)
              clear * - r18599 b18600 b18601 b18602 d18590 g31
              omega
            have d18603 : (x (-4) 14).toNat = 1 := by
              have r18604 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
              have b18605 := hb (x (-4) 2)
              have b18606 := hb (x (-4) 14)
              clear * - r18604 b18605 b18606 d18598
              omega
            have d18607 : (x (-5) 1).toNat = 0 := by
              have r18608 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
              have b18609 := hb (x (-5) 1)
              have b18610 := hb (x (-4) 14)
              clear * - r18608 b18609 b18610 d18603
              omega
            have d18611 : (x (-5) 13).toNat = 0 := by
              have r18612 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
              have b18613 := hb (x (-5) 1)
              have b18614 := hb (x (-5) 13)
              clear * - r18612 b18613 b18614 d18607
              omega
            have d18615 : (x (-3) 2).toNat = 0 := by
              have r18616 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e18617 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e18618 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b18619 := hb (x (-4) 3)
              have b18620 := hb (x (-3) 2)
              have b18621 := hb (x (-2) 13)
              have b18622 := hb (x (-1) 12)
              clear * - r18616 e18617 e18618 b18619 b18620 b18621 b18622 d18586 d18590
              omega
            have d18623 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
              have r18624 := hand1 (x (-3) 2) (x (-3) 12)
              have b18625 := hb (x (-3) 2)
              have b18626 := hb (x (-3) 2 && x (-3) 12)
              clear * - r18624 b18625 b18626 d18615
              omega
            have d18627 : (x (-4) 3).toNat = 0 := by
              have r18628 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e18629 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e18630 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b18631 := hb (x (-4) 3)
              have b18632 := hb (x (-3) 2)
              have b18633 := hb (x (-2) 13)
              have b18634 := hb (x (-1) 12)
              clear * - r18628 e18629 e18630 b18631 b18632 b18633 b18634 d18586 d18590 d18615
              omega
            have d18635 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
              have r18636 := hand1 (x (-4) 3) (x (-4) 14)
              have b18637 := hb (x (-4) 3)
              have b18638 := hb (x (-4) 3 && x (-4) 14)
              clear * - r18636 b18637 b18638 d18627
              omega
            have d18639 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
              have r18640 := hand1 (x (-4) 3) (x (-4) 13)
              have b18641 := hb (x (-4) 3)
              have b18642 := hb (x (-4) 3 && x (-4) 13)
              clear * - r18640 b18641 b18642 d18627
              omega
            have d18643 : (x (-2) 12).toNat = 0 := by
              have r18644 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
              have e18645 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e18646 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b18647 := hb (x (-5) 3)
              have b18648 := hb (x (-4) 2)
              have b18649 := hb (x (-3) 13)
              have b18650 := hb (x (-2) 12)
              clear * - r18644 e18645 e18646 b18647 b18648 b18649 b18650 g2 d18598
              omega
            have d18651 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
              have r18652 := hand2 (x (-2) 1) (x (-2) 12)
              have b18653 := hb (x (-2) 12)
              have b18654 := hb (x (-2) 1 && x (-2) 12)
              clear * - r18652 b18653 b18654 d18643
              omega
            have d18655 : (x (-5) 4).toNat = 1 := by
              have r18656 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := hcov11 (-1)
              have b18657 := hb (x (-5) 4)
              have b18658 := hb (x (-1) 11)
              have b18659 := hb (x (-2) 1 && x (-2) 12)
              have b18660 := hb (x (-3) 2 && x (-3) 13)
              have b18661 := hb (x (-4) 3 && x (-4) 14)
              clear * - r18656 b18657 b18658 b18659 b18660 b18661 d18084 d18651 g25 d18635
              omega
            have d18662 : (x (-5) 12).toNat = 1 := by
              have r18663 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
              have b18664 := hb (x (-5) 4)
              have b18665 := hb (x (-5) 12)
              clear * - r18663 b18664 b18665 d18655
              omega
            have d18666 : (x (-6) 13).toNat = 0 := by
              have r18667 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
              have e18668 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e18669 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b18670 := hb (x (-8) 3)
              have b18671 := hb (x (-7) 2)
              have b18672 := hb (x (-6) 13)
              have b18673 := hb (x (-5) 12)
              clear * - r18667 e18668 e18669 b18670 b18671 b18672 b18673 d18662
              omega
            have d18674 : (x (-6) 5).toNat = 0 := by
              have r18675 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
              have b18676 := hb (x (-6) 5)
              have b18677 := hb (x (-6) 13)
              clear * - r18675 b18676 b18677 d18666
              omega
            have d18678 : (x (-7) 2).toNat = 0 := by
              have r18679 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
              have e18680 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e18681 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b18682 := hb (x (-8) 3)
              have b18683 := hb (x (-7) 2)
              have b18684 := hb (x (-6) 13)
              have b18685 := hb (x (-5) 12)
              clear * - r18679 e18680 e18681 b18682 b18683 b18684 b18685 d18662 d18666
              omega
            have d18686 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
              have r18687 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
              have b18688 := hb (x (-7) 2)
              have b18689 := hb (x (-5) 13)
              have b18690 := hb (x (-6) 1 && x (-6) 14)
              clear * - r18687 b18688 b18689 b18690 d18611 d18678
              omega
            have d18691 : (x (-6) 1).toNat = 1 := by
              have r18692 := hand1 (x (-6) 1) (x (-6) 14)
              have b18693 := hb (x (-6) 1)
              have b18694 := hb (x (-6) 1 && x (-6) 14)
              clear * - r18692 b18693 b18694 d18686
              omega
            have d18695 : (x (-5) 14).toNat = 0 := by
              have r18696 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
              have b18697 := hb (x (-6) 1)
              have b18698 := hb (x (-5) 14)
              clear * - r18696 b18697 b18698 d18691
              omega
            have d18699 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
              have r18700 := hand2 (x (-5) 4) (x (-5) 14)
              have b18701 := hb (x (-5) 14)
              have b18702 := hb (x (-5) 4 && x (-5) 14)
              clear * - r18700 b18701 b18702 d18695
              omega
            have r18703 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
            have b18704 := hb (x (-6) 5)
            have b18705 := hb (x (-1) 10)
            have b18706 := hb (x (-2) 1 && x (-2) 11)
            have b18707 := hb (x (-3) 2 && x (-3) 12)
            have b18708 := hb (x (-4) 3 && x (-4) 13)
            have b18709 := hb (x (-5) 4 && x (-5) 14)
            linarith only [r18703, b18704, b18705, b18706, b18707, b18708, b18709, d18197, d18213, d18623, d18639, d18699, d18674]
      · have f18710 : (x 0 8).toNat = 1 := by rw [h17781]; rfl
        have d18711 : (x (-2) 10).toNat = 0 := by
          have r18712 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e18713 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e18714 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e18715 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e18716 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e18717 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e18718 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b18719 := hb (x (-7) 7)
          have b18720 := hb (x (-6) 6)
          have b18721 := hb (x (-5) 5)
          have b18722 := hb (x (-4) 4)
          have b18723 := hb (x (-3) 11)
          have b18724 := hb (x (-2) 10)
          have b18725 := hb (x (-1) 9)
          have b18726 := hb (x 0 8)
          clear * - r18712 e18713 e18714 e18715 e18716 e18717 e18718 b18719 b18720 b18721 b18722 b18723 b18724 b18725 b18726 f18710 g5 g1
          omega
        have d18727 : (x (-4) 4).toNat = 0 := by
          have r18728 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e18729 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e18730 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e18731 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e18732 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e18733 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e18734 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b18735 := hb (x (-7) 7)
          have b18736 := hb (x (-6) 6)
          have b18737 := hb (x (-5) 5)
          have b18738 := hb (x (-4) 4)
          have b18739 := hb (x (-3) 11)
          have b18740 := hb (x (-2) 10)
          have b18741 := hb (x (-1) 9)
          have b18742 := hb (x 0 8)
          clear * - r18728 e18729 e18730 e18731 e18732 e18733 e18734 b18735 b18736 b18737 b18738 b18739 b18740 b18741 b18742 f18710 g5 d18711 g1
          omega
        have d18743 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
          have r18744 := hand1 (x (-4) 4) (x (-4) 13)
          have b18745 := hb (x (-4) 4)
          have b18746 := hb (x (-4) 4 && x (-4) 13)
          clear * - r18744 b18745 b18746 d18727
          omega
        have d18747 : (x (-2) 2 && x (-2) 13).toNat = 1 := by
          have r18748 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
          have b18749 := hb (x (-4) 4)
          have b18750 := hb (x 0 11)
          have b18751 := hb (x (-1) 1 && x (-1) 12)
          have b18752 := hb (x (-2) 2 && x (-2) 13)
          have b18753 := hb (x (-3) 3 && x (-3) 14)
          clear * - r18748 b18749 b18750 b18751 b18752 b18753 d15579 g26 g27 d18727
          omega
        have d18754 : (x (-2) 13).toNat = 1 := by
          have r18755 := hand2 (x (-2) 2) (x (-2) 13)
          have b18756 := hb (x (-2) 13)
          have b18757 := hb (x (-2) 2 && x (-2) 13)
          clear * - r18755 b18756 b18757 d18747
          omega
        have d18758 : (x (-2) 1).toNat = 1 := by
          have r18759 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b18760 := hb (x (-2) 1)
          have b18761 := hb (x (-2) 13)
          clear * - r18759 b18760 b18761 d18754
          omega
        have d18762 : (x (-1) 14).toNat = 0 := by
          have r18763 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
          have b18764 := hb (x (-2) 1)
          have b18765 := hb (x (-1) 14)
          clear * - r18763 b18764 b18765 d18758
          omega
        have d18766 : (x (-1) 2).toNat = 0 := by
          have r18767 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b18768 := hb (x (-1) 2)
          have b18769 := hb (x (-1) 14)
          clear * - r18767 b18768 b18769 d18762
          omega
        have d18770 : (x 1 13).toNat = 1 := by
          have r18771 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
          have b18772 := hb (x (-1) 2)
          have b18773 := hb (x 1 13)
          have b18774 := hb (x 0 1 && x 0 14)
          clear * - r18771 b18772 b18773 b18774 g32 d18766
          omega
        have d18775 : (x 1 1).toNat = 1 := by
          have r18776 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b18777 := hb (x 1 1)
          have b18778 := hb (x 1 13)
          clear * - r18776 b18777 b18778 d18770
          omega
        have d18779 : (x 2 14).toNat = 0 := by
          have r18780 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
          have b18781 := hb (x 1 1)
          have b18782 := hb (x 2 14)
          clear * - r18780 b18781 b18782 d18775
          omega
        have d18783 : (x 2 1 && x 2 14).toNat = 0 := by
          have r18784 := hand2 (x 2 1) (x 2 14)
          have b18785 := hb (x 2 14)
          have b18786 := hb (x 2 1 && x 2 14)
          clear * - r18784 b18785 b18786 d18779
          omega
        have d18787 : (x 2 2).toNat = 0 := by
          have r18788 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b18789 := hb (x 2 2)
          have b18790 := hb (x 2 14)
          clear * - r18788 b18789 b18790 d18779
          omega
        have d18791 : (x 2 2 && x 2 12).toNat = 0 := by
          have r18792 := hand1 (x 2 2) (x 2 12)
          have b18793 := hb (x 2 2)
          have b18794 := hb (x 2 2 && x 2 12)
          clear * - r18792 b18793 b18794 d18787
          omega
        have d18795 : (x 1 3 && x 1 13).toNat = 1 := by
          have r18796 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := hcov10 4
          have b18797 := hb (x (-1) 5)
          have b18798 := hb (x 4 10)
          have b18799 := hb (x 3 1 && x 3 11)
          have b18800 := hb (x 2 2 && x 2 12)
          have b18801 := hb (x 1 3 && x 1 13)
          have b18802 := hb (x 0 4 && x 0 14)
          clear * - r18796 b18797 b18798 b18799 b18800 b18801 b18802 d17709 d17741 d18791 g24 g4
          omega
        have d18803 : (x 1 3).toNat = 1 := by
          have r18804 := hand1 (x 1 3) (x 1 13)
          have b18805 := hb (x 1 3)
          have b18806 := hb (x 1 3 && x 1 13)
          clear * - r18804 b18805 b18806 d18795
          omega
        have d18807 : (x 4 12).toNat = 0 := by
          have r18808 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e18809 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e18810 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b18811 := hb (x 1 3)
          have b18812 := hb (x 2 2)
          have b18813 := hb (x 3 13)
          have b18814 := hb (x 4 12)
          clear * - r18808 e18809 e18810 b18811 b18812 b18813 b18814 d18787 d18803
          omega
        have d18815 : (x 3 13).toNat = 0 := by
          have r18816 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e18817 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e18818 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b18819 := hb (x 1 3)
          have b18820 := hb (x 2 2)
          have b18821 := hb (x 3 13)
          have b18822 := hb (x 4 12)
          clear * - r18816 e18817 e18818 b18819 b18820 b18821 b18822 d18807 d18787 d18803
          omega
        have d18823 : (x 1 2).toNat = 1 := by
          have r18824 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
          have b18825 := hb (x 1 2)
          have b18826 := hb (x 3 13)
          have b18827 := hb (x 2 1 && x 2 14)
          clear * - r18824 b18825 b18826 b18827 d18815 d18783
          omega
        have d18828 : (x 3 12).toNat = 0 := by
          have r18829 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
          have e18830 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e18831 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b18832 := hb (x 0 3)
          have b18833 := hb (x 1 2)
          have b18834 := hb (x 2 13)
          have b18835 := hb (x 3 12)
          clear * - r18829 e18830 e18831 b18832 b18833 b18834 b18835 d18823 f15574
          omega
        have d18836 : (x 3 2 && x 3 12).toNat = 0 := by
          have r18837 := hand2 (x 3 2) (x 3 12)
          have b18838 := hb (x 3 12)
          have b18839 := hb (x 3 2 && x 3 12)
          clear * - r18837 b18838 b18839 d18828
          omega
        have d18840 : (x 2 13).toNat = 0 := by
          have r18841 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
          have e18842 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e18843 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b18844 := hb (x 0 3)
          have b18845 := hb (x 1 2)
          have b18846 := hb (x 2 13)
          have b18847 := hb (x 3 12)
          clear * - r18841 e18842 e18843 b18844 b18845 b18846 b18847 d18828 d18823 f15574
          omega
        have d18848 : (x 2 3 && x 2 13).toNat = 0 := by
          have r18849 := hand2 (x 2 3) (x 2 13)
          have b18850 := hb (x 2 13)
          have b18851 := hb (x 2 3 && x 2 13)
          clear * - r18849 b18850 b18851 d18840
          omega
        have d18852 : (x 1 4 && x 1 14).toNat = 1 := by
          have r18853 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
          have b18854 := hb (x 0 5)
          have b18855 := hb (x 5 10)
          have b18856 := hb (x 4 1 && x 4 11)
          have b18857 := hb (x 3 2 && x 3 12)
          have b18858 := hb (x 2 3 && x 2 13)
          have b18859 := hb (x 1 4 && x 1 14)
          clear * - r18853 b18854 b18855 b18856 b18857 b18858 b18859 d15453 d15497 d18836 d18848 g9
          omega
        have d18860 : (x 1 4).toNat = 1 := by
          have r18861 := hand1 (x 1 4) (x 1 14)
          have b18862 := hb (x 1 4)
          have b18863 := hb (x 1 4 && x 1 14)
          clear * - r18861 b18862 b18863 d18852
          omega
        have d18864 : (x 1 12).toNat = 1 := by
          have r18865 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b18866 := hb (x 1 4)
          have b18867 := hb (x 1 12)
          clear * - r18865 b18866 b18867 d18860
          omega
        have d18868 : (x (-2) 3).toNat = 0 := by
          have r18869 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
          have e18870 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e18871 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b18872 := hb (x (-2) 3)
          have b18873 := hb (x (-1) 2)
          have b18874 := hb (x 0 13)
          have b18875 := hb (x 1 12)
          clear * - r18869 e18870 e18871 b18872 b18873 b18874 b18875 d18864 g14 d18766
          omega
        have d18876 : (x (-2) 11).toNat = 0 := by
          have r18877 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
          have b18878 := hb (x (-2) 3)
          have b18879 := hb (x (-2) 11)
          clear * - r18877 b18878 b18879 d18868
          omega
        have d18880 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
          have r18881 := hand2 (x (-2) 2) (x (-2) 11)
          have b18882 := hb (x (-2) 11)
          have b18883 := hb (x (-2) 2 && x (-2) 11)
          clear * - r18881 b18882 b18883 d18876
          omega
        have d18884 : (x (-5) 5).toNat = 0 := by
          have r18885 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e18886 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e18887 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e18888 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e18889 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e18890 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e18891 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b18892 := hb (x (-7) 7)
          have b18893 := hb (x (-6) 6)
          have b18894 := hb (x (-5) 5)
          have b18895 := hb (x (-4) 4)
          have b18896 := hb (x (-3) 11)
          have b18897 := hb (x (-2) 10)
          have b18898 := hb (x (-1) 9)
          have b18899 := hb (x 0 8)
          clear * - r18885 e18886 e18887 e18888 e18889 e18890 e18891 b18892 b18893 b18894 b18895 b18896 b18897 b18898 b18899 f18710 g5 d18711 g1 d18727
          omega
        have d18900 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
          have r18901 := hand1 (x (-5) 5) (x (-5) 14)
          have b18902 := hb (x (-5) 5)
          have b18903 := hb (x (-5) 5 && x (-5) 14)
          clear * - r18901 b18902 b18903 d18884
          omega
        have d18904 : (x (-6) 6).toNat = 1 := by
          have r18905 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
          have b18906 := hb (x (-6) 6)
          have b18907 := hb (x 0 9)
          have b18908 := hb (x (-1) 1 && x (-1) 10)
          have b18909 := hb (x (-2) 2 && x (-2) 11)
          have b18910 := hb (x (-3) 3 && x (-3) 12)
          have b18911 := hb (x (-4) 4 && x (-4) 13)
          have b18912 := hb (x (-5) 5 && x (-5) 14)
          clear * - r18905 b18906 b18907 b18908 b18909 b18910 b18911 b18912 g11 g19 d18880 g20 d18743 d18900
          omega
        have r18913 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
        have e18914 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e18915 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e18916 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e18917 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e18918 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e18919 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b18920 := hb (x (-7) 7)
        have b18921 := hb (x (-6) 6)
        have b18922 := hb (x (-5) 5)
        have b18923 := hb (x (-4) 4)
        have b18924 := hb (x (-3) 11)
        have b18925 := hb (x (-2) 10)
        have b18926 := hb (x (-1) 9)
        have b18927 := hb (x 0 8)
        linarith only [r18913, e18914, e18915, e18916, e18917, e18918, e18919, b18920, b18921, b18922, b18923, b18924, b18925, b18926, b18927, f18710, g5, d18711, g1, d18727, d18884, d18904]
  · have f18928 : (x 0 3).toNat = 1 := by rw [h15573]; rfl
    have d18929 : (x 3 12).toNat = 0 := by
      have r18930 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
      have e18931 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e18932 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b18933 := hb (x 0 3)
      have b18934 := hb (x 1 2)
      have b18935 := hb (x 2 13)
      have b18936 := hb (x 3 12)
      clear * - r18930 e18931 e18932 b18933 b18934 b18935 b18936 f18928
      omega
    have d18937 : (x 3 1 && x 3 12).toNat = 0 := by
      have r18938 := hand2 (x 3 1) (x 3 12)
      have b18939 := hb (x 3 12)
      have b18940 := hb (x 3 1 && x 3 12)
      clear * - r18938 b18939 b18940 d18929
      omega
    have d18941 : (x 2 13).toNat = 0 := by
      have r18942 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
      have e18943 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e18944 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b18945 := hb (x 0 3)
      have b18946 := hb (x 1 2)
      have b18947 := hb (x 2 13)
      have b18948 := hb (x 3 12)
      clear * - r18942 e18943 e18944 b18945 b18946 b18947 b18948 d18929 f18928
      omega
    have d18949 : (x 2 2 && x 2 13).toNat = 0 := by
      have r18950 := hand2 (x 2 2) (x 2 13)
      have b18951 := hb (x 2 13)
      have b18952 := hb (x 2 2 && x 2 13)
      clear * - r18950 b18951 b18952 d18941
      omega
    have d18953 : (x 1 1 && x 1 14).toNat = 1 := by
      have r18954 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := hcov13 2
      have b18955 := hb (x 0 2)
      have b18956 := hb (x 2 13)
      have b18957 := hb (x 1 1 && x 1 14)
      clear * - r18954 b18955 b18956 b18957 d18941 g7
      omega
    have d18958 : (x 1 1).toNat = 1 := by
      have r18959 := hand1 (x 1 1) (x 1 14)
      have b18960 := hb (x 1 1)
      have b18961 := hb (x 1 1 && x 1 14)
      clear * - r18959 b18960 b18961 d18953
      omega
    have d18962 : (x 2 14).toNat = 0 := by
      have r18963 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
      have b18964 := hb (x 1 1)
      have b18965 := hb (x 2 14)
      clear * - r18963 b18964 b18965 d18958
      omega
    have d18966 : (x 2 1 && x 2 14).toNat = 0 := by
      have r18967 := hand2 (x 2 1) (x 2 14)
      have b18968 := hb (x 2 14)
      have b18969 := hb (x 2 1 && x 2 14)
      clear * - r18967 b18968 b18969 d18962
      omega
    have d18970 : (x 2 2).toNat = 0 := by
      have r18971 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b18972 := hb (x 2 2)
      have b18973 := hb (x 2 14)
      clear * - r18971 b18972 b18973 d18962
      omega
    have d18974 : (x 1 2).toNat = 0 := by
      have r18975 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
      have e18976 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e18977 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b18978 := hb (x 0 3)
      have b18979 := hb (x 1 2)
      have b18980 := hb (x 2 13)
      have b18981 := hb (x 3 12)
      clear * - r18975 e18976 e18977 b18978 b18979 b18980 b18981 d18929 d18941 f18928
      omega
    have d18982 : (x 3 13).toNat = 1 := by
      have r18983 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
      have b18984 := hb (x 1 2)
      have b18985 := hb (x 3 13)
      have b18986 := hb (x 2 1 && x 2 14)
      clear * - r18983 b18984 b18985 b18986 d18966 d18974
      omega
    have d18987 : (x 4 12).toNat = 0 := by
      have r18988 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e18989 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e18990 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b18991 := hb (x 1 3)
      have b18992 := hb (x 2 2)
      have b18993 := hb (x 3 13)
      have b18994 := hb (x 4 12)
      clear * - r18988 e18989 e18990 b18991 b18992 b18993 b18994 d18982 d18970
      omega
    have d18995 : (x 1 3).toNat = 0 := by
      have r18996 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e18997 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e18998 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b18999 := hb (x 1 3)
      have b19000 := hb (x 2 2)
      have b19001 := hb (x 3 13)
      have b19002 := hb (x 4 12)
      clear * - r18996 e18997 e18998 b18999 b19000 b19001 b19002 d18987 d18982 d18970
      omega
    have d19003 : (x 1 3 && x 1 14).toNat = 0 := by
      have r19004 := hand1 (x 1 3) (x 1 14)
      have b19005 := hb (x 1 3)
      have b19006 := hb (x 1 3 && x 1 14)
      clear * - r19004 b19005 b19006 d18995
      omega
    have r19007 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
    have b19008 := hb (x 0 4)
    have b19009 := hb (x 4 11)
    have b19010 := hb (x 3 1 && x 3 12)
    have b19011 := hb (x 2 2 && x 2 13)
    have b19012 := hb (x 1 3 && x 1 14)
    linarith only [r19007, b19008, b19009, b19010, b19011, b19012, d15481, d18937, d18949, d19003, g8]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b01 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-3) 13).toNat = 0)
    (g3 : (x (-2) 14).toNat = 1)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 13).toNat = 0)
    (g7 : (x 0 2).toNat = 0)
    (g8 : (x 0 4).toNat = 0)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 7).toNat = 1)
    (g11 : (x 0 9).toNat = 0)
    (g12 : (x 0 10).toNat = 0)
    (g13 : (x 0 12).toNat = 0)
    (g14 : (x 0 13).toNat = 0)
    (g15 : (x 0 14).toNat = 1)
    (g16 : (x 0 8 && x 0 12).toNat = 0)
    (g17 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g18 : (x 0 9 && x 0 14).toNat = 0)
    (g19 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g20 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g21 : (x 0 5 && x 0 14).toNat = 0)
    (g22 : (x 0 2 && x 0 12).toNat = 0)
    (g23 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g24 : (x 0 4 && x 0 14).toNat = 0)
    (g25 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g26 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g27 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g28 : (x 0 1 && x 0 12).toNat = 0)
    (g29 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g30 : (x 0 2 && x 0 13).toNat = 0)
    (g31 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g32 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b01_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32
