import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01001

Topic: combinatorics   Node: 044cff85d750

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 34 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 5).toNat = 0)
    (g1 : (x (-4) 4).toNat = 0)
    (g2 : (x 0 2).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 4).toNat = 0)
    (g5 : (x 0 6).toNat = 0)
    (g6 : (x 0 7).toNat = 0)
    (g7 : (x 0 9).toNat = 1)
    (g8 : (x 0 10).toNat = 0)
    (g9 : (x 0 11).toNat = 0)
    (g10 : (x 1 2).toNat = 0)
    (g11 : (x 1 6).toNat = 0)
    (g12 : (x 1 10).toNat = 0)
    (g13 : (x 2 1).toNat = 1)
    (g14 : (x 3 2).toNat = 0)
    (g15 : (x 3 4).toNat = 0)
    (g16 : (x 1 2 && x 1 6).toNat = 0)
    (g17 : (x 0 3 && x 0 7).toNat = 0)
    (g18 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g19 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g20 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g21 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g22 : (x 3 3 && x 3 12).toNat = 0)
    (g23 : (x 1 5 && x 1 14).toNat = 0)
    (g24 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g25 : (x 0 1 && x 0 11).toNat = 0)
    (g26 : (x 1 2 && x 1 13).toNat = 0)
    (g27 : (x 0 3 && x 0 14).toNat = 0)
    (g28 : (x 3 1 && x 3 12).toNat = 0)
    (g29 : (x 1 3 && x 1 14).toNat = 0)
    (g30 : (x 3 2 && x 3 13).toNat = 0)
    (g31 : (x 3 3 && x 3 14).toNat = 0)
    (g32 : (x 0 1 && x 0 14).toNat = 0)
    (g33 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d45418 : (x 1 8).toNat = 0 := by
    have r45419 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e45420 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e45421 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e45422 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e45423 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e45424 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e45425 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b45426 := hb (x (-6) 7)
    have b45427 := hb (x (-5) 6)
    have b45428 := hb (x (-4) 5)
    have b45429 := hb (x (-3) 4)
    have b45430 := hb (x (-2) 11)
    have b45431 := hb (x (-1) 10)
    have b45432 := hb (x 0 9)
    have b45433 := hb (x 1 8)
    clear * - r45419 e45420 e45421 e45422 e45423 e45424 e45425 b45426 b45427 b45428 b45429 b45430 b45431 b45432 b45433 g7
    omega
  have d45434 : (x (-1) 10).toNat = 0 := by
    have r45435 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e45436 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e45437 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e45438 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e45439 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e45440 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e45441 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b45442 := hb (x (-6) 7)
    have b45443 := hb (x (-5) 6)
    have b45444 := hb (x (-4) 5)
    have b45445 := hb (x (-3) 4)
    have b45446 := hb (x (-2) 11)
    have b45447 := hb (x (-1) 10)
    have b45448 := hb (x 0 9)
    have b45449 := hb (x 1 8)
    clear * - r45435 e45436 e45437 e45438 e45439 e45440 e45441 b45442 b45443 b45444 b45445 b45446 b45447 b45448 b45449 d45418 g7
    omega
  have d45450 : (x (-2) 11).toNat = 0 := by
    have r45451 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e45452 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e45453 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e45454 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e45455 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e45456 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e45457 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b45458 := hb (x (-6) 7)
    have b45459 := hb (x (-5) 6)
    have b45460 := hb (x (-4) 5)
    have b45461 := hb (x (-3) 4)
    have b45462 := hb (x (-2) 11)
    have b45463 := hb (x (-1) 10)
    have b45464 := hb (x 0 9)
    have b45465 := hb (x 1 8)
    clear * - r45451 e45452 e45453 e45454 e45455 e45456 e45457 b45458 b45459 b45460 b45461 b45462 b45463 b45464 b45465 d45418 g7 d45434
    omega
  have d45466 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
    have r45467 := hand2 (x (-2) 1) (x (-2) 11)
    have b45468 := hb (x (-2) 11)
    have b45469 := hb (x (-2) 1 && x (-2) 11)
    clear * - r45467 b45468 b45469 d45450
    omega
  have d45470 : (x (-3) 4).toNat = 0 := by
    have r45471 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e45472 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e45473 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e45474 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e45475 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e45476 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e45477 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b45478 := hb (x (-6) 7)
    have b45479 := hb (x (-5) 6)
    have b45480 := hb (x (-4) 5)
    have b45481 := hb (x (-3) 4)
    have b45482 := hb (x (-2) 11)
    have b45483 := hb (x (-1) 10)
    have b45484 := hb (x 0 9)
    have b45485 := hb (x 1 8)
    clear * - r45471 e45472 e45473 e45474 e45475 e45476 e45477 b45478 b45479 b45480 b45481 b45482 b45483 b45484 b45485 d45418 g7 d45434 d45450
    omega
  have d45486 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
    have r45487 := hand1 (x (-3) 4) (x (-3) 14)
    have b45488 := hb (x (-3) 4)
    have b45489 := hb (x (-3) 4 && x (-3) 14)
    clear * - r45487 b45488 b45489 d45470
    omega
  have d45490 : (x (-4) 5).toNat = 0 := by
    have r45491 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e45492 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e45493 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e45494 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e45495 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e45496 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e45497 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b45498 := hb (x (-6) 7)
    have b45499 := hb (x (-5) 6)
    have b45500 := hb (x (-4) 5)
    have b45501 := hb (x (-3) 4)
    have b45502 := hb (x (-2) 11)
    have b45503 := hb (x (-1) 10)
    have b45504 := hb (x 0 9)
    have b45505 := hb (x 1 8)
    clear * - r45491 e45492 e45493 e45494 e45495 e45496 e45497 b45498 b45499 b45500 b45501 b45502 b45503 b45504 b45505 d45418 g7 d45434 d45450 d45470
    omega
  cases h45506 : x 0 12
  · have f45507 : (x 0 12).toNat = 0 := by rw [h45506]; rfl
    cases h45508 : x 0 13
    · have f45509 : (x 0 13).toNat = 0 := by rw [h45508]; rfl
      cases h45510 : x 1 1
      · have f45511 : (x 1 1).toNat = 0 := by rw [h45510]; rfl
        have d45512 : (x 1 13).toNat = 0 := by
          have r45513 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b45514 := hb (x 1 1)
          have b45515 := hb (x 1 13)
          clear * - r45513 b45514 b45515 f45511
          omega
        have d45516 : (x (-1) 2).toNat = 1 := by
          have r45517 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
          have b45518 := hb (x (-1) 2)
          have b45519 := hb (x 1 13)
          have b45520 := hb (x 0 1 && x 0 14)
          clear * - r45517 b45518 b45519 b45520 d45512 g32
          omega
        have d45521 : (x (-1) 14).toNat = 1 := by
          have r45522 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b45523 := hb (x (-1) 2)
          have b45524 := hb (x (-1) 14)
          clear * - r45522 b45523 b45524 d45516
          omega
        have d45525 : (x (-2) 1).toNat = 0 := by
          have r45526 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
          have b45527 := hb (x (-2) 1)
          have b45528 := hb (x (-1) 14)
          clear * - r45526 b45527 b45528 d45521
          omega
        have d45529 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r45530 := hand1 (x (-2) 1) (x (-2) 14)
          have b45531 := hb (x (-2) 1)
          have b45532 := hb (x (-2) 1 && x (-2) 14)
          clear * - r45530 b45531 b45532 d45525
          omega
        have d45533 : (x (-2) 13).toNat = 0 := by
          have r45534 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b45535 := hb (x (-2) 1)
          have b45536 := hb (x (-2) 13)
          clear * - r45534 b45535 b45536 d45525
          omega
        have d45537 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
          have r45538 := hand2 (x (-2) 3) (x (-2) 13)
          have b45539 := hb (x (-2) 13)
          have b45540 := hb (x (-2) 3 && x (-2) 13)
          clear * - r45538 b45539 b45540 d45533
          omega
        have d45541 : (x (-2) 5).toNat = 0 := by
          have r45542 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b45543 := hb (x (-2) 5)
          have b45544 := hb (x (-2) 13)
          clear * - r45542 b45543 b45544 d45533
          omega
        have d45545 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
          have r45546 := hand1 (x (-2) 5) (x (-2) 9)
          have b45547 := hb (x (-2) 5)
          have b45548 := hb (x (-2) 5 && x (-2) 9)
          clear * - r45546 b45547 b45548 d45541
          omega
        have d45549 : (x (-2) 9).toNat = 0 := by
          have r45550 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
          have b45551 := hb (x (-2) 1)
          have b45552 := hb (x (-2) 9)
          clear * - r45550 b45551 b45552 d45525
          omega
        have d45553 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
          have r45554 := hand2 (x (-2) 2) (x (-2) 9)
          have b45555 := hb (x (-2) 9)
          have b45556 := hb (x (-2) 2 && x (-2) 9)
          clear * - r45554 b45555 b45556 d45549
          omega
        have d45557 : (x 1 12).toNat = 0 := by
          have r45558 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
          have e45559 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e45560 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b45561 := hb (x (-2) 3)
          have b45562 := hb (x (-1) 2)
          have b45563 := hb (x 0 13)
          have b45564 := hb (x 1 12)
          clear * - r45558 e45559 e45560 b45561 b45562 b45563 b45564 f45509 d45516
          omega
        have d45565 : (x 1 4).toNat = 0 := by
          have r45566 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b45567 := hb (x 1 4)
          have b45568 := hb (x 1 12)
          clear * - r45566 b45567 b45568 d45557
          omega
        have d45569 : (x (-1) 2 && x (-1) 12).toNat = 1 := by
          have r45570 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := hcov10 1
          have b45571 := hb (x (-4) 5)
          have b45572 := hb (x 1 10)
          have b45573 := hb (x 0 1 && x 0 11)
          have b45574 := hb (x (-1) 2 && x (-1) 12)
          have b45575 := hb (x (-2) 3 && x (-2) 13)
          have b45576 := hb (x (-3) 4 && x (-3) 14)
          clear * - r45570 b45571 b45572 b45573 b45574 b45575 b45576 g12 g25 d45537 d45486 d45490
          omega
        have d45577 : (x (-1) 12).toNat = 1 := by
          have r45578 := hand2 (x (-1) 2) (x (-1) 12)
          have b45579 := hb (x (-1) 12)
          have b45580 := hb (x (-1) 2 && x (-1) 12)
          clear * - r45578 b45579 b45580 d45569
          omega
        have d45581 : (x (-3) 2).toNat = 0 := by
          have r45582 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
          have e45583 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e45584 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b45585 := hb (x (-4) 3)
          have b45586 := hb (x (-3) 2)
          have b45587 := hb (x (-2) 13)
          have b45588 := hb (x (-1) 12)
          clear * - r45582 e45583 e45584 b45585 b45586 b45587 b45588 d45577 d45533
          omega
        have d45589 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
          have r45590 := hand1 (x (-3) 2) (x (-3) 12)
          have b45591 := hb (x (-3) 2)
          have b45592 := hb (x (-3) 2 && x (-3) 12)
          clear * - r45590 b45591 b45592 d45581
          omega
        have d45593 : (x (-3) 10).toNat = 0 := by
          have r45594 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
          have b45595 := hb (x (-3) 2)
          have b45596 := hb (x (-3) 10)
          clear * - r45594 b45595 b45596 d45581
          omega
        have d45597 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
          have r45598 := hand2 (x (-3) 3) (x (-3) 10)
          have b45599 := hb (x (-3) 10)
          have b45600 := hb (x (-3) 3 && x (-3) 10)
          clear * - r45598 b45599 b45600 d45593
          omega
        have d45601 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
          have r45602 := hand2 (x (-3) 6) (x (-3) 10)
          have b45603 := hb (x (-3) 10)
          have b45604 := hb (x (-3) 6 && x (-3) 10)
          clear * - r45602 b45603 b45604 d45593
          omega
        have d45605 : (x (-1) 13).toNat = 1 := by
          have r45606 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
          have b45607 := hb (x (-3) 2)
          have b45608 := hb (x (-1) 13)
          have b45609 := hb (x (-2) 1 && x (-2) 14)
          clear * - r45606 b45607 b45608 b45609 d45529 d45581
          omega
        have d45610 : (x (-2) 2).toNat = 0 := by
          have r45611 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
          have e45612 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e45613 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b45614 := hb (x (-3) 3)
          have b45615 := hb (x (-2) 2)
          have b45616 := hb (x (-1) 13)
          have b45617 := hb (x 0 12)
          clear * - r45611 e45612 e45613 b45614 b45615 b45616 b45617 f45507 d45605
          omega
        have d45618 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
          have r45619 := hand1 (x (-2) 2) (x (-2) 12)
          have b45620 := hb (x (-2) 2)
          have b45621 := hb (x (-2) 2 && x (-2) 12)
          clear * - r45619 b45620 b45621 d45610
          omega
        have d45622 : (x (-3) 3).toNat = 0 := by
          have r45623 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
          have e45624 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e45625 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b45626 := hb (x (-3) 3)
          have b45627 := hb (x (-2) 2)
          have b45628 := hb (x (-1) 13)
          have b45629 := hb (x 0 12)
          clear * - r45623 e45624 e45625 b45626 b45627 b45628 b45629 f45507 d45605 d45610
          omega
        have d45630 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
          have r45631 := hand1 (x (-3) 3) (x (-3) 13)
          have b45632 := hb (x (-3) 3)
          have b45633 := hb (x (-3) 3 && x (-3) 13)
          clear * - r45631 b45632 b45633 d45622
          omega
        have d45634 : (x (-4) 3).toNat = 0 := by
          have r45635 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
          have e45636 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e45637 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b45638 := hb (x (-4) 3)
          have b45639 := hb (x (-3) 2)
          have b45640 := hb (x (-2) 13)
          have b45641 := hb (x (-1) 12)
          clear * - r45635 e45636 e45637 b45638 b45639 b45640 b45641 d45577 d45533 d45581
          omega
        have d45642 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
          have r45643 := hand1 (x (-4) 3) (x (-4) 13)
          have b45644 := hb (x (-4) 3)
          have b45645 := hb (x (-4) 3 && x (-4) 13)
          clear * - r45643 b45644 b45645 d45634
          omega
        have d45646 : (x (-4) 11).toNat = 0 := by
          have r45647 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b45648 := hb (x (-4) 3)
          have b45649 := hb (x (-4) 11)
          clear * - r45647 b45648 b45649 d45634
          omega
        have d45650 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
          have r45651 := hand2 (x (-4) 7) (x (-4) 11)
          have b45652 := hb (x (-4) 11)
          have b45653 := hb (x (-4) 7 && x (-4) 11)
          clear * - r45651 b45652 b45653 d45646
          omega
        have d45654 : (x (-1) 1 && x (-1) 11).toNat = 1 := by
          have r45655 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
          have b45656 := hb (x (-5) 5)
          have b45657 := hb (x 0 10)
          have b45658 := hb (x (-1) 1 && x (-1) 11)
          have b45659 := hb (x (-2) 2 && x (-2) 12)
          have b45660 := hb (x (-3) 3 && x (-3) 13)
          have b45661 := hb (x (-4) 4 && x (-4) 14)
          clear * - r45655 b45656 b45657 b45658 b45659 b45660 b45661 g8 d45618 d45630 g24 g0
          omega
        have d45662 : (x (-1) 11).toNat = 1 := by
          have r45663 := hand2 (x (-1) 1) (x (-1) 11)
          have b45664 := hb (x (-1) 11)
          have b45665 := hb (x (-1) 1 && x (-1) 11)
          clear * - r45663 b45664 b45665 d45654
          omega
        have d45666 : (x (-1) 3).toNat = 1 := by
          have r45667 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
          have b45668 := hb (x (-1) 3)
          have b45669 := hb (x (-1) 11)
          clear * - r45667 b45668 b45669 d45662
          omega
        have d45670 : (x 2 12).toNat = 0 := by
          have r45671 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
          have e45672 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e45673 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b45674 := hb (x (-1) 3)
          have b45675 := hb (x 0 2)
          have b45676 := hb (x 1 13)
          have b45677 := hb (x 2 12)
          clear * - r45671 e45672 e45673 b45674 b45675 b45676 b45677 d45512 g2 d45666
          omega
        have d45678 : (x 2 1 && x 2 12).toNat = 0 := by
          have r45679 := hand2 (x 2 1) (x 2 12)
          have b45680 := hb (x 2 12)
          have b45681 := hb (x 2 1 && x 2 12)
          clear * - r45679 b45680 b45681 d45670
          omega
        have d45682 : (x 2 4).toNat = 0 := by
          have r45683 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
          have b45684 := hb (x 2 4)
          have b45685 := hb (x 2 12)
          clear * - r45683 b45684 b45685 d45670
          omega
        have d45686 : (x 2 4 && x 2 13).toNat = 0 := by
          have r45687 := hand1 (x 2 4) (x 2 13)
          have b45688 := hb (x 2 4)
          have b45689 := hb (x 2 4 && x 2 13)
          clear * - r45687 b45688 b45689 d45682
          omega
        cases h45690 : x 1 3
        · have f45691 : (x 1 3).toNat = 0 := by rw [h45690]; rfl
          cases h45692 : x (-1) 4
          · have f45693 : (x (-1) 4).toNat = 0 := by rw [h45692]; rfl
            have d45694 : (x 3 11).toNat = 1 := by
              have r45695 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
              have b45696 := hb (x (-1) 4)
              have b45697 := hb (x 3 11)
              have b45698 := hb (x 2 1 && x 2 12)
              have b45699 := hb (x 1 2 && x 1 13)
              have b45700 := hb (x 0 3 && x 0 14)
              clear * - r45695 b45696 b45697 b45698 b45699 b45700 d45678 g26 g27 f45693
              omega
            have d45701 : (x 3 3).toNat = 1 := by
              have r45702 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
              have b45703 := hb (x 3 3)
              have b45704 := hb (x 3 11)
              clear * - r45702 b45703 b45704 d45694
              omega
            have d45705 : (x 6 12).toNat = 0 := by
              have r45706 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
              have e45707 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e45708 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b45709 := hb (x 3 3)
              have b45710 := hb (x 4 2)
              have b45711 := hb (x 5 13)
              have b45712 := hb (x 6 12)
              clear * - r45706 e45707 e45708 b45709 b45710 b45711 b45712 d45701
              omega
            have d45713 : (x 6 1 && x 6 12).toNat = 0 := by
              have r45714 := hand2 (x 6 1) (x 6 12)
              have b45715 := hb (x 6 12)
              have b45716 := hb (x 6 1 && x 6 12)
              clear * - r45714 b45715 b45716 d45705
              omega
            have d45717 : (x 6 4).toNat = 0 := by
              have r45718 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
              have b45719 := hb (x 6 4)
              have b45720 := hb (x 6 12)
              clear * - r45718 b45719 b45720 d45705
              omega
            have d45721 : (x 5 13).toNat = 0 := by
              have r45722 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
              have e45723 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e45724 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b45725 := hb (x 3 3)
              have b45726 := hb (x 4 2)
              have b45727 := hb (x 5 13)
              have b45728 := hb (x 6 12)
              clear * - r45722 e45723 e45724 b45725 b45726 b45727 b45728 d45705 d45701
              omega
            have d45729 : (x 5 2 && x 5 13).toNat = 0 := by
              have r45730 := hand2 (x 5 2) (x 5 13)
              have b45731 := hb (x 5 13)
              have b45732 := hb (x 5 2 && x 5 13)
              clear * - r45730 b45731 b45732 d45721
              omega
            have d45733 : (x 4 1 && x 4 14).toNat = 1 := by
              have r45734 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
              have b45735 := hb (x 3 2)
              have b45736 := hb (x 5 13)
              have b45737 := hb (x 4 1 && x 4 14)
              clear * - r45734 b45735 b45736 b45737 d45721 g14
              omega
            have d45738 : (x 4 1).toNat = 1 := by
              have r45739 := hand1 (x 4 1) (x 4 14)
              have b45740 := hb (x 4 1)
              have b45741 := hb (x 4 1 && x 4 14)
              clear * - r45739 b45740 b45741 d45733
              omega
            have d45742 : (x 5 14).toNat = 0 := by
              have r45743 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
              have b45744 := hb (x 4 1)
              have b45745 := hb (x 5 14)
              clear * - r45743 b45744 b45745 d45738
              omega
            have d45746 : (x 5 1 && x 5 14).toNat = 0 := by
              have r45747 := hand2 (x 5 1) (x 5 14)
              have b45748 := hb (x 5 14)
              have b45749 := hb (x 5 1 && x 5 14)
              clear * - r45747 b45748 b45749 d45742
              omega
            have d45750 : (x 5 2).toNat = 0 := by
              have r45751 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b45752 := hb (x 5 2)
              have b45753 := hb (x 5 14)
              clear * - r45751 b45752 b45753 d45742
              omega
            have d45754 : (x 4 2).toNat = 0 := by
              have r45755 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
              have e45756 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e45757 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b45758 := hb (x 3 3)
              have b45759 := hb (x 4 2)
              have b45760 := hb (x 5 13)
              have b45761 := hb (x 6 12)
              clear * - r45755 e45756 e45757 b45758 b45759 b45760 b45761 d45705 d45721 d45701
              omega
            have d45762 : (x 4 2 && x 4 13).toNat = 0 := by
              have r45763 := hand1 (x 4 2) (x 4 13)
              have b45764 := hb (x 4 2)
              have b45765 := hb (x 4 2 && x 4 13)
              clear * - r45763 b45764 b45765 d45754
              omega
            have d45766 : (x 6 13).toNat = 1 := by
              have r45767 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
              have b45768 := hb (x 4 2)
              have b45769 := hb (x 6 13)
              have b45770 := hb (x 5 1 && x 5 14)
              clear * - r45767 b45768 b45769 b45770 d45746 d45754
              omega
            have d45771 : (x 6 1).toNat = 1 := by
              have r45772 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
              have b45773 := hb (x 6 1)
              have b45774 := hb (x 6 13)
              clear * - r45772 b45773 b45774 d45766
              omega
            have d45775 : (x 7 14).toNat = 0 := by
              have r45776 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
              have b45777 := hb (x 6 1)
              have b45778 := hb (x 7 14)
              clear * - r45776 b45777 b45778 d45771
              omega
            have d45779 : (x 7 3 && x 7 14).toNat = 0 := by
              have r45780 := hand2 (x 7 3) (x 7 14)
              have b45781 := hb (x 7 14)
              have b45782 := hb (x 7 3 && x 7 14)
              clear * - r45780 b45781 b45782 d45775
              omega
            have d45783 : (x 7 2).toNat = 0 := by
              have r45784 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b45785 := hb (x 7 2)
              have b45786 := hb (x 7 14)
              clear * - r45784 b45785 b45786 d45775
              omega
            have d45787 : (x 7 12).toNat = 0 := by
              have r45788 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
              have e45789 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e45790 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b45791 := hb (x 4 3)
              have b45792 := hb (x 5 2)
              have b45793 := hb (x 6 13)
              have b45794 := hb (x 7 12)
              clear * - r45788 e45789 e45790 b45791 b45792 b45793 b45794 d45766 d45750
              omega
            have d45795 : (x 7 4).toNat = 0 := by
              have r45796 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
              have b45797 := hb (x 7 4)
              have b45798 := hb (x 7 12)
              clear * - r45796 b45797 b45798 d45787
              omega
            have d45799 : (x 4 3).toNat = 0 := by
              have r45800 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
              have e45801 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e45802 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b45803 := hb (x 4 3)
              have b45804 := hb (x 5 2)
              have b45805 := hb (x 6 13)
              have b45806 := hb (x 7 12)
              clear * - r45800 e45801 e45802 b45803 b45804 b45805 b45806 d45787 d45766 d45750
              omega
            have d45807 : (x 4 3 && x 4 14).toNat = 0 := by
              have r45808 := hand1 (x 4 3) (x 4 14)
              have b45809 := hb (x 4 3)
              have b45810 := hb (x 4 3 && x 4 14)
              clear * - r45808 b45809 b45810 d45799
              omega
            have d45811 : (x 7 11).toNat = 1 := by
              have r45812 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
              have b45813 := hb (x 3 4)
              have b45814 := hb (x 7 11)
              have b45815 := hb (x 6 1 && x 6 12)
              have b45816 := hb (x 5 2 && x 5 13)
              have b45817 := hb (x 4 3 && x 4 14)
              clear * - r45812 b45813 b45814 b45815 b45816 b45817 d45713 d45729 d45807 g15
              omega
            have d45818 : (x 7 3).toNat = 1 := by
              have r45819 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
              have b45820 := hb (x 7 3)
              have b45821 := hb (x 7 11)
              clear * - r45819 b45820 b45821 d45811
              omega
            have d45822 : (x 10 12).toNat = 0 := by
              have r45823 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
              have e45824 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e45825 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b45826 := hb (x 7 3)
              have b45827 := hb (x 8 2)
              have b45828 := hb (x 9 13)
              have b45829 := hb (x 10 12)
              clear * - r45823 e45824 e45825 b45826 b45827 b45828 b45829 d45818
              omega
            have d45830 : (x 10 1 && x 10 12).toNat = 0 := by
              have r45831 := hand2 (x 10 1) (x 10 12)
              have b45832 := hb (x 10 12)
              have b45833 := hb (x 10 1 && x 10 12)
              clear * - r45831 b45832 b45833 d45822
              omega
            have d45834 : (x 10 4).toNat = 0 := by
              have r45835 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
              have b45836 := hb (x 10 4)
              have b45837 := hb (x 10 12)
              clear * - r45835 b45836 b45837 d45822
              omega
            have d45838 : (x 9 13).toNat = 0 := by
              have r45839 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
              have e45840 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e45841 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b45842 := hb (x 7 3)
              have b45843 := hb (x 8 2)
              have b45844 := hb (x 9 13)
              have b45845 := hb (x 10 12)
              clear * - r45839 e45840 e45841 b45842 b45843 b45844 b45845 d45822 d45818
              omega
            have d45846 : (x 9 2 && x 9 13).toNat = 0 := by
              have r45847 := hand2 (x 9 2) (x 9 13)
              have b45848 := hb (x 9 13)
              have b45849 := hb (x 9 2 && x 9 13)
              clear * - r45847 b45848 b45849 d45838
              omega
            have d45850 : (x 8 1 && x 8 14).toNat = 1 := by
              have r45851 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
              have b45852 := hb (x 7 2)
              have b45853 := hb (x 9 13)
              have b45854 := hb (x 8 1 && x 8 14)
              clear * - r45851 b45852 b45853 b45854 d45838 d45783
              omega
            have d45855 : (x 8 14).toNat = 1 := by
              have r45856 := hand2 (x 8 1) (x 8 14)
              have b45857 := hb (x 8 14)
              have b45858 := hb (x 8 1 && x 8 14)
              clear * - r45856 b45857 b45858 d45850
              omega
            have d45859 : (x 7 1).toNat = 0 := by
              have r45860 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
              have b45861 := hb (x 7 1)
              have b45862 := hb (x 8 14)
              clear * - r45860 b45861 b45862 d45855
              omega
            have d45863 : (x 7 13).toNat = 0 := by
              have r45864 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
              have b45865 := hb (x 7 1)
              have b45866 := hb (x 7 13)
              clear * - r45864 b45865 b45866 d45859
              omega
            have d45867 : (x 6 1 && x 6 14).toNat = 1 := by
              have r45868 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
              have b45869 := hb (x 5 2)
              have b45870 := hb (x 7 13)
              have b45871 := hb (x 6 1 && x 6 14)
              clear * - r45868 b45869 b45870 b45871 d45863 d45750
              omega
            have d45872 : (x 6 14).toNat = 1 := by
              have r45873 := hand2 (x 6 1) (x 6 14)
              have b45874 := hb (x 6 14)
              have b45875 := hb (x 6 1 && x 6 14)
              clear * - r45873 b45874 b45875 d45867
              omega
            have d45876 : (x 5 1).toNat = 0 := by
              have r45877 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
              have b45878 := hb (x 5 1)
              have b45879 := hb (x 6 14)
              clear * - r45877 b45878 b45879 d45872
              omega
            have d45880 : (x 5 1 && x 5 12).toNat = 0 := by
              have r45881 := hand1 (x 5 1) (x 5 12)
              have b45882 := hb (x 5 1)
              have b45883 := hb (x 5 1 && x 5 12)
              clear * - r45881 b45882 b45883 d45876
              omega
            have d45884 : (x 6 11).toNat = 1 := by
              have r45885 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
              have b45886 := hb (x 2 4)
              have b45887 := hb (x 6 11)
              have b45888 := hb (x 5 1 && x 5 12)
              have b45889 := hb (x 4 2 && x 4 13)
              have b45890 := hb (x 3 3 && x 3 14)
              clear * - r45885 b45886 b45887 b45888 b45889 b45890 d45880 d45762 g31 d45682
              omega
            have d45891 : (x 6 3).toNat = 1 := by
              have r45892 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
              have b45893 := hb (x 6 3)
              have b45894 := hb (x 6 11)
              clear * - r45892 b45893 b45894 d45884
              omega
            have d45895 : (x 9 12).toNat = 0 := by
              have r45896 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
              have e45897 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e45898 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b45899 := hb (x 6 3)
              have b45900 := hb (x 7 2)
              have b45901 := hb (x 8 13)
              have b45902 := hb (x 9 12)
              clear * - r45896 e45897 e45898 b45899 b45900 b45901 b45902 d45783 d45891
              omega
            have d45903 : (x 9 1 && x 9 12).toNat = 0 := by
              have r45904 := hand2 (x 9 1) (x 9 12)
              have b45905 := hb (x 9 12)
              have b45906 := hb (x 9 1 && x 9 12)
              clear * - r45904 b45905 b45906 d45895
              omega
            have d45907 : (x 8 13).toNat = 0 := by
              have r45908 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
              have e45909 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e45910 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b45911 := hb (x 6 3)
              have b45912 := hb (x 7 2)
              have b45913 := hb (x 8 13)
              have b45914 := hb (x 9 12)
              clear * - r45908 e45909 e45910 b45911 b45912 b45913 b45914 d45895 d45783 d45891
              omega
            have d45915 : (x 8 2 && x 8 13).toNat = 0 := by
              have r45916 := hand2 (x 8 2) (x 8 13)
              have b45917 := hb (x 8 13)
              have b45918 := hb (x 8 2 && x 8 13)
              clear * - r45916 b45917 b45918 d45907
              omega
            have d45919 : (x 10 11).toNat = 1 := by
              have r45920 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := hcov11 10
              have b45921 := hb (x 6 4)
              have b45922 := hb (x 10 11)
              have b45923 := hb (x 9 1 && x 9 12)
              have b45924 := hb (x 8 2 && x 8 13)
              have b45925 := hb (x 7 3 && x 7 14)
              clear * - r45920 b45921 b45922 b45923 b45924 b45925 d45903 d45915 d45779 d45717
              omega
            have d45926 : (x 10 3).toNat = 1 := by
              have r45927 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
              have b45928 := hb (x 10 3)
              have b45929 := hb (x 10 11)
              clear * - r45927 b45928 b45929 d45919
              omega
            have d45930 : (x 13 12).toNat = 0 := by
              have r45931 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
              have e45932 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e45933 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b45934 := hb (x 10 3)
              have b45935 := hb (x 11 2)
              have b45936 := hb (x 12 13)
              have b45937 := hb (x 13 12)
              clear * - r45931 e45932 e45933 b45934 b45935 b45936 b45937 d45926
              omega
            have d45938 : (x 13 1 && x 13 12).toNat = 0 := by
              have r45939 := hand2 (x 13 1) (x 13 12)
              have b45940 := hb (x 13 12)
              have b45941 := hb (x 13 1 && x 13 12)
              clear * - r45939 b45940 b45941 d45930
              omega
            have d45942 : (x 12 13).toNat = 0 := by
              have r45943 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
              have e45944 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e45945 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b45946 := hb (x 10 3)
              have b45947 := hb (x 11 2)
              have b45948 := hb (x 12 13)
              have b45949 := hb (x 13 12)
              clear * - r45943 e45944 e45945 b45946 b45947 b45948 b45949 d45930 d45926
              omega
            have d45950 : (x 12 2 && x 12 13).toNat = 0 := by
              have r45951 := hand2 (x 12 2) (x 12 13)
              have b45952 := hb (x 12 13)
              have b45953 := hb (x 12 2 && x 12 13)
              clear * - r45951 b45952 b45953 d45942
              omega
            have d45954 : (x 11 2).toNat = 0 := by
              have r45955 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
              have e45956 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e45957 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b45958 := hb (x 10 3)
              have b45959 := hb (x 11 2)
              have b45960 := hb (x 12 13)
              have b45961 := hb (x 13 12)
              clear * - r45955 e45956 e45957 b45958 b45959 b45960 b45961 d45930 d45942 d45926
              omega
            have d45962 : (x 8 1).toNat = 1 := by
              have r45963 := hand1 (x 8 1) (x 8 14)
              have b45964 := hb (x 8 1)
              have b45965 := hb (x 8 1 && x 8 14)
              clear * - r45963 b45964 b45965 d45850
              omega
            have d45966 : (x 9 14).toNat = 0 := by
              have r45967 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
              have b45968 := hb (x 8 1)
              have b45969 := hb (x 9 14)
              clear * - r45967 b45968 b45969 d45962
              omega
            have d45970 : (x 9 1 && x 9 14).toNat = 0 := by
              have r45971 := hand2 (x 9 1) (x 9 14)
              have b45972 := hb (x 9 14)
              have b45973 := hb (x 9 1 && x 9 14)
              clear * - r45971 b45972 b45973 d45966
              omega
            have d45974 : (x 9 2).toNat = 0 := by
              have r45975 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
              have b45976 := hb (x 9 2)
              have b45977 := hb (x 9 14)
              clear * - r45975 b45976 b45977 d45966
              omega
            have d45978 : (x 8 2).toNat = 0 := by
              have r45979 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
              have e45980 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e45981 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b45982 := hb (x 7 3)
              have b45983 := hb (x 8 2)
              have b45984 := hb (x 9 13)
              have b45985 := hb (x 10 12)
              clear * - r45979 e45980 e45981 b45982 b45983 b45984 b45985 d45822 d45838 d45818
              omega
            have d45986 : (x 10 13).toNat = 1 := by
              have r45987 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
              have b45988 := hb (x 8 2)
              have b45989 := hb (x 10 13)
              have b45990 := hb (x 9 1 && x 9 14)
              clear * - r45987 b45988 b45989 b45990 d45970 d45978
              omega
            have d45991 : (x 10 1).toNat = 1 := by
              have r45992 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
              have b45993 := hb (x 10 1)
              have b45994 := hb (x 10 13)
              clear * - r45992 b45993 b45994 d45986
              omega
            have d45995 : (x 11 14).toNat = 0 := by
              have r45996 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
              have b45997 := hb (x 10 1)
              have b45998 := hb (x 11 14)
              clear * - r45996 b45997 b45998 d45991
              omega
            have d45999 : (x 11 1 && x 11 14).toNat = 0 := by
              have r46000 := hand2 (x 11 1) (x 11 14)
              have b46001 := hb (x 11 14)
              have b46002 := hb (x 11 1 && x 11 14)
              clear * - r46000 b46001 b46002 d45995
              omega
            have d46003 : (x 10 2).toNat = 1 := by
              have r46004 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
              have b46005 := hb (x 10 2)
              have b46006 := hb (x 12 13)
              have b46007 := hb (x 11 1 && x 11 14)
              clear * - r46004 b46005 b46006 b46007 d45942 d45999
              omega
            have d46008 : (x 12 12).toNat = 0 := by
              have r46009 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
              have e46010 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e46011 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b46012 := hb (x 9 3)
              have b46013 := hb (x 10 2)
              have b46014 := hb (x 11 13)
              have b46015 := hb (x 12 12)
              clear * - r46009 e46010 e46011 b46012 b46013 b46014 b46015 d46003
              omega
            have d46016 : (x 12 4).toNat = 0 := by
              have r46017 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
              have b46018 := hb (x 12 4)
              have b46019 := hb (x 12 12)
              clear * - r46017 b46018 b46019 d46008
              omega
            have d46020 : (x 12 4 && x 12 14).toNat = 0 := by
              have r46021 := hand1 (x 12 4) (x 12 14)
              have b46022 := hb (x 12 4)
              have b46023 := hb (x 12 4 && x 12 14)
              clear * - r46021 b46022 b46023 d46016
              omega
            have d46024 : (x 11 13).toNat = 0 := by
              have r46025 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
              have e46026 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e46027 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b46028 := hb (x 9 3)
              have b46029 := hb (x 10 2)
              have b46030 := hb (x 11 13)
              have b46031 := hb (x 12 12)
              clear * - r46025 e46026 e46027 b46028 b46029 b46030 b46031 d46008 d46003
              omega
            have d46032 : (x 11 5).toNat = 0 := by
              have r46033 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
              have b46034 := hb (x 11 5)
              have b46035 := hb (x 11 13)
              clear * - r46033 b46034 b46035 d46024
              omega
            have d46036 : (x 11 3 && x 11 14).toNat = 0 := by
              have r46037 := hand2 (x 11 3) (x 11 14)
              have b46038 := hb (x 11 14)
              have b46039 := hb (x 11 3 && x 11 14)
              clear * - r46037 b46038 b46039 d45995
              omega
            have d46040 : (x 14 11).toNat = 1 := by
              have r46041 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := hcov11 14
              have b46042 := hb (x 10 4)
              have b46043 := hb (x 14 11)
              have b46044 := hb (x 13 1 && x 13 12)
              have b46045 := hb (x 12 2 && x 12 13)
              have b46046 := hb (x 11 3 && x 11 14)
              clear * - r46041 b46042 b46043 b46044 b46045 b46046 d45938 d45950 d46036 d45834
              omega
            have d46047 : (x 14 3).toNat = 1 := by
              have r46048 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
              have b46049 := hb (x 14 3)
              have b46050 := hb (x 14 11)
              clear * - r46048 b46049 b46050 d46040
              omega
            have d46051 : (x 17 12).toNat = 0 := by
              have r46052 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
              have e46053 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e46054 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b46055 := hb (x 14 3)
              have b46056 := hb (x 15 2)
              have b46057 := hb (x 16 13)
              have b46058 := hb (x 17 12)
              clear * - r46052 e46053 e46054 b46055 b46056 b46057 b46058 d46047
              omega
            have d46059 : (x 16 13).toNat = 0 := by
              have r46060 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
              have e46061 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e46062 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b46063 := hb (x 14 3)
              have b46064 := hb (x 15 2)
              have b46065 := hb (x 16 13)
              have b46066 := hb (x 17 12)
              clear * - r46060 e46061 e46062 b46063 b46064 b46065 b46066 d46051 d46047
              omega
            have d46067 : (x 15 2).toNat = 0 := by
              have r46068 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
              have e46069 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e46070 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b46071 := hb (x 14 3)
              have b46072 := hb (x 15 2)
              have b46073 := hb (x 16 13)
              have b46074 := hb (x 17 12)
              clear * - r46068 e46069 e46070 b46071 b46072 b46073 b46074 d46051 d46059 d46047
              omega
            have d46075 : (x 11 12).toNat = 0 := by
              have r46076 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
              have e46077 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e46078 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b46079 := hb (x 8 3)
              have b46080 := hb (x 9 2)
              have b46081 := hb (x 10 13)
              have b46082 := hb (x 11 12)
              clear * - r46076 e46077 e46078 b46079 b46080 b46081 b46082 d45986 d45974
              omega
            have d46083 : (x 11 4).toNat = 0 := by
              have r46084 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
              have b46085 := hb (x 11 4)
              have b46086 := hb (x 11 12)
              clear * - r46084 b46085 b46086 d46075
              omega
            have d46087 : (x 8 3).toNat = 0 := by
              have r46088 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
              have e46089 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e46090 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b46091 := hb (x 8 3)
              have b46092 := hb (x 9 2)
              have b46093 := hb (x 10 13)
              have b46094 := hb (x 11 12)
              clear * - r46088 e46089 e46090 b46091 b46092 b46093 b46094 d46075 d45986 d45974
              omega
            have d46095 : (x 8 3 && x 8 14).toNat = 0 := by
              have r46096 := hand1 (x 8 3) (x 8 14)
              have b46097 := hb (x 8 3)
              have b46098 := hb (x 8 3 && x 8 14)
              clear * - r46096 b46097 b46098 d46087
              omega
            have d46099 : (x 11 11).toNat = 1 := by
              have r46100 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
              have b46101 := hb (x 7 4)
              have b46102 := hb (x 11 11)
              have b46103 := hb (x 10 1 && x 10 12)
              have b46104 := hb (x 9 2 && x 9 13)
              have b46105 := hb (x 8 3 && x 8 14)
              clear * - r46100 b46101 b46102 b46103 b46104 b46105 d45830 d45846 d46095 d45795
              omega
            have d46106 : (x 11 3).toNat = 1 := by
              have r46107 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
              have b46108 := hb (x 11 3)
              have b46109 := hb (x 11 11)
              clear * - r46107 b46108 b46109 d46099
              omega
            have d46110 : (x 14 12).toNat = 0 := by
              have r46111 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
              have e46112 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e46113 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b46114 := hb (x 11 3)
              have b46115 := hb (x 12 2)
              have b46116 := hb (x 13 13)
              have b46117 := hb (x 14 12)
              clear * - r46111 e46112 e46113 b46114 b46115 b46116 b46117 d46106
              omega
            have d46118 : (x 14 1 && x 14 12).toNat = 0 := by
              have r46119 := hand2 (x 14 1) (x 14 12)
              have b46120 := hb (x 14 12)
              have b46121 := hb (x 14 1 && x 14 12)
              clear * - r46119 b46120 b46121 d46110
              omega
            have d46122 : (x 14 2 && x 14 12).toNat = 0 := by
              have r46123 := hand2 (x 14 2) (x 14 12)
              have b46124 := hb (x 14 12)
              have b46125 := hb (x 14 2 && x 14 12)
              clear * - r46123 b46124 b46125 d46110
              omega
            have d46126 : (x 13 13).toNat = 0 := by
              have r46127 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
              have e46128 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e46129 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b46130 := hb (x 11 3)
              have b46131 := hb (x 12 2)
              have b46132 := hb (x 13 13)
              have b46133 := hb (x 14 12)
              clear * - r46127 e46128 e46129 b46130 b46131 b46132 b46133 d46110 d46106
              omega
            have d46134 : (x 13 2 && x 13 13).toNat = 0 := by
              have r46135 := hand2 (x 13 2) (x 13 13)
              have b46136 := hb (x 13 13)
              have b46137 := hb (x 13 2 && x 13 13)
              clear * - r46135 b46136 b46137 d46126
              omega
            have d46138 : (x 13 3 && x 13 13).toNat = 0 := by
              have r46139 := hand2 (x 13 3) (x 13 13)
              have b46140 := hb (x 13 13)
              have b46141 := hb (x 13 3 && x 13 13)
              clear * - r46139 b46140 b46141 d46126
              omega
            have d46142 : (x 12 1 && x 12 14).toNat = 1 := by
              have r46143 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
              have b46144 := hb (x 11 2)
              have b46145 := hb (x 13 13)
              have b46146 := hb (x 12 1 && x 12 14)
              clear * - r46143 b46144 b46145 b46146 d46126 d45954
              omega
            have d46147 : (x 12 1).toNat = 1 := by
              have r46148 := hand1 (x 12 1) (x 12 14)
              have b46149 := hb (x 12 1)
              have b46150 := hb (x 12 1 && x 12 14)
              clear * - r46148 b46149 b46150 d46142
              omega
            have d46151 : (x 13 14).toNat = 0 := by
              have r46152 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
              have b46153 := hb (x 12 1)
              have b46154 := hb (x 13 14)
              clear * - r46152 b46153 b46154 d46147
              omega
            have d46155 : (x 13 1 && x 13 14).toNat = 0 := by
              have r46156 := hand2 (x 13 1) (x 13 14)
              have b46157 := hb (x 13 14)
              have b46158 := hb (x 13 1 && x 13 14)
              clear * - r46156 b46157 b46158 d46151
              omega
            have d46159 : (x 13 2).toNat = 0 := by
              have r46160 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
              have b46161 := hb (x 13 2)
              have b46162 := hb (x 13 14)
              clear * - r46160 b46161 b46162 d46151
              omega
            have d46163 : (x 12 2).toNat = 0 := by
              have r46164 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
              have e46165 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e46166 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b46167 := hb (x 11 3)
              have b46168 := hb (x 12 2)
              have b46169 := hb (x 13 13)
              have b46170 := hb (x 14 12)
              clear * - r46164 e46165 e46166 b46167 b46168 b46169 b46170 d46110 d46126 d46106
              omega
            have d46171 : (x 14 13).toNat = 1 := by
              have r46172 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
              have b46173 := hb (x 12 2)
              have b46174 := hb (x 14 13)
              have b46175 := hb (x 13 1 && x 13 14)
              clear * - r46172 b46173 b46174 b46175 d46155 d46163
              omega
            have d46176 : (x 15 12).toNat = 0 := by
              have r46177 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e46178 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e46179 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b46180 := hb (x 12 3)
              have b46181 := hb (x 13 2)
              have b46182 := hb (x 14 13)
              have b46183 := hb (x 15 12)
              clear * - r46177 e46178 e46179 b46180 b46181 b46182 b46183 d46171 d46159
              omega
            have d46184 : (x 12 3).toNat = 0 := by
              have r46185 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e46186 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e46187 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b46188 := hb (x 12 3)
              have b46189 := hb (x 13 2)
              have b46190 := hb (x 14 13)
              have b46191 := hb (x 15 12)
              clear * - r46185 e46186 e46187 b46188 b46189 b46190 b46191 d46176 d46171 d46159
              omega
            have d46192 : (x 12 3 && x 12 14).toNat = 0 := by
              have r46193 := hand1 (x 12 3) (x 12 14)
              have b46194 := hb (x 12 3)
              have b46195 := hb (x 12 3 && x 12 14)
              clear * - r46193 b46194 b46195 d46184
              omega
            have d46196 : (x 15 11).toNat = 1 := by
              have r46197 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
              have b46198 := hb (x 11 4)
              have b46199 := hb (x 15 11)
              have b46200 := hb (x 14 1 && x 14 12)
              have b46201 := hb (x 13 2 && x 13 13)
              have b46202 := hb (x 12 3 && x 12 14)
              clear * - r46197 b46198 b46199 b46200 b46201 b46202 d46118 d46134 d46192 d46083
              omega
            have d46203 : (x 15 3).toNat = 1 := by
              have r46204 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
              have b46205 := hb (x 15 3)
              have b46206 := hb (x 15 11)
              clear * - r46204 b46205 b46206 d46196
              omega
            have d46207 : (x 18 12).toNat = 0 := by
              have r46208 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
              have e46209 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
              have e46210 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
              have b46211 := hb (x 15 3)
              have b46212 := hb (x 16 2)
              have b46213 := hb (x 17 13)
              have b46214 := hb (x 18 12)
              clear * - r46208 e46209 e46210 b46211 b46212 b46213 b46214 d46203
              omega
            have d46215 : (x 17 13).toNat = 0 := by
              have r46216 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
              have e46217 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
              have e46218 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
              have b46219 := hb (x 15 3)
              have b46220 := hb (x 16 2)
              have b46221 := hb (x 17 13)
              have b46222 := hb (x 18 12)
              clear * - r46216 e46217 e46218 b46219 b46220 b46221 b46222 d46207 d46203
              omega
            have d46223 : (x 16 1 && x 16 14).toNat = 1 := by
              have r46224 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
              have b46225 := hb (x 15 2)
              have b46226 := hb (x 17 13)
              have b46227 := hb (x 16 1 && x 16 14)
              clear * - r46224 b46225 b46226 b46227 d46215 d46067
              omega
            have d46228 : (x 16 14).toNat = 1 := by
              have r46229 := hand2 (x 16 1) (x 16 14)
              have b46230 := hb (x 16 14)
              have b46231 := hb (x 16 1 && x 16 14)
              clear * - r46229 b46230 b46231 d46223
              omega
            have d46232 : (x 15 1).toNat = 0 := by
              have r46233 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
              have b46234 := hb (x 15 1)
              have b46235 := hb (x 16 14)
              clear * - r46233 b46234 b46235 d46228
              omega
            have d46236 : (x 15 1 && x 15 11).toNat = 0 := by
              have r46237 := hand1 (x 15 1) (x 15 11)
              have b46238 := hb (x 15 1)
              have b46239 := hb (x 15 1 && x 15 11)
              clear * - r46237 b46238 b46239 d46232
              omega
            have d46240 : (x 16 2).toNat = 0 := by
              have r46241 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
              have e46242 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
              have e46243 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
              have b46244 := hb (x 15 3)
              have b46245 := hb (x 16 2)
              have b46246 := hb (x 17 13)
              have b46247 := hb (x 18 12)
              clear * - r46241 e46242 e46243 b46244 b46245 b46246 b46247 d46207 d46215 d46203
              omega
            have d46248 : (x 16 10).toNat = 0 := by
              have r46249 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
              have b46250 := hb (x 16 2)
              have b46251 := hb (x 16 10)
              clear * - r46249 b46250 b46251 d46240
              omega
            have r46252 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := hcov10 16
            have b46253 := hb (x 11 5)
            have b46254 := hb (x 16 10)
            have b46255 := hb (x 15 1 && x 15 11)
            have b46256 := hb (x 14 2 && x 14 12)
            have b46257 := hb (x 13 3 && x 13 13)
            have b46258 := hb (x 12 4 && x 12 14)
            linarith only [r46252, b46253, b46254, b46255, b46256, b46257, b46258, d46248, d46236, d46122, d46138, d46020, d46032]
          · have f46259 : (x (-1) 4).toNat = 1 := by rw [h45692]; rfl
            have d46260 : (x 3 8).toNat = 0 := by
              have r46261 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
              have e46262 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
              have e46263 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
              have e46264 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
              have e46265 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
              have e46266 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
              have e46267 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
              have b46268 := hb (x (-4) 7)
              have b46269 := hb (x (-3) 6)
              have b46270 := hb (x (-2) 5)
              have b46271 := hb (x (-1) 4)
              have b46272 := hb (x 0 11)
              have b46273 := hb (x 1 10)
              have b46274 := hb (x 2 9)
              have b46275 := hb (x 3 8)
              clear * - r46261 e46262 e46263 e46264 e46265 e46266 e46267 b46268 b46269 b46270 b46271 b46272 b46273 b46274 b46275 g12 g9 f46259 d45541
              omega
            have d46276 : (x 2 9).toNat = 0 := by
              have r46277 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
              have e46278 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
              have e46279 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
              have e46280 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
              have e46281 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
              have e46282 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
              have e46283 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
              have b46284 := hb (x (-4) 7)
              have b46285 := hb (x (-3) 6)
              have b46286 := hb (x (-2) 5)
              have b46287 := hb (x (-1) 4)
              have b46288 := hb (x 0 11)
              have b46289 := hb (x 1 10)
              have b46290 := hb (x 2 9)
              have b46291 := hb (x 3 8)
              clear * - r46277 e46278 e46279 e46280 e46281 e46282 e46283 b46284 b46285 b46286 b46287 b46288 b46289 b46290 b46291 d46260 g12 g9 f46259 d45541
              omega
            have d46292 : (x (-3) 6).toNat = 0 := by
              have r46293 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
              have e46294 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
              have e46295 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
              have e46296 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
              have e46297 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
              have e46298 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
              have e46299 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
              have b46300 := hb (x (-4) 7)
              have b46301 := hb (x (-3) 6)
              have b46302 := hb (x (-2) 5)
              have b46303 := hb (x (-1) 4)
              have b46304 := hb (x 0 11)
              have b46305 := hb (x 1 10)
              have b46306 := hb (x 2 9)
              have b46307 := hb (x 3 8)
              clear * - r46293 e46294 e46295 e46296 e46297 e46298 e46299 b46300 b46301 b46302 b46303 b46304 b46305 b46306 b46307 d46260 d46276 g12 g9 f46259 d45541
              omega
            have d46308 : (x (-4) 7).toNat = 0 := by
              have r46309 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
              have e46310 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
              have e46311 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
              have e46312 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
              have e46313 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
              have e46314 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
              have e46315 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
              have b46316 := hb (x (-4) 7)
              have b46317 := hb (x (-3) 6)
              have b46318 := hb (x (-2) 5)
              have b46319 := hb (x (-1) 4)
              have b46320 := hb (x 0 11)
              have b46321 := hb (x 1 10)
              have b46322 := hb (x 2 9)
              have b46323 := hb (x 3 8)
              clear * - r46309 e46310 e46311 e46312 e46313 e46314 e46315 b46316 b46317 b46318 b46319 b46320 b46321 b46322 b46323 d46260 d46276 g12 g9 f46259 d45541 d46292
              omega
            have r46324 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := hcount 3
            have r46325 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
            have e46326 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
            have e46327 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
            have e46328 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
            have e46329 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
            have e46330 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
            have e46331 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
            have r46332 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
            have e46333 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e46334 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e46335 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e46336 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e46337 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e46338 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have r46339 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
            have e46340 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e46341 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e46342 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e46343 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e46344 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e46345 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have r46346 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
            have e46347 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e46348 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have r46349 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := hcov4 3
            have e46350 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
            have e46351 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
            have r46352 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := hcov7 0
            have r46353 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
            have r46354 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
            have r46355 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := hcov11 (-8)
            have r46356 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
            have r46357 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
            have r46358 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
            have r46359 := hand2 (x (-1) 4) (x (-1) 8)
            have r46360 := hand1 (x (-5) 8) (x (-5) 12)
            have r46361 := hand1 (x (-6) 9) (x (-6) 13)
            have r46362 := hand2 (x (-1) 1) (x (-1) 8)
            have r46363 := hand2 (x 5 1) (x 5 10)
            have r46364 := hand2 (x 4 2) (x 4 11)
            have r46365 := hand1 (x (-5) 4) (x (-5) 14)
            have r46366 := hand2 (x (-9) 1) (x (-9) 12)
            have r46367 := hand2 (x (-10) 2) (x (-10) 13)
            have r46368 := hand2 (x (-11) 3) (x (-11) 14)
            have b46369 := hb (x (-15) 7)
            have b46370 := hb (x (-14) 6)
            have b46371 := hb (x (-13) 5)
            have b46372 := hb (x (-12) 4)
            have b46373 := hb (x (-11) 11)
            have b46374 := hb (x (-11) 14)
            have b46375 := hb (x (-10) 10)
            have b46376 := hb (x (-10) 13)
            have b46377 := hb (x (-9) 9)
            have b46378 := hb (x (-9) 12)
            have b46379 := hb (x (-8) 3)
            have b46380 := hb (x (-8) 7)
            have b46381 := hb (x (-8) 8)
            have b46382 := hb (x (-8) 11)
            have b46383 := hb (x (-7) 2)
            have b46384 := hb (x (-7) 6)
            have b46385 := hb (x (-7) 10)
            have b46386 := hb (x (-6) 5)
            have b46387 := hb (x (-6) 9)
            have b46388 := hb (x (-6) 13)
            have b46389 := hb (x (-5) 4)
            have b46390 := hb (x (-5) 8)
            have b46391 := hb (x (-5) 12)
            have b46392 := hb (x (-4) 7)
            have b46393 := hb (x (-4) 11)
            have b46394 := hb (x (-3) 6)
            have b46395 := hb (x (-3) 10)
            have b46396 := hb (x (-2) 5)
            have b46397 := hb (x (-2) 9)
            have b46398 := hb (x (-1) 4)
            have b46399 := hb (x (-1) 8)
            have b46400 := hb (x (-1) 10)
            have b46401 := hb (x 0 3)
            have b46402 := hb (x 0 6)
            have b46403 := hb (x 0 7)
            have b46404 := hb (x 1 2)
            have b46405 := hb (x 1 6)
            have b46406 := hb (x 2 1)
            have b46407 := hb (x 2 5)
            have b46408 := hb (x 3 4)
            have b46409 := hb (x 4 11)
            have b46410 := hb (x 5 10)
            have b46411 := hb (x 6 9)
            have b46412 := hb (x 7 8)
            have b46413 := hb (x 1 2 && x 1 6)
            have b46414 := hb (x 0 3 && x 0 7)
            have b46415 := hb (x (-1) 4 && x (-1) 8)
            have b46416 := hb (x (-2) 5 && x (-2) 9)
            have b46417 := hb (x (-3) 6 && x (-3) 10)
            have b46418 := hb (x (-4) 7 && x (-4) 11)
            have b46419 := hb (x (-5) 8 && x (-5) 12)
            have b46420 := hb (x (-6) 9 && x (-6) 13)
            have b46421 := hb (x (-1) 1 && x (-1) 8)
            have b46422 := hb (x (-2) 2 && x (-2) 9)
            have b46423 := hb (x (-3) 3 && x (-3) 10)
            have b46424 := hb (x (-4) 4 && x (-4) 11)
            have b46425 := hb (x (-5) 5 && x (-5) 12)
            have b46426 := hb (x (-6) 6 && x (-6) 13)
            have b46427 := hb (x (-7) 7 && x (-7) 14)
            have b46428 := hb (x 5 1 && x 5 10)
            have b46429 := hb (x 4 2 && x 4 11)
            have b46430 := hb (x 3 3 && x 3 12)
            have b46431 := hb (x 2 4 && x 2 13)
            have b46432 := hb (x 1 5 && x 1 14)
            have b46433 := hb (x (-2) 1 && x (-2) 11)
            have b46434 := hb (x (-3) 2 && x (-3) 12)
            have b46435 := hb (x (-4) 3 && x (-4) 13)
            have b46436 := hb (x (-5) 4 && x (-5) 14)
            have b46437 := hb (x (-9) 1 && x (-9) 12)
            have b46438 := hb (x (-10) 2 && x (-10) 13)
            have b46439 := hb (x (-11) 3 && x (-11) 14)
            linarith only [r46324, r46325, e46326, e46327, e46328, e46329, e46330, e46331, r46332, e46333, e46334, e46335, e46336, e46337, e46338, r46339, e46340, e46341, e46342, e46343, e46344, e46345, r46346, e46347, e46348, r46349, e46350, e46351, r46352, r46353, r46354, r46355, r46356, r46357, r46358, r46359, r46360, r46361, r46362, r46363, r46364, r46365, r46366, r46367, r46368, b46369, b46370, b46371, b46372, b46373, b46374, b46375, b46376, b46377, b46378, b46379, b46380, b46381, b46382, b46383, b46384, b46385, b46386, b46387, b46388, b46389, b46390, b46391, b46392, b46393, b46394, b46395, b46396, b46397, b46398, b46399, b46400, b46401, b46402, b46403, b46404, b46405, b46406, b46407, b46408, b46409, b46410, b46411, b46412, b46413, b46414, b46415, b46416, b46417, b46418, b46419, b46420, b46421, b46422, b46423, b46424, b46425, b46426, b46427, b46428, b46429, b46430, b46431, b46432, b46433, b46434, b46435, b46436, b46437, b46438, b46439, d46308, d45646, d46292, d45593, d45541, d45549, f46259, d45434, g3, g5, g6, g10, g11, g13, g15, g16, g17, d45545, d45601, d45650, d45553, d45597, g18, g19, g20, g21, g22, d45686, g23, d45466, d45589, d45642]
        · have f46440 : (x 1 3).toNat = 1 := by rw [h45690]; rfl
          have d46441 : (x 4 12).toNat = 0 := by
            have r46442 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e46443 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e46444 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b46445 := hb (x 1 3)
            have b46446 := hb (x 2 2)
            have b46447 := hb (x 3 13)
            have b46448 := hb (x 4 12)
            clear * - r46442 e46443 e46444 b46445 b46446 b46447 b46448 f46440
            omega
          have d46449 : (x 4 1 && x 4 12).toNat = 0 := by
            have r46450 := hand2 (x 4 1) (x 4 12)
            have b46451 := hb (x 4 12)
            have b46452 := hb (x 4 1 && x 4 12)
            clear * - r46450 b46451 b46452 d46441
            omega
          have d46453 : (x 4 4).toNat = 0 := by
            have r46454 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b46455 := hb (x 4 4)
            have b46456 := hb (x 4 12)
            clear * - r46454 b46455 b46456 d46441
            omega
          have d46457 : (x 3 13).toNat = 0 := by
            have r46458 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e46459 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e46460 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b46461 := hb (x 1 3)
            have b46462 := hb (x 2 2)
            have b46463 := hb (x 3 13)
            have b46464 := hb (x 4 12)
            clear * - r46458 e46459 e46460 b46461 b46462 b46463 b46464 d46441 f46440
            omega
          have d46465 : (x 2 2).toNat = 0 := by
            have r46466 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e46467 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e46468 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b46469 := hb (x 1 3)
            have b46470 := hb (x 2 2)
            have b46471 := hb (x 3 13)
            have b46472 := hb (x 4 12)
            clear * - r46466 e46467 e46468 b46469 b46470 b46471 b46472 d46441 d46457 f46440
            omega
          have d46473 : (x 4 13).toNat = 1 := by
            have r46474 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
            have b46475 := hb (x 2 2)
            have b46476 := hb (x 4 13)
            have b46477 := hb (x 3 1 && x 3 14)
            clear * - r46474 b46475 b46476 b46477 g33 d46465
            omega
          have d46478 : (x 4 1).toNat = 1 := by
            have r46479 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
            have b46480 := hb (x 4 1)
            have b46481 := hb (x 4 13)
            clear * - r46479 b46480 b46481 d46473
            omega
          have d46482 : (x 5 14).toNat = 0 := by
            have r46483 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
            have b46484 := hb (x 4 1)
            have b46485 := hb (x 5 14)
            clear * - r46483 b46484 b46485 d46478
            omega
          have d46486 : (x 5 3 && x 5 14).toNat = 0 := by
            have r46487 := hand2 (x 5 3) (x 5 14)
            have b46488 := hb (x 5 14)
            have b46489 := hb (x 5 3 && x 5 14)
            clear * - r46487 b46488 b46489 d46482
            omega
          have d46490 : (x 5 2).toNat = 0 := by
            have r46491 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b46492 := hb (x 5 2)
            have b46493 := hb (x 5 14)
            clear * - r46491 b46492 b46493 d46482
            omega
          have d46494 : (x 5 12).toNat = 0 := by
            have r46495 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e46496 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e46497 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b46498 := hb (x 2 3)
            have b46499 := hb (x 3 2)
            have b46500 := hb (x 4 13)
            have b46501 := hb (x 5 12)
            clear * - r46495 e46496 e46497 b46498 b46499 b46500 b46501 d46473 g14
            omega
          have d46502 : (x 5 4).toNat = 0 := by
            have r46503 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b46504 := hb (x 5 4)
            have b46505 := hb (x 5 12)
            clear * - r46503 b46504 b46505 d46494
            omega
          have d46506 : (x 2 3).toNat = 0 := by
            have r46507 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e46508 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e46509 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b46510 := hb (x 2 3)
            have b46511 := hb (x 3 2)
            have b46512 := hb (x 4 13)
            have b46513 := hb (x 5 12)
            clear * - r46507 e46508 e46509 b46510 b46511 b46512 b46513 d46494 d46473 g14
            omega
          have d46514 : (x 2 3 && x 2 14).toNat = 0 := by
            have r46515 := hand1 (x 2 3) (x 2 14)
            have b46516 := hb (x 2 3)
            have b46517 := hb (x 2 3 && x 2 14)
            clear * - r46515 b46516 b46517 d46506
            omega
          have d46518 : (x 5 11).toNat = 1 := by
            have r46519 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
            have b46520 := hb (x 1 4)
            have b46521 := hb (x 5 11)
            have b46522 := hb (x 4 1 && x 4 12)
            have b46523 := hb (x 3 2 && x 3 13)
            have b46524 := hb (x 2 3 && x 2 14)
            clear * - r46519 b46520 b46521 b46522 b46523 b46524 d46449 g30 d46514 d45565
            omega
          have d46525 : (x 5 3).toNat = 1 := by
            have r46526 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
            have b46527 := hb (x 5 3)
            have b46528 := hb (x 5 11)
            clear * - r46526 b46527 b46528 d46518
            omega
          have d46529 : (x 8 12).toNat = 0 := by
            have r46530 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
            have e46531 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e46532 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b46533 := hb (x 5 3)
            have b46534 := hb (x 6 2)
            have b46535 := hb (x 7 13)
            have b46536 := hb (x 8 12)
            clear * - r46530 e46531 e46532 b46533 b46534 b46535 b46536 d46525
            omega
          have d46537 : (x 8 1 && x 8 12).toNat = 0 := by
            have r46538 := hand2 (x 8 1) (x 8 12)
            have b46539 := hb (x 8 12)
            have b46540 := hb (x 8 1 && x 8 12)
            clear * - r46538 b46539 b46540 d46529
            omega
          have d46541 : (x 8 4).toNat = 0 := by
            have r46542 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
            have b46543 := hb (x 8 4)
            have b46544 := hb (x 8 12)
            clear * - r46542 b46543 b46544 d46529
            omega
          have d46545 : (x 7 13).toNat = 0 := by
            have r46546 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
            have e46547 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e46548 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b46549 := hb (x 5 3)
            have b46550 := hb (x 6 2)
            have b46551 := hb (x 7 13)
            have b46552 := hb (x 8 12)
            clear * - r46546 e46547 e46548 b46549 b46550 b46551 b46552 d46529 d46525
            omega
          have d46553 : (x 7 2 && x 7 13).toNat = 0 := by
            have r46554 := hand2 (x 7 2) (x 7 13)
            have b46555 := hb (x 7 13)
            have b46556 := hb (x 7 2 && x 7 13)
            clear * - r46554 b46555 b46556 d46545
            omega
          have d46557 : (x 6 1 && x 6 14).toNat = 1 := by
            have r46558 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
            have b46559 := hb (x 5 2)
            have b46560 := hb (x 7 13)
            have b46561 := hb (x 6 1 && x 6 14)
            clear * - r46558 b46559 b46560 b46561 d46545 d46490
            omega
          have d46562 : (x 6 1).toNat = 1 := by
            have r46563 := hand1 (x 6 1) (x 6 14)
            have b46564 := hb (x 6 1)
            have b46565 := hb (x 6 1 && x 6 14)
            clear * - r46563 b46564 b46565 d46557
            omega
          have d46566 : (x 7 14).toNat = 0 := by
            have r46567 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
            have b46568 := hb (x 6 1)
            have b46569 := hb (x 7 14)
            clear * - r46567 b46568 b46569 d46562
            omega
          have d46570 : (x 7 1 && x 7 14).toNat = 0 := by
            have r46571 := hand2 (x 7 1) (x 7 14)
            have b46572 := hb (x 7 14)
            have b46573 := hb (x 7 1 && x 7 14)
            clear * - r46571 b46572 b46573 d46566
            omega
          have d46574 : (x 7 2).toNat = 0 := by
            have r46575 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b46576 := hb (x 7 2)
            have b46577 := hb (x 7 14)
            clear * - r46575 b46576 b46577 d46566
            omega
          have d46578 : (x 6 2).toNat = 0 := by
            have r46579 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
            have e46580 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e46581 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b46582 := hb (x 5 3)
            have b46583 := hb (x 6 2)
            have b46584 := hb (x 7 13)
            have b46585 := hb (x 8 12)
            clear * - r46579 e46580 e46581 b46582 b46583 b46584 b46585 d46529 d46545 d46525
            omega
          have d46586 : (x 6 2 && x 6 13).toNat = 0 := by
            have r46587 := hand1 (x 6 2) (x 6 13)
            have b46588 := hb (x 6 2)
            have b46589 := hb (x 6 2 && x 6 13)
            clear * - r46587 b46588 b46589 d46578
            omega
          have d46590 : (x 8 13).toNat = 1 := by
            have r46591 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
            have b46592 := hb (x 6 2)
            have b46593 := hb (x 8 13)
            have b46594 := hb (x 7 1 && x 7 14)
            clear * - r46591 b46592 b46593 b46594 d46570 d46578
            omega
          have d46595 : (x 8 1).toNat = 1 := by
            have r46596 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
            have b46597 := hb (x 8 1)
            have b46598 := hb (x 8 13)
            clear * - r46596 b46597 b46598 d46590
            omega
          have d46599 : (x 9 14).toNat = 0 := by
            have r46600 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
            have b46601 := hb (x 8 1)
            have b46602 := hb (x 9 14)
            clear * - r46600 b46601 b46602 d46595
            omega
          have d46603 : (x 9 3 && x 9 14).toNat = 0 := by
            have r46604 := hand2 (x 9 3) (x 9 14)
            have b46605 := hb (x 9 14)
            have b46606 := hb (x 9 3 && x 9 14)
            clear * - r46604 b46605 b46606 d46599
            omega
          have d46607 : (x 9 2).toNat = 0 := by
            have r46608 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
            have b46609 := hb (x 9 2)
            have b46610 := hb (x 9 14)
            clear * - r46608 b46609 b46610 d46599
            omega
          have d46611 : (x 9 12).toNat = 0 := by
            have r46612 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
            have e46613 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e46614 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b46615 := hb (x 6 3)
            have b46616 := hb (x 7 2)
            have b46617 := hb (x 8 13)
            have b46618 := hb (x 9 12)
            clear * - r46612 e46613 e46614 b46615 b46616 b46617 b46618 d46590 d46574
            omega
          have d46619 : (x 9 4).toNat = 0 := by
            have r46620 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
            have b46621 := hb (x 9 4)
            have b46622 := hb (x 9 12)
            clear * - r46620 b46621 b46622 d46611
            omega
          have d46623 : (x 6 3).toNat = 0 := by
            have r46624 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
            have e46625 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e46626 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b46627 := hb (x 6 3)
            have b46628 := hb (x 7 2)
            have b46629 := hb (x 8 13)
            have b46630 := hb (x 9 12)
            clear * - r46624 e46625 e46626 b46627 b46628 b46629 b46630 d46611 d46590 d46574
            omega
          have d46631 : (x 6 3 && x 6 14).toNat = 0 := by
            have r46632 := hand1 (x 6 3) (x 6 14)
            have b46633 := hb (x 6 3)
            have b46634 := hb (x 6 3 && x 6 14)
            clear * - r46632 b46633 b46634 d46623
            omega
          have d46635 : (x 9 11).toNat = 1 := by
            have r46636 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := hcov11 9
            have b46637 := hb (x 5 4)
            have b46638 := hb (x 9 11)
            have b46639 := hb (x 8 1 && x 8 12)
            have b46640 := hb (x 7 2 && x 7 13)
            have b46641 := hb (x 6 3 && x 6 14)
            clear * - r46636 b46637 b46638 b46639 b46640 b46641 d46537 d46553 d46631 d46502
            omega
          have d46642 : (x 9 3).toNat = 1 := by
            have r46643 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
            have b46644 := hb (x 9 3)
            have b46645 := hb (x 9 11)
            clear * - r46643 b46644 b46645 d46635
            omega
          have d46646 : (x 12 12).toNat = 0 := by
            have r46647 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
            have e46648 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e46649 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b46650 := hb (x 9 3)
            have b46651 := hb (x 10 2)
            have b46652 := hb (x 11 13)
            have b46653 := hb (x 12 12)
            clear * - r46647 e46648 e46649 b46650 b46651 b46652 b46653 d46642
            omega
          have d46654 : (x 12 1 && x 12 12).toNat = 0 := by
            have r46655 := hand2 (x 12 1) (x 12 12)
            have b46656 := hb (x 12 12)
            have b46657 := hb (x 12 1 && x 12 12)
            clear * - r46655 b46656 b46657 d46646
            omega
          have d46658 : (x 12 4).toNat = 0 := by
            have r46659 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
            have b46660 := hb (x 12 4)
            have b46661 := hb (x 12 12)
            clear * - r46659 b46660 b46661 d46646
            omega
          have d46662 : (x 11 13).toNat = 0 := by
            have r46663 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
            have e46664 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e46665 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b46666 := hb (x 9 3)
            have b46667 := hb (x 10 2)
            have b46668 := hb (x 11 13)
            have b46669 := hb (x 12 12)
            clear * - r46663 e46664 e46665 b46666 b46667 b46668 b46669 d46646 d46642
            omega
          have d46670 : (x 11 2 && x 11 13).toNat = 0 := by
            have r46671 := hand2 (x 11 2) (x 11 13)
            have b46672 := hb (x 11 13)
            have b46673 := hb (x 11 2 && x 11 13)
            clear * - r46671 b46672 b46673 d46662
            omega
          have d46674 : (x 10 1 && x 10 14).toNat = 1 := by
            have r46675 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
            have b46676 := hb (x 9 2)
            have b46677 := hb (x 11 13)
            have b46678 := hb (x 10 1 && x 10 14)
            clear * - r46675 b46676 b46677 b46678 d46662 d46607
            omega
          have d46679 : (x 10 14).toNat = 1 := by
            have r46680 := hand2 (x 10 1) (x 10 14)
            have b46681 := hb (x 10 14)
            have b46682 := hb (x 10 1 && x 10 14)
            clear * - r46680 b46681 b46682 d46674
            omega
          have d46683 : (x 9 1).toNat = 0 := by
            have r46684 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
            have b46685 := hb (x 9 1)
            have b46686 := hb (x 10 14)
            clear * - r46684 b46685 b46686 d46679
            omega
          have d46687 : (x 9 13).toNat = 0 := by
            have r46688 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
            have b46689 := hb (x 9 1)
            have b46690 := hb (x 9 13)
            clear * - r46688 b46689 b46690 d46683
            omega
          have d46691 : (x 8 1 && x 8 14).toNat = 1 := by
            have r46692 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
            have b46693 := hb (x 7 2)
            have b46694 := hb (x 9 13)
            have b46695 := hb (x 8 1 && x 8 14)
            clear * - r46692 b46693 b46694 b46695 d46687 d46574
            omega
          have d46696 : (x 8 14).toNat = 1 := by
            have r46697 := hand2 (x 8 1) (x 8 14)
            have b46698 := hb (x 8 14)
            have b46699 := hb (x 8 1 && x 8 14)
            clear * - r46697 b46698 b46699 d46691
            omega
          have d46700 : (x 7 1).toNat = 0 := by
            have r46701 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
            have b46702 := hb (x 7 1)
            have b46703 := hb (x 8 14)
            clear * - r46701 b46702 b46703 d46696
            omega
          have d46704 : (x 7 1 && x 7 12).toNat = 0 := by
            have r46705 := hand1 (x 7 1) (x 7 12)
            have b46706 := hb (x 7 1)
            have b46707 := hb (x 7 1 && x 7 12)
            clear * - r46705 b46706 b46707 d46700
            omega
          have d46708 : (x 8 11).toNat = 1 := by
            have r46709 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
            have b46710 := hb (x 4 4)
            have b46711 := hb (x 8 11)
            have b46712 := hb (x 7 1 && x 7 12)
            have b46713 := hb (x 6 2 && x 6 13)
            have b46714 := hb (x 5 3 && x 5 14)
            clear * - r46709 b46710 b46711 b46712 b46713 b46714 d46704 d46586 d46486 d46453
            omega
          have d46715 : (x 8 3).toNat = 1 := by
            have r46716 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
            have b46717 := hb (x 8 3)
            have b46718 := hb (x 8 11)
            clear * - r46716 b46717 b46718 d46708
            omega
          have d46719 : (x 11 12).toNat = 0 := by
            have r46720 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
            have e46721 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e46722 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b46723 := hb (x 8 3)
            have b46724 := hb (x 9 2)
            have b46725 := hb (x 10 13)
            have b46726 := hb (x 11 12)
            clear * - r46720 e46721 e46722 b46723 b46724 b46725 b46726 d46607 d46715
            omega
          have d46727 : (x 11 1 && x 11 12).toNat = 0 := by
            have r46728 := hand2 (x 11 1) (x 11 12)
            have b46729 := hb (x 11 12)
            have b46730 := hb (x 11 1 && x 11 12)
            clear * - r46728 b46729 b46730 d46719
            omega
          have d46731 : (x 10 13).toNat = 0 := by
            have r46732 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
            have e46733 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e46734 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b46735 := hb (x 8 3)
            have b46736 := hb (x 9 2)
            have b46737 := hb (x 10 13)
            have b46738 := hb (x 11 12)
            clear * - r46732 e46733 e46734 b46735 b46736 b46737 b46738 d46719 d46607 d46715
            omega
          have d46739 : (x 10 2 && x 10 13).toNat = 0 := by
            have r46740 := hand2 (x 10 2) (x 10 13)
            have b46741 := hb (x 10 13)
            have b46742 := hb (x 10 2 && x 10 13)
            clear * - r46740 b46741 b46742 d46731
            omega
          have d46743 : (x 12 11).toNat = 1 := by
            have r46744 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
            have b46745 := hb (x 8 4)
            have b46746 := hb (x 12 11)
            have b46747 := hb (x 11 1 && x 11 12)
            have b46748 := hb (x 10 2 && x 10 13)
            have b46749 := hb (x 9 3 && x 9 14)
            clear * - r46744 b46745 b46746 b46747 b46748 b46749 d46727 d46739 d46603 d46541
            omega
          have d46750 : (x 12 3).toNat = 1 := by
            have r46751 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
            have b46752 := hb (x 12 3)
            have b46753 := hb (x 12 11)
            clear * - r46751 b46752 b46753 d46743
            omega
          have d46754 : (x 15 12).toNat = 0 := by
            have r46755 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
            have e46756 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e46757 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b46758 := hb (x 12 3)
            have b46759 := hb (x 13 2)
            have b46760 := hb (x 14 13)
            have b46761 := hb (x 15 12)
            clear * - r46755 e46756 e46757 b46758 b46759 b46760 b46761 d46750
            omega
          have d46762 : (x 15 1 && x 15 12).toNat = 0 := by
            have r46763 := hand2 (x 15 1) (x 15 12)
            have b46764 := hb (x 15 12)
            have b46765 := hb (x 15 1 && x 15 12)
            clear * - r46763 b46764 b46765 d46754
            omega
          have d46766 : (x 14 13).toNat = 0 := by
            have r46767 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
            have e46768 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e46769 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b46770 := hb (x 12 3)
            have b46771 := hb (x 13 2)
            have b46772 := hb (x 14 13)
            have b46773 := hb (x 15 12)
            clear * - r46767 e46768 e46769 b46770 b46771 b46772 b46773 d46754 d46750
            omega
          have d46774 : (x 14 2 && x 14 13).toNat = 0 := by
            have r46775 := hand2 (x 14 2) (x 14 13)
            have b46776 := hb (x 14 13)
            have b46777 := hb (x 14 2 && x 14 13)
            clear * - r46775 b46776 b46777 d46766
            omega
          have d46778 : (x 13 2).toNat = 0 := by
            have r46779 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
            have e46780 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e46781 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b46782 := hb (x 12 3)
            have b46783 := hb (x 13 2)
            have b46784 := hb (x 14 13)
            have b46785 := hb (x 15 12)
            clear * - r46779 e46780 e46781 b46782 b46783 b46784 b46785 d46754 d46766 d46750
            omega
          have d46786 : (x 10 1).toNat = 1 := by
            have r46787 := hand1 (x 10 1) (x 10 14)
            have b46788 := hb (x 10 1)
            have b46789 := hb (x 10 1 && x 10 14)
            clear * - r46787 b46788 b46789 d46674
            omega
          have d46790 : (x 11 14).toNat = 0 := by
            have r46791 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
            have b46792 := hb (x 10 1)
            have b46793 := hb (x 11 14)
            clear * - r46791 b46792 b46793 d46786
            omega
          have d46794 : (x 11 1 && x 11 14).toNat = 0 := by
            have r46795 := hand2 (x 11 1) (x 11 14)
            have b46796 := hb (x 11 14)
            have b46797 := hb (x 11 1 && x 11 14)
            clear * - r46795 b46796 b46797 d46790
            omega
          have d46798 : (x 11 2).toNat = 0 := by
            have r46799 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
            have b46800 := hb (x 11 2)
            have b46801 := hb (x 11 14)
            clear * - r46799 b46800 b46801 d46790
            omega
          have d46802 : (x 10 2).toNat = 0 := by
            have r46803 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
            have e46804 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e46805 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b46806 := hb (x 9 3)
            have b46807 := hb (x 10 2)
            have b46808 := hb (x 11 13)
            have b46809 := hb (x 12 12)
            clear * - r46803 e46804 e46805 b46806 b46807 b46808 b46809 d46646 d46662 d46642
            omega
          have d46810 : (x 12 13).toNat = 1 := by
            have r46811 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
            have b46812 := hb (x 10 2)
            have b46813 := hb (x 12 13)
            have b46814 := hb (x 11 1 && x 11 14)
            clear * - r46811 b46812 b46813 b46814 d46794 d46802
            omega
          have d46815 : (x 12 1).toNat = 1 := by
            have r46816 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
            have b46817 := hb (x 12 1)
            have b46818 := hb (x 12 13)
            clear * - r46816 b46817 b46818 d46810
            omega
          have d46819 : (x 13 14).toNat = 0 := by
            have r46820 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
            have b46821 := hb (x 12 1)
            have b46822 := hb (x 13 14)
            clear * - r46820 b46821 b46822 d46815
            omega
          have d46823 : (x 13 1 && x 13 14).toNat = 0 := by
            have r46824 := hand2 (x 13 1) (x 13 14)
            have b46825 := hb (x 13 14)
            have b46826 := hb (x 13 1 && x 13 14)
            clear * - r46824 b46825 b46826 d46819
            omega
          have d46827 : (x 12 2).toNat = 1 := by
            have r46828 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
            have b46829 := hb (x 12 2)
            have b46830 := hb (x 14 13)
            have b46831 := hb (x 13 1 && x 13 14)
            clear * - r46828 b46829 b46830 b46831 d46766 d46823
            omega
          have d46832 : (x 14 12).toNat = 0 := by
            have r46833 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
            have e46834 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e46835 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b46836 := hb (x 11 3)
            have b46837 := hb (x 12 2)
            have b46838 := hb (x 13 13)
            have b46839 := hb (x 14 12)
            clear * - r46833 e46834 e46835 b46836 b46837 b46838 b46839 d46827
            omega
          have d46840 : (x 14 4).toNat = 0 := by
            have r46841 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
            have b46842 := hb (x 14 4)
            have b46843 := hb (x 14 12)
            clear * - r46841 b46842 b46843 d46832
            omega
          have d46844 : (x 14 4 && x 14 14).toNat = 0 := by
            have r46845 := hand1 (x 14 4) (x 14 14)
            have b46846 := hb (x 14 4)
            have b46847 := hb (x 14 4 && x 14 14)
            clear * - r46845 b46846 b46847 d46840
            omega
          have d46848 : (x 13 13).toNat = 0 := by
            have r46849 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
            have e46850 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
            have e46851 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
            have b46852 := hb (x 11 3)
            have b46853 := hb (x 12 2)
            have b46854 := hb (x 13 13)
            have b46855 := hb (x 14 12)
            clear * - r46849 e46850 e46851 b46852 b46853 b46854 b46855 d46832 d46827
            omega
          have d46856 : (x 13 5).toNat = 0 := by
            have r46857 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
            have b46858 := hb (x 13 5)
            have b46859 := hb (x 13 13)
            clear * - r46857 b46858 b46859 d46848
            omega
          have d46860 : (x 13 3 && x 13 14).toNat = 0 := by
            have r46861 := hand2 (x 13 3) (x 13 14)
            have b46862 := hb (x 13 14)
            have b46863 := hb (x 13 3 && x 13 14)
            clear * - r46861 b46862 b46863 d46819
            omega
          have d46864 : (x 16 11).toNat = 1 := by
            have r46865 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := hcov11 16
            have b46866 := hb (x 12 4)
            have b46867 := hb (x 16 11)
            have b46868 := hb (x 15 1 && x 15 12)
            have b46869 := hb (x 14 2 && x 14 13)
            have b46870 := hb (x 13 3 && x 13 14)
            clear * - r46865 b46866 b46867 b46868 b46869 b46870 d46762 d46774 d46860 d46658
            omega
          have d46871 : (x 16 3).toNat = 1 := by
            have r46872 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
            have b46873 := hb (x 16 3)
            have b46874 := hb (x 16 11)
            clear * - r46872 b46873 b46874 d46864
            omega
          have d46875 : (x 19 12).toNat = 0 := by
            have r46876 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
            have e46877 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e46878 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b46879 := hb (x 16 3)
            have b46880 := hb (x 17 2)
            have b46881 := hb (x 18 13)
            have b46882 := hb (x 19 12)
            clear * - r46876 e46877 e46878 b46879 b46880 b46881 b46882 d46871
            omega
          have d46883 : (x 18 13).toNat = 0 := by
            have r46884 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
            have e46885 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e46886 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b46887 := hb (x 16 3)
            have b46888 := hb (x 17 2)
            have b46889 := hb (x 18 13)
            have b46890 := hb (x 19 12)
            clear * - r46884 e46885 e46886 b46887 b46888 b46889 b46890 d46875 d46871
            omega
          have d46891 : (x 17 2).toNat = 0 := by
            have r46892 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
            have e46893 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
            have e46894 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
            have b46895 := hb (x 16 3)
            have b46896 := hb (x 17 2)
            have b46897 := hb (x 18 13)
            have b46898 := hb (x 19 12)
            clear * - r46892 e46893 e46894 b46895 b46896 b46897 b46898 d46875 d46883 d46871
            omega
          have d46899 : (x 13 12).toNat = 0 := by
            have r46900 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
            have e46901 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e46902 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b46903 := hb (x 10 3)
            have b46904 := hb (x 11 2)
            have b46905 := hb (x 12 13)
            have b46906 := hb (x 13 12)
            clear * - r46900 e46901 e46902 b46903 b46904 b46905 b46906 d46810 d46798
            omega
          have d46907 : (x 13 4).toNat = 0 := by
            have r46908 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
            have b46909 := hb (x 13 4)
            have b46910 := hb (x 13 12)
            clear * - r46908 b46909 b46910 d46899
            omega
          have d46911 : (x 10 3).toNat = 0 := by
            have r46912 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
            have e46913 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e46914 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b46915 := hb (x 10 3)
            have b46916 := hb (x 11 2)
            have b46917 := hb (x 12 13)
            have b46918 := hb (x 13 12)
            clear * - r46912 e46913 e46914 b46915 b46916 b46917 b46918 d46899 d46810 d46798
            omega
          have d46919 : (x 10 3 && x 10 14).toNat = 0 := by
            have r46920 := hand1 (x 10 3) (x 10 14)
            have b46921 := hb (x 10 3)
            have b46922 := hb (x 10 3 && x 10 14)
            clear * - r46920 b46921 b46922 d46911
            omega
          have d46923 : (x 13 11).toNat = 1 := by
            have r46924 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := hcov11 13
            have b46925 := hb (x 9 4)
            have b46926 := hb (x 13 11)
            have b46927 := hb (x 12 1 && x 12 12)
            have b46928 := hb (x 11 2 && x 11 13)
            have b46929 := hb (x 10 3 && x 10 14)
            clear * - r46924 b46925 b46926 b46927 b46928 b46929 d46654 d46670 d46919 d46619
            omega
          have d46930 : (x 13 3).toNat = 1 := by
            have r46931 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
            have b46932 := hb (x 13 3)
            have b46933 := hb (x 13 11)
            clear * - r46931 b46932 b46933 d46923
            omega
          have d46934 : (x 16 12).toNat = 0 := by
            have r46935 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
            have e46936 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e46937 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b46938 := hb (x 13 3)
            have b46939 := hb (x 14 2)
            have b46940 := hb (x 15 13)
            have b46941 := hb (x 16 12)
            clear * - r46935 e46936 e46937 b46938 b46939 b46940 b46941 d46930
            omega
          have d46942 : (x 16 1 && x 16 12).toNat = 0 := by
            have r46943 := hand2 (x 16 1) (x 16 12)
            have b46944 := hb (x 16 12)
            have b46945 := hb (x 16 1 && x 16 12)
            clear * - r46943 b46944 b46945 d46934
            omega
          have d46946 : (x 16 2 && x 16 12).toNat = 0 := by
            have r46947 := hand2 (x 16 2) (x 16 12)
            have b46948 := hb (x 16 12)
            have b46949 := hb (x 16 2 && x 16 12)
            clear * - r46947 b46948 b46949 d46934
            omega
          have d46950 : (x 15 13).toNat = 0 := by
            have r46951 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
            have e46952 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e46953 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b46954 := hb (x 13 3)
            have b46955 := hb (x 14 2)
            have b46956 := hb (x 15 13)
            have b46957 := hb (x 16 12)
            clear * - r46951 e46952 e46953 b46954 b46955 b46956 b46957 d46934 d46930
            omega
          have d46958 : (x 15 2 && x 15 13).toNat = 0 := by
            have r46959 := hand2 (x 15 2) (x 15 13)
            have b46960 := hb (x 15 13)
            have b46961 := hb (x 15 2 && x 15 13)
            clear * - r46959 b46960 b46961 d46950
            omega
          have d46962 : (x 15 3 && x 15 13).toNat = 0 := by
            have r46963 := hand2 (x 15 3) (x 15 13)
            have b46964 := hb (x 15 13)
            have b46965 := hb (x 15 3 && x 15 13)
            clear * - r46963 b46964 b46965 d46950
            omega
          have d46966 : (x 14 1 && x 14 14).toNat = 1 := by
            have r46967 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
            have b46968 := hb (x 13 2)
            have b46969 := hb (x 15 13)
            have b46970 := hb (x 14 1 && x 14 14)
            clear * - r46967 b46968 b46969 b46970 d46950 d46778
            omega
          have d46971 : (x 14 1).toNat = 1 := by
            have r46972 := hand1 (x 14 1) (x 14 14)
            have b46973 := hb (x 14 1)
            have b46974 := hb (x 14 1 && x 14 14)
            clear * - r46972 b46973 b46974 d46966
            omega
          have d46975 : (x 15 14).toNat = 0 := by
            have r46976 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
            have b46977 := hb (x 14 1)
            have b46978 := hb (x 15 14)
            clear * - r46976 b46977 b46978 d46971
            omega
          have d46979 : (x 15 1 && x 15 14).toNat = 0 := by
            have r46980 := hand2 (x 15 1) (x 15 14)
            have b46981 := hb (x 15 14)
            have b46982 := hb (x 15 1 && x 15 14)
            clear * - r46980 b46981 b46982 d46975
            omega
          have d46983 : (x 15 2).toNat = 0 := by
            have r46984 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
            have b46985 := hb (x 15 2)
            have b46986 := hb (x 15 14)
            clear * - r46984 b46985 b46986 d46975
            omega
          have d46987 : (x 14 2).toNat = 0 := by
            have r46988 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
            have e46989 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
            have e46990 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
            have b46991 := hb (x 13 3)
            have b46992 := hb (x 14 2)
            have b46993 := hb (x 15 13)
            have b46994 := hb (x 16 12)
            clear * - r46988 e46989 e46990 b46991 b46992 b46993 b46994 d46934 d46950 d46930
            omega
          have d46995 : (x 16 13).toNat = 1 := by
            have r46996 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
            have b46997 := hb (x 14 2)
            have b46998 := hb (x 16 13)
            have b46999 := hb (x 15 1 && x 15 14)
            clear * - r46996 b46997 b46998 b46999 d46979 d46987
            omega
          have d47000 : (x 17 12).toNat = 0 := by
            have r47001 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
            have e47002 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e47003 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b47004 := hb (x 14 3)
            have b47005 := hb (x 15 2)
            have b47006 := hb (x 16 13)
            have b47007 := hb (x 17 12)
            clear * - r47001 e47002 e47003 b47004 b47005 b47006 b47007 d46995 d46983
            omega
          have d47008 : (x 14 3).toNat = 0 := by
            have r47009 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
            have e47010 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e47011 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b47012 := hb (x 14 3)
            have b47013 := hb (x 15 2)
            have b47014 := hb (x 16 13)
            have b47015 := hb (x 17 12)
            clear * - r47009 e47010 e47011 b47012 b47013 b47014 b47015 d47000 d46995 d46983
            omega
          have d47016 : (x 14 3 && x 14 14).toNat = 0 := by
            have r47017 := hand1 (x 14 3) (x 14 14)
            have b47018 := hb (x 14 3)
            have b47019 := hb (x 14 3 && x 14 14)
            clear * - r47017 b47018 b47019 d47008
            omega
          have d47020 : (x 17 11).toNat = 1 := by
            have r47021 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
            have b47022 := hb (x 13 4)
            have b47023 := hb (x 17 11)
            have b47024 := hb (x 16 1 && x 16 12)
            have b47025 := hb (x 15 2 && x 15 13)
            have b47026 := hb (x 14 3 && x 14 14)
            clear * - r47021 b47022 b47023 b47024 b47025 b47026 d46942 d46958 d47016 d46907
            omega
          have d47027 : (x 17 3).toNat = 1 := by
            have r47028 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
            have b47029 := hb (x 17 3)
            have b47030 := hb (x 17 11)
            clear * - r47028 b47029 b47030 d47020
            omega
          have d47031 : (x 20 12).toNat = 0 := by
            have r47032 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
            have e47033 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e47034 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b47035 := hb (x 17 3)
            have b47036 := hb (x 18 2)
            have b47037 := hb (x 19 13)
            have b47038 := hb (x 20 12)
            clear * - r47032 e47033 e47034 b47035 b47036 b47037 b47038 d47027
            omega
          have d47039 : (x 19 13).toNat = 0 := by
            have r47040 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
            have e47041 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e47042 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b47043 := hb (x 17 3)
            have b47044 := hb (x 18 2)
            have b47045 := hb (x 19 13)
            have b47046 := hb (x 20 12)
            clear * - r47040 e47041 e47042 b47043 b47044 b47045 b47046 d47031 d47027
            omega
          have d47047 : (x 18 1 && x 18 14).toNat = 1 := by
            have r47048 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
            have b47049 := hb (x 17 2)
            have b47050 := hb (x 19 13)
            have b47051 := hb (x 18 1 && x 18 14)
            clear * - r47048 b47049 b47050 b47051 d47039 d46891
            omega
          have d47052 : (x 18 14).toNat = 1 := by
            have r47053 := hand2 (x 18 1) (x 18 14)
            have b47054 := hb (x 18 14)
            have b47055 := hb (x 18 1 && x 18 14)
            clear * - r47053 b47054 b47055 d47047
            omega
          have d47056 : (x 17 1).toNat = 0 := by
            have r47057 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
            have b47058 := hb (x 17 1)
            have b47059 := hb (x 18 14)
            clear * - r47057 b47058 b47059 d47052
            omega
          have d47060 : (x 17 1 && x 17 11).toNat = 0 := by
            have r47061 := hand1 (x 17 1) (x 17 11)
            have b47062 := hb (x 17 1)
            have b47063 := hb (x 17 1 && x 17 11)
            clear * - r47061 b47062 b47063 d47056
            omega
          have d47064 : (x 18 2).toNat = 0 := by
            have r47065 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
            have e47066 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
            have e47067 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
            have b47068 := hb (x 17 3)
            have b47069 := hb (x 18 2)
            have b47070 := hb (x 19 13)
            have b47071 := hb (x 20 12)
            clear * - r47065 e47066 e47067 b47068 b47069 b47070 b47071 d47031 d47039 d47027
            omega
          have d47072 : (x 18 10).toNat = 0 := by
            have r47073 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
            have b47074 := hb (x 18 2)
            have b47075 := hb (x 18 10)
            clear * - r47073 b47074 b47075 d47064
            omega
          have r47076 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := hcov10 18
          have b47077 := hb (x 13 5)
          have b47078 := hb (x 18 10)
          have b47079 := hb (x 17 1 && x 17 11)
          have b47080 := hb (x 16 2 && x 16 12)
          have b47081 := hb (x 15 3 && x 15 13)
          have b47082 := hb (x 14 4 && x 14 14)
          linarith only [r47076, b47077, b47078, b47079, b47080, b47081, b47082, d47072, d47060, d46946, d46962, d46844, d46856]
      · have f47083 : (x 1 1).toNat = 1 := by rw [h45510]; rfl
        have d47084 : (x 2 14).toNat = 0 := by
          have r47085 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
          have b47086 := hb (x 1 1)
          have b47087 := hb (x 2 14)
          clear * - r47085 b47086 b47087 f47083
          omega
        have d47088 : (x 2 1 && x 2 14).toNat = 0 := by
          have r47089 := hand2 (x 2 1) (x 2 14)
          have b47090 := hb (x 2 14)
          have b47091 := hb (x 2 1 && x 2 14)
          clear * - r47089 b47090 b47091 d47084
          omega
        have d47092 : (x 2 2).toNat = 0 := by
          have r47093 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b47094 := hb (x 2 2)
          have b47095 := hb (x 2 14)
          clear * - r47093 b47094 b47095 d47084
          omega
        have d47096 : (x 4 13).toNat = 1 := by
          have r47097 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
          have b47098 := hb (x 2 2)
          have b47099 := hb (x 4 13)
          have b47100 := hb (x 3 1 && x 3 14)
          clear * - r47097 b47098 b47099 b47100 g33 d47092
          omega
        have d47101 : (x 4 1).toNat = 1 := by
          have r47102 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b47103 := hb (x 4 1)
          have b47104 := hb (x 4 13)
          clear * - r47102 b47103 b47104 d47096
          omega
        have d47105 : (x 5 14).toNat = 0 := by
          have r47106 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
          have b47107 := hb (x 4 1)
          have b47108 := hb (x 5 14)
          clear * - r47106 b47107 b47108 d47101
          omega
        have d47109 : (x 5 1 && x 5 14).toNat = 0 := by
          have r47110 := hand2 (x 5 1) (x 5 14)
          have b47111 := hb (x 5 14)
          have b47112 := hb (x 5 1 && x 5 14)
          clear * - r47110 b47111 b47112 d47105
          omega
        have d47113 : (x 5 2).toNat = 0 := by
          have r47114 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b47115 := hb (x 5 2)
          have b47116 := hb (x 5 14)
          clear * - r47114 b47115 b47116 d47105
          omega
        have d47117 : (x 3 13).toNat = 1 := by
          have r47118 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
          have b47119 := hb (x 1 2)
          have b47120 := hb (x 3 13)
          have b47121 := hb (x 2 1 && x 2 14)
          clear * - r47118 b47119 b47120 b47121 d47088 g10
          omega
        have d47122 : (x 3 1).toNat = 1 := by
          have r47123 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b47124 := hb (x 3 1)
          have b47125 := hb (x 3 13)
          clear * - r47123 b47124 b47125 d47117
          omega
        have d47126 : (x 4 14).toNat = 0 := by
          have r47127 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
          have b47128 := hb (x 3 1)
          have b47129 := hb (x 4 14)
          clear * - r47127 b47128 b47129 d47122
          omega
        have d47130 : (x 4 1 && x 4 14).toNat = 0 := by
          have r47131 := hand2 (x 4 1) (x 4 14)
          have b47132 := hb (x 4 14)
          have b47133 := hb (x 4 1 && x 4 14)
          clear * - r47131 b47132 b47133 d47126
          omega
        have d47134 : (x 5 13).toNat = 1 := by
          have r47135 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
          have b47136 := hb (x 3 2)
          have b47137 := hb (x 5 13)
          have b47138 := hb (x 4 1 && x 4 14)
          clear * - r47135 b47136 b47137 b47138 d47130 g14
          omega
        have d47139 : (x 5 1).toNat = 1 := by
          have r47140 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
          have b47141 := hb (x 5 1)
          have b47142 := hb (x 5 13)
          clear * - r47140 b47141 b47142 d47134
          omega
        have d47143 : (x 6 14).toNat = 0 := by
          have r47144 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
          have b47145 := hb (x 5 1)
          have b47146 := hb (x 6 14)
          clear * - r47144 b47145 b47146 d47139
          omega
        have d47147 : (x 6 1 && x 6 14).toNat = 0 := by
          have r47148 := hand2 (x 6 1) (x 6 14)
          have b47149 := hb (x 6 14)
          have b47150 := hb (x 6 1 && x 6 14)
          clear * - r47148 b47149 b47150 d47143
          omega
        have d47151 : (x 7 13).toNat = 1 := by
          have r47152 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
          have b47153 := hb (x 5 2)
          have b47154 := hb (x 7 13)
          have b47155 := hb (x 6 1 && x 6 14)
          clear * - r47152 b47153 b47154 b47155 d47147 d47113
          omega
        have d47156 : (x 7 1).toNat = 1 := by
          have r47157 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b47158 := hb (x 7 1)
          have b47159 := hb (x 7 13)
          clear * - r47157 b47158 b47159 d47151
          omega
        have d47160 : (x 8 14).toNat = 0 := by
          have r47161 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
          have b47162 := hb (x 7 1)
          have b47163 := hb (x 8 14)
          clear * - r47161 b47162 b47163 d47156
          omega
        have d47164 : (x 8 1 && x 8 14).toNat = 0 := by
          have r47165 := hand2 (x 8 1) (x 8 14)
          have b47166 := hb (x 8 14)
          have b47167 := hb (x 8 1 && x 8 14)
          clear * - r47165 b47166 b47167 d47160
          omega
        have d47168 : (x 8 2).toNat = 0 := by
          have r47169 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
          have b47170 := hb (x 8 2)
          have b47171 := hb (x 8 14)
          clear * - r47169 b47170 b47171 d47160
          omega
        have d47172 : (x 6 2).toNat = 0 := by
          have r47173 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
          have b47174 := hb (x 6 2)
          have b47175 := hb (x 6 14)
          clear * - r47173 b47174 b47175 d47143
          omega
        have d47176 : (x 4 2).toNat = 0 := by
          have r47177 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b47178 := hb (x 4 2)
          have b47179 := hb (x 4 14)
          clear * - r47177 b47178 b47179 d47126
          omega
        have d47180 : (x 6 13).toNat = 1 := by
          have r47181 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
          have b47182 := hb (x 4 2)
          have b47183 := hb (x 6 13)
          have b47184 := hb (x 5 1 && x 5 14)
          clear * - r47181 b47182 b47183 b47184 d47109 d47176
          omega
        have d47185 : (x 6 1).toNat = 1 := by
          have r47186 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b47187 := hb (x 6 1)
          have b47188 := hb (x 6 13)
          clear * - r47186 b47187 b47188 d47180
          omega
        have d47189 : (x 7 14).toNat = 0 := by
          have r47190 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
          have b47191 := hb (x 6 1)
          have b47192 := hb (x 7 14)
          clear * - r47190 b47191 b47192 d47185
          omega
        have d47193 : (x 7 1 && x 7 14).toNat = 0 := by
          have r47194 := hand2 (x 7 1) (x 7 14)
          have b47195 := hb (x 7 14)
          have b47196 := hb (x 7 1 && x 7 14)
          clear * - r47194 b47195 b47196 d47189
          omega
        have d47197 : (x 8 13).toNat = 1 := by
          have r47198 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
          have b47199 := hb (x 6 2)
          have b47200 := hb (x 8 13)
          have b47201 := hb (x 7 1 && x 7 14)
          clear * - r47198 b47199 b47200 b47201 d47193 d47172
          omega
        have d47202 : (x 8 1).toNat = 1 := by
          have r47203 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b47204 := hb (x 8 1)
          have b47205 := hb (x 8 13)
          clear * - r47203 b47204 b47205 d47197
          omega
        have d47206 : (x 9 14).toNat = 0 := by
          have r47207 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
          have b47208 := hb (x 8 1)
          have b47209 := hb (x 9 14)
          clear * - r47207 b47208 b47209 d47202
          omega
        have d47210 : (x 9 1 && x 9 14).toNat = 0 := by
          have r47211 := hand2 (x 9 1) (x 9 14)
          have b47212 := hb (x 9 14)
          have b47213 := hb (x 9 1 && x 9 14)
          clear * - r47211 b47212 b47213 d47206
          omega
        have d47214 : (x 10 13).toNat = 1 := by
          have r47215 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
          have b47216 := hb (x 8 2)
          have b47217 := hb (x 10 13)
          have b47218 := hb (x 9 1 && x 9 14)
          clear * - r47215 b47216 b47217 b47218 d47210 d47168
          omega
        have d47219 : (x 10 1).toNat = 1 := by
          have r47220 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b47221 := hb (x 10 1)
          have b47222 := hb (x 10 13)
          clear * - r47220 b47221 b47222 d47214
          omega
        have d47223 : (x 11 14).toNat = 0 := by
          have r47224 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
          have b47225 := hb (x 10 1)
          have b47226 := hb (x 11 14)
          clear * - r47224 b47225 b47226 d47219
          omega
        have d47227 : (x 11 1 && x 11 14).toNat = 0 := by
          have r47228 := hand2 (x 11 1) (x 11 14)
          have b47229 := hb (x 11 14)
          have b47230 := hb (x 11 1 && x 11 14)
          clear * - r47228 b47229 b47230 d47223
          omega
        have d47231 : (x 11 2).toNat = 0 := by
          have r47232 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b47233 := hb (x 11 2)
          have b47234 := hb (x 11 14)
          clear * - r47232 b47233 b47234 d47223
          omega
        have d47235 : (x 9 2).toNat = 0 := by
          have r47236 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b47237 := hb (x 9 2)
          have b47238 := hb (x 9 14)
          clear * - r47236 b47237 b47238 d47206
          omega
        have d47239 : (x 7 2).toNat = 0 := by
          have r47240 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b47241 := hb (x 7 2)
          have b47242 := hb (x 7 14)
          clear * - r47240 b47241 b47242 d47189
          omega
        have d47243 : (x 9 13).toNat = 1 := by
          have r47244 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
          have b47245 := hb (x 7 2)
          have b47246 := hb (x 9 13)
          have b47247 := hb (x 8 1 && x 8 14)
          clear * - r47244 b47245 b47246 b47247 d47164 d47239
          omega
        have d47248 : (x 9 1).toNat = 1 := by
          have r47249 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b47250 := hb (x 9 1)
          have b47251 := hb (x 9 13)
          clear * - r47249 b47250 b47251 d47243
          omega
        have d47252 : (x 10 14).toNat = 0 := by
          have r47253 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
          have b47254 := hb (x 9 1)
          have b47255 := hb (x 10 14)
          clear * - r47253 b47254 b47255 d47248
          omega
        have d47256 : (x 10 1 && x 10 14).toNat = 0 := by
          have r47257 := hand2 (x 10 1) (x 10 14)
          have b47258 := hb (x 10 14)
          have b47259 := hb (x 10 1 && x 10 14)
          clear * - r47257 b47258 b47259 d47252
          omega
        have d47260 : (x 11 13).toNat = 1 := by
          have r47261 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
          have b47262 := hb (x 9 2)
          have b47263 := hb (x 11 13)
          have b47264 := hb (x 10 1 && x 10 14)
          clear * - r47261 b47262 b47263 b47264 d47256 d47235
          omega
        have d47265 : (x 11 1).toNat = 1 := by
          have r47266 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
          have b47267 := hb (x 11 1)
          have b47268 := hb (x 11 13)
          clear * - r47266 b47267 b47268 d47260
          omega
        have d47269 : (x 12 14).toNat = 0 := by
          have r47270 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
          have b47271 := hb (x 11 1)
          have b47272 := hb (x 12 14)
          clear * - r47270 b47271 b47272 d47265
          omega
        have d47273 : (x 12 1 && x 12 14).toNat = 0 := by
          have r47274 := hand2 (x 12 1) (x 12 14)
          have b47275 := hb (x 12 14)
          have b47276 := hb (x 12 1 && x 12 14)
          clear * - r47274 b47275 b47276 d47269
          omega
        have d47277 : (x 13 13).toNat = 1 := by
          have r47278 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
          have b47279 := hb (x 11 2)
          have b47280 := hb (x 13 13)
          have b47281 := hb (x 12 1 && x 12 14)
          clear * - r47278 b47279 b47280 b47281 d47273 d47231
          omega
        have d47282 : (x 13 1).toNat = 1 := by
          have r47283 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have b47284 := hb (x 13 1)
          have b47285 := hb (x 13 13)
          clear * - r47283 b47284 b47285 d47277
          omega
        have d47286 : (x 14 14).toNat = 0 := by
          have r47287 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
          have b47288 := hb (x 13 1)
          have b47289 := hb (x 14 14)
          clear * - r47287 b47288 b47289 d47282
          omega
        have d47290 : (x 14 1 && x 14 14).toNat = 0 := by
          have r47291 := hand2 (x 14 1) (x 14 14)
          have b47292 := hb (x 14 14)
          have b47293 := hb (x 14 1 && x 14 14)
          clear * - r47291 b47292 b47293 d47286
          omega
        have d47294 : (x 14 3 && x 14 14).toNat = 0 := by
          have r47295 := hand2 (x 14 3) (x 14 14)
          have b47296 := hb (x 14 14)
          have b47297 := hb (x 14 3 && x 14 14)
          clear * - r47295 b47296 b47297 d47286
          omega
        have d47298 : (x 14 2).toNat = 0 := by
          have r47299 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
          have b47300 := hb (x 14 2)
          have b47301 := hb (x 14 14)
          clear * - r47299 b47300 b47301 d47286
          omega
        have d47302 : (x 12 2).toNat = 0 := by
          have r47303 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
          have b47304 := hb (x 12 2)
          have b47305 := hb (x 12 14)
          clear * - r47303 b47304 b47305 d47269
          omega
        have d47306 : (x 10 2).toNat = 0 := by
          have r47307 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
          have b47308 := hb (x 10 2)
          have b47309 := hb (x 10 14)
          clear * - r47307 b47308 b47309 d47252
          omega
        have d47310 : (x 12 13).toNat = 1 := by
          have r47311 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
          have b47312 := hb (x 10 2)
          have b47313 := hb (x 12 13)
          have b47314 := hb (x 11 1 && x 11 14)
          clear * - r47311 b47312 b47313 b47314 d47227 d47306
          omega
        have d47315 : (x 12 1).toNat = 1 := by
          have r47316 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b47317 := hb (x 12 1)
          have b47318 := hb (x 12 13)
          clear * - r47316 b47317 b47318 d47310
          omega
        have d47319 : (x 13 14).toNat = 0 := by
          have r47320 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
          have b47321 := hb (x 12 1)
          have b47322 := hb (x 13 14)
          clear * - r47320 b47321 b47322 d47315
          omega
        have d47323 : (x 13 1 && x 13 14).toNat = 0 := by
          have r47324 := hand2 (x 13 1) (x 13 14)
          have b47325 := hb (x 13 14)
          have b47326 := hb (x 13 1 && x 13 14)
          clear * - r47324 b47325 b47326 d47319
          omega
        have d47327 : (x 14 13).toNat = 1 := by
          have r47328 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
          have b47329 := hb (x 12 2)
          have b47330 := hb (x 14 13)
          have b47331 := hb (x 13 1 && x 13 14)
          clear * - r47328 b47329 b47330 b47331 d47323 d47302
          omega
        have d47332 : (x 14 1).toNat = 1 := by
          have r47333 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
          have b47334 := hb (x 14 1)
          have b47335 := hb (x 14 13)
          clear * - r47333 b47334 b47335 d47327
          omega
        have d47336 : (x 15 14).toNat = 0 := by
          have r47337 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
          have b47338 := hb (x 14 1)
          have b47339 := hb (x 15 14)
          clear * - r47337 b47338 b47339 d47332
          omega
        have d47340 : (x 15 1 && x 15 14).toNat = 0 := by
          have r47341 := hand2 (x 15 1) (x 15 14)
          have b47342 := hb (x 15 14)
          have b47343 := hb (x 15 1 && x 15 14)
          clear * - r47341 b47342 b47343 d47336
          omega
        have d47344 : (x 16 13).toNat = 1 := by
          have r47345 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
          have b47346 := hb (x 14 2)
          have b47347 := hb (x 16 13)
          have b47348 := hb (x 15 1 && x 15 14)
          clear * - r47345 b47346 b47347 b47348 d47340 d47298
          omega
        have d47349 : (x 16 1).toNat = 1 := by
          have r47350 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
          have b47351 := hb (x 16 1)
          have b47352 := hb (x 16 13)
          clear * - r47350 b47351 b47352 d47344
          omega
        have d47353 : (x 17 14).toNat = 0 := by
          have r47354 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
          have b47355 := hb (x 16 1)
          have b47356 := hb (x 17 14)
          clear * - r47354 b47355 b47356 d47349
          omega
        have d47357 : (x 17 2).toNat = 0 := by
          have r47358 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
          have b47359 := hb (x 17 2)
          have b47360 := hb (x 17 14)
          clear * - r47358 b47359 b47360 d47353
          omega
        have d47361 : (x 15 2).toNat = 0 := by
          have r47362 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b47363 := hb (x 15 2)
          have b47364 := hb (x 15 14)
          clear * - r47362 b47363 b47364 d47336
          omega
        have d47365 : (x 15 2 && x 15 13).toNat = 0 := by
          have r47366 := hand1 (x 15 2) (x 15 13)
          have b47367 := hb (x 15 2)
          have b47368 := hb (x 15 2 && x 15 13)
          clear * - r47366 b47367 b47368 d47361
          omega
        have d47369 : (x 13 2).toNat = 0 := by
          have r47370 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b47371 := hb (x 13 2)
          have b47372 := hb (x 13 14)
          clear * - r47370 b47371 b47372 d47319
          omega
        have d47373 : (x 15 13).toNat = 1 := by
          have r47374 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
          have b47375 := hb (x 13 2)
          have b47376 := hb (x 15 13)
          have b47377 := hb (x 14 1 && x 14 14)
          clear * - r47374 b47375 b47376 b47377 d47290 d47369
          omega
        have d47378 : (x 15 1).toNat = 1 := by
          have r47379 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
          have b47380 := hb (x 15 1)
          have b47381 := hb (x 15 13)
          clear * - r47379 b47380 b47381 d47373
          omega
        have d47382 : (x 16 14).toNat = 0 := by
          have r47383 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
          have b47384 := hb (x 15 1)
          have b47385 := hb (x 16 14)
          clear * - r47383 b47384 b47385 d47378
          omega
        have d47386 : (x 16 1 && x 16 14).toNat = 0 := by
          have r47387 := hand2 (x 16 1) (x 16 14)
          have b47388 := hb (x 16 14)
          have b47389 := hb (x 16 1 && x 16 14)
          clear * - r47387 b47388 b47389 d47382
          omega
        have d47390 : (x 17 13).toNat = 1 := by
          have r47391 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
          have b47392 := hb (x 15 2)
          have b47393 := hb (x 17 13)
          have b47394 := hb (x 16 1 && x 16 14)
          clear * - r47391 b47392 b47393 b47394 d47386 d47361
          omega
        have d47395 : (x 17 1).toNat = 1 := by
          have r47396 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
          have b47397 := hb (x 17 1)
          have b47398 := hb (x 17 13)
          clear * - r47396 b47397 b47398 d47390
          omega
        have d47399 : (x 18 14).toNat = 0 := by
          have r47400 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
          have b47401 := hb (x 17 1)
          have b47402 := hb (x 18 14)
          clear * - r47400 b47401 b47402 d47395
          omega
        have d47403 : (x 18 1 && x 18 14).toNat = 0 := by
          have r47404 := hand2 (x 18 1) (x 18 14)
          have b47405 := hb (x 18 14)
          have b47406 := hb (x 18 1 && x 18 14)
          clear * - r47404 b47405 b47406 d47399
          omega
        have d47407 : (x 19 13).toNat = 1 := by
          have r47408 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
          have b47409 := hb (x 17 2)
          have b47410 := hb (x 19 13)
          have b47411 := hb (x 18 1 && x 18 14)
          clear * - r47408 b47409 b47410 b47411 d47403 d47357
          omega
        have d47412 : (x 18 2).toNat = 0 := by
          have r47413 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
          have b47414 := hb (x 18 2)
          have b47415 := hb (x 18 14)
          clear * - r47413 b47414 b47415 d47399
          omega
        have d47416 : (x 20 12).toNat = 0 := by
          have r47417 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e47418 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e47419 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b47420 := hb (x 17 3)
          have b47421 := hb (x 18 2)
          have b47422 := hb (x 19 13)
          have b47423 := hb (x 20 12)
          clear * - r47417 e47418 e47419 b47420 b47421 b47422 b47423 d47407 d47412
          omega
        have d47424 : (x 17 3).toNat = 0 := by
          have r47425 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e47426 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e47427 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b47428 := hb (x 17 3)
          have b47429 := hb (x 18 2)
          have b47430 := hb (x 19 13)
          have b47431 := hb (x 20 12)
          clear * - r47425 e47426 e47427 b47428 b47429 b47430 b47431 d47416 d47407 d47412
          omega
        have d47432 : (x 17 11).toNat = 0 := by
          have r47433 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b47434 := hb (x 17 3)
          have b47435 := hb (x 17 11)
          clear * - r47433 b47434 b47435 d47424
          omega
        have d47436 : (x 16 12).toNat = 0 := by
          have r47437 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e47438 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e47439 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b47440 := hb (x 13 3)
          have b47441 := hb (x 14 2)
          have b47442 := hb (x 15 13)
          have b47443 := hb (x 16 12)
          clear * - r47437 e47438 e47439 b47440 b47441 b47442 b47443 d47373 d47298
          omega
        have d47444 : (x 16 1 && x 16 12).toNat = 0 := by
          have r47445 := hand2 (x 16 1) (x 16 12)
          have b47446 := hb (x 16 12)
          have b47447 := hb (x 16 1 && x 16 12)
          clear * - r47445 b47446 b47447 d47436
          omega
        have d47448 : (x 13 12).toNat = 0 := by
          have r47449 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e47450 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e47451 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b47452 := hb (x 10 3)
          have b47453 := hb (x 11 2)
          have b47454 := hb (x 12 13)
          have b47455 := hb (x 13 12)
          clear * - r47449 e47450 e47451 b47452 b47453 b47454 b47455 d47310 d47231
          omega
        have d47456 : (x 13 4).toNat = 0 := by
          have r47457 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b47458 := hb (x 13 4)
          have b47459 := hb (x 13 12)
          clear * - r47457 b47458 b47459 d47448
          omega
        have r47460 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
        have b47461 := hb (x 13 4)
        have b47462 := hb (x 17 11)
        have b47463 := hb (x 16 1 && x 16 12)
        have b47464 := hb (x 15 2 && x 15 13)
        have b47465 := hb (x 14 3 && x 14 14)
        linarith only [r47460, b47461, b47462, b47463, b47464, b47465, d47432, d47444, d47365, d47294, d47456]
    · have f47466 : (x 0 13).toNat = 1 := by rw [h45508]; rfl
      have d47467 : (x 1 12).toNat = 0 := by
        have r47468 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
        have e47469 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e47470 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b47471 := hb (x (-2) 3)
        have b47472 := hb (x (-1) 2)
        have b47473 := hb (x 0 13)
        have b47474 := hb (x 1 12)
        clear * - r47468 e47469 e47470 b47471 b47472 b47473 b47474 f47466
        omega
      have d47475 : (x (-1) 2).toNat = 0 := by
        have r47476 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
        have e47477 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e47478 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b47479 := hb (x (-2) 3)
        have b47480 := hb (x (-1) 2)
        have b47481 := hb (x 0 13)
        have b47482 := hb (x 1 12)
        clear * - r47476 e47477 e47478 b47479 b47480 b47481 b47482 d47467 f47466
        omega
      have d47483 : (x 1 13).toNat = 1 := by
        have r47484 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
        have b47485 := hb (x (-1) 2)
        have b47486 := hb (x 1 13)
        have b47487 := hb (x 0 1 && x 0 14)
        clear * - r47484 b47485 b47486 b47487 g32 d47475
        omega
      have d47488 : (x 1 1).toNat = 1 := by
        have r47489 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
        have b47490 := hb (x 1 1)
        have b47491 := hb (x 1 13)
        clear * - r47489 b47490 b47491 d47483
        omega
      have d47492 : (x 2 14).toNat = 0 := by
        have r47493 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
        have b47494 := hb (x 1 1)
        have b47495 := hb (x 2 14)
        clear * - r47493 b47494 b47495 d47488
        omega
      have d47496 : (x 2 1 && x 2 14).toNat = 0 := by
        have r47497 := hand2 (x 2 1) (x 2 14)
        have b47498 := hb (x 2 14)
        have b47499 := hb (x 2 1 && x 2 14)
        clear * - r47497 b47498 b47499 d47492
        omega
      have d47500 : (x 3 13).toNat = 1 := by
        have r47501 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
        have b47502 := hb (x 1 2)
        have b47503 := hb (x 3 13)
        have b47504 := hb (x 2 1 && x 2 14)
        clear * - r47501 b47502 b47503 b47504 d47496 g10
        omega
      have d47505 : (x 3 1).toNat = 1 := by
        have r47506 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b47507 := hb (x 3 1)
        have b47508 := hb (x 3 13)
        clear * - r47506 b47507 b47508 d47500
        omega
      have d47509 : (x 4 14).toNat = 0 := by
        have r47510 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
        have b47511 := hb (x 3 1)
        have b47512 := hb (x 4 14)
        clear * - r47510 b47511 b47512 d47505
        omega
      have d47513 : (x 4 1 && x 4 14).toNat = 0 := by
        have r47514 := hand2 (x 4 1) (x 4 14)
        have b47515 := hb (x 4 14)
        have b47516 := hb (x 4 1 && x 4 14)
        clear * - r47514 b47515 b47516 d47509
        omega
      have d47517 : (x 5 13).toNat = 1 := by
        have r47518 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
        have b47519 := hb (x 3 2)
        have b47520 := hb (x 5 13)
        have b47521 := hb (x 4 1 && x 4 14)
        clear * - r47518 b47519 b47520 b47521 d47513 g14
        omega
      have d47522 : (x 5 1).toNat = 1 := by
        have r47523 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
        have b47524 := hb (x 5 1)
        have b47525 := hb (x 5 13)
        clear * - r47523 b47524 b47525 d47517
        omega
      have d47526 : (x 6 14).toNat = 0 := by
        have r47527 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
        have b47528 := hb (x 5 1)
        have b47529 := hb (x 6 14)
        clear * - r47527 b47528 b47529 d47522
        omega
      have d47530 : (x 6 1 && x 6 14).toNat = 0 := by
        have r47531 := hand2 (x 6 1) (x 6 14)
        have b47532 := hb (x 6 14)
        have b47533 := hb (x 6 1 && x 6 14)
        clear * - r47531 b47532 b47533 d47526
        omega
      have d47534 : (x 6 2).toNat = 0 := by
        have r47535 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have b47536 := hb (x 6 2)
        have b47537 := hb (x 6 14)
        clear * - r47535 b47536 b47537 d47526
        omega
      have d47538 : (x 6 12).toNat = 0 := by
        have r47539 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
        have e47540 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e47541 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b47542 := hb (x 3 3)
        have b47543 := hb (x 4 2)
        have b47544 := hb (x 5 13)
        have b47545 := hb (x 6 12)
        clear * - r47539 e47540 e47541 b47542 b47543 b47544 b47545 d47517
        omega
      have d47546 : (x 4 2).toNat = 0 := by
        have r47547 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
        have e47548 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e47549 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b47550 := hb (x 3 3)
        have b47551 := hb (x 4 2)
        have b47552 := hb (x 5 13)
        have b47553 := hb (x 6 12)
        clear * - r47547 e47548 e47549 b47550 b47551 b47552 b47553 d47538 d47517
        omega
      have d47554 : (x 4 12).toNat = 0 := by
        have r47555 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
        have e47556 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e47557 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b47558 := hb (x 1 3)
        have b47559 := hb (x 2 2)
        have b47560 := hb (x 3 13)
        have b47561 := hb (x 4 12)
        clear * - r47555 e47556 e47557 b47558 b47559 b47560 b47561 d47500
        omega
      have d47562 : (x 2 2).toNat = 0 := by
        have r47563 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
        have e47564 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e47565 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b47566 := hb (x 1 3)
        have b47567 := hb (x 2 2)
        have b47568 := hb (x 3 13)
        have b47569 := hb (x 4 12)
        clear * - r47563 e47564 e47565 b47566 b47567 b47568 b47569 d47554 d47500
        omega
      have d47570 : (x 4 13).toNat = 1 := by
        have r47571 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
        have b47572 := hb (x 2 2)
        have b47573 := hb (x 4 13)
        have b47574 := hb (x 3 1 && x 3 14)
        clear * - r47571 b47572 b47573 b47574 g33 d47562
        omega
      have d47575 : (x 4 1).toNat = 1 := by
        have r47576 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b47577 := hb (x 4 1)
        have b47578 := hb (x 4 13)
        clear * - r47576 b47577 b47578 d47570
        omega
      have d47579 : (x 5 14).toNat = 0 := by
        have r47580 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
        have b47581 := hb (x 4 1)
        have b47582 := hb (x 5 14)
        clear * - r47580 b47581 b47582 d47575
        omega
      have d47583 : (x 5 1 && x 5 14).toNat = 0 := by
        have r47584 := hand2 (x 5 1) (x 5 14)
        have b47585 := hb (x 5 14)
        have b47586 := hb (x 5 1 && x 5 14)
        clear * - r47584 b47585 b47586 d47579
        omega
      have d47587 : (x 6 13).toNat = 1 := by
        have r47588 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
        have b47589 := hb (x 4 2)
        have b47590 := hb (x 6 13)
        have b47591 := hb (x 5 1 && x 5 14)
        clear * - r47588 b47589 b47590 b47591 d47583 d47546
        omega
      have d47592 : (x 6 1).toNat = 1 := by
        have r47593 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
        have b47594 := hb (x 6 1)
        have b47595 := hb (x 6 13)
        clear * - r47593 b47594 b47595 d47587
        omega
      have d47596 : (x 7 14).toNat = 0 := by
        have r47597 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
        have b47598 := hb (x 6 1)
        have b47599 := hb (x 7 14)
        clear * - r47597 b47598 b47599 d47592
        omega
      have d47600 : (x 7 1 && x 7 14).toNat = 0 := by
        have r47601 := hand2 (x 7 1) (x 7 14)
        have b47602 := hb (x 7 14)
        have b47603 := hb (x 7 1 && x 7 14)
        clear * - r47601 b47602 b47603 d47596
        omega
      have d47604 : (x 8 13).toNat = 1 := by
        have r47605 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
        have b47606 := hb (x 6 2)
        have b47607 := hb (x 8 13)
        have b47608 := hb (x 7 1 && x 7 14)
        clear * - r47605 b47606 b47607 b47608 d47600 d47534
        omega
      have d47609 : (x 8 1).toNat = 1 := by
        have r47610 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b47611 := hb (x 8 1)
        have b47612 := hb (x 8 13)
        clear * - r47610 b47611 b47612 d47604
        omega
      have d47613 : (x 9 14).toNat = 0 := by
        have r47614 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
        have b47615 := hb (x 8 1)
        have b47616 := hb (x 9 14)
        clear * - r47614 b47615 b47616 d47609
        omega
      have d47617 : (x 9 1 && x 9 14).toNat = 0 := by
        have r47618 := hand2 (x 9 1) (x 9 14)
        have b47619 := hb (x 9 14)
        have b47620 := hb (x 9 1 && x 9 14)
        clear * - r47618 b47619 b47620 d47613
        omega
      have d47621 : (x 9 2).toNat = 0 := by
        have r47622 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b47623 := hb (x 9 2)
        have b47624 := hb (x 9 14)
        clear * - r47622 b47623 b47624 d47613
        omega
      have d47625 : (x 9 12).toNat = 0 := by
        have r47626 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
        have e47627 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e47628 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b47629 := hb (x 6 3)
        have b47630 := hb (x 7 2)
        have b47631 := hb (x 8 13)
        have b47632 := hb (x 9 12)
        clear * - r47626 e47627 e47628 b47629 b47630 b47631 b47632 d47604
        omega
      have d47633 : (x 7 2).toNat = 0 := by
        have r47634 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
        have e47635 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e47636 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b47637 := hb (x 6 3)
        have b47638 := hb (x 7 2)
        have b47639 := hb (x 8 13)
        have b47640 := hb (x 9 12)
        clear * - r47634 e47635 e47636 b47637 b47638 b47639 b47640 d47625 d47604
        omega
      have d47641 : (x 7 12).toNat = 0 := by
        have r47642 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
        have e47643 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e47644 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b47645 := hb (x 4 3)
        have b47646 := hb (x 5 2)
        have b47647 := hb (x 6 13)
        have b47648 := hb (x 7 12)
        clear * - r47642 e47643 e47644 b47645 b47646 b47647 b47648 d47587
        omega
      have d47649 : (x 5 2).toNat = 0 := by
        have r47650 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
        have e47651 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e47652 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b47653 := hb (x 4 3)
        have b47654 := hb (x 5 2)
        have b47655 := hb (x 6 13)
        have b47656 := hb (x 7 12)
        clear * - r47650 e47651 e47652 b47653 b47654 b47655 b47656 d47641 d47587
        omega
      have d47657 : (x 7 13).toNat = 1 := by
        have r47658 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
        have b47659 := hb (x 5 2)
        have b47660 := hb (x 7 13)
        have b47661 := hb (x 6 1 && x 6 14)
        clear * - r47658 b47659 b47660 b47661 d47530 d47649
        omega
      have d47662 : (x 7 1).toNat = 1 := by
        have r47663 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
        have b47664 := hb (x 7 1)
        have b47665 := hb (x 7 13)
        clear * - r47663 b47664 b47665 d47657
        omega
      have d47666 : (x 8 14).toNat = 0 := by
        have r47667 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
        have b47668 := hb (x 7 1)
        have b47669 := hb (x 8 14)
        clear * - r47667 b47668 b47669 d47662
        omega
      have d47670 : (x 8 1 && x 8 14).toNat = 0 := by
        have r47671 := hand2 (x 8 1) (x 8 14)
        have b47672 := hb (x 8 14)
        have b47673 := hb (x 8 1 && x 8 14)
        clear * - r47671 b47672 b47673 d47666
        omega
      have d47674 : (x 9 13).toNat = 1 := by
        have r47675 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
        have b47676 := hb (x 7 2)
        have b47677 := hb (x 9 13)
        have b47678 := hb (x 8 1 && x 8 14)
        clear * - r47675 b47676 b47677 b47678 d47670 d47633
        omega
      have d47679 : (x 9 1).toNat = 1 := by
        have r47680 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b47681 := hb (x 9 1)
        have b47682 := hb (x 9 13)
        clear * - r47680 b47681 b47682 d47674
        omega
      have d47683 : (x 10 14).toNat = 0 := by
        have r47684 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
        have b47685 := hb (x 9 1)
        have b47686 := hb (x 10 14)
        clear * - r47684 b47685 b47686 d47679
        omega
      have d47687 : (x 10 1 && x 10 14).toNat = 0 := by
        have r47688 := hand2 (x 10 1) (x 10 14)
        have b47689 := hb (x 10 14)
        have b47690 := hb (x 10 1 && x 10 14)
        clear * - r47688 b47689 b47690 d47683
        omega
      have d47691 : (x 11 13).toNat = 1 := by
        have r47692 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
        have b47693 := hb (x 9 2)
        have b47694 := hb (x 11 13)
        have b47695 := hb (x 10 1 && x 10 14)
        clear * - r47692 b47693 b47694 b47695 d47687 d47621
        omega
      have d47696 : (x 11 1).toNat = 1 := by
        have r47697 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
        have b47698 := hb (x 11 1)
        have b47699 := hb (x 11 13)
        clear * - r47697 b47698 b47699 d47691
        omega
      have d47700 : (x 12 14).toNat = 0 := by
        have r47701 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
        have b47702 := hb (x 11 1)
        have b47703 := hb (x 12 14)
        clear * - r47701 b47702 b47703 d47696
        omega
      have d47704 : (x 12 1 && x 12 14).toNat = 0 := by
        have r47705 := hand2 (x 12 1) (x 12 14)
        have b47706 := hb (x 12 14)
        have b47707 := hb (x 12 1 && x 12 14)
        clear * - r47705 b47706 b47707 d47700
        omega
      have d47708 : (x 12 2).toNat = 0 := by
        have r47709 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
        have b47710 := hb (x 12 2)
        have b47711 := hb (x 12 14)
        clear * - r47709 b47710 b47711 d47700
        omega
      have d47712 : (x 12 12).toNat = 0 := by
        have r47713 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e47714 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e47715 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b47716 := hb (x 9 3)
        have b47717 := hb (x 10 2)
        have b47718 := hb (x 11 13)
        have b47719 := hb (x 12 12)
        clear * - r47713 e47714 e47715 b47716 b47717 b47718 b47719 d47691
        omega
      have d47720 : (x 10 2).toNat = 0 := by
        have r47721 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
        have e47722 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e47723 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b47724 := hb (x 9 3)
        have b47725 := hb (x 10 2)
        have b47726 := hb (x 11 13)
        have b47727 := hb (x 12 12)
        clear * - r47721 e47722 e47723 b47724 b47725 b47726 b47727 d47712 d47691
        omega
      have d47728 : (x 10 12).toNat = 0 := by
        have r47729 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
        have e47730 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e47731 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b47732 := hb (x 7 3)
        have b47733 := hb (x 8 2)
        have b47734 := hb (x 9 13)
        have b47735 := hb (x 10 12)
        clear * - r47729 e47730 e47731 b47732 b47733 b47734 b47735 d47674
        omega
      have d47736 : (x 8 2).toNat = 0 := by
        have r47737 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
        have e47738 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e47739 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b47740 := hb (x 7 3)
        have b47741 := hb (x 8 2)
        have b47742 := hb (x 9 13)
        have b47743 := hb (x 10 12)
        clear * - r47737 e47738 e47739 b47740 b47741 b47742 b47743 d47728 d47674
        omega
      have d47744 : (x 10 13).toNat = 1 := by
        have r47745 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
        have b47746 := hb (x 8 2)
        have b47747 := hb (x 10 13)
        have b47748 := hb (x 9 1 && x 9 14)
        clear * - r47745 b47746 b47747 b47748 d47617 d47736
        omega
      have d47749 : (x 10 1).toNat = 1 := by
        have r47750 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
        have b47751 := hb (x 10 1)
        have b47752 := hb (x 10 13)
        clear * - r47750 b47751 b47752 d47744
        omega
      have d47753 : (x 11 14).toNat = 0 := by
        have r47754 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
        have b47755 := hb (x 10 1)
        have b47756 := hb (x 11 14)
        clear * - r47754 b47755 b47756 d47749
        omega
      have d47757 : (x 11 1 && x 11 14).toNat = 0 := by
        have r47758 := hand2 (x 11 1) (x 11 14)
        have b47759 := hb (x 11 14)
        have b47760 := hb (x 11 1 && x 11 14)
        clear * - r47758 b47759 b47760 d47753
        omega
      have d47761 : (x 12 13).toNat = 1 := by
        have r47762 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
        have b47763 := hb (x 10 2)
        have b47764 := hb (x 12 13)
        have b47765 := hb (x 11 1 && x 11 14)
        clear * - r47762 b47763 b47764 b47765 d47757 d47720
        omega
      have d47766 : (x 12 1).toNat = 1 := by
        have r47767 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b47768 := hb (x 12 1)
        have b47769 := hb (x 12 13)
        clear * - r47767 b47768 b47769 d47761
        omega
      have d47770 : (x 13 14).toNat = 0 := by
        have r47771 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
        have b47772 := hb (x 12 1)
        have b47773 := hb (x 13 14)
        clear * - r47771 b47772 b47773 d47766
        omega
      have d47774 : (x 13 1 && x 13 14).toNat = 0 := by
        have r47775 := hand2 (x 13 1) (x 13 14)
        have b47776 := hb (x 13 14)
        have b47777 := hb (x 13 1 && x 13 14)
        clear * - r47775 b47776 b47777 d47770
        omega
      have d47778 : (x 14 13).toNat = 1 := by
        have r47779 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
        have b47780 := hb (x 12 2)
        have b47781 := hb (x 14 13)
        have b47782 := hb (x 13 1 && x 13 14)
        clear * - r47779 b47780 b47781 b47782 d47774 d47708
        omega
      have d47783 : (x 14 1).toNat = 1 := by
        have r47784 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
        have b47785 := hb (x 14 1)
        have b47786 := hb (x 14 13)
        clear * - r47784 b47785 b47786 d47778
        omega
      have d47787 : (x 15 14).toNat = 0 := by
        have r47788 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
        have b47789 := hb (x 14 1)
        have b47790 := hb (x 15 14)
        clear * - r47788 b47789 b47790 d47783
        omega
      have d47791 : (x 15 1 && x 15 14).toNat = 0 := by
        have r47792 := hand2 (x 15 1) (x 15 14)
        have b47793 := hb (x 15 14)
        have b47794 := hb (x 15 1 && x 15 14)
        clear * - r47792 b47793 b47794 d47787
        omega
      have d47795 : (x 15 2).toNat = 0 := by
        have r47796 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b47797 := hb (x 15 2)
        have b47798 := hb (x 15 14)
        clear * - r47796 b47797 b47798 d47787
        omega
      have d47799 : (x 15 2 && x 15 13).toNat = 0 := by
        have r47800 := hand1 (x 15 2) (x 15 13)
        have b47801 := hb (x 15 2)
        have b47802 := hb (x 15 2 && x 15 13)
        clear * - r47800 b47801 b47802 d47795
        omega
      have d47803 : (x 15 12).toNat = 0 := by
        have r47804 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
        have e47805 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e47806 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b47807 := hb (x 12 3)
        have b47808 := hb (x 13 2)
        have b47809 := hb (x 14 13)
        have b47810 := hb (x 15 12)
        clear * - r47804 e47805 e47806 b47807 b47808 b47809 b47810 d47778
        omega
      have d47811 : (x 13 2).toNat = 0 := by
        have r47812 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
        have e47813 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e47814 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b47815 := hb (x 12 3)
        have b47816 := hb (x 13 2)
        have b47817 := hb (x 14 13)
        have b47818 := hb (x 15 12)
        clear * - r47812 e47813 e47814 b47815 b47816 b47817 b47818 d47803 d47778
        omega
      have d47819 : (x 13 12).toNat = 0 := by
        have r47820 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
        have e47821 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e47822 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b47823 := hb (x 10 3)
        have b47824 := hb (x 11 2)
        have b47825 := hb (x 12 13)
        have b47826 := hb (x 13 12)
        clear * - r47820 e47821 e47822 b47823 b47824 b47825 b47826 d47761
        omega
      have d47827 : (x 13 4).toNat = 0 := by
        have r47828 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b47829 := hb (x 13 4)
        have b47830 := hb (x 13 12)
        clear * - r47828 b47829 b47830 d47819
        omega
      have d47831 : (x 11 2).toNat = 0 := by
        have r47832 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
        have e47833 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e47834 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b47835 := hb (x 10 3)
        have b47836 := hb (x 11 2)
        have b47837 := hb (x 12 13)
        have b47838 := hb (x 13 12)
        clear * - r47832 e47833 e47834 b47835 b47836 b47837 b47838 d47819 d47761
        omega
      have d47839 : (x 13 13).toNat = 1 := by
        have r47840 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
        have b47841 := hb (x 11 2)
        have b47842 := hb (x 13 13)
        have b47843 := hb (x 12 1 && x 12 14)
        clear * - r47840 b47841 b47842 b47843 d47704 d47831
        omega
      have d47844 : (x 13 1).toNat = 1 := by
        have r47845 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
        have b47846 := hb (x 13 1)
        have b47847 := hb (x 13 13)
        clear * - r47845 b47846 b47847 d47839
        omega
      have d47848 : (x 14 14).toNat = 0 := by
        have r47849 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
        have b47850 := hb (x 13 1)
        have b47851 := hb (x 14 14)
        clear * - r47849 b47850 b47851 d47844
        omega
      have d47852 : (x 14 1 && x 14 14).toNat = 0 := by
        have r47853 := hand2 (x 14 1) (x 14 14)
        have b47854 := hb (x 14 14)
        have b47855 := hb (x 14 1 && x 14 14)
        clear * - r47853 b47854 b47855 d47848
        omega
      have d47856 : (x 15 13).toNat = 1 := by
        have r47857 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
        have b47858 := hb (x 13 2)
        have b47859 := hb (x 15 13)
        have b47860 := hb (x 14 1 && x 14 14)
        clear * - r47857 b47858 b47859 b47860 d47852 d47811
        omega
      have d47861 : (x 15 1).toNat = 1 := by
        have r47862 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
        have b47863 := hb (x 15 1)
        have b47864 := hb (x 15 13)
        clear * - r47862 b47863 b47864 d47856
        omega
      have d47865 : (x 16 14).toNat = 0 := by
        have r47866 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
        have b47867 := hb (x 15 1)
        have b47868 := hb (x 16 14)
        clear * - r47866 b47867 b47868 d47861
        omega
      have d47869 : (x 16 1 && x 16 14).toNat = 0 := by
        have r47870 := hand2 (x 16 1) (x 16 14)
        have b47871 := hb (x 16 14)
        have b47872 := hb (x 16 1 && x 16 14)
        clear * - r47870 b47871 b47872 d47865
        omega
      have d47873 : (x 17 13).toNat = 1 := by
        have r47874 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
        have b47875 := hb (x 15 2)
        have b47876 := hb (x 17 13)
        have b47877 := hb (x 16 1 && x 16 14)
        clear * - r47874 b47875 b47876 b47877 d47869 d47795
        omega
      have d47878 : (x 17 1).toNat = 1 := by
        have r47879 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
        have b47880 := hb (x 17 1)
        have b47881 := hb (x 17 13)
        clear * - r47879 b47880 b47881 d47873
        omega
      have d47882 : (x 18 14).toNat = 0 := by
        have r47883 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
        have b47884 := hb (x 17 1)
        have b47885 := hb (x 18 14)
        clear * - r47883 b47884 b47885 d47878
        omega
      have d47886 : (x 18 1 && x 18 14).toNat = 0 := by
        have r47887 := hand2 (x 18 1) (x 18 14)
        have b47888 := hb (x 18 14)
        have b47889 := hb (x 18 1 && x 18 14)
        clear * - r47887 b47888 b47889 d47882
        omega
      have d47890 : (x 18 2).toNat = 0 := by
        have r47891 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
        have b47892 := hb (x 18 2)
        have b47893 := hb (x 18 14)
        clear * - r47891 b47892 b47893 d47882
        omega
      have d47894 : (x 18 12).toNat = 0 := by
        have r47895 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
        have e47896 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e47897 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b47898 := hb (x 15 3)
        have b47899 := hb (x 16 2)
        have b47900 := hb (x 17 13)
        have b47901 := hb (x 18 12)
        clear * - r47895 e47896 e47897 b47898 b47899 b47900 b47901 d47873
        omega
      have d47902 : (x 16 2).toNat = 0 := by
        have r47903 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
        have e47904 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e47905 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b47906 := hb (x 15 3)
        have b47907 := hb (x 16 2)
        have b47908 := hb (x 17 13)
        have b47909 := hb (x 18 12)
        clear * - r47903 e47904 e47905 b47906 b47907 b47908 b47909 d47894 d47873
        omega
      have d47910 : (x 16 12).toNat = 0 := by
        have r47911 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e47912 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e47913 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b47914 := hb (x 13 3)
        have b47915 := hb (x 14 2)
        have b47916 := hb (x 15 13)
        have b47917 := hb (x 16 12)
        clear * - r47911 e47912 e47913 b47914 b47915 b47916 b47917 d47856
        omega
      have d47918 : (x 16 1 && x 16 12).toNat = 0 := by
        have r47919 := hand2 (x 16 1) (x 16 12)
        have b47920 := hb (x 16 12)
        have b47921 := hb (x 16 1 && x 16 12)
        clear * - r47919 b47920 b47921 d47910
        omega
      have d47922 : (x 14 2).toNat = 0 := by
        have r47923 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e47924 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e47925 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b47926 := hb (x 13 3)
        have b47927 := hb (x 14 2)
        have b47928 := hb (x 15 13)
        have b47929 := hb (x 16 12)
        clear * - r47923 e47924 e47925 b47926 b47927 b47928 b47929 d47910 d47856
        omega
      have d47930 : (x 16 13).toNat = 1 := by
        have r47931 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
        have b47932 := hb (x 14 2)
        have b47933 := hb (x 16 13)
        have b47934 := hb (x 15 1 && x 15 14)
        clear * - r47931 b47932 b47933 b47934 d47791 d47922
        omega
      have d47935 : (x 16 1).toNat = 1 := by
        have r47936 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
        have b47937 := hb (x 16 1)
        have b47938 := hb (x 16 13)
        clear * - r47936 b47937 b47938 d47930
        omega
      have d47939 : (x 17 14).toNat = 0 := by
        have r47940 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
        have b47941 := hb (x 16 1)
        have b47942 := hb (x 17 14)
        clear * - r47940 b47941 b47942 d47935
        omega
      have d47943 : (x 17 1 && x 17 14).toNat = 0 := by
        have r47944 := hand2 (x 17 1) (x 17 14)
        have b47945 := hb (x 17 14)
        have b47946 := hb (x 17 1 && x 17 14)
        clear * - r47944 b47945 b47946 d47939
        omega
      have d47947 : (x 18 13).toNat = 1 := by
        have r47948 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := hcov13 18
        have b47949 := hb (x 16 2)
        have b47950 := hb (x 18 13)
        have b47951 := hb (x 17 1 && x 17 14)
        clear * - r47948 b47949 b47950 b47951 d47943 d47902
        omega
      have d47952 : (x 19 12).toNat = 0 := by
        have r47953 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
        have e47954 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e47955 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b47956 := hb (x 16 3)
        have b47957 := hb (x 17 2)
        have b47958 := hb (x 18 13)
        have b47959 := hb (x 19 12)
        clear * - r47953 e47954 e47955 b47956 b47957 b47958 b47959 d47947
        omega
      have d47960 : (x 17 2).toNat = 0 := by
        have r47961 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
        have e47962 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e47963 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b47964 := hb (x 16 3)
        have b47965 := hb (x 17 2)
        have b47966 := hb (x 18 13)
        have b47967 := hb (x 19 12)
        clear * - r47961 e47962 e47963 b47964 b47965 b47966 b47967 d47952 d47947
        omega
      have d47968 : (x 19 13).toNat = 1 := by
        have r47969 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
        have b47970 := hb (x 17 2)
        have b47971 := hb (x 19 13)
        have b47972 := hb (x 18 1 && x 18 14)
        clear * - r47969 b47970 b47971 b47972 d47886 d47960
        omega
      have d47973 : (x 20 12).toNat = 0 := by
        have r47974 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e47975 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e47976 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b47977 := hb (x 17 3)
        have b47978 := hb (x 18 2)
        have b47979 := hb (x 19 13)
        have b47980 := hb (x 20 12)
        clear * - r47974 e47975 e47976 b47977 b47978 b47979 b47980 d47968 d47890
        omega
      have d47981 : (x 17 3).toNat = 0 := by
        have r47982 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e47983 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e47984 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b47985 := hb (x 17 3)
        have b47986 := hb (x 18 2)
        have b47987 := hb (x 19 13)
        have b47988 := hb (x 20 12)
        clear * - r47982 e47983 e47984 b47985 b47986 b47987 b47988 d47973 d47968 d47890
        omega
      have d47989 : (x 17 11).toNat = 0 := by
        have r47990 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b47991 := hb (x 17 3)
        have b47992 := hb (x 17 11)
        clear * - r47990 b47991 b47992 d47981
        omega
      have d47993 : (x 17 12).toNat = 0 := by
        have r47994 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
        have e47995 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e47996 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b47997 := hb (x 14 3)
        have b47998 := hb (x 15 2)
        have b47999 := hb (x 16 13)
        have b48000 := hb (x 17 12)
        clear * - r47994 e47995 e47996 b47997 b47998 b47999 b48000 d47930 d47795
        omega
      have d48001 : (x 14 3).toNat = 0 := by
        have r48002 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
        have e48003 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e48004 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b48005 := hb (x 14 3)
        have b48006 := hb (x 15 2)
        have b48007 := hb (x 16 13)
        have b48008 := hb (x 17 12)
        clear * - r48002 e48003 e48004 b48005 b48006 b48007 b48008 d47993 d47930 d47795
        omega
      have d48009 : (x 14 3 && x 14 14).toNat = 0 := by
        have r48010 := hand1 (x 14 3) (x 14 14)
        have b48011 := hb (x 14 3)
        have b48012 := hb (x 14 3 && x 14 14)
        clear * - r48010 b48011 b48012 d48001
        omega
      have r48013 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
      have b48014 := hb (x 13 4)
      have b48015 := hb (x 17 11)
      have b48016 := hb (x 16 1 && x 16 12)
      have b48017 := hb (x 15 2 && x 15 13)
      have b48018 := hb (x 14 3 && x 14 14)
      linarith only [r48013, b48014, b48015, b48016, b48017, b48018, d47989, d47918, d47799, d48009, d47827]
  · have f48019 : (x 0 12).toNat = 1 := by rw [h45506]; rfl
    have d48020 : (x (-1) 13).toNat = 0 := by
      have r48021 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e48022 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e48023 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b48024 := hb (x (-3) 3)
      have b48025 := hb (x (-2) 2)
      have b48026 := hb (x (-1) 13)
      have b48027 := hb (x 0 12)
      clear * - r48021 e48022 e48023 b48024 b48025 b48026 b48027 f48019
      omega
    have d48028 : (x (-2) 2).toNat = 0 := by
      have r48029 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e48030 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e48031 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b48032 := hb (x (-3) 3)
      have b48033 := hb (x (-2) 2)
      have b48034 := hb (x (-1) 13)
      have b48035 := hb (x 0 12)
      clear * - r48029 e48030 e48031 b48032 b48033 b48034 b48035 f48019 d48020
      omega
    have d48036 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r48037 := hand1 (x (-2) 2) (x (-2) 13)
      have b48038 := hb (x (-2) 2)
      have b48039 := hb (x (-2) 2 && x (-2) 13)
      clear * - r48037 b48038 b48039 d48028
      omega
    have d48040 : (x (-3) 3).toNat = 0 := by
      have r48041 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
      have e48042 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e48043 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b48044 := hb (x (-3) 3)
      have b48045 := hb (x (-2) 2)
      have b48046 := hb (x (-1) 13)
      have b48047 := hb (x 0 12)
      clear * - r48041 e48042 e48043 b48044 b48045 b48046 b48047 f48019 d48020 d48028
      omega
    have d48048 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r48049 := hand1 (x (-3) 3) (x (-3) 14)
      have b48050 := hb (x (-3) 3)
      have b48051 := hb (x (-3) 3 && x (-3) 14)
      clear * - r48049 b48050 b48051 d48040
      omega
    have d48052 : (x (-1) 1 && x (-1) 12).toNat = 1 := by
      have r48053 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
      have b48054 := hb (x (-4) 4)
      have b48055 := hb (x 0 11)
      have b48056 := hb (x (-1) 1 && x (-1) 12)
      have b48057 := hb (x (-2) 2 && x (-2) 13)
      have b48058 := hb (x (-3) 3 && x (-3) 14)
      clear * - r48053 b48054 b48055 b48056 b48057 b48058 g9 d48036 d48048 g1
      omega
    have d48059 : (x (-1) 12).toNat = 1 := by
      have r48060 := hand2 (x (-1) 1) (x (-1) 12)
      have b48061 := hb (x (-1) 12)
      have b48062 := hb (x (-1) 1 && x (-1) 12)
      clear * - r48060 b48061 b48062 d48052
      omega
    have d48063 : (x (-2) 13).toNat = 0 := by
      have r48064 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e48065 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e48066 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b48067 := hb (x (-4) 3)
      have b48068 := hb (x (-3) 2)
      have b48069 := hb (x (-2) 13)
      have b48070 := hb (x (-1) 12)
      clear * - r48064 e48065 e48066 b48067 b48068 b48069 b48070 d48059
      omega
    have d48071 : (x (-3) 2).toNat = 0 := by
      have r48072 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
      have e48073 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e48074 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b48075 := hb (x (-4) 3)
      have b48076 := hb (x (-3) 2)
      have b48077 := hb (x (-2) 13)
      have b48078 := hb (x (-1) 12)
      clear * - r48072 e48073 e48074 b48075 b48076 b48077 b48078 d48059 d48063
      omega
    have d48079 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
      have r48080 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
      have b48081 := hb (x (-3) 2)
      have b48082 := hb (x (-1) 13)
      have b48083 := hb (x (-2) 1 && x (-2) 14)
      clear * - r48080 b48081 b48082 b48083 d48020 d48071
      omega
    have d48084 : (x (-2) 1).toNat = 1 := by
      have r48085 := hand1 (x (-2) 1) (x (-2) 14)
      have b48086 := hb (x (-2) 1)
      have b48087 := hb (x (-2) 1 && x (-2) 14)
      clear * - r48085 b48086 b48087 d48079
      omega
    have d48088 : (x (-1) 14).toNat = 0 := by
      have r48089 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
      have b48090 := hb (x (-2) 1)
      have b48091 := hb (x (-1) 14)
      clear * - r48089 b48090 b48091 d48084
      omega
    have d48092 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r48093 := hand2 (x (-1) 1) (x (-1) 14)
      have b48094 := hb (x (-1) 14)
      have b48095 := hb (x (-1) 1 && x (-1) 14)
      clear * - r48093 b48094 b48095 d48088
      omega
    have d48096 : (x 0 13).toNat = 1 := by
      have r48097 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := hcov13 0
      have b48098 := hb (x (-2) 2)
      have b48099 := hb (x 0 13)
      have b48100 := hb (x (-1) 1 && x (-1) 14)
      clear * - r48097 b48098 b48099 b48100 d48092 d48028
      omega
    have d48101 : (x 1 12).toNat = 0 := by
      have r48102 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
      have e48103 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e48104 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b48105 := hb (x (-2) 3)
      have b48106 := hb (x (-1) 2)
      have b48107 := hb (x 0 13)
      have b48108 := hb (x 1 12)
      clear * - r48102 e48103 e48104 b48105 b48106 b48107 b48108 d48096
      omega
    have d48109 : (x (-1) 2).toNat = 0 := by
      have r48110 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
      have e48111 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e48112 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b48113 := hb (x (-2) 3)
      have b48114 := hb (x (-1) 2)
      have b48115 := hb (x 0 13)
      have b48116 := hb (x 1 12)
      clear * - r48110 e48111 e48112 b48113 b48114 b48115 b48116 d48101 d48096
      omega
    have d48117 : (x 1 13).toNat = 1 := by
      have r48118 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
      have b48119 := hb (x (-1) 2)
      have b48120 := hb (x 1 13)
      have b48121 := hb (x 0 1 && x 0 14)
      clear * - r48118 b48119 b48120 b48121 g32 d48109
      omega
    have d48122 : (x 1 1).toNat = 1 := by
      have r48123 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b48124 := hb (x 1 1)
      have b48125 := hb (x 1 13)
      clear * - r48123 b48124 b48125 d48117
      omega
    have d48126 : (x 2 14).toNat = 0 := by
      have r48127 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
      have b48128 := hb (x 1 1)
      have b48129 := hb (x 2 14)
      clear * - r48127 b48128 b48129 d48122
      omega
    have d48130 : (x 2 1 && x 2 14).toNat = 0 := by
      have r48131 := hand2 (x 2 1) (x 2 14)
      have b48132 := hb (x 2 14)
      have b48133 := hb (x 2 1 && x 2 14)
      clear * - r48131 b48132 b48133 d48126
      omega
    have d48134 : (x 3 13).toNat = 1 := by
      have r48135 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
      have b48136 := hb (x 1 2)
      have b48137 := hb (x 3 13)
      have b48138 := hb (x 2 1 && x 2 14)
      clear * - r48135 b48136 b48137 b48138 d48130 g10
      omega
    have d48139 : (x 3 1).toNat = 1 := by
      have r48140 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b48141 := hb (x 3 1)
      have b48142 := hb (x 3 13)
      clear * - r48140 b48141 b48142 d48134
      omega
    have d48143 : (x 4 14).toNat = 0 := by
      have r48144 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
      have b48145 := hb (x 3 1)
      have b48146 := hb (x 4 14)
      clear * - r48144 b48145 b48146 d48139
      omega
    have d48147 : (x 4 1 && x 4 14).toNat = 0 := by
      have r48148 := hand2 (x 4 1) (x 4 14)
      have b48149 := hb (x 4 14)
      have b48150 := hb (x 4 1 && x 4 14)
      clear * - r48148 b48149 b48150 d48143
      omega
    have d48151 : (x 5 13).toNat = 1 := by
      have r48152 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
      have b48153 := hb (x 3 2)
      have b48154 := hb (x 5 13)
      have b48155 := hb (x 4 1 && x 4 14)
      clear * - r48152 b48153 b48154 b48155 d48147 g14
      omega
    have d48156 : (x 6 12).toNat = 0 := by
      have r48157 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e48158 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e48159 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b48160 := hb (x 3 3)
      have b48161 := hb (x 4 2)
      have b48162 := hb (x 5 13)
      have b48163 := hb (x 6 12)
      clear * - r48157 e48158 e48159 b48160 b48161 b48162 b48163 d48151
      omega
    have d48164 : (x 4 2).toNat = 0 := by
      have r48165 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e48166 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e48167 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b48168 := hb (x 3 3)
      have b48169 := hb (x 4 2)
      have b48170 := hb (x 5 13)
      have b48171 := hb (x 6 12)
      clear * - r48165 e48166 e48167 b48168 b48169 b48170 b48171 d48156 d48151
      omega
    have d48172 : (x 4 12).toNat = 0 := by
      have r48173 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e48174 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e48175 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b48176 := hb (x 1 3)
      have b48177 := hb (x 2 2)
      have b48178 := hb (x 3 13)
      have b48179 := hb (x 4 12)
      clear * - r48173 e48174 e48175 b48176 b48177 b48178 b48179 d48134
      omega
    have d48180 : (x 2 2).toNat = 0 := by
      have r48181 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e48182 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e48183 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b48184 := hb (x 1 3)
      have b48185 := hb (x 2 2)
      have b48186 := hb (x 3 13)
      have b48187 := hb (x 4 12)
      clear * - r48181 e48182 e48183 b48184 b48185 b48186 b48187 d48172 d48134
      omega
    have d48188 : (x 2 2 && x 2 13).toNat = 0 := by
      have r48189 := hand1 (x 2 2) (x 2 13)
      have b48190 := hb (x 2 2)
      have b48191 := hb (x 2 2 && x 2 13)
      clear * - r48189 b48190 b48191 d48180
      omega
    have d48192 : (x 4 11).toNat = 1 := by
      have r48193 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
      have b48194 := hb (x 0 4)
      have b48195 := hb (x 4 11)
      have b48196 := hb (x 3 1 && x 3 12)
      have b48197 := hb (x 2 2 && x 2 13)
      have b48198 := hb (x 1 3 && x 1 14)
      clear * - r48193 b48194 b48195 b48196 b48197 b48198 g28 d48188 g29 g4
      omega
    have d48199 : (x 4 3).toNat = 1 := by
      have r48200 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b48201 := hb (x 4 3)
      have b48202 := hb (x 4 11)
      clear * - r48200 b48201 b48202 d48192
      omega
    have d48203 : (x 7 12).toNat = 0 := by
      have r48204 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e48205 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e48206 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b48207 := hb (x 4 3)
      have b48208 := hb (x 5 2)
      have b48209 := hb (x 6 13)
      have b48210 := hb (x 7 12)
      clear * - r48204 e48205 e48206 b48207 b48208 b48209 b48210 d48199
      omega
    have d48211 : (x 6 13).toNat = 0 := by
      have r48212 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e48213 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e48214 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b48215 := hb (x 4 3)
      have b48216 := hb (x 5 2)
      have b48217 := hb (x 6 13)
      have b48218 := hb (x 7 12)
      clear * - r48212 e48213 e48214 b48215 b48216 b48217 b48218 d48203 d48199
      omega
    have d48219 : (x 5 1 && x 5 14).toNat = 1 := by
      have r48220 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
      have b48221 := hb (x 4 2)
      have b48222 := hb (x 6 13)
      have b48223 := hb (x 5 1 && x 5 14)
      clear * - r48220 b48221 b48222 b48223 d48211 d48164
      omega
    have d48224 : (x 5 14).toNat = 1 := by
      have r48225 := hand2 (x 5 1) (x 5 14)
      have b48226 := hb (x 5 14)
      have b48227 := hb (x 5 1 && x 5 14)
      clear * - r48225 b48226 b48227 d48219
      omega
    have d48228 : (x 4 1).toNat = 0 := by
      have r48229 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
      have b48230 := hb (x 4 1)
      have b48231 := hb (x 5 14)
      clear * - r48229 b48230 b48231 d48224
      omega
    have d48232 : (x 4 13).toNat = 0 := by
      have r48233 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b48234 := hb (x 4 1)
      have b48235 := hb (x 4 13)
      clear * - r48233 b48234 b48235 d48228
      omega
    have r48236 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b48237 := hb (x 2 2)
    have b48238 := hb (x 4 13)
    have b48239 := hb (x 3 1 && x 3 14)
    linarith only [r48236, b48237, b48238, b48239, d48232, g33, d48180]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 5).toNat = 0)
    (g1 : (x (-4) 4).toNat = 0)
    (g2 : (x 0 2).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 4).toNat = 0)
    (g5 : (x 0 6).toNat = 0)
    (g6 : (x 0 7).toNat = 0)
    (g7 : (x 0 9).toNat = 1)
    (g8 : (x 0 10).toNat = 0)
    (g9 : (x 0 11).toNat = 0)
    (g10 : (x 1 2).toNat = 0)
    (g11 : (x 1 6).toNat = 0)
    (g12 : (x 1 10).toNat = 0)
    (g13 : (x 2 1).toNat = 1)
    (g14 : (x 3 2).toNat = 0)
    (g15 : (x 3 4).toNat = 0)
    (g16 : (x 1 2 && x 1 6).toNat = 0)
    (g17 : (x 0 3 && x 0 7).toNat = 0)
    (g18 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g19 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g20 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g21 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g22 : (x 3 3 && x 3 12).toNat = 0)
    (g23 : (x 1 5 && x 1 14).toNat = 0)
    (g24 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g25 : (x 0 1 && x 0 11).toNat = 0)
    (g26 : (x 1 2 && x 1 13).toNat = 0)
    (g27 : (x 0 3 && x 0 14).toNat = 0)
    (g28 : (x 3 1 && x 3 12).toNat = 0)
    (g29 : (x 1 3 && x 1 14).toNat = 0)
    (g30 : (x 3 2 && x 3 13).toNat = 0)
    (g31 : (x 3 3 && x 3 14).toNat = 0)
    (g32 : (x 0 1 && x 0 14).toNat = 0)
    (g33 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a01001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33
