import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000111

Topic: combinatorics   Node: d7e70352dadc

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 70 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000111_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 7).toNat = 0)
    (g1 : (x (-5) 6).toNat = 0)
    (g2 : (x (-4) 5).toNat = 0)
    (g3 : (x (-3) 4).toNat = 0)
    (g4 : (x (-3) 5).toNat = 0)
    (g5 : (x (-2) 3).toNat = 0)
    (g6 : (x (-2) 4).toNat = 0)
    (g7 : (x (-1) 2).toNat = 1)
    (g8 : (x 0 1).toNat = 1)
    (g9 : (x 0 4).toNat = 0)
    (g10 : (x 0 6).toNat = 0)
    (g11 : (x 0 7).toNat = 0)
    (g12 : (x 0 8).toNat = 0)
    (g13 : (x 0 10).toNat = 0)
    (g14 : (x 0 12).toNat = 0)
    (g15 : (x 0 14).toNat = 0)
    (g16 : (x 1 3).toNat = 0)
    (g17 : (x 1 5).toNat = 0)
    (g18 : (x 1 6).toNat = 0)
    (g19 : (x 1 11).toNat = 0)
    (g20 : (x 1 13).toNat = 0)
    (g21 : (x 1 14).toNat = 0)
    (g22 : (x 2 4).toNat = 0)
    (g23 : (x 2 10).toNat = 0)
    (g24 : (x 2 12).toNat = 0)
    (g25 : (x 2 13).toNat = 1)
    (g26 : (x 2 14).toNat = 1)
    (g27 : (x 3 2).toNat = 0)
    (g28 : (x 3 4).toNat = 0)
    (g29 : (x 3 12).toNat = 0)
    (g30 : (x 2 12 && x 2 14).toNat = 0)
    (g31 : (x 4 8 && x 4 11).toNat = 0)
    (g32 : (x 3 9 && x 3 12).toNat = 0)
    (g33 : (x 2 10 && x 2 13).toNat = 0)
    (g34 : (x 1 11 && x 1 14).toNat = 0)
    (g35 : (x (-4) 2 && x (-4) 6).toNat = 0)
    (g36 : (x (-5) 3 && x (-5) 7).toNat = 0)
    (g37 : (x 4 8 && x 4 12).toNat = 0)
    (g38 : (x 3 9 && x 3 13).toNat = 0)
    (g39 : (x 0 1 && x 0 6).toNat = 0)
    (g40 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g41 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g42 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g43 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g44 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g45 : (x 3 7 && x 3 12).toNat = 0)
    (g46 : (x 2 8 && x 2 13).toNat = 0)
    (g47 : (x 1 9 && x 1 14).toNat = 0)
    (g48 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g49 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g50 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g51 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g52 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g53 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g54 : (x (-2) 1 && x (-2) 8).toNat = 0)
    (g55 : (x (-3) 2 && x (-3) 9).toNat = 0)
    (g56 : (x (-4) 3 && x (-4) 10).toNat = 0)
    (g57 : (x (-5) 4 && x (-5) 11).toNat = 0)
    (g58 : (x (-6) 5 && x (-6) 12).toNat = 0)
    (g59 : (x (-7) 6 && x (-7) 13).toNat = 0)
    (g60 : (x (-8) 7 && x (-8) 14).toNat = 0)
    (g61 : (x 3 5 && x 3 12).toNat = 0)
    (g62 : (x 1 7 && x 1 14).toNat = 0)
    (g63 : (x 3 3 && x 3 12).toNat = 0)
    (g64 : (x 2 4 && x 2 13).toNat = 0)
    (g65 : (x 1 5 && x 1 14).toNat = 0)
    (g66 : (x 2 4 && x 2 14).toNat = 0)
    (g67 : (x 3 1 && x 3 12).toNat = 0)
    (g68 : (x 1 3 && x 1 14).toNat = 0)
    (g69 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h38439 : x (-1) 7
  · have f38440 : (x (-1) 7).toNat = 0 := by rw [h38439]; rfl
    have d38441 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
      have r38442 := hand2 (x (-1) 1) (x (-1) 7)
      have b38443 := hb (x (-1) 7)
      have b38444 := hb (x (-1) 1 && x (-1) 7)
      clear * - r38442 b38443 b38444 f38440
      omega
    have d38445 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
      have r38446 := hand2 (x (-1) 2) (x (-1) 7)
      have b38447 := hb (x (-1) 7)
      have b38448 := hb (x (-1) 2 && x (-1) 7)
      clear * - r38446 b38447 b38448 f38440
      omega
    have d38449 : (x (-9) 8).toNat = 1 := by
      have r38450 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := hcov7 (-1)
      have b38451 := hb (x (-9) 8)
      have b38452 := hb (x (-1) 7)
      have b38453 := hb (x (-2) 1 && x (-2) 8)
      have b38454 := hb (x (-3) 2 && x (-3) 9)
      have b38455 := hb (x (-4) 3 && x (-4) 10)
      have b38456 := hb (x (-5) 4 && x (-5) 11)
      have b38457 := hb (x (-6) 5 && x (-6) 12)
      have b38458 := hb (x (-7) 6 && x (-7) 13)
      have b38459 := hb (x (-8) 7 && x (-8) 14)
      clear * - r38450 b38451 b38452 b38453 b38454 b38455 b38456 b38457 b38458 b38459 f38440 g54 g55 g56 g57 g58 g59 g60
      omega
    have d38460 : (x (-10) 9).toNat = 0 := by
      have r38461 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := hd8 (-9)
      have e38462 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e38463 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e38464 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e38465 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e38466 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e38467 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b38468 := hb (x (-16) 7)
      have b38469 := hb (x (-15) 6)
      have b38470 := hb (x (-14) 5)
      have b38471 := hb (x (-13) 4)
      have b38472 := hb (x (-12) 11)
      have b38473 := hb (x (-11) 10)
      have b38474 := hb (x (-10) 9)
      have b38475 := hb (x (-9) 8)
      clear * - r38461 e38462 e38463 e38464 e38465 e38466 e38467 b38468 b38469 b38470 b38471 b38472 b38473 b38474 b38475 d38449
      omega
    have d38476 : (x (-11) 10).toNat = 0 := by
      have r38477 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := hd8 (-9)
      have e38478 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e38479 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e38480 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e38481 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e38482 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e38483 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b38484 := hb (x (-16) 7)
      have b38485 := hb (x (-15) 6)
      have b38486 := hb (x (-14) 5)
      have b38487 := hb (x (-13) 4)
      have b38488 := hb (x (-12) 11)
      have b38489 := hb (x (-11) 10)
      have b38490 := hb (x (-10) 9)
      have b38491 := hb (x (-9) 8)
      clear * - r38477 e38478 e38479 e38480 e38481 e38482 e38483 b38484 b38485 b38486 b38487 b38488 b38489 b38490 b38491 d38449 d38460
      omega
    have d38492 : (x (-12) 11).toNat = 0 := by
      have r38493 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := hd8 (-9)
      have e38494 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e38495 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e38496 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e38497 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e38498 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e38499 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b38500 := hb (x (-16) 7)
      have b38501 := hb (x (-15) 6)
      have b38502 := hb (x (-14) 5)
      have b38503 := hb (x (-13) 4)
      have b38504 := hb (x (-12) 11)
      have b38505 := hb (x (-11) 10)
      have b38506 := hb (x (-10) 9)
      have b38507 := hb (x (-9) 8)
      clear * - r38493 e38494 e38495 e38496 e38497 e38498 e38499 b38500 b38501 b38502 b38503 b38504 b38505 b38506 b38507 d38449 d38460 d38476
      omega
    have d38508 : (x (-13) 4).toNat = 0 := by
      have r38509 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := hd8 (-9)
      have e38510 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e38511 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e38512 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e38513 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e38514 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e38515 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b38516 := hb (x (-16) 7)
      have b38517 := hb (x (-15) 6)
      have b38518 := hb (x (-14) 5)
      have b38519 := hb (x (-13) 4)
      have b38520 := hb (x (-12) 11)
      have b38521 := hb (x (-11) 10)
      have b38522 := hb (x (-10) 9)
      have b38523 := hb (x (-9) 8)
      clear * - r38509 e38510 e38511 e38512 e38513 e38514 e38515 b38516 b38517 b38518 b38519 b38520 b38521 b38522 b38523 d38449 d38460 d38476 d38492
      omega
    have d38524 : (x (-13) 4 && x (-13) 13).toNat = 0 := by
      have r38525 := hand1 (x (-13) 4) (x (-13) 13)
      have b38526 := hb (x (-13) 4)
      have b38527 := hb (x (-13) 4 && x (-13) 13)
      clear * - r38525 b38526 b38527 d38508
      omega
    have d38528 : (x (-14) 5).toNat = 0 := by
      have r38529 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := hd8 (-9)
      have e38530 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e38531 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e38532 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e38533 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e38534 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e38535 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b38536 := hb (x (-16) 7)
      have b38537 := hb (x (-15) 6)
      have b38538 := hb (x (-14) 5)
      have b38539 := hb (x (-13) 4)
      have b38540 := hb (x (-12) 11)
      have b38541 := hb (x (-11) 10)
      have b38542 := hb (x (-10) 9)
      have b38543 := hb (x (-9) 8)
      clear * - r38529 e38530 e38531 e38532 e38533 e38534 e38535 b38536 b38537 b38538 b38539 b38540 b38541 b38542 b38543 d38449 d38460 d38476 d38492 d38508
      omega
    have d38544 : (x (-14) 5 && x (-14) 14).toNat = 0 := by
      have r38545 := hand1 (x (-14) 5) (x (-14) 14)
      have b38546 := hb (x (-14) 5)
      have b38547 := hb (x (-14) 5 && x (-14) 14)
      clear * - r38545 b38546 b38547 d38528
      omega
    have d38548 : (x (-15) 6).toNat = 0 := by
      have r38549 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := hd8 (-9)
      have e38550 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e38551 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e38552 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e38553 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e38554 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e38555 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b38556 := hb (x (-16) 7)
      have b38557 := hb (x (-15) 6)
      have b38558 := hb (x (-14) 5)
      have b38559 := hb (x (-13) 4)
      have b38560 := hb (x (-12) 11)
      have b38561 := hb (x (-11) 10)
      have b38562 := hb (x (-10) 9)
      have b38563 := hb (x (-9) 8)
      clear * - r38549 e38550 e38551 e38552 e38553 e38554 e38555 b38556 b38557 b38558 b38559 b38560 b38561 b38562 b38563 d38449 d38460 d38476 d38492 d38508 d38528
      omega
    cases h38564 : x 1 7
    · have f38565 : (x 1 7).toNat = 0 := by rw [h38564]; rfl
      cases h38566 : x 2 2
      · have f38567 : (x 2 2).toNat = 0 := by rw [h38566]; rfl
        have d38568 : (x 2 2 && x 2 13).toNat = 0 := by
          have r38569 := hand1 (x 2 2) (x 2 13)
          have b38570 := hb (x 2 2)
          have b38571 := hb (x 2 2 && x 2 13)
          clear * - r38569 b38570 b38571 f38567
          omega
        have d38572 : (x 4 13).toNat = 1 := by
          have r38573 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
          have b38574 := hb (x 2 2)
          have b38575 := hb (x 4 13)
          have b38576 := hb (x 3 1 && x 3 14)
          clear * - r38573 b38574 b38575 b38576 g69 f38567
          omega
        have d38577 : (x 4 1).toNat = 1 := by
          have r38578 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b38579 := hb (x 4 1)
          have b38580 := hb (x 4 13)
          clear * - r38578 b38579 b38580 d38572
          omega
        have d38581 : (x 5 14).toNat = 0 := by
          have r38582 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
          have b38583 := hb (x 4 1)
          have b38584 := hb (x 5 14)
          clear * - r38582 b38583 b38584 d38577
          omega
        have d38585 : (x 5 1 && x 5 14).toNat = 0 := by
          have r38586 := hand2 (x 5 1) (x 5 14)
          have b38587 := hb (x 5 14)
          have b38588 := hb (x 5 1 && x 5 14)
          clear * - r38586 b38587 b38588 d38581
          omega
        have d38589 : (x 5 2).toNat = 0 := by
          have r38590 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b38591 := hb (x 5 2)
          have b38592 := hb (x 5 14)
          clear * - r38590 b38591 b38592 d38581
          omega
        have d38593 : (x 5 10).toNat = 0 := by
          have r38594 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
          have b38595 := hb (x 5 2)
          have b38596 := hb (x 5 10)
          clear * - r38594 b38595 b38596 d38589
          omega
        have d38597 : (x 5 7 && x 5 10).toNat = 0 := by
          have r38598 := hand2 (x 5 7) (x 5 10)
          have b38599 := hb (x 5 10)
          have b38600 := hb (x 5 7 && x 5 10)
          clear * - r38598 b38599 b38600 d38593
          omega
        have d38601 : (x 4 11).toNat = 1 := by
          have r38602 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
          have b38603 := hb (x 0 4)
          have b38604 := hb (x 4 11)
          have b38605 := hb (x 3 1 && x 3 12)
          have b38606 := hb (x 2 2 && x 2 13)
          have b38607 := hb (x 1 3 && x 1 14)
          clear * - r38602 b38603 b38604 b38605 b38606 b38607 g67 d38568 g68 g9
          omega
        have d38608 : (x 4 3).toNat = 1 := by
          have r38609 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
          have b38610 := hb (x 4 3)
          have b38611 := hb (x 4 11)
          clear * - r38609 b38610 b38611 d38601
          omega
        have d38612 : (x 7 12).toNat = 0 := by
          have r38613 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
          have e38614 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e38615 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b38616 := hb (x 4 3)
          have b38617 := hb (x 5 2)
          have b38618 := hb (x 6 13)
          have b38619 := hb (x 7 12)
          clear * - r38613 e38614 e38615 b38616 b38617 b38618 b38619 d38589 d38608
          omega
        have d38620 : (x 6 13).toNat = 0 := by
          have r38621 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
          have e38622 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e38623 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b38624 := hb (x 4 3)
          have b38625 := hb (x 5 2)
          have b38626 := hb (x 6 13)
          have b38627 := hb (x 7 12)
          clear * - r38621 e38622 e38623 b38624 b38625 b38626 b38627 d38612 d38589 d38608
          omega
        have d38628 : (x 4 2).toNat = 1 := by
          have r38629 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
          have b38630 := hb (x 4 2)
          have b38631 := hb (x 6 13)
          have b38632 := hb (x 5 1 && x 5 14)
          clear * - r38629 b38630 b38631 b38632 d38620 d38585
          omega
        have d38633 : (x 4 14).toNat = 1 := by
          have r38634 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b38635 := hb (x 4 2)
          have b38636 := hb (x 4 14)
          clear * - r38634 b38635 b38636 d38628
          omega
        have d38637 : (x 3 1).toNat = 0 := by
          have r38638 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
          have b38639 := hb (x 3 1)
          have b38640 := hb (x 4 14)
          clear * - r38638 b38639 b38640 d38633
          omega
        have d38641 : (x 3 13).toNat = 0 := by
          have r38642 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b38643 := hb (x 3 1)
          have b38644 := hb (x 3 13)
          clear * - r38642 b38643 b38644 d38637
          omega
        have d38645 : (x 4 12).toNat = 1 := by
          have r38646 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e38647 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e38648 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b38649 := hb (x 1 3)
          have b38650 := hb (x 2 2)
          have b38651 := hb (x 3 13)
          have b38652 := hb (x 4 12)
          clear * - r38646 e38647 e38648 b38649 b38650 b38651 b38652 d38641 f38567 g16
          omega
        have d38653 : (x 7 8).toNat = 0 := by
          have r38654 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
          have e38655 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e38656 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e38657 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e38658 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e38659 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e38660 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b38661 := hb (x 0 7)
          have b38662 := hb (x 1 6)
          have b38663 := hb (x 2 5)
          have b38664 := hb (x 3 4)
          have b38665 := hb (x 4 11)
          have b38666 := hb (x 5 10)
          have b38667 := hb (x 6 9)
          have b38668 := hb (x 7 8)
          clear * - r38654 e38655 e38656 e38657 e38658 e38659 e38660 b38661 b38662 b38663 b38664 b38665 b38666 b38667 b38668 d38593 d38601 g28 g18 g11
          omega
        have d38669 : (x 7 5 && x 7 8).toNat = 0 := by
          have r38670 := hand2 (x 7 5) (x 7 8)
          have b38671 := hb (x 7 8)
          have b38672 := hb (x 7 5 && x 7 8)
          clear * - r38670 b38671 b38672 d38653
          omega
        have d38673 : (x 6 9).toNat = 0 := by
          have r38674 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
          have e38675 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e38676 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e38677 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e38678 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e38679 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e38680 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b38681 := hb (x 0 7)
          have b38682 := hb (x 1 6)
          have b38683 := hb (x 2 5)
          have b38684 := hb (x 3 4)
          have b38685 := hb (x 4 11)
          have b38686 := hb (x 5 10)
          have b38687 := hb (x 6 9)
          have b38688 := hb (x 7 8)
          clear * - r38674 e38675 e38676 e38677 e38678 e38679 e38680 b38681 b38682 b38683 b38684 b38685 b38686 b38687 b38688 d38653 d38593 d38601 g28 g18 g11
          omega
        have d38689 : (x 6 6 && x 6 9).toNat = 0 := by
          have r38690 := hand2 (x 6 6) (x 6 9)
          have b38691 := hb (x 6 9)
          have b38692 := hb (x 6 6 && x 6 9)
          clear * - r38690 b38691 b38692 d38673
          omega
        have r38693 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
        have r38694 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := hcount 16
        have r38695 : 1 ≤ (x 12 3).toNat + (x 11 1 && x 11 4).toNat + (x 10 2 && x 10 5).toNat + (x 9 3 && x 9 6).toNat + (x 8 4 && x 8 7).toNat + (x 7 5 && x 7 8).toNat + (x 6 6 && x 6 9).toNat + (x 5 7 && x 5 10).toNat + (x 4 8 && x 4 11).toNat + (x 3 9 && x 3 12).toNat + (x 2 10 && x 2 13).toNat + (x 1 11 && x 1 14).toNat + (x 0 12).toNat := hcov3 12
        have r38696 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := hcov4 12
        have e38697 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
        have e38698 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
        have r38699 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
        have r38700 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
        have r38701 := hand2 (x 11 1) (x 11 4)
        have r38702 := hand2 (x 10 2) (x 10 5)
        have r38703 := hand2 (x 9 3) (x 9 6)
        have r38704 := hand2 (x 8 4) (x 8 7)
        have r38705 := hand2 (x 10 2) (x 10 6)
        have r38706 := hand2 (x 9 3) (x 9 7)
        have r38707 := hand2 (x 8 4) (x 8 8)
        have r38708 := hand2 (x 7 5) (x 7 9)
        have r38709 := hand2 (x 6 6) (x 6 10)
        have r38710 := hand2 (x 5 7) (x 5 11)
        have r38711 := hand1 (x 14 1) (x 14 14)
        have b38712 := hb (x 0 12)
        have b38713 := hb (x 1 11)
        have b38714 := hb (x 1 14)
        have b38715 := hb (x 2 10)
        have b38716 := hb (x 2 13)
        have b38717 := hb (x 2 14)
        have b38718 := hb (x 3 12)
        have b38719 := hb (x 3 13)
        have b38720 := hb (x 4 11)
        have b38721 := hb (x 4 12)
        have b38722 := hb (x 5 10)
        have b38723 := hb (x 5 11)
        have b38724 := hb (x 6 9)
        have b38725 := hb (x 6 10)
        have b38726 := hb (x 7 8)
        have b38727 := hb (x 7 9)
        have b38728 := hb (x 8 7)
        have b38729 := hb (x 8 8)
        have b38730 := hb (x 9 6)
        have b38731 := hb (x 9 7)
        have b38732 := hb (x 10 5)
        have b38733 := hb (x 10 6)
        have b38734 := hb (x 11 4)
        have b38735 := hb (x 11 5)
        have b38736 := hb (x 12 3)
        have b38737 := hb (x 12 4)
        have b38738 := hb (x 13 2)
        have b38739 := hb (x 13 3)
        have b38740 := hb (x 14 1)
        have b38741 := hb (x 14 2)
        have b38742 := hb (x 15 1)
        have b38743 := hb (x 15 13)
        have b38744 := hb (x 11 1 && x 11 4)
        have b38745 := hb (x 10 2 && x 10 5)
        have b38746 := hb (x 9 3 && x 9 6)
        have b38747 := hb (x 8 4 && x 8 7)
        have b38748 := hb (x 7 5 && x 7 8)
        have b38749 := hb (x 6 6 && x 6 9)
        have b38750 := hb (x 5 7 && x 5 10)
        have b38751 := hb (x 4 8 && x 4 11)
        have b38752 := hb (x 3 9 && x 3 12)
        have b38753 := hb (x 2 10 && x 2 13)
        have b38754 := hb (x 1 11 && x 1 14)
        have b38755 := hb (x 10 2 && x 10 6)
        have b38756 := hb (x 9 3 && x 9 7)
        have b38757 := hb (x 8 4 && x 8 8)
        have b38758 := hb (x 7 5 && x 7 9)
        have b38759 := hb (x 6 6 && x 6 10)
        have b38760 := hb (x 5 7 && x 5 11)
        have b38761 := hb (x 4 8 && x 4 12)
        have b38762 := hb (x 3 9 && x 3 13)
        have b38763 := hb (x 14 1 && x 14 14)
        linarith only [r38693, r38694, r38695, r38696, e38697, e38698, r38699, r38700, r38701, r38702, r38703, r38704, r38705, r38706, r38707, r38708, r38709, r38710, r38711, b38712, b38713, b38714, b38715, b38716, b38717, b38718, b38719, b38720, b38721, b38722, b38723, b38724, b38725, b38726, b38727, b38728, b38729, b38730, b38731, b38732, b38733, b38734, b38735, b38736, b38737, b38738, b38739, b38740, b38741, b38742, b38743, b38744, b38745, b38746, b38747, b38748, b38749, b38750, b38751, b38752, b38753, b38754, b38755, b38756, b38757, b38758, b38759, b38760, b38761, b38762, b38763, g14, g19, g21, g23, g25, g26, g29, d38641, d38601, d38645, d38593, d38673, d38653, d38669, d38689, d38597, g31, g32, g33, g34, g37, g38]
      · have f38764 : (x 2 2).toNat = 1 := by rw [h38566]; rfl
        have d38765 : (x 4 12).toNat = 0 := by
          have r38766 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e38767 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e38768 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b38769 := hb (x 1 3)
          have b38770 := hb (x 2 2)
          have b38771 := hb (x 3 13)
          have b38772 := hb (x 4 12)
          clear * - r38766 e38767 e38768 b38769 b38770 b38771 b38772 f38764 g16
          omega
        have d38773 : (x 4 2 && x 4 12).toNat = 0 := by
          have r38774 := hand2 (x 4 2) (x 4 12)
          have b38775 := hb (x 4 12)
          have b38776 := hb (x 4 2 && x 4 12)
          clear * - r38774 b38775 b38776 d38765
          omega
        have d38777 : (x 3 13).toNat = 0 := by
          have r38778 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e38779 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e38780 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b38781 := hb (x 1 3)
          have b38782 := hb (x 2 2)
          have b38783 := hb (x 3 13)
          have b38784 := hb (x 4 12)
          clear * - r38778 e38779 e38780 b38781 b38782 b38783 b38784 d38765 f38764 g16
          omega
        have d38785 : (x 3 3 && x 3 13).toNat = 0 := by
          have r38786 := hand2 (x 3 3) (x 3 13)
          have b38787 := hb (x 3 13)
          have b38788 := hb (x 3 3 && x 3 13)
          clear * - r38786 b38787 b38788 d38777
          omega
        have r38789 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
        have r38790 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := hcount 6
        have r38791 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := hd8 (-10)
        have e38792 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
        have e38793 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
        have e38794 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
        have e38795 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
        have e38796 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
        have e38797 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
        have r38798 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
        have e38799 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e38800 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e38801 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e38802 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e38803 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e38804 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have r38805 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := hd8 (-2)
        have e38806 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e38807 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e38808 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e38809 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e38810 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e38811 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have r38812 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := hd12 (-12)
        have e38813 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
        have e38814 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
        have r38815 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := hd12 (-6)
        have e38816 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e38817 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have r38818 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
        have e38819 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e38820 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have r38821 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
        have e38822 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e38823 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have r38824 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := hd14 (-8)
        have r38825 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
        have r38826 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
        have r38827 : 1 ≤ (x (-2) 4).toNat + (x (-3) 1 && x (-3) 5).toNat + (x (-4) 2 && x (-4) 6).toNat + (x (-5) 3 && x (-5) 7).toNat + (x (-6) 4 && x (-6) 8).toNat + (x (-7) 5 && x (-7) 9).toNat + (x (-8) 6 && x (-8) 10).toNat + (x (-9) 7 && x (-9) 11).toNat + (x (-10) 8 && x (-10) 12).toNat + (x (-11) 9 && x (-11) 13).toNat + (x (-12) 10 && x (-12) 14).toNat + (x (-13) 11).toNat := hcov4 (-2)
        have e38828 : (x (-3) 1 && x (-3) 5).toNat = (x (-3) 5).toNat := handr _ _ (fun h => hp13 (-3) (hp5 (-3) (h)))
        have e38829 : (x (-12) 10 && x (-12) 14).toNat = (x (-12) 10).toNat := handl _ _ (fun h => hp2 (-12) (hp10 (-12) (h)))
        have r38830 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := hcov5 1
        have r38831 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := hcov6 0
        have r38832 : 1 ≤ (x (-9) 9).toNat + (x (-10) 1 && x (-10) 10).toNat + (x (-11) 2 && x (-11) 11).toNat + (x (-12) 3 && x (-12) 12).toNat + (x (-13) 4 && x (-13) 13).toNat + (x (-14) 5 && x (-14) 14).toNat + (x (-15) 6).toNat := hcov9 (-9)
        have r38833 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
        have r38834 : 1 ≤ (x (-10) 11).toNat + (x (-11) 1 && x (-11) 12).toNat + (x (-12) 2 && x (-12) 13).toNat + (x (-13) 3 && x (-13) 14).toNat + (x (-14) 4).toNat := hcov11 (-10)
        have r38835 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := hcov13 (-12)
        have r38836 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
        have r38837 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
        have r38838 : (x (-9) 9).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp9 (-9))
        have r38839 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have r38840 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have r38841 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
        have r38842 := hand1 (x (-6) 4) (x (-6) 8)
        have r38843 := hand1 (x (-7) 5) (x (-7) 9)
        have r38844 := hand1 (x (-8) 6) (x (-8) 10)
        have r38845 := hand1 (x (-9) 7) (x (-9) 11)
        have r38846 := hand1 (x (-10) 8) (x (-10) 12)
        have r38847 := hand1 (x (-11) 9) (x (-11) 13)
        have r38848 := hand1 (x (-7) 8) (x (-7) 13)
        have r38849 := hand1 (x (-8) 9) (x (-8) 14)
        have r38850 := hand1 (x (-8) 8) (x (-8) 14)
        have r38851 := hand2 (x (-10) 1) (x (-10) 10)
        have r38852 := hand2 (x (-11) 2) (x (-11) 11)
        have r38853 := hand2 (x (-12) 3) (x (-12) 12)
        have r38854 := hand2 (x 5 1) (x 5 11)
        have r38855 := hand2 (x (-11) 1) (x (-11) 12)
        have r38856 := hand2 (x (-12) 2) (x (-12) 13)
        have r38857 := hand2 (x (-13) 3) (x (-13) 14)
        have r38858 := hand2 (x (-13) 1) (x (-13) 14)
        have r38859 := hand1 (x 4 1) (x 4 14)
        have r38860 := hand2 (x 6 1) (x 6 14)
        have b38861 := hb (x (-17) 7)
        have b38862 := hb (x (-16) 6)
        have b38863 := hb (x (-15) 3)
        have b38864 := hb (x (-15) 5)
        have b38865 := hb (x (-15) 6)
        have b38866 := hb (x (-15) 7)
        have b38867 := hb (x (-14) 2)
        have b38868 := hb (x (-14) 4)
        have b38869 := hb (x (-14) 6)
        have b38870 := hb (x (-13) 5)
        have b38871 := hb (x (-13) 11)
        have b38872 := hb (x (-13) 13)
        have b38873 := hb (x (-13) 14)
        have b38874 := hb (x (-12) 4)
        have b38875 := hb (x (-12) 10)
        have b38876 := hb (x (-12) 12)
        have b38877 := hb (x (-12) 13)
        have b38878 := hb (x (-11) 9)
        have b38879 := hb (x (-11) 11)
        have b38880 := hb (x (-11) 12)
        have b38881 := hb (x (-10) 8)
        have b38882 := hb (x (-10) 10)
        have b38883 := hb (x (-10) 11)
        have b38884 := hb (x (-9) 1)
        have b38885 := hb (x (-9) 3)
        have b38886 := hb (x (-9) 7)
        have b38887 := hb (x (-9) 9)
        have b38888 := hb (x (-9) 10)
        have b38889 := hb (x (-8) 2)
        have b38890 := hb (x (-8) 6)
        have b38891 := hb (x (-8) 8)
        have b38892 := hb (x (-8) 9)
        have b38893 := hb (x (-8) 14)
        have b38894 := hb (x (-7) 5)
        have b38895 := hb (x (-7) 8)
        have b38896 := hb (x (-7) 13)
        have b38897 := hb (x (-6) 4)
        have b38898 := hb (x (-6) 7)
        have b38899 := hb (x (-6) 12)
        have b38900 := hb (x (-5) 6)
        have b38901 := hb (x (-5) 11)
        have b38902 := hb (x (-4) 5)
        have b38903 := hb (x (-4) 10)
        have b38904 := hb (x (-3) 4)
        have b38905 := hb (x (-3) 5)
        have b38906 := hb (x (-3) 9)
        have b38907 := hb (x (-2) 3)
        have b38908 := hb (x (-2) 4)
        have b38909 := hb (x (-2) 8)
        have b38910 := hb (x (-1) 2)
        have b38911 := hb (x (-1) 7)
        have b38912 := hb (x 0 1)
        have b38913 := hb (x 0 6)
        have b38914 := hb (x 1 5)
        have b38915 := hb (x 2 4)
        have b38916 := hb (x 3 2)
        have b38917 := hb (x 3 3)
        have b38918 := hb (x 4 1)
        have b38919 := hb (x 4 2)
        have b38920 := hb (x 5 1)
        have b38921 := hb (x 5 2)
        have b38922 := hb (x 5 3)
        have b38923 := hb (x 5 11)
        have b38924 := hb (x 5 13)
        have b38925 := hb (x 5 14)
        have b38926 := hb (x 6 2)
        have b38927 := hb (x 6 10)
        have b38928 := hb (x 6 12)
        have b38929 := hb (x 6 14)
        have b38930 := hb (x 7 13)
        have b38931 := hb (x 8 12)
        have b38932 := hb (x (-4) 2 && x (-4) 6)
        have b38933 := hb (x (-5) 3 && x (-5) 7)
        have b38934 := hb (x (-6) 4 && x (-6) 8)
        have b38935 := hb (x (-7) 5 && x (-7) 9)
        have b38936 := hb (x (-8) 6 && x (-8) 10)
        have b38937 := hb (x (-9) 7 && x (-9) 11)
        have b38938 := hb (x (-10) 8 && x (-10) 12)
        have b38939 := hb (x (-11) 9 && x (-11) 13)
        have b38940 := hb (x 0 1 && x 0 6)
        have b38941 := hb (x (-1) 2 && x (-1) 7)
        have b38942 := hb (x (-2) 3 && x (-2) 8)
        have b38943 := hb (x (-3) 4 && x (-3) 9)
        have b38944 := hb (x (-4) 5 && x (-4) 10)
        have b38945 := hb (x (-5) 6 && x (-5) 11)
        have b38946 := hb (x (-6) 7 && x (-6) 12)
        have b38947 := hb (x (-7) 8 && x (-7) 13)
        have b38948 := hb (x (-8) 9 && x (-8) 14)
        have b38949 := hb (x (-1) 1 && x (-1) 7)
        have b38950 := hb (x (-2) 2 && x (-2) 8)
        have b38951 := hb (x (-3) 3 && x (-3) 9)
        have b38952 := hb (x (-4) 4 && x (-4) 10)
        have b38953 := hb (x (-5) 5 && x (-5) 11)
        have b38954 := hb (x (-6) 6 && x (-6) 12)
        have b38955 := hb (x (-7) 7 && x (-7) 13)
        have b38956 := hb (x (-8) 8 && x (-8) 14)
        have b38957 := hb (x (-10) 1 && x (-10) 10)
        have b38958 := hb (x (-11) 2 && x (-11) 11)
        have b38959 := hb (x (-12) 3 && x (-12) 12)
        have b38960 := hb (x (-13) 4 && x (-13) 13)
        have b38961 := hb (x (-14) 5 && x (-14) 14)
        have b38962 := hb (x 5 1 && x 5 11)
        have b38963 := hb (x 4 2 && x 4 12)
        have b38964 := hb (x 3 3 && x 3 13)
        have b38965 := hb (x 2 4 && x 2 14)
        have b38966 := hb (x (-11) 1 && x (-11) 12)
        have b38967 := hb (x (-12) 2 && x (-12) 13)
        have b38968 := hb (x (-13) 3 && x (-13) 14)
        have b38969 := hb (x (-13) 1 && x (-13) 14)
        have b38970 := hb (x 4 1 && x 4 14)
        have b38971 := hb (x 6 1 && x 6 14)
        linarith only [r38789, r38790, r38791, e38792, e38793, e38794, e38795, e38796, e38797, r38798, e38799, e38800, e38801, e38802, e38803, e38804, r38805, e38806, e38807, e38808, e38809, e38810, e38811, r38812, e38813, e38814, r38815, e38816, e38817, r38818, e38819, e38820, r38821, e38822, e38823, r38824, r38825, r38826, r38827, e38828, e38829, r38830, r38831, r38832, r38833, r38834, r38835, r38836, r38837, r38838, r38839, r38840, r38841, r38842, r38843, r38844, r38845, r38846, r38847, r38848, r38849, r38850, r38851, r38852, r38853, r38854, r38855, r38856, r38857, r38858, r38859, r38860, b38861, b38862, b38863, b38864, b38865, b38866, b38867, b38868, b38869, b38870, b38871, b38872, b38873, b38874, b38875, b38876, b38877, b38878, b38879, b38880, b38881, b38882, b38883, b38884, b38885, b38886, b38887, b38888, b38889, b38890, b38891, b38892, b38893, b38894, b38895, b38896, b38897, b38898, b38899, b38900, b38901, b38902, b38903, b38904, b38905, b38906, b38907, b38908, b38909, b38910, b38911, b38912, b38913, b38914, b38915, b38916, b38917, b38918, b38919, b38920, b38921, b38922, b38923, b38924, b38925, b38926, b38927, b38928, b38929, b38930, b38931, b38932, b38933, b38934, b38935, b38936, b38937, b38938, b38939, b38940, b38941, b38942, b38943, b38944, b38945, b38946, b38947, b38948, b38949, b38950, b38951, b38952, b38953, b38954, b38955, b38956, b38957, b38958, b38959, b38960, b38961, b38962, b38963, b38964, b38965, b38966, b38967, b38968, b38969, b38970, b38971, d38548, g0, g1, g2, g3, g4, g5, g6, g7, f38440, g8, g10, g17, g22, g27, g35, g36, g39, d38445, g40, g41, g42, g43, g44, d38441, g48, g49, g50, g51, g52, g53, d38524, d38544, d38773, d38785, g66]
    · have f38972 : (x 1 7).toNat = 1 := by rw [h38564]; rfl
      have d38973 : (x 8 8).toNat = 0 := by
        have r38974 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e38975 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38976 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38977 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38978 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38979 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e38980 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b38981 := hb (x 1 7)
        have b38982 := hb (x 2 6)
        have b38983 := hb (x 3 5)
        have b38984 := hb (x 4 4)
        have b38985 := hb (x 5 11)
        have b38986 := hb (x 6 10)
        have b38987 := hb (x 7 9)
        have b38988 := hb (x 8 8)
        clear * - r38974 e38975 e38976 e38977 e38978 e38979 e38980 b38981 b38982 b38983 b38984 b38985 b38986 b38987 b38988 f38972
        omega
      have d38989 : (x 8 4 && x 8 8).toNat = 0 := by
        have r38990 := hand2 (x 8 4) (x 8 8)
        have b38991 := hb (x 8 8)
        have b38992 := hb (x 8 4 && x 8 8)
        clear * - r38990 b38991 b38992 d38973
        omega
      have d38993 : (x 7 9).toNat = 0 := by
        have r38994 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e38995 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38996 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38997 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38998 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38999 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e39000 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b39001 := hb (x 1 7)
        have b39002 := hb (x 2 6)
        have b39003 := hb (x 3 5)
        have b39004 := hb (x 4 4)
        have b39005 := hb (x 5 11)
        have b39006 := hb (x 6 10)
        have b39007 := hb (x 7 9)
        have b39008 := hb (x 8 8)
        clear * - r38994 e38995 e38996 e38997 e38998 e38999 e39000 b39001 b39002 b39003 b39004 b39005 b39006 b39007 b39008 d38973 f38972
        omega
      have d39009 : (x 7 5 && x 7 9).toNat = 0 := by
        have r39010 := hand2 (x 7 5) (x 7 9)
        have b39011 := hb (x 7 9)
        have b39012 := hb (x 7 5 && x 7 9)
        clear * - r39010 b39011 b39012 d38993
        omega
      have d39013 : (x 6 10).toNat = 0 := by
        have r39014 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e39015 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e39016 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e39017 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e39018 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e39019 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e39020 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b39021 := hb (x 1 7)
        have b39022 := hb (x 2 6)
        have b39023 := hb (x 3 5)
        have b39024 := hb (x 4 4)
        have b39025 := hb (x 5 11)
        have b39026 := hb (x 6 10)
        have b39027 := hb (x 7 9)
        have b39028 := hb (x 8 8)
        clear * - r39014 e39015 e39016 e39017 e39018 e39019 e39020 b39021 b39022 b39023 b39024 b39025 b39026 b39027 b39028 d38973 d38993 f38972
        omega
      have d39029 : (x 6 6 && x 6 10).toNat = 0 := by
        have r39030 := hand2 (x 6 6) (x 6 10)
        have b39031 := hb (x 6 10)
        have b39032 := hb (x 6 6 && x 6 10)
        clear * - r39030 b39031 b39032 d39013
        omega
      have d39033 : (x 5 11).toNat = 0 := by
        have r39034 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e39035 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e39036 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e39037 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e39038 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e39039 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e39040 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b39041 := hb (x 1 7)
        have b39042 := hb (x 2 6)
        have b39043 := hb (x 3 5)
        have b39044 := hb (x 4 4)
        have b39045 := hb (x 5 11)
        have b39046 := hb (x 6 10)
        have b39047 := hb (x 7 9)
        have b39048 := hb (x 8 8)
        clear * - r39034 e39035 e39036 e39037 e39038 e39039 e39040 b39041 b39042 b39043 b39044 b39045 b39046 b39047 b39048 d38973 d38993 d39013 f38972
        omega
      have d39049 : (x 5 1 && x 5 11).toNat = 0 := by
        have r39050 := hand2 (x 5 1) (x 5 11)
        have b39051 := hb (x 5 11)
        have b39052 := hb (x 5 1 && x 5 11)
        clear * - r39050 b39051 b39052 d39033
        omega
      have d39053 : (x 5 7 && x 5 11).toNat = 0 := by
        have r39054 := hand2 (x 5 7) (x 5 11)
        have b39055 := hb (x 5 11)
        have b39056 := hb (x 5 7 && x 5 11)
        clear * - r39054 b39055 b39056 d39033
        omega
      have d39057 : (x 4 4).toNat = 0 := by
        have r39058 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e39059 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e39060 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e39061 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e39062 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e39063 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e39064 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b39065 := hb (x 1 7)
        have b39066 := hb (x 2 6)
        have b39067 := hb (x 3 5)
        have b39068 := hb (x 4 4)
        have b39069 := hb (x 5 11)
        have b39070 := hb (x 6 10)
        have b39071 := hb (x 7 9)
        have b39072 := hb (x 8 8)
        clear * - r39058 e39059 e39060 e39061 e39062 e39063 e39064 b39065 b39066 b39067 b39068 b39069 b39070 b39071 b39072 d38973 d38993 d39013 d39033 f38972
        omega
      have d39073 : (x 4 4 && x 4 11).toNat = 0 := by
        have r39074 := hand1 (x 4 4) (x 4 11)
        have b39075 := hb (x 4 4)
        have b39076 := hb (x 4 4 && x 4 11)
        clear * - r39074 b39075 b39076 d39057
        omega
      have d39077 : (x 3 5).toNat = 0 := by
        have r39078 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e39079 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e39080 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e39081 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e39082 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e39083 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e39084 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b39085 := hb (x 1 7)
        have b39086 := hb (x 2 6)
        have b39087 := hb (x 3 5)
        have b39088 := hb (x 4 4)
        have b39089 := hb (x 5 11)
        have b39090 := hb (x 6 10)
        have b39091 := hb (x 7 9)
        have b39092 := hb (x 8 8)
        clear * - r39078 e39079 e39080 e39081 e39082 e39083 e39084 b39085 b39086 b39087 b39088 b39089 b39090 b39091 b39092 d38973 d38993 d39013 d39033 d39057 f38972
        omega
      have d39093 : (x 2 6).toNat = 0 := by
        have r39094 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
        have e39095 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e39096 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e39097 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e39098 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e39099 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e39100 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b39101 := hb (x 1 7)
        have b39102 := hb (x 2 6)
        have b39103 := hb (x 3 5)
        have b39104 := hb (x 4 4)
        have b39105 := hb (x 5 11)
        have b39106 := hb (x 6 10)
        have b39107 := hb (x 7 9)
        have b39108 := hb (x 8 8)
        clear * - r39094 e39095 e39096 e39097 e39098 e39099 e39100 b39101 b39102 b39103 b39104 b39105 b39106 b39107 b39108 d38973 d38993 d39013 d39033 d39057 d39077 f38972
        omega
      have d39109 : (x 2 6 && x 2 13).toNat = 0 := by
        have r39110 := hand1 (x 2 6) (x 2 13)
        have b39111 := hb (x 2 6)
        have b39112 := hb (x 2 6 && x 2 13)
        clear * - r39110 b39111 b39112 d39093
        omega
      have r39113 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
      have r39114 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
      have e39115 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
      have e39116 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
      have e39117 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
      have e39118 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
      have e39119 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
      have e39120 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
      have r39121 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e39122 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e39123 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have r39124 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := hcov4 12
      have e39125 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
      have e39126 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
      have r39127 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := hcov7 8
      have r39128 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := hcov9 15
      have r39129 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
      have r39130 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
      have r39131 := hand2 (x 10 2) (x 10 6)
      have r39132 := hand2 (x 9 3) (x 9 7)
      have r39133 := hand2 (x 7 1) (x 7 8)
      have r39134 := hand2 (x 6 2) (x 6 9)
      have r39135 := hand2 (x 5 3) (x 5 10)
      have r39136 := hand2 (x 14 1) (x 14 10)
      have r39137 := hand2 (x 13 2) (x 13 11)
      have r39138 := hand1 (x 12 3) (x 12 12)
      have r39139 := hand1 (x 11 4) (x 11 13)
      have r39140 := hand1 (x 10 5) (x 10 14)
      have r39141 := hand2 (x 4 2) (x 4 12)
      have r39142 := hand2 (x 3 3) (x 3 13)
      have r39143 := hand1 (x 2 2) (x 2 13)
      have b39144 := hb (x 0 4)
      have b39145 := hb (x 0 8)
      have b39146 := hb (x 1 3)
      have b39147 := hb (x 1 5)
      have b39148 := hb (x 1 11)
      have b39149 := hb (x 1 14)
      have b39150 := hb (x 2 2)
      have b39151 := hb (x 2 10)
      have b39152 := hb (x 2 13)
      have b39153 := hb (x 3 12)
      have b39154 := hb (x 3 13)
      have b39155 := hb (x 4 11)
      have b39156 := hb (x 4 12)
      have b39157 := hb (x 5 10)
      have b39158 := hb (x 6 9)
      have b39159 := hb (x 6 10)
      have b39160 := hb (x 7 8)
      have b39161 := hb (x 8 7)
      have b39162 := hb (x 9 6)
      have b39163 := hb (x 9 7)
      have b39164 := hb (x 10 5)
      have b39165 := hb (x 10 6)
      have b39166 := hb (x 11 4)
      have b39167 := hb (x 11 5)
      have b39168 := hb (x 12 3)
      have b39169 := hb (x 12 4)
      have b39170 := hb (x 13 2)
      have b39171 := hb (x 13 11)
      have b39172 := hb (x 14 1)
      have b39173 := hb (x 14 10)
      have b39174 := hb (x 15 9)
      have b39175 := hb (x 16 8)
      have b39176 := hb (x 10 2 && x 10 6)
      have b39177 := hb (x 9 3 && x 9 7)
      have b39178 := hb (x 8 4 && x 8 8)
      have b39179 := hb (x 7 5 && x 7 9)
      have b39180 := hb (x 6 6 && x 6 10)
      have b39181 := hb (x 5 7 && x 5 11)
      have b39182 := hb (x 4 8 && x 4 12)
      have b39183 := hb (x 3 9 && x 3 13)
      have b39184 := hb (x 7 1 && x 7 8)
      have b39185 := hb (x 6 2 && x 6 9)
      have b39186 := hb (x 5 3 && x 5 10)
      have b39187 := hb (x 4 4 && x 4 11)
      have b39188 := hb (x 3 5 && x 3 12)
      have b39189 := hb (x 2 6 && x 2 13)
      have b39190 := hb (x 1 7 && x 1 14)
      have b39191 := hb (x 14 1 && x 14 10)
      have b39192 := hb (x 13 2 && x 13 11)
      have b39193 := hb (x 12 3 && x 12 12)
      have b39194 := hb (x 11 4 && x 11 13)
      have b39195 := hb (x 10 5 && x 10 14)
      have b39196 := hb (x 5 1 && x 5 11)
      have b39197 := hb (x 4 2 && x 4 12)
      have b39198 := hb (x 3 3 && x 3 13)
      have b39199 := hb (x 2 4 && x 2 14)
      have b39200 := hb (x 3 1 && x 3 12)
      have b39201 := hb (x 2 2 && x 2 13)
      have b39202 := hb (x 1 3 && x 1 14)
      linarith only [r39113, r39114, e39115, e39116, e39117, e39118, e39119, e39120, r39121, e39122, e39123, r39124, e39125, e39126, r39127, r39128, r39129, r39130, r39131, r39132, r39133, r39134, r39135, r39136, r39137, r39138, r39139, r39140, r39141, r39142, r39143, b39144, b39145, b39146, b39147, b39148, b39149, b39150, b39151, b39152, b39153, b39154, b39155, b39156, b39157, b39158, b39159, b39160, b39161, b39162, b39163, b39164, b39165, b39166, b39167, b39168, b39169, b39170, b39171, b39172, b39173, b39174, b39175, b39176, b39177, b39178, b39179, b39180, b39181, b39182, b39183, b39184, b39185, b39186, b39187, b39188, b39189, b39190, b39191, b39192, b39193, b39194, b39195, b39196, b39197, b39198, b39199, b39200, b39201, b39202, g9, g12, g16, g17, g19, g21, g23, g25, g29, d39013, d38989, d39009, d39029, d39053, g37, g38, d39073, g61, d39109, g62, d39049, g66, g67, g68]
  · have f39203 : (x (-1) 7).toNat = 1 := by rw [h38439]; rfl
    have d39204 : (x 6 8).toNat = 0 := by
      have r39205 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e39206 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e39207 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e39208 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e39209 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e39210 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e39211 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b39212 := hb (x (-1) 7)
      have b39213 := hb (x 0 6)
      have b39214 := hb (x 1 5)
      have b39215 := hb (x 2 4)
      have b39216 := hb (x 3 11)
      have b39217 := hb (x 4 10)
      have b39218 := hb (x 5 9)
      have b39219 := hb (x 6 8)
      clear * - r39205 e39206 e39207 e39208 e39209 e39210 e39211 b39212 b39213 b39214 b39215 b39216 b39217 b39218 b39219 g22 g17 g10 f39203
      omega
    have d39220 : (x 6 8 && x 6 12).toNat = 0 := by
      have r39221 := hand1 (x 6 8) (x 6 12)
      have b39222 := hb (x 6 8)
      have b39223 := hb (x 6 8 && x 6 12)
      clear * - r39221 b39222 b39223 d39204
      omega
    have d39224 : (x 6 8 && x 6 10).toNat = 0 := by
      have r39225 := hand1 (x 6 8) (x 6 10)
      have b39226 := hb (x 6 8)
      have b39227 := hb (x 6 8 && x 6 10)
      clear * - r39225 b39226 b39227 d39204
      omega
    have d39228 : (x 5 9).toNat = 0 := by
      have r39229 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e39230 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e39231 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e39232 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e39233 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e39234 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e39235 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b39236 := hb (x (-1) 7)
      have b39237 := hb (x 0 6)
      have b39238 := hb (x 1 5)
      have b39239 := hb (x 2 4)
      have b39240 := hb (x 3 11)
      have b39241 := hb (x 4 10)
      have b39242 := hb (x 5 9)
      have b39243 := hb (x 6 8)
      clear * - r39229 e39230 e39231 e39232 e39233 e39234 e39235 b39236 b39237 b39238 b39239 b39240 b39241 b39242 b39243 d39204 g22 g17 g10 f39203
      omega
    have d39244 : (x 5 9 && x 5 13).toNat = 0 := by
      have r39245 := hand1 (x 5 9) (x 5 13)
      have b39246 := hb (x 5 9)
      have b39247 := hb (x 5 9 && x 5 13)
      clear * - r39245 b39246 b39247 d39228
      omega
    have d39248 : (x 5 9 && x 5 11).toNat = 0 := by
      have r39249 := hand1 (x 5 9) (x 5 11)
      have b39250 := hb (x 5 9)
      have b39251 := hb (x 5 9 && x 5 11)
      clear * - r39249 b39250 b39251 d39228
      omega
    have d39252 : (x 4 10).toNat = 0 := by
      have r39253 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e39254 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e39255 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e39256 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e39257 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e39258 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e39259 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b39260 := hb (x (-1) 7)
      have b39261 := hb (x 0 6)
      have b39262 := hb (x 1 5)
      have b39263 := hb (x 2 4)
      have b39264 := hb (x 3 11)
      have b39265 := hb (x 4 10)
      have b39266 := hb (x 5 9)
      have b39267 := hb (x 6 8)
      clear * - r39253 e39254 e39255 e39256 e39257 e39258 e39259 b39260 b39261 b39262 b39263 b39264 b39265 b39266 b39267 d39204 d39228 g22 g17 g10 f39203
      omega
    have d39268 : (x 4 10 && x 4 12).toNat = 0 := by
      have r39269 := hand1 (x 4 10) (x 4 12)
      have b39270 := hb (x 4 10)
      have b39271 := hb (x 4 10 && x 4 12)
      clear * - r39269 b39270 b39271 d39252
      omega
    have d39272 : (x 3 11).toNat = 0 := by
      have r39273 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e39274 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e39275 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e39276 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e39277 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e39278 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e39279 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b39280 := hb (x (-1) 7)
      have b39281 := hb (x 0 6)
      have b39282 := hb (x 1 5)
      have b39283 := hb (x 2 4)
      have b39284 := hb (x 3 11)
      have b39285 := hb (x 4 10)
      have b39286 := hb (x 5 9)
      have b39287 := hb (x 6 8)
      clear * - r39273 e39274 e39275 e39276 e39277 e39278 e39279 b39280 b39281 b39282 b39283 b39284 b39285 b39286 b39287 d39204 d39228 d39252 g22 g17 g10 f39203
      omega
    have d39288 : (x 3 11 && x 3 13).toNat = 0 := by
      have r39289 := hand1 (x 3 11) (x 3 13)
      have b39290 := hb (x 3 11)
      have b39291 := hb (x 3 11 && x 3 13)
      clear * - r39289 b39290 b39291 d39272
      omega
    have r39292 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
    have r39293 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
    have r39294 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := hcount 16
    have r39295 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := hd8 10
    have e39296 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e39297 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e39298 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e39299 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e39300 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e39301 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have r39302 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
    have e39303 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e39304 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e39305 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e39306 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e39307 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e39308 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have r39309 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := hd8 18
    have e39310 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e39311 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e39312 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e39313 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e39314 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e39315 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have r39316 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e39317 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e39318 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have r39319 : 1 ≤ (x 14 2).toNat + (x 13 1 && x 13 3).toNat + (x 12 2 && x 12 4).toNat + (x 11 3 && x 11 5).toNat + (x 10 4 && x 10 6).toNat + (x 9 5 && x 9 7).toNat + (x 8 6 && x 8 8).toNat + (x 7 7 && x 7 9).toNat + (x 6 8 && x 6 10).toNat + (x 5 9 && x 5 11).toNat + (x 4 10 && x 4 12).toNat + (x 3 11 && x 3 13).toNat + (x 2 12 && x 2 14).toNat + (x 1 13).toNat := hcov2 14
    have r39320 : 1 ≤ (x 14 4).toNat + (x 13 1 && x 13 5).toNat + (x 12 2 && x 12 6).toNat + (x 11 3 && x 11 7).toNat + (x 10 4 && x 10 8).toNat + (x 9 5 && x 9 9).toNat + (x 8 6 && x 8 10).toNat + (x 7 7 && x 7 11).toNat + (x 6 8 && x 6 12).toNat + (x 5 9 && x 5 13).toNat + (x 4 10 && x 4 14).toNat + (x 3 11).toNat := hcov4 14
    have e39321 : (x 13 1 && x 13 5).toNat = (x 13 5).toNat := handr _ _ (fun h => hp13 13 (hp5 13 (h)))
    have e39322 : (x 4 10 && x 4 14).toNat = (x 4 10).toNat := handl _ _ (fun h => hp2 4 (hp10 4 (h)))
    have r39323 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := hcov5 10
    have r39324 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
    have r39325 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
    have r39326 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
    have r39327 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
    have r39328 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have r39329 := hand2 (x 13 1) (x 13 3)
    have r39330 := hand2 (x 12 2) (x 12 4)
    have r39331 := hand2 (x 11 3) (x 11 5)
    have r39332 := hand2 (x 10 4) (x 10 6)
    have r39333 := hand2 (x 9 5) (x 9 7)
    have r39334 := hand2 (x 8 6) (x 8 8)
    have r39335 := hand2 (x 7 7) (x 7 9)
    have r39336 := hand2 (x 12 2) (x 12 6)
    have r39337 := hand2 (x 11 3) (x 11 7)
    have r39338 := hand2 (x 10 4) (x 10 8)
    have r39339 := hand2 (x 9 5) (x 9 9)
    have r39340 := hand2 (x 8 6) (x 8 10)
    have r39341 := hand2 (x 7 7) (x 7 11)
    have r39342 := hand2 (x 9 1) (x 9 6)
    have r39343 := hand2 (x 8 2) (x 8 7)
    have r39344 := hand2 (x 7 3) (x 7 8)
    have r39345 := hand1 (x 6 4) (x 6 9)
    have r39346 := hand1 (x 5 5) (x 5 10)
    have r39347 := hand1 (x 4 6) (x 4 11)
    have r39348 := hand2 (x 5 1) (x 5 10)
    have r39349 := hand2 (x 4 2) (x 4 11)
    have r39350 := hand2 (x 5 1) (x 5 11)
    have r39351 := hand2 (x 4 2) (x 4 12)
    have r39352 := hand2 (x 3 3) (x 3 13)
    have r39353 := hand2 (x 14 1) (x 14 12)
    have r39354 := hand2 (x 13 2) (x 13 13)
    have r39355 := hand1 (x 12 3) (x 12 14)
    have r39356 := hand1 (x 14 1) (x 14 14)
    have b39357 := hb (x 0 6)
    have b39358 := hb (x 0 10)
    have b39359 := hb (x 0 14)
    have b39360 := hb (x 1 5)
    have b39361 := hb (x 1 13)
    have b39362 := hb (x 1 14)
    have b39363 := hb (x 2 12)
    have b39364 := hb (x 2 13)
    have b39365 := hb (x 2 14)
    have b39366 := hb (x 3 7)
    have b39367 := hb (x 3 11)
    have b39368 := hb (x 3 12)
    have b39369 := hb (x 3 13)
    have b39370 := hb (x 4 6)
    have b39371 := hb (x 4 10)
    have b39372 := hb (x 4 11)
    have b39373 := hb (x 4 12)
    have b39374 := hb (x 5 5)
    have b39375 := hb (x 5 9)
    have b39376 := hb (x 5 10)
    have b39377 := hb (x 5 11)
    have b39378 := hb (x 6 4)
    have b39379 := hb (x 6 8)
    have b39380 := hb (x 6 9)
    have b39381 := hb (x 6 10)
    have b39382 := hb (x 7 7)
    have b39383 := hb (x 7 8)
    have b39384 := hb (x 7 9)
    have b39385 := hb (x 7 11)
    have b39386 := hb (x 8 6)
    have b39387 := hb (x 8 7)
    have b39388 := hb (x 8 8)
    have b39389 := hb (x 8 10)
    have b39390 := hb (x 9 5)
    have b39391 := hb (x 9 6)
    have b39392 := hb (x 9 7)
    have b39393 := hb (x 9 9)
    have b39394 := hb (x 10 4)
    have b39395 := hb (x 10 5)
    have b39396 := hb (x 10 6)
    have b39397 := hb (x 10 8)
    have b39398 := hb (x 11 3)
    have b39399 := hb (x 11 4)
    have b39400 := hb (x 11 5)
    have b39401 := hb (x 11 7)
    have b39402 := hb (x 11 11)
    have b39403 := hb (x 12 2)
    have b39404 := hb (x 12 3)
    have b39405 := hb (x 12 4)
    have b39406 := hb (x 12 6)
    have b39407 := hb (x 12 10)
    have b39408 := hb (x 13 1)
    have b39409 := hb (x 13 2)
    have b39410 := hb (x 13 3)
    have b39411 := hb (x 13 5)
    have b39412 := hb (x 13 9)
    have b39413 := hb (x 13 13)
    have b39414 := hb (x 14 1)
    have b39415 := hb (x 14 2)
    have b39416 := hb (x 14 4)
    have b39417 := hb (x 14 8)
    have b39418 := hb (x 14 12)
    have b39419 := hb (x 15 1)
    have b39420 := hb (x 15 11)
    have b39421 := hb (x 15 13)
    have b39422 := hb (x 16 10)
    have b39423 := hb (x 17 9)
    have b39424 := hb (x 18 8)
    have b39425 := hb (x 13 1 && x 13 3)
    have b39426 := hb (x 12 2 && x 12 4)
    have b39427 := hb (x 11 3 && x 11 5)
    have b39428 := hb (x 10 4 && x 10 6)
    have b39429 := hb (x 9 5 && x 9 7)
    have b39430 := hb (x 8 6 && x 8 8)
    have b39431 := hb (x 7 7 && x 7 9)
    have b39432 := hb (x 6 8 && x 6 10)
    have b39433 := hb (x 5 9 && x 5 11)
    have b39434 := hb (x 4 10 && x 4 12)
    have b39435 := hb (x 3 11 && x 3 13)
    have b39436 := hb (x 2 12 && x 2 14)
    have b39437 := hb (x 12 2 && x 12 6)
    have b39438 := hb (x 11 3 && x 11 7)
    have b39439 := hb (x 10 4 && x 10 8)
    have b39440 := hb (x 9 5 && x 9 9)
    have b39441 := hb (x 8 6 && x 8 10)
    have b39442 := hb (x 7 7 && x 7 11)
    have b39443 := hb (x 6 8 && x 6 12)
    have b39444 := hb (x 5 9 && x 5 13)
    have b39445 := hb (x 9 1 && x 9 6)
    have b39446 := hb (x 8 2 && x 8 7)
    have b39447 := hb (x 7 3 && x 7 8)
    have b39448 := hb (x 6 4 && x 6 9)
    have b39449 := hb (x 5 5 && x 5 10)
    have b39450 := hb (x 4 6 && x 4 11)
    have b39451 := hb (x 3 7 && x 3 12)
    have b39452 := hb (x 2 8 && x 2 13)
    have b39453 := hb (x 1 9 && x 1 14)
    have b39454 := hb (x 5 1 && x 5 10)
    have b39455 := hb (x 4 2 && x 4 11)
    have b39456 := hb (x 3 3 && x 3 12)
    have b39457 := hb (x 2 4 && x 2 13)
    have b39458 := hb (x 1 5 && x 1 14)
    have b39459 := hb (x 5 1 && x 5 11)
    have b39460 := hb (x 4 2 && x 4 12)
    have b39461 := hb (x 3 3 && x 3 13)
    have b39462 := hb (x 2 4 && x 2 14)
    have b39463 := hb (x 14 1 && x 14 12)
    have b39464 := hb (x 13 2 && x 13 13)
    have b39465 := hb (x 12 3 && x 12 14)
    have b39466 := hb (x 14 1 && x 14 14)
    linarith only [r39292, r39293, r39294, r39295, e39296, e39297, e39298, e39299, e39300, e39301, r39302, e39303, e39304, e39305, e39306, e39307, e39308, r39309, e39310, e39311, e39312, e39313, e39314, e39315, r39316, e39317, e39318, r39319, r39320, e39321, e39322, r39323, r39324, r39325, r39326, r39327, r39328, r39329, r39330, r39331, r39332, r39333, r39334, r39335, r39336, r39337, r39338, r39339, r39340, r39341, r39342, r39343, r39344, r39345, r39346, r39347, r39348, r39349, r39350, r39351, r39352, r39353, r39354, r39355, r39356, b39357, b39358, b39359, b39360, b39361, b39362, b39363, b39364, b39365, b39366, b39367, b39368, b39369, b39370, b39371, b39372, b39373, b39374, b39375, b39376, b39377, b39378, b39379, b39380, b39381, b39382, b39383, b39384, b39385, b39386, b39387, b39388, b39389, b39390, b39391, b39392, b39393, b39394, b39395, b39396, b39397, b39398, b39399, b39400, b39401, b39402, b39403, b39404, b39405, b39406, b39407, b39408, b39409, b39410, b39411, b39412, b39413, b39414, b39415, b39416, b39417, b39418, b39419, b39420, b39421, b39422, b39423, b39424, b39425, b39426, b39427, b39428, b39429, b39430, b39431, b39432, b39433, b39434, b39435, b39436, b39437, b39438, b39439, b39440, b39441, b39442, b39443, b39444, b39445, b39446, b39447, b39448, b39449, b39450, b39451, b39452, b39453, b39454, b39455, b39456, b39457, b39458, b39459, b39460, b39461, b39462, b39463, b39464, b39465, b39466, g10, g13, g15, g17, g20, g21, g24, g25, g26, d39272, g29, d39252, d39228, d39204, d39224, d39248, d39268, d39288, g30, d39220, d39244, g45, g46, g47, g63, g64, g65, g66]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000111 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 7).toNat = 0)
    (g1 : (x (-5) 6).toNat = 0)
    (g2 : (x (-4) 5).toNat = 0)
    (g3 : (x (-3) 4).toNat = 0)
    (g4 : (x (-3) 5).toNat = 0)
    (g5 : (x (-2) 3).toNat = 0)
    (g6 : (x (-2) 4).toNat = 0)
    (g7 : (x (-1) 2).toNat = 1)
    (g8 : (x 0 1).toNat = 1)
    (g9 : (x 0 4).toNat = 0)
    (g10 : (x 0 6).toNat = 0)
    (g11 : (x 0 7).toNat = 0)
    (g12 : (x 0 8).toNat = 0)
    (g13 : (x 0 10).toNat = 0)
    (g14 : (x 0 12).toNat = 0)
    (g15 : (x 0 14).toNat = 0)
    (g16 : (x 1 3).toNat = 0)
    (g17 : (x 1 5).toNat = 0)
    (g18 : (x 1 6).toNat = 0)
    (g19 : (x 1 11).toNat = 0)
    (g20 : (x 1 13).toNat = 0)
    (g21 : (x 1 14).toNat = 0)
    (g22 : (x 2 4).toNat = 0)
    (g23 : (x 2 10).toNat = 0)
    (g24 : (x 2 12).toNat = 0)
    (g25 : (x 2 13).toNat = 1)
    (g26 : (x 2 14).toNat = 1)
    (g27 : (x 3 2).toNat = 0)
    (g28 : (x 3 4).toNat = 0)
    (g29 : (x 3 12).toNat = 0)
    (g30 : (x 2 12 && x 2 14).toNat = 0)
    (g31 : (x 4 8 && x 4 11).toNat = 0)
    (g32 : (x 3 9 && x 3 12).toNat = 0)
    (g33 : (x 2 10 && x 2 13).toNat = 0)
    (g34 : (x 1 11 && x 1 14).toNat = 0)
    (g35 : (x (-4) 2 && x (-4) 6).toNat = 0)
    (g36 : (x (-5) 3 && x (-5) 7).toNat = 0)
    (g37 : (x 4 8 && x 4 12).toNat = 0)
    (g38 : (x 3 9 && x 3 13).toNat = 0)
    (g39 : (x 0 1 && x 0 6).toNat = 0)
    (g40 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g41 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g42 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g43 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g44 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g45 : (x 3 7 && x 3 12).toNat = 0)
    (g46 : (x 2 8 && x 2 13).toNat = 0)
    (g47 : (x 1 9 && x 1 14).toNat = 0)
    (g48 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g49 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g50 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g51 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g52 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g53 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g54 : (x (-2) 1 && x (-2) 8).toNat = 0)
    (g55 : (x (-3) 2 && x (-3) 9).toNat = 0)
    (g56 : (x (-4) 3 && x (-4) 10).toNat = 0)
    (g57 : (x (-5) 4 && x (-5) 11).toNat = 0)
    (g58 : (x (-6) 5 && x (-6) 12).toNat = 0)
    (g59 : (x (-7) 6 && x (-7) 13).toNat = 0)
    (g60 : (x (-8) 7 && x (-8) 14).toNat = 0)
    (g61 : (x 3 5 && x 3 12).toNat = 0)
    (g62 : (x 1 7 && x 1 14).toNat = 0)
    (g63 : (x 3 3 && x 3 12).toNat = 0)
    (g64 : (x 2 4 && x 2 13).toNat = 0)
    (g65 : (x 1 5 && x 1 14).toNat = 0)
    (g66 : (x 2 4 && x 2 14).toNat = 0)
    (g67 : (x 3 1 && x 3 12).toNat = 0)
    (g68 : (x 1 3 && x 1 14).toNat = 0)
    (g69 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000111_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69
