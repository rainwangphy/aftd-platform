import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011000010

Topic: combinatorics   Node: 0e7deef8d696

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 89 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011000010_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 11).toNat = 0)
    (g1 : (x (-3) 10).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 9).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-2) 13).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 8).toNat = 1)
    (g9 : (x (-1) 9).toNat = 1)
    (g10 : (x (-1) 10).toNat = 1)
    (g11 : (x (-1) 12).toNat = 1)
    (g12 : (x 0 5).toNat = 0)
    (g13 : (x 0 6).toNat = 0)
    (g14 : (x 0 7).toNat = 0)
    (g15 : (x 0 8).toNat = 0)
    (g16 : (x 0 9).toNat = 0)
    (g17 : (x 0 11).toNat = 0)
    (g18 : (x 0 14).toNat = 0)
    (g19 : (x 1 3).toNat = 0)
    (g20 : (x 1 5).toNat = 0)
    (g21 : (x 1 6).toNat = 0)
    (g22 : (x 1 8).toNat = 0)
    (g23 : (x 1 10).toNat = 0)
    (g24 : (x 1 13).toNat = 0)
    (g25 : (x 1 14).toNat = 0)
    (g26 : (x 2 4).toNat = 0)
    (g27 : (x 2 9).toNat = 0)
    (g28 : (x 2 12).toNat = 0)
    (g29 : (x 2 13).toNat = 1)
    (g30 : (x 2 14).toNat = 1)
    (g31 : (x 3 2).toNat = 0)
    (g32 : (x 3 4).toNat = 0)
    (g33 : (x 3 6).toNat = 0)
    (g34 : (x 3 8).toNat = 0)
    (g35 : (x 3 12).toNat = 0)
    (g36 : (x 3 3 && x 3 6).toNat = 0)
    (g37 : (x 2 4 && x 2 7).toNat = 0)
    (g38 : (x 1 5 && x 1 8).toNat = 0)
    (g39 : (x 0 6 && x 0 9).toNat = 0)
    (g40 : (x (-2) 8 && x (-2) 11).toNat = 0)
    (g41 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g42 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g43 : (x (-4) 3 && x (-4) 8).toNat = 0)
    (g44 : (x (-5) 4 && x (-5) 9).toNat = 0)
    (g45 : (x (-6) 5 && x (-6) 10).toNat = 0)
    (g46 : (x (-7) 6 && x (-7) 11).toNat = 0)
    (g47 : (x (-8) 7 && x (-8) 12).toNat = 0)
    (g48 : (x 0 1 && x 0 6).toNat = 0)
    (g49 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g50 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g51 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g52 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g53 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g54 : (x 3 3 && x 3 8).toNat = 0)
    (g55 : (x 2 4 && x 2 9).toNat = 0)
    (g56 : (x 1 5 && x 1 10).toNat = 0)
    (g57 : (x 0 6 && x 0 11).toNat = 0)
    (g58 : (x (-2) 8 && x (-2) 13).toNat = 0)
    (g59 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g60 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g61 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g62 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g63 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g64 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g65 : (x 3 6 && x 3 12).toNat = 0)
    (g66 : (x 1 8 && x 1 14).toNat = 0)
    (g67 : (x (-2) 1 && x (-2) 8).toNat = 0)
    (g68 : (x (-3) 2 && x (-3) 9).toNat = 0)
    (g69 : (x (-4) 3 && x (-4) 10).toNat = 0)
    (g70 : (x (-5) 4 && x (-5) 11).toNat = 0)
    (g71 : (x (-6) 5 && x (-6) 12).toNat = 0)
    (g72 : (x (-7) 6 && x (-7) 13).toNat = 0)
    (g73 : (x (-8) 7 && x (-8) 14).toNat = 0)
    (g74 : (x 3 6 && x 3 13).toNat = 0)
    (g75 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g76 : (x (-4) 2 && x (-4) 11).toNat = 0)
    (g77 : (x 3 3 && x 3 12).toNat = 0)
    (g78 : (x 2 4 && x 2 13).toNat = 0)
    (g79 : (x 1 5 && x 1 14).toNat = 0)
    (g80 : (x (-4) 1 && x (-4) 11).toNat = 0)
    (g81 : (x 2 2 && x 2 12).toNat = 0)
    (g82 : (x 1 3 && x 1 13).toNat = 0)
    (g83 : (x 0 4 && x 0 14).toNat = 0)
    (g84 : (x 3 2 && x 3 12).toNat = 0)
    (g85 : (x 1 4 && x 1 14).toNat = 0)
    (g86 : (x 2 4 && x 2 14).toNat = 0)
    (g87 : (x 3 3 && x 3 14).toNat = 0)
    (g88 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h31568 : x (-1) 7
  · have f31569 : (x (-1) 7).toNat = 0 := by rw [h31568]; rfl
    have d31570 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
      have r31571 := hand2 (x (-1) 1) (x (-1) 7)
      have b31572 := hb (x (-1) 7)
      have b31573 := hb (x (-1) 1 && x (-1) 7)
      clear * - r31571 b31572 b31573 f31569
      omega
    have d31574 : (x (-1) 7 && x (-1) 12).toNat = 0 := by
      have r31575 := hand1 (x (-1) 7) (x (-1) 12)
      have b31576 := hb (x (-1) 7)
      have b31577 := hb (x (-1) 7 && x (-1) 12)
      clear * - r31575 b31576 b31577 f31569
      omega
    have d31578 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
      have r31579 := hand2 (x (-1) 2) (x (-1) 7)
      have b31580 := hb (x (-1) 7)
      have b31581 := hb (x (-1) 2 && x (-1) 7)
      clear * - r31579 b31580 b31581 f31569
      omega
    have d31582 : (x (-1) 7 && x (-1) 10).toNat = 0 := by
      have r31583 := hand1 (x (-1) 7) (x (-1) 10)
      have b31584 := hb (x (-1) 7)
      have b31585 := hb (x (-1) 7 && x (-1) 10)
      clear * - r31583 b31584 b31585 f31569
      omega
    have d31586 : (x (-9) 8).toNat = 1 := by
      have r31587 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := hcov7 (-1)
      have b31588 := hb (x (-9) 8)
      have b31589 := hb (x (-1) 7)
      have b31590 := hb (x (-2) 1 && x (-2) 8)
      have b31591 := hb (x (-3) 2 && x (-3) 9)
      have b31592 := hb (x (-4) 3 && x (-4) 10)
      have b31593 := hb (x (-5) 4 && x (-5) 11)
      have b31594 := hb (x (-6) 5 && x (-6) 12)
      have b31595 := hb (x (-7) 6 && x (-7) 13)
      have b31596 := hb (x (-8) 7 && x (-8) 14)
      clear * - r31587 b31588 b31589 b31590 b31591 b31592 b31593 b31594 b31595 b31596 f31569 g67 g68 g69 g70 g71 g72 g73
      omega
    have d31597 : (x (-10) 9).toNat = 0 := by
      have r31598 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := hd8 (-9)
      have e31599 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e31600 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e31601 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e31602 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e31603 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e31604 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b31605 := hb (x (-16) 7)
      have b31606 := hb (x (-15) 6)
      have b31607 := hb (x (-14) 5)
      have b31608 := hb (x (-13) 4)
      have b31609 := hb (x (-12) 11)
      have b31610 := hb (x (-11) 10)
      have b31611 := hb (x (-10) 9)
      have b31612 := hb (x (-9) 8)
      clear * - r31598 e31599 e31600 e31601 e31602 e31603 e31604 b31605 b31606 b31607 b31608 b31609 b31610 b31611 b31612 d31586
      omega
    have d31613 : (x (-10) 9 && x (-10) 14).toNat = 0 := by
      have r31614 := hand1 (x (-10) 9) (x (-10) 14)
      have b31615 := hb (x (-10) 9)
      have b31616 := hb (x (-10) 9 && x (-10) 14)
      clear * - r31614 b31615 b31616 d31597
      omega
    have d31617 : (x (-11) 10).toNat = 0 := by
      have r31618 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := hd8 (-9)
      have e31619 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e31620 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e31621 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e31622 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e31623 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e31624 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b31625 := hb (x (-16) 7)
      have b31626 := hb (x (-15) 6)
      have b31627 := hb (x (-14) 5)
      have b31628 := hb (x (-13) 4)
      have b31629 := hb (x (-12) 11)
      have b31630 := hb (x (-11) 10)
      have b31631 := hb (x (-10) 9)
      have b31632 := hb (x (-9) 8)
      clear * - r31618 e31619 e31620 e31621 e31622 e31623 e31624 b31625 b31626 b31627 b31628 b31629 b31630 b31631 b31632 d31586 d31597
      omega
    have d31633 : (x (-9) 8 && x (-9) 13).toNat = 1 := by
      have r31634 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := hcov5 (-1)
      have b31635 := hb (x (-11) 10)
      have b31636 := hb (x (-1) 5)
      have b31637 := hb (x (-2) 1 && x (-2) 6)
      have b31638 := hb (x (-3) 2 && x (-3) 7)
      have b31639 := hb (x (-4) 3 && x (-4) 8)
      have b31640 := hb (x (-5) 4 && x (-5) 9)
      have b31641 := hb (x (-6) 5 && x (-6) 10)
      have b31642 := hb (x (-7) 6 && x (-7) 11)
      have b31643 := hb (x (-8) 7 && x (-8) 12)
      have b31644 := hb (x (-9) 8 && x (-9) 13)
      have b31645 := hb (x (-10) 9 && x (-10) 14)
      clear * - r31634 b31635 b31636 b31637 b31638 b31639 b31640 b31641 b31642 b31643 b31644 b31645 g7 g41 g42 g43 g44 g45 g46 g47 d31613 d31617
      omega
    have d31646 : (x (-9) 13).toNat = 1 := by
      have r31647 := hand2 (x (-9) 8) (x (-9) 13)
      have b31648 := hb (x (-9) 13)
      have b31649 := hb (x (-9) 8 && x (-9) 13)
      clear * - r31647 b31648 b31649 d31633
      omega
    have d31650 : (x (-9) 1).toNat = 1 := by
      have r31651 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
      have b31652 := hb (x (-9) 1)
      have b31653 := hb (x (-9) 13)
      clear * - r31651 b31652 b31653 d31646
      omega
    have d31654 : (x (-8) 14).toNat = 0 := by
      have r31655 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := hd14 (-8)
      have b31656 := hb (x (-9) 1)
      have b31657 := hb (x (-8) 14)
      clear * - r31655 b31656 b31657 d31650
      omega
    have d31658 : (x (-8) 8 && x (-8) 14).toNat = 0 := by
      have r31659 := hand2 (x (-8) 8) (x (-8) 14)
      have b31660 := hb (x (-8) 14)
      have b31661 := hb (x (-8) 8 && x (-8) 14)
      clear * - r31659 b31660 b31661 d31654
      omega
    have d31662 : (x (-9) 9).toNat = 1 := by
      have r31663 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := hcov6 0
      have b31664 := hb (x (-9) 9)
      have b31665 := hb (x 0 6)
      have b31666 := hb (x (-1) 1 && x (-1) 7)
      have b31667 := hb (x (-2) 2 && x (-2) 8)
      have b31668 := hb (x (-3) 3 && x (-3) 9)
      have b31669 := hb (x (-4) 4 && x (-4) 10)
      have b31670 := hb (x (-5) 5 && x (-5) 11)
      have b31671 := hb (x (-6) 6 && x (-6) 12)
      have b31672 := hb (x (-7) 7 && x (-7) 13)
      have b31673 := hb (x (-8) 8 && x (-8) 14)
      clear * - r31663 b31664 b31665 b31666 b31667 b31668 b31669 b31670 b31671 b31672 b31673 g13 d31570 g59 g60 g61 g62 g63 g64 d31658
      omega
    have d31674 : (x (-8) 8).toNat = 0 := by
      have r31675 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
      have e31676 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e31677 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e31678 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e31679 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e31680 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e31681 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b31682 := hb (x (-15) 7)
      have b31683 := hb (x (-14) 6)
      have b31684 := hb (x (-13) 5)
      have b31685 := hb (x (-12) 4)
      have b31686 := hb (x (-11) 11)
      have b31687 := hb (x (-10) 10)
      have b31688 := hb (x (-9) 9)
      have b31689 := hb (x (-8) 8)
      clear * - r31675 e31676 e31677 e31678 e31679 e31680 e31681 b31682 b31683 b31684 b31685 b31686 b31687 b31688 b31689 d31662
      omega
    have d31690 : (x (-10) 10).toNat = 0 := by
      have r31691 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
      have e31692 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e31693 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e31694 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e31695 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e31696 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e31697 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b31698 := hb (x (-15) 7)
      have b31699 := hb (x (-14) 6)
      have b31700 := hb (x (-13) 5)
      have b31701 := hb (x (-12) 4)
      have b31702 := hb (x (-11) 11)
      have b31703 := hb (x (-10) 10)
      have b31704 := hb (x (-9) 9)
      have b31705 := hb (x (-8) 8)
      clear * - r31691 e31692 e31693 e31694 e31695 e31696 e31697 b31698 b31699 b31700 b31701 b31702 b31703 b31704 b31705 d31674 d31662
      omega
    have d31706 : (x (-11) 11).toNat = 0 := by
      have r31707 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
      have e31708 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e31709 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e31710 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e31711 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e31712 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e31713 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b31714 := hb (x (-15) 7)
      have b31715 := hb (x (-14) 6)
      have b31716 := hb (x (-13) 5)
      have b31717 := hb (x (-12) 4)
      have b31718 := hb (x (-11) 11)
      have b31719 := hb (x (-10) 10)
      have b31720 := hb (x (-9) 9)
      have b31721 := hb (x (-8) 8)
      clear * - r31707 e31708 e31709 e31710 e31711 e31712 e31713 b31714 b31715 b31716 b31717 b31718 b31719 b31720 b31721 d31674 d31662 d31690
      omega
    have d31722 : (x (-12) 4).toNat = 0 := by
      have r31723 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
      have e31724 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e31725 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e31726 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e31727 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e31728 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e31729 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b31730 := hb (x (-15) 7)
      have b31731 := hb (x (-14) 6)
      have b31732 := hb (x (-13) 5)
      have b31733 := hb (x (-12) 4)
      have b31734 := hb (x (-11) 11)
      have b31735 := hb (x (-10) 10)
      have b31736 := hb (x (-9) 9)
      have b31737 := hb (x (-8) 8)
      clear * - r31723 e31724 e31725 e31726 e31727 e31728 e31729 b31730 b31731 b31732 b31733 b31734 b31735 b31736 b31737 d31674 d31662 d31690 d31706
      omega
    have d31738 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
      have r31739 := hand1 (x (-12) 4) (x (-12) 14)
      have b31740 := hb (x (-12) 4)
      have b31741 := hb (x (-12) 4 && x (-12) 14)
      clear * - r31739 b31740 b31741 d31722
      omega
    have d31742 : (x (-13) 5).toNat = 0 := by
      have r31743 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
      have e31744 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e31745 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e31746 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e31747 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e31748 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e31749 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have b31750 := hb (x (-15) 7)
      have b31751 := hb (x (-14) 6)
      have b31752 := hb (x (-13) 5)
      have b31753 := hb (x (-12) 4)
      have b31754 := hb (x (-11) 11)
      have b31755 := hb (x (-10) 10)
      have b31756 := hb (x (-9) 9)
      have b31757 := hb (x (-8) 8)
      clear * - r31743 e31744 e31745 e31746 e31747 e31748 e31749 b31750 b31751 b31752 b31753 b31754 b31755 b31756 b31757 d31674 d31662 d31690 d31706 d31722
      omega
    have d31758 : (x (-8) 9 && x (-8) 14).toNat = 0 := by
      have r31759 := hand2 (x (-8) 9) (x (-8) 14)
      have b31760 := hb (x (-8) 14)
      have b31761 := hb (x (-8) 9 && x (-8) 14)
      clear * - r31759 b31760 b31761 d31654
      omega
    have d31762 : (x (-8) 6).toNat = 0 := by
      have r31763 : (x (-8) 6).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp6 (-8))
      have b31764 := hb (x (-8) 6)
      have b31765 := hb (x (-8) 14)
      clear * - r31763 b31764 b31765 d31654
      omega
    have d31766 : (x (-8) 2).toNat = 0 := by
      have r31767 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
      have b31768 := hb (x (-8) 2)
      have b31769 := hb (x (-8) 14)
      clear * - r31767 b31768 b31769 d31654
      omega
    have d31770 : (x (-8) 10).toNat = 0 := by
      have r31771 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have b31772 := hb (x (-8) 2)
      have b31773 := hb (x (-8) 10)
      clear * - r31771 b31772 b31773 d31766
      omega
    have d31774 : (x (-8) 12).toNat = 0 := by
      have r31775 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := hd12 (-8)
      have e31776 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e31777 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b31778 := hb (x (-11) 3)
      have b31779 := hb (x (-10) 2)
      have b31780 := hb (x (-9) 13)
      have b31781 := hb (x (-8) 12)
      clear * - r31775 e31776 e31777 b31778 b31779 b31780 b31781 d31646
      omega
    have d31782 : (x (-10) 2).toNat = 0 := by
      have r31783 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := hd12 (-8)
      have e31784 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e31785 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b31786 := hb (x (-11) 3)
      have b31787 := hb (x (-10) 2)
      have b31788 := hb (x (-9) 13)
      have b31789 := hb (x (-8) 12)
      clear * - r31783 e31784 e31785 b31786 b31787 b31788 b31789 d31774 d31646
      omega
    have d31790 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
      have r31791 := hand1 (x (-10) 2) (x (-10) 12)
      have b31792 := hb (x (-10) 2)
      have b31793 := hb (x (-10) 2 && x (-10) 12)
      clear * - r31791 b31792 b31793 d31782
      omega
    have d31794 : (x (-11) 3).toNat = 0 := by
      have r31795 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := hd12 (-8)
      have e31796 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e31797 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b31798 := hb (x (-11) 3)
      have b31799 := hb (x (-10) 2)
      have b31800 := hb (x (-9) 13)
      have b31801 := hb (x (-8) 12)
      clear * - r31795 e31796 e31797 b31798 b31799 b31800 b31801 d31774 d31646 d31782
      omega
    have d31802 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
      have r31803 := hand1 (x (-11) 3) (x (-11) 13)
      have b31804 := hb (x (-11) 3)
      have b31805 := hb (x (-11) 3 && x (-11) 13)
      clear * - r31803 b31804 b31805 d31794
      omega
    have d31806 : (x (-9) 1 && x (-9) 11).toNat = 1 := by
      have r31807 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := hcov10 (-8)
      have b31808 := hb (x (-13) 5)
      have b31809 := hb (x (-8) 10)
      have b31810 := hb (x (-9) 1 && x (-9) 11)
      have b31811 := hb (x (-10) 2 && x (-10) 12)
      have b31812 := hb (x (-11) 3 && x (-11) 13)
      have b31813 := hb (x (-12) 4 && x (-12) 14)
      clear * - r31807 b31808 b31809 b31810 b31811 b31812 b31813 d31770 d31790 d31802 d31738 d31742
      omega
    have d31814 : (x (-9) 11).toNat = 1 := by
      have r31815 := hand2 (x (-9) 1) (x (-9) 11)
      have b31816 := hb (x (-9) 11)
      have b31817 := hb (x (-9) 1 && x (-9) 11)
      clear * - r31815 b31816 b31817 d31806
      omega
    have d31818 : (x (-9) 3).toNat = 1 := by
      have r31819 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
      have b31820 := hb (x (-9) 3)
      have b31821 := hb (x (-9) 11)
      clear * - r31819 b31820 b31821 d31814
      omega
    have d31822 : (x (-6) 12).toNat = 0 := by
      have r31823 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := hd12 (-6)
      have e31824 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e31825 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b31826 := hb (x (-9) 3)
      have b31827 := hb (x (-8) 2)
      have b31828 := hb (x (-7) 13)
      have b31829 := hb (x (-6) 12)
      clear * - r31823 e31824 e31825 b31826 b31827 b31828 b31829 d31766 d31818
      omega
    have d31830 : (x (-6) 4).toNat = 0 := by
      have r31831 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have b31832 := hb (x (-6) 4)
      have b31833 := hb (x (-6) 12)
      clear * - r31831 b31832 b31833 d31822
      omega
    have d31834 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
      have r31835 := hand1 (x (-6) 4) (x (-6) 13)
      have b31836 := hb (x (-6) 4)
      have b31837 := hb (x (-6) 4 && x (-6) 13)
      clear * - r31835 b31836 b31837 d31830
      omega
    have d31838 : (x (-7) 13).toNat = 0 := by
      have r31839 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := hd12 (-6)
      have e31840 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e31841 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b31842 := hb (x (-9) 3)
      have b31843 := hb (x (-8) 2)
      have b31844 := hb (x (-7) 13)
      have b31845 := hb (x (-6) 12)
      clear * - r31839 e31840 e31841 b31842 b31843 b31844 b31845 d31822 d31766 d31818
      omega
    have d31846 : (x (-7) 8 && x (-7) 13).toNat = 0 := by
      have r31847 := hand2 (x (-7) 8) (x (-7) 13)
      have b31848 := hb (x (-7) 13)
      have b31849 := hb (x (-7) 8 && x (-7) 13)
      clear * - r31847 b31848 b31849 d31838
      omega
    have d31850 : (x (-9) 10).toNat = 1 := by
      have r31851 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := hcov5 1
      have b31852 := hb (x (-9) 10)
      have b31853 := hb (x 1 5)
      have b31854 := hb (x 0 1 && x 0 6)
      have b31855 := hb (x (-1) 2 && x (-1) 7)
      have b31856 := hb (x (-2) 3 && x (-2) 8)
      have b31857 := hb (x (-3) 4 && x (-3) 9)
      have b31858 := hb (x (-4) 5 && x (-4) 10)
      have b31859 := hb (x (-5) 6 && x (-5) 11)
      have b31860 := hb (x (-6) 7 && x (-6) 12)
      have b31861 := hb (x (-7) 8 && x (-7) 13)
      have b31862 := hb (x (-8) 9 && x (-8) 14)
      clear * - r31851 b31852 b31853 b31854 b31855 b31856 b31857 b31858 b31859 b31860 b31861 b31862 g20 g48 d31578 g49 g50 g51 g52 g53 d31846 d31758
      omega
    have d31863 : (x (-9) 2).toNat = 1 := by
      have r31864 : (x (-9) 10).toNat ≤ (x (-9) 2).toNat := himp _ _ (hp10 (-9))
      have b31865 := hb (x (-9) 2)
      have b31866 := hb (x (-9) 10)
      clear * - r31864 b31865 b31866 d31850
      omega
    have d31867 : (x (-7) 12).toNat = 0 := by
      have r31868 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
      have e31869 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e31870 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b31871 := hb (x (-10) 3)
      have b31872 := hb (x (-9) 2)
      have b31873 := hb (x (-8) 13)
      have b31874 := hb (x (-7) 12)
      clear * - r31868 e31869 e31870 b31871 b31872 b31873 b31874 d31863
      omega
    have d31875 : (x (-7) 4).toNat = 0 := by
      have r31876 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
      have b31877 := hb (x (-7) 4)
      have b31878 := hb (x (-7) 12)
      clear * - r31876 b31877 b31878 d31867
      omega
    have d31879 : (x (-7) 4 && x (-7) 14).toNat = 0 := by
      have r31880 := hand1 (x (-7) 4) (x (-7) 14)
      have b31881 := hb (x (-7) 4)
      have b31882 := hb (x (-7) 4 && x (-7) 14)
      clear * - r31880 b31881 b31882 d31875
      omega
    have d31883 : (x (-8) 13).toNat = 0 := by
      have r31884 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
      have e31885 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e31886 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b31887 := hb (x (-10) 3)
      have b31888 := hb (x (-9) 2)
      have b31889 := hb (x (-8) 13)
      have b31890 := hb (x (-7) 12)
      clear * - r31884 e31885 e31886 b31887 b31888 b31889 b31890 d31867 d31863
      omega
    have d31891 : (x (-8) 5).toNat = 0 := by
      have r31892 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
      have b31893 := hb (x (-8) 5)
      have b31894 := hb (x (-8) 13)
      clear * - r31892 b31893 b31894 d31883
      omega
    have d31895 : (x (-7) 5).toNat = 0 := by
      have r31896 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b31897 := hb (x (-7) 5)
      have b31898 := hb (x (-7) 13)
      clear * - r31896 b31897 b31898 d31838
      omega
    have d31899 : (x (-7) 5 && x (-7) 14).toNat = 0 := by
      have r31900 := hand1 (x (-7) 5) (x (-7) 14)
      have b31901 := hb (x (-7) 5)
      have b31902 := hb (x (-7) 5 && x (-7) 14)
      clear * - r31900 b31901 b31902 d31895
      omega
    have d31903 : (x (-5) 3 && x (-5) 12).toNat = 1 := by
      have r31904 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := hcov9 (-2)
      have b31905 := hb (x (-8) 6)
      have b31906 := hb (x (-2) 9)
      have b31907 := hb (x (-3) 1 && x (-3) 10)
      have b31908 := hb (x (-4) 2 && x (-4) 11)
      have b31909 := hb (x (-5) 3 && x (-5) 12)
      have b31910 := hb (x (-6) 4 && x (-6) 13)
      have b31911 := hb (x (-7) 5 && x (-7) 14)
      clear * - r31904 b31905 b31906 b31907 b31908 b31909 b31910 b31911 g3 g75 g76 d31834 d31899 d31762
      omega
    have d31912 : (x (-5) 12).toNat = 1 := by
      have r31913 := hand2 (x (-5) 3) (x (-5) 12)
      have b31914 := hb (x (-5) 12)
      have b31915 := hb (x (-5) 3 && x (-5) 12)
      clear * - r31913 b31914 b31915 d31903
      omega
    have d31916 : (x (-6) 13).toNat = 0 := by
      have r31917 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
      have e31918 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e31919 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b31920 := hb (x (-8) 3)
      have b31921 := hb (x (-7) 2)
      have b31922 := hb (x (-6) 13)
      have b31923 := hb (x (-5) 12)
      clear * - r31917 e31918 e31919 b31920 b31921 b31922 b31923 d31912
      omega
    have d31924 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
      have r31925 := hand2 (x (-6) 3) (x (-6) 13)
      have b31926 := hb (x (-6) 13)
      have b31927 := hb (x (-6) 3 && x (-6) 13)
      clear * - r31925 b31926 b31927 d31916
      omega
    have d31928 : (x (-5) 2 && x (-5) 12).toNat = 1 := by
      have r31929 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := hcov10 (-3)
      have b31930 := hb (x (-8) 5)
      have b31931 := hb (x (-3) 10)
      have b31932 := hb (x (-4) 1 && x (-4) 11)
      have b31933 := hb (x (-5) 2 && x (-5) 12)
      have b31934 := hb (x (-6) 3 && x (-6) 13)
      have b31935 := hb (x (-7) 4 && x (-7) 14)
      clear * - r31929 b31930 b31931 b31932 b31933 b31934 b31935 g1 g80 d31924 d31879 d31891
      omega
    have d31936 : (x (-5) 2).toNat = 1 := by
      have r31937 := hand1 (x (-5) 2) (x (-5) 12)
      have b31938 := hb (x (-5) 2)
      have b31939 := hb (x (-5) 2 && x (-5) 12)
      clear * - r31937 b31938 b31939 d31928
      omega
    have d31940 : (x (-5) 14).toNat = 1 := by
      have r31941 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
      have b31942 := hb (x (-5) 2)
      have b31943 := hb (x (-5) 14)
      clear * - r31941 b31942 b31943 d31936
      omega
    have d31944 : (x (-3) 12).toNat = 0 := by
      have r31945 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e31946 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e31947 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b31948 := hb (x (-6) 3)
      have b31949 := hb (x (-5) 2)
      have b31950 := hb (x (-4) 13)
      have b31951 := hb (x (-3) 12)
      clear * - r31945 e31946 e31947 b31948 b31949 b31950 b31951 d31936
      omega
    have d31952 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
      have r31953 := hand2 (x (-3) 1) (x (-3) 12)
      have b31954 := hb (x (-3) 12)
      have b31955 := hb (x (-3) 1 && x (-3) 12)
      clear * - r31953 b31954 b31955 d31944
      omega
    have d31956 : (x (-3) 9 && x (-3) 12).toNat = 0 := by
      have r31957 := hand2 (x (-3) 9) (x (-3) 12)
      have b31958 := hb (x (-3) 12)
      have b31959 := hb (x (-3) 9 && x (-3) 12)
      clear * - r31957 b31958 b31959 d31944
      omega
    have d31960 : (x (-4) 13).toNat = 0 := by
      have r31961 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e31962 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e31963 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b31964 := hb (x (-6) 3)
      have b31965 := hb (x (-5) 2)
      have b31966 := hb (x (-4) 13)
      have b31967 := hb (x (-3) 12)
      clear * - r31961 e31962 e31963 b31964 b31965 b31966 b31967 d31944 d31936
      omega
    have d31968 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
      have r31969 := hand2 (x (-4) 2) (x (-4) 13)
      have b31970 := hb (x (-4) 13)
      have b31971 := hb (x (-4) 2 && x (-4) 13)
      clear * - r31969 b31970 b31971 d31960
      omega
    have d31972 : (x (-5) 3 && x (-5) 14).toNat = 1 := by
      have r31973 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := hcov11 (-2)
      have b31974 := hb (x (-6) 4)
      have b31975 := hb (x (-2) 11)
      have b31976 := hb (x (-3) 1 && x (-3) 12)
      have b31977 := hb (x (-4) 2 && x (-4) 13)
      have b31978 := hb (x (-5) 3 && x (-5) 14)
      clear * - r31973 b31974 b31975 b31976 b31977 b31978 g5 d31952 d31968 d31830
      omega
    have d31979 : (x (-5) 3).toNat = 1 := by
      have r31980 := hand1 (x (-5) 3) (x (-5) 14)
      have b31981 := hb (x (-5) 3)
      have b31982 := hb (x (-5) 3 && x (-5) 14)
      clear * - r31980 b31981 b31982 d31972
      omega
    have d31983 : (x (-2) 12).toNat = 0 := by
      have r31984 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
      have e31985 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e31986 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b31987 := hb (x (-5) 3)
      have b31988 := hb (x (-4) 2)
      have b31989 := hb (x (-3) 13)
      have b31990 := hb (x (-2) 12)
      clear * - r31984 e31985 e31986 b31987 b31988 b31989 b31990 d31979
      omega
    have d31991 : (x (-3) 13).toNat = 0 := by
      have r31992 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
      have e31993 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e31994 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b31995 := hb (x (-5) 3)
      have b31996 := hb (x (-4) 2)
      have b31997 := hb (x (-3) 13)
      have b31998 := hb (x (-2) 12)
      clear * - r31992 e31993 e31994 b31995 b31996 b31997 b31998 d31983 d31979
      omega
    have d31999 : (x (-4) 2).toNat = 0 := by
      have r32000 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
      have e32001 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e32002 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b32003 := hb (x (-5) 3)
      have b32004 := hb (x (-4) 2)
      have b32005 := hb (x (-3) 13)
      have b32006 := hb (x (-2) 12)
      clear * - r32000 e32001 e32002 b32003 b32004 b32005 b32006 d31983 d31991 d31979
      omega
    have d32007 : (x (-4) 10).toNat = 0 := by
      have r32008 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
      have b32009 := hb (x (-4) 2)
      have b32010 := hb (x (-4) 10)
      clear * - r32008 b32009 b32010 d31999
      omega
    have d32011 : (x (-4) 10 && x (-4) 13).toNat = 0 := by
      have r32012 := hand1 (x (-4) 10) (x (-4) 13)
      have b32013 := hb (x (-4) 10)
      have b32014 := hb (x (-4) 10 && x (-4) 13)
      clear * - r32012 b32013 b32014 d32007
      omega
    have d32015 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
      have r32016 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
      have b32017 := hb (x (-4) 2)
      have b32018 := hb (x (-2) 13)
      have b32019 := hb (x (-3) 1 && x (-3) 14)
      clear * - r32016 b32017 b32018 b32019 g6 d31999
      omega
    have d32020 : (x (-3) 14).toNat = 1 := by
      have r32021 := hand2 (x (-3) 1) (x (-3) 14)
      have b32022 := hb (x (-3) 14)
      have b32023 := hb (x (-3) 1 && x (-3) 14)
      clear * - r32021 b32022 b32023 d32015
      omega
    have d32024 : (x (-4) 1).toNat = 0 := by
      have r32025 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
      have b32026 := hb (x (-4) 1)
      have b32027 := hb (x (-3) 14)
      clear * - r32025 b32026 b32027 d32020
      omega
    have d32028 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
      have r32029 := hand1 (x (-4) 1) (x (-4) 12)
      have b32030 := hb (x (-4) 1)
      have b32031 := hb (x (-4) 1 && x (-4) 12)
      clear * - r32029 b32030 b32031 d32024
      omega
    have d32032 : (x (-6) 3).toNat = 0 := by
      have r32033 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
      have e32034 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e32035 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b32036 := hb (x (-6) 3)
      have b32037 := hb (x (-5) 2)
      have b32038 := hb (x (-4) 13)
      have b32039 := hb (x (-3) 12)
      clear * - r32033 e32034 e32035 b32036 b32037 b32038 b32039 d31944 d31960 d31936
      omega
    have d32040 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
      have r32041 := hand1 (x (-6) 3) (x (-6) 14)
      have b32042 := hb (x (-6) 3)
      have b32043 := hb (x (-6) 3 && x (-6) 14)
      clear * - r32041 b32042 b32043 d32032
      omega
    have d32044 : (x (-5) 2 && x (-5) 13).toNat = 1 := by
      have r32045 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := hcov11 (-3)
      have b32046 := hb (x (-7) 4)
      have b32047 := hb (x (-3) 11)
      have b32048 := hb (x (-4) 1 && x (-4) 12)
      have b32049 := hb (x (-5) 2 && x (-5) 13)
      have b32050 := hb (x (-6) 3 && x (-6) 14)
      clear * - r32045 b32046 b32047 b32048 b32049 b32050 g2 d32028 d32040 d31875
      omega
    have d32051 : (x (-5) 13).toNat = 1 := by
      have r32052 := hand2 (x (-5) 2) (x (-5) 13)
      have b32053 := hb (x (-5) 13)
      have b32054 := hb (x (-5) 2 && x (-5) 13)
      clear * - r32052 b32053 b32054 d32044
      omega
    have d32055 : (x (-4) 12).toNat = 0 := by
      have r32056 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
      have e32057 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e32058 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b32059 := hb (x (-7) 3)
      have b32060 := hb (x (-6) 2)
      have b32061 := hb (x (-5) 13)
      have b32062 := hb (x (-4) 12)
      clear * - r32056 e32057 e32058 b32059 b32060 b32061 b32062 d32051
      omega
    have d32063 : (x (-7) 1 && x (-7) 14).toNat = 1 := by
      have r32064 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := hcov13 (-6)
      have b32065 := hb (x (-8) 2)
      have b32066 := hb (x (-6) 13)
      have b32067 := hb (x (-7) 1 && x (-7) 14)
      clear * - r32064 b32065 b32066 b32067 d31916 d31766
      omega
    have d32068 : (x (-7) 14).toNat = 1 := by
      have r32069 := hand2 (x (-7) 1) (x (-7) 14)
      have b32070 := hb (x (-7) 14)
      have b32071 := hb (x (-7) 1 && x (-7) 14)
      clear * - r32069 b32070 b32071 d32063
      omega
    have d32072 : (x (-7) 1).toNat = 1 := by
      have r32073 := hand1 (x (-7) 1) (x (-7) 14)
      have b32074 := hb (x (-7) 1)
      have b32075 := hb (x (-7) 1 && x (-7) 14)
      clear * - r32073 b32074 b32075 d32063
      omega
    have d32076 : (x (-6) 14).toNat = 0 := by
      have r32077 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := hd14 (-6)
      have b32078 := hb (x (-7) 1)
      have b32079 := hb (x (-6) 14)
      clear * - r32077 b32078 b32079 d32072
      omega
    have d32080 : (x 6 1).toNat = 0 := by
      have r32081 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := hcount 7
      have b32082 := hb (x (-7) 14)
      have b32083 := hb (x (-6) 13)
      have b32084 := hb (x (-5) 12)
      have b32085 := hb (x (-4) 11)
      have b32086 := hb (x (-3) 10)
      have b32087 := hb (x (-2) 9)
      have b32088 := hb (x (-1) 8)
      have b32089 := hb (x 0 7)
      have b32090 := hb (x 1 6)
      have b32091 := hb (x 2 5)
      have b32092 := hb (x 3 4)
      have b32093 := hb (x 4 3)
      have b32094 := hb (x 5 2)
      have b32095 := hb (x 6 1)
      clear * - r32081 b32082 b32083 b32084 b32085 b32086 b32087 b32088 b32089 b32090 b32091 b32092 b32093 b32094 b32095 g32 g21 g14 g8 g3 g1 g0 d31912 d31916 d32068
      omega
    have d32096 : (x 6 1 && x 6 14).toNat = 0 := by
      have r32097 := hand1 (x 6 1) (x 6 14)
      have b32098 := hb (x 6 1)
      have b32099 := hb (x 6 1 && x 6 14)
      clear * - r32097 b32098 b32099 d32080
      omega
    have d32100 : (x 6 13).toNat = 0 := by
      have r32101 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b32102 := hb (x 6 1)
      have b32103 := hb (x 6 13)
      clear * - r32101 b32102 b32103 d32080
      omega
    have d32104 : (x 6 5).toNat = 0 := by
      have r32105 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
      have b32106 := hb (x 6 5)
      have b32107 := hb (x 6 13)
      clear * - r32105 b32106 b32107 d32100
      omega
    have d32108 : (x 6 9).toNat = 0 := by
      have r32109 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
      have b32110 := hb (x 6 1)
      have b32111 := hb (x 6 9)
      clear * - r32109 b32110 b32111 d32080
      omega
    have d32112 : (x 6 3 && x 6 9).toNat = 0 := by
      have r32113 := hand2 (x 6 3) (x 6 9)
      have b32114 := hb (x 6 9)
      have b32115 := hb (x 6 3 && x 6 9)
      clear * - r32113 b32114 b32115 d32108
      omega
    have d32116 : (x 5 2).toNat = 0 := by
      have r32117 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := hcount 7
      have b32118 := hb (x (-7) 14)
      have b32119 := hb (x (-6) 13)
      have b32120 := hb (x (-5) 12)
      have b32121 := hb (x (-4) 11)
      have b32122 := hb (x (-3) 10)
      have b32123 := hb (x (-2) 9)
      have b32124 := hb (x (-1) 8)
      have b32125 := hb (x 0 7)
      have b32126 := hb (x 1 6)
      have b32127 := hb (x 2 5)
      have b32128 := hb (x 3 4)
      have b32129 := hb (x 4 3)
      have b32130 := hb (x 5 2)
      have b32131 := hb (x 6 1)
      clear * - r32117 b32118 b32119 b32120 b32121 b32122 b32123 b32124 b32125 b32126 b32127 b32128 b32129 b32130 b32131 d32080 g32 g21 g14 g8 g3 g1 g0 d31912 d31916 d32068
      omega
    have d32132 : (x 5 10).toNat = 0 := by
      have r32133 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
      have b32134 := hb (x 5 2)
      have b32135 := hb (x 5 10)
      clear * - r32133 b32134 b32135 d32116
      omega
    have d32136 : (x 5 1 && x 5 10).toNat = 0 := by
      have r32137 := hand2 (x 5 1) (x 5 10)
      have b32138 := hb (x 5 10)
      have b32139 := hb (x 5 1 && x 5 10)
      clear * - r32137 b32138 b32139 d32132
      omega
    have d32140 : (x 4 2 && x 4 11).toNat = 1 := by
      have r32141 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
      have b32142 := hb (x 0 6)
      have b32143 := hb (x 6 9)
      have b32144 := hb (x 5 1 && x 5 10)
      have b32145 := hb (x 4 2 && x 4 11)
      have b32146 := hb (x 3 3 && x 3 12)
      have b32147 := hb (x 2 4 && x 2 13)
      have b32148 := hb (x 1 5 && x 1 14)
      clear * - r32141 b32142 b32143 b32144 b32145 b32146 b32147 b32148 d32108 d32136 g77 g78 g79 g13
      omega
    have d32149 : (x 4 11).toNat = 1 := by
      have r32150 := hand2 (x 4 2) (x 4 11)
      have b32151 := hb (x 4 11)
      have b32152 := hb (x 4 2 && x 4 11)
      clear * - r32150 b32151 b32152 d32140
      omega
    have d32153 : (x 4 2).toNat = 1 := by
      have r32154 := hand1 (x 4 2) (x 4 11)
      have b32155 := hb (x 4 2)
      have b32156 := hb (x 4 2 && x 4 11)
      clear * - r32154 b32155 b32156 d32140
      omega
    have d32157 : (x 4 14).toNat = 1 := by
      have r32158 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b32159 := hb (x 4 2)
      have b32160 := hb (x 4 14)
      clear * - r32158 b32159 b32160 d32153
      omega
    have d32161 : (x 3 1).toNat = 0 := by
      have r32162 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
      have b32163 := hb (x 3 1)
      have b32164 := hb (x 4 14)
      clear * - r32162 b32163 b32164 d32157
      omega
    have d32165 : (x 3 1 && x 3 11).toNat = 0 := by
      have r32166 := hand1 (x 3 1) (x 3 11)
      have b32167 := hb (x 3 1)
      have b32168 := hb (x 3 1 && x 3 11)
      clear * - r32166 b32167 b32168 d32161
      omega
    have d32169 : (x 4 10).toNat = 1 := by
      have r32170 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := hcov10 4
      have b32171 := hb (x (-1) 5)
      have b32172 := hb (x 4 10)
      have b32173 := hb (x 3 1 && x 3 11)
      have b32174 := hb (x 2 2 && x 2 12)
      have b32175 := hb (x 1 3 && x 1 13)
      have b32176 := hb (x 0 4 && x 0 14)
      clear * - r32170 b32171 b32172 b32173 b32174 b32175 b32176 d32165 g81 g82 g83 g7
      omega
    have d32177 : (x 6 8).toNat = 0 := by
      have r32178 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e32179 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e32180 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e32181 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e32182 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e32183 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e32184 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b32185 := hb (x (-1) 7)
      have b32186 := hb (x 0 6)
      have b32187 := hb (x 1 5)
      have b32188 := hb (x 2 4)
      have b32189 := hb (x 3 11)
      have b32190 := hb (x 4 10)
      have b32191 := hb (x 5 9)
      have b32192 := hb (x 6 8)
      clear * - r32178 e32179 e32180 e32181 e32182 e32183 e32184 b32185 b32186 b32187 b32188 b32189 b32190 b32191 b32192 d32169 g26 g20 g13 f31569
      omega
    have d32193 : (x 5 9).toNat = 0 := by
      have r32194 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e32195 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e32196 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e32197 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e32198 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e32199 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e32200 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b32201 := hb (x (-1) 7)
      have b32202 := hb (x 0 6)
      have b32203 := hb (x 1 5)
      have b32204 := hb (x 2 4)
      have b32205 := hb (x 3 11)
      have b32206 := hb (x 4 10)
      have b32207 := hb (x 5 9)
      have b32208 := hb (x 6 8)
      clear * - r32194 e32195 e32196 e32197 e32198 e32199 e32200 b32201 b32202 b32203 b32204 b32205 b32206 b32207 b32208 d32177 d32169 g26 g20 g13 f31569
      omega
    have d32209 : (x 3 11).toNat = 0 := by
      have r32210 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e32211 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e32212 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e32213 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e32214 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e32215 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e32216 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b32217 := hb (x (-1) 7)
      have b32218 := hb (x 0 6)
      have b32219 := hb (x 1 5)
      have b32220 := hb (x 2 4)
      have b32221 := hb (x 3 11)
      have b32222 := hb (x 4 10)
      have b32223 := hb (x 5 9)
      have b32224 := hb (x 6 8)
      clear * - r32210 e32211 e32212 e32213 e32214 e32215 e32216 b32217 b32218 b32219 b32220 b32221 b32222 b32223 b32224 d32177 d32193 d32169 g26 g20 g13 f31569
      omega
    have d32225 : (x 3 13).toNat = 0 := by
      have r32226 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b32227 := hb (x 3 1)
      have b32228 := hb (x 3 13)
      clear * - r32226 b32227 b32228 d32161
      omega
    have d32229 : (x 3 3 && x 3 13).toNat = 0 := by
      have r32230 := hand2 (x 3 3) (x 3 13)
      have b32231 := hb (x 3 13)
      have b32232 := hb (x 3 3 && x 3 13)
      clear * - r32230 b32231 b32232 d32225
      omega
    have d32233 : (x 3 5).toNat = 0 := by
      have r32234 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b32235 := hb (x 3 5)
      have b32236 := hb (x 3 13)
      clear * - r32234 b32235 b32236 d32225
      omega
    have d32237 : (x 6 12).toNat = 0 := by
      have r32238 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e32239 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e32240 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b32241 := hb (x 3 3)
      have b32242 := hb (x 4 2)
      have b32243 := hb (x 5 13)
      have b32244 := hb (x 6 12)
      clear * - r32238 e32239 e32240 b32241 b32242 b32243 b32244 d32153
      omega
    have d32245 : (x 6 2 && x 6 12).toNat = 0 := by
      have r32246 := hand2 (x 6 2) (x 6 12)
      have b32247 := hb (x 6 12)
      have b32248 := hb (x 6 2 && x 6 12)
      clear * - r32246 b32247 b32248 d32237
      omega
    have d32249 : (x 5 13).toNat = 0 := by
      have r32250 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e32251 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e32252 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b32253 := hb (x 3 3)
      have b32254 := hb (x 4 2)
      have b32255 := hb (x 5 13)
      have b32256 := hb (x 6 12)
      clear * - r32250 e32251 e32252 b32253 b32254 b32255 b32256 d32237 d32153
      omega
    have d32257 : (x 5 3 && x 5 13).toNat = 0 := by
      have r32258 := hand2 (x 5 3) (x 5 13)
      have b32259 := hb (x 5 13)
      have b32260 := hb (x 5 3 && x 5 13)
      clear * - r32258 b32259 b32260 d32249
      omega
    have d32261 : (x 4 1 && x 4 14).toNat = 1 := by
      have r32262 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
      have b32263 := hb (x 3 2)
      have b32264 := hb (x 5 13)
      have b32265 := hb (x 4 1 && x 4 14)
      clear * - r32262 b32263 b32264 b32265 d32249 g31
      omega
    have d32266 : (x 4 1).toNat = 1 := by
      have r32267 := hand1 (x 4 1) (x 4 14)
      have b32268 := hb (x 4 1)
      have b32269 := hb (x 4 1 && x 4 14)
      clear * - r32267 b32268 b32269 d32261
      omega
    have d32270 : (x 5 14).toNat = 0 := by
      have r32271 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
      have b32272 := hb (x 4 1)
      have b32273 := hb (x 5 14)
      clear * - r32271 b32272 b32273 d32266
      omega
    have d32274 : (x 5 6).toNat = 0 := by
      have r32275 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
      have b32276 := hb (x 5 6)
      have b32277 := hb (x 5 14)
      clear * - r32275 b32276 b32277 d32270
      omega
    have d32278 : (x 5 1 && x 5 6).toNat = 0 := by
      have r32279 := hand2 (x 5 1) (x 5 6)
      have b32280 := hb (x 5 6)
      have b32281 := hb (x 5 1 && x 5 6)
      clear * - r32279 b32280 b32281 d32274
      omega
    have d32282 : (x 5 4 && x 5 10).toNat = 0 := by
      have r32283 := hand2 (x 5 4) (x 5 10)
      have b32284 := hb (x 5 10)
      have b32285 := hb (x 5 4 && x 5 10)
      clear * - r32283 b32284 b32285 d32132
      omega
    have d32286 : (x 7 8).toNat = 0 := by
      have r32287 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
      have e32288 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e32289 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e32290 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e32291 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e32292 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e32293 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b32294 := hb (x 0 7)
      have b32295 := hb (x 1 6)
      have b32296 := hb (x 2 5)
      have b32297 := hb (x 3 4)
      have b32298 := hb (x 4 11)
      have b32299 := hb (x 5 10)
      have b32300 := hb (x 6 9)
      have b32301 := hb (x 7 8)
      clear * - r32287 e32288 e32289 e32290 e32291 e32292 e32293 b32294 b32295 b32296 b32297 b32298 b32299 b32300 b32301 d32108 d32132 d32149 g32 g21 g14
      omega
    have d32302 : (x 7 2 && x 7 8).toNat = 0 := by
      have r32303 := hand2 (x 7 2) (x 7 8)
      have b32304 := hb (x 7 8)
      have b32305 := hb (x 7 2 && x 7 8)
      clear * - r32303 b32304 b32305 d32286
      omega
    have d32306 : (x 7 13).toNat = 1 := by
      have r32307 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
      have b32308 := hb (x 5 2)
      have b32309 := hb (x 7 13)
      have b32310 := hb (x 6 1 && x 6 14)
      clear * - r32307 b32308 b32309 b32310 d32096 d32116
      omega
    have d32311 : (x 7 1).toNat = 1 := by
      have r32312 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b32313 := hb (x 7 1)
      have b32314 := hb (x 7 13)
      clear * - r32312 b32313 b32314 d32306
      omega
    have d32315 : (x 8 14).toNat = 0 := by
      have r32316 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
      have b32317 := hb (x 7 1)
      have b32318 := hb (x 8 14)
      clear * - r32316 b32317 b32318 d32311
      omega
    have d32319 : (x 8 1 && x 8 14).toNat = 0 := by
      have r32320 := hand2 (x 8 1) (x 8 14)
      have b32321 := hb (x 8 14)
      have b32322 := hb (x 8 1 && x 8 14)
      clear * - r32320 b32321 b32322 d32315
      omega
    have d32323 : (x 8 3 && x 8 14).toNat = 0 := by
      have r32324 := hand2 (x 8 3) (x 8 14)
      have b32325 := hb (x 8 14)
      have b32326 := hb (x 8 3 && x 8 14)
      clear * - r32324 b32325 b32326 d32315
      omega
    have d32327 : (x 8 7 && x 8 14).toNat = 0 := by
      have r32328 := hand2 (x 8 7) (x 8 14)
      have b32329 := hb (x 8 14)
      have b32330 := hb (x 8 7 && x 8 14)
      clear * - r32328 b32329 b32330 d32315
      omega
    have d32331 : (x 8 6).toNat = 0 := by
      have r32332 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
      have b32333 := hb (x 8 6)
      have b32334 := hb (x 8 14)
      clear * - r32332 b32333 b32334 d32315
      omega
    have d32335 : (x 8 2).toNat = 0 := by
      have r32336 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
      have b32337 := hb (x 8 2)
      have b32338 := hb (x 8 14)
      clear * - r32336 b32337 b32338 d32315
      omega
    have d32339 : (x 8 10).toNat = 0 := by
      have r32340 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
      have b32341 := hb (x 8 2)
      have b32342 := hb (x 8 10)
      clear * - r32340 b32341 b32342 d32335
      omega
    have d32343 : (x 6 2).toNat = 0 := by
      have r32344 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := hcount 8
      have b32345 := hb (x (-6) 14)
      have b32346 := hb (x (-5) 13)
      have b32347 := hb (x (-4) 12)
      have b32348 := hb (x (-3) 11)
      have b32349 := hb (x (-2) 10)
      have b32350 := hb (x (-1) 9)
      have b32351 := hb (x 0 8)
      have b32352 := hb (x 1 7)
      have b32353 := hb (x 2 6)
      have b32354 := hb (x 3 5)
      have b32355 := hb (x 4 4)
      have b32356 := hb (x 5 3)
      have b32357 := hb (x 6 2)
      have b32358 := hb (x 7 1)
      clear * - r32344 b32345 b32346 b32347 b32348 b32349 b32350 b32351 b32352 b32353 b32354 b32355 b32356 b32357 b32358 d32311 d32233 g15 g9 g4 g2 d32055 d32051 d32076
      omega
    have d32359 : (x 6 10).toNat = 0 := by
      have r32360 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
      have b32361 := hb (x 6 2)
      have b32362 := hb (x 6 10)
      clear * - r32360 b32361 b32362 d32343
      omega
    have d32363 : (x 6 3 && x 6 10).toNat = 0 := by
      have r32364 := hand2 (x 6 3) (x 6 10)
      have b32365 := hb (x 6 10)
      have b32366 := hb (x 6 3 && x 6 10)
      clear * - r32364 b32365 b32366 d32359
      omega
    have d32367 : (x 5 3).toNat = 0 := by
      have r32368 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := hcount 8
      have b32369 := hb (x (-6) 14)
      have b32370 := hb (x (-5) 13)
      have b32371 := hb (x (-4) 12)
      have b32372 := hb (x (-3) 11)
      have b32373 := hb (x (-2) 10)
      have b32374 := hb (x (-1) 9)
      have b32375 := hb (x 0 8)
      have b32376 := hb (x 1 7)
      have b32377 := hb (x 2 6)
      have b32378 := hb (x 3 5)
      have b32379 := hb (x 4 4)
      have b32380 := hb (x 5 3)
      have b32381 := hb (x 6 2)
      have b32382 := hb (x 7 1)
      clear * - r32368 b32369 b32370 b32371 b32372 b32373 b32374 b32375 b32376 b32377 b32378 b32379 b32380 b32381 b32382 d32311 d32343 d32233 g15 g9 g4 g2 d32055 d32051 d32076
      omega
    have d32383 : (x 5 11).toNat = 0 := by
      have r32384 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
      have b32385 := hb (x 5 3)
      have b32386 := hb (x 5 11)
      clear * - r32384 b32385 b32386 d32367
      omega
    have d32387 : (x 5 1 && x 5 11).toNat = 0 := by
      have r32388 := hand2 (x 5 1) (x 5 11)
      have b32389 := hb (x 5 11)
      have b32390 := hb (x 5 1 && x 5 11)
      clear * - r32388 b32389 b32390 d32383
      omega
    have d32391 : (x 4 2 && x 4 12).toNat = 1 := by
      have r32392 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
      have b32393 := hb (x 1 5)
      have b32394 := hb (x 6 10)
      have b32395 := hb (x 5 1 && x 5 11)
      have b32396 := hb (x 4 2 && x 4 12)
      have b32397 := hb (x 3 3 && x 3 13)
      have b32398 := hb (x 2 4 && x 2 14)
      clear * - r32392 b32393 b32394 b32395 b32396 b32397 b32398 d32359 d32387 d32229 g86 g20
      omega
    have d32399 : (x 4 12).toNat = 1 := by
      have r32400 := hand2 (x 4 2) (x 4 12)
      have b32401 := hb (x 4 12)
      have b32402 := hb (x 4 2 && x 4 12)
      clear * - r32400 b32401 b32402 d32391
      omega
    have d32403 : (x 2 2).toNat = 0 := by
      have r32404 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e32405 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e32406 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b32407 := hb (x 1 3)
      have b32408 := hb (x 2 2)
      have b32409 := hb (x 3 13)
      have b32410 := hb (x 4 12)
      clear * - r32404 e32405 e32406 b32407 b32408 b32409 b32410 d32399 d32225 g19
      omega
    have d32411 : (x 4 13).toNat = 1 := by
      have r32412 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
      have b32413 := hb (x 2 2)
      have b32414 := hb (x 4 13)
      have b32415 := hb (x 3 1 && x 3 14)
      clear * - r32412 b32413 b32414 b32415 g88 d32403
      omega
    have d32416 : (x 5 12).toNat = 0 := by
      have r32417 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
      have e32418 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e32419 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b32420 := hb (x 2 3)
      have b32421 := hb (x 3 2)
      have b32422 := hb (x 4 13)
      have b32423 := hb (x 5 12)
      clear * - r32417 e32418 e32419 b32420 b32421 b32422 b32423 d32411 g31
      omega
    have d32424 : (x 5 4).toNat = 0 := by
      have r32425 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b32426 := hb (x 5 4)
      have b32427 := hb (x 5 12)
      clear * - r32425 b32426 b32427 d32416
      omega
    have d32428 : (x 5 4 && x 5 11).toNat = 0 := by
      have r32429 := hand1 (x 5 4) (x 5 11)
      have b32430 := hb (x 5 4)
      have b32431 := hb (x 5 4 && x 5 11)
      clear * - r32429 b32430 b32431 d32424
      omega
    have d32432 : (x 5 1 && x 5 4).toNat = 0 := by
      have r32433 := hand2 (x 5 1) (x 5 4)
      have b32434 := hb (x 5 4)
      have b32435 := hb (x 5 1 && x 5 4)
      clear * - r32433 b32434 b32435 d32424
      omega
    have d32436 : (x 4 4).toNat = 0 := by
      have r32437 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := hcount 8
      have b32438 := hb (x (-6) 14)
      have b32439 := hb (x (-5) 13)
      have b32440 := hb (x (-4) 12)
      have b32441 := hb (x (-3) 11)
      have b32442 := hb (x (-2) 10)
      have b32443 := hb (x (-1) 9)
      have b32444 := hb (x 0 8)
      have b32445 := hb (x 1 7)
      have b32446 := hb (x 2 6)
      have b32447 := hb (x 3 5)
      have b32448 := hb (x 4 4)
      have b32449 := hb (x 5 3)
      have b32450 := hb (x 6 2)
      have b32451 := hb (x 7 1)
      clear * - r32437 b32438 b32439 b32440 b32441 b32442 b32443 b32444 b32445 b32446 b32447 b32448 b32449 b32450 b32451 d32311 d32343 d32367 d32233 g15 g9 g4 g2 d32055 d32051 d32076
      omega
    have d32452 : (x 4 4 && x 4 14).toNat = 0 := by
      have r32453 := hand1 (x 4 4) (x 4 14)
      have b32454 := hb (x 4 4)
      have b32455 := hb (x 4 4 && x 4 14)
      clear * - r32453 b32454 b32455 d32436
      omega
    have d32456 : (x 7 1 && x 7 11).toNat = 1 := by
      have r32457 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := hcov10 8
      have b32458 := hb (x 3 5)
      have b32459 := hb (x 8 10)
      have b32460 := hb (x 7 1 && x 7 11)
      have b32461 := hb (x 6 2 && x 6 12)
      have b32462 := hb (x 5 3 && x 5 13)
      have b32463 := hb (x 4 4 && x 4 14)
      clear * - r32457 b32458 b32459 b32460 b32461 b32462 b32463 d32339 d32245 d32257 d32452 d32233
      omega
    have d32464 : (x 7 11).toNat = 1 := by
      have r32465 := hand2 (x 7 1) (x 7 11)
      have b32466 := hb (x 7 11)
      have b32467 := hb (x 7 1 && x 7 11)
      clear * - r32465 b32466 b32467 d32456
      omega
    have d32468 : (x 7 3).toNat = 1 := by
      have r32469 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b32470 := hb (x 7 3)
      have b32471 := hb (x 7 11)
      clear * - r32469 b32470 b32471 d32464
      omega
    have d32472 : (x 10 12).toNat = 0 := by
      have r32473 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e32474 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e32475 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b32476 := hb (x 7 3)
      have b32477 := hb (x 8 2)
      have b32478 := hb (x 9 13)
      have b32479 := hb (x 10 12)
      clear * - r32473 e32474 e32475 b32476 b32477 b32478 b32479 d32335 d32468
      omega
    have d32480 : (x 10 1 && x 10 12).toNat = 0 := by
      have r32481 := hand2 (x 10 1) (x 10 12)
      have b32482 := hb (x 10 12)
      have b32483 := hb (x 10 1 && x 10 12)
      clear * - r32481 b32482 b32483 d32472
      omega
    have d32484 : (x 10 5 && x 10 12).toNat = 0 := by
      have r32485 := hand2 (x 10 5) (x 10 12)
      have b32486 := hb (x 10 12)
      have b32487 := hb (x 10 5 && x 10 12)
      clear * - r32485 b32486 b32487 d32472
      omega
    have d32488 : (x 10 4).toNat = 0 := by
      have r32489 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
      have b32490 := hb (x 10 4)
      have b32491 := hb (x 10 12)
      clear * - r32489 b32490 b32491 d32472
      omega
    have d32492 : (x 9 13).toNat = 0 := by
      have r32493 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e32494 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e32495 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b32496 := hb (x 7 3)
      have b32497 := hb (x 8 2)
      have b32498 := hb (x 9 13)
      have b32499 := hb (x 10 12)
      clear * - r32493 e32494 e32495 b32496 b32497 b32498 b32499 d32472 d32335 d32468
      omega
    have d32500 : (x 9 2 && x 9 13).toNat = 0 := by
      have r32501 := hand2 (x 9 2) (x 9 13)
      have b32502 := hb (x 9 13)
      have b32503 := hb (x 9 2 && x 9 13)
      clear * - r32501 b32502 b32503 d32492
      omega
    have d32504 : (x 9 6 && x 9 13).toNat = 0 := by
      have r32505 := hand2 (x 9 6) (x 9 13)
      have b32506 := hb (x 9 13)
      have b32507 := hb (x 9 6 && x 9 13)
      clear * - r32505 b32506 b32507 d32492
      omega
    have d32508 : (x 9 5).toNat = 0 := by
      have r32509 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
      have b32510 := hb (x 9 5)
      have b32511 := hb (x 9 13)
      clear * - r32509 b32510 b32511 d32492
      omega
    have d32512 : (x 7 2).toNat = 1 := by
      have r32513 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
      have b32514 := hb (x 7 2)
      have b32515 := hb (x 9 13)
      have b32516 := hb (x 8 1 && x 8 14)
      clear * - r32513 b32514 b32515 b32516 d32492 d32319
      omega
    have d32517 : (x 9 12).toNat = 0 := by
      have r32518 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e32519 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e32520 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b32521 := hb (x 6 3)
      have b32522 := hb (x 7 2)
      have b32523 := hb (x 8 13)
      have b32524 := hb (x 9 12)
      clear * - r32518 e32519 e32520 b32521 b32522 b32523 b32524 d32512
      omega
    have d32525 : (x 9 2 && x 9 12).toNat = 0 := by
      have r32526 := hand2 (x 9 2) (x 9 12)
      have b32527 := hb (x 9 12)
      have b32528 := hb (x 9 2 && x 9 12)
      clear * - r32526 b32527 b32528 d32517
      omega
    have d32529 : (x 8 13).toNat = 0 := by
      have r32530 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e32531 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e32532 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b32533 := hb (x 6 3)
      have b32534 := hb (x 7 2)
      have b32535 := hb (x 8 13)
      have b32536 := hb (x 9 12)
      clear * - r32530 e32531 e32532 b32533 b32534 b32535 b32536 d32517 d32512
      omega
    have d32537 : (x 8 3 && x 8 13).toNat = 0 := by
      have r32538 := hand2 (x 8 3) (x 8 13)
      have b32539 := hb (x 8 13)
      have b32540 := hb (x 8 3 && x 8 13)
      clear * - r32538 b32539 b32540 d32529
      omega
    have d32541 : (x 6 3).toNat = 0 := by
      have r32542 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e32543 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e32544 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b32545 := hb (x 6 3)
      have b32546 := hb (x 7 2)
      have b32547 := hb (x 8 13)
      have b32548 := hb (x 9 12)
      clear * - r32542 e32543 e32544 b32545 b32546 b32547 b32548 d32517 d32529 d32512
      omega
    have d32549 : (x 8 1).toNat = 0 := by
      have r32550 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := hcount 9
      have b32551 := hb (x (-5) 14)
      have b32552 := hb (x (-4) 13)
      have b32553 := hb (x (-3) 12)
      have b32554 := hb (x (-2) 11)
      have b32555 := hb (x (-1) 10)
      have b32556 := hb (x 0 9)
      have b32557 := hb (x 1 8)
      have b32558 := hb (x 2 7)
      have b32559 := hb (x 3 6)
      have b32560 := hb (x 4 5)
      have b32561 := hb (x 5 4)
      have b32562 := hb (x 6 3)
      have b32563 := hb (x 7 2)
      have b32564 := hb (x 8 1)
      clear * - r32550 b32551 b32552 b32553 b32554 b32555 b32556 b32557 b32558 b32559 b32560 b32561 b32562 b32563 b32564 d32512 d32541 d32424 g33 g22 g16 g10 g5 d31944 d31960 d31940
      omega
    have d32565 : (x 8 1 && x 8 8).toNat = 0 := by
      have r32566 := hand1 (x 8 1) (x 8 8)
      have b32567 := hb (x 8 1)
      have b32568 := hb (x 8 1 && x 8 8)
      clear * - r32566 b32567 b32568 d32549
      omega
    have d32569 : (x 8 1 && x 8 7).toNat = 0 := by
      have r32570 := hand1 (x 8 1) (x 8 7)
      have b32571 := hb (x 8 1)
      have b32572 := hb (x 8 1 && x 8 7)
      clear * - r32570 b32571 b32572 d32549
      omega
    have d32573 : (x 4 5).toNat = 0 := by
      have r32574 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := hcount 9
      have b32575 := hb (x (-5) 14)
      have b32576 := hb (x (-4) 13)
      have b32577 := hb (x (-3) 12)
      have b32578 := hb (x (-2) 11)
      have b32579 := hb (x (-1) 10)
      have b32580 := hb (x 0 9)
      have b32581 := hb (x 1 8)
      have b32582 := hb (x 2 7)
      have b32583 := hb (x 3 6)
      have b32584 := hb (x 4 5)
      have b32585 := hb (x 5 4)
      have b32586 := hb (x 6 3)
      have b32587 := hb (x 7 2)
      have b32588 := hb (x 8 1)
      clear * - r32574 b32575 b32576 b32577 b32578 b32579 b32580 b32581 b32582 b32583 b32584 b32585 b32586 b32587 b32588 d32549 d32512 d32541 d32424 g33 g22 g16 g10 g5 d31944 d31960 d31940
      omega
    have d32589 : (x 4 5 && x 4 12).toNat = 0 := by
      have r32590 := hand1 (x 4 5) (x 4 12)
      have b32591 := hb (x 4 5)
      have b32592 := hb (x 4 5 && x 4 12)
      clear * - r32590 b32591 b32592 d32573
      omega
    have d32593 : (x 4 5 && x 4 11).toNat = 0 := by
      have r32594 := hand1 (x 4 5) (x 4 11)
      have b32595 := hb (x 4 5)
      have b32596 := hb (x 4 5 && x 4 11)
      clear * - r32594 b32595 b32596 d32573
      omega
    have d32597 : (x 4 2 && x 4 5).toNat = 0 := by
      have r32598 := hand2 (x 4 2) (x 4 5)
      have b32599 := hb (x 4 5)
      have b32600 := hb (x 4 2 && x 4 5)
      clear * - r32598 b32599 b32600 d32573
      omega
    have d32601 : (x (-5) 11 && x (-5) 14).toNat = 1 := by
      have r32602 : 1 ≤ (x 6 3).toNat + (x 5 1 && x 5 4).toNat + (x 4 2 && x 4 5).toNat + (x 3 3 && x 3 6).toNat + (x 2 4 && x 2 7).toNat + (x 1 5 && x 1 8).toNat + (x 0 6 && x 0 9).toNat + (x (-1) 7 && x (-1) 10).toNat + (x (-2) 8 && x (-2) 11).toNat + (x (-3) 9 && x (-3) 12).toNat + (x (-4) 10 && x (-4) 13).toNat + (x (-5) 11 && x (-5) 14).toNat + (x (-6) 12).toNat := hcov3 6
      have b32603 := hb (x (-6) 12)
      have b32604 := hb (x 6 3)
      have b32605 := hb (x 5 1 && x 5 4)
      have b32606 := hb (x 4 2 && x 4 5)
      have b32607 := hb (x 3 3 && x 3 6)
      have b32608 := hb (x 2 4 && x 2 7)
      have b32609 := hb (x 1 5 && x 1 8)
      have b32610 := hb (x 0 6 && x 0 9)
      have b32611 := hb (x (-1) 7 && x (-1) 10)
      have b32612 := hb (x (-2) 8 && x (-2) 11)
      have b32613 := hb (x (-3) 9 && x (-3) 12)
      have b32614 := hb (x (-4) 10 && x (-4) 13)
      have b32615 := hb (x (-5) 11 && x (-5) 14)
      clear * - r32602 b32603 b32604 b32605 b32606 b32607 b32608 b32609 b32610 b32611 b32612 b32613 b32614 b32615 d32541 d32432 d32597 g36 g37 g38 g39 d31582 g40 d31956 d32011 d31822
      omega
    have d32616 : (x (-5) 11).toNat = 1 := by
      have r32617 := hand1 (x (-5) 11) (x (-5) 14)
      have b32618 := hb (x (-5) 11)
      have b32619 := hb (x (-5) 11 && x (-5) 14)
      clear * - r32617 b32618 b32619 d32601
      omega
    have d32620 : (x (-2) 8).toNat = 0 := by
      have r32621 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := hd8 (-2)
      have e32622 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e32623 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e32624 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e32625 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e32626 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e32627 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have b32628 := hb (x (-9) 7)
      have b32629 := hb (x (-8) 6)
      have b32630 := hb (x (-7) 5)
      have b32631 := hb (x (-6) 4)
      have b32632 := hb (x (-5) 11)
      have b32633 := hb (x (-4) 10)
      have b32634 := hb (x (-3) 9)
      have b32635 := hb (x (-2) 8)
      clear * - r32621 e32622 e32623 e32624 e32625 e32626 e32627 b32628 b32629 b32630 b32631 b32632 b32633 b32634 b32635 d32007 d32616 d31830 d31895 d31762
      omega
    have d32636 : (x (-3) 9).toNat = 0 := by
      have r32637 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := hd8 (-2)
      have e32638 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e32639 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e32640 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e32641 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e32642 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e32643 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have b32644 := hb (x (-9) 7)
      have b32645 := hb (x (-8) 6)
      have b32646 := hb (x (-7) 5)
      have b32647 := hb (x (-6) 4)
      have b32648 := hb (x (-5) 11)
      have b32649 := hb (x (-4) 10)
      have b32650 := hb (x (-3) 9)
      have b32651 := hb (x (-2) 8)
      clear * - r32637 e32638 e32639 e32640 e32641 e32642 e32643 b32644 b32645 b32646 b32647 b32648 b32649 b32650 b32651 d32620 d32007 d32616 d31830 d31895 d31762
      omega
    have d32652 : (x (-3) 9 && x (-3) 14).toNat = 0 := by
      have r32653 := hand1 (x (-3) 9) (x (-3) 14)
      have b32654 := hb (x (-3) 9)
      have b32655 := hb (x (-3) 9 && x (-3) 14)
      clear * - r32653 b32654 b32655 d32636
      omega
    have d32656 : (x 4 2 && x 4 7).toNat = 1 := by
      have r32657 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := hcov5 6
      have b32658 := hb (x (-4) 10)
      have b32659 := hb (x 6 5)
      have b32660 := hb (x 5 1 && x 5 6)
      have b32661 := hb (x 4 2 && x 4 7)
      have b32662 := hb (x 3 3 && x 3 8)
      have b32663 := hb (x 2 4 && x 2 9)
      have b32664 := hb (x 1 5 && x 1 10)
      have b32665 := hb (x 0 6 && x 0 11)
      have b32666 := hb (x (-1) 7 && x (-1) 12)
      have b32667 := hb (x (-2) 8 && x (-2) 13)
      have b32668 := hb (x (-3) 9 && x (-3) 14)
      clear * - r32657 b32658 b32659 b32660 b32661 b32662 b32663 b32664 b32665 b32666 b32667 b32668 d32104 d32278 g54 g55 g56 g57 d31574 g58 d32652 d32007
      omega
    have d32669 : (x 4 7).toNat = 1 := by
      have r32670 := hand2 (x 4 2) (x 4 7)
      have b32671 := hb (x 4 7)
      have b32672 := hb (x 4 2 && x 4 7)
      clear * - r32670 b32671 b32672 d32656
      omega
    have d32673 : (x 11 8).toNat = 0 := by
      have r32674 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := hd8 11
      have e32675 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e32676 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e32677 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e32678 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e32679 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e32680 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b32681 := hb (x 4 7)
      have b32682 := hb (x 5 6)
      have b32683 := hb (x 6 5)
      have b32684 := hb (x 7 4)
      have b32685 := hb (x 8 11)
      have b32686 := hb (x 9 10)
      have b32687 := hb (x 10 9)
      have b32688 := hb (x 11 8)
      clear * - r32674 e32675 e32676 e32677 e32678 e32679 e32680 b32681 b32682 b32683 b32684 b32685 b32686 b32687 b32688 d32104 d32274 d32669
      omega
    have d32689 : (x 10 9).toNat = 0 := by
      have r32690 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := hd8 11
      have e32691 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e32692 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e32693 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e32694 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e32695 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e32696 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b32697 := hb (x 4 7)
      have b32698 := hb (x 5 6)
      have b32699 := hb (x 6 5)
      have b32700 := hb (x 7 4)
      have b32701 := hb (x 8 11)
      have b32702 := hb (x 9 10)
      have b32703 := hb (x 10 9)
      have b32704 := hb (x 11 8)
      clear * - r32690 e32691 e32692 e32693 e32694 e32695 e32696 b32697 b32698 b32699 b32700 b32701 b32702 b32703 b32704 d32673 d32104 d32274 d32669
      omega
    have d32705 : (x 9 10).toNat = 0 := by
      have r32706 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := hd8 11
      have e32707 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e32708 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e32709 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e32710 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e32711 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e32712 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b32713 := hb (x 4 7)
      have b32714 := hb (x 5 6)
      have b32715 := hb (x 6 5)
      have b32716 := hb (x 7 4)
      have b32717 := hb (x 8 11)
      have b32718 := hb (x 9 10)
      have b32719 := hb (x 10 9)
      have b32720 := hb (x 11 8)
      clear * - r32706 e32707 e32708 e32709 e32710 e32711 e32712 b32713 b32714 b32715 b32716 b32717 b32718 b32719 b32720 d32673 d32689 d32104 d32274 d32669
      omega
    have d32721 : (x 8 11).toNat = 0 := by
      have r32722 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := hd8 11
      have e32723 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e32724 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e32725 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e32726 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e32727 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e32728 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b32729 := hb (x 4 7)
      have b32730 := hb (x 5 6)
      have b32731 := hb (x 6 5)
      have b32732 := hb (x 7 4)
      have b32733 := hb (x 8 11)
      have b32734 := hb (x 9 10)
      have b32735 := hb (x 10 9)
      have b32736 := hb (x 11 8)
      clear * - r32722 e32723 e32724 e32725 e32726 e32727 e32728 b32729 b32730 b32731 b32732 b32733 b32734 b32735 b32736 d32673 d32689 d32705 d32104 d32274 d32669
      omega
    have d32737 : (x 7 4).toNat = 0 := by
      have r32738 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := hd8 11
      have e32739 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e32740 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e32741 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e32742 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e32743 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e32744 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b32745 := hb (x 4 7)
      have b32746 := hb (x 5 6)
      have b32747 := hb (x 6 5)
      have b32748 := hb (x 7 4)
      have b32749 := hb (x 8 11)
      have b32750 := hb (x 9 10)
      have b32751 := hb (x 10 9)
      have b32752 := hb (x 11 8)
      clear * - r32738 e32739 e32740 e32741 e32742 e32743 e32744 b32745 b32746 b32747 b32748 b32749 b32750 b32751 b32752 d32673 d32689 d32705 d32721 d32104 d32274 d32669
      omega
    have d32753 : (x 7 4 && x 7 14).toNat = 0 := by
      have r32754 := hand1 (x 7 4) (x 7 14)
      have b32755 := hb (x 7 4)
      have b32756 := hb (x 7 4 && x 7 14)
      clear * - r32754 b32755 b32756 d32737
      omega
    have d32757 : (x 11 11).toNat = 1 := by
      have r32758 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
      have b32759 := hb (x 7 4)
      have b32760 := hb (x 11 11)
      have b32761 := hb (x 10 1 && x 10 12)
      have b32762 := hb (x 9 2 && x 9 13)
      have b32763 := hb (x 8 3 && x 8 14)
      clear * - r32758 b32759 b32760 b32761 b32762 b32763 d32480 d32500 d32323 d32737
      omega
    have d32764 : (x 11 3).toNat = 1 := by
      have r32765 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
      have b32766 := hb (x 11 3)
      have b32767 := hb (x 11 11)
      clear * - r32765 b32766 b32767 d32757
      omega
    have d32768 : (x 14 12).toNat = 0 := by
      have r32769 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
      have e32770 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e32771 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b32772 := hb (x 11 3)
      have b32773 := hb (x 12 2)
      have b32774 := hb (x 13 13)
      have b32775 := hb (x 14 12)
      clear * - r32769 e32770 e32771 b32772 b32773 b32774 b32775 d32764
      omega
    have d32776 : (x 14 1 && x 14 12).toNat = 0 := by
      have r32777 := hand2 (x 14 1) (x 14 12)
      have b32778 := hb (x 14 12)
      have b32779 := hb (x 14 1 && x 14 12)
      clear * - r32777 b32778 b32779 d32768
      omega
    have d32780 : (x 13 13).toNat = 0 := by
      have r32781 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
      have e32782 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e32783 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b32784 := hb (x 11 3)
      have b32785 := hb (x 12 2)
      have b32786 := hb (x 13 13)
      have b32787 := hb (x 14 12)
      clear * - r32781 e32782 e32783 b32784 b32785 b32786 b32787 d32768 d32764
      omega
    have d32788 : (x 13 2 && x 13 13).toNat = 0 := by
      have r32789 := hand2 (x 13 2) (x 13 13)
      have b32790 := hb (x 13 13)
      have b32791 := hb (x 13 2 && x 13 13)
      clear * - r32789 b32790 b32791 d32780
      omega
    have d32792 : (x 12 2).toNat = 0 := by
      have r32793 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
      have e32794 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e32795 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b32796 := hb (x 11 3)
      have b32797 := hb (x 12 2)
      have b32798 := hb (x 13 13)
      have b32799 := hb (x 14 12)
      clear * - r32793 e32794 e32795 b32796 b32797 b32798 b32799 d32768 d32780 d32764
      omega
    have d32800 : (x 12 10).toNat = 0 := by
      have r32801 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
      have b32802 := hb (x 12 2)
      have b32803 := hb (x 12 10)
      clear * - r32801 b32802 b32803 d32792
      omega
    have d32804 : (x 12 3 && x 12 10).toNat = 0 := by
      have r32805 := hand2 (x 12 3) (x 12 10)
      have b32806 := hb (x 12 10)
      have b32807 := hb (x 12 3 && x 12 10)
      clear * - r32805 b32806 b32807 d32800
      omega
    have d32808 : (x 14 8).toNat = 0 := by
      have r32809 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
      have e32810 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e32811 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e32812 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e32813 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e32814 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e32815 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b32816 := hb (x 7 7)
      have b32817 := hb (x 8 6)
      have b32818 := hb (x 9 5)
      have b32819 := hb (x 10 4)
      have b32820 := hb (x 11 11)
      have b32821 := hb (x 12 10)
      have b32822 := hb (x 13 9)
      have b32823 := hb (x 14 8)
      clear * - r32809 e32810 e32811 e32812 e32813 e32814 e32815 b32816 b32817 b32818 b32819 b32820 b32821 b32822 b32823 d32800 d32757 d32488 d32508 d32331
      omega
    have d32824 : (x 14 1 && x 14 8).toNat = 0 := by
      have r32825 := hand2 (x 14 1) (x 14 8)
      have b32826 := hb (x 14 8)
      have b32827 := hb (x 14 1 && x 14 8)
      clear * - r32825 b32826 b32827 d32808
      omega
    have d32828 : (x 13 9).toNat = 0 := by
      have r32829 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
      have e32830 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e32831 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e32832 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e32833 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e32834 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e32835 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b32836 := hb (x 7 7)
      have b32837 := hb (x 8 6)
      have b32838 := hb (x 9 5)
      have b32839 := hb (x 10 4)
      have b32840 := hb (x 11 11)
      have b32841 := hb (x 12 10)
      have b32842 := hb (x 13 9)
      have b32843 := hb (x 14 8)
      clear * - r32829 e32830 e32831 e32832 e32833 e32834 e32835 b32836 b32837 b32838 b32839 b32840 b32841 b32842 b32843 d32808 d32800 d32757 d32488 d32508 d32331
      omega
    have d32844 : (x 13 2 && x 13 9).toNat = 0 := by
      have r32845 := hand2 (x 13 2) (x 13 9)
      have b32846 := hb (x 13 9)
      have b32847 := hb (x 13 2 && x 13 9)
      clear * - r32845 b32846 b32847 d32828
      omega
    have d32848 : (x 7 7).toNat = 0 := by
      have r32849 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
      have e32850 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e32851 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e32852 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e32853 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e32854 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e32855 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b32856 := hb (x 7 7)
      have b32857 := hb (x 8 6)
      have b32858 := hb (x 9 5)
      have b32859 := hb (x 10 4)
      have b32860 := hb (x 11 11)
      have b32861 := hb (x 12 10)
      have b32862 := hb (x 13 9)
      have b32863 := hb (x 14 8)
      clear * - r32849 e32850 e32851 e32852 e32853 e32854 e32855 b32856 b32857 b32858 b32859 b32860 b32861 b32862 b32863 d32808 d32828 d32800 d32757 d32488 d32508 d32331
      omega
    have d32864 : (x 13 1).toNat = 1 := by
      have r32865 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
      have b32866 := hb (x 0 14)
      have b32867 := hb (x 1 13)
      have b32868 := hb (x 2 12)
      have b32869 := hb (x 3 11)
      have b32870 := hb (x 4 10)
      have b32871 := hb (x 5 9)
      have b32872 := hb (x 6 8)
      have b32873 := hb (x 7 7)
      have b32874 := hb (x 8 6)
      have b32875 := hb (x 9 5)
      have b32876 := hb (x 10 4)
      have b32877 := hb (x 11 3)
      have b32878 := hb (x 12 2)
      have b32879 := hb (x 13 1)
      clear * - r32865 b32866 b32867 b32868 b32869 b32870 b32871 b32872 b32873 b32874 b32875 b32876 b32877 b32878 b32879 d32792 d32764 d32488 d32508 d32331 d32848 d32177 d32193 d32169 d32209 g28 g24 g18
      omega
    have d32880 : (x 14 14).toNat = 0 := by
      have r32881 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
      have b32882 := hb (x 13 1)
      have b32883 := hb (x 14 14)
      clear * - r32881 b32882 b32883 d32864
      omega
    have d32884 : (x 14 6).toNat = 0 := by
      have r32885 : (x 14 6).toNat ≤ (x 14 14).toNat := himp _ _ (hp6 14)
      have b32886 := hb (x 14 6)
      have b32887 := hb (x 14 14)
      clear * - r32885 b32886 b32887 d32880
      omega
    have d32888 : (x 14 2).toNat = 0 := by
      have r32889 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
      have b32890 := hb (x 14 2)
      have b32891 := hb (x 14 14)
      clear * - r32889 b32890 b32891 d32880
      omega
    have d32892 : (x 10 1).toNat = 0 := by
      have r32893 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := hcount 11
      have b32894 := hb (x (-3) 14)
      have b32895 := hb (x (-2) 13)
      have b32896 := hb (x (-1) 12)
      have b32897 := hb (x 0 11)
      have b32898 := hb (x 1 10)
      have b32899 := hb (x 2 9)
      have b32900 := hb (x 3 8)
      have b32901 := hb (x 4 7)
      have b32902 := hb (x 5 6)
      have b32903 := hb (x 6 5)
      have b32904 := hb (x 7 4)
      have b32905 := hb (x 8 3)
      have b32906 := hb (x 9 2)
      have b32907 := hb (x 10 1)
      clear * - r32893 b32894 b32895 b32896 b32897 b32898 b32899 b32900 b32901 b32902 b32903 b32904 b32905 b32906 b32907 d32737 d32104 d32274 d32669 g34 g27 g23 g17 g11 g6 d32020
      omega
    have d32908 : (x 10 1 && x 10 14).toNat = 0 := by
      have r32909 := hand1 (x 10 1) (x 10 14)
      have b32910 := hb (x 10 1)
      have b32911 := hb (x 10 1 && x 10 14)
      clear * - r32909 b32910 b32911 d32892
      omega
    have d32912 : (x 10 1 && x 10 11).toNat = 0 := by
      have r32913 := hand1 (x 10 1) (x 10 11)
      have b32914 := hb (x 10 1)
      have b32915 := hb (x 10 1 && x 10 11)
      clear * - r32913 b32914 b32915 d32892
      omega
    have d32916 : (x 11 10).toNat = 1 := by
      have r32917 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := hcov10 11
      have b32918 := hb (x 6 5)
      have b32919 := hb (x 11 10)
      have b32920 := hb (x 10 1 && x 10 11)
      have b32921 := hb (x 9 2 && x 9 12)
      have b32922 := hb (x 8 3 && x 8 13)
      have b32923 := hb (x 7 4 && x 7 14)
      clear * - r32917 b32918 b32919 b32920 b32921 b32922 b32923 d32912 d32525 d32537 d32753 d32104
      omega
    have d32924 : (x 11 2).toNat = 1 := by
      have r32925 : (x 11 10).toNat ≤ (x 11 2).toNat := himp _ _ (hp10 11)
      have b32926 := hb (x 11 2)
      have b32927 := hb (x 11 10)
      clear * - r32925 b32926 b32927 d32916
      omega
    have d32928 : (x 13 12).toNat = 0 := by
      have r32929 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
      have e32930 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e32931 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b32932 := hb (x 10 3)
      have b32933 := hb (x 11 2)
      have b32934 := hb (x 12 13)
      have b32935 := hb (x 13 12)
      clear * - r32929 e32930 e32931 b32932 b32933 b32934 b32935 d32924
      omega
    have d32936 : (x 13 2 && x 13 12).toNat = 0 := by
      have r32937 := hand2 (x 13 2) (x 13 12)
      have b32938 := hb (x 13 12)
      have b32939 := hb (x 13 2 && x 13 12)
      clear * - r32937 b32938 b32939 d32928
      omega
    have d32940 : (x 12 13).toNat = 0 := by
      have r32941 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
      have e32942 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e32943 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b32944 := hb (x 10 3)
      have b32945 := hb (x 11 2)
      have b32946 := hb (x 12 13)
      have b32947 := hb (x 13 12)
      clear * - r32941 e32942 e32943 b32944 b32945 b32946 b32947 d32928 d32924
      omega
    have d32948 : (x 12 3 && x 12 13).toNat = 0 := by
      have r32949 := hand2 (x 12 3) (x 12 13)
      have b32950 := hb (x 12 13)
      have b32951 := hb (x 12 3 && x 12 13)
      clear * - r32949 b32950 b32951 d32940
      omega
    have d32952 : (x 10 13).toNat = 0 := by
      have r32953 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b32954 := hb (x 10 1)
      have b32955 := hb (x 10 13)
      clear * - r32953 b32954 b32955 d32892
      omega
    have d32956 : (x 10 5).toNat = 0 := by
      have r32957 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
      have b32958 := hb (x 10 5)
      have b32959 := hb (x 10 13)
      clear * - r32957 b32958 b32959 d32952
      omega
    have d32960 : (x 9 1 && x 9 14).toNat = 1 := by
      have r32961 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
      have b32962 := hb (x 8 2)
      have b32963 := hb (x 10 13)
      have b32964 := hb (x 9 1 && x 9 14)
      clear * - r32961 b32962 b32963 b32964 d32952 d32335
      omega
    have d32965 : (x 9 1).toNat = 1 := by
      have r32966 := hand1 (x 9 1) (x 9 14)
      have b32967 := hb (x 9 1)
      have b32968 := hb (x 9 1 && x 9 14)
      clear * - r32966 b32967 b32968 d32960
      omega
    have d32969 : (x 10 14).toNat = 0 := by
      have r32970 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
      have b32971 := hb (x 9 1)
      have b32972 := hb (x 10 14)
      clear * - r32970 b32971 b32972 d32965
      omega
    have d32973 : (x 10 6).toNat = 0 := by
      have r32974 : (x 10 6).toNat ≤ (x 10 14).toNat := himp _ _ (hp6 10)
      have b32975 := hb (x 10 6)
      have b32976 := hb (x 10 14)
      clear * - r32974 b32975 b32976 d32969
      omega
    have d32977 : (x 10 2).toNat = 0 := by
      have r32978 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
      have b32979 := hb (x 10 2)
      have b32980 := hb (x 10 14)
      clear * - r32978 b32979 b32980 d32969
      omega
    have d32981 : (x 11 1 && x 11 14).toNat = 1 := by
      have r32982 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
      have b32983 := hb (x 10 2)
      have b32984 := hb (x 12 13)
      have b32985 := hb (x 11 1 && x 11 14)
      clear * - r32982 b32983 b32984 b32985 d32940 d32977
      omega
    have d32986 : (x 11 1).toNat = 1 := by
      have r32987 := hand1 (x 11 1) (x 11 14)
      have b32988 := hb (x 11 1)
      have b32989 := hb (x 11 1 && x 11 14)
      clear * - r32987 b32988 b32989 d32981
      omega
    have d32990 : (x 12 14).toNat = 0 := by
      have r32991 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
      have b32992 := hb (x 11 1)
      have b32993 := hb (x 12 14)
      clear * - r32991 b32992 b32993 d32986
      omega
    have d32994 : (x 12 3 && x 12 14).toNat = 0 := by
      have r32995 := hand2 (x 12 3) (x 12 14)
      have b32996 := hb (x 12 14)
      have b32997 := hb (x 12 3 && x 12 14)
      clear * - r32995 b32996 b32997 d32990
      omega
    have d32998 : (x 9 2).toNat = 0 := by
      have r32999 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := hcount 11
      have b33000 := hb (x (-3) 14)
      have b33001 := hb (x (-2) 13)
      have b33002 := hb (x (-1) 12)
      have b33003 := hb (x 0 11)
      have b33004 := hb (x 1 10)
      have b33005 := hb (x 2 9)
      have b33006 := hb (x 3 8)
      have b33007 := hb (x 4 7)
      have b33008 := hb (x 5 6)
      have b33009 := hb (x 6 5)
      have b33010 := hb (x 7 4)
      have b33011 := hb (x 8 3)
      have b33012 := hb (x 9 2)
      have b33013 := hb (x 10 1)
      clear * - r32999 b33000 b33001 b33002 b33003 b33004 b33005 b33006 b33007 b33008 b33009 b33010 b33011 b33012 b33013 d32892 d32737 d32104 d32274 d32669 g34 g27 g23 g17 g11 g6 d32020
      omega
    have d33014 : (x 11 13).toNat = 1 := by
      have r33015 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
      have b33016 := hb (x 9 2)
      have b33017 := hb (x 11 13)
      have b33018 := hb (x 10 1 && x 10 14)
      clear * - r33015 b33016 b33017 b33018 d32908 d32998
      omega
    have d33019 : (x 12 12).toNat = 0 := by
      have r33020 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
      have e33021 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e33022 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b33023 := hb (x 9 3)
      have b33024 := hb (x 10 2)
      have b33025 := hb (x 11 13)
      have b33026 := hb (x 12 12)
      clear * - r33020 e33021 e33022 b33023 b33024 b33025 b33026 d33014 d32977
      omega
    have d33027 : (x 12 4).toNat = 0 := by
      have r33028 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b33029 := hb (x 12 4)
      have b33030 := hb (x 12 12)
      clear * - r33028 b33029 b33030 d33019
      omega
    have d33031 : (x 2 7).toNat = 0 := by
      have r33032 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := hcount 9
      have b33033 := hb (x (-5) 14)
      have b33034 := hb (x (-4) 13)
      have b33035 := hb (x (-3) 12)
      have b33036 := hb (x (-2) 11)
      have b33037 := hb (x (-1) 10)
      have b33038 := hb (x 0 9)
      have b33039 := hb (x 1 8)
      have b33040 := hb (x 2 7)
      have b33041 := hb (x 3 6)
      have b33042 := hb (x 4 5)
      have b33043 := hb (x 5 4)
      have b33044 := hb (x 6 3)
      have b33045 := hb (x 7 2)
      have b33046 := hb (x 8 1)
      clear * - r33032 b33033 b33034 b33035 b33036 b33037 b33038 b33039 b33040 b33041 b33042 b33043 b33044 b33045 b33046 d32549 d32512 d32541 d32424 d32573 g33 g22 g16 g10 g5 d31944 d31960 d31940
      omega
    have d33047 : (x 2 7 && x 2 14).toNat = 0 := by
      have r33048 := hand1 (x 2 7) (x 2 14)
      have b33049 := hb (x 2 7)
      have b33050 := hb (x 2 7 && x 2 14)
      clear * - r33048 b33049 b33050 d33031
      omega
    have d33051 : (x 2 7 && x 2 13).toNat = 0 := by
      have r33052 := hand1 (x 2 7) (x 2 13)
      have b33053 := hb (x 2 7)
      have b33054 := hb (x 2 7 && x 2 13)
      clear * - r33052 b33053 b33054 d33031
      omega
    have d33055 : (x 9 6).toNat = 1 := by
      have r33056 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := hcov6 9
      have b33057 := hb (x 0 9)
      have b33058 := hb (x 9 6)
      have b33059 := hb (x 8 1 && x 8 7)
      have b33060 := hb (x 7 2 && x 7 8)
      have b33061 := hb (x 6 3 && x 6 9)
      have b33062 := hb (x 5 4 && x 5 10)
      have b33063 := hb (x 4 5 && x 4 11)
      have b33064 := hb (x 3 6 && x 3 12)
      have b33065 := hb (x 2 7 && x 2 13)
      have b33066 := hb (x 1 8 && x 1 14)
      clear * - r33056 b33057 b33058 b33059 b33060 b33061 b33062 b33063 b33064 b33065 b33066 d32569 d32302 d32112 d32282 d32593 g65 d33051 g66 g16
      omega
    have d33067 : (x 15 8).toNat = 0 := by
      have r33068 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
      have e33069 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e33070 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e33071 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e33072 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e33073 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e33074 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b33075 := hb (x 8 7)
      have b33076 := hb (x 9 6)
      have b33077 := hb (x 10 5)
      have b33078 := hb (x 11 4)
      have b33079 := hb (x 12 11)
      have b33080 := hb (x 13 10)
      have b33081 := hb (x 14 9)
      have b33082 := hb (x 15 8)
      clear * - r33068 e33069 e33070 e33071 e33072 e33073 e33074 b33075 b33076 b33077 b33078 b33079 b33080 b33081 b33082 d32956 d33055
      omega
    have d33083 : (x 14 9).toNat = 0 := by
      have r33084 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
      have e33085 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e33086 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e33087 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e33088 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e33089 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e33090 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b33091 := hb (x 8 7)
      have b33092 := hb (x 9 6)
      have b33093 := hb (x 10 5)
      have b33094 := hb (x 11 4)
      have b33095 := hb (x 12 11)
      have b33096 := hb (x 13 10)
      have b33097 := hb (x 14 9)
      have b33098 := hb (x 15 8)
      clear * - r33084 e33085 e33086 e33087 e33088 e33089 e33090 b33091 b33092 b33093 b33094 b33095 b33096 b33097 b33098 d33067 d32956 d33055
      omega
    have d33099 : (x 13 10).toNat = 0 := by
      have r33100 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
      have e33101 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e33102 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e33103 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e33104 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e33105 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e33106 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b33107 := hb (x 8 7)
      have b33108 := hb (x 9 6)
      have b33109 := hb (x 10 5)
      have b33110 := hb (x 11 4)
      have b33111 := hb (x 12 11)
      have b33112 := hb (x 13 10)
      have b33113 := hb (x 14 9)
      have b33114 := hb (x 15 8)
      clear * - r33100 e33101 e33102 e33103 e33104 e33105 e33106 b33107 b33108 b33109 b33110 b33111 b33112 b33113 b33114 d33067 d33083 d32956 d33055
      omega
    have d33115 : (x 12 11).toNat = 0 := by
      have r33116 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
      have e33117 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e33118 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e33119 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e33120 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e33121 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e33122 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b33123 := hb (x 8 7)
      have b33124 := hb (x 9 6)
      have b33125 := hb (x 10 5)
      have b33126 := hb (x 11 4)
      have b33127 := hb (x 12 11)
      have b33128 := hb (x 13 10)
      have b33129 := hb (x 14 9)
      have b33130 := hb (x 15 8)
      clear * - r33116 e33117 e33118 e33119 e33120 e33121 e33122 b33123 b33124 b33125 b33126 b33127 b33128 b33129 b33130 d33067 d33083 d33099 d32956 d33055
      omega
    have d33131 : (x 11 4).toNat = 0 := by
      have r33132 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
      have e33133 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e33134 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e33135 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e33136 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e33137 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e33138 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b33139 := hb (x 8 7)
      have b33140 := hb (x 9 6)
      have b33141 := hb (x 10 5)
      have b33142 := hb (x 11 4)
      have b33143 := hb (x 12 11)
      have b33144 := hb (x 13 10)
      have b33145 := hb (x 14 9)
      have b33146 := hb (x 15 8)
      clear * - r33132 e33133 e33134 e33135 e33136 e33137 e33138 b33139 b33140 b33141 b33142 b33143 b33144 b33145 b33146 d33067 d33083 d33099 d33115 d32956 d33055
      omega
    have d33147 : (x 11 4 && x 11 14).toNat = 0 := by
      have r33148 := hand1 (x 11 4) (x 11 14)
      have b33149 := hb (x 11 4)
      have b33150 := hb (x 11 4 && x 11 14)
      clear * - r33148 b33149 b33150 d33131
      omega
    have d33151 : (x 11 4 && x 11 11).toNat = 0 := by
      have r33152 := hand1 (x 11 4) (x 11 11)
      have b33153 := hb (x 11 4)
      have b33154 := hb (x 11 4 && x 11 11)
      clear * - r33152 b33153 b33154 d33131
      omega
    have d33155 : (x 15 7).toNat = 1 := by
      have r33156 : 1 ≤ (x 15 7).toNat + (x 14 1 && x 14 8).toNat + (x 13 2 && x 13 9).toNat + (x 12 3 && x 12 10).toNat + (x 11 4 && x 11 11).toNat + (x 10 5 && x 10 12).toNat + (x 9 6 && x 9 13).toNat + (x 8 7 && x 8 14).toNat + (x 7 8).toNat := hcov7 15
      have b33157 := hb (x 7 8)
      have b33158 := hb (x 15 7)
      have b33159 := hb (x 14 1 && x 14 8)
      have b33160 := hb (x 13 2 && x 13 9)
      have b33161 := hb (x 12 3 && x 12 10)
      have b33162 := hb (x 11 4 && x 11 11)
      have b33163 := hb (x 10 5 && x 10 12)
      have b33164 := hb (x 9 6 && x 9 13)
      have b33165 := hb (x 8 7 && x 8 14)
      clear * - r33156 b33157 b33158 b33159 b33160 b33161 b33162 b33163 b33164 b33165 d32824 d32844 d32804 d33151 d32484 d32504 d32327 d32286
      omega
    have d33166 : (x 22 8).toNat = 0 := by
      have r33167 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
      have e33168 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
      have e33169 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
      have e33170 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
      have e33171 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
      have e33172 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
      have e33173 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
      have b33174 := hb (x 15 7)
      have b33175 := hb (x 16 6)
      have b33176 := hb (x 17 5)
      have b33177 := hb (x 18 4)
      have b33178 := hb (x 19 11)
      have b33179 := hb (x 20 10)
      have b33180 := hb (x 21 9)
      have b33181 := hb (x 22 8)
      clear * - r33167 e33168 e33169 e33170 e33171 e33172 e33173 b33174 b33175 b33176 b33177 b33178 b33179 b33180 b33181 d33155
      omega
    have d33182 : (x 21 9).toNat = 0 := by
      have r33183 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
      have e33184 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
      have e33185 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
      have e33186 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
      have e33187 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
      have e33188 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
      have e33189 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
      have b33190 := hb (x 15 7)
      have b33191 := hb (x 16 6)
      have b33192 := hb (x 17 5)
      have b33193 := hb (x 18 4)
      have b33194 := hb (x 19 11)
      have b33195 := hb (x 20 10)
      have b33196 := hb (x 21 9)
      have b33197 := hb (x 22 8)
      clear * - r33183 e33184 e33185 e33186 e33187 e33188 e33189 b33190 b33191 b33192 b33193 b33194 b33195 b33196 b33197 d33166 d33155
      omega
    have d33198 : (x 20 10).toNat = 0 := by
      have r33199 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
      have e33200 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
      have e33201 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
      have e33202 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
      have e33203 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
      have e33204 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
      have e33205 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
      have b33206 := hb (x 15 7)
      have b33207 := hb (x 16 6)
      have b33208 := hb (x 17 5)
      have b33209 := hb (x 18 4)
      have b33210 := hb (x 19 11)
      have b33211 := hb (x 20 10)
      have b33212 := hb (x 21 9)
      have b33213 := hb (x 22 8)
      clear * - r33199 e33200 e33201 e33202 e33203 e33204 e33205 b33206 b33207 b33208 b33209 b33210 b33211 b33212 b33213 d33166 d33182 d33155
      omega
    have d33214 : (x 20 1 && x 20 10).toNat = 0 := by
      have r33215 := hand2 (x 20 1) (x 20 10)
      have b33216 := hb (x 20 10)
      have b33217 := hb (x 20 1 && x 20 10)
      clear * - r33215 b33216 b33217 d33198
      omega
    have d33218 : (x 19 11).toNat = 0 := by
      have r33219 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := hd8 22
      have e33220 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
      have e33221 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
      have e33222 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
      have e33223 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
      have e33224 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
      have e33225 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
      have b33226 := hb (x 15 7)
      have b33227 := hb (x 16 6)
      have b33228 := hb (x 17 5)
      have b33229 := hb (x 18 4)
      have b33230 := hb (x 19 11)
      have b33231 := hb (x 20 10)
      have b33232 := hb (x 21 9)
      have b33233 := hb (x 22 8)
      clear * - r33219 e33220 e33221 e33222 e33223 e33224 e33225 b33226 b33227 b33228 b33229 b33230 b33231 b33232 b33233 d33166 d33182 d33198 d33155
      omega
    have d33234 : (x 19 2 && x 19 11).toNat = 0 := by
      have r33235 := hand2 (x 19 2) (x 19 11)
      have b33236 := hb (x 19 11)
      have b33237 := hb (x 19 2 && x 19 11)
      clear * - r33235 b33236 b33237 d33218
      omega
    have d33238 : (x 15 11).toNat = 1 := by
      have r33239 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
      have b33240 := hb (x 11 4)
      have b33241 := hb (x 15 11)
      have b33242 := hb (x 14 1 && x 14 12)
      have b33243 := hb (x 13 2 && x 13 13)
      have b33244 := hb (x 12 3 && x 12 14)
      clear * - r33239 b33240 b33241 b33242 b33243 b33244 d32776 d32788 d32994 d33131
      omega
    have d33245 : (x 15 3).toNat = 1 := by
      have r33246 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
      have b33247 := hb (x 15 3)
      have b33248 := hb (x 15 11)
      clear * - r33246 b33247 b33248 d33238
      omega
    have d33249 : (x 18 12).toNat = 0 := by
      have r33250 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
      have e33251 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e33252 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b33253 := hb (x 15 3)
      have b33254 := hb (x 16 2)
      have b33255 := hb (x 17 13)
      have b33256 := hb (x 18 12)
      clear * - r33250 e33251 e33252 b33253 b33254 b33255 b33256 d33245
      omega
    have d33257 : (x 18 3 && x 18 12).toNat = 0 := by
      have r33258 := hand2 (x 18 3) (x 18 12)
      have b33259 := hb (x 18 12)
      have b33260 := hb (x 18 3 && x 18 12)
      clear * - r33258 b33259 b33260 d33249
      omega
    have d33261 : (x 17 13).toNat = 0 := by
      have r33262 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
      have e33263 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e33264 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b33265 := hb (x 15 3)
      have b33266 := hb (x 16 2)
      have b33267 := hb (x 17 13)
      have b33268 := hb (x 18 12)
      clear * - r33262 e33263 e33264 b33265 b33266 b33267 b33268 d33249 d33245
      omega
    have d33269 : (x 17 4 && x 17 13).toNat = 0 := by
      have r33270 := hand2 (x 17 4) (x 17 13)
      have b33271 := hb (x 17 13)
      have b33272 := hb (x 17 4 && x 17 13)
      clear * - r33270 b33271 b33272 d33261
      omega
    have d33273 : (x 8 7).toNat = 0 := by
      have r33274 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
      have e33275 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e33276 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e33277 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e33278 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e33279 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e33280 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b33281 := hb (x 8 7)
      have b33282 := hb (x 9 6)
      have b33283 := hb (x 10 5)
      have b33284 := hb (x 11 4)
      have b33285 := hb (x 12 11)
      have b33286 := hb (x 13 10)
      have b33287 := hb (x 14 9)
      have b33288 := hb (x 15 8)
      clear * - r33274 e33275 e33276 e33277 e33278 e33279 e33280 b33281 b33282 b33283 b33284 b33285 b33286 b33287 b33288 d33067 d33083 d33099 d33115 d33131 d32956 d33055
      omega
    have d33289 : (x 14 1).toNat = 0 := by
      have r33290 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := hcount 15
      have b33291 := hb (x 1 14)
      have b33292 := hb (x 2 13)
      have b33293 := hb (x 3 12)
      have b33294 := hb (x 4 11)
      have b33295 := hb (x 5 10)
      have b33296 := hb (x 6 9)
      have b33297 := hb (x 7 8)
      have b33298 := hb (x 8 7)
      have b33299 := hb (x 9 6)
      have b33300 := hb (x 10 5)
      have b33301 := hb (x 11 4)
      have b33302 := hb (x 12 3)
      have b33303 := hb (x 13 2)
      have b33304 := hb (x 14 1)
      clear * - r33290 b33291 b33292 b33293 b33294 b33295 b33296 b33297 b33298 b33299 b33300 b33301 b33302 b33303 b33304 d33131 d32956 d33055 d33273 d32286 d32108 d32132 d32149 g35 g29 g25
      omega
    have d33305 : (x 14 1 && x 14 11).toNat = 0 := by
      have r33306 := hand1 (x 14 1) (x 14 11)
      have b33307 := hb (x 14 1)
      have b33308 := hb (x 14 1 && x 14 11)
      clear * - r33306 b33307 b33308 d33289
      omega
    have d33309 : (x 15 10).toNat = 1 := by
      have r33310 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := hcov10 15
      have b33311 := hb (x 10 5)
      have b33312 := hb (x 15 10)
      have b33313 := hb (x 14 1 && x 14 11)
      have b33314 := hb (x 13 2 && x 13 12)
      have b33315 := hb (x 12 3 && x 12 13)
      have b33316 := hb (x 11 4 && x 11 14)
      clear * - r33310 b33311 b33312 b33313 b33314 b33315 b33316 d33305 d32936 d32948 d33147 d32956
      omega
    have d33317 : (x 15 2).toNat = 1 := by
      have r33318 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
      have b33319 := hb (x 15 2)
      have b33320 := hb (x 15 10)
      clear * - r33318 b33319 b33320 d33309
      omega
    have d33321 : (x 17 12).toNat = 0 := by
      have r33322 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
      have e33323 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e33324 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b33325 := hb (x 14 3)
      have b33326 := hb (x 15 2)
      have b33327 := hb (x 16 13)
      have b33328 := hb (x 17 12)
      clear * - r33322 e33323 e33324 b33325 b33326 b33327 b33328 d33317
      omega
    have d33329 : (x 17 3 && x 17 12).toNat = 0 := by
      have r33330 := hand2 (x 17 3) (x 17 12)
      have b33331 := hb (x 17 12)
      have b33332 := hb (x 17 3 && x 17 12)
      clear * - r33330 b33331 b33332 d33321
      omega
    have d33333 : (x 17 4).toNat = 0 := by
      have r33334 : (x 17 4).toNat ≤ (x 17 12).toNat := himp _ _ (hp4 17)
      have b33335 := hb (x 17 4)
      have b33336 := hb (x 17 12)
      clear * - r33334 b33335 b33336 d33321
      omega
    have d33337 : (x 16 13).toNat = 0 := by
      have r33338 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
      have e33339 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e33340 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b33341 := hb (x 14 3)
      have b33342 := hb (x 15 2)
      have b33343 := hb (x 16 13)
      have b33344 := hb (x 17 12)
      clear * - r33338 e33339 e33340 b33341 b33342 b33343 b33344 d33321 d33317
      omega
    have d33345 : (x 16 4 && x 16 13).toNat = 0 := by
      have r33346 := hand2 (x 16 4) (x 16 13)
      have b33347 := hb (x 16 13)
      have b33348 := hb (x 16 4 && x 16 13)
      clear * - r33346 b33347 b33348 d33337
      omega
    have d33349 : (x 16 5).toNat = 0 := by
      have r33350 : (x 16 5).toNat ≤ (x 16 13).toNat := himp _ _ (hp5 16)
      have b33351 := hb (x 16 5)
      have b33352 := hb (x 16 13)
      clear * - r33350 b33351 b33352 d33337
      omega
    have d33353 : (x 16 5 && x 16 14).toNat = 0 := by
      have r33354 := hand1 (x 16 5) (x 16 14)
      have b33355 := hb (x 16 5)
      have b33356 := hb (x 16 5 && x 16 14)
      clear * - r33354 b33355 b33356 d33349
      omega
    have d33357 : (x 15 6).toNat = 1 := by
      have r33358 : 1 ≤ (x 21 9).toNat + (x 20 1 && x 20 10).toNat + (x 19 2 && x 19 11).toNat + (x 18 3 && x 18 12).toNat + (x 17 4 && x 17 13).toNat + (x 16 5 && x 16 14).toNat + (x 15 6).toNat := hcov9 21
      have b33359 := hb (x 15 6)
      have b33360 := hb (x 21 9)
      have b33361 := hb (x 20 1 && x 20 10)
      have b33362 := hb (x 19 2 && x 19 11)
      have b33363 := hb (x 18 3 && x 18 12)
      have b33364 := hb (x 17 4 && x 17 13)
      have b33365 := hb (x 16 5 && x 16 14)
      clear * - r33358 b33359 b33360 b33361 b33362 b33363 b33364 b33365 d33182 d33214 d33234 d33257 d33269 d33353
      omega
    have d33366 : (x 21 8).toNat = 0 := by
      have r33367 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
      have e33368 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e33369 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e33370 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e33371 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e33372 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e33373 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b33374 := hb (x 14 7)
      have b33375 := hb (x 15 6)
      have b33376 := hb (x 16 5)
      have b33377 := hb (x 17 4)
      have b33378 := hb (x 18 11)
      have b33379 := hb (x 19 10)
      have b33380 := hb (x 20 9)
      have b33381 := hb (x 21 8)
      clear * - r33367 e33368 e33369 e33370 e33371 e33372 e33373 b33374 b33375 b33376 b33377 b33378 b33379 b33380 b33381 d33333 d33349 d33357
      omega
    have d33382 : (x 20 9).toNat = 0 := by
      have r33383 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
      have e33384 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e33385 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e33386 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e33387 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e33388 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e33389 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b33390 := hb (x 14 7)
      have b33391 := hb (x 15 6)
      have b33392 := hb (x 16 5)
      have b33393 := hb (x 17 4)
      have b33394 := hb (x 18 11)
      have b33395 := hb (x 19 10)
      have b33396 := hb (x 20 9)
      have b33397 := hb (x 21 8)
      clear * - r33383 e33384 e33385 e33386 e33387 e33388 e33389 b33390 b33391 b33392 b33393 b33394 b33395 b33396 b33397 d33366 d33333 d33349 d33357
      omega
    have d33398 : (x 19 10).toNat = 0 := by
      have r33399 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
      have e33400 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e33401 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e33402 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e33403 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e33404 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e33405 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b33406 := hb (x 14 7)
      have b33407 := hb (x 15 6)
      have b33408 := hb (x 16 5)
      have b33409 := hb (x 17 4)
      have b33410 := hb (x 18 11)
      have b33411 := hb (x 19 10)
      have b33412 := hb (x 20 9)
      have b33413 := hb (x 21 8)
      clear * - r33399 e33400 e33401 e33402 e33403 e33404 e33405 b33406 b33407 b33408 b33409 b33410 b33411 b33412 b33413 d33366 d33382 d33333 d33349 d33357
      omega
    have d33414 : (x 19 1 && x 19 10).toNat = 0 := by
      have r33415 := hand2 (x 19 1) (x 19 10)
      have b33416 := hb (x 19 10)
      have b33417 := hb (x 19 1 && x 19 10)
      clear * - r33415 b33416 b33417 d33398
      omega
    have d33418 : (x 18 11).toNat = 0 := by
      have r33419 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := hd8 21
      have e33420 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
      have e33421 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
      have e33422 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
      have e33423 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
      have e33424 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
      have e33425 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
      have b33426 := hb (x 14 7)
      have b33427 := hb (x 15 6)
      have b33428 := hb (x 16 5)
      have b33429 := hb (x 17 4)
      have b33430 := hb (x 18 11)
      have b33431 := hb (x 19 10)
      have b33432 := hb (x 20 9)
      have b33433 := hb (x 21 8)
      clear * - r33419 e33420 e33421 e33422 e33423 e33424 e33425 b33426 b33427 b33428 b33429 b33430 b33431 b33432 b33433 d33366 d33382 d33398 d33333 d33349 d33357
      omega
    have d33434 : (x 18 2 && x 18 11).toNat = 0 := by
      have r33435 := hand2 (x 18 2) (x 18 11)
      have b33436 := hb (x 18 11)
      have b33437 := hb (x 18 2 && x 18 11)
      clear * - r33435 b33436 b33437 d33418
      omega
    have d33438 : (x 15 5 && x 15 14).toNat = 1 := by
      have r33439 : 1 ≤ (x 20 9).toNat + (x 19 1 && x 19 10).toNat + (x 18 2 && x 18 11).toNat + (x 17 3 && x 17 12).toNat + (x 16 4 && x 16 13).toNat + (x 15 5 && x 15 14).toNat + (x 14 6).toNat := hcov9 20
      have b33440 := hb (x 14 6)
      have b33441 := hb (x 20 9)
      have b33442 := hb (x 19 1 && x 19 10)
      have b33443 := hb (x 18 2 && x 18 11)
      have b33444 := hb (x 17 3 && x 17 12)
      have b33445 := hb (x 16 4 && x 16 13)
      have b33446 := hb (x 15 5 && x 15 14)
      clear * - r33439 b33440 b33441 b33442 b33443 b33444 b33445 b33446 d33382 d33414 d33434 d33329 d33345 d32884
      omega
    have d33447 : (x 15 5).toNat = 1 := by
      have r33448 := hand1 (x 15 5) (x 15 14)
      have b33449 := hb (x 15 5)
      have b33450 := hb (x 15 5 && x 15 14)
      clear * - r33448 b33449 b33450 d33438
      omega
    have d33451 : (x 15 13).toNat = 1 := by
      have r33452 : (x 15 5).toNat ≤ (x 15 13).toNat := himp _ _ (hp5 15)
      have b33453 := hb (x 15 5)
      have b33454 := hb (x 15 13)
      clear * - r33452 b33453 b33454 d33447
      omega
    have d33455 : (x 15 1).toNat = 1 := by
      have r33456 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b33457 := hb (x 15 1)
      have b33458 := hb (x 15 13)
      clear * - r33456 b33457 b33458 d33451
      omega
    have d33459 : (x 13 3).toNat = 0 := by
      have r33460 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := hcount 16
      have b33461 := hb (x 2 14)
      have b33462 := hb (x 3 13)
      have b33463 := hb (x 4 12)
      have b33464 := hb (x 5 11)
      have b33465 := hb (x 6 10)
      have b33466 := hb (x 7 9)
      have b33467 := hb (x 8 8)
      have b33468 := hb (x 9 7)
      have b33469 := hb (x 10 6)
      have b33470 := hb (x 11 5)
      have b33471 := hb (x 12 4)
      have b33472 := hb (x 13 3)
      have b33473 := hb (x 14 2)
      have b33474 := hb (x 15 1)
      clear * - r33460 b33461 b33462 b33463 b33464 b33465 b33466 b33467 b33468 b33469 b33470 b33471 b33472 b33473 b33474 d33455 d32888 d33027 d32973 d32359 d32383 d32399 d32225 g30
      omega
    have d33475 : (x 11 5).toNat = 0 := by
      have r33476 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := hcount 16
      have b33477 := hb (x 2 14)
      have b33478 := hb (x 3 13)
      have b33479 := hb (x 4 12)
      have b33480 := hb (x 5 11)
      have b33481 := hb (x 6 10)
      have b33482 := hb (x 7 9)
      have b33483 := hb (x 8 8)
      have b33484 := hb (x 9 7)
      have b33485 := hb (x 10 6)
      have b33486 := hb (x 11 5)
      have b33487 := hb (x 12 4)
      have b33488 := hb (x 13 3)
      have b33489 := hb (x 14 2)
      have b33490 := hb (x 15 1)
      clear * - r33476 b33477 b33478 b33479 b33480 b33481 b33482 b33483 b33484 b33485 b33486 b33487 b33488 b33489 b33490 d33455 d32888 d33459 d33027 d32973 d32359 d32383 d32399 d32225 g30
      omega
    have d33491 : (x 9 7).toNat = 0 := by
      have r33492 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := hcount 16
      have b33493 := hb (x 2 14)
      have b33494 := hb (x 3 13)
      have b33495 := hb (x 4 12)
      have b33496 := hb (x 5 11)
      have b33497 := hb (x 6 10)
      have b33498 := hb (x 7 9)
      have b33499 := hb (x 8 8)
      have b33500 := hb (x 9 7)
      have b33501 := hb (x 10 6)
      have b33502 := hb (x 11 5)
      have b33503 := hb (x 12 4)
      have b33504 := hb (x 13 3)
      have b33505 := hb (x 14 2)
      have b33506 := hb (x 15 1)
      clear * - r33492 b33493 b33494 b33495 b33496 b33497 b33498 b33499 b33500 b33501 b33502 b33503 b33504 b33505 b33506 d33455 d32888 d33459 d33027 d33475 d32973 d32359 d32383 d32399 d32225 g30
      omega
    have d33507 : (x 7 2 && x 7 9).toNat = 1 := by
      have r33508 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := hcov7 9
      have b33509 := hb (x 1 8)
      have b33510 := hb (x 9 7)
      have b33511 := hb (x 8 1 && x 8 8)
      have b33512 := hb (x 7 2 && x 7 9)
      have b33513 := hb (x 6 3 && x 6 10)
      have b33514 := hb (x 5 4 && x 5 11)
      have b33515 := hb (x 4 5 && x 4 12)
      have b33516 := hb (x 3 6 && x 3 13)
      have b33517 := hb (x 2 7 && x 2 14)
      clear * - r33508 b33509 b33510 b33511 b33512 b33513 b33514 b33515 b33516 b33517 d33491 d32565 d32363 d32428 d32589 g74 d33047 g22
      omega
    have d33518 : (x 7 9).toNat = 1 := by
      have r33519 := hand2 (x 7 2) (x 7 9)
      have b33520 := hb (x 7 9)
      have b33521 := hb (x 7 2 && x 7 9)
      clear * - r33519 b33520 b33521 d33507
      omega
    have r33522 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := hcount 16
    have b33523 := hb (x 2 14)
    have b33524 := hb (x 3 13)
    have b33525 := hb (x 4 12)
    have b33526 := hb (x 5 11)
    have b33527 := hb (x 6 10)
    have b33528 := hb (x 7 9)
    have b33529 := hb (x 8 8)
    have b33530 := hb (x 9 7)
    have b33531 := hb (x 10 6)
    have b33532 := hb (x 11 5)
    have b33533 := hb (x 12 4)
    have b33534 := hb (x 13 3)
    have b33535 := hb (x 14 2)
    have b33536 := hb (x 15 1)
    linarith only [r33522, b33523, b33524, b33525, b33526, b33527, b33528, b33529, b33530, b33531, b33532, b33533, b33534, b33535, b33536, d33455, d32888, d33459, d33027, d33475, d32973, d33491, d33518, d32359, d32383, d32399, d32225, g30]
  · have f33537 : (x (-1) 7).toNat = 1 := by rw [h31568]; rfl
    have d33538 : (x 6 8).toNat = 0 := by
      have r33539 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e33540 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e33541 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e33542 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e33543 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e33544 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e33545 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b33546 := hb (x (-1) 7)
      have b33547 := hb (x 0 6)
      have b33548 := hb (x 1 5)
      have b33549 := hb (x 2 4)
      have b33550 := hb (x 3 11)
      have b33551 := hb (x 4 10)
      have b33552 := hb (x 5 9)
      have b33553 := hb (x 6 8)
      clear * - r33539 e33540 e33541 e33542 e33543 e33544 e33545 b33546 b33547 b33548 b33549 b33550 b33551 b33552 b33553 g26 g20 g13 f33537
      omega
    have d33554 : (x 5 9).toNat = 0 := by
      have r33555 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e33556 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e33557 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e33558 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e33559 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e33560 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e33561 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b33562 := hb (x (-1) 7)
      have b33563 := hb (x 0 6)
      have b33564 := hb (x 1 5)
      have b33565 := hb (x 2 4)
      have b33566 := hb (x 3 11)
      have b33567 := hb (x 4 10)
      have b33568 := hb (x 5 9)
      have b33569 := hb (x 6 8)
      clear * - r33555 e33556 e33557 e33558 e33559 e33560 e33561 b33562 b33563 b33564 b33565 b33566 b33567 b33568 b33569 d33538 g26 g20 g13 f33537
      omega
    have d33570 : (x 4 10).toNat = 0 := by
      have r33571 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
      have e33572 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e33573 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e33574 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e33575 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e33576 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e33577 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b33578 := hb (x (-1) 7)
      have b33579 := hb (x 0 6)
      have b33580 := hb (x 1 5)
      have b33581 := hb (x 2 4)
      have b33582 := hb (x 3 11)
      have b33583 := hb (x 4 10)
      have b33584 := hb (x 5 9)
      have b33585 := hb (x 6 8)
      clear * - r33571 e33572 e33573 e33574 e33575 e33576 e33577 b33578 b33579 b33580 b33581 b33582 b33583 b33584 b33585 d33538 d33554 g26 g20 g13 f33537
      omega
    have d33586 : (x 3 1 && x 3 11).toNat = 1 := by
      have r33587 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := hcov10 4
      have b33588 := hb (x (-1) 5)
      have b33589 := hb (x 4 10)
      have b33590 := hb (x 3 1 && x 3 11)
      have b33591 := hb (x 2 2 && x 2 12)
      have b33592 := hb (x 1 3 && x 1 13)
      have b33593 := hb (x 0 4 && x 0 14)
      clear * - r33587 b33588 b33589 b33590 b33591 b33592 b33593 d33570 g81 g82 g83 g7
      omega
    have d33594 : (x 3 11).toNat = 1 := by
      have r33595 := hand2 (x 3 1) (x 3 11)
      have b33596 := hb (x 3 11)
      have b33597 := hb (x 3 1 && x 3 11)
      clear * - r33595 b33596 b33597 d33586
      omega
    have d33598 : (x 3 3).toNat = 1 := by
      have r33599 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b33600 := hb (x 3 3)
      have b33601 := hb (x 3 11)
      clear * - r33599 b33600 b33601 d33594
      omega
    have d33602 : (x 6 12).toNat = 0 := by
      have r33603 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e33604 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e33605 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b33606 := hb (x 3 3)
      have b33607 := hb (x 4 2)
      have b33608 := hb (x 5 13)
      have b33609 := hb (x 6 12)
      clear * - r33603 e33604 e33605 b33606 b33607 b33608 b33609 d33598
      omega
    have d33610 : (x 6 1 && x 6 12).toNat = 0 := by
      have r33611 := hand2 (x 6 1) (x 6 12)
      have b33612 := hb (x 6 12)
      have b33613 := hb (x 6 1 && x 6 12)
      clear * - r33611 b33612 b33613 d33602
      omega
    have d33614 : (x 6 2 && x 6 12).toNat = 0 := by
      have r33615 := hand2 (x 6 2) (x 6 12)
      have b33616 := hb (x 6 12)
      have b33617 := hb (x 6 2 && x 6 12)
      clear * - r33615 b33616 b33617 d33602
      omega
    have d33618 : (x 5 13).toNat = 0 := by
      have r33619 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e33620 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e33621 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b33622 := hb (x 3 3)
      have b33623 := hb (x 4 2)
      have b33624 := hb (x 5 13)
      have b33625 := hb (x 6 12)
      clear * - r33619 e33620 e33621 b33622 b33623 b33624 b33625 d33602 d33598
      omega
    have d33626 : (x 5 2 && x 5 13).toNat = 0 := by
      have r33627 := hand2 (x 5 2) (x 5 13)
      have b33628 := hb (x 5 13)
      have b33629 := hb (x 5 2 && x 5 13)
      clear * - r33627 b33628 b33629 d33618
      omega
    have d33630 : (x 5 3 && x 5 13).toNat = 0 := by
      have r33631 := hand2 (x 5 3) (x 5 13)
      have b33632 := hb (x 5 13)
      have b33633 := hb (x 5 3 && x 5 13)
      clear * - r33631 b33632 b33633 d33618
      omega
    have d33634 : (x 4 1 && x 4 14).toNat = 1 := by
      have r33635 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
      have b33636 := hb (x 3 2)
      have b33637 := hb (x 5 13)
      have b33638 := hb (x 4 1 && x 4 14)
      clear * - r33635 b33636 b33637 b33638 d33618 g31
      omega
    have d33639 : (x 4 14).toNat = 1 := by
      have r33640 := hand2 (x 4 1) (x 4 14)
      have b33641 := hb (x 4 14)
      have b33642 := hb (x 4 1 && x 4 14)
      clear * - r33640 b33641 b33642 d33634
      omega
    have d33643 : (x 3 1).toNat = 0 := by
      have r33644 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
      have b33645 := hb (x 3 1)
      have b33646 := hb (x 4 14)
      clear * - r33644 b33645 b33646 d33639
      omega
    have d33647 : (x 3 13).toNat = 0 := by
      have r33648 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b33649 := hb (x 3 1)
      have b33650 := hb (x 3 13)
      clear * - r33648 b33649 b33650 d33643
      omega
    have d33651 : (x 3 3 && x 3 13).toNat = 0 := by
      have r33652 := hand2 (x 3 3) (x 3 13)
      have b33653 := hb (x 3 13)
      have b33654 := hb (x 3 3 && x 3 13)
      clear * - r33652 b33653 b33654 d33647
      omega
    have d33655 : (x 3 5).toNat = 0 := by
      have r33656 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b33657 := hb (x 3 5)
      have b33658 := hb (x 3 13)
      clear * - r33656 b33657 b33658 d33647
      omega
    have d33659 : (x 4 1).toNat = 1 := by
      have r33660 := hand1 (x 4 1) (x 4 14)
      have b33661 := hb (x 4 1)
      have b33662 := hb (x 4 1 && x 4 14)
      clear * - r33660 b33661 b33662 d33634
      omega
    have d33663 : (x 5 14).toNat = 0 := by
      have r33664 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
      have b33665 := hb (x 4 1)
      have b33666 := hb (x 5 14)
      clear * - r33664 b33665 b33666 d33659
      omega
    have d33667 : (x 5 1 && x 5 14).toNat = 0 := by
      have r33668 := hand2 (x 5 1) (x 5 14)
      have b33669 := hb (x 5 14)
      have b33670 := hb (x 5 1 && x 5 14)
      clear * - r33668 b33669 b33670 d33663
      omega
    have d33671 : (x 5 2).toNat = 0 := by
      have r33672 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b33673 := hb (x 5 2)
      have b33674 := hb (x 5 14)
      clear * - r33672 b33673 b33674 d33663
      omega
    have d33675 : (x 5 10).toNat = 0 := by
      have r33676 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
      have b33677 := hb (x 5 2)
      have b33678 := hb (x 5 10)
      clear * - r33676 b33677 b33678 d33671
      omega
    have d33679 : (x 5 1 && x 5 10).toNat = 0 := by
      have r33680 := hand2 (x 5 1) (x 5 10)
      have b33681 := hb (x 5 10)
      have b33682 := hb (x 5 1 && x 5 10)
      clear * - r33680 b33681 b33682 d33675
      omega
    have d33683 : (x 4 2).toNat = 0 := by
      have r33684 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e33685 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e33686 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b33687 := hb (x 3 3)
      have b33688 := hb (x 4 2)
      have b33689 := hb (x 5 13)
      have b33690 := hb (x 6 12)
      clear * - r33684 e33685 e33686 b33687 b33688 b33689 b33690 d33602 d33618 d33598
      omega
    have d33691 : (x 4 2 && x 4 13).toNat = 0 := by
      have r33692 := hand1 (x 4 2) (x 4 13)
      have b33693 := hb (x 4 2)
      have b33694 := hb (x 4 2 && x 4 13)
      clear * - r33692 b33693 b33694 d33683
      omega
    have d33695 : (x 4 2 && x 4 12).toNat = 0 := by
      have r33696 := hand1 (x 4 2) (x 4 12)
      have b33697 := hb (x 4 2)
      have b33698 := hb (x 4 2 && x 4 12)
      clear * - r33696 b33697 b33698 d33683
      omega
    have d33699 : (x 4 2 && x 4 11).toNat = 0 := by
      have r33700 := hand1 (x 4 2) (x 4 11)
      have b33701 := hb (x 4 2)
      have b33702 := hb (x 4 2 && x 4 11)
      clear * - r33700 b33701 b33702 d33683
      omega
    have d33703 : (x 6 9).toNat = 1 := by
      have r33704 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
      have b33705 := hb (x 0 6)
      have b33706 := hb (x 6 9)
      have b33707 := hb (x 5 1 && x 5 10)
      have b33708 := hb (x 4 2 && x 4 11)
      have b33709 := hb (x 3 3 && x 3 12)
      have b33710 := hb (x 2 4 && x 2 13)
      have b33711 := hb (x 1 5 && x 1 14)
      clear * - r33704 b33705 b33706 b33707 b33708 b33709 b33710 b33711 d33679 d33699 g77 g78 g79 g13
      omega
    have d33712 : (x 6 1).toNat = 1 := by
      have r33713 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
      have b33714 := hb (x 6 1)
      have b33715 := hb (x 6 9)
      clear * - r33713 b33714 b33715 d33703
      omega
    have d33716 : (x 7 14).toNat = 0 := by
      have r33717 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
      have b33718 := hb (x 6 1)
      have b33719 := hb (x 7 14)
      clear * - r33717 b33718 b33719 d33712
      omega
    have d33720 : (x 7 1 && x 7 14).toNat = 0 := by
      have r33721 := hand2 (x 7 1) (x 7 14)
      have b33722 := hb (x 7 14)
      have b33723 := hb (x 7 1 && x 7 14)
      clear * - r33721 b33722 b33723 d33716
      omega
    have d33724 : (x 7 2).toNat = 0 := by
      have r33725 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b33726 := hb (x 7 2)
      have b33727 := hb (x 7 14)
      clear * - r33725 b33726 b33727 d33716
      omega
    have d33728 : (x 7 8).toNat = 0 := by
      have r33729 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
      have e33730 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e33731 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e33732 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e33733 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e33734 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e33735 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b33736 := hb (x 0 7)
      have b33737 := hb (x 1 6)
      have b33738 := hb (x 2 5)
      have b33739 := hb (x 3 4)
      have b33740 := hb (x 4 11)
      have b33741 := hb (x 5 10)
      have b33742 := hb (x 6 9)
      have b33743 := hb (x 7 8)
      clear * - r33729 e33730 e33731 e33732 e33733 e33734 e33735 b33736 b33737 b33738 b33739 b33740 b33741 b33742 b33743 d33703 d33675 g32 g21 g14
      omega
    have d33744 : (x 4 11).toNat = 0 := by
      have r33745 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
      have e33746 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e33747 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e33748 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e33749 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e33750 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e33751 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b33752 := hb (x 0 7)
      have b33753 := hb (x 1 6)
      have b33754 := hb (x 2 5)
      have b33755 := hb (x 3 4)
      have b33756 := hb (x 4 11)
      have b33757 := hb (x 5 10)
      have b33758 := hb (x 6 9)
      have b33759 := hb (x 7 8)
      clear * - r33745 e33746 e33747 e33748 e33749 e33750 e33751 b33752 b33753 b33754 b33755 b33756 b33757 b33758 b33759 d33728 d33703 d33675 g32 g21 g14
      omega
    have d33760 : (x 4 1 && x 4 11).toNat = 0 := by
      have r33761 := hand2 (x 4 1) (x 4 11)
      have b33762 := hb (x 4 11)
      have b33763 := hb (x 4 1 && x 4 11)
      clear * - r33761 b33762 b33763 d33744
      omega
    have d33764 : (x 2 3 && x 2 13).toNat = 1 := by
      have r33765 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
      have b33766 := hb (x 0 5)
      have b33767 := hb (x 5 10)
      have b33768 := hb (x 4 1 && x 4 11)
      have b33769 := hb (x 3 2 && x 3 12)
      have b33770 := hb (x 2 3 && x 2 13)
      have b33771 := hb (x 1 4 && x 1 14)
      clear * - r33765 b33766 b33767 b33768 b33769 b33770 b33771 d33675 d33760 g84 g85 g12
      omega
    have d33772 : (x 2 3).toNat = 1 := by
      have r33773 := hand1 (x 2 3) (x 2 13)
      have b33774 := hb (x 2 3)
      have b33775 := hb (x 2 3 && x 2 13)
      clear * - r33773 b33774 b33775 d33764
      omega
    have d33776 : (x 5 12).toNat = 0 := by
      have r33777 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
      have e33778 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e33779 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b33780 := hb (x 2 3)
      have b33781 := hb (x 3 2)
      have b33782 := hb (x 4 13)
      have b33783 := hb (x 5 12)
      clear * - r33777 e33778 e33779 b33780 b33781 b33782 b33783 g31 d33772
      omega
    have d33784 : (x 5 1 && x 5 12).toNat = 0 := by
      have r33785 := hand2 (x 5 1) (x 5 12)
      have b33786 := hb (x 5 12)
      have b33787 := hb (x 5 1 && x 5 12)
      clear * - r33785 b33786 b33787 d33776
      omega
    have d33788 : (x 6 11).toNat = 1 := by
      have r33789 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
      have b33790 := hb (x 2 4)
      have b33791 := hb (x 6 11)
      have b33792 := hb (x 5 1 && x 5 12)
      have b33793 := hb (x 4 2 && x 4 13)
      have b33794 := hb (x 3 3 && x 3 14)
      clear * - r33789 b33790 b33791 b33792 b33793 b33794 d33784 d33691 g87 g26
      omega
    have d33795 : (x 6 3).toNat = 1 := by
      have r33796 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
      have b33797 := hb (x 6 3)
      have b33798 := hb (x 6 11)
      clear * - r33796 b33797 b33798 d33788
      omega
    have d33799 : (x 9 12).toNat = 0 := by
      have r33800 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e33801 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e33802 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b33803 := hb (x 6 3)
      have b33804 := hb (x 7 2)
      have b33805 := hb (x 8 13)
      have b33806 := hb (x 9 12)
      clear * - r33800 e33801 e33802 b33803 b33804 b33805 b33806 d33724 d33795
      omega
    have d33807 : (x 8 13).toNat = 0 := by
      have r33808 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e33809 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e33810 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b33811 := hb (x 6 3)
      have b33812 := hb (x 7 2)
      have b33813 := hb (x 8 13)
      have b33814 := hb (x 9 12)
      clear * - r33808 e33809 e33810 b33811 b33812 b33813 b33814 d33799 d33724 d33795
      omega
    have d33815 : (x 6 2).toNat = 1 := by
      have r33816 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
      have b33817 := hb (x 6 2)
      have b33818 := hb (x 8 13)
      have b33819 := hb (x 7 1 && x 7 14)
      clear * - r33816 b33817 b33818 b33819 d33807 d33720
      omega
    have d33820 : (x 6 14).toNat = 1 := by
      have r33821 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b33822 := hb (x 6 2)
      have b33823 := hb (x 6 14)
      clear * - r33821 b33822 b33823 d33815
      omega
    have d33824 : (x 5 1).toNat = 0 := by
      have r33825 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
      have b33826 := hb (x 5 1)
      have b33827 := hb (x 6 14)
      clear * - r33825 b33826 b33827 d33820
      omega
    have d33828 : (x 5 1 && x 5 11).toNat = 0 := by
      have r33829 := hand1 (x 5 1) (x 5 11)
      have b33830 := hb (x 5 1)
      have b33831 := hb (x 5 1 && x 5 11)
      clear * - r33829 b33830 b33831 d33824
      omega
    have d33832 : (x 6 10).toNat = 1 := by
      have r33833 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := hcov10 6
      have b33834 := hb (x 1 5)
      have b33835 := hb (x 6 10)
      have b33836 := hb (x 5 1 && x 5 11)
      have b33837 := hb (x 4 2 && x 4 12)
      have b33838 := hb (x 3 3 && x 3 13)
      have b33839 := hb (x 2 4 && x 2 14)
      clear * - r33833 b33834 b33835 b33836 b33837 b33838 b33839 d33828 d33695 d33651 g86 g20
      omega
    have d33840 : (x 8 8).toNat = 0 := by
      have r33841 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
      have e33842 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e33843 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e33844 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e33845 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e33846 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e33847 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b33848 := hb (x 1 7)
      have b33849 := hb (x 2 6)
      have b33850 := hb (x 3 5)
      have b33851 := hb (x 4 4)
      have b33852 := hb (x 5 11)
      have b33853 := hb (x 6 10)
      have b33854 := hb (x 7 9)
      have b33855 := hb (x 8 8)
      clear * - r33841 e33842 e33843 e33844 e33845 e33846 e33847 b33848 b33849 b33850 b33851 b33852 b33853 b33854 b33855 d33832 d33655
      omega
    have d33856 : (x 7 9).toNat = 0 := by
      have r33857 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
      have e33858 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e33859 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e33860 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e33861 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e33862 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e33863 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b33864 := hb (x 1 7)
      have b33865 := hb (x 2 6)
      have b33866 := hb (x 3 5)
      have b33867 := hb (x 4 4)
      have b33868 := hb (x 5 11)
      have b33869 := hb (x 6 10)
      have b33870 := hb (x 7 9)
      have b33871 := hb (x 8 8)
      clear * - r33857 e33858 e33859 e33860 e33861 e33862 e33863 b33864 b33865 b33866 b33867 b33868 b33869 b33870 b33871 d33840 d33832 d33655
      omega
    have d33872 : (x 5 11).toNat = 0 := by
      have r33873 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
      have e33874 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e33875 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e33876 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e33877 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e33878 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e33879 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b33880 := hb (x 1 7)
      have b33881 := hb (x 2 6)
      have b33882 := hb (x 3 5)
      have b33883 := hb (x 4 4)
      have b33884 := hb (x 5 11)
      have b33885 := hb (x 6 10)
      have b33886 := hb (x 7 9)
      have b33887 := hb (x 8 8)
      clear * - r33873 e33874 e33875 e33876 e33877 e33878 e33879 b33880 b33881 b33882 b33883 b33884 b33885 b33886 b33887 d33840 d33856 d33832 d33655
      omega
    have d33888 : (x 4 4).toNat = 0 := by
      have r33889 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
      have e33890 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e33891 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e33892 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e33893 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e33894 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e33895 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b33896 := hb (x 1 7)
      have b33897 := hb (x 2 6)
      have b33898 := hb (x 3 5)
      have b33899 := hb (x 4 4)
      have b33900 := hb (x 5 11)
      have b33901 := hb (x 6 10)
      have b33902 := hb (x 7 9)
      have b33903 := hb (x 8 8)
      clear * - r33889 e33890 e33891 e33892 e33893 e33894 e33895 b33896 b33897 b33898 b33899 b33900 b33901 b33902 b33903 d33840 d33856 d33832 d33872 d33655
      omega
    have d33904 : (x 4 4 && x 4 14).toNat = 0 := by
      have r33905 := hand1 (x 4 4) (x 4 14)
      have b33906 := hb (x 4 4)
      have b33907 := hb (x 4 4 && x 4 14)
      clear * - r33905 b33906 b33907 d33888
      omega
    have d33908 : (x 6 13).toNat = 1 := by
      have r33909 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
      have b33910 := hb (x 4 2)
      have b33911 := hb (x 6 13)
      have b33912 := hb (x 5 1 && x 5 14)
      clear * - r33909 b33910 b33911 b33912 d33667 d33683
      omega
    have d33913 : (x 7 12).toNat = 0 := by
      have r33914 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e33915 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e33916 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b33917 := hb (x 4 3)
      have b33918 := hb (x 5 2)
      have b33919 := hb (x 6 13)
      have b33920 := hb (x 7 12)
      clear * - r33914 e33915 e33916 b33917 b33918 b33919 b33920 d33908 d33671
      omega
    have d33921 : (x 4 3).toNat = 0 := by
      have r33922 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e33923 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e33924 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b33925 := hb (x 4 3)
      have b33926 := hb (x 5 2)
      have b33927 := hb (x 6 13)
      have b33928 := hb (x 7 12)
      clear * - r33922 e33923 e33924 b33925 b33926 b33927 b33928 d33913 d33908 d33671
      omega
    have d33929 : (x 4 3 && x 4 14).toNat = 0 := by
      have r33930 := hand1 (x 4 3) (x 4 14)
      have b33931 := hb (x 4 3)
      have b33932 := hb (x 4 3 && x 4 14)
      clear * - r33930 b33931 b33932 d33921
      omega
    have d33933 : (x 7 11).toNat = 1 := by
      have r33934 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
      have b33935 := hb (x 3 4)
      have b33936 := hb (x 7 11)
      have b33937 := hb (x 6 1 && x 6 12)
      have b33938 := hb (x 5 2 && x 5 13)
      have b33939 := hb (x 4 3 && x 4 14)
      clear * - r33934 b33935 b33936 b33937 b33938 b33939 d33610 d33626 d33929 g32
      omega
    have d33940 : (x 7 3).toNat = 1 := by
      have r33941 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b33942 := hb (x 7 3)
      have b33943 := hb (x 7 11)
      clear * - r33941 b33942 b33943 d33933
      omega
    have d33944 : (x 10 12).toNat = 0 := by
      have r33945 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e33946 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e33947 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b33948 := hb (x 7 3)
      have b33949 := hb (x 8 2)
      have b33950 := hb (x 9 13)
      have b33951 := hb (x 10 12)
      clear * - r33945 e33946 e33947 b33948 b33949 b33950 b33951 d33940
      omega
    have d33952 : (x 9 13).toNat = 0 := by
      have r33953 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e33954 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e33955 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b33956 := hb (x 7 3)
      have b33957 := hb (x 8 2)
      have b33958 := hb (x 9 13)
      have b33959 := hb (x 10 12)
      clear * - r33953 e33954 e33955 b33956 b33957 b33958 b33959 d33944 d33940
      omega
    have d33960 : (x 8 1 && x 8 14).toNat = 1 := by
      have r33961 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
      have b33962 := hb (x 7 2)
      have b33963 := hb (x 9 13)
      have b33964 := hb (x 8 1 && x 8 14)
      clear * - r33961 b33962 b33963 b33964 d33952 d33724
      omega
    have d33965 : (x 8 14).toNat = 1 := by
      have r33966 := hand2 (x 8 1) (x 8 14)
      have b33967 := hb (x 8 14)
      have b33968 := hb (x 8 1 && x 8 14)
      clear * - r33966 b33967 b33968 d33960
      omega
    have d33969 : (x 7 1).toNat = 0 := by
      have r33970 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
      have b33971 := hb (x 7 1)
      have b33972 := hb (x 8 14)
      clear * - r33970 b33971 b33972 d33965
      omega
    have d33973 : (x 7 1 && x 7 11).toNat = 0 := by
      have r33974 := hand1 (x 7 1) (x 7 11)
      have b33975 := hb (x 7 1)
      have b33976 := hb (x 7 1 && x 7 11)
      clear * - r33974 b33975 b33976 d33969
      omega
    have d33977 : (x 8 10).toNat = 1 := by
      have r33978 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := hcov10 8
      have b33979 := hb (x 3 5)
      have b33980 := hb (x 8 10)
      have b33981 := hb (x 7 1 && x 7 11)
      have b33982 := hb (x 6 2 && x 6 12)
      have b33983 := hb (x 5 3 && x 5 13)
      have b33984 := hb (x 4 4 && x 4 14)
      clear * - r33978 b33979 b33980 b33981 b33982 b33983 b33984 d33973 d33614 d33630 d33904 d33655
      omega
    have d33985 : (x 8 2).toNat = 1 := by
      have r33986 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
      have b33987 := hb (x 8 2)
      have b33988 := hb (x 8 10)
      clear * - r33986 b33987 b33988 d33977
      omega
    have r33989 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e33990 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e33991 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b33992 := hb (x 7 3)
    have b33993 := hb (x 8 2)
    have b33994 := hb (x 9 13)
    have b33995 := hb (x 10 12)
    linarith only [r33989, e33990, e33991, b33992, b33993, b33994, b33995, d33944, d33952, d33985, d33940]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011000010 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 11).toNat = 0)
    (g1 : (x (-3) 10).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 9).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-2) 13).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 8).toNat = 1)
    (g9 : (x (-1) 9).toNat = 1)
    (g10 : (x (-1) 10).toNat = 1)
    (g11 : (x (-1) 12).toNat = 1)
    (g12 : (x 0 5).toNat = 0)
    (g13 : (x 0 6).toNat = 0)
    (g14 : (x 0 7).toNat = 0)
    (g15 : (x 0 8).toNat = 0)
    (g16 : (x 0 9).toNat = 0)
    (g17 : (x 0 11).toNat = 0)
    (g18 : (x 0 14).toNat = 0)
    (g19 : (x 1 3).toNat = 0)
    (g20 : (x 1 5).toNat = 0)
    (g21 : (x 1 6).toNat = 0)
    (g22 : (x 1 8).toNat = 0)
    (g23 : (x 1 10).toNat = 0)
    (g24 : (x 1 13).toNat = 0)
    (g25 : (x 1 14).toNat = 0)
    (g26 : (x 2 4).toNat = 0)
    (g27 : (x 2 9).toNat = 0)
    (g28 : (x 2 12).toNat = 0)
    (g29 : (x 2 13).toNat = 1)
    (g30 : (x 2 14).toNat = 1)
    (g31 : (x 3 2).toNat = 0)
    (g32 : (x 3 4).toNat = 0)
    (g33 : (x 3 6).toNat = 0)
    (g34 : (x 3 8).toNat = 0)
    (g35 : (x 3 12).toNat = 0)
    (g36 : (x 3 3 && x 3 6).toNat = 0)
    (g37 : (x 2 4 && x 2 7).toNat = 0)
    (g38 : (x 1 5 && x 1 8).toNat = 0)
    (g39 : (x 0 6 && x 0 9).toNat = 0)
    (g40 : (x (-2) 8 && x (-2) 11).toNat = 0)
    (g41 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g42 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g43 : (x (-4) 3 && x (-4) 8).toNat = 0)
    (g44 : (x (-5) 4 && x (-5) 9).toNat = 0)
    (g45 : (x (-6) 5 && x (-6) 10).toNat = 0)
    (g46 : (x (-7) 6 && x (-7) 11).toNat = 0)
    (g47 : (x (-8) 7 && x (-8) 12).toNat = 0)
    (g48 : (x 0 1 && x 0 6).toNat = 0)
    (g49 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g50 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g51 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g52 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g53 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g54 : (x 3 3 && x 3 8).toNat = 0)
    (g55 : (x 2 4 && x 2 9).toNat = 0)
    (g56 : (x 1 5 && x 1 10).toNat = 0)
    (g57 : (x 0 6 && x 0 11).toNat = 0)
    (g58 : (x (-2) 8 && x (-2) 13).toNat = 0)
    (g59 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g60 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g61 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g62 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g63 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g64 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g65 : (x 3 6 && x 3 12).toNat = 0)
    (g66 : (x 1 8 && x 1 14).toNat = 0)
    (g67 : (x (-2) 1 && x (-2) 8).toNat = 0)
    (g68 : (x (-3) 2 && x (-3) 9).toNat = 0)
    (g69 : (x (-4) 3 && x (-4) 10).toNat = 0)
    (g70 : (x (-5) 4 && x (-5) 11).toNat = 0)
    (g71 : (x (-6) 5 && x (-6) 12).toNat = 0)
    (g72 : (x (-7) 6 && x (-7) 13).toNat = 0)
    (g73 : (x (-8) 7 && x (-8) 14).toNat = 0)
    (g74 : (x 3 6 && x 3 13).toNat = 0)
    (g75 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g76 : (x (-4) 2 && x (-4) 11).toNat = 0)
    (g77 : (x 3 3 && x 3 12).toNat = 0)
    (g78 : (x 2 4 && x 2 13).toNat = 0)
    (g79 : (x 1 5 && x 1 14).toNat = 0)
    (g80 : (x (-4) 1 && x (-4) 11).toNat = 0)
    (g81 : (x 2 2 && x 2 12).toNat = 0)
    (g82 : (x 1 3 && x 1 13).toNat = 0)
    (g83 : (x 0 4 && x 0 14).toNat = 0)
    (g84 : (x 3 2 && x 3 12).toNat = 0)
    (g85 : (x 1 4 && x 1 14).toNat = 0)
    (g86 : (x 2 4 && x 2 14).toNat = 0)
    (g87 : (x 3 3 && x 3 14).toNat = 0)
    (g88 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011000010_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88
