import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000001

Topic: combinatorics   Node: 9632cca80a94

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 60 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 1).toNat = 1)
    (g1 : (x (-1) 3).toNat = 0)
    (g2 : (x (-1) 11).toNat = 0)
    (g3 : (x (-1) 13).toNat = 1)
    (g4 : (x 0 1).toNat = 1)
    (g5 : (x 0 2).toNat = 0)
    (g6 : (x 0 4).toNat = 0)
    (g7 : (x 0 5).toNat = 0)
    (g8 : (x 0 6).toNat = 0)
    (g9 : (x 0 8).toNat = 0)
    (g10 : (x 0 10).toNat = 0)
    (g11 : (x 0 11).toNat = 0)
    (g12 : (x 0 13).toNat = 0)
    (g13 : (x 0 14).toNat = 0)
    (g14 : (x 1 2).toNat = 0)
    (g15 : (x 1 6).toNat = 0)
    (g16 : (x 1 10).toNat = 0)
    (g17 : (x 3 2).toNat = 0)
    (g18 : (x 3 4).toNat = 0)
    (g19 : (x 3 6).toNat = 0)
    (g20 : (x 3 10).toNat = 0)
    (g21 : (x 0 1 && x 0 2).toNat = 0)
    (g22 : (x (-1) 2 && x (-1) 3).toNat = 0)
    (g23 : (x 1 9 && x 1 10).toNat = 0)
    (g24 : (x 0 10 && x 0 11).toNat = 0)
    (g25 : (x (-1) 11 && x (-1) 12).toNat = 0)
    (g26 : (x (-1) 1 && x (-1) 3).toNat = 0)
    (g27 : (x 0 1 && x 0 3).toNat = 0)
    (g28 : (x 3 7 && x 3 10).toNat = 0)
    (g29 : (x 0 10 && x 0 13).toNat = 0)
    (g30 : (x (-1) 11 && x (-1) 14).toNat = 0)
    (g31 : (x 3 6 && x 3 10).toNat = 0)
    (g32 : (x 0 9 && x 0 13).toNat = 0)
    (g33 : (x 0 1 && x 0 6).toNat = 0)
    (g34 : (x 3 5 && x 3 10).toNat = 0)
    (g35 : (x 0 8 && x 0 13).toNat = 0)
    (g36 : (x 0 1 && x 0 7).toNat = 0)
    (g37 : (x 3 6 && x 3 13).toNat = 0)
    (g38 : (x 0 1 && x 0 10).toNat = 0)
    (g39 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g40 : (x 1 1 && x 1 10).toNat = 0)
    (g41 : (x 0 2 && x 0 11).toNat = 0)
    (g42 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g43 : (x 1 2 && x 1 11).toNat = 0)
    (g44 : (x 0 3 && x 0 12).toNat = 0)
    (g45 : (x 3 5 && x 3 14).toNat = 0)
    (g46 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g47 : (x 0 1 && x 0 11).toNat = 0)
    (g48 : (x 0 2 && x 0 12).toNat = 0)
    (g49 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g50 : (x 1 2 && x 1 12).toNat = 0)
    (g51 : (x 0 3 && x 0 13).toNat = 0)
    (g52 : (x 3 2 && x 3 12).toNat = 0)
    (g53 : (x 1 4 && x 1 14).toNat = 0)
    (g54 : (x 3 1 && x 3 12).toNat = 0)
    (g55 : (x 1 3 && x 1 14).toNat = 0)
    (g56 : (x 3 2 && x 3 13).toNat = 0)
    (g57 : (x 3 3 && x 3 14).toNat = 0)
    (g58 : (x 0 1 && x 0 14).toNat = 0)
    (g59 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d21611 : (x 0 12).toNat = 0 := by
    have r21612 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
    have e21613 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e21614 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b21615 := hb (x (-3) 3)
    have b21616 := hb (x (-2) 2)
    have b21617 := hb (x (-1) 13)
    have b21618 := hb (x 0 12)
    clear * - r21612 e21613 e21614 b21615 b21616 b21617 b21618 g3
    omega
  have d21619 : (x (-2) 2).toNat = 0 := by
    have r21620 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
    have e21621 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e21622 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b21623 := hb (x (-3) 3)
    have b21624 := hb (x (-2) 2)
    have b21625 := hb (x (-1) 13)
    have b21626 := hb (x 0 12)
    clear * - r21620 e21621 e21622 b21623 b21624 b21625 b21626 d21611 g3
    omega
  have d21627 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r21628 := hand1 (x (-2) 2) (x (-2) 13)
    have b21629 := hb (x (-2) 2)
    have b21630 := hb (x (-2) 2 && x (-2) 13)
    clear * - r21628 b21629 b21630 d21619
    omega
  have d21631 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
    have r21632 := hand1 (x (-2) 2) (x (-2) 12)
    have b21633 := hb (x (-2) 2)
    have b21634 := hb (x (-2) 2 && x (-2) 12)
    clear * - r21632 b21633 b21634 d21619
    omega
  have d21635 : (x (-2) 2 && x (-2) 4).toNat = 0 := by
    have r21636 := hand1 (x (-2) 2) (x (-2) 4)
    have b21637 := hb (x (-2) 2)
    have b21638 := hb (x (-2) 2 && x (-2) 4)
    clear * - r21636 b21637 b21638 d21619
    omega
  have d21639 : (x (-2) 10).toNat = 0 := by
    have r21640 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b21641 := hb (x (-2) 2)
    have b21642 := hb (x (-2) 10)
    clear * - r21640 b21641 b21642 d21619
    omega
  have d21643 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
    have r21644 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := hcov13 0
    have b21645 := hb (x (-2) 2)
    have b21646 := hb (x 0 13)
    have b21647 := hb (x (-1) 1 && x (-1) 14)
    clear * - r21644 b21645 b21646 b21647 g12 d21619
    omega
  have d21648 : (x (-1) 14).toNat = 1 := by
    have r21649 := hand2 (x (-1) 1) (x (-1) 14)
    have b21650 := hb (x (-1) 14)
    have b21651 := hb (x (-1) 1 && x (-1) 14)
    clear * - r21649 b21650 b21651 d21643
    omega
  have d21652 : (x (-2) 1).toNat = 0 := by
    have r21653 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
    have b21654 := hb (x (-2) 1)
    have b21655 := hb (x (-1) 14)
    clear * - r21653 b21654 b21655 d21648
    omega
  have d21656 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
    have r21657 := hand1 (x (-2) 1) (x (-2) 12)
    have b21658 := hb (x (-2) 1)
    have b21659 := hb (x (-2) 1 && x (-2) 12)
    clear * - r21657 b21658 b21659 d21652
    omega
  have d21660 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
    have r21661 := hand1 (x (-2) 1) (x (-2) 11)
    have b21662 := hb (x (-2) 1)
    have b21663 := hb (x (-2) 1 && x (-2) 11)
    clear * - r21661 b21662 b21663 d21652
    omega
  have d21664 : (x (-2) 13).toNat = 0 := by
    have r21665 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b21666 := hb (x (-2) 1)
    have b21667 := hb (x (-2) 13)
    clear * - r21665 b21666 b21667 d21652
    omega
  have d21668 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r21669 := hand2 (x (-2) 3) (x (-2) 13)
    have b21670 := hb (x (-2) 13)
    have b21671 := hb (x (-2) 3 && x (-2) 13)
    clear * - r21669 b21670 b21671 d21664
    omega
  have d21672 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
    have r21673 := hand2 (x (-2) 4) (x (-2) 13)
    have b21674 := hb (x (-2) 13)
    have b21675 := hb (x (-2) 4 && x (-2) 13)
    clear * - r21673 b21674 b21675 d21664
    omega
  have d21676 : (x (-2) 12 && x (-2) 13).toNat = 0 := by
    have r21677 := hand2 (x (-2) 12) (x (-2) 13)
    have b21678 := hb (x (-2) 13)
    have b21679 := hb (x (-2) 12 && x (-2) 13)
    clear * - r21677 b21678 b21679 d21664
    omega
  have d21680 : (x (-2) 5).toNat = 0 := by
    have r21681 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b21682 := hb (x (-2) 5)
    have b21683 := hb (x (-2) 13)
    clear * - r21681 b21682 b21683 d21664
    omega
  have d21684 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
    have r21685 := hand1 (x (-2) 5) (x (-2) 14)
    have b21686 := hb (x (-2) 5)
    have b21687 := hb (x (-2) 5 && x (-2) 14)
    clear * - r21685 b21686 b21687 d21680
    omega
  have d21688 : (x (-2) 3 && x (-2) 5).toNat = 0 := by
    have r21689 := hand2 (x (-2) 3) (x (-2) 5)
    have b21690 := hb (x (-2) 5)
    have b21691 := hb (x (-2) 3 && x (-2) 5)
    clear * - r21689 b21690 b21691 d21680
    omega
  have d21692 : (x (-2) 9).toNat = 0 := by
    have r21693 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
    have b21694 := hb (x (-2) 1)
    have b21695 := hb (x (-2) 9)
    clear * - r21693 b21694 b21695 d21652
    omega
  have d21696 : (x (-2) 3 && x (-2) 9).toNat = 0 := by
    have r21697 := hand2 (x (-2) 3) (x (-2) 9)
    have b21698 := hb (x (-2) 9)
    have b21699 := hb (x (-2) 3 && x (-2) 9)
    clear * - r21697 b21698 b21699 d21692
    omega
  have d21700 : (x (-3) 3).toNat = 0 := by
    have r21701 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
    have e21702 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e21703 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b21704 := hb (x (-3) 3)
    have b21705 := hb (x (-2) 2)
    have b21706 := hb (x (-1) 13)
    have b21707 := hb (x 0 12)
    clear * - r21701 e21702 e21703 b21704 b21705 b21706 b21707 d21611 g3 d21619
    omega
  have d21708 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r21709 := hand1 (x (-3) 3) (x (-3) 14)
    have b21710 := hb (x (-3) 3)
    have b21711 := hb (x (-3) 3 && x (-3) 14)
    clear * - r21709 b21710 b21711 d21700
    omega
  have d21712 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r21713 := hand1 (x (-3) 3) (x (-3) 13)
    have b21714 := hb (x (-3) 3)
    have b21715 := hb (x (-3) 3 && x (-3) 13)
    clear * - r21713 b21714 b21715 d21700
    omega
  have d21716 : (x (-3) 3 && x (-3) 5).toNat = 0 := by
    have r21717 := hand1 (x (-3) 3) (x (-3) 5)
    have b21718 := hb (x (-3) 3)
    have b21719 := hb (x (-3) 3 && x (-3) 5)
    clear * - r21717 b21718 b21719 d21700
    omega
  have d21720 : (x (-3) 11).toNat = 0 := by
    have r21721 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b21722 := hb (x (-3) 3)
    have b21723 := hb (x (-3) 11)
    clear * - r21721 b21722 b21723 d21700
    omega
  cases h21724 : x 0 9
  · have f21725 : (x 0 9).toNat = 0 := by rw [h21724]; rfl
    cases h21726 : x 1 1
    · have f21727 : (x 1 1).toNat = 0 := by rw [h21726]; rfl
      have d21728 : (x 1 1 && x 1 11).toNat = 0 := by
        have r21729 := hand1 (x 1 1) (x 1 11)
        have b21730 := hb (x 1 1)
        have b21731 := hb (x 1 1 && x 1 11)
        clear * - r21729 b21730 b21731 f21727
        omega
      have d21732 : (x 1 13).toNat = 0 := by
        have r21733 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
        have b21734 := hb (x 1 1)
        have b21735 := hb (x 1 13)
        clear * - r21733 b21734 b21735 f21727
        omega
      have d21736 : (x 1 9).toNat = 0 := by
        have r21737 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
        have b21738 := hb (x 1 1)
        have b21739 := hb (x 1 9)
        clear * - r21737 b21738 b21739 f21727
        omega
      have d21740 : (x 1 9 && x 1 12).toNat = 0 := by
        have r21741 := hand1 (x 1 9) (x 1 12)
        have b21742 := hb (x 1 9)
        have b21743 := hb (x 1 9 && x 1 12)
        clear * - r21741 b21742 b21743 d21736
        omega
      have d21744 : (x 1 5).toNat = 0 := by
        have r21745 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
        have b21746 := hb (x 1 5)
        have b21747 := hb (x 1 13)
        clear * - r21745 b21746 b21747 d21732
        omega
      have d21748 : (x (-1) 2).toNat = 1 := by
        have r21749 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
        have b21750 := hb (x (-1) 2)
        have b21751 := hb (x 1 13)
        have b21752 := hb (x 0 1 && x 0 14)
        clear * - r21749 b21750 b21751 b21752 d21732 g58
        omega
      have d21753 : (x 2 12).toNat = 1 := by
        have r21754 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
        have e21755 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e21756 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b21757 := hb (x (-1) 3)
        have b21758 := hb (x 0 2)
        have b21759 := hb (x 1 13)
        have b21760 := hb (x 2 12)
        clear * - r21754 e21755 e21756 b21757 b21758 b21759 b21760 d21732 g5 g1
        omega
      have d21761 : (x 1 12).toNat = 0 := by
        have r21762 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
        have e21763 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e21764 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b21765 := hb (x (-2) 3)
        have b21766 := hb (x (-1) 2)
        have b21767 := hb (x 0 13)
        have b21768 := hb (x 1 12)
        clear * - r21762 e21763 e21764 b21765 b21766 b21767 b21768 g12 d21748
        omega
      have d21769 : (x 1 7 && x 1 12).toNat = 0 := by
        have r21770 := hand2 (x 1 7) (x 1 12)
        have b21771 := hb (x 1 12)
        have b21772 := hb (x 1 7 && x 1 12)
        clear * - r21770 b21771 b21772 d21761
        omega
      have d21773 : (x 1 8 && x 1 12).toNat = 0 := by
        have r21774 := hand2 (x 1 8) (x 1 12)
        have b21775 := hb (x 1 12)
        have b21776 := hb (x 1 8 && x 1 12)
        clear * - r21774 b21775 b21776 d21761
        omega
      have d21777 : (x 1 4).toNat = 0 := by
        have r21778 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
        have b21779 := hb (x 1 4)
        have b21780 := hb (x 1 12)
        clear * - r21778 b21779 b21780 d21761
        omega
      have d21781 : (x (-2) 3).toNat = 0 := by
        have r21782 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
        have e21783 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e21784 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b21785 := hb (x (-2) 3)
        have b21786 := hb (x (-1) 2)
        have b21787 := hb (x 0 13)
        have b21788 := hb (x 1 12)
        clear * - r21782 e21783 e21784 b21785 b21786 b21787 b21788 d21761 g12 d21748
        omega
      have d21789 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
        have r21790 := hand1 (x (-2) 3) (x (-2) 12)
        have b21791 := hb (x (-2) 3)
        have b21792 := hb (x (-2) 3 && x (-2) 12)
        clear * - r21790 b21791 b21792 d21781
        omega
      have d21793 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
        have r21794 := hand1 (x (-2) 3) (x (-2) 8)
        have b21795 := hb (x (-2) 3)
        have b21796 := hb (x (-2) 3 && x (-2) 8)
        clear * - r21794 b21795 b21796 d21781
        omega
      have d21797 : (x (-2) 3 && x (-2) 7).toNat = 0 := by
        have r21798 := hand1 (x (-2) 3) (x (-2) 7)
        have b21799 := hb (x (-2) 3)
        have b21800 := hb (x (-2) 3 && x (-2) 7)
        clear * - r21798 b21799 b21800 d21781
        omega
      have d21801 : (x (-2) 3 && x (-2) 4).toNat = 0 := by
        have r21802 := hand1 (x (-2) 3) (x (-2) 4)
        have b21803 := hb (x (-2) 3)
        have b21804 := hb (x (-2) 3 && x (-2) 4)
        clear * - r21802 b21803 b21804 d21781
        omega
      have d21805 : (x (-2) 11).toNat = 0 := by
        have r21806 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
        have b21807 := hb (x (-2) 3)
        have b21808 := hb (x (-2) 11)
        clear * - r21806 b21807 b21808 d21781
        omega
      cases h21809 : x 1 3
      · have f21810 : (x 1 3).toNat = 0 := by rw [h21809]; rfl
        have d21811 : (x 1 11).toNat = 0 := by
          have r21812 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b21813 := hb (x 1 3)
          have b21814 := hb (x 1 11)
          clear * - r21812 b21813 b21814 f21810
          omega
        cases h21815 : x (-1) 4
        · have f21816 : (x (-1) 4).toNat = 0 := by rw [h21815]; rfl
          have d21817 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
            have r21818 := hand1 (x (-1) 4) (x (-1) 14)
            have b21819 := hb (x (-1) 4)
            have b21820 := hb (x (-1) 4 && x (-1) 14)
            clear * - r21818 b21819 b21820 f21816
            omega
          have d21821 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
            have r21822 := hand1 (x (-1) 4) (x (-1) 13)
            have b21823 := hb (x (-1) 4)
            have b21824 := hb (x (-1) 4 && x (-1) 13)
            clear * - r21822 b21823 b21824 f21816
            omega
          have d21825 : (x (-1) 2 && x (-1) 4).toNat = 0 := by
            have r21826 := hand2 (x (-1) 2) (x (-1) 4)
            have b21827 := hb (x (-1) 4)
            have b21828 := hb (x (-1) 2 && x (-1) 4)
            clear * - r21826 b21827 b21828 f21816
            omega
          have d21829 : (x 2 1 && x 2 11).toNat = 1 := by
            have r21830 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := hcov10 3
            have b21831 := hb (x (-2) 5)
            have b21832 := hb (x 3 10)
            have b21833 := hb (x 2 1 && x 2 11)
            have b21834 := hb (x 1 2 && x 1 12)
            have b21835 := hb (x 0 3 && x 0 13)
            have b21836 := hb (x (-1) 4 && x (-1) 14)
            clear * - r21830 b21831 b21832 b21833 b21834 b21835 b21836 g20 g50 g51 d21817 d21680
            omega
          have d21837 : (x 2 11).toNat = 1 := by
            have r21838 := hand2 (x 2 1) (x 2 11)
            have b21839 := hb (x 2 11)
            have b21840 := hb (x 2 1 && x 2 11)
            clear * - r21838 b21839 b21840 d21829
            omega
          have d21841 : (x 2 3).toNat = 1 := by
            have r21842 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
            have b21843 := hb (x 2 3)
            have b21844 := hb (x 2 11)
            clear * - r21842 b21843 b21844 d21837
            omega
          have d21845 : (x 5 12).toNat = 0 := by
            have r21846 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e21847 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e21848 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b21849 := hb (x 2 3)
            have b21850 := hb (x 3 2)
            have b21851 := hb (x 4 13)
            have b21852 := hb (x 5 12)
            clear * - r21846 e21847 e21848 b21849 b21850 b21851 b21852 g17 d21841
            omega
          have d21853 : (x 5 1 && x 5 12).toNat = 0 := by
            have r21854 := hand2 (x 5 1) (x 5 12)
            have b21855 := hb (x 5 12)
            have b21856 := hb (x 5 1 && x 5 12)
            clear * - r21854 b21855 b21856 d21845
            omega
          have d21857 : (x 5 3 && x 5 12).toNat = 0 := by
            have r21858 := hand2 (x 5 3) (x 5 12)
            have b21859 := hb (x 5 12)
            have b21860 := hb (x 5 3 && x 5 12)
            clear * - r21858 b21859 b21860 d21845
            omega
          have d21861 : (x 5 4).toNat = 0 := by
            have r21862 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b21863 := hb (x 5 4)
            have b21864 := hb (x 5 12)
            clear * - r21862 b21863 b21864 d21845
            omega
          have d21865 : (x 5 4 && x 5 14).toNat = 0 := by
            have r21866 := hand1 (x 5 4) (x 5 14)
            have b21867 := hb (x 5 4)
            have b21868 := hb (x 5 4 && x 5 14)
            clear * - r21866 b21867 b21868 d21861
            omega
          have d21869 : (x 5 4 && x 5 11).toNat = 0 := by
            have r21870 := hand1 (x 5 4) (x 5 11)
            have b21871 := hb (x 5 4)
            have b21872 := hb (x 5 4 && x 5 11)
            clear * - r21870 b21871 b21872 d21861
            omega
          have d21873 : (x 5 4 && x 5 8).toNat = 0 := by
            have r21874 := hand1 (x 5 4) (x 5 8)
            have b21875 := hb (x 5 4)
            have b21876 := hb (x 5 4 && x 5 8)
            clear * - r21874 b21875 b21876 d21861
            omega
          have d21877 : (x 4 13).toNat = 0 := by
            have r21878 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
            have e21879 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e21880 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b21881 := hb (x 2 3)
            have b21882 := hb (x 3 2)
            have b21883 := hb (x 4 13)
            have b21884 := hb (x 5 12)
            clear * - r21878 e21879 e21880 b21881 b21882 b21883 b21884 d21845 g17 d21841
            omega
          have d21885 : (x 4 2 && x 4 13).toNat = 0 := by
            have r21886 := hand2 (x 4 2) (x 4 13)
            have b21887 := hb (x 4 13)
            have b21888 := hb (x 4 2 && x 4 13)
            clear * - r21886 b21887 b21888 d21877
            omega
          have d21889 : (x 4 4 && x 4 13).toNat = 0 := by
            have r21890 := hand2 (x 4 4) (x 4 13)
            have b21891 := hb (x 4 13)
            have b21892 := hb (x 4 4 && x 4 13)
            clear * - r21890 b21891 b21892 d21877
            omega
          have d21893 : (x 4 5).toNat = 0 := by
            have r21894 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
            have b21895 := hb (x 4 5)
            have b21896 := hb (x 4 13)
            clear * - r21894 b21895 b21896 d21877
            omega
          have d21897 : (x 4 5 && x 4 12).toNat = 0 := by
            have r21898 := hand1 (x 4 5) (x 4 12)
            have b21899 := hb (x 4 5)
            have b21900 := hb (x 4 5 && x 4 12)
            clear * - r21898 b21899 b21900 d21893
            omega
          have d21901 : (x 4 5 && x 4 9).toNat = 0 := by
            have r21902 := hand1 (x 4 5) (x 4 9)
            have b21903 := hb (x 4 5)
            have b21904 := hb (x 4 5 && x 4 9)
            clear * - r21902 b21903 b21904 d21893
            omega
          have d21905 : (x 2 2).toNat = 1 := by
            have r21906 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
            have b21907 := hb (x 2 2)
            have b21908 := hb (x 4 13)
            have b21909 := hb (x 3 1 && x 3 14)
            clear * - r21906 b21907 b21908 b21909 d21877 g59
            omega
          have d21910 : (x 4 12).toNat = 0 := by
            have r21911 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e21912 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e21913 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b21914 := hb (x 1 3)
            have b21915 := hb (x 2 2)
            have b21916 := hb (x 3 13)
            have b21917 := hb (x 4 12)
            clear * - r21911 e21912 e21913 b21914 b21915 b21916 b21917 d21905 f21810
            omega
          have d21918 : (x 4 4).toNat = 0 := by
            have r21919 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b21920 := hb (x 4 4)
            have b21921 := hb (x 4 12)
            clear * - r21919 b21920 b21921 d21910
            omega
          have d21922 : (x 4 4 && x 4 9).toNat = 0 := by
            have r21923 := hand1 (x 4 4) (x 4 9)
            have b21924 := hb (x 4 4)
            have b21925 := hb (x 4 4 && x 4 9)
            clear * - r21923 b21924 b21925 d21918
            omega
          have d21926 : (x 3 13).toNat = 0 := by
            have r21927 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
            have e21928 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e21929 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b21930 := hb (x 1 3)
            have b21931 := hb (x 2 2)
            have b21932 := hb (x 3 13)
            have b21933 := hb (x 4 12)
            clear * - r21927 e21928 e21929 b21930 b21931 b21932 b21933 d21910 d21905 f21810
            omega
          have d21934 : (x 3 5).toNat = 0 := by
            have r21935 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
            have b21936 := hb (x 3 5)
            have b21937 := hb (x 3 13)
            clear * - r21935 b21936 b21937 d21926
            omega
          have d21938 : (x 5 8).toNat = 0 := by
            have r21939 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
            have e21940 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e21941 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e21942 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e21943 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e21944 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e21945 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b21946 := hb (x (-2) 7)
            have b21947 := hb (x (-1) 6)
            have b21948 := hb (x 0 5)
            have b21949 := hb (x 1 4)
            have b21950 := hb (x 2 11)
            have b21951 := hb (x 3 10)
            have b21952 := hb (x 4 9)
            have b21953 := hb (x 5 8)
            clear * - r21939 e21940 e21941 e21942 e21943 e21944 e21945 b21946 b21947 b21948 b21949 b21950 b21951 b21952 b21953 g20 d21837 d21777 g7
            omega
          have d21954 : (x 5 3 && x 5 8).toNat = 0 := by
            have r21955 := hand2 (x 5 3) (x 5 8)
            have b21956 := hb (x 5 8)
            have b21957 := hb (x 5 3 && x 5 8)
            clear * - r21955 b21956 b21957 d21938
            omega
          have d21958 : (x 5 5 && x 5 8).toNat = 0 := by
            have r21959 := hand2 (x 5 5) (x 5 8)
            have b21960 := hb (x 5 8)
            have b21961 := hb (x 5 5 && x 5 8)
            clear * - r21959 b21960 b21961 d21938
            omega
          have d21962 : (x 4 9).toNat = 0 := by
            have r21963 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
            have e21964 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e21965 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e21966 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e21967 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e21968 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e21969 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b21970 := hb (x (-2) 7)
            have b21971 := hb (x (-1) 6)
            have b21972 := hb (x 0 5)
            have b21973 := hb (x 1 4)
            have b21974 := hb (x 2 11)
            have b21975 := hb (x 3 10)
            have b21976 := hb (x 4 9)
            have b21977 := hb (x 5 8)
            clear * - r21963 e21964 e21965 e21966 e21967 e21968 e21969 b21970 b21971 b21972 b21973 b21974 b21975 b21976 b21977 d21938 g20 d21837 d21777 g7
            omega
          have d21978 : (x 4 6 && x 4 9).toNat = 0 := by
            have r21979 := hand2 (x 4 6) (x 4 9)
            have b21980 := hb (x 4 9)
            have b21981 := hb (x 4 6 && x 4 9)
            clear * - r21979 b21980 b21981 d21962
            omega
          have d21982 : (x (-1) 6).toNat = 0 := by
            have r21983 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
            have e21984 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e21985 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e21986 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e21987 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e21988 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e21989 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b21990 := hb (x (-2) 7)
            have b21991 := hb (x (-1) 6)
            have b21992 := hb (x 0 5)
            have b21993 := hb (x 1 4)
            have b21994 := hb (x 2 11)
            have b21995 := hb (x 3 10)
            have b21996 := hb (x 4 9)
            have b21997 := hb (x 5 8)
            clear * - r21983 e21984 e21985 e21986 e21987 e21988 e21989 b21990 b21991 b21992 b21993 b21994 b21995 b21996 b21997 d21938 d21962 g20 d21837 d21777 g7
            omega
          have d21998 : (x (-1) 2 && x (-1) 6).toNat = 0 := by
            have r21999 := hand2 (x (-1) 2) (x (-1) 6)
            have b22000 := hb (x (-1) 6)
            have b22001 := hb (x (-1) 2 && x (-1) 6)
            clear * - r21999 b22000 b22001 d21982
            omega
          cases h22002 : x (-1) 5
          · have f22003 : (x (-1) 5).toNat = 0 := by rw [h22002]; rfl
            cases h22004 : x (-1) 7
            · have f22005 : (x (-1) 7).toNat = 0 := by rw [h22004]; rfl
              have d22006 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
                have r22007 := hand2 (x (-1) 2) (x (-1) 7)
                have b22008 := hb (x (-1) 7)
                have b22009 := hb (x (-1) 2 && x (-1) 7)
                clear * - r22007 b22008 b22009 f22005
                omega
              cases h22010 : x 1 7
              · have f22011 : (x 1 7).toNat = 0 := by rw [h22010]; rfl
                cases h22012 : x (-1) 8
                · have f22013 : (x (-1) 8).toNat = 0 := by rw [h22012]; rfl
                  have d22014 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
                    have r22015 := hand2 (x (-1) 2) (x (-1) 8)
                    have b22016 := hb (x (-1) 8)
                    have b22017 := hb (x (-1) 2 && x (-1) 8)
                    clear * - r22015 b22016 b22017 f22013
                    omega
                  cases h22018 : x 1 8
                  · have f22019 : (x 1 8).toNat = 0 := by rw [h22018]; rfl
                    cases h22020 : x (-1) 9
                    · have f22021 : (x (-1) 9).toNat = 0 := by rw [h22020]; rfl
                      cases h22022 : x (-1) 10
                      · have f22023 : (x (-1) 10).toNat = 0 := by rw [h22022]; rfl
                        cases h22024 : x (-1) 12
                        · have f22025 : (x (-1) 12).toNat = 0 := by rw [h22024]; rfl
                          have d22026 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
                            have r22027 := hand2 (x (-1) 1) (x (-1) 12)
                            have b22028 := hb (x (-1) 12)
                            have b22029 := hb (x (-1) 1 && x (-1) 12)
                            clear * - r22027 b22028 b22029 f22025
                            omega
                          have d22030 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
                            have r22031 := hand2 (x (-1) 2) (x (-1) 12)
                            have b22032 := hb (x (-1) 12)
                            have b22033 := hb (x (-1) 2 && x (-1) 12)
                            clear * - r22031 b22032 b22033 f22025
                            omega
                          have d22034 : (x (-4) 4).toNat = 1 := by
                            have r22035 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
                            have b22036 := hb (x (-4) 4)
                            have b22037 := hb (x 0 11)
                            have b22038 := hb (x (-1) 1 && x (-1) 12)
                            have b22039 := hb (x (-2) 2 && x (-2) 13)
                            have b22040 := hb (x (-3) 3 && x (-3) 14)
                            clear * - r22035 b22036 b22037 b22038 b22039 b22040 g11 d22026 d21627 d21708
                            omega
                          have d22041 : (x (-4) 12).toNat = 1 := by
                            have r22042 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
                            have b22043 := hb (x (-4) 4)
                            have b22044 := hb (x (-4) 12)
                            clear * - r22042 b22043 b22044 d22034
                            omega
                          have d22045 : (x (-5) 13).toNat = 0 := by
                            have r22046 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
                            have e22047 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                            have e22048 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                            have b22049 := hb (x (-7) 3)
                            have b22050 := hb (x (-6) 2)
                            have b22051 := hb (x (-5) 13)
                            have b22052 := hb (x (-4) 12)
                            clear * - r22046 e22047 e22048 b22049 b22050 b22051 b22052 d22041
                            omega
                          have d22053 : (x (-5) 5).toNat = 0 := by
                            have r22054 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
                            have b22055 := hb (x (-5) 5)
                            have b22056 := hb (x (-5) 13)
                            clear * - r22054 b22055 b22056 d22045
                            omega
                          have d22057 : (x (-6) 2).toNat = 0 := by
                            have r22058 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
                            have e22059 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                            have e22060 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                            have b22061 := hb (x (-7) 3)
                            have b22062 := hb (x (-6) 2)
                            have b22063 := hb (x (-5) 13)
                            have b22064 := hb (x (-4) 12)
                            clear * - r22058 e22059 e22060 b22061 b22062 b22063 b22064 d22041 d22045
                            omega
                          have d22065 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
                            have r22066 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
                            have b22067 := hb (x (-5) 5)
                            have b22068 := hb (x 0 10)
                            have b22069 := hb (x (-1) 1 && x (-1) 11)
                            have b22070 := hb (x (-2) 2 && x (-2) 12)
                            have b22071 := hb (x (-3) 3 && x (-3) 13)
                            have b22072 := hb (x (-4) 4 && x (-4) 14)
                            clear * - r22066 b22067 b22068 b22069 b22070 b22071 b22072 g10 g46 d21631 d21712 d22053
                            omega
                          have d22073 : (x (-4) 14).toNat = 1 := by
                            have r22074 := hand2 (x (-4) 4) (x (-4) 14)
                            have b22075 := hb (x (-4) 14)
                            have b22076 := hb (x (-4) 4 && x (-4) 14)
                            clear * - r22074 b22075 b22076 d22065
                            omega
                          have d22077 : (x (-5) 1).toNat = 0 := by
                            have r22078 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
                            have b22079 := hb (x (-5) 1)
                            have b22080 := hb (x (-4) 14)
                            clear * - r22078 b22079 b22080 d22073
                            omega
                          have d22081 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
                            have r22082 := hand1 (x (-5) 1) (x (-5) 14)
                            have b22083 := hb (x (-5) 1)
                            have b22084 := hb (x (-5) 1 && x (-5) 14)
                            clear * - r22082 b22083 b22084 d22077
                            omega
                          have d22085 : (x (-4) 13).toNat = 1 := by
                            have r22086 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
                            have b22087 := hb (x (-6) 2)
                            have b22088 := hb (x (-4) 13)
                            have b22089 := hb (x (-5) 1 && x (-5) 14)
                            clear * - r22086 b22087 b22088 b22089 d22081 d22057
                            omega
                          have d22090 : (x (-4) 1).toNat = 1 := by
                            have r22091 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                            have b22092 := hb (x (-4) 1)
                            have b22093 := hb (x (-4) 13)
                            clear * - r22091 b22092 b22093 d22085
                            omega
                          have d22094 : (x (-3) 14).toNat = 0 := by
                            have r22095 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
                            have b22096 := hb (x (-4) 1)
                            have b22097 := hb (x (-3) 14)
                            clear * - r22095 b22096 b22097 d22090
                            omega
                          have d22098 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                            have r22099 := hand2 (x (-3) 1) (x (-3) 14)
                            have b22100 := hb (x (-3) 14)
                            have b22101 := hb (x (-3) 1 && x (-3) 14)
                            clear * - r22099 b22100 b22101 d22094
                            omega
                          have d22102 : (x (-4) 2).toNat = 1 := by
                            have r22103 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
                            have b22104 := hb (x (-4) 2)
                            have b22105 := hb (x (-2) 13)
                            have b22106 := hb (x (-3) 1 && x (-3) 14)
                            clear * - r22103 b22104 b22105 b22106 d21664 d22098
                            omega
                          have d22107 : (x (-2) 12).toNat = 0 := by
                            have r22108 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
                            have e22109 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                            have e22110 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                            have b22111 := hb (x (-5) 3)
                            have b22112 := hb (x (-4) 2)
                            have b22113 := hb (x (-3) 13)
                            have b22114 := hb (x (-2) 12)
                            clear * - r22108 e22109 e22110 b22111 b22112 b22113 b22114 d22102
                            omega
                          have d22115 : (x (-2) 4).toNat = 0 := by
                            have r22116 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
                            have b22117 := hb (x (-2) 4)
                            have b22118 := hb (x (-2) 12)
                            clear * - r22116 b22117 b22118 d22107
                            omega
                          have d22119 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
                            have r22120 := hand1 (x (-2) 4) (x (-2) 14)
                            have b22121 := hb (x (-2) 4)
                            have b22122 := hb (x (-2) 4 && x (-2) 14)
                            clear * - r22120 b22121 b22122 d22115
                            omega
                          have d22123 : (x (-3) 13).toNat = 0 := by
                            have r22124 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
                            have e22125 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                            have e22126 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                            have b22127 := hb (x (-5) 3)
                            have b22128 := hb (x (-4) 2)
                            have b22129 := hb (x (-3) 13)
                            have b22130 := hb (x (-2) 12)
                            clear * - r22124 e22125 e22126 b22127 b22128 b22129 b22130 d22107 d22102
                            omega
                          have d22131 : (x (-3) 5).toNat = 0 := by
                            have r22132 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
                            have b22133 := hb (x (-3) 5)
                            have b22134 := hb (x (-3) 13)
                            clear * - r22132 b22133 b22134 d22123
                            omega
                          have d22135 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
                            have r22136 := hand1 (x (-3) 5) (x (-3) 14)
                            have b22137 := hb (x (-3) 5)
                            have b22138 := hb (x (-3) 5 && x (-3) 14)
                            clear * - r22136 b22137 b22138 d22131
                            omega
                          have d22139 : (x 2 10).toNat = 1 := by
                            have r22140 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := hcov10 2
                            have b22141 := hb (x (-3) 5)
                            have b22142 := hb (x 2 10)
                            have b22143 := hb (x 1 1 && x 1 11)
                            have b22144 := hb (x 0 2 && x 0 12)
                            have b22145 := hb (x (-1) 3 && x (-1) 13)
                            have b22146 := hb (x (-2) 4 && x (-2) 14)
                            clear * - r22140 b22141 b22142 b22143 b22144 b22145 b22146 d21728 g48 g49 d22119 d22131
                            omega
                          have d22147 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
                            have r22148 := hand2 (x (-3) 4) (x (-3) 14)
                            have b22149 := hb (x (-3) 14)
                            have b22150 := hb (x (-3) 4 && x (-3) 14)
                            clear * - r22148 b22149 b22150 d22094
                            omega
                          have d22151 : (x (-4) 5).toNat = 1 := by
                            have r22152 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := hcov10 1
                            have b22153 := hb (x (-4) 5)
                            have b22154 := hb (x 1 10)
                            have b22155 := hb (x 0 1 && x 0 11)
                            have b22156 := hb (x (-1) 2 && x (-1) 12)
                            have b22157 := hb (x (-2) 3 && x (-2) 13)
                            have b22158 := hb (x (-3) 4 && x (-3) 14)
                            clear * - r22152 b22153 b22154 b22155 b22156 b22157 b22158 g16 g47 d22030 d21668 d22147
                            omega
                          have d22159 : (x (-3) 6).toNat = 0 := by
                            have r22160 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
                            have b22161 := hb (x (-3) 6)
                            have b22162 := hb (x (-3) 14)
                            clear * - r22160 b22161 b22162 d22094
                            omega
                          have d22163 : (x (-3) 4 && x (-3) 6).toNat = 0 := by
                            have r22164 := hand2 (x (-3) 4) (x (-3) 6)
                            have b22165 := hb (x (-3) 6)
                            have b22166 := hb (x (-3) 4 && x (-3) 6)
                            clear * - r22164 b22165 b22166 d22159
                            omega
                          have d22167 : (x (-3) 12).toNat = 0 := by
                            have r22168 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
                            have e22169 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                            have e22170 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                            have b22171 := hb (x (-6) 3)
                            have b22172 := hb (x (-5) 2)
                            have b22173 := hb (x (-4) 13)
                            have b22174 := hb (x (-3) 12)
                            clear * - r22168 e22169 e22170 b22171 b22172 b22173 b22174 d22085
                            omega
                          have d22175 : (x (-3) 4).toNat = 0 := by
                            have r22176 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                            have b22177 := hb (x (-3) 4)
                            have b22178 := hb (x (-3) 12)
                            clear * - r22176 b22177 b22178 d22167
                            omega
                          have d22179 : (x 4 8).toNat = 0 := by
                            have r22180 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                            have e22181 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                            have e22182 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                            have e22183 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                            have e22184 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                            have e22185 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                            have e22186 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                            have b22187 := hb (x (-3) 7)
                            have b22188 := hb (x (-2) 6)
                            have b22189 := hb (x (-1) 5)
                            have b22190 := hb (x 0 4)
                            have b22191 := hb (x 1 11)
                            have b22192 := hb (x 2 10)
                            have b22193 := hb (x 3 9)
                            have b22194 := hb (x 4 8)
                            clear * - r22180 e22181 e22182 e22183 e22184 e22185 e22186 b22187 b22188 b22189 b22190 b22191 b22192 b22193 b22194 d22139 d21811 g6 f22003
                            omega
                          have d22195 : (x 3 9).toNat = 0 := by
                            have r22196 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
                            have e22197 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                            have e22198 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                            have e22199 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                            have e22200 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                            have e22201 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                            have e22202 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                            have b22203 := hb (x (-3) 7)
                            have b22204 := hb (x (-2) 6)
                            have b22205 := hb (x (-1) 5)
                            have b22206 := hb (x 0 4)
                            have b22207 := hb (x 1 11)
                            have b22208 := hb (x 2 10)
                            have b22209 := hb (x 3 9)
                            have b22210 := hb (x 4 8)
                            clear * - r22196 e22197 e22198 e22199 e22200 e22201 e22202 b22203 b22204 b22205 b22206 b22207 b22208 b22209 b22210 d22179 d22139 d21811 g6 f22003
                            omega
                          have d22211 : (x (-5) 6).toNat = 0 := by
                            have r22212 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                            have e22213 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                            have e22214 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                            have e22215 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                            have e22216 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                            have e22217 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                            have e22218 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                            have b22219 := hb (x (-6) 7)
                            have b22220 := hb (x (-5) 6)
                            have b22221 := hb (x (-4) 5)
                            have b22222 := hb (x (-3) 4)
                            have b22223 := hb (x (-2) 11)
                            have b22224 := hb (x (-1) 10)
                            have b22225 := hb (x 0 9)
                            have b22226 := hb (x 1 8)
                            clear * - r22212 e22213 e22214 e22215 e22216 e22217 e22218 b22219 b22220 b22221 b22222 b22223 b22224 b22225 b22226 f22019 f21725 f22023 d21805 d22175 d22151
                            omega
                          have d22227 : (x (-5) 6 && x (-5) 8).toNat = 0 := by
                            have r22228 := hand1 (x (-5) 6) (x (-5) 8)
                            have b22229 := hb (x (-5) 6)
                            have b22230 := hb (x (-5) 6 && x (-5) 8)
                            clear * - r22228 b22229 b22230 d22211
                            omega
                          have d22231 : (x (-6) 7).toNat = 0 := by
                            have r22232 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                            have e22233 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                            have e22234 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                            have e22235 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                            have e22236 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                            have e22237 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                            have e22238 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                            have b22239 := hb (x (-6) 7)
                            have b22240 := hb (x (-5) 6)
                            have b22241 := hb (x (-4) 5)
                            have b22242 := hb (x (-3) 4)
                            have b22243 := hb (x (-2) 11)
                            have b22244 := hb (x (-1) 10)
                            have b22245 := hb (x 0 9)
                            have b22246 := hb (x 1 8)
                            clear * - r22232 e22233 e22234 e22235 e22236 e22237 e22238 b22239 b22240 b22241 b22242 b22243 b22244 b22245 b22246 f22019 f21725 f22023 d21805 d22175 d22151 d22211
                            omega
                          have d22247 : (x (-6) 7 && x (-6) 9).toNat = 0 := by
                            have r22248 := hand1 (x (-6) 7) (x (-6) 9)
                            have b22249 := hb (x (-6) 7)
                            have b22250 := hb (x (-6) 7 && x (-6) 9)
                            clear * - r22248 b22249 b22250 d22231
                            omega
                          have d22251 : (x (-7) 8).toNat = 0 := by
                            have r22252 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
                            have b22253 := hb (x (-13) 14)
                            have b22254 := hb (x (-12) 13)
                            have b22255 := hb (x (-11) 12)
                            have b22256 := hb (x (-10) 11)
                            have b22257 := hb (x (-9) 10)
                            have b22258 := hb (x (-8) 9)
                            have b22259 := hb (x (-7) 8)
                            have b22260 := hb (x (-6) 7)
                            have b22261 := hb (x (-5) 6)
                            have b22262 := hb (x (-4) 5)
                            have b22263 := hb (x (-3) 4)
                            have b22264 := hb (x (-2) 3)
                            have b22265 := hb (x (-1) 2)
                            have b22266 := hb (x 0 1)
                            clear * - r22252 b22253 b22254 b22255 b22256 b22257 b22258 b22259 b22260 b22261 b22262 b22263 b22264 b22265 b22266 g4 d21748 d21781 d22175 d22151 d22211 d22231
                            omega
                          have d22267 : (x (-7) 8 && x (-7) 10).toNat = 0 := by
                            have r22268 := hand1 (x (-7) 8) (x (-7) 10)
                            have b22269 := hb (x (-7) 8)
                            have b22270 := hb (x (-7) 8 && x (-7) 10)
                            clear * - r22268 b22269 b22270 d22251
                            omega
                          have d22271 : (x (-8) 9).toNat = 0 := by
                            have r22272 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
                            have b22273 := hb (x (-13) 14)
                            have b22274 := hb (x (-12) 13)
                            have b22275 := hb (x (-11) 12)
                            have b22276 := hb (x (-10) 11)
                            have b22277 := hb (x (-9) 10)
                            have b22278 := hb (x (-8) 9)
                            have b22279 := hb (x (-7) 8)
                            have b22280 := hb (x (-6) 7)
                            have b22281 := hb (x (-5) 6)
                            have b22282 := hb (x (-4) 5)
                            have b22283 := hb (x (-3) 4)
                            have b22284 := hb (x (-2) 3)
                            have b22285 := hb (x (-1) 2)
                            have b22286 := hb (x 0 1)
                            clear * - r22272 b22273 b22274 b22275 b22276 b22277 b22278 b22279 b22280 b22281 b22282 b22283 b22284 b22285 b22286 g4 d21748 d21781 d22175 d22151 d22211 d22231 d22251
                            omega
                          have d22287 : (x (-8) 9 && x (-8) 11).toNat = 0 := by
                            have r22288 := hand1 (x (-8) 9) (x (-8) 11)
                            have b22289 := hb (x (-8) 9)
                            have b22290 := hb (x (-8) 9 && x (-8) 11)
                            clear * - r22288 b22289 b22290 d22271
                            omega
                          have d22291 : (x (-9) 10).toNat = 0 := by
                            have r22292 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
                            have b22293 := hb (x (-13) 14)
                            have b22294 := hb (x (-12) 13)
                            have b22295 := hb (x (-11) 12)
                            have b22296 := hb (x (-10) 11)
                            have b22297 := hb (x (-9) 10)
                            have b22298 := hb (x (-8) 9)
                            have b22299 := hb (x (-7) 8)
                            have b22300 := hb (x (-6) 7)
                            have b22301 := hb (x (-5) 6)
                            have b22302 := hb (x (-4) 5)
                            have b22303 := hb (x (-3) 4)
                            have b22304 := hb (x (-2) 3)
                            have b22305 := hb (x (-1) 2)
                            have b22306 := hb (x 0 1)
                            clear * - r22292 b22293 b22294 b22295 b22296 b22297 b22298 b22299 b22300 b22301 b22302 b22303 b22304 b22305 b22306 g4 d21748 d21781 d22175 d22151 d22211 d22231 d22251 d22271
                            omega
                          have d22307 : (x (-9) 10 && x (-9) 12).toNat = 0 := by
                            have r22308 := hand1 (x (-9) 10) (x (-9) 12)
                            have b22309 := hb (x (-9) 10)
                            have b22310 := hb (x (-9) 10 && x (-9) 12)
                            clear * - r22308 b22309 b22310 d22291
                            omega
                          have d22311 : (x (-10) 11).toNat = 0 := by
                            have r22312 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
                            have b22313 := hb (x (-13) 14)
                            have b22314 := hb (x (-12) 13)
                            have b22315 := hb (x (-11) 12)
                            have b22316 := hb (x (-10) 11)
                            have b22317 := hb (x (-9) 10)
                            have b22318 := hb (x (-8) 9)
                            have b22319 := hb (x (-7) 8)
                            have b22320 := hb (x (-6) 7)
                            have b22321 := hb (x (-5) 6)
                            have b22322 := hb (x (-4) 5)
                            have b22323 := hb (x (-3) 4)
                            have b22324 := hb (x (-2) 3)
                            have b22325 := hb (x (-1) 2)
                            have b22326 := hb (x 0 1)
                            clear * - r22312 b22313 b22314 b22315 b22316 b22317 b22318 b22319 b22320 b22321 b22322 b22323 b22324 b22325 b22326 g4 d21748 d21781 d22175 d22151 d22211 d22231 d22251 d22271 d22291
                            omega
                          have d22327 : (x (-10) 11 && x (-10) 13).toNat = 0 := by
                            have r22328 := hand1 (x (-10) 11) (x (-10) 13)
                            have b22329 := hb (x (-10) 11)
                            have b22330 := hb (x (-10) 11 && x (-10) 13)
                            clear * - r22328 b22329 b22330 d22311
                            omega
                          have d22331 : (x (-11) 12).toNat = 0 := by
                            have r22332 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
                            have b22333 := hb (x (-13) 14)
                            have b22334 := hb (x (-12) 13)
                            have b22335 := hb (x (-11) 12)
                            have b22336 := hb (x (-10) 11)
                            have b22337 := hb (x (-9) 10)
                            have b22338 := hb (x (-8) 9)
                            have b22339 := hb (x (-7) 8)
                            have b22340 := hb (x (-6) 7)
                            have b22341 := hb (x (-5) 6)
                            have b22342 := hb (x (-4) 5)
                            have b22343 := hb (x (-3) 4)
                            have b22344 := hb (x (-2) 3)
                            have b22345 := hb (x (-1) 2)
                            have b22346 := hb (x 0 1)
                            clear * - r22332 b22333 b22334 b22335 b22336 b22337 b22338 b22339 b22340 b22341 b22342 b22343 b22344 b22345 b22346 g4 d21748 d21781 d22175 d22151 d22211 d22231 d22251 d22271 d22291 d22311
                            omega
                          have d22347 : (x (-11) 12 && x (-11) 14).toNat = 0 := by
                            have r22348 := hand1 (x (-11) 12) (x (-11) 14)
                            have b22349 := hb (x (-11) 12)
                            have b22350 := hb (x (-11) 12 && x (-11) 14)
                            clear * - r22348 b22349 b22350 d22331
                            omega
                          have d22351 : (x (-12) 13).toNat = 0 := by
                            have r22352 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
                            have b22353 := hb (x (-13) 14)
                            have b22354 := hb (x (-12) 13)
                            have b22355 := hb (x (-11) 12)
                            have b22356 := hb (x (-10) 11)
                            have b22357 := hb (x (-9) 10)
                            have b22358 := hb (x (-8) 9)
                            have b22359 := hb (x (-7) 8)
                            have b22360 := hb (x (-6) 7)
                            have b22361 := hb (x (-5) 6)
                            have b22362 := hb (x (-4) 5)
                            have b22363 := hb (x (-3) 4)
                            have b22364 := hb (x (-2) 3)
                            have b22365 := hb (x (-1) 2)
                            have b22366 := hb (x 0 1)
                            clear * - r22352 b22353 b22354 b22355 b22356 b22357 b22358 b22359 b22360 b22361 b22362 b22363 b22364 b22365 b22366 g4 d21748 d21781 d22175 d22151 d22211 d22231 d22251 d22271 d22291 d22311 d22331
                            omega
                          have d22367 : (x (-4) 5 && x (-4) 7).toNat = 1 := by
                            have r22368 : 1 ≤ (x 1 2).toNat + (x 0 1 && x 0 3).toNat + (x (-1) 2 && x (-1) 4).toNat + (x (-2) 3 && x (-2) 5).toNat + (x (-3) 4 && x (-3) 6).toNat + (x (-4) 5 && x (-4) 7).toNat + (x (-5) 6 && x (-5) 8).toNat + (x (-6) 7 && x (-6) 9).toNat + (x (-7) 8 && x (-7) 10).toNat + (x (-8) 9 && x (-8) 11).toNat + (x (-9) 10 && x (-9) 12).toNat + (x (-10) 11 && x (-10) 13).toNat + (x (-11) 12 && x (-11) 14).toNat + (x (-12) 13).toNat := hcov2 1
                            have b22369 := hb (x (-12) 13)
                            have b22370 := hb (x 1 2)
                            have b22371 := hb (x 0 1 && x 0 3)
                            have b22372 := hb (x (-1) 2 && x (-1) 4)
                            have b22373 := hb (x (-2) 3 && x (-2) 5)
                            have b22374 := hb (x (-3) 4 && x (-3) 6)
                            have b22375 := hb (x (-4) 5 && x (-4) 7)
                            have b22376 := hb (x (-5) 6 && x (-5) 8)
                            have b22377 := hb (x (-6) 7 && x (-6) 9)
                            have b22378 := hb (x (-7) 8 && x (-7) 10)
                            have b22379 := hb (x (-8) 9 && x (-8) 11)
                            have b22380 := hb (x (-9) 10 && x (-9) 12)
                            have b22381 := hb (x (-10) 11 && x (-10) 13)
                            have b22382 := hb (x (-11) 12 && x (-11) 14)
                            clear * - r22368 b22369 b22370 b22371 b22372 b22373 b22374 b22375 b22376 b22377 b22378 b22379 b22380 b22381 b22382 g14 g27 d21825 d21688 d22163 d22227 d22247 d22267 d22287 d22307 d22327 d22347 d22351
                            omega
                          have d22383 : (x (-4) 7).toNat = 1 := by
                            have r22384 := hand2 (x (-4) 5) (x (-4) 7)
                            have b22385 := hb (x (-4) 7)
                            have b22386 := hb (x (-4) 5 && x (-4) 7)
                            clear * - r22384 b22385 b22386 d22367
                            omega
                          have d22387 : (x 3 8).toNat = 0 := by
                            have r22388 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                            have e22389 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                            have e22390 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                            have e22391 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                            have e22392 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                            have e22393 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                            have e22394 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                            have b22395 := hb (x (-4) 7)
                            have b22396 := hb (x (-3) 6)
                            have b22397 := hb (x (-2) 5)
                            have b22398 := hb (x (-1) 4)
                            have b22399 := hb (x 0 11)
                            have b22400 := hb (x 1 10)
                            have b22401 := hb (x 2 9)
                            have b22402 := hb (x 3 8)
                            clear * - r22388 e22389 e22390 e22391 e22392 e22393 e22394 b22395 b22396 b22397 b22398 b22399 b22400 b22401 b22402 g16 g11 f21816 d21680 d22159 d22383
                            omega
                          have d22403 : (x 2 9).toNat = 0 := by
                            have r22404 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
                            have e22405 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                            have e22406 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                            have e22407 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                            have e22408 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                            have e22409 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                            have e22410 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                            have b22411 := hb (x (-4) 7)
                            have b22412 := hb (x (-3) 6)
                            have b22413 := hb (x (-2) 5)
                            have b22414 := hb (x (-1) 4)
                            have b22415 := hb (x 0 11)
                            have b22416 := hb (x 1 10)
                            have b22417 := hb (x 2 9)
                            have b22418 := hb (x 3 8)
                            clear * - r22404 e22405 e22406 e22407 e22408 e22409 e22410 b22411 b22412 b22413 b22414 b22415 b22416 b22417 b22418 d22387 g16 g11 f21816 d21680 d22159 d22383
                            omega
                          have d22419 : (x (-4) 6).toNat = 1 := by
                            have r22420 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := hcov9 2
                            have b22421 := hb (x (-4) 6)
                            have b22422 := hb (x 2 9)
                            have b22423 := hb (x 1 1 && x 1 10)
                            have b22424 := hb (x 0 2 && x 0 11)
                            have b22425 := hb (x (-1) 3 && x (-1) 12)
                            have b22426 := hb (x (-2) 4 && x (-2) 13)
                            have b22427 := hb (x (-3) 5 && x (-3) 14)
                            clear * - r22420 b22421 b22422 b22423 b22424 b22425 b22426 b22427 d22403 g40 g41 g42 d21672 d22135
                            omega
                          have d22428 : (x 2 8).toNat = 0 := by
                            have r22429 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                            have e22430 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                            have e22431 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                            have e22432 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                            have e22433 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                            have e22434 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                            have e22435 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                            have b22436 := hb (x (-5) 7)
                            have b22437 := hb (x (-4) 6)
                            have b22438 := hb (x (-3) 5)
                            have b22439 := hb (x (-2) 4)
                            have b22440 := hb (x (-1) 11)
                            have b22441 := hb (x 0 10)
                            have b22442 := hb (x 1 9)
                            have b22443 := hb (x 2 8)
                            clear * - r22429 e22430 e22431 e22432 e22433 e22434 e22435 b22436 b22437 b22438 b22439 b22440 b22441 b22442 b22443 d21736 g10 g2 d22115 d22131 d22419
                            omega
                          have d22444 : (x 2 8 && x 2 11).toNat = 0 := by
                            have r22445 := hand1 (x 2 8) (x 2 11)
                            have b22446 := hb (x 2 8)
                            have b22447 := hb (x 2 8 && x 2 11)
                            clear * - r22445 b22446 b22447 d22428
                            omega
                          have r22448 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := hcount 11
                          have r22449 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := hcount 12
                          have r22450 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := hcount 13
                          have r22451 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := hd8 11
                          have e22452 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                          have e22453 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                          have e22454 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                          have e22455 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                          have e22456 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                          have e22457 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                          have r22458 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
                          have e22459 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                          have e22460 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                          have e22461 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                          have e22462 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                          have e22463 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                          have e22464 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                          have r22465 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                          have e22466 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                          have e22467 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                          have r22468 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
                          have e22469 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                          have e22470 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                          have r22471 : 1 ≤ (x 10 3).toNat + (x 9 1 && x 9 4).toNat + (x 8 2 && x 8 5).toNat + (x 7 3 && x 7 6).toNat + (x 6 4 && x 6 7).toNat + (x 5 5 && x 5 8).toNat + (x 4 6 && x 4 9).toNat + (x 3 7 && x 3 10).toNat + (x 2 8 && x 2 11).toNat + (x 1 9 && x 1 12).toNat + (x 0 10 && x 0 13).toNat + (x (-1) 11 && x (-1) 14).toNat + (x (-2) 12).toNat := hcov3 10
                          have r22472 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := hcov10 9
                          have r22473 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := hcov10 13
                          have r22474 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
                          have r22475 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
                          have r22476 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                          have r22477 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                          have r22478 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                          have r22479 := hand2 (x 9 1) (x 9 4)
                          have r22480 := hand2 (x 8 2) (x 8 5)
                          have r22481 := hand2 (x 7 3) (x 7 6)
                          have r22482 := hand2 (x 6 4) (x 6 7)
                          have r22483 := hand2 (x 8 1) (x 8 11)
                          have r22484 := hand1 (x 7 2) (x 7 12)
                          have r22485 := hand1 (x 6 3) (x 6 13)
                          have r22486 := hand1 (x 12 1) (x 12 11)
                          have r22487 := hand1 (x 11 2) (x 11 12)
                          have r22488 := hand2 (x 10 3) (x 10 13)
                          have r22489 := hand1 (x 9 4) (x 9 14)
                          have r22490 := hand2 (x 11 1) (x 11 12)
                          have r22491 := hand2 (x 10 2) (x 10 13)
                          have r22492 := hand1 (x 9 3) (x 9 14)
                          have r22493 := hand1 (x 11 1) (x 11 14)
                          have b22494 := hb (x (-3) 14)
                          have b22495 := hb (x (-2) 12)
                          have b22496 := hb (x (-2) 13)
                          have b22497 := hb (x (-2) 14)
                          have b22498 := hb (x (-1) 12)
                          have b22499 := hb (x (-1) 13)
                          have b22500 := hb (x (-1) 14)
                          have b22501 := hb (x 0 11)
                          have b22502 := hb (x 0 12)
                          have b22503 := hb (x 0 13)
                          have b22504 := hb (x 1 10)
                          have b22505 := hb (x 1 11)
                          have b22506 := hb (x 1 12)
                          have b22507 := hb (x 2 9)
                          have b22508 := hb (x 2 10)
                          have b22509 := hb (x 2 11)
                          have b22510 := hb (x 3 8)
                          have b22511 := hb (x 3 9)
                          have b22512 := hb (x 3 10)
                          have b22513 := hb (x 4 5)
                          have b22514 := hb (x 4 7)
                          have b22515 := hb (x 4 8)
                          have b22516 := hb (x 4 9)
                          have b22517 := hb (x 5 6)
                          have b22518 := hb (x 5 7)
                          have b22519 := hb (x 5 8)
                          have b22520 := hb (x 6 3)
                          have b22521 := hb (x 6 5)
                          have b22522 := hb (x 6 6)
                          have b22523 := hb (x 6 7)
                          have b22524 := hb (x 7 2)
                          have b22525 := hb (x 7 4)
                          have b22526 := hb (x 7 5)
                          have b22527 := hb (x 7 6)
                          have b22528 := hb (x 8 3)
                          have b22529 := hb (x 8 4)
                          have b22530 := hb (x 8 5)
                          have b22531 := hb (x 8 7)
                          have b22532 := hb (x 8 11)
                          have b22533 := hb (x 8 13)
                          have b22534 := hb (x 9 2)
                          have b22535 := hb (x 9 3)
                          have b22536 := hb (x 9 4)
                          have b22537 := hb (x 9 6)
                          have b22538 := hb (x 9 10)
                          have b22539 := hb (x 9 12)
                          have b22540 := hb (x 10 1)
                          have b22541 := hb (x 10 2)
                          have b22542 := hb (x 10 3)
                          have b22543 := hb (x 10 5)
                          have b22544 := hb (x 10 9)
                          have b22545 := hb (x 10 13)
                          have b22546 := hb (x 11 1)
                          have b22547 := hb (x 11 2)
                          have b22548 := hb (x 11 4)
                          have b22549 := hb (x 11 8)
                          have b22550 := hb (x 11 12)
                          have b22551 := hb (x 12 1)
                          have b22552 := hb (x 12 11)
                          have b22553 := hb (x 12 13)
                          have b22554 := hb (x 13 10)
                          have b22555 := hb (x 14 9)
                          have b22556 := hb (x 15 8)
                          have b22557 := hb (x 9 1 && x 9 4)
                          have b22558 := hb (x 8 2 && x 8 5)
                          have b22559 := hb (x 7 3 && x 7 6)
                          have b22560 := hb (x 6 4 && x 6 7)
                          have b22561 := hb (x 5 5 && x 5 8)
                          have b22562 := hb (x 4 6 && x 4 9)
                          have b22563 := hb (x 3 7 && x 3 10)
                          have b22564 := hb (x 2 8 && x 2 11)
                          have b22565 := hb (x 1 9 && x 1 12)
                          have b22566 := hb (x 0 10 && x 0 13)
                          have b22567 := hb (x (-1) 11 && x (-1) 14)
                          have b22568 := hb (x 8 1 && x 8 11)
                          have b22569 := hb (x 7 2 && x 7 12)
                          have b22570 := hb (x 6 3 && x 6 13)
                          have b22571 := hb (x 5 4 && x 5 14)
                          have b22572 := hb (x 12 1 && x 12 11)
                          have b22573 := hb (x 11 2 && x 11 12)
                          have b22574 := hb (x 10 3 && x 10 13)
                          have b22575 := hb (x 9 4 && x 9 14)
                          have b22576 := hb (x 11 1 && x 11 12)
                          have b22577 := hb (x 10 2 && x 10 13)
                          have b22578 := hb (x 9 3 && x 9 14)
                          have b22579 := hb (x 11 1 && x 11 14)
                          linarith only [r22448, r22449, r22450, r22451, e22452, e22453, e22454, e22455, e22456, e22457, r22458, e22459, e22460, e22461, e22462, e22463, e22464, r22465, e22466, e22467, r22468, e22469, e22470, r22471, r22472, r22473, r22474, r22475, r22476, r22477, r22478, r22479, r22480, r22481, r22482, r22483, r22484, r22485, r22486, r22487, r22488, r22489, r22490, r22491, r22492, r22493, b22494, b22495, b22496, b22497, b22498, b22499, b22500, b22501, b22502, b22503, b22504, b22505, b22506, b22507, b22508, b22509, b22510, b22511, b22512, b22513, b22514, b22515, b22516, b22517, b22518, b22519, b22520, b22521, b22522, b22523, b22524, b22525, b22526, b22527, b22528, b22529, b22530, b22531, b22532, b22533, b22534, b22535, b22536, b22537, b22538, b22539, b22540, b22541, b22542, b22543, b22544, b22545, b22546, b22547, b22548, b22549, b22550, b22551, b22552, b22553, b22554, b22555, b22556, b22557, b22558, b22559, b22560, b22561, b22562, b22563, b22564, b22565, b22566, b22567, b22568, b22569, b22570, b22571, b22572, b22573, b22574, b22575, b22576, b22577, b22578, b22579, d22094, d22107, d21664, f22025, g3, d21648, g11, d21611, g12, g16, d21811, d21761, d22403, d22139, d21837, d22387, d22195, g20, d21893, d22179, d21962, d21938, d21958, d21978, g28, d22444, d21740, g29, g30, d21865]
                        · have f22580 : (x (-1) 12).toNat = 1 := by rw [h22024]; rfl
                          have d22581 : (x (-3) 2).toNat = 0 := by
                            have r22582 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                            have e22583 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                            have e22584 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                            have b22585 := hb (x (-4) 3)
                            have b22586 := hb (x (-3) 2)
                            have b22587 := hb (x (-2) 13)
                            have b22588 := hb (x (-1) 12)
                            clear * - r22582 e22583 e22584 b22585 b22586 b22587 b22588 f22580 d21664
                            omega
                          have d22589 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
                            have r22590 := hand1 (x (-3) 2) (x (-3) 13)
                            have b22591 := hb (x (-3) 2)
                            have b22592 := hb (x (-3) 2 && x (-3) 13)
                            clear * - r22590 b22591 b22592 d22581
                            omega
                          have d22593 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                            have r22594 := hand1 (x (-3) 2) (x (-3) 12)
                            have b22595 := hb (x (-3) 2)
                            have b22596 := hb (x (-3) 2 && x (-3) 12)
                            clear * - r22594 b22595 b22596 d22581
                            omega
                          have d22597 : (x (-3) 10).toNat = 0 := by
                            have r22598 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
                            have b22599 := hb (x (-3) 2)
                            have b22600 := hb (x (-3) 10)
                            clear * - r22598 b22599 b22600 d22581
                            omega
                          have d22601 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
                            have r22602 := hand2 (x (-3) 4) (x (-3) 10)
                            have b22603 := hb (x (-3) 10)
                            have b22604 := hb (x (-3) 4 && x (-3) 10)
                            clear * - r22602 b22603 b22604 d22597
                            omega
                          have d22605 : (x (-4) 3).toNat = 0 := by
                            have r22606 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
                            have e22607 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                            have e22608 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                            have b22609 := hb (x (-4) 3)
                            have b22610 := hb (x (-3) 2)
                            have b22611 := hb (x (-2) 13)
                            have b22612 := hb (x (-1) 12)
                            clear * - r22606 e22607 e22608 b22609 b22610 b22611 b22612 f22580 d21664 d22581
                            omega
                          have d22613 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                            have r22614 := hand1 (x (-4) 3) (x (-4) 14)
                            have b22615 := hb (x (-4) 3)
                            have b22616 := hb (x (-4) 3 && x (-4) 14)
                            clear * - r22614 b22615 b22616 d22605
                            omega
                          have d22617 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                            have r22618 := hand1 (x (-4) 3) (x (-4) 13)
                            have b22619 := hb (x (-4) 3)
                            have b22620 := hb (x (-4) 3 && x (-4) 13)
                            clear * - r22618 b22619 b22620 d22605
                            omega
                          have d22621 : (x (-4) 11).toNat = 0 := by
                            have r22622 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                            have b22623 := hb (x (-4) 3)
                            have b22624 := hb (x (-4) 11)
                            clear * - r22622 b22623 b22624 d22605
                            omega
                          have d22625 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
                            have r22626 := hand2 (x (-4) 5) (x (-4) 11)
                            have b22627 := hb (x (-4) 11)
                            have b22628 := hb (x (-4) 5 && x (-4) 11)
                            clear * - r22626 b22627 b22628 d22621
                            omega
                          have d22629 : (x (-5) 4).toNat = 1 := by
                            have r22630 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := hcov11 (-1)
                            have b22631 := hb (x (-5) 4)
                            have b22632 := hb (x (-1) 11)
                            have b22633 := hb (x (-2) 1 && x (-2) 12)
                            have b22634 := hb (x (-3) 2 && x (-3) 13)
                            have b22635 := hb (x (-4) 3 && x (-4) 14)
                            clear * - r22630 b22631 b22632 b22633 b22634 b22635 g2 d21656 d22589 d22613
                            omega
                          have d22636 : (x (-5) 12).toNat = 1 := by
                            have r22637 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                            have b22638 := hb (x (-5) 4)
                            have b22639 := hb (x (-5) 12)
                            clear * - r22637 b22638 b22639 d22629
                            omega
                          have d22640 : (x (-6) 13).toNat = 0 := by
                            have r22641 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
                            have e22642 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                            have e22643 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                            have b22644 := hb (x (-8) 3)
                            have b22645 := hb (x (-7) 2)
                            have b22646 := hb (x (-6) 13)
                            have b22647 := hb (x (-5) 12)
                            clear * - r22641 e22642 e22643 b22644 b22645 b22646 b22647 d22636
                            omega
                          have d22648 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
                            have r22649 := hand2 (x (-6) 7) (x (-6) 13)
                            have b22650 := hb (x (-6) 13)
                            have b22651 := hb (x (-6) 7 && x (-6) 13)
                            clear * - r22649 b22650 b22651 d22640
                            omega
                          have d22652 : (x (-6) 5).toNat = 0 := by
                            have r22653 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                            have b22654 := hb (x (-6) 5)
                            have b22655 := hb (x (-6) 13)
                            clear * - r22653 b22654 b22655 d22640
                            omega
                          have d22656 : (x (-7) 2).toNat = 0 := by
                            have r22657 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
                            have e22658 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                            have e22659 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                            have b22660 := hb (x (-8) 3)
                            have b22661 := hb (x (-7) 2)
                            have b22662 := hb (x (-6) 13)
                            have b22663 := hb (x (-5) 12)
                            clear * - r22657 e22658 e22659 b22660 b22661 b22662 b22663 d22636 d22640
                            omega
                          have d22664 : (x (-5) 4 && x (-5) 14).toNat = 1 := by
                            have r22665 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
                            have b22666 := hb (x (-6) 5)
                            have b22667 := hb (x (-1) 10)
                            have b22668 := hb (x (-2) 1 && x (-2) 11)
                            have b22669 := hb (x (-3) 2 && x (-3) 12)
                            have b22670 := hb (x (-4) 3 && x (-4) 13)
                            have b22671 := hb (x (-5) 4 && x (-5) 14)
                            clear * - r22665 b22666 b22667 b22668 b22669 b22670 b22671 f22023 d21660 d22593 d22617 d22652
                            omega
                          have d22672 : (x (-5) 14).toNat = 1 := by
                            have r22673 := hand2 (x (-5) 4) (x (-5) 14)
                            have b22674 := hb (x (-5) 14)
                            have b22675 := hb (x (-5) 4 && x (-5) 14)
                            clear * - r22673 b22674 b22675 d22664
                            omega
                          have d22676 : (x (-6) 1).toNat = 0 := by
                            have r22677 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
                            have b22678 := hb (x (-6) 1)
                            have b22679 := hb (x (-5) 14)
                            clear * - r22677 b22678 b22679 d22672
                            omega
                          have d22680 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
                            have r22681 := hand1 (x (-6) 1) (x (-6) 14)
                            have b22682 := hb (x (-6) 1)
                            have b22683 := hb (x (-6) 1 && x (-6) 14)
                            clear * - r22681 b22682 b22683 d22676
                            omega
                          have d22684 : (x (-5) 13).toNat = 1 := by
                            have r22685 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
                            have b22686 := hb (x (-7) 2)
                            have b22687 := hb (x (-5) 13)
                            have b22688 := hb (x (-6) 1 && x (-6) 14)
                            clear * - r22685 b22686 b22687 b22688 d22680 d22656
                            omega
                          have d22689 : (x (-5) 1).toNat = 1 := by
                            have r22690 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                            have b22691 := hb (x (-5) 1)
                            have b22692 := hb (x (-5) 13)
                            clear * - r22690 b22691 b22692 d22684
                            omega
                          have d22693 : (x (-4) 14).toNat = 0 := by
                            have r22694 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
                            have b22695 := hb (x (-5) 1)
                            have b22696 := hb (x (-4) 14)
                            clear * - r22694 b22695 b22696 d22689
                            omega
                          have d22697 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
                            have r22698 := hand2 (x (-4) 4) (x (-4) 14)
                            have b22699 := hb (x (-4) 14)
                            have b22700 := hb (x (-4) 4 && x (-4) 14)
                            clear * - r22698 b22699 b22700 d22693
                            omega
                          have d22701 : (x (-5) 5).toNat = 1 := by
                            have r22702 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
                            have b22703 := hb (x (-5) 5)
                            have b22704 := hb (x 0 10)
                            have b22705 := hb (x (-1) 1 && x (-1) 11)
                            have b22706 := hb (x (-2) 2 && x (-2) 12)
                            have b22707 := hb (x (-3) 3 && x (-3) 13)
                            have b22708 := hb (x (-4) 4 && x (-4) 14)
                            clear * - r22702 b22703 b22704 b22705 b22706 b22707 b22708 g10 g46 d21631 d21712 d22697
                            omega
                          have d22709 : (x (-4) 6).toNat = 0 := by
                            have r22710 : (x (-4) 6).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp6 (-4))
                            have b22711 := hb (x (-4) 6)
                            have b22712 := hb (x (-4) 14)
                            clear * - r22710 b22711 b22712 d22693
                            omega
                          have d22713 : (x (-4) 4 && x (-4) 6).toNat = 0 := by
                            have r22714 := hand2 (x (-4) 4) (x (-4) 6)
                            have b22715 := hb (x (-4) 6)
                            have b22716 := hb (x (-4) 4 && x (-4) 6)
                            clear * - r22714 b22715 b22716 d22709
                            omega
                          have d22717 : (x (-4) 2).toNat = 0 := by
                            have r22718 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                            have b22719 := hb (x (-4) 2)
                            have b22720 := hb (x (-4) 14)
                            clear * - r22718 b22719 b22720 d22693
                            omega
                          have d22721 : (x (-4) 10).toNat = 0 := by
                            have r22722 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
                            have b22723 := hb (x (-4) 2)
                            have b22724 := hb (x (-4) 10)
                            clear * - r22722 b22723 b22724 d22717
                            omega
                          have d22725 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
                            have r22726 := hand2 (x (-4) 5) (x (-4) 10)
                            have b22727 := hb (x (-4) 10)
                            have b22728 := hb (x (-4) 5 && x (-4) 10)
                            clear * - r22726 b22727 b22728 d22721
                            omega
                          have d22729 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
                            have r22730 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
                            have b22731 := hb (x (-4) 2)
                            have b22732 := hb (x (-2) 13)
                            have b22733 := hb (x (-3) 1 && x (-3) 14)
                            clear * - r22730 b22731 b22732 b22733 d21664 d22717
                            omega
                          have d22734 : (x (-3) 14).toNat = 1 := by
                            have r22735 := hand2 (x (-3) 1) (x (-3) 14)
                            have b22736 := hb (x (-3) 14)
                            have b22737 := hb (x (-3) 1 && x (-3) 14)
                            clear * - r22735 b22736 b22737 d22729
                            omega
                          have d22738 : (x (-4) 1).toNat = 0 := by
                            have r22739 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
                            have b22740 := hb (x (-4) 1)
                            have b22741 := hb (x (-3) 14)
                            clear * - r22739 b22740 b22741 d22734
                            omega
                          have d22742 : (x (-4) 13).toNat = 0 := by
                            have r22743 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                            have b22744 := hb (x (-4) 1)
                            have b22745 := hb (x (-4) 13)
                            clear * - r22743 b22744 b22745 d22738
                            omega
                          have d22746 : (x (-4) 5).toNat = 0 := by
                            have r22747 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
                            have b22748 := hb (x (-4) 5)
                            have b22749 := hb (x (-4) 13)
                            clear * - r22747 b22748 b22749 d22742
                            omega
                          have d22750 : (x (-4) 12).toNat = 0 := by
                            have r22751 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
                            have e22752 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                            have e22753 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                            have b22754 := hb (x (-7) 3)
                            have b22755 := hb (x (-6) 2)
                            have b22756 := hb (x (-5) 13)
                            have b22757 := hb (x (-4) 12)
                            clear * - r22751 e22752 e22753 b22754 b22755 b22756 b22757 d22684
                            omega
                          have d22758 : (x (-4) 4).toNat = 0 := by
                            have r22759 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
                            have b22760 := hb (x (-4) 4)
                            have b22761 := hb (x (-4) 12)
                            clear * - r22759 b22760 b22761 d22750
                            omega
                          have d22762 : (x (-6) 6).toNat = 0 := by
                            have r22763 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                            have e22764 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                            have e22765 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                            have e22766 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                            have e22767 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                            have e22768 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                            have e22769 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                            have b22770 := hb (x (-7) 7)
                            have b22771 := hb (x (-6) 6)
                            have b22772 := hb (x (-5) 5)
                            have b22773 := hb (x (-4) 4)
                            have b22774 := hb (x (-3) 11)
                            have b22775 := hb (x (-2) 10)
                            have b22776 := hb (x (-1) 9)
                            have b22777 := hb (x 0 8)
                            clear * - r22763 e22764 e22765 e22766 e22767 e22768 e22769 b22770 b22771 b22772 b22773 b22774 b22775 b22776 b22777 g9 f22021 d21639 d21720 d22758 d22701
                            omega
                          have d22778 : (x (-6) 6 && x (-6) 8).toNat = 0 := by
                            have r22779 := hand1 (x (-6) 6) (x (-6) 8)
                            have b22780 := hb (x (-6) 6)
                            have b22781 := hb (x (-6) 6 && x (-6) 8)
                            clear * - r22779 b22780 b22781 d22762
                            omega
                          have d22782 : (x (-7) 7).toNat = 0 := by
                            have r22783 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                            have e22784 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                            have e22785 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                            have e22786 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                            have e22787 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                            have e22788 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                            have e22789 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                            have b22790 := hb (x (-7) 7)
                            have b22791 := hb (x (-6) 6)
                            have b22792 := hb (x (-5) 5)
                            have b22793 := hb (x (-4) 4)
                            have b22794 := hb (x (-3) 11)
                            have b22795 := hb (x (-2) 10)
                            have b22796 := hb (x (-1) 9)
                            have b22797 := hb (x 0 8)
                            clear * - r22783 e22784 e22785 e22786 e22787 e22788 e22789 b22790 b22791 b22792 b22793 b22794 b22795 b22796 b22797 g9 f22021 d21639 d21720 d22758 d22701 d22762
                            omega
                          have d22798 : (x (-7) 7 && x (-7) 9).toNat = 0 := by
                            have r22799 := hand1 (x (-7) 7) (x (-7) 9)
                            have b22800 := hb (x (-7) 7)
                            have b22801 := hb (x (-7) 7 && x (-7) 9)
                            clear * - r22799 b22800 b22801 d22782
                            omega
                          have r22802 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := hcount 0
                          have r22803 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
                          have r22804 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := hcount 11
                          have r22805 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                          have e22806 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                          have e22807 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                          have e22808 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                          have e22809 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                          have e22810 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                          have e22811 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                          have r22812 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
                          have e22813 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                          have e22814 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                          have e22815 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                          have e22816 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                          have e22817 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                          have e22818 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                          have r22819 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
                          have e22820 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                          have e22821 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                          have r22822 : 1 ≤ (x 10 1).toNat + (x 9 1 && x 9 2).toNat + (x 8 2 && x 8 3).toNat + (x 7 3 && x 7 4).toNat + (x 6 4 && x 6 5).toNat + (x 5 5 && x 5 6).toNat + (x 4 6 && x 4 7).toNat + (x 3 7 && x 3 8).toNat + (x 2 8 && x 2 9).toNat + (x 1 9 && x 1 10).toNat + (x 0 10 && x 0 11).toNat + (x (-1) 11 && x (-1) 12).toNat + (x (-2) 12 && x (-2) 13).toNat + (x (-3) 13 && x (-3) 14).toNat + (x (-4) 14).toNat := hcov1 10
                          have r22823 : 1 ≤ (x 0 2).toNat + (x (-1) 1 && x (-1) 3).toNat + (x (-2) 2 && x (-2) 4).toNat + (x (-3) 3 && x (-3) 5).toNat + (x (-4) 4 && x (-4) 6).toNat + (x (-5) 5 && x (-5) 7).toNat + (x (-6) 6 && x (-6) 8).toNat + (x (-7) 7 && x (-7) 9).toNat + (x (-8) 8 && x (-8) 10).toNat + (x (-9) 9 && x (-9) 11).toNat + (x (-10) 10 && x (-10) 12).toNat + (x (-11) 11 && x (-11) 13).toNat + (x (-12) 12 && x (-12) 14).toNat + (x (-13) 13).toNat := hcov2 0
                          have r22824 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := hcov5 1
                          have r22825 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := hcov6 1
                          have r22826 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := hcov9 2
                          have r22827 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := hcov13 (-12)
                          have r22828 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
                          have r22829 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                          have r22830 := hand2 (x 9 1) (x 9 2)
                          have r22831 := hand2 (x 8 2) (x 8 3)
                          have r22832 := hand2 (x 7 3) (x 7 4)
                          have r22833 := hand2 (x 6 4) (x 6 5)
                          have r22834 := hand2 (x 5 5) (x 5 6)
                          have r22835 := hand2 (x 4 6) (x 4 7)
                          have r22836 := hand2 (x 3 7) (x 3 8)
                          have r22837 := hand1 (x 2 8) (x 2 9)
                          have r22838 := hand1 (x (-3) 13) (x (-3) 14)
                          have r22839 := hand2 (x (-5) 5) (x (-5) 7)
                          have r22840 := hand1 (x (-8) 8) (x (-8) 10)
                          have r22841 := hand1 (x (-9) 9) (x (-9) 11)
                          have r22842 := hand1 (x (-10) 10) (x (-10) 12)
                          have r22843 := hand1 (x (-11) 11) (x (-11) 13)
                          have r22844 := hand1 (x (-12) 12) (x (-12) 14)
                          have r22845 := hand1 (x (-3) 4) (x (-3) 9)
                          have r22846 := hand2 (x (-5) 6) (x (-5) 11)
                          have r22847 := hand1 (x (-6) 7) (x (-6) 12)
                          have r22848 := hand1 (x (-7) 8) (x (-7) 13)
                          have r22849 := hand1 (x (-8) 9) (x (-8) 14)
                          have r22850 := hand1 (x (-5) 6) (x (-5) 12)
                          have r22851 := hand1 (x (-7) 8) (x (-7) 14)
                          have r22852 := hand1 (x (-3) 5) (x (-3) 14)
                          have r22853 := hand2 (x (-13) 1) (x (-13) 14)
                          have b22854 := hb (x (-14) 2)
                          have b22855 := hb (x (-14) 14)
                          have b22856 := hb (x (-13) 13)
                          have b22857 := hb (x (-13) 14)
                          have b22858 := hb (x (-12) 12)
                          have b22859 := hb (x (-12) 13)
                          have b22860 := hb (x (-11) 11)
                          have b22861 := hb (x (-11) 12)
                          have b22862 := hb (x (-10) 10)
                          have b22863 := hb (x (-10) 11)
                          have b22864 := hb (x (-9) 9)
                          have b22865 := hb (x (-9) 10)
                          have b22866 := hb (x (-8) 8)
                          have b22867 := hb (x (-8) 9)
                          have b22868 := hb (x (-7) 7)
                          have b22869 := hb (x (-7) 8)
                          have b22870 := hb (x (-6) 6)
                          have b22871 := hb (x (-6) 7)
                          have b22872 := hb (x (-5) 3)
                          have b22873 := hb (x (-5) 5)
                          have b22874 := hb (x (-5) 6)
                          have b22875 := hb (x (-5) 7)
                          have b22876 := hb (x (-5) 11)
                          have b22877 := hb (x (-4) 2)
                          have b22878 := hb (x (-4) 4)
                          have b22879 := hb (x (-4) 5)
                          have b22880 := hb (x (-4) 6)
                          have b22881 := hb (x (-4) 14)
                          have b22882 := hb (x (-3) 3)
                          have b22883 := hb (x (-3) 4)
                          have b22884 := hb (x (-3) 5)
                          have b22885 := hb (x (-3) 13)
                          have b22886 := hb (x (-3) 14)
                          have b22887 := hb (x (-2) 2)
                          have b22888 := hb (x (-2) 3)
                          have b22889 := hb (x (-2) 4)
                          have b22890 := hb (x (-2) 11)
                          have b22891 := hb (x (-2) 12)
                          have b22892 := hb (x (-2) 13)
                          have b22893 := hb (x (-1) 1)
                          have b22894 := hb (x (-1) 2)
                          have b22895 := hb (x (-1) 10)
                          have b22896 := hb (x (-1) 11)
                          have b22897 := hb (x (-1) 12)
                          have b22898 := hb (x 0 1)
                          have b22899 := hb (x 0 2)
                          have b22900 := hb (x 0 9)
                          have b22901 := hb (x 0 10)
                          have b22902 := hb (x 0 11)
                          have b22903 := hb (x 1 5)
                          have b22904 := hb (x 1 6)
                          have b22905 := hb (x 1 8)
                          have b22906 := hb (x 1 9)
                          have b22907 := hb (x 1 10)
                          have b22908 := hb (x 2 8)
                          have b22909 := hb (x 2 9)
                          have b22910 := hb (x 3 8)
                          have b22911 := hb (x 4 7)
                          have b22912 := hb (x 5 6)
                          have b22913 := hb (x 6 5)
                          have b22914 := hb (x 7 4)
                          have b22915 := hb (x 8 3)
                          have b22916 := hb (x 9 2)
                          have b22917 := hb (x 10 1)
                          have b22918 := hb (x 9 1 && x 9 2)
                          have b22919 := hb (x 8 2 && x 8 3)
                          have b22920 := hb (x 7 3 && x 7 4)
                          have b22921 := hb (x 6 4 && x 6 5)
                          have b22922 := hb (x 5 5 && x 5 6)
                          have b22923 := hb (x 4 6 && x 4 7)
                          have b22924 := hb (x 3 7 && x 3 8)
                          have b22925 := hb (x 2 8 && x 2 9)
                          have b22926 := hb (x 1 9 && x 1 10)
                          have b22927 := hb (x 0 10 && x 0 11)
                          have b22928 := hb (x (-1) 11 && x (-1) 12)
                          have b22929 := hb (x (-2) 12 && x (-2) 13)
                          have b22930 := hb (x (-3) 13 && x (-3) 14)
                          have b22931 := hb (x (-1) 1 && x (-1) 3)
                          have b22932 := hb (x (-2) 2 && x (-2) 4)
                          have b22933 := hb (x (-3) 3 && x (-3) 5)
                          have b22934 := hb (x (-4) 4 && x (-4) 6)
                          have b22935 := hb (x (-5) 5 && x (-5) 7)
                          have b22936 := hb (x (-6) 6 && x (-6) 8)
                          have b22937 := hb (x (-7) 7 && x (-7) 9)
                          have b22938 := hb (x (-8) 8 && x (-8) 10)
                          have b22939 := hb (x (-9) 9 && x (-9) 11)
                          have b22940 := hb (x (-10) 10 && x (-10) 12)
                          have b22941 := hb (x (-11) 11 && x (-11) 13)
                          have b22942 := hb (x (-12) 12 && x (-12) 14)
                          have b22943 := hb (x 0 1 && x 0 6)
                          have b22944 := hb (x (-1) 2 && x (-1) 7)
                          have b22945 := hb (x (-2) 3 && x (-2) 8)
                          have b22946 := hb (x (-3) 4 && x (-3) 9)
                          have b22947 := hb (x (-4) 5 && x (-4) 10)
                          have b22948 := hb (x (-5) 6 && x (-5) 11)
                          have b22949 := hb (x (-6) 7 && x (-6) 12)
                          have b22950 := hb (x (-7) 8 && x (-7) 13)
                          have b22951 := hb (x (-8) 9 && x (-8) 14)
                          have b22952 := hb (x 0 1 && x 0 7)
                          have b22953 := hb (x (-1) 2 && x (-1) 8)
                          have b22954 := hb (x (-2) 3 && x (-2) 9)
                          have b22955 := hb (x (-3) 4 && x (-3) 10)
                          have b22956 := hb (x (-4) 5 && x (-4) 11)
                          have b22957 := hb (x (-5) 6 && x (-5) 12)
                          have b22958 := hb (x (-6) 7 && x (-6) 13)
                          have b22959 := hb (x (-7) 8 && x (-7) 14)
                          have b22960 := hb (x 1 1 && x 1 10)
                          have b22961 := hb (x 0 2 && x 0 11)
                          have b22962 := hb (x (-1) 3 && x (-1) 12)
                          have b22963 := hb (x (-2) 4 && x (-2) 13)
                          have b22964 := hb (x (-3) 5 && x (-3) 14)
                          have b22965 := hb (x (-13) 1 && x (-13) 14)
                          linarith only [r22802, r22803, r22804, r22805, e22806, e22807, e22808, e22809, e22810, e22811, r22812, e22813, e22814, e22815, e22816, e22817, e22818, r22819, e22820, e22821, r22822, r22823, r22824, r22825, r22826, r22827, r22828, r22829, r22830, r22831, r22832, r22833, r22834, r22835, r22836, r22837, r22838, r22839, r22840, r22841, r22842, r22843, r22844, r22845, r22846, r22847, r22848, r22849, r22850, r22851, r22852, r22853, b22854, b22855, b22856, b22857, b22858, b22859, b22860, b22861, b22862, b22863, b22864, b22865, b22866, b22867, b22868, b22869, b22870, b22871, b22872, b22873, b22874, b22875, b22876, b22877, b22878, b22879, b22880, b22881, b22882, b22883, b22884, b22885, b22886, b22887, b22888, b22889, b22890, b22891, b22892, b22893, b22894, b22895, b22896, b22897, b22898, b22899, b22900, b22901, b22902, b22903, b22904, b22905, b22906, b22907, b22908, b22909, b22910, b22911, b22912, b22913, b22914, b22915, b22916, b22917, b22918, b22919, b22920, b22921, b22922, b22923, b22924, b22925, b22926, b22927, b22928, b22929, b22930, b22931, b22932, b22933, b22934, b22935, b22936, b22937, b22938, b22939, b22940, b22941, b22942, b22943, b22944, b22945, b22946, b22947, b22948, b22949, b22950, b22951, b22952, b22953, b22954, b22955, b22956, b22957, b22958, b22959, b22960, b22961, b22962, b22963, b22964, b22965, d22782, d22762, d22701, d22717, d22758, d22746, d22709, d22693, d21700, d22734, d21619, d21781, d21805, d21664, g0, d21748, f22023, g2, f22580, g4, g5, f21725, g10, g11, d21744, g15, f22019, d21736, g16, g23, g24, g25, d21676, g26, d21635, d21716, d22713, d22778, d22798, g33, d22006, d21793, d22725, g36, d22014, d21696, d22601, d22625, d22648, g40, g41, g42, d21672]
                      · have f22966 : (x (-1) 10).toNat = 1 := by rw [h22022]; rfl
                        have d22967 : (x (-3) 4).toNat = 0 := by
                          have r22968 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                          have e22969 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                          have e22970 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                          have e22971 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                          have e22972 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                          have e22973 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                          have e22974 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                          have b22975 := hb (x (-6) 7)
                          have b22976 := hb (x (-5) 6)
                          have b22977 := hb (x (-4) 5)
                          have b22978 := hb (x (-3) 4)
                          have b22979 := hb (x (-2) 11)
                          have b22980 := hb (x (-1) 10)
                          have b22981 := hb (x 0 9)
                          have b22982 := hb (x 1 8)
                          clear * - r22968 e22969 e22970 e22971 e22972 e22973 e22974 b22975 b22976 b22977 b22978 b22979 b22980 b22981 b22982 f22019 f21725 f22966 d21805
                          omega
                        have d22983 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
                          have r22984 := hand1 (x (-3) 4) (x (-3) 13)
                          have b22985 := hb (x (-3) 4)
                          have b22986 := hb (x (-3) 4 && x (-3) 13)
                          clear * - r22984 b22985 b22986 d22967
                          omega
                        have d22987 : (x (-4) 5).toNat = 0 := by
                          have r22988 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                          have e22989 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                          have e22990 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                          have e22991 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                          have e22992 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                          have e22993 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                          have e22994 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                          have b22995 := hb (x (-6) 7)
                          have b22996 := hb (x (-5) 6)
                          have b22997 := hb (x (-4) 5)
                          have b22998 := hb (x (-3) 4)
                          have b22999 := hb (x (-2) 11)
                          have b23000 := hb (x (-1) 10)
                          have b23001 := hb (x 0 9)
                          have b23002 := hb (x 1 8)
                          clear * - r22988 e22989 e22990 e22991 e22992 e22993 e22994 b22995 b22996 b22997 b22998 b22999 b23000 b23001 b23002 f22019 f21725 f22966 d21805 d22967
                          omega
                        have d23003 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
                          have r23004 := hand1 (x (-4) 5) (x (-4) 14)
                          have b23005 := hb (x (-4) 5)
                          have b23006 := hb (x (-4) 5 && x (-4) 14)
                          clear * - r23004 b23005 b23006 d22987
                          omega
                        have d23007 : (x (-5) 6).toNat = 1 := by
                          have r23008 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
                          have b23009 := hb (x (-5) 6)
                          have b23010 := hb (x 1 9)
                          have b23011 := hb (x 0 1 && x 0 10)
                          have b23012 := hb (x (-1) 2 && x (-1) 11)
                          have b23013 := hb (x (-2) 3 && x (-2) 12)
                          have b23014 := hb (x (-3) 4 && x (-3) 13)
                          have b23015 := hb (x (-4) 5 && x (-4) 14)
                          clear * - r23008 b23009 b23010 b23011 b23012 b23013 b23014 b23015 d21736 g38 g39 d21789 d22983 d23003
                          omega
                        have r23016 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                        have e23017 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                        have e23018 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                        have e23019 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                        have e23020 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                        have e23021 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                        have e23022 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                        have b23023 := hb (x (-6) 7)
                        have b23024 := hb (x (-5) 6)
                        have b23025 := hb (x (-4) 5)
                        have b23026 := hb (x (-3) 4)
                        have b23027 := hb (x (-2) 11)
                        have b23028 := hb (x (-1) 10)
                        have b23029 := hb (x 0 9)
                        have b23030 := hb (x 1 8)
                        linarith only [r23016, e23017, e23018, e23019, e23020, e23021, e23022, b23023, b23024, b23025, b23026, b23027, b23028, b23029, b23030, f22019, f21725, f22966, d21805, d22967, d22987, d23007]
                    · have f23031 : (x (-1) 9).toNat = 1 := by rw [h22020]; rfl
                      have d23032 : (x (-4) 4).toNat = 0 := by
                        have r23033 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                        have e23034 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                        have e23035 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                        have e23036 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                        have e23037 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                        have e23038 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                        have e23039 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                        have b23040 := hb (x (-7) 7)
                        have b23041 := hb (x (-6) 6)
                        have b23042 := hb (x (-5) 5)
                        have b23043 := hb (x (-4) 4)
                        have b23044 := hb (x (-3) 11)
                        have b23045 := hb (x (-2) 10)
                        have b23046 := hb (x (-1) 9)
                        have b23047 := hb (x 0 8)
                        clear * - r23033 e23034 e23035 e23036 e23037 e23038 e23039 b23040 b23041 b23042 b23043 b23044 b23045 b23046 b23047 g9 f23031 d21639 d21720
                        omega
                      have d23048 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
                        have r23049 := hand1 (x (-4) 4) (x (-4) 14)
                        have b23050 := hb (x (-4) 4)
                        have b23051 := hb (x (-4) 4 && x (-4) 14)
                        clear * - r23049 b23050 b23051 d23032
                        omega
                      have d23052 : (x (-5) 5).toNat = 1 := by
                        have r23053 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
                        have b23054 := hb (x (-5) 5)
                        have b23055 := hb (x 0 10)
                        have b23056 := hb (x (-1) 1 && x (-1) 11)
                        have b23057 := hb (x (-2) 2 && x (-2) 12)
                        have b23058 := hb (x (-3) 3 && x (-3) 13)
                        have b23059 := hb (x (-4) 4 && x (-4) 14)
                        clear * - r23053 b23054 b23055 b23056 b23057 b23058 b23059 g10 g46 d21631 d21712 d23048
                        omega
                      have r23060 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                      have e23061 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                      have e23062 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                      have e23063 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                      have e23064 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                      have e23065 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                      have e23066 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                      have b23067 := hb (x (-7) 7)
                      have b23068 := hb (x (-6) 6)
                      have b23069 := hb (x (-5) 5)
                      have b23070 := hb (x (-4) 4)
                      have b23071 := hb (x (-3) 11)
                      have b23072 := hb (x (-2) 10)
                      have b23073 := hb (x (-1) 9)
                      have b23074 := hb (x 0 8)
                      linarith only [r23060, e23061, e23062, e23063, e23064, e23065, e23066, b23067, b23068, b23069, b23070, b23071, b23072, b23073, b23074, g9, f23031, d21639, d21720, d23032, d23052]
                  · have f23075 : (x 1 8).toNat = 1 := by rw [h22018]; rfl
                    have d23076 : (x (-1) 10).toNat = 0 := by
                      have r23077 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                      have e23078 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                      have e23079 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                      have e23080 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                      have e23081 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                      have e23082 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                      have e23083 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                      have b23084 := hb (x (-6) 7)
                      have b23085 := hb (x (-5) 6)
                      have b23086 := hb (x (-4) 5)
                      have b23087 := hb (x (-3) 4)
                      have b23088 := hb (x (-2) 11)
                      have b23089 := hb (x (-1) 10)
                      have b23090 := hb (x 0 9)
                      have b23091 := hb (x 1 8)
                      clear * - r23077 e23078 e23079 e23080 e23081 e23082 e23083 b23084 b23085 b23086 b23087 b23088 b23089 b23090 b23091 f23075 f21725 d21805
                      omega
                    have d23092 : (x (-3) 4).toNat = 0 := by
                      have r23093 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                      have e23094 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                      have e23095 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                      have e23096 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                      have e23097 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                      have e23098 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                      have e23099 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                      have b23100 := hb (x (-6) 7)
                      have b23101 := hb (x (-5) 6)
                      have b23102 := hb (x (-4) 5)
                      have b23103 := hb (x (-3) 4)
                      have b23104 := hb (x (-2) 11)
                      have b23105 := hb (x (-1) 10)
                      have b23106 := hb (x 0 9)
                      have b23107 := hb (x 1 8)
                      clear * - r23093 e23094 e23095 e23096 e23097 e23098 e23099 b23100 b23101 b23102 b23103 b23104 b23105 b23106 b23107 f23075 f21725 d23076 d21805
                      omega
                    have d23108 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
                      have r23109 := hand1 (x (-3) 4) (x (-3) 13)
                      have b23110 := hb (x (-3) 4)
                      have b23111 := hb (x (-3) 4 && x (-3) 13)
                      clear * - r23109 b23110 b23111 d23092
                      omega
                    have d23112 : (x (-4) 5).toNat = 0 := by
                      have r23113 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                      have e23114 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                      have e23115 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                      have e23116 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                      have e23117 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                      have e23118 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                      have e23119 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                      have b23120 := hb (x (-6) 7)
                      have b23121 := hb (x (-5) 6)
                      have b23122 := hb (x (-4) 5)
                      have b23123 := hb (x (-3) 4)
                      have b23124 := hb (x (-2) 11)
                      have b23125 := hb (x (-1) 10)
                      have b23126 := hb (x 0 9)
                      have b23127 := hb (x 1 8)
                      clear * - r23113 e23114 e23115 e23116 e23117 e23118 e23119 b23120 b23121 b23122 b23123 b23124 b23125 b23126 b23127 f23075 f21725 d23076 d21805 d23092
                      omega
                    have d23128 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
                      have r23129 := hand1 (x (-4) 5) (x (-4) 14)
                      have b23130 := hb (x (-4) 5)
                      have b23131 := hb (x (-4) 5 && x (-4) 14)
                      clear * - r23129 b23130 b23131 d23112
                      omega
                    have d23132 : (x (-5) 6).toNat = 1 := by
                      have r23133 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
                      have b23134 := hb (x (-5) 6)
                      have b23135 := hb (x 1 9)
                      have b23136 := hb (x 0 1 && x 0 10)
                      have b23137 := hb (x (-1) 2 && x (-1) 11)
                      have b23138 := hb (x (-2) 3 && x (-2) 12)
                      have b23139 := hb (x (-3) 4 && x (-3) 13)
                      have b23140 := hb (x (-4) 5 && x (-4) 14)
                      clear * - r23133 b23134 b23135 b23136 b23137 b23138 b23139 b23140 d21736 g38 g39 d21789 d23108 d23128
                      omega
                    have r23141 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                    have e23142 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e23143 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e23144 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e23145 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e23146 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e23147 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b23148 := hb (x (-6) 7)
                    have b23149 := hb (x (-5) 6)
                    have b23150 := hb (x (-4) 5)
                    have b23151 := hb (x (-3) 4)
                    have b23152 := hb (x (-2) 11)
                    have b23153 := hb (x (-1) 10)
                    have b23154 := hb (x 0 9)
                    have b23155 := hb (x 1 8)
                    linarith only [r23141, e23142, e23143, e23144, e23145, e23146, e23147, b23148, b23149, b23150, b23151, b23152, b23153, b23154, b23155, f23075, f21725, d23076, d21805, d23092, d23112, d23132]
                · have f23156 : (x (-1) 8).toNat = 1 := by rw [h22012]; rfl
                  have d23157 : (x (-3) 10).toNat = 0 := by
                    have r23158 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                    have e23159 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                    have e23160 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                    have e23161 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                    have e23162 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                    have e23163 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                    have e23164 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                    have b23165 := hb (x (-8) 7)
                    have b23166 := hb (x (-7) 6)
                    have b23167 := hb (x (-6) 5)
                    have b23168 := hb (x (-5) 4)
                    have b23169 := hb (x (-4) 11)
                    have b23170 := hb (x (-3) 10)
                    have b23171 := hb (x (-2) 9)
                    have b23172 := hb (x (-1) 8)
                    clear * - r23158 e23159 e23160 e23161 e23162 e23163 e23164 b23165 b23166 b23167 b23168 b23169 b23170 b23171 b23172 f23156 d21692
                    omega
                  have d23173 : (x (-4) 11).toNat = 0 := by
                    have r23174 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                    have e23175 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                    have e23176 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                    have e23177 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                    have e23178 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                    have e23179 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                    have e23180 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                    have b23181 := hb (x (-8) 7)
                    have b23182 := hb (x (-7) 6)
                    have b23183 := hb (x (-6) 5)
                    have b23184 := hb (x (-5) 4)
                    have b23185 := hb (x (-4) 11)
                    have b23186 := hb (x (-3) 10)
                    have b23187 := hb (x (-2) 9)
                    have b23188 := hb (x (-1) 8)
                    clear * - r23174 e23175 e23176 e23177 e23178 e23179 e23180 b23181 b23182 b23183 b23184 b23185 b23186 b23187 b23188 f23156 d21692 d23157
                    omega
                  have d23189 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
                    have r23190 := hand2 (x (-4) 1) (x (-4) 11)
                    have b23191 := hb (x (-4) 11)
                    have b23192 := hb (x (-4) 1 && x (-4) 11)
                    clear * - r23190 b23191 b23192 d23173
                    omega
                  have d23193 : (x (-5) 4).toNat = 0 := by
                    have r23194 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                    have e23195 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                    have e23196 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                    have e23197 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                    have e23198 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                    have e23199 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                    have e23200 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                    have b23201 := hb (x (-8) 7)
                    have b23202 := hb (x (-7) 6)
                    have b23203 := hb (x (-6) 5)
                    have b23204 := hb (x (-5) 4)
                    have b23205 := hb (x (-4) 11)
                    have b23206 := hb (x (-3) 10)
                    have b23207 := hb (x (-2) 9)
                    have b23208 := hb (x (-1) 8)
                    clear * - r23194 e23195 e23196 e23197 e23198 e23199 e23200 b23201 b23202 b23203 b23204 b23205 b23206 b23207 b23208 f23156 d21692 d23157 d23173
                    omega
                  have d23209 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                    have r23210 := hand1 (x (-5) 4) (x (-5) 14)
                    have b23211 := hb (x (-5) 4)
                    have b23212 := hb (x (-5) 4 && x (-5) 14)
                    clear * - r23210 b23211 b23212 d23193
                    omega
                  have d23213 : (x (-6) 5).toNat = 0 := by
                    have r23214 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
                    have e23215 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                    have e23216 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                    have e23217 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                    have e23218 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                    have e23219 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                    have e23220 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                    have b23221 := hb (x (-8) 7)
                    have b23222 := hb (x (-7) 6)
                    have b23223 := hb (x (-6) 5)
                    have b23224 := hb (x (-5) 4)
                    have b23225 := hb (x (-4) 11)
                    have b23226 := hb (x (-3) 10)
                    have b23227 := hb (x (-2) 9)
                    have b23228 := hb (x (-1) 8)
                    clear * - r23214 e23215 e23216 e23217 e23218 e23219 e23220 b23221 b23222 b23223 b23224 b23225 b23226 b23227 b23228 f23156 d21692 d23157 d23173 d23193
                    omega
                  have r23229 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
                  have r23230 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := hd8 (-3)
                  have e23231 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                  have e23232 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                  have e23233 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                  have e23234 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                  have e23235 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                  have e23236 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                  have r23237 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                  have e23238 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                  have e23239 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                  have e23240 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                  have e23241 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                  have e23242 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                  have e23243 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                  have r23244 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
                  have e23245 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                  have e23246 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                  have r23247 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := hcov4 1
                  have e23248 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
                  have e23249 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
                  have r23250 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
                  have r23251 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := hcov10 (-3)
                  have r23252 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := hcov10 (-1)
                  have r23253 := hand2 (x (-3) 4) (x (-3) 8)
                  have r23254 := hand2 (x (-4) 5) (x (-4) 9)
                  have r23255 := hand2 (x (-5) 6) (x (-5) 10)
                  have r23256 := hand2 (x (-6) 7) (x (-6) 11)
                  have r23257 := hand1 (x (-7) 8) (x (-7) 12)
                  have r23258 := hand1 (x (-8) 9) (x (-8) 13)
                  have r23259 := hand1 (x (-3) 4) (x (-3) 13)
                  have r23260 := hand1 (x (-4) 5) (x (-4) 14)
                  have r23261 := hand1 (x (-5) 2) (x (-5) 12)
                  have r23262 := hand1 (x (-6) 3) (x (-6) 13)
                  have r23263 := hand1 (x (-7) 4) (x (-7) 14)
                  have r23264 := hand2 (x (-3) 2) (x (-3) 12)
                  have r23265 := hand2 (x (-4) 3) (x (-4) 13)
                  have b23266 := hb (x (-13) 14)
                  have b23267 := hb (x (-12) 13)
                  have b23268 := hb (x (-11) 12)
                  have b23269 := hb (x (-10) 7)
                  have b23270 := hb (x (-10) 11)
                  have b23271 := hb (x (-9) 6)
                  have b23272 := hb (x (-9) 10)
                  have b23273 := hb (x (-8) 5)
                  have b23274 := hb (x (-8) 9)
                  have b23275 := hb (x (-7) 4)
                  have b23276 := hb (x (-7) 8)
                  have b23277 := hb (x (-6) 3)
                  have b23278 := hb (x (-6) 5)
                  have b23279 := hb (x (-6) 7)
                  have b23280 := hb (x (-6) 11)
                  have b23281 := hb (x (-5) 2)
                  have b23282 := hb (x (-5) 6)
                  have b23283 := hb (x (-5) 10)
                  have b23284 := hb (x (-4) 5)
                  have b23285 := hb (x (-4) 9)
                  have b23286 := hb (x (-4) 13)
                  have b23287 := hb (x (-3) 4)
                  have b23288 := hb (x (-3) 8)
                  have b23289 := hb (x (-3) 10)
                  have b23290 := hb (x (-3) 12)
                  have b23291 := hb (x (-2) 3)
                  have b23292 := hb (x (-2) 11)
                  have b23293 := hb (x (-1) 2)
                  have b23294 := hb (x (-1) 10)
                  have b23295 := hb (x 0 1)
                  have b23296 := hb (x 0 5)
                  have b23297 := hb (x 0 9)
                  have b23298 := hb (x 1 4)
                  have b23299 := hb (x 1 8)
                  have b23300 := hb (x 1 9)
                  have b23301 := hb (x (-1) 2 && x (-1) 6)
                  have b23302 := hb (x (-2) 3 && x (-2) 7)
                  have b23303 := hb (x (-3) 4 && x (-3) 8)
                  have b23304 := hb (x (-4) 5 && x (-4) 9)
                  have b23305 := hb (x (-5) 6 && x (-5) 10)
                  have b23306 := hb (x (-6) 7 && x (-6) 11)
                  have b23307 := hb (x (-7) 8 && x (-7) 12)
                  have b23308 := hb (x (-8) 9 && x (-8) 13)
                  have b23309 := hb (x 0 1 && x 0 10)
                  have b23310 := hb (x (-1) 2 && x (-1) 11)
                  have b23311 := hb (x (-2) 3 && x (-2) 12)
                  have b23312 := hb (x (-3) 4 && x (-3) 13)
                  have b23313 := hb (x (-4) 5 && x (-4) 14)
                  have b23314 := hb (x (-4) 1 && x (-4) 11)
                  have b23315 := hb (x (-5) 2 && x (-5) 12)
                  have b23316 := hb (x (-6) 3 && x (-6) 13)
                  have b23317 := hb (x (-7) 4 && x (-7) 14)
                  have b23318 := hb (x (-2) 1 && x (-2) 11)
                  have b23319 := hb (x (-3) 2 && x (-3) 12)
                  have b23320 := hb (x (-4) 3 && x (-4) 13)
                  have b23321 := hb (x (-5) 4 && x (-5) 14)
                  linarith only [r23229, r23230, e23231, e23232, e23233, e23234, e23235, e23236, r23237, e23238, e23239, e23240, e23241, e23242, e23243, r23244, e23245, e23246, r23247, e23248, e23249, r23250, r23251, r23252, r23253, r23254, r23255, r23256, r23257, r23258, r23259, r23260, r23261, r23262, r23263, r23264, r23265, b23266, b23267, b23268, b23269, b23270, b23271, b23272, b23273, b23274, b23275, b23276, b23277, b23278, b23279, b23280, b23281, b23282, b23283, b23284, b23285, b23286, b23287, b23288, b23289, b23290, b23291, b23292, b23293, b23294, b23295, b23296, b23297, b23298, b23299, b23300, b23301, b23302, b23303, b23304, b23305, b23306, b23307, b23308, b23309, b23310, b23311, b23312, b23313, b23314, b23315, b23316, b23317, b23318, b23319, b23320, b23321, d23213, d23157, d21781, d21805, d21748, g4, g7, f21725, d21777, d21736, d21998, d21797, g38, g39, d21789, d23189, d21660, d23209]
              · have f23322 : (x 1 7).toNat = 1 := by rw [h22010]; rfl
                have d23323 : (x 8 8).toNat = 0 := by
                  have r23324 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                  have e23325 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e23326 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e23327 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e23328 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e23329 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e23330 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b23331 := hb (x 1 7)
                  have b23332 := hb (x 2 6)
                  have b23333 := hb (x 3 5)
                  have b23334 := hb (x 4 4)
                  have b23335 := hb (x 5 11)
                  have b23336 := hb (x 6 10)
                  have b23337 := hb (x 7 9)
                  have b23338 := hb (x 8 8)
                  clear * - r23324 e23325 e23326 e23327 e23328 e23329 e23330 b23331 b23332 b23333 b23334 b23335 b23336 b23337 b23338 d21918 d21934 f23322
                  omega
                have d23339 : (x 8 1 && x 8 8).toNat = 0 := by
                  have r23340 := hand2 (x 8 1) (x 8 8)
                  have b23341 := hb (x 8 8)
                  have b23342 := hb (x 8 1 && x 8 8)
                  clear * - r23340 b23341 b23342 d23323
                  omega
                have d23343 : (x 7 9).toNat = 0 := by
                  have r23344 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                  have e23345 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e23346 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e23347 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e23348 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e23349 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e23350 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b23351 := hb (x 1 7)
                  have b23352 := hb (x 2 6)
                  have b23353 := hb (x 3 5)
                  have b23354 := hb (x 4 4)
                  have b23355 := hb (x 5 11)
                  have b23356 := hb (x 6 10)
                  have b23357 := hb (x 7 9)
                  have b23358 := hb (x 8 8)
                  clear * - r23344 e23345 e23346 e23347 e23348 e23349 e23350 b23351 b23352 b23353 b23354 b23355 b23356 b23357 b23358 d23323 d21918 d21934 f23322
                  omega
                have d23359 : (x 7 2 && x 7 9).toNat = 0 := by
                  have r23360 := hand2 (x 7 2) (x 7 9)
                  have b23361 := hb (x 7 9)
                  have b23362 := hb (x 7 2 && x 7 9)
                  clear * - r23360 b23361 b23362 d23343
                  omega
                have d23363 : (x 6 10).toNat = 0 := by
                  have r23364 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                  have e23365 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e23366 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e23367 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e23368 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e23369 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e23370 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b23371 := hb (x 1 7)
                  have b23372 := hb (x 2 6)
                  have b23373 := hb (x 3 5)
                  have b23374 := hb (x 4 4)
                  have b23375 := hb (x 5 11)
                  have b23376 := hb (x 6 10)
                  have b23377 := hb (x 7 9)
                  have b23378 := hb (x 8 8)
                  clear * - r23364 e23365 e23366 e23367 e23368 e23369 e23370 b23371 b23372 b23373 b23374 b23375 b23376 b23377 b23378 d23323 d23343 d21918 d21934 f23322
                  omega
                have d23379 : (x 6 3 && x 6 10).toNat = 0 := by
                  have r23380 := hand2 (x 6 3) (x 6 10)
                  have b23381 := hb (x 6 10)
                  have b23382 := hb (x 6 3 && x 6 10)
                  clear * - r23380 b23381 b23382 d23363
                  omega
                have d23383 : (x 5 11).toNat = 0 := by
                  have r23384 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                  have e23385 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e23386 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e23387 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e23388 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e23389 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e23390 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b23391 := hb (x 1 7)
                  have b23392 := hb (x 2 6)
                  have b23393 := hb (x 3 5)
                  have b23394 := hb (x 4 4)
                  have b23395 := hb (x 5 11)
                  have b23396 := hb (x 6 10)
                  have b23397 := hb (x 7 9)
                  have b23398 := hb (x 8 8)
                  clear * - r23384 e23385 e23386 e23387 e23388 e23389 e23390 b23391 b23392 b23393 b23394 b23395 b23396 b23397 b23398 d23323 d23343 d23363 d21918 d21934 f23322
                  omega
                have d23399 : (x 2 6).toNat = 0 := by
                  have r23400 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
                  have e23401 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e23402 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e23403 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e23404 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e23405 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e23406 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have b23407 := hb (x 1 7)
                  have b23408 := hb (x 2 6)
                  have b23409 := hb (x 3 5)
                  have b23410 := hb (x 4 4)
                  have b23411 := hb (x 5 11)
                  have b23412 := hb (x 6 10)
                  have b23413 := hb (x 7 9)
                  have b23414 := hb (x 8 8)
                  clear * - r23400 e23401 e23402 e23403 e23404 e23405 e23406 b23407 b23408 b23409 b23410 b23411 b23412 b23413 b23414 d23323 d23343 d23363 d23383 d21918 d21934 f23322
                  omega
                have d23415 : (x 2 6 && x 2 11).toNat = 0 := by
                  have r23416 := hand1 (x 2 6) (x 2 11)
                  have b23417 := hb (x 2 6)
                  have b23418 := hb (x 2 6 && x 2 11)
                  clear * - r23416 b23417 b23418 d23399
                  omega
                have r23419 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := hcount 13
                have r23420 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
                have e23421 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                have e23422 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                have e23423 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                have e23424 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                have e23425 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                have e23426 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                have r23427 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
                have e23428 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e23429 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e23430 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e23431 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e23432 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e23433 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have r23434 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
                have e23435 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23436 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23437 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23438 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23439 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23440 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have r23441 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := hd8 16
                have e23442 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e23443 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e23444 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e23445 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e23446 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e23447 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have r23448 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := hcov5 8
                have r23449 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := hcov7 9
                have r23450 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
                have r23451 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := hcov9 8
                have r23452 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
                have r23453 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := hcov11 13
                have r23454 := hand2 (x 7 1) (x 7 6)
                have r23455 := hand2 (x 6 2) (x 6 7)
                have r23456 := hand1 (x (-1) 9) (x (-1) 14)
                have r23457 := hand1 (x 2 7) (x 2 14)
                have r23458 := hand1 (x (-3) 4) (x (-3) 13)
                have r23459 := hand1 (x (-4) 5) (x (-4) 14)
                have r23460 := hand2 (x 7 1) (x 7 10)
                have r23461 := hand2 (x 6 2) (x 6 11)
                have r23462 := hand1 (x (-4) 4) (x (-4) 14)
                have r23463 := hand1 (x 12 1) (x 12 12)
                have r23464 := hand1 (x 11 2) (x 11 13)
                have r23465 := hand1 (x 10 3) (x 10 14)
                have b23466 := hb (x (-7) 7)
                have b23467 := hb (x (-6) 6)
                have b23468 := hb (x (-6) 7)
                have b23469 := hb (x (-5) 5)
                have b23470 := hb (x (-5) 6)
                have b23471 := hb (x (-4) 4)
                have b23472 := hb (x (-4) 5)
                have b23473 := hb (x (-3) 4)
                have b23474 := hb (x (-3) 11)
                have b23475 := hb (x (-2) 10)
                have b23476 := hb (x (-2) 11)
                have b23477 := hb (x (-1) 9)
                have b23478 := hb (x (-1) 10)
                have b23479 := hb (x (-1) 14)
                have b23480 := hb (x 0 8)
                have b23481 := hb (x 0 9)
                have b23482 := hb (x 0 10)
                have b23483 := hb (x 0 13)
                have b23484 := hb (x 1 8)
                have b23485 := hb (x 1 9)
                have b23486 := hb (x 1 12)
                have b23487 := hb (x 2 6)
                have b23488 := hb (x 2 7)
                have b23489 := hb (x 2 11)
                have b23490 := hb (x 3 6)
                have b23491 := hb (x 3 10)
                have b23492 := hb (x 4 5)
                have b23493 := hb (x 4 9)
                have b23494 := hb (x 5 4)
                have b23495 := hb (x 5 8)
                have b23496 := hb (x 6 7)
                have b23497 := hb (x 6 11)
                have b23498 := hb (x 7 6)
                have b23499 := hb (x 7 10)
                have b23500 := hb (x 8 5)
                have b23501 := hb (x 8 9)
                have b23502 := hb (x 9 4)
                have b23503 := hb (x 9 7)
                have b23504 := hb (x 9 8)
                have b23505 := hb (x 10 3)
                have b23506 := hb (x 10 6)
                have b23507 := hb (x 11 2)
                have b23508 := hb (x 11 5)
                have b23509 := hb (x 12 1)
                have b23510 := hb (x 12 4)
                have b23511 := hb (x 13 11)
                have b23512 := hb (x 14 10)
                have b23513 := hb (x 15 9)
                have b23514 := hb (x 16 8)
                have b23515 := hb (x 7 1 && x 7 6)
                have b23516 := hb (x 6 2 && x 6 7)
                have b23517 := hb (x 5 3 && x 5 8)
                have b23518 := hb (x 4 4 && x 4 9)
                have b23519 := hb (x 3 5 && x 3 10)
                have b23520 := hb (x 2 6 && x 2 11)
                have b23521 := hb (x 1 7 && x 1 12)
                have b23522 := hb (x 0 8 && x 0 13)
                have b23523 := hb (x (-1) 9 && x (-1) 14)
                have b23524 := hb (x 8 1 && x 8 8)
                have b23525 := hb (x 7 2 && x 7 9)
                have b23526 := hb (x 6 3 && x 6 10)
                have b23527 := hb (x 5 4 && x 5 11)
                have b23528 := hb (x 4 5 && x 4 12)
                have b23529 := hb (x 3 6 && x 3 13)
                have b23530 := hb (x 2 7 && x 2 14)
                have b23531 := hb (x 0 1 && x 0 10)
                have b23532 := hb (x (-1) 2 && x (-1) 11)
                have b23533 := hb (x (-2) 3 && x (-2) 12)
                have b23534 := hb (x (-3) 4 && x (-3) 13)
                have b23535 := hb (x (-4) 5 && x (-4) 14)
                have b23536 := hb (x 7 1 && x 7 10)
                have b23537 := hb (x 6 2 && x 6 11)
                have b23538 := hb (x 5 3 && x 5 12)
                have b23539 := hb (x 4 4 && x 4 13)
                have b23540 := hb (x 3 5 && x 3 14)
                have b23541 := hb (x (-1) 1 && x (-1) 11)
                have b23542 := hb (x (-2) 2 && x (-2) 12)
                have b23543 := hb (x (-3) 3 && x (-3) 13)
                have b23544 := hb (x (-4) 4 && x (-4) 14)
                have b23545 := hb (x 12 1 && x 12 12)
                have b23546 := hb (x 11 2 && x 11 13)
                have b23547 := hb (x 10 3 && x 10 14)
                linarith only [r23419, r23420, e23421, e23422, e23423, e23424, e23425, e23426, r23427, e23428, e23429, e23430, e23431, e23432, e23433, r23434, e23435, e23436, e23437, e23438, e23439, e23440, r23441, e23442, e23443, e23444, e23445, e23446, e23447, r23448, r23449, r23450, r23451, r23452, r23453, r23454, r23455, r23456, r23457, r23458, r23459, r23460, r23461, r23462, r23463, r23464, r23465, b23466, b23467, b23468, b23469, b23470, b23471, b23472, b23473, b23474, b23475, b23476, b23477, b23478, b23479, b23480, b23481, b23482, b23483, b23484, b23485, b23486, b23487, b23488, b23489, b23490, b23491, b23492, b23493, b23494, b23495, b23496, b23497, b23498, b23499, b23500, b23501, b23502, b23503, b23504, b23505, b23506, b23507, b23508, b23509, b23510, b23511, b23512, b23513, b23514, b23515, b23516, b23517, b23518, b23519, b23520, b23521, b23522, b23523, b23524, b23525, b23526, b23527, b23528, b23529, b23530, b23531, b23532, b23533, b23534, b23535, b23536, b23537, b23538, b23539, b23540, b23541, b23542, b23543, b23544, b23545, b23546, b23547, d21720, d21639, d21805, d21648, g9, f21725, g10, g12, d21736, d21761, d23399, d21837, g19, g20, d21893, d21962, d21861, d21938, d21954, d21922, g34, d23415, d21769, g35, d23339, d23359, d23379, d21869, d21897, g37, g38, g39, d21789, d21857, d21889, g45, g46, d21631, d21712]
            · have f23548 : (x (-1) 7).toNat = 1 := by rw [h22004]; rfl
              have d23549 : (x 6 8).toNat = 0 := by
                have r23550 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e23551 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e23552 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e23553 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e23554 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e23555 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e23556 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b23557 := hb (x (-1) 7)
                have b23558 := hb (x 0 6)
                have b23559 := hb (x 1 5)
                have b23560 := hb (x 2 4)
                have b23561 := hb (x 3 11)
                have b23562 := hb (x 4 10)
                have b23563 := hb (x 5 9)
                have b23564 := hb (x 6 8)
                clear * - r23550 e23551 e23552 e23553 e23554 e23555 e23556 b23557 b23558 b23559 b23560 b23561 b23562 b23563 b23564 d21744 g8 f23548
                omega
              have d23565 : (x 5 9).toNat = 0 := by
                have r23566 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e23567 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e23568 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e23569 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e23570 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e23571 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e23572 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b23573 := hb (x (-1) 7)
                have b23574 := hb (x 0 6)
                have b23575 := hb (x 1 5)
                have b23576 := hb (x 2 4)
                have b23577 := hb (x 3 11)
                have b23578 := hb (x 4 10)
                have b23579 := hb (x 5 9)
                have b23580 := hb (x 6 8)
                clear * - r23566 e23567 e23568 e23569 e23570 e23571 e23572 b23573 b23574 b23575 b23576 b23577 b23578 b23579 b23580 d23549 d21744 g8 f23548
                omega
              have d23581 : (x 4 10).toNat = 0 := by
                have r23582 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e23583 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e23584 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e23585 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e23586 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e23587 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e23588 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b23589 := hb (x (-1) 7)
                have b23590 := hb (x 0 6)
                have b23591 := hb (x 1 5)
                have b23592 := hb (x 2 4)
                have b23593 := hb (x 3 11)
                have b23594 := hb (x 4 10)
                have b23595 := hb (x 5 9)
                have b23596 := hb (x 6 8)
                clear * - r23582 e23583 e23584 e23585 e23586 e23587 e23588 b23589 b23590 b23591 b23592 b23593 b23594 b23595 b23596 d23549 d23565 d21744 g8 f23548
                omega
              have d23597 : (x 3 11).toNat = 0 := by
                have r23598 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e23599 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e23600 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e23601 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e23602 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e23603 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e23604 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b23605 := hb (x (-1) 7)
                have b23606 := hb (x 0 6)
                have b23607 := hb (x 1 5)
                have b23608 := hb (x 2 4)
                have b23609 := hb (x 3 11)
                have b23610 := hb (x 4 10)
                have b23611 := hb (x 5 9)
                have b23612 := hb (x 6 8)
                clear * - r23598 e23599 e23600 e23601 e23602 e23603 e23604 b23605 b23606 b23607 b23608 b23609 b23610 b23611 b23612 d23549 d23565 d23581 d21744 g8 f23548
                omega
              have d23613 : (x 2 4).toNat = 0 := by
                have r23614 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
                have e23615 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e23616 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e23617 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e23618 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e23619 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e23620 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b23621 := hb (x (-1) 7)
                have b23622 := hb (x 0 6)
                have b23623 := hb (x 1 5)
                have b23624 := hb (x 2 4)
                have b23625 := hb (x 3 11)
                have b23626 := hb (x 4 10)
                have b23627 := hb (x 5 9)
                have b23628 := hb (x 6 8)
                clear * - r23614 e23615 e23616 e23617 e23618 e23619 e23620 b23621 b23622 b23623 b23624 b23625 b23626 b23627 b23628 d23549 d23565 d23581 d23597 d21744 g8 f23548
                omega
              have d23629 : (x 6 11).toNat = 1 := by
                have r23630 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := hcov11 6
                have b23631 := hb (x 2 4)
                have b23632 := hb (x 6 11)
                have b23633 := hb (x 5 1 && x 5 12)
                have b23634 := hb (x 4 2 && x 4 13)
                have b23635 := hb (x 3 3 && x 3 14)
                clear * - r23630 b23631 b23632 b23633 b23634 b23635 d21853 d21885 g57 d23613
                omega
              have d23636 : (x 6 3).toNat = 1 := by
                have r23637 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                have b23638 := hb (x 6 3)
                have b23639 := hb (x 6 11)
                clear * - r23637 b23638 b23639 d23629
                omega
              have d23640 : (x 9 12).toNat = 0 := by
                have r23641 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                have e23642 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e23643 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b23644 := hb (x 6 3)
                have b23645 := hb (x 7 2)
                have b23646 := hb (x 8 13)
                have b23647 := hb (x 9 12)
                clear * - r23641 e23642 e23643 b23644 b23645 b23646 b23647 d23636
                omega
              have d23648 : (x 9 4).toNat = 0 := by
                have r23649 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have b23650 := hb (x 9 4)
                have b23651 := hb (x 9 12)
                clear * - r23649 b23650 b23651 d23640
                omega
              have d23652 : (x 9 4 && x 9 13).toNat = 0 := by
                have r23653 := hand1 (x 9 4) (x 9 13)
                have b23654 := hb (x 9 4)
                have b23655 := hb (x 9 4 && x 9 13)
                clear * - r23653 b23654 b23655 d23648
                omega
              have d23656 : (x 8 13).toNat = 0 := by
                have r23657 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                have e23658 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e23659 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b23660 := hb (x 6 3)
                have b23661 := hb (x 7 2)
                have b23662 := hb (x 8 13)
                have b23663 := hb (x 9 12)
                clear * - r23657 e23658 e23659 b23660 b23661 b23662 b23663 d23640 d23636
                omega
              have d23664 : (x 8 5).toNat = 0 := by
                have r23665 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                have b23666 := hb (x 8 5)
                have b23667 := hb (x 8 13)
                clear * - r23665 b23666 b23667 d23656
                omega
              have d23668 : (x 8 5 && x 8 14).toNat = 0 := by
                have r23669 := hand1 (x 8 5) (x 8 14)
                have b23670 := hb (x 8 5)
                have b23671 := hb (x 8 5 && x 8 14)
                clear * - r23669 b23670 b23671 d23664
                omega
              have d23672 : (x 7 2).toNat = 0 := by
                have r23673 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
                have e23674 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e23675 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b23676 := hb (x 6 3)
                have b23677 := hb (x 7 2)
                have b23678 := hb (x 8 13)
                have b23679 := hb (x 9 12)
                clear * - r23673 e23674 e23675 b23676 b23677 b23678 b23679 d23640 d23656 d23636
                omega
              have d23680 : (x 7 2 && x 7 6).toNat = 0 := by
                have r23681 := hand1 (x 7 2) (x 7 6)
                have b23682 := hb (x 7 2)
                have b23683 := hb (x 7 2 && x 7 6)
                clear * - r23681 b23682 b23683 d23672
                omega
              have d23684 : (x 7 10).toNat = 0 := by
                have r23685 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
                have b23686 := hb (x 7 2)
                have b23687 := hb (x 7 10)
                clear * - r23685 b23686 b23687 d23672
                omega
              have d23688 : (x 9 8).toNat = 0 := by
                have r23689 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
                have e23690 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23691 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23692 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23693 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23694 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23695 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b23696 := hb (x 2 7)
                have b23697 := hb (x 3 6)
                have b23698 := hb (x 4 5)
                have b23699 := hb (x 5 4)
                have b23700 := hb (x 6 11)
                have b23701 := hb (x 7 10)
                have b23702 := hb (x 8 9)
                have b23703 := hb (x 9 8)
                clear * - r23689 e23690 e23691 e23692 e23693 e23694 e23695 b23696 b23697 b23698 b23699 b23700 b23701 b23702 b23703 d23684 d23629 d21861 d21893 g19
                omega
              have d23704 : (x 8 9).toNat = 0 := by
                have r23705 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
                have e23706 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23707 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23708 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23709 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23710 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23711 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b23712 := hb (x 2 7)
                have b23713 := hb (x 3 6)
                have b23714 := hb (x 4 5)
                have b23715 := hb (x 5 4)
                have b23716 := hb (x 6 11)
                have b23717 := hb (x 7 10)
                have b23718 := hb (x 8 9)
                have b23719 := hb (x 9 8)
                clear * - r23705 e23706 e23707 e23708 e23709 e23710 e23711 b23712 b23713 b23714 b23715 b23716 b23717 b23718 b23719 d23688 d23684 d23629 d21861 d21893 g19
                omega
              have d23720 : (x 2 7).toNat = 0 := by
                have r23721 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
                have e23722 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e23723 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e23724 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e23725 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e23726 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e23727 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b23728 := hb (x 2 7)
                have b23729 := hb (x 3 6)
                have b23730 := hb (x 4 5)
                have b23731 := hb (x 5 4)
                have b23732 := hb (x 6 11)
                have b23733 := hb (x 7 10)
                have b23734 := hb (x 8 9)
                have b23735 := hb (x 9 8)
                clear * - r23721 e23722 e23723 e23724 e23725 e23726 e23727 b23728 b23729 b23730 b23731 b23732 b23733 b23734 b23735 d23688 d23704 d23684 d23629 d21861 d21893 g19
                omega
              have d23736 : (x 2 7 && x 2 11).toNat = 0 := by
                have r23737 := hand1 (x 2 7) (x 2 11)
                have b23738 := hb (x 2 7)
                have b23739 := hb (x 2 7 && x 2 11)
                clear * - r23737 b23738 b23739 d23720
                omega
              have r23740 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := hcount 13
              have r23741 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
              have r23742 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
              have e23743 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e23744 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e23745 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e23746 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e23747 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e23748 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have r23749 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
              have e23750 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e23751 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e23752 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e23753 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e23754 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e23755 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have r23756 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
              have e23757 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e23758 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have r23759 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := hcov4 9
              have e23760 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
              have e23761 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
              have r23762 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
              have r23763 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := hcov9 13
              have r23764 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
              have r23765 := hand2 (x 6 3) (x 6 7)
              have r23766 := hand1 (x (-3) 4) (x (-3) 13)
              have r23767 := hand1 (x (-4) 5) (x (-4) 14)
              have r23768 := hand2 (x 12 1) (x 12 10)
              have r23769 := hand2 (x 11 2) (x 11 11)
              have r23770 := hand1 (x 10 3) (x 10 12)
              have r23771 := hand1 (x 12 1) (x 12 14)
              have b23772 := hb (x (-6) 7)
              have b23773 := hb (x (-5) 6)
              have b23774 := hb (x (-4) 5)
              have b23775 := hb (x (-3) 4)
              have b23776 := hb (x (-2) 11)
              have b23777 := hb (x (-1) 10)
              have b23778 := hb (x (-1) 14)
              have b23779 := hb (x 0 9)
              have b23780 := hb (x 0 13)
              have b23781 := hb (x 0 14)
              have b23782 := hb (x 1 8)
              have b23783 := hb (x 1 9)
              have b23784 := hb (x 1 12)
              have b23785 := hb (x 1 13)
              have b23786 := hb (x 2 11)
              have b23787 := hb (x 2 12)
              have b23788 := hb (x 3 10)
              have b23789 := hb (x 3 11)
              have b23790 := hb (x 4 9)
              have b23791 := hb (x 4 10)
              have b23792 := hb (x 5 8)
              have b23793 := hb (x 5 9)
              have b23794 := hb (x 6 7)
              have b23795 := hb (x 6 8)
              have b23796 := hb (x 7 6)
              have b23797 := hb (x 7 7)
              have b23798 := hb (x 8 5)
              have b23799 := hb (x 8 6)
              have b23800 := hb (x 9 4)
              have b23801 := hb (x 9 5)
              have b23802 := hb (x 10 3)
              have b23803 := hb (x 10 4)
              have b23804 := hb (x 11 2)
              have b23805 := hb (x 11 3)
              have b23806 := hb (x 11 11)
              have b23807 := hb (x 12 1)
              have b23808 := hb (x 12 2)
              have b23809 := hb (x 12 10)
              have b23810 := hb (x 13 1)
              have b23811 := hb (x 13 9)
              have b23812 := hb (x 13 13)
              have b23813 := hb (x 14 8)
              have b23814 := hb (x 14 12)
              have b23815 := hb (x 7 2 && x 7 6)
              have b23816 := hb (x 6 3 && x 6 7)
              have b23817 := hb (x 5 4 && x 5 8)
              have b23818 := hb (x 4 5 && x 4 9)
              have b23819 := hb (x 3 6 && x 3 10)
              have b23820 := hb (x 2 7 && x 2 11)
              have b23821 := hb (x 1 8 && x 1 12)
              have b23822 := hb (x 0 9 && x 0 13)
              have b23823 := hb (x 0 1 && x 0 10)
              have b23824 := hb (x (-1) 2 && x (-1) 11)
              have b23825 := hb (x (-2) 3 && x (-2) 12)
              have b23826 := hb (x (-3) 4 && x (-3) 13)
              have b23827 := hb (x (-4) 5 && x (-4) 14)
              have b23828 := hb (x 12 1 && x 12 10)
              have b23829 := hb (x 11 2 && x 11 11)
              have b23830 := hb (x 10 3 && x 10 12)
              have b23831 := hb (x 9 4 && x 9 13)
              have b23832 := hb (x 8 5 && x 8 14)
              have b23833 := hb (x 12 1 && x 12 14)
              linarith only [r23740, r23741, r23742, e23743, e23744, e23745, e23746, e23747, e23748, r23749, e23750, e23751, e23752, e23753, e23754, e23755, r23756, e23757, e23758, r23759, e23760, e23761, r23762, r23763, r23764, r23765, r23766, r23767, r23768, r23769, r23770, r23771, b23772, b23773, b23774, b23775, b23776, b23777, b23778, b23779, b23780, b23781, b23782, b23783, b23784, b23785, b23786, b23787, b23788, b23789, b23790, b23791, b23792, b23793, b23794, b23795, b23796, b23797, b23798, b23799, b23800, b23801, b23802, b23803, b23804, b23805, b23806, b23807, b23808, b23809, b23810, b23811, b23812, b23813, b23814, b23815, b23816, b23817, b23818, b23819, b23820, b23821, b23822, b23823, b23824, b23825, b23826, b23827, b23828, b23829, b23830, b23831, b23832, b23833, d21805, d21648, f21725, g12, g13, d21736, d21761, d21732, d21837, d21753, g20, d23597, d21962, d23581, d21938, d23565, d23549, d23664, d23648, d23680, d21873, d21901, g31, d23736, d21773, g32, g38, g39, d21789, d23652, d23668]
          · have f23834 : (x (-1) 5).toNat = 1 := by rw [h22002]; rfl
            have d23835 : (x 4 8).toNat = 0 := by
              have r23836 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
              have e23837 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
              have e23838 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
              have e23839 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
              have e23840 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
              have e23841 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
              have e23842 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
              have b23843 := hb (x (-3) 7)
              have b23844 := hb (x (-2) 6)
              have b23845 := hb (x (-1) 5)
              have b23846 := hb (x 0 4)
              have b23847 := hb (x 1 11)
              have b23848 := hb (x 2 10)
              have b23849 := hb (x 3 9)
              have b23850 := hb (x 4 8)
              clear * - r23836 e23837 e23838 e23839 e23840 e23841 e23842 b23843 b23844 b23845 b23846 b23847 b23848 b23849 b23850 d21811 g6 f23834
              omega
            have d23851 : (x 3 9).toNat = 0 := by
              have r23852 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
              have e23853 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
              have e23854 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
              have e23855 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
              have e23856 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
              have e23857 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
              have e23858 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
              have b23859 := hb (x (-3) 7)
              have b23860 := hb (x (-2) 6)
              have b23861 := hb (x (-1) 5)
              have b23862 := hb (x 0 4)
              have b23863 := hb (x 1 11)
              have b23864 := hb (x 2 10)
              have b23865 := hb (x 3 9)
              have b23866 := hb (x 4 8)
              clear * - r23852 e23853 e23854 e23855 e23856 e23857 e23858 b23859 b23860 b23861 b23862 b23863 b23864 b23865 b23866 d23835 d21811 g6 f23834
              omega
            have d23867 : (x 2 10).toNat = 0 := by
              have r23868 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
              have e23869 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
              have e23870 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
              have e23871 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
              have e23872 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
              have e23873 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
              have e23874 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
              have b23875 := hb (x (-3) 7)
              have b23876 := hb (x (-2) 6)
              have b23877 := hb (x (-1) 5)
              have b23878 := hb (x 0 4)
              have b23879 := hb (x 1 11)
              have b23880 := hb (x 2 10)
              have b23881 := hb (x 3 9)
              have b23882 := hb (x 4 8)
              clear * - r23868 e23869 e23870 e23871 e23872 e23873 e23874 b23875 b23876 b23877 b23878 b23879 b23880 b23881 b23882 d23835 d23851 d21811 g6 f23834
              omega
            have d23883 : (x 2 1 && x 2 10).toNat = 0 := by
              have r23884 := hand2 (x 2 1) (x 2 10)
              have b23885 := hb (x 2 10)
              have b23886 := hb (x 2 1 && x 2 10)
              clear * - r23884 b23885 b23886 d23867
              omega
            have d23887 : (x (-3) 6).toNat = 1 := by
              have r23888 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := hcov9 3
              have b23889 := hb (x (-3) 6)
              have b23890 := hb (x 3 9)
              have b23891 := hb (x 2 1 && x 2 10)
              have b23892 := hb (x 1 2 && x 1 11)
              have b23893 := hb (x 0 3 && x 0 12)
              have b23894 := hb (x (-1) 4 && x (-1) 13)
              have b23895 := hb (x (-2) 5 && x (-2) 14)
              clear * - r23888 b23889 b23890 b23891 b23892 b23893 b23894 b23895 d23851 d23883 g43 g44 d21821 d21684
              omega
            have d23896 : (x (-3) 14).toNat = 1 := by
              have r23897 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
              have b23898 := hb (x (-3) 6)
              have b23899 := hb (x (-3) 14)
              clear * - r23897 b23898 b23899 d23887
              omega
            have d23900 : (x (-4) 1).toNat = 0 := by
              have r23901 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
              have b23902 := hb (x (-4) 1)
              have b23903 := hb (x (-3) 14)
              clear * - r23901 b23902 b23903 d23896
              omega
            have d23904 : (x (-4) 13).toNat = 0 := by
              have r23905 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
              have b23906 := hb (x (-4) 1)
              have b23907 := hb (x (-4) 13)
              clear * - r23905 b23906 b23907 d23900
              omega
            have d23908 : (x (-4) 5).toNat = 0 := by
              have r23909 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
              have b23910 := hb (x (-4) 5)
              have b23911 := hb (x (-4) 13)
              clear * - r23909 b23910 b23911 d23904
              omega
            have d23912 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
              have r23913 := hand1 (x (-4) 5) (x (-4) 14)
              have b23914 := hb (x (-4) 5)
              have b23915 := hb (x (-4) 5 && x (-4) 14)
              clear * - r23913 b23914 b23915 d23908
              omega
            have r23916 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := hcount 0
            have r23917 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
            have r23918 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
            have e23919 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e23920 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e23921 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e23922 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e23923 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e23924 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have r23925 : 1 ≤ (x 0 2).toNat + (x (-1) 1 && x (-1) 3).toNat + (x (-2) 2 && x (-2) 4).toNat + (x (-3) 3 && x (-3) 5).toNat + (x (-4) 4 && x (-4) 6).toNat + (x (-5) 5 && x (-5) 7).toNat + (x (-6) 6 && x (-6) 8).toNat + (x (-7) 7 && x (-7) 9).toNat + (x (-8) 8 && x (-8) 10).toNat + (x (-9) 9 && x (-9) 11).toNat + (x (-10) 10 && x (-10) 12).toNat + (x (-11) 11 && x (-11) 13).toNat + (x (-12) 12 && x (-12) 14).toNat + (x (-13) 13).toNat := hcov2 0
            have r23926 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
            have r23927 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
            have r23928 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := hcov10 2
            have r23929 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := hcov13 (-12)
            have r23930 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
            have r23931 := hand2 (x (-4) 4) (x (-4) 6)
            have r23932 := hand2 (x (-5) 5) (x (-5) 7)
            have r23933 := hand1 (x (-6) 6) (x (-6) 8)
            have r23934 := hand1 (x (-7) 7) (x (-7) 9)
            have r23935 := hand1 (x (-8) 8) (x (-8) 10)
            have r23936 := hand1 (x (-9) 9) (x (-9) 11)
            have r23937 := hand1 (x (-10) 10) (x (-10) 12)
            have r23938 := hand1 (x (-11) 11) (x (-11) 13)
            have r23939 := hand1 (x (-12) 12) (x (-12) 14)
            have r23940 := hand1 (x (-3) 4) (x (-3) 13)
            have r23941 := hand1 (x (-4) 4) (x (-4) 14)
            have r23942 := hand1 (x (-2) 4) (x (-2) 14)
            have r23943 := hand2 (x (-13) 1) (x (-13) 14)
            have b23944 := hb (x (-14) 2)
            have b23945 := hb (x (-14) 14)
            have b23946 := hb (x (-13) 13)
            have b23947 := hb (x (-13) 14)
            have b23948 := hb (x (-12) 12)
            have b23949 := hb (x (-12) 13)
            have b23950 := hb (x (-11) 11)
            have b23951 := hb (x (-11) 12)
            have b23952 := hb (x (-10) 10)
            have b23953 := hb (x (-10) 11)
            have b23954 := hb (x (-9) 9)
            have b23955 := hb (x (-9) 10)
            have b23956 := hb (x (-8) 8)
            have b23957 := hb (x (-8) 9)
            have b23958 := hb (x (-7) 7)
            have b23959 := hb (x (-7) 8)
            have b23960 := hb (x (-6) 6)
            have b23961 := hb (x (-6) 7)
            have b23962 := hb (x (-5) 5)
            have b23963 := hb (x (-5) 6)
            have b23964 := hb (x (-5) 7)
            have b23965 := hb (x (-4) 4)
            have b23966 := hb (x (-4) 5)
            have b23967 := hb (x (-4) 6)
            have b23968 := hb (x (-3) 3)
            have b23969 := hb (x (-3) 4)
            have b23970 := hb (x (-3) 5)
            have b23971 := hb (x (-2) 2)
            have b23972 := hb (x (-2) 3)
            have b23973 := hb (x (-2) 4)
            have b23974 := hb (x (-1) 1)
            have b23975 := hb (x (-1) 2)
            have b23976 := hb (x (-1) 11)
            have b23977 := hb (x 0 1)
            have b23978 := hb (x 0 2)
            have b23979 := hb (x 0 10)
            have b23980 := hb (x 1 9)
            have b23981 := hb (x 2 8)
            have b23982 := hb (x 2 10)
            have b23983 := hb (x (-1) 1 && x (-1) 3)
            have b23984 := hb (x (-2) 2 && x (-2) 4)
            have b23985 := hb (x (-3) 3 && x (-3) 5)
            have b23986 := hb (x (-4) 4 && x (-4) 6)
            have b23987 := hb (x (-5) 5 && x (-5) 7)
            have b23988 := hb (x (-6) 6 && x (-6) 8)
            have b23989 := hb (x (-7) 7 && x (-7) 9)
            have b23990 := hb (x (-8) 8 && x (-8) 10)
            have b23991 := hb (x (-9) 9 && x (-9) 11)
            have b23992 := hb (x (-10) 10 && x (-10) 12)
            have b23993 := hb (x (-11) 11 && x (-11) 13)
            have b23994 := hb (x (-12) 12 && x (-12) 14)
            have b23995 := hb (x 0 1 && x 0 10)
            have b23996 := hb (x (-1) 2 && x (-1) 11)
            have b23997 := hb (x (-2) 3 && x (-2) 12)
            have b23998 := hb (x (-3) 4 && x (-3) 13)
            have b23999 := hb (x (-4) 5 && x (-4) 14)
            have b24000 := hb (x (-1) 1 && x (-1) 11)
            have b24001 := hb (x (-2) 2 && x (-2) 12)
            have b24002 := hb (x (-3) 3 && x (-3) 13)
            have b24003 := hb (x (-4) 4 && x (-4) 14)
            have b24004 := hb (x 1 1 && x 1 11)
            have b24005 := hb (x 0 2 && x 0 12)
            have b24006 := hb (x (-1) 3 && x (-1) 13)
            have b24007 := hb (x (-2) 4 && x (-2) 14)
            have b24008 := hb (x (-13) 1 && x (-13) 14)
            linarith only [r23916, r23917, r23918, e23919, e23920, e23921, e23922, e23923, e23924, r23925, r23926, r23927, r23928, r23929, r23930, r23931, r23932, r23933, r23934, r23935, r23936, r23937, r23938, r23939, r23940, r23941, r23942, r23943, b23944, b23945, b23946, b23947, b23948, b23949, b23950, b23951, b23952, b23953, b23954, b23955, b23956, b23957, b23958, b23959, b23960, b23961, b23962, b23963, b23964, b23965, b23966, b23967, b23968, b23969, b23970, b23971, b23972, b23973, b23974, b23975, b23976, b23977, b23978, b23979, b23980, b23981, b23982, b23983, b23984, b23985, b23986, b23987, b23988, b23989, b23990, b23991, b23992, b23993, b23994, b23995, b23996, b23997, b23998, b23999, b24000, b24001, b24002, b24003, b24004, b24005, b24006, b24007, b24008, d23908, d21700, d21619, d21781, g0, d21748, g2, g4, g5, g10, d21736, d23867, g26, d21635, d21716, g38, g39, d21789, d23912, g46, d21631, d21712, d21728, g48, g49]
        · have f24009 : (x (-1) 4).toNat = 1 := by rw [h21815]; rfl
          have d24010 : (x (-1) 12).toNat = 1 := by
            have r24011 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b24012 := hb (x (-1) 4)
            have b24013 := hb (x (-1) 12)
            clear * - r24011 b24012 b24013 f24009
            omega
          have d24014 : (x (-3) 2).toNat = 0 := by
            have r24015 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
            have e24016 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e24017 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b24018 := hb (x (-4) 3)
            have b24019 := hb (x (-3) 2)
            have b24020 := hb (x (-2) 13)
            have b24021 := hb (x (-1) 12)
            clear * - r24015 e24016 e24017 b24018 b24019 b24020 b24021 d24010 d21664
            omega
          have d24022 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
            have r24023 := hand1 (x (-3) 2) (x (-3) 13)
            have b24024 := hb (x (-3) 2)
            have b24025 := hb (x (-3) 2 && x (-3) 13)
            clear * - r24023 b24024 b24025 d24014
            omega
          have d24026 : (x (-3) 10).toNat = 0 := by
            have r24027 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
            have b24028 := hb (x (-3) 2)
            have b24029 := hb (x (-3) 10)
            clear * - r24027 b24028 b24029 d24014
            omega
          have d24030 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
            have r24031 := hand2 (x (-3) 4) (x (-3) 10)
            have b24032 := hb (x (-3) 10)
            have b24033 := hb (x (-3) 4 && x (-3) 10)
            clear * - r24031 b24032 b24033 d24026
            omega
          have d24034 : (x (-4) 3).toNat = 0 := by
            have r24035 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
            have e24036 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e24037 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b24038 := hb (x (-4) 3)
            have b24039 := hb (x (-3) 2)
            have b24040 := hb (x (-2) 13)
            have b24041 := hb (x (-1) 12)
            clear * - r24035 e24036 e24037 b24038 b24039 b24040 b24041 d24010 d21664 d24014
            omega
          have d24042 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
            have r24043 := hand1 (x (-4) 3) (x (-4) 14)
            have b24044 := hb (x (-4) 3)
            have b24045 := hb (x (-4) 3 && x (-4) 14)
            clear * - r24043 b24044 b24045 d24034
            omega
          have d24046 : (x (-4) 11).toNat = 0 := by
            have r24047 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
            have b24048 := hb (x (-4) 3)
            have b24049 := hb (x (-4) 11)
            clear * - r24047 b24048 b24049 d24034
            omega
          have d24050 : (x (-4) 5 && x (-4) 11).toNat = 0 := by
            have r24051 := hand2 (x (-4) 5) (x (-4) 11)
            have b24052 := hb (x (-4) 11)
            have b24053 := hb (x (-4) 5 && x (-4) 11)
            clear * - r24051 b24052 b24053 d24046
            omega
          have d24054 : (x (-5) 4).toNat = 1 := by
            have r24055 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := hcov11 (-1)
            have b24056 := hb (x (-5) 4)
            have b24057 := hb (x (-1) 11)
            have b24058 := hb (x (-2) 1 && x (-2) 12)
            have b24059 := hb (x (-3) 2 && x (-3) 13)
            have b24060 := hb (x (-4) 3 && x (-4) 14)
            clear * - r24055 b24056 b24057 b24058 b24059 b24060 g2 d21656 d24022 d24042
            omega
          have d24061 : (x (-5) 12).toNat = 1 := by
            have r24062 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
            have b24063 := hb (x (-5) 4)
            have b24064 := hb (x (-5) 12)
            clear * - r24062 b24063 b24064 d24054
            omega
          have d24065 : (x (-6) 13).toNat = 0 := by
            have r24066 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
            have e24067 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e24068 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b24069 := hb (x (-8) 3)
            have b24070 := hb (x (-7) 2)
            have b24071 := hb (x (-6) 13)
            have b24072 := hb (x (-5) 12)
            clear * - r24066 e24067 e24068 b24069 b24070 b24071 b24072 d24061
            omega
          have d24073 : (x (-6) 7 && x (-6) 13).toNat = 0 := by
            have r24074 := hand2 (x (-6) 7) (x (-6) 13)
            have b24075 := hb (x (-6) 13)
            have b24076 := hb (x (-6) 7 && x (-6) 13)
            clear * - r24074 b24075 b24076 d24065
            omega
          have d24077 : (x (-6) 5).toNat = 0 := by
            have r24078 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
            have b24079 := hb (x (-6) 5)
            have b24080 := hb (x (-6) 13)
            clear * - r24078 b24079 b24080 d24065
            omega
          have d24081 : (x 3 8).toNat = 0 := by
            have r24082 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
            have e24083 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e24084 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e24085 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e24086 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e24087 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e24088 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b24089 := hb (x (-4) 7)
            have b24090 := hb (x (-3) 6)
            have b24091 := hb (x (-2) 5)
            have b24092 := hb (x (-1) 4)
            have b24093 := hb (x 0 11)
            have b24094 := hb (x 1 10)
            have b24095 := hb (x 2 9)
            have b24096 := hb (x 3 8)
            clear * - r24082 e24083 e24084 e24085 e24086 e24087 e24088 b24089 b24090 b24091 b24092 b24093 b24094 b24095 b24096 g16 g11 f24009 d21680
            omega
          have d24097 : (x 2 9).toNat = 0 := by
            have r24098 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
            have e24099 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e24100 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e24101 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e24102 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e24103 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e24104 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b24105 := hb (x (-4) 7)
            have b24106 := hb (x (-3) 6)
            have b24107 := hb (x (-2) 5)
            have b24108 := hb (x (-1) 4)
            have b24109 := hb (x 0 11)
            have b24110 := hb (x 1 10)
            have b24111 := hb (x 2 9)
            have b24112 := hb (x 3 8)
            clear * - r24098 e24099 e24100 e24101 e24102 e24103 e24104 b24105 b24106 b24107 b24108 b24109 b24110 b24111 b24112 d24081 g16 g11 f24009 d21680
            omega
          have d24113 : (x (-1) 8).toNat = 0 := by
            have r24114 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
            have e24115 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e24116 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e24117 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e24118 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e24119 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e24120 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b24121 := hb (x (-8) 7)
            have b24122 := hb (x (-7) 6)
            have b24123 := hb (x (-6) 5)
            have b24124 := hb (x (-5) 4)
            have b24125 := hb (x (-4) 11)
            have b24126 := hb (x (-3) 10)
            have b24127 := hb (x (-2) 9)
            have b24128 := hb (x (-1) 8)
            clear * - r24114 e24115 e24116 e24117 e24118 e24119 e24120 b24121 b24122 b24123 b24124 b24125 b24126 b24127 b24128 d21692 d24026 d24046 d24054 d24077
            omega
          have d24129 : (x (-1) 2 && x (-1) 8).toNat = 0 := by
            have r24130 := hand2 (x (-1) 2) (x (-1) 8)
            have b24131 := hb (x (-1) 8)
            have b24132 := hb (x (-1) 2 && x (-1) 8)
            clear * - r24130 b24131 b24132 d24113
            omega
          have r24133 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
          have r24134 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
          have e24135 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e24136 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e24137 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e24138 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e24139 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e24140 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have r24141 : 1 ≤ (x 1 1).toNat + (x 0 1 && x 0 2).toNat + (x (-1) 2 && x (-1) 3).toNat + (x (-2) 3 && x (-2) 4).toNat + (x (-3) 4 && x (-3) 5).toNat + (x (-4) 5 && x (-4) 6).toNat + (x (-5) 6 && x (-5) 7).toNat + (x (-6) 7 && x (-6) 8).toNat + (x (-7) 8 && x (-7) 9).toNat + (x (-8) 9 && x (-8) 10).toNat + (x (-9) 10 && x (-9) 11).toNat + (x (-10) 11 && x (-10) 12).toNat + (x (-11) 12 && x (-11) 13).toNat + (x (-12) 13 && x (-12) 14).toNat + (x (-13) 14).toNat := hcov1 1
          have r24142 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := hcov6 1
          have r24143 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
          have r24144 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := hcov9 2
          have r24145 := hand1 (x (-3) 4) (x (-3) 5)
          have r24146 := hand1 (x (-4) 5) (x (-4) 6)
          have r24147 := hand2 (x (-5) 6) (x (-5) 7)
          have r24148 := hand1 (x (-6) 7) (x (-6) 8)
          have r24149 := hand1 (x (-7) 8) (x (-7) 9)
          have r24150 := hand1 (x (-8) 9) (x (-8) 10)
          have r24151 := hand1 (x (-9) 10) (x (-9) 11)
          have r24152 := hand1 (x (-10) 11) (x (-10) 12)
          have r24153 := hand1 (x (-11) 12) (x (-11) 13)
          have r24154 := hand1 (x (-12) 13) (x (-12) 14)
          have r24155 := hand1 (x (-5) 6) (x (-5) 12)
          have r24156 := hand1 (x (-7) 8) (x (-7) 14)
          have r24157 := hand1 (x (-3) 4) (x (-3) 13)
          have r24158 := hand1 (x (-4) 5) (x (-4) 14)
          have r24159 := hand1 (x (-3) 5) (x (-3) 14)
          have b24160 := hb (x (-13) 14)
          have b24161 := hb (x (-12) 13)
          have b24162 := hb (x (-11) 12)
          have b24163 := hb (x (-10) 11)
          have b24164 := hb (x (-9) 10)
          have b24165 := hb (x (-8) 9)
          have b24166 := hb (x (-7) 8)
          have b24167 := hb (x (-6) 7)
          have b24168 := hb (x (-5) 6)
          have b24169 := hb (x (-5) 7)
          have b24170 := hb (x (-4) 5)
          have b24171 := hb (x (-4) 6)
          have b24172 := hb (x (-3) 4)
          have b24173 := hb (x (-3) 5)
          have b24174 := hb (x (-2) 3)
          have b24175 := hb (x (-2) 4)
          have b24176 := hb (x (-1) 2)
          have b24177 := hb (x (-1) 11)
          have b24178 := hb (x 0 1)
          have b24179 := hb (x 0 10)
          have b24180 := hb (x 1 1)
          have b24181 := hb (x 1 6)
          have b24182 := hb (x 1 9)
          have b24183 := hb (x 2 8)
          have b24184 := hb (x 2 9)
          have b24185 := hb (x 0 1 && x 0 2)
          have b24186 := hb (x (-1) 2 && x (-1) 3)
          have b24187 := hb (x (-2) 3 && x (-2) 4)
          have b24188 := hb (x (-3) 4 && x (-3) 5)
          have b24189 := hb (x (-4) 5 && x (-4) 6)
          have b24190 := hb (x (-5) 6 && x (-5) 7)
          have b24191 := hb (x (-6) 7 && x (-6) 8)
          have b24192 := hb (x (-7) 8 && x (-7) 9)
          have b24193 := hb (x (-8) 9 && x (-8) 10)
          have b24194 := hb (x (-9) 10 && x (-9) 11)
          have b24195 := hb (x (-10) 11 && x (-10) 12)
          have b24196 := hb (x (-11) 12 && x (-11) 13)
          have b24197 := hb (x (-12) 13 && x (-12) 14)
          have b24198 := hb (x 0 1 && x 0 7)
          have b24199 := hb (x (-1) 2 && x (-1) 8)
          have b24200 := hb (x (-2) 3 && x (-2) 9)
          have b24201 := hb (x (-3) 4 && x (-3) 10)
          have b24202 := hb (x (-4) 5 && x (-4) 11)
          have b24203 := hb (x (-5) 6 && x (-5) 12)
          have b24204 := hb (x (-6) 7 && x (-6) 13)
          have b24205 := hb (x (-7) 8 && x (-7) 14)
          have b24206 := hb (x 0 1 && x 0 10)
          have b24207 := hb (x (-1) 2 && x (-1) 11)
          have b24208 := hb (x (-2) 3 && x (-2) 12)
          have b24209 := hb (x (-3) 4 && x (-3) 13)
          have b24210 := hb (x (-4) 5 && x (-4) 14)
          have b24211 := hb (x 1 1 && x 1 10)
          have b24212 := hb (x 0 2 && x 0 11)
          have b24213 := hb (x (-1) 3 && x (-1) 12)
          have b24214 := hb (x (-2) 4 && x (-2) 13)
          have b24215 := hb (x (-3) 5 && x (-3) 14)
          linarith only [r24133, r24134, e24135, e24136, e24137, e24138, e24139, e24140, r24141, r24142, r24143, r24144, r24145, r24146, r24147, r24148, r24149, r24150, r24151, r24152, r24153, r24154, r24155, r24156, r24157, r24158, r24159, b24160, b24161, b24162, b24163, b24164, b24165, b24166, b24167, b24168, b24169, b24170, b24171, b24172, b24173, b24174, b24175, b24176, b24177, b24178, b24179, b24180, b24181, b24182, b24183, b24184, b24185, b24186, b24187, b24188, b24189, b24190, b24191, b24192, b24193, b24194, b24195, b24196, b24197, b24198, b24199, b24200, b24201, b24202, b24203, b24204, b24205, b24206, b24207, b24208, b24209, b24210, b24211, b24212, b24213, b24214, b24215, d21781, d21748, g2, g4, g10, f21727, g15, d21736, d24097, g21, g22, d21801, g36, d24129, d21696, d24030, d24050, d24073, g38, g39, d21789, g40, g41, g42, d21672]
      · have f24216 : (x 1 3).toNat = 1 := by rw [h21809]; rfl
        have d24217 : (x 4 12).toNat = 0 := by
          have r24218 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e24219 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e24220 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b24221 := hb (x 1 3)
          have b24222 := hb (x 2 2)
          have b24223 := hb (x 3 13)
          have b24224 := hb (x 4 12)
          clear * - r24218 e24219 e24220 b24221 b24222 b24223 b24224 f24216
          omega
        have d24225 : (x 4 1 && x 4 12).toNat = 0 := by
          have r24226 := hand2 (x 4 1) (x 4 12)
          have b24227 := hb (x 4 12)
          have b24228 := hb (x 4 1 && x 4 12)
          clear * - r24226 b24227 b24228 d24217
          omega
        have d24229 : (x 4 4).toNat = 0 := by
          have r24230 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b24231 := hb (x 4 4)
          have b24232 := hb (x 4 12)
          clear * - r24230 b24231 b24232 d24217
          omega
        have d24233 : (x 3 13).toNat = 0 := by
          have r24234 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e24235 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e24236 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b24237 := hb (x 1 3)
          have b24238 := hb (x 2 2)
          have b24239 := hb (x 3 13)
          have b24240 := hb (x 4 12)
          clear * - r24234 e24235 e24236 b24237 b24238 b24239 b24240 d24217 f24216
          omega
        have d24241 : (x 2 2).toNat = 0 := by
          have r24242 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
          have e24243 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e24244 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b24245 := hb (x 1 3)
          have b24246 := hb (x 2 2)
          have b24247 := hb (x 3 13)
          have b24248 := hb (x 4 12)
          clear * - r24242 e24243 e24244 b24245 b24246 b24247 b24248 d24217 d24233 f24216
          omega
        have d24249 : (x 4 13).toNat = 1 := by
          have r24250 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
          have b24251 := hb (x 2 2)
          have b24252 := hb (x 4 13)
          have b24253 := hb (x 3 1 && x 3 14)
          clear * - r24250 b24251 b24252 b24253 g59 d24241
          omega
        have d24254 : (x 4 1).toNat = 1 := by
          have r24255 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b24256 := hb (x 4 1)
          have b24257 := hb (x 4 13)
          clear * - r24255 b24256 b24257 d24249
          omega
        have d24258 : (x 5 14).toNat = 0 := by
          have r24259 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
          have b24260 := hb (x 4 1)
          have b24261 := hb (x 5 14)
          clear * - r24259 b24260 b24261 d24254
          omega
        have d24262 : (x 5 3 && x 5 14).toNat = 0 := by
          have r24263 := hand2 (x 5 3) (x 5 14)
          have b24264 := hb (x 5 14)
          have b24265 := hb (x 5 3 && x 5 14)
          clear * - r24263 b24264 b24265 d24258
          omega
        have d24266 : (x 5 2).toNat = 0 := by
          have r24267 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b24268 := hb (x 5 2)
          have b24269 := hb (x 5 14)
          clear * - r24267 b24268 b24269 d24258
          omega
        have d24270 : (x 5 12).toNat = 0 := by
          have r24271 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
          have e24272 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e24273 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b24274 := hb (x 2 3)
          have b24275 := hb (x 3 2)
          have b24276 := hb (x 4 13)
          have b24277 := hb (x 5 12)
          clear * - r24271 e24272 e24273 b24274 b24275 b24276 b24277 d24249 g17
          omega
        have d24278 : (x 5 4).toNat = 0 := by
          have r24279 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b24280 := hb (x 5 4)
          have b24281 := hb (x 5 12)
          clear * - r24279 b24280 b24281 d24270
          omega
        have d24282 : (x 2 3).toNat = 0 := by
          have r24283 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
          have e24284 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e24285 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b24286 := hb (x 2 3)
          have b24287 := hb (x 3 2)
          have b24288 := hb (x 4 13)
          have b24289 := hb (x 5 12)
          clear * - r24283 e24284 e24285 b24286 b24287 b24288 b24289 d24270 d24249 g17
          omega
        have d24290 : (x 2 3 && x 2 14).toNat = 0 := by
          have r24291 := hand1 (x 2 3) (x 2 14)
          have b24292 := hb (x 2 3)
          have b24293 := hb (x 2 3 && x 2 14)
          clear * - r24291 b24292 b24293 d24282
          omega
        have d24294 : (x 5 11).toNat = 1 := by
          have r24295 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := hcov11 5
          have b24296 := hb (x 1 4)
          have b24297 := hb (x 5 11)
          have b24298 := hb (x 4 1 && x 4 12)
          have b24299 := hb (x 3 2 && x 3 13)
          have b24300 := hb (x 2 3 && x 2 14)
          clear * - r24295 b24296 b24297 b24298 b24299 b24300 d24225 g56 d24290 d21777
          omega
        have d24301 : (x 5 3).toNat = 1 := by
          have r24302 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b24303 := hb (x 5 3)
          have b24304 := hb (x 5 11)
          clear * - r24302 b24303 b24304 d24294
          omega
        have d24305 : (x 8 12).toNat = 0 := by
          have r24306 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
          have e24307 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e24308 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b24309 := hb (x 5 3)
          have b24310 := hb (x 6 2)
          have b24311 := hb (x 7 13)
          have b24312 := hb (x 8 12)
          clear * - r24306 e24307 e24308 b24309 b24310 b24311 b24312 d24301
          omega
        have d24313 : (x 8 1 && x 8 12).toNat = 0 := by
          have r24314 := hand2 (x 8 1) (x 8 12)
          have b24315 := hb (x 8 12)
          have b24316 := hb (x 8 1 && x 8 12)
          clear * - r24314 b24315 b24316 d24305
          omega
        have d24317 : (x 8 4).toNat = 0 := by
          have r24318 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
          have b24319 := hb (x 8 4)
          have b24320 := hb (x 8 12)
          clear * - r24318 b24319 b24320 d24305
          omega
        have d24321 : (x 7 13).toNat = 0 := by
          have r24322 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
          have e24323 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e24324 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b24325 := hb (x 5 3)
          have b24326 := hb (x 6 2)
          have b24327 := hb (x 7 13)
          have b24328 := hb (x 8 12)
          clear * - r24322 e24323 e24324 b24325 b24326 b24327 b24328 d24305 d24301
          omega
        have d24329 : (x 7 2 && x 7 13).toNat = 0 := by
          have r24330 := hand2 (x 7 2) (x 7 13)
          have b24331 := hb (x 7 13)
          have b24332 := hb (x 7 2 && x 7 13)
          clear * - r24330 b24331 b24332 d24321
          omega
        have d24333 : (x 6 1 && x 6 14).toNat = 1 := by
          have r24334 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
          have b24335 := hb (x 5 2)
          have b24336 := hb (x 7 13)
          have b24337 := hb (x 6 1 && x 6 14)
          clear * - r24334 b24335 b24336 b24337 d24321 d24266
          omega
        have d24338 : (x 6 1).toNat = 1 := by
          have r24339 := hand1 (x 6 1) (x 6 14)
          have b24340 := hb (x 6 1)
          have b24341 := hb (x 6 1 && x 6 14)
          clear * - r24339 b24340 b24341 d24333
          omega
        have d24342 : (x 7 14).toNat = 0 := by
          have r24343 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
          have b24344 := hb (x 6 1)
          have b24345 := hb (x 7 14)
          clear * - r24343 b24344 b24345 d24338
          omega
        have d24346 : (x 7 1 && x 7 14).toNat = 0 := by
          have r24347 := hand2 (x 7 1) (x 7 14)
          have b24348 := hb (x 7 14)
          have b24349 := hb (x 7 1 && x 7 14)
          clear * - r24347 b24348 b24349 d24342
          omega
        have d24350 : (x 7 2).toNat = 0 := by
          have r24351 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b24352 := hb (x 7 2)
          have b24353 := hb (x 7 14)
          clear * - r24351 b24352 b24353 d24342
          omega
        have d24354 : (x 6 2).toNat = 0 := by
          have r24355 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
          have e24356 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e24357 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b24358 := hb (x 5 3)
          have b24359 := hb (x 6 2)
          have b24360 := hb (x 7 13)
          have b24361 := hb (x 8 12)
          clear * - r24355 e24356 e24357 b24358 b24359 b24360 b24361 d24305 d24321 d24301
          omega
        have d24362 : (x 6 2 && x 6 13).toNat = 0 := by
          have r24363 := hand1 (x 6 2) (x 6 13)
          have b24364 := hb (x 6 2)
          have b24365 := hb (x 6 2 && x 6 13)
          clear * - r24363 b24364 b24365 d24354
          omega
        have d24366 : (x 8 13).toNat = 1 := by
          have r24367 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
          have b24368 := hb (x 6 2)
          have b24369 := hb (x 8 13)
          have b24370 := hb (x 7 1 && x 7 14)
          clear * - r24367 b24368 b24369 b24370 d24346 d24354
          omega
        have d24371 : (x 8 1).toNat = 1 := by
          have r24372 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b24373 := hb (x 8 1)
          have b24374 := hb (x 8 13)
          clear * - r24372 b24373 b24374 d24366
          omega
        have d24375 : (x 9 14).toNat = 0 := by
          have r24376 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
          have b24377 := hb (x 8 1)
          have b24378 := hb (x 9 14)
          clear * - r24376 b24377 b24378 d24371
          omega
        have d24379 : (x 9 3 && x 9 14).toNat = 0 := by
          have r24380 := hand2 (x 9 3) (x 9 14)
          have b24381 := hb (x 9 14)
          have b24382 := hb (x 9 3 && x 9 14)
          clear * - r24380 b24381 b24382 d24375
          omega
        have d24383 : (x 9 2).toNat = 0 := by
          have r24384 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b24385 := hb (x 9 2)
          have b24386 := hb (x 9 14)
          clear * - r24384 b24385 b24386 d24375
          omega
        have d24387 : (x 9 12).toNat = 0 := by
          have r24388 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
          have e24389 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e24390 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b24391 := hb (x 6 3)
          have b24392 := hb (x 7 2)
          have b24393 := hb (x 8 13)
          have b24394 := hb (x 9 12)
          clear * - r24388 e24389 e24390 b24391 b24392 b24393 b24394 d24366 d24350
          omega
        have d24395 : (x 9 4).toNat = 0 := by
          have r24396 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
          have b24397 := hb (x 9 4)
          have b24398 := hb (x 9 12)
          clear * - r24396 b24397 b24398 d24387
          omega
        have d24399 : (x 6 3).toNat = 0 := by
          have r24400 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
          have e24401 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e24402 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b24403 := hb (x 6 3)
          have b24404 := hb (x 7 2)
          have b24405 := hb (x 8 13)
          have b24406 := hb (x 9 12)
          clear * - r24400 e24401 e24402 b24403 b24404 b24405 b24406 d24387 d24366 d24350
          omega
        have d24407 : (x 6 3 && x 6 14).toNat = 0 := by
          have r24408 := hand1 (x 6 3) (x 6 14)
          have b24409 := hb (x 6 3)
          have b24410 := hb (x 6 3 && x 6 14)
          clear * - r24408 b24409 b24410 d24399
          omega
        have d24411 : (x 9 11).toNat = 1 := by
          have r24412 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := hcov11 9
          have b24413 := hb (x 5 4)
          have b24414 := hb (x 9 11)
          have b24415 := hb (x 8 1 && x 8 12)
          have b24416 := hb (x 7 2 && x 7 13)
          have b24417 := hb (x 6 3 && x 6 14)
          clear * - r24412 b24413 b24414 b24415 b24416 b24417 d24313 d24329 d24407 d24278
          omega
        have d24418 : (x 9 3).toNat = 1 := by
          have r24419 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
          have b24420 := hb (x 9 3)
          have b24421 := hb (x 9 11)
          clear * - r24419 b24420 b24421 d24411
          omega
        have d24422 : (x 12 12).toNat = 0 := by
          have r24423 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
          have e24424 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e24425 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b24426 := hb (x 9 3)
          have b24427 := hb (x 10 2)
          have b24428 := hb (x 11 13)
          have b24429 := hb (x 12 12)
          clear * - r24423 e24424 e24425 b24426 b24427 b24428 b24429 d24418
          omega
        have d24430 : (x 12 1 && x 12 12).toNat = 0 := by
          have r24431 := hand2 (x 12 1) (x 12 12)
          have b24432 := hb (x 12 12)
          have b24433 := hb (x 12 1 && x 12 12)
          clear * - r24431 b24432 b24433 d24422
          omega
        have d24434 : (x 12 4).toNat = 0 := by
          have r24435 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
          have b24436 := hb (x 12 4)
          have b24437 := hb (x 12 12)
          clear * - r24435 b24436 b24437 d24422
          omega
        have d24438 : (x 11 13).toNat = 0 := by
          have r24439 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
          have e24440 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e24441 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b24442 := hb (x 9 3)
          have b24443 := hb (x 10 2)
          have b24444 := hb (x 11 13)
          have b24445 := hb (x 12 12)
          clear * - r24439 e24440 e24441 b24442 b24443 b24444 b24445 d24422 d24418
          omega
        have d24446 : (x 11 2 && x 11 13).toNat = 0 := by
          have r24447 := hand2 (x 11 2) (x 11 13)
          have b24448 := hb (x 11 13)
          have b24449 := hb (x 11 2 && x 11 13)
          clear * - r24447 b24448 b24449 d24438
          omega
        have d24450 : (x 10 1 && x 10 14).toNat = 1 := by
          have r24451 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
          have b24452 := hb (x 9 2)
          have b24453 := hb (x 11 13)
          have b24454 := hb (x 10 1 && x 10 14)
          clear * - r24451 b24452 b24453 b24454 d24438 d24383
          omega
        have d24455 : (x 10 14).toNat = 1 := by
          have r24456 := hand2 (x 10 1) (x 10 14)
          have b24457 := hb (x 10 14)
          have b24458 := hb (x 10 1 && x 10 14)
          clear * - r24456 b24457 b24458 d24450
          omega
        have d24459 : (x 9 1).toNat = 0 := by
          have r24460 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
          have b24461 := hb (x 9 1)
          have b24462 := hb (x 10 14)
          clear * - r24460 b24461 b24462 d24455
          omega
        have d24463 : (x 9 13).toNat = 0 := by
          have r24464 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b24465 := hb (x 9 1)
          have b24466 := hb (x 9 13)
          clear * - r24464 b24465 b24466 d24459
          omega
        have d24467 : (x 8 1 && x 8 14).toNat = 1 := by
          have r24468 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
          have b24469 := hb (x 7 2)
          have b24470 := hb (x 9 13)
          have b24471 := hb (x 8 1 && x 8 14)
          clear * - r24468 b24469 b24470 b24471 d24463 d24350
          omega
        have d24472 : (x 8 14).toNat = 1 := by
          have r24473 := hand2 (x 8 1) (x 8 14)
          have b24474 := hb (x 8 14)
          have b24475 := hb (x 8 1 && x 8 14)
          clear * - r24473 b24474 b24475 d24467
          omega
        have d24476 : (x 7 1).toNat = 0 := by
          have r24477 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
          have b24478 := hb (x 7 1)
          have b24479 := hb (x 8 14)
          clear * - r24477 b24478 b24479 d24472
          omega
        have d24480 : (x 7 1 && x 7 12).toNat = 0 := by
          have r24481 := hand1 (x 7 1) (x 7 12)
          have b24482 := hb (x 7 1)
          have b24483 := hb (x 7 1 && x 7 12)
          clear * - r24481 b24482 b24483 d24476
          omega
        have d24484 : (x 8 11).toNat = 1 := by
          have r24485 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
          have b24486 := hb (x 4 4)
          have b24487 := hb (x 8 11)
          have b24488 := hb (x 7 1 && x 7 12)
          have b24489 := hb (x 6 2 && x 6 13)
          have b24490 := hb (x 5 3 && x 5 14)
          clear * - r24485 b24486 b24487 b24488 b24489 b24490 d24480 d24362 d24262 d24229
          omega
        have d24491 : (x 8 3).toNat = 1 := by
          have r24492 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b24493 := hb (x 8 3)
          have b24494 := hb (x 8 11)
          clear * - r24492 b24493 b24494 d24484
          omega
        have d24495 : (x 11 12).toNat = 0 := by
          have r24496 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
          have e24497 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e24498 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b24499 := hb (x 8 3)
          have b24500 := hb (x 9 2)
          have b24501 := hb (x 10 13)
          have b24502 := hb (x 11 12)
          clear * - r24496 e24497 e24498 b24499 b24500 b24501 b24502 d24383 d24491
          omega
        have d24503 : (x 11 1 && x 11 12).toNat = 0 := by
          have r24504 := hand2 (x 11 1) (x 11 12)
          have b24505 := hb (x 11 12)
          have b24506 := hb (x 11 1 && x 11 12)
          clear * - r24504 b24505 b24506 d24495
          omega
        have d24507 : (x 10 13).toNat = 0 := by
          have r24508 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
          have e24509 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e24510 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b24511 := hb (x 8 3)
          have b24512 := hb (x 9 2)
          have b24513 := hb (x 10 13)
          have b24514 := hb (x 11 12)
          clear * - r24508 e24509 e24510 b24511 b24512 b24513 b24514 d24495 d24383 d24491
          omega
        have d24515 : (x 10 2 && x 10 13).toNat = 0 := by
          have r24516 := hand2 (x 10 2) (x 10 13)
          have b24517 := hb (x 10 13)
          have b24518 := hb (x 10 2 && x 10 13)
          clear * - r24516 b24517 b24518 d24507
          omega
        have d24519 : (x 12 11).toNat = 1 := by
          have r24520 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
          have b24521 := hb (x 8 4)
          have b24522 := hb (x 12 11)
          have b24523 := hb (x 11 1 && x 11 12)
          have b24524 := hb (x 10 2 && x 10 13)
          have b24525 := hb (x 9 3 && x 9 14)
          clear * - r24520 b24521 b24522 b24523 b24524 b24525 d24503 d24515 d24379 d24317
          omega
        have d24526 : (x 12 3).toNat = 1 := by
          have r24527 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
          have b24528 := hb (x 12 3)
          have b24529 := hb (x 12 11)
          clear * - r24527 b24528 b24529 d24519
          omega
        have d24530 : (x 15 12).toNat = 0 := by
          have r24531 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
          have e24532 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e24533 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b24534 := hb (x 12 3)
          have b24535 := hb (x 13 2)
          have b24536 := hb (x 14 13)
          have b24537 := hb (x 15 12)
          clear * - r24531 e24532 e24533 b24534 b24535 b24536 b24537 d24526
          omega
        have d24538 : (x 15 1 && x 15 12).toNat = 0 := by
          have r24539 := hand2 (x 15 1) (x 15 12)
          have b24540 := hb (x 15 12)
          have b24541 := hb (x 15 1 && x 15 12)
          clear * - r24539 b24540 b24541 d24530
          omega
        have d24542 : (x 14 13).toNat = 0 := by
          have r24543 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
          have e24544 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e24545 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b24546 := hb (x 12 3)
          have b24547 := hb (x 13 2)
          have b24548 := hb (x 14 13)
          have b24549 := hb (x 15 12)
          clear * - r24543 e24544 e24545 b24546 b24547 b24548 b24549 d24530 d24526
          omega
        have d24550 : (x 14 2 && x 14 13).toNat = 0 := by
          have r24551 := hand2 (x 14 2) (x 14 13)
          have b24552 := hb (x 14 13)
          have b24553 := hb (x 14 2 && x 14 13)
          clear * - r24551 b24552 b24553 d24542
          omega
        have d24554 : (x 13 2).toNat = 0 := by
          have r24555 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
          have e24556 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e24557 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b24558 := hb (x 12 3)
          have b24559 := hb (x 13 2)
          have b24560 := hb (x 14 13)
          have b24561 := hb (x 15 12)
          clear * - r24555 e24556 e24557 b24558 b24559 b24560 b24561 d24530 d24542 d24526
          omega
        have d24562 : (x 10 1).toNat = 1 := by
          have r24563 := hand1 (x 10 1) (x 10 14)
          have b24564 := hb (x 10 1)
          have b24565 := hb (x 10 1 && x 10 14)
          clear * - r24563 b24564 b24565 d24450
          omega
        have d24566 : (x 11 14).toNat = 0 := by
          have r24567 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
          have b24568 := hb (x 10 1)
          have b24569 := hb (x 11 14)
          clear * - r24567 b24568 b24569 d24562
          omega
        have d24570 : (x 11 1 && x 11 14).toNat = 0 := by
          have r24571 := hand2 (x 11 1) (x 11 14)
          have b24572 := hb (x 11 14)
          have b24573 := hb (x 11 1 && x 11 14)
          clear * - r24571 b24572 b24573 d24566
          omega
        have d24574 : (x 11 2).toNat = 0 := by
          have r24575 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b24576 := hb (x 11 2)
          have b24577 := hb (x 11 14)
          clear * - r24575 b24576 b24577 d24566
          omega
        have d24578 : (x 10 2).toNat = 0 := by
          have r24579 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
          have e24580 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e24581 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b24582 := hb (x 9 3)
          have b24583 := hb (x 10 2)
          have b24584 := hb (x 11 13)
          have b24585 := hb (x 12 12)
          clear * - r24579 e24580 e24581 b24582 b24583 b24584 b24585 d24422 d24438 d24418
          omega
        have d24586 : (x 12 13).toNat = 1 := by
          have r24587 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
          have b24588 := hb (x 10 2)
          have b24589 := hb (x 12 13)
          have b24590 := hb (x 11 1 && x 11 14)
          clear * - r24587 b24588 b24589 b24590 d24570 d24578
          omega
        have d24591 : (x 12 1).toNat = 1 := by
          have r24592 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b24593 := hb (x 12 1)
          have b24594 := hb (x 12 13)
          clear * - r24592 b24593 b24594 d24586
          omega
        have d24595 : (x 13 14).toNat = 0 := by
          have r24596 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
          have b24597 := hb (x 12 1)
          have b24598 := hb (x 13 14)
          clear * - r24596 b24597 b24598 d24591
          omega
        have d24599 : (x 13 1 && x 13 14).toNat = 0 := by
          have r24600 := hand2 (x 13 1) (x 13 14)
          have b24601 := hb (x 13 14)
          have b24602 := hb (x 13 1 && x 13 14)
          clear * - r24600 b24601 b24602 d24595
          omega
        have d24603 : (x 12 2).toNat = 1 := by
          have r24604 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
          have b24605 := hb (x 12 2)
          have b24606 := hb (x 14 13)
          have b24607 := hb (x 13 1 && x 13 14)
          clear * - r24604 b24605 b24606 b24607 d24542 d24599
          omega
        have d24608 : (x 14 12).toNat = 0 := by
          have r24609 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
          have e24610 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e24611 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b24612 := hb (x 11 3)
          have b24613 := hb (x 12 2)
          have b24614 := hb (x 13 13)
          have b24615 := hb (x 14 12)
          clear * - r24609 e24610 e24611 b24612 b24613 b24614 b24615 d24603
          omega
        have d24616 : (x 14 4).toNat = 0 := by
          have r24617 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
          have b24618 := hb (x 14 4)
          have b24619 := hb (x 14 12)
          clear * - r24617 b24618 b24619 d24608
          omega
        have d24620 : (x 14 4 && x 14 14).toNat = 0 := by
          have r24621 := hand1 (x 14 4) (x 14 14)
          have b24622 := hb (x 14 4)
          have b24623 := hb (x 14 4 && x 14 14)
          clear * - r24621 b24622 b24623 d24616
          omega
        have d24624 : (x 13 13).toNat = 0 := by
          have r24625 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
          have e24626 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e24627 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b24628 := hb (x 11 3)
          have b24629 := hb (x 12 2)
          have b24630 := hb (x 13 13)
          have b24631 := hb (x 14 12)
          clear * - r24625 e24626 e24627 b24628 b24629 b24630 b24631 d24608 d24603
          omega
        have d24632 : (x 13 5).toNat = 0 := by
          have r24633 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
          have b24634 := hb (x 13 5)
          have b24635 := hb (x 13 13)
          clear * - r24633 b24634 b24635 d24624
          omega
        have d24636 : (x 13 3 && x 13 14).toNat = 0 := by
          have r24637 := hand2 (x 13 3) (x 13 14)
          have b24638 := hb (x 13 14)
          have b24639 := hb (x 13 3 && x 13 14)
          clear * - r24637 b24638 b24639 d24595
          omega
        have d24640 : (x 16 11).toNat = 1 := by
          have r24641 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := hcov11 16
          have b24642 := hb (x 12 4)
          have b24643 := hb (x 16 11)
          have b24644 := hb (x 15 1 && x 15 12)
          have b24645 := hb (x 14 2 && x 14 13)
          have b24646 := hb (x 13 3 && x 13 14)
          clear * - r24641 b24642 b24643 b24644 b24645 b24646 d24538 d24550 d24636 d24434
          omega
        have d24647 : (x 16 3).toNat = 1 := by
          have r24648 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
          have b24649 := hb (x 16 3)
          have b24650 := hb (x 16 11)
          clear * - r24648 b24649 b24650 d24640
          omega
        have d24651 : (x 19 12).toNat = 0 := by
          have r24652 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
          have e24653 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e24654 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b24655 := hb (x 16 3)
          have b24656 := hb (x 17 2)
          have b24657 := hb (x 18 13)
          have b24658 := hb (x 19 12)
          clear * - r24652 e24653 e24654 b24655 b24656 b24657 b24658 d24647
          omega
        have d24659 : (x 18 13).toNat = 0 := by
          have r24660 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
          have e24661 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e24662 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b24663 := hb (x 16 3)
          have b24664 := hb (x 17 2)
          have b24665 := hb (x 18 13)
          have b24666 := hb (x 19 12)
          clear * - r24660 e24661 e24662 b24663 b24664 b24665 b24666 d24651 d24647
          omega
        have d24667 : (x 17 2).toNat = 0 := by
          have r24668 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
          have e24669 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e24670 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b24671 := hb (x 16 3)
          have b24672 := hb (x 17 2)
          have b24673 := hb (x 18 13)
          have b24674 := hb (x 19 12)
          clear * - r24668 e24669 e24670 b24671 b24672 b24673 b24674 d24651 d24659 d24647
          omega
        have d24675 : (x 13 12).toNat = 0 := by
          have r24676 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e24677 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e24678 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b24679 := hb (x 10 3)
          have b24680 := hb (x 11 2)
          have b24681 := hb (x 12 13)
          have b24682 := hb (x 13 12)
          clear * - r24676 e24677 e24678 b24679 b24680 b24681 b24682 d24586 d24574
          omega
        have d24683 : (x 13 4).toNat = 0 := by
          have r24684 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b24685 := hb (x 13 4)
          have b24686 := hb (x 13 12)
          clear * - r24684 b24685 b24686 d24675
          omega
        have d24687 : (x 10 3).toNat = 0 := by
          have r24688 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
          have e24689 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e24690 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b24691 := hb (x 10 3)
          have b24692 := hb (x 11 2)
          have b24693 := hb (x 12 13)
          have b24694 := hb (x 13 12)
          clear * - r24688 e24689 e24690 b24691 b24692 b24693 b24694 d24675 d24586 d24574
          omega
        have d24695 : (x 10 3 && x 10 14).toNat = 0 := by
          have r24696 := hand1 (x 10 3) (x 10 14)
          have b24697 := hb (x 10 3)
          have b24698 := hb (x 10 3 && x 10 14)
          clear * - r24696 b24697 b24698 d24687
          omega
        have d24699 : (x 13 11).toNat = 1 := by
          have r24700 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := hcov11 13
          have b24701 := hb (x 9 4)
          have b24702 := hb (x 13 11)
          have b24703 := hb (x 12 1 && x 12 12)
          have b24704 := hb (x 11 2 && x 11 13)
          have b24705 := hb (x 10 3 && x 10 14)
          clear * - r24700 b24701 b24702 b24703 b24704 b24705 d24430 d24446 d24695 d24395
          omega
        have d24706 : (x 13 3).toNat = 1 := by
          have r24707 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
          have b24708 := hb (x 13 3)
          have b24709 := hb (x 13 11)
          clear * - r24707 b24708 b24709 d24699
          omega
        have d24710 : (x 16 12).toNat = 0 := by
          have r24711 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e24712 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e24713 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b24714 := hb (x 13 3)
          have b24715 := hb (x 14 2)
          have b24716 := hb (x 15 13)
          have b24717 := hb (x 16 12)
          clear * - r24711 e24712 e24713 b24714 b24715 b24716 b24717 d24706
          omega
        have d24718 : (x 16 1 && x 16 12).toNat = 0 := by
          have r24719 := hand2 (x 16 1) (x 16 12)
          have b24720 := hb (x 16 12)
          have b24721 := hb (x 16 1 && x 16 12)
          clear * - r24719 b24720 b24721 d24710
          omega
        have d24722 : (x 16 2 && x 16 12).toNat = 0 := by
          have r24723 := hand2 (x 16 2) (x 16 12)
          have b24724 := hb (x 16 12)
          have b24725 := hb (x 16 2 && x 16 12)
          clear * - r24723 b24724 b24725 d24710
          omega
        have d24726 : (x 15 13).toNat = 0 := by
          have r24727 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e24728 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e24729 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b24730 := hb (x 13 3)
          have b24731 := hb (x 14 2)
          have b24732 := hb (x 15 13)
          have b24733 := hb (x 16 12)
          clear * - r24727 e24728 e24729 b24730 b24731 b24732 b24733 d24710 d24706
          omega
        have d24734 : (x 15 2 && x 15 13).toNat = 0 := by
          have r24735 := hand2 (x 15 2) (x 15 13)
          have b24736 := hb (x 15 13)
          have b24737 := hb (x 15 2 && x 15 13)
          clear * - r24735 b24736 b24737 d24726
          omega
        have d24738 : (x 15 3 && x 15 13).toNat = 0 := by
          have r24739 := hand2 (x 15 3) (x 15 13)
          have b24740 := hb (x 15 13)
          have b24741 := hb (x 15 3 && x 15 13)
          clear * - r24739 b24740 b24741 d24726
          omega
        have d24742 : (x 14 1 && x 14 14).toNat = 1 := by
          have r24743 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
          have b24744 := hb (x 13 2)
          have b24745 := hb (x 15 13)
          have b24746 := hb (x 14 1 && x 14 14)
          clear * - r24743 b24744 b24745 b24746 d24726 d24554
          omega
        have d24747 : (x 14 1).toNat = 1 := by
          have r24748 := hand1 (x 14 1) (x 14 14)
          have b24749 := hb (x 14 1)
          have b24750 := hb (x 14 1 && x 14 14)
          clear * - r24748 b24749 b24750 d24742
          omega
        have d24751 : (x 15 14).toNat = 0 := by
          have r24752 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
          have b24753 := hb (x 14 1)
          have b24754 := hb (x 15 14)
          clear * - r24752 b24753 b24754 d24747
          omega
        have d24755 : (x 15 1 && x 15 14).toNat = 0 := by
          have r24756 := hand2 (x 15 1) (x 15 14)
          have b24757 := hb (x 15 14)
          have b24758 := hb (x 15 1 && x 15 14)
          clear * - r24756 b24757 b24758 d24751
          omega
        have d24759 : (x 15 2).toNat = 0 := by
          have r24760 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b24761 := hb (x 15 2)
          have b24762 := hb (x 15 14)
          clear * - r24760 b24761 b24762 d24751
          omega
        have d24763 : (x 14 2).toNat = 0 := by
          have r24764 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
          have e24765 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e24766 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b24767 := hb (x 13 3)
          have b24768 := hb (x 14 2)
          have b24769 := hb (x 15 13)
          have b24770 := hb (x 16 12)
          clear * - r24764 e24765 e24766 b24767 b24768 b24769 b24770 d24710 d24726 d24706
          omega
        have d24771 : (x 16 13).toNat = 1 := by
          have r24772 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
          have b24773 := hb (x 14 2)
          have b24774 := hb (x 16 13)
          have b24775 := hb (x 15 1 && x 15 14)
          clear * - r24772 b24773 b24774 b24775 d24755 d24763
          omega
        have d24776 : (x 17 12).toNat = 0 := by
          have r24777 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e24778 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e24779 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b24780 := hb (x 14 3)
          have b24781 := hb (x 15 2)
          have b24782 := hb (x 16 13)
          have b24783 := hb (x 17 12)
          clear * - r24777 e24778 e24779 b24780 b24781 b24782 b24783 d24771 d24759
          omega
        have d24784 : (x 14 3).toNat = 0 := by
          have r24785 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
          have e24786 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e24787 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b24788 := hb (x 14 3)
          have b24789 := hb (x 15 2)
          have b24790 := hb (x 16 13)
          have b24791 := hb (x 17 12)
          clear * - r24785 e24786 e24787 b24788 b24789 b24790 b24791 d24776 d24771 d24759
          omega
        have d24792 : (x 14 3 && x 14 14).toNat = 0 := by
          have r24793 := hand1 (x 14 3) (x 14 14)
          have b24794 := hb (x 14 3)
          have b24795 := hb (x 14 3 && x 14 14)
          clear * - r24793 b24794 b24795 d24784
          omega
        have d24796 : (x 17 11).toNat = 1 := by
          have r24797 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
          have b24798 := hb (x 13 4)
          have b24799 := hb (x 17 11)
          have b24800 := hb (x 16 1 && x 16 12)
          have b24801 := hb (x 15 2 && x 15 13)
          have b24802 := hb (x 14 3 && x 14 14)
          clear * - r24797 b24798 b24799 b24800 b24801 b24802 d24718 d24734 d24792 d24683
          omega
        have d24803 : (x 17 3).toNat = 1 := by
          have r24804 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b24805 := hb (x 17 3)
          have b24806 := hb (x 17 11)
          clear * - r24804 b24805 b24806 d24796
          omega
        have d24807 : (x 20 12).toNat = 0 := by
          have r24808 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e24809 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e24810 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b24811 := hb (x 17 3)
          have b24812 := hb (x 18 2)
          have b24813 := hb (x 19 13)
          have b24814 := hb (x 20 12)
          clear * - r24808 e24809 e24810 b24811 b24812 b24813 b24814 d24803
          omega
        have d24815 : (x 19 13).toNat = 0 := by
          have r24816 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e24817 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e24818 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b24819 := hb (x 17 3)
          have b24820 := hb (x 18 2)
          have b24821 := hb (x 19 13)
          have b24822 := hb (x 20 12)
          clear * - r24816 e24817 e24818 b24819 b24820 b24821 b24822 d24807 d24803
          omega
        have d24823 : (x 18 1 && x 18 14).toNat = 1 := by
          have r24824 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
          have b24825 := hb (x 17 2)
          have b24826 := hb (x 19 13)
          have b24827 := hb (x 18 1 && x 18 14)
          clear * - r24824 b24825 b24826 b24827 d24815 d24667
          omega
        have d24828 : (x 18 14).toNat = 1 := by
          have r24829 := hand2 (x 18 1) (x 18 14)
          have b24830 := hb (x 18 14)
          have b24831 := hb (x 18 1 && x 18 14)
          clear * - r24829 b24830 b24831 d24823
          omega
        have d24832 : (x 17 1).toNat = 0 := by
          have r24833 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
          have b24834 := hb (x 17 1)
          have b24835 := hb (x 18 14)
          clear * - r24833 b24834 b24835 d24828
          omega
        have d24836 : (x 17 1 && x 17 11).toNat = 0 := by
          have r24837 := hand1 (x 17 1) (x 17 11)
          have b24838 := hb (x 17 1)
          have b24839 := hb (x 17 1 && x 17 11)
          clear * - r24837 b24838 b24839 d24832
          omega
        have d24840 : (x 18 2).toNat = 0 := by
          have r24841 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
          have e24842 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e24843 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b24844 := hb (x 17 3)
          have b24845 := hb (x 18 2)
          have b24846 := hb (x 19 13)
          have b24847 := hb (x 20 12)
          clear * - r24841 e24842 e24843 b24844 b24845 b24846 b24847 d24807 d24815 d24803
          omega
        have d24848 : (x 18 10).toNat = 0 := by
          have r24849 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
          have b24850 := hb (x 18 2)
          have b24851 := hb (x 18 10)
          clear * - r24849 b24850 b24851 d24840
          omega
        have r24852 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := hcov10 18
        have b24853 := hb (x 13 5)
        have b24854 := hb (x 18 10)
        have b24855 := hb (x 17 1 && x 17 11)
        have b24856 := hb (x 16 2 && x 16 12)
        have b24857 := hb (x 15 3 && x 15 13)
        have b24858 := hb (x 14 4 && x 14 14)
        linarith only [r24852, b24853, b24854, b24855, b24856, b24857, b24858, d24848, d24836, d24722, d24738, d24620, d24632]
    · have f24859 : (x 1 1).toNat = 1 := by rw [h21726]; rfl
      have d24860 : (x 2 14).toNat = 0 := by
        have r24861 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
        have b24862 := hb (x 1 1)
        have b24863 := hb (x 2 14)
        clear * - r24861 b24862 b24863 f24859
        omega
      have d24864 : (x 2 1 && x 2 14).toNat = 0 := by
        have r24865 := hand2 (x 2 1) (x 2 14)
        have b24866 := hb (x 2 14)
        have b24867 := hb (x 2 1 && x 2 14)
        clear * - r24865 b24866 b24867 d24860
        omega
      have d24868 : (x 2 2).toNat = 0 := by
        have r24869 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b24870 := hb (x 2 2)
        have b24871 := hb (x 2 14)
        clear * - r24869 b24870 b24871 d24860
        omega
      have d24872 : (x 4 13).toNat = 1 := by
        have r24873 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
        have b24874 := hb (x 2 2)
        have b24875 := hb (x 4 13)
        have b24876 := hb (x 3 1 && x 3 14)
        clear * - r24873 b24874 b24875 b24876 g59 d24868
        omega
      have d24877 : (x 4 1).toNat = 1 := by
        have r24878 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b24879 := hb (x 4 1)
        have b24880 := hb (x 4 13)
        clear * - r24878 b24879 b24880 d24872
        omega
      have d24881 : (x 5 14).toNat = 0 := by
        have r24882 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
        have b24883 := hb (x 4 1)
        have b24884 := hb (x 5 14)
        clear * - r24882 b24883 b24884 d24877
        omega
      have d24885 : (x 5 1 && x 5 14).toNat = 0 := by
        have r24886 := hand2 (x 5 1) (x 5 14)
        have b24887 := hb (x 5 14)
        have b24888 := hb (x 5 1 && x 5 14)
        clear * - r24886 b24887 b24888 d24881
        omega
      have d24889 : (x 5 2).toNat = 0 := by
        have r24890 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b24891 := hb (x 5 2)
        have b24892 := hb (x 5 14)
        clear * - r24890 b24891 b24892 d24881
        omega
      have d24893 : (x 3 13).toNat = 1 := by
        have r24894 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
        have b24895 := hb (x 1 2)
        have b24896 := hb (x 3 13)
        have b24897 := hb (x 2 1 && x 2 14)
        clear * - r24894 b24895 b24896 b24897 d24864 g14
        omega
      have d24898 : (x 3 1).toNat = 1 := by
        have r24899 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b24900 := hb (x 3 1)
        have b24901 := hb (x 3 13)
        clear * - r24899 b24900 b24901 d24893
        omega
      have d24902 : (x 4 14).toNat = 0 := by
        have r24903 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
        have b24904 := hb (x 3 1)
        have b24905 := hb (x 4 14)
        clear * - r24903 b24904 b24905 d24898
        omega
      have d24906 : (x 4 1 && x 4 14).toNat = 0 := by
        have r24907 := hand2 (x 4 1) (x 4 14)
        have b24908 := hb (x 4 14)
        have b24909 := hb (x 4 1 && x 4 14)
        clear * - r24907 b24908 b24909 d24902
        omega
      have d24910 : (x 5 13).toNat = 1 := by
        have r24911 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
        have b24912 := hb (x 3 2)
        have b24913 := hb (x 5 13)
        have b24914 := hb (x 4 1 && x 4 14)
        clear * - r24911 b24912 b24913 b24914 d24906 g17
        omega
      have d24915 : (x 5 1).toNat = 1 := by
        have r24916 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
        have b24917 := hb (x 5 1)
        have b24918 := hb (x 5 13)
        clear * - r24916 b24917 b24918 d24910
        omega
      have d24919 : (x 6 14).toNat = 0 := by
        have r24920 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
        have b24921 := hb (x 5 1)
        have b24922 := hb (x 6 14)
        clear * - r24920 b24921 b24922 d24915
        omega
      have d24923 : (x 6 1 && x 6 14).toNat = 0 := by
        have r24924 := hand2 (x 6 1) (x 6 14)
        have b24925 := hb (x 6 14)
        have b24926 := hb (x 6 1 && x 6 14)
        clear * - r24924 b24925 b24926 d24919
        omega
      have d24927 : (x 7 13).toNat = 1 := by
        have r24928 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
        have b24929 := hb (x 5 2)
        have b24930 := hb (x 7 13)
        have b24931 := hb (x 6 1 && x 6 14)
        clear * - r24928 b24929 b24930 b24931 d24923 d24889
        omega
      have d24932 : (x 7 1).toNat = 1 := by
        have r24933 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
        have b24934 := hb (x 7 1)
        have b24935 := hb (x 7 13)
        clear * - r24933 b24934 b24935 d24927
        omega
      have d24936 : (x 8 14).toNat = 0 := by
        have r24937 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
        have b24938 := hb (x 7 1)
        have b24939 := hb (x 8 14)
        clear * - r24937 b24938 b24939 d24932
        omega
      have d24940 : (x 8 1 && x 8 14).toNat = 0 := by
        have r24941 := hand2 (x 8 1) (x 8 14)
        have b24942 := hb (x 8 14)
        have b24943 := hb (x 8 1 && x 8 14)
        clear * - r24941 b24942 b24943 d24936
        omega
      have d24944 : (x 8 2).toNat = 0 := by
        have r24945 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
        have b24946 := hb (x 8 2)
        have b24947 := hb (x 8 14)
        clear * - r24945 b24946 b24947 d24936
        omega
      have d24948 : (x 6 2).toNat = 0 := by
        have r24949 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have b24950 := hb (x 6 2)
        have b24951 := hb (x 6 14)
        clear * - r24949 b24950 b24951 d24919
        omega
      have d24952 : (x 4 2).toNat = 0 := by
        have r24953 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
        have b24954 := hb (x 4 2)
        have b24955 := hb (x 4 14)
        clear * - r24953 b24954 b24955 d24902
        omega
      have d24956 : (x 6 13).toNat = 1 := by
        have r24957 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
        have b24958 := hb (x 4 2)
        have b24959 := hb (x 6 13)
        have b24960 := hb (x 5 1 && x 5 14)
        clear * - r24957 b24958 b24959 b24960 d24885 d24952
        omega
      have d24961 : (x 6 1).toNat = 1 := by
        have r24962 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
        have b24963 := hb (x 6 1)
        have b24964 := hb (x 6 13)
        clear * - r24962 b24963 b24964 d24956
        omega
      have d24965 : (x 7 14).toNat = 0 := by
        have r24966 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
        have b24967 := hb (x 6 1)
        have b24968 := hb (x 7 14)
        clear * - r24966 b24967 b24968 d24961
        omega
      have d24969 : (x 7 1 && x 7 14).toNat = 0 := by
        have r24970 := hand2 (x 7 1) (x 7 14)
        have b24971 := hb (x 7 14)
        have b24972 := hb (x 7 1 && x 7 14)
        clear * - r24970 b24971 b24972 d24965
        omega
      have d24973 : (x 8 13).toNat = 1 := by
        have r24974 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
        have b24975 := hb (x 6 2)
        have b24976 := hb (x 8 13)
        have b24977 := hb (x 7 1 && x 7 14)
        clear * - r24974 b24975 b24976 b24977 d24969 d24948
        omega
      have d24978 : (x 8 1).toNat = 1 := by
        have r24979 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b24980 := hb (x 8 1)
        have b24981 := hb (x 8 13)
        clear * - r24979 b24980 b24981 d24973
        omega
      have d24982 : (x 9 14).toNat = 0 := by
        have r24983 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
        have b24984 := hb (x 8 1)
        have b24985 := hb (x 9 14)
        clear * - r24983 b24984 b24985 d24978
        omega
      have d24986 : (x 9 1 && x 9 14).toNat = 0 := by
        have r24987 := hand2 (x 9 1) (x 9 14)
        have b24988 := hb (x 9 14)
        have b24989 := hb (x 9 1 && x 9 14)
        clear * - r24987 b24988 b24989 d24982
        omega
      have d24990 : (x 10 13).toNat = 1 := by
        have r24991 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
        have b24992 := hb (x 8 2)
        have b24993 := hb (x 10 13)
        have b24994 := hb (x 9 1 && x 9 14)
        clear * - r24991 b24992 b24993 b24994 d24986 d24944
        omega
      have d24995 : (x 10 1).toNat = 1 := by
        have r24996 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
        have b24997 := hb (x 10 1)
        have b24998 := hb (x 10 13)
        clear * - r24996 b24997 b24998 d24990
        omega
      have d24999 : (x 11 14).toNat = 0 := by
        have r25000 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
        have b25001 := hb (x 10 1)
        have b25002 := hb (x 11 14)
        clear * - r25000 b25001 b25002 d24995
        omega
      have d25003 : (x 11 1 && x 11 14).toNat = 0 := by
        have r25004 := hand2 (x 11 1) (x 11 14)
        have b25005 := hb (x 11 14)
        have b25006 := hb (x 11 1 && x 11 14)
        clear * - r25004 b25005 b25006 d24999
        omega
      have d25007 : (x 11 2).toNat = 0 := by
        have r25008 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
        have b25009 := hb (x 11 2)
        have b25010 := hb (x 11 14)
        clear * - r25008 b25009 b25010 d24999
        omega
      have d25011 : (x 9 2).toNat = 0 := by
        have r25012 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b25013 := hb (x 9 2)
        have b25014 := hb (x 9 14)
        clear * - r25012 b25013 b25014 d24982
        omega
      have d25015 : (x 7 2).toNat = 0 := by
        have r25016 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b25017 := hb (x 7 2)
        have b25018 := hb (x 7 14)
        clear * - r25016 b25017 b25018 d24965
        omega
      have d25019 : (x 9 13).toNat = 1 := by
        have r25020 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
        have b25021 := hb (x 7 2)
        have b25022 := hb (x 9 13)
        have b25023 := hb (x 8 1 && x 8 14)
        clear * - r25020 b25021 b25022 b25023 d24940 d25015
        omega
      have d25024 : (x 9 1).toNat = 1 := by
        have r25025 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b25026 := hb (x 9 1)
        have b25027 := hb (x 9 13)
        clear * - r25025 b25026 b25027 d25019
        omega
      have d25028 : (x 10 14).toNat = 0 := by
        have r25029 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
        have b25030 := hb (x 9 1)
        have b25031 := hb (x 10 14)
        clear * - r25029 b25030 b25031 d25024
        omega
      have d25032 : (x 10 1 && x 10 14).toNat = 0 := by
        have r25033 := hand2 (x 10 1) (x 10 14)
        have b25034 := hb (x 10 14)
        have b25035 := hb (x 10 1 && x 10 14)
        clear * - r25033 b25034 b25035 d25028
        omega
      have d25036 : (x 11 13).toNat = 1 := by
        have r25037 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
        have b25038 := hb (x 9 2)
        have b25039 := hb (x 11 13)
        have b25040 := hb (x 10 1 && x 10 14)
        clear * - r25037 b25038 b25039 b25040 d25032 d25011
        omega
      have d25041 : (x 11 1).toNat = 1 := by
        have r25042 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
        have b25043 := hb (x 11 1)
        have b25044 := hb (x 11 13)
        clear * - r25042 b25043 b25044 d25036
        omega
      have d25045 : (x 12 14).toNat = 0 := by
        have r25046 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
        have b25047 := hb (x 11 1)
        have b25048 := hb (x 12 14)
        clear * - r25046 b25047 b25048 d25041
        omega
      have d25049 : (x 12 1 && x 12 14).toNat = 0 := by
        have r25050 := hand2 (x 12 1) (x 12 14)
        have b25051 := hb (x 12 14)
        have b25052 := hb (x 12 1 && x 12 14)
        clear * - r25050 b25051 b25052 d25045
        omega
      have d25053 : (x 13 13).toNat = 1 := by
        have r25054 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
        have b25055 := hb (x 11 2)
        have b25056 := hb (x 13 13)
        have b25057 := hb (x 12 1 && x 12 14)
        clear * - r25054 b25055 b25056 b25057 d25049 d25007
        omega
      have d25058 : (x 13 1).toNat = 1 := by
        have r25059 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
        have b25060 := hb (x 13 1)
        have b25061 := hb (x 13 13)
        clear * - r25059 b25060 b25061 d25053
        omega
      have d25062 : (x 14 14).toNat = 0 := by
        have r25063 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
        have b25064 := hb (x 13 1)
        have b25065 := hb (x 14 14)
        clear * - r25063 b25064 b25065 d25058
        omega
      have d25066 : (x 14 1 && x 14 14).toNat = 0 := by
        have r25067 := hand2 (x 14 1) (x 14 14)
        have b25068 := hb (x 14 14)
        have b25069 := hb (x 14 1 && x 14 14)
        clear * - r25067 b25068 b25069 d25062
        omega
      have d25070 : (x 14 3 && x 14 14).toNat = 0 := by
        have r25071 := hand2 (x 14 3) (x 14 14)
        have b25072 := hb (x 14 14)
        have b25073 := hb (x 14 3 && x 14 14)
        clear * - r25071 b25072 b25073 d25062
        omega
      have d25074 : (x 14 2).toNat = 0 := by
        have r25075 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
        have b25076 := hb (x 14 2)
        have b25077 := hb (x 14 14)
        clear * - r25075 b25076 b25077 d25062
        omega
      have d25078 : (x 12 2).toNat = 0 := by
        have r25079 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
        have b25080 := hb (x 12 2)
        have b25081 := hb (x 12 14)
        clear * - r25079 b25080 b25081 d25045
        omega
      have d25082 : (x 10 2).toNat = 0 := by
        have r25083 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
        have b25084 := hb (x 10 2)
        have b25085 := hb (x 10 14)
        clear * - r25083 b25084 b25085 d25028
        omega
      have d25086 : (x 12 13).toNat = 1 := by
        have r25087 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
        have b25088 := hb (x 10 2)
        have b25089 := hb (x 12 13)
        have b25090 := hb (x 11 1 && x 11 14)
        clear * - r25087 b25088 b25089 b25090 d25003 d25082
        omega
      have d25091 : (x 12 1).toNat = 1 := by
        have r25092 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b25093 := hb (x 12 1)
        have b25094 := hb (x 12 13)
        clear * - r25092 b25093 b25094 d25086
        omega
      have d25095 : (x 13 14).toNat = 0 := by
        have r25096 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
        have b25097 := hb (x 12 1)
        have b25098 := hb (x 13 14)
        clear * - r25096 b25097 b25098 d25091
        omega
      have d25099 : (x 13 1 && x 13 14).toNat = 0 := by
        have r25100 := hand2 (x 13 1) (x 13 14)
        have b25101 := hb (x 13 14)
        have b25102 := hb (x 13 1 && x 13 14)
        clear * - r25100 b25101 b25102 d25095
        omega
      have d25103 : (x 14 13).toNat = 1 := by
        have r25104 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
        have b25105 := hb (x 12 2)
        have b25106 := hb (x 14 13)
        have b25107 := hb (x 13 1 && x 13 14)
        clear * - r25104 b25105 b25106 b25107 d25099 d25078
        omega
      have d25108 : (x 14 1).toNat = 1 := by
        have r25109 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
        have b25110 := hb (x 14 1)
        have b25111 := hb (x 14 13)
        clear * - r25109 b25110 b25111 d25103
        omega
      have d25112 : (x 15 14).toNat = 0 := by
        have r25113 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
        have b25114 := hb (x 14 1)
        have b25115 := hb (x 15 14)
        clear * - r25113 b25114 b25115 d25108
        omega
      have d25116 : (x 15 1 && x 15 14).toNat = 0 := by
        have r25117 := hand2 (x 15 1) (x 15 14)
        have b25118 := hb (x 15 14)
        have b25119 := hb (x 15 1 && x 15 14)
        clear * - r25117 b25118 b25119 d25112
        omega
      have d25120 : (x 16 13).toNat = 1 := by
        have r25121 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
        have b25122 := hb (x 14 2)
        have b25123 := hb (x 16 13)
        have b25124 := hb (x 15 1 && x 15 14)
        clear * - r25121 b25122 b25123 b25124 d25116 d25074
        omega
      have d25125 : (x 16 1).toNat = 1 := by
        have r25126 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
        have b25127 := hb (x 16 1)
        have b25128 := hb (x 16 13)
        clear * - r25126 b25127 b25128 d25120
        omega
      have d25129 : (x 17 14).toNat = 0 := by
        have r25130 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
        have b25131 := hb (x 16 1)
        have b25132 := hb (x 17 14)
        clear * - r25130 b25131 b25132 d25125
        omega
      have d25133 : (x 17 2).toNat = 0 := by
        have r25134 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
        have b25135 := hb (x 17 2)
        have b25136 := hb (x 17 14)
        clear * - r25134 b25135 b25136 d25129
        omega
      have d25137 : (x 15 2).toNat = 0 := by
        have r25138 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b25139 := hb (x 15 2)
        have b25140 := hb (x 15 14)
        clear * - r25138 b25139 b25140 d25112
        omega
      have d25141 : (x 15 2 && x 15 13).toNat = 0 := by
        have r25142 := hand1 (x 15 2) (x 15 13)
        have b25143 := hb (x 15 2)
        have b25144 := hb (x 15 2 && x 15 13)
        clear * - r25142 b25143 b25144 d25137
        omega
      have d25145 : (x 13 2).toNat = 0 := by
        have r25146 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
        have b25147 := hb (x 13 2)
        have b25148 := hb (x 13 14)
        clear * - r25146 b25147 b25148 d25095
        omega
      have d25149 : (x 15 13).toNat = 1 := by
        have r25150 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
        have b25151 := hb (x 13 2)
        have b25152 := hb (x 15 13)
        have b25153 := hb (x 14 1 && x 14 14)
        clear * - r25150 b25151 b25152 b25153 d25066 d25145
        omega
      have d25154 : (x 15 1).toNat = 1 := by
        have r25155 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
        have b25156 := hb (x 15 1)
        have b25157 := hb (x 15 13)
        clear * - r25155 b25156 b25157 d25149
        omega
      have d25158 : (x 16 14).toNat = 0 := by
        have r25159 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
        have b25160 := hb (x 15 1)
        have b25161 := hb (x 16 14)
        clear * - r25159 b25160 b25161 d25154
        omega
      have d25162 : (x 16 1 && x 16 14).toNat = 0 := by
        have r25163 := hand2 (x 16 1) (x 16 14)
        have b25164 := hb (x 16 14)
        have b25165 := hb (x 16 1 && x 16 14)
        clear * - r25163 b25164 b25165 d25158
        omega
      have d25166 : (x 17 13).toNat = 1 := by
        have r25167 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
        have b25168 := hb (x 15 2)
        have b25169 := hb (x 17 13)
        have b25170 := hb (x 16 1 && x 16 14)
        clear * - r25167 b25168 b25169 b25170 d25162 d25137
        omega
      have d25171 : (x 17 1).toNat = 1 := by
        have r25172 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
        have b25173 := hb (x 17 1)
        have b25174 := hb (x 17 13)
        clear * - r25172 b25173 b25174 d25166
        omega
      have d25175 : (x 18 14).toNat = 0 := by
        have r25176 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
        have b25177 := hb (x 17 1)
        have b25178 := hb (x 18 14)
        clear * - r25176 b25177 b25178 d25171
        omega
      have d25179 : (x 18 1 && x 18 14).toNat = 0 := by
        have r25180 := hand2 (x 18 1) (x 18 14)
        have b25181 := hb (x 18 14)
        have b25182 := hb (x 18 1 && x 18 14)
        clear * - r25180 b25181 b25182 d25175
        omega
      have d25183 : (x 19 13).toNat = 1 := by
        have r25184 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
        have b25185 := hb (x 17 2)
        have b25186 := hb (x 19 13)
        have b25187 := hb (x 18 1 && x 18 14)
        clear * - r25184 b25185 b25186 b25187 d25179 d25133
        omega
      have d25188 : (x 18 2).toNat = 0 := by
        have r25189 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
        have b25190 := hb (x 18 2)
        have b25191 := hb (x 18 14)
        clear * - r25189 b25190 b25191 d25175
        omega
      have d25192 : (x 20 12).toNat = 0 := by
        have r25193 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e25194 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e25195 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b25196 := hb (x 17 3)
        have b25197 := hb (x 18 2)
        have b25198 := hb (x 19 13)
        have b25199 := hb (x 20 12)
        clear * - r25193 e25194 e25195 b25196 b25197 b25198 b25199 d25183 d25188
        omega
      have d25200 : (x 17 3).toNat = 0 := by
        have r25201 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
        have e25202 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e25203 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b25204 := hb (x 17 3)
        have b25205 := hb (x 18 2)
        have b25206 := hb (x 19 13)
        have b25207 := hb (x 20 12)
        clear * - r25201 e25202 e25203 b25204 b25205 b25206 b25207 d25192 d25183 d25188
        omega
      have d25208 : (x 17 11).toNat = 0 := by
        have r25209 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b25210 := hb (x 17 3)
        have b25211 := hb (x 17 11)
        clear * - r25209 b25210 b25211 d25200
        omega
      have d25212 : (x 16 12).toNat = 0 := by
        have r25213 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
        have e25214 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e25215 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b25216 := hb (x 13 3)
        have b25217 := hb (x 14 2)
        have b25218 := hb (x 15 13)
        have b25219 := hb (x 16 12)
        clear * - r25213 e25214 e25215 b25216 b25217 b25218 b25219 d25149 d25074
        omega
      have d25220 : (x 16 1 && x 16 12).toNat = 0 := by
        have r25221 := hand2 (x 16 1) (x 16 12)
        have b25222 := hb (x 16 12)
        have b25223 := hb (x 16 1 && x 16 12)
        clear * - r25221 b25222 b25223 d25212
        omega
      have d25224 : (x 13 12).toNat = 0 := by
        have r25225 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
        have e25226 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e25227 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b25228 := hb (x 10 3)
        have b25229 := hb (x 11 2)
        have b25230 := hb (x 12 13)
        have b25231 := hb (x 13 12)
        clear * - r25225 e25226 e25227 b25228 b25229 b25230 b25231 d25086 d25007
        omega
      have d25232 : (x 13 4).toNat = 0 := by
        have r25233 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b25234 := hb (x 13 4)
        have b25235 := hb (x 13 12)
        clear * - r25233 b25234 b25235 d25224
        omega
      have r25236 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
      have b25237 := hb (x 13 4)
      have b25238 := hb (x 17 11)
      have b25239 := hb (x 16 1 && x 16 12)
      have b25240 := hb (x 15 2 && x 15 13)
      have b25241 := hb (x 14 3 && x 14 14)
      linarith only [r25236, b25237, b25238, b25239, b25240, b25241, d25208, d25220, d25141, d25070, d25232]
  · have f25242 : (x 0 9).toNat = 1 := by rw [h21724]; rfl
    have d25243 : (x 1 8).toNat = 0 := by
      have r25244 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
      have e25245 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e25246 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e25247 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e25248 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e25249 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e25250 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b25251 := hb (x (-6) 7)
      have b25252 := hb (x (-5) 6)
      have b25253 := hb (x (-4) 5)
      have b25254 := hb (x (-3) 4)
      have b25255 := hb (x (-2) 11)
      have b25256 := hb (x (-1) 10)
      have b25257 := hb (x 0 9)
      have b25258 := hb (x 1 8)
      clear * - r25244 e25245 e25246 e25247 e25248 e25249 e25250 b25251 b25252 b25253 b25254 b25255 b25256 b25257 b25258 f25242
      omega
    have d25259 : (x (-1) 10).toNat = 0 := by
      have r25260 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
      have e25261 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e25262 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e25263 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e25264 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e25265 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e25266 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b25267 := hb (x (-6) 7)
      have b25268 := hb (x (-5) 6)
      have b25269 := hb (x (-4) 5)
      have b25270 := hb (x (-3) 4)
      have b25271 := hb (x (-2) 11)
      have b25272 := hb (x (-1) 10)
      have b25273 := hb (x 0 9)
      have b25274 := hb (x 1 8)
      clear * - r25260 e25261 e25262 e25263 e25264 e25265 e25266 b25267 b25268 b25269 b25270 b25271 b25272 b25273 b25274 d25243 f25242
      omega
    have d25275 : (x (-2) 11).toNat = 0 := by
      have r25276 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
      have e25277 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e25278 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e25279 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e25280 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e25281 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e25282 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b25283 := hb (x (-6) 7)
      have b25284 := hb (x (-5) 6)
      have b25285 := hb (x (-4) 5)
      have b25286 := hb (x (-3) 4)
      have b25287 := hb (x (-2) 11)
      have b25288 := hb (x (-1) 10)
      have b25289 := hb (x 0 9)
      have b25290 := hb (x 1 8)
      clear * - r25276 e25277 e25278 e25279 e25280 e25281 e25282 b25283 b25284 b25285 b25286 b25287 b25288 b25289 b25290 d25243 f25242 d25259
      omega
    have d25291 : (x (-3) 4).toNat = 0 := by
      have r25292 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
      have e25293 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e25294 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e25295 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e25296 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e25297 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e25298 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b25299 := hb (x (-6) 7)
      have b25300 := hb (x (-5) 6)
      have b25301 := hb (x (-4) 5)
      have b25302 := hb (x (-3) 4)
      have b25303 := hb (x (-2) 11)
      have b25304 := hb (x (-1) 10)
      have b25305 := hb (x 0 9)
      have b25306 := hb (x 1 8)
      clear * - r25292 e25293 e25294 e25295 e25296 e25297 e25298 b25299 b25300 b25301 b25302 b25303 b25304 b25305 b25306 d25243 f25242 d25259 d25275
      omega
    have d25307 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
      have r25308 := hand1 (x (-3) 4) (x (-3) 14)
      have b25309 := hb (x (-3) 4)
      have b25310 := hb (x (-3) 4 && x (-3) 14)
      clear * - r25308 b25309 b25310 d25291
      omega
    have d25311 : (x (-3) 4 && x (-3) 13).toNat = 0 := by
      have r25312 := hand1 (x (-3) 4) (x (-3) 13)
      have b25313 := hb (x (-3) 4)
      have b25314 := hb (x (-3) 4 && x (-3) 13)
      clear * - r25312 b25313 b25314 d25291
      omega
    have d25315 : (x (-4) 5).toNat = 0 := by
      have r25316 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
      have e25317 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e25318 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e25319 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e25320 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e25321 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e25322 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b25323 := hb (x (-6) 7)
      have b25324 := hb (x (-5) 6)
      have b25325 := hb (x (-4) 5)
      have b25326 := hb (x (-3) 4)
      have b25327 := hb (x (-2) 11)
      have b25328 := hb (x (-1) 10)
      have b25329 := hb (x 0 9)
      have b25330 := hb (x 1 8)
      clear * - r25316 e25317 e25318 e25319 e25320 e25321 e25322 b25323 b25324 b25325 b25326 b25327 b25328 b25329 b25330 d25243 f25242 d25259 d25275 d25291
      omega
    have d25331 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
      have r25332 := hand1 (x (-4) 5) (x (-4) 14)
      have b25333 := hb (x (-4) 5)
      have b25334 := hb (x (-4) 5 && x (-4) 14)
      clear * - r25332 b25333 b25334 d25315
      omega
    have d25335 : (x (-1) 2 && x (-1) 12).toNat = 1 := by
      have r25336 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := hcov10 1
      have b25337 := hb (x (-4) 5)
      have b25338 := hb (x 1 10)
      have b25339 := hb (x 0 1 && x 0 11)
      have b25340 := hb (x (-1) 2 && x (-1) 12)
      have b25341 := hb (x (-2) 3 && x (-2) 13)
      have b25342 := hb (x (-3) 4 && x (-3) 14)
      clear * - r25336 b25337 b25338 b25339 b25340 b25341 b25342 g16 g47 d21668 d25307 d25315
      omega
    have d25343 : (x (-1) 2).toNat = 1 := by
      have r25344 := hand1 (x (-1) 2) (x (-1) 12)
      have b25345 := hb (x (-1) 2)
      have b25346 := hb (x (-1) 2 && x (-1) 12)
      clear * - r25344 b25345 b25346 d25335
      omega
    have d25347 : (x 1 12).toNat = 0 := by
      have r25348 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
      have e25349 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e25350 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b25351 := hb (x (-2) 3)
      have b25352 := hb (x (-1) 2)
      have b25353 := hb (x 0 13)
      have b25354 := hb (x 1 12)
      clear * - r25348 e25349 e25350 b25351 b25352 b25353 b25354 g12 d25343
      omega
    have d25355 : (x (-2) 3).toNat = 0 := by
      have r25356 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
      have e25357 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e25358 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b25359 := hb (x (-2) 3)
      have b25360 := hb (x (-1) 2)
      have b25361 := hb (x 0 13)
      have b25362 := hb (x 1 12)
      clear * - r25356 e25357 e25358 b25359 b25360 b25361 b25362 d25347 g12 d25343
      omega
    have d25363 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
      have r25364 := hand1 (x (-2) 3) (x (-2) 12)
      have b25365 := hb (x (-2) 3)
      have b25366 := hb (x (-2) 3 && x (-2) 12)
      clear * - r25364 b25365 b25366 d25355
      omega
    have d25367 : (x (-5) 6).toNat = 0 := by
      have r25368 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
      have e25369 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e25370 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e25371 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e25372 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e25373 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e25374 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b25375 := hb (x (-6) 7)
      have b25376 := hb (x (-5) 6)
      have b25377 := hb (x (-4) 5)
      have b25378 := hb (x (-3) 4)
      have b25379 := hb (x (-2) 11)
      have b25380 := hb (x (-1) 10)
      have b25381 := hb (x 0 9)
      have b25382 := hb (x 1 8)
      clear * - r25368 e25369 e25370 e25371 e25372 e25373 e25374 b25375 b25376 b25377 b25378 b25379 b25380 b25381 b25382 d25243 f25242 d25259 d25275 d25291 d25315
      omega
    have d25383 : (x 1 9).toNat = 1 := by
      have r25384 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
      have b25385 := hb (x (-5) 6)
      have b25386 := hb (x 1 9)
      have b25387 := hb (x 0 1 && x 0 10)
      have b25388 := hb (x (-1) 2 && x (-1) 11)
      have b25389 := hb (x (-2) 3 && x (-2) 12)
      have b25390 := hb (x (-3) 4 && x (-3) 13)
      have b25391 := hb (x (-4) 5 && x (-4) 14)
      clear * - r25384 b25385 b25386 b25387 b25388 b25389 b25390 b25391 g38 g39 d25363 d25311 d25331 d25367
      omega
    have d25392 : (x 1 1).toNat = 1 := by
      have r25393 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b25394 := hb (x 1 1)
      have b25395 := hb (x 1 9)
      clear * - r25393 b25394 b25395 d25383
      omega
    have d25396 : (x 2 14).toNat = 0 := by
      have r25397 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
      have b25398 := hb (x 1 1)
      have b25399 := hb (x 2 14)
      clear * - r25397 b25398 b25399 d25392
      omega
    have d25400 : (x 2 1 && x 2 14).toNat = 0 := by
      have r25401 := hand2 (x 2 1) (x 2 14)
      have b25402 := hb (x 2 14)
      have b25403 := hb (x 2 1 && x 2 14)
      clear * - r25401 b25402 b25403 d25396
      omega
    have d25404 : (x 3 13).toNat = 1 := by
      have r25405 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
      have b25406 := hb (x 1 2)
      have b25407 := hb (x 3 13)
      have b25408 := hb (x 2 1 && x 2 14)
      clear * - r25405 b25406 b25407 b25408 d25400 g14
      omega
    have d25409 : (x 3 1).toNat = 1 := by
      have r25410 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b25411 := hb (x 3 1)
      have b25412 := hb (x 3 13)
      clear * - r25410 b25411 b25412 d25404
      omega
    have d25413 : (x 4 14).toNat = 0 := by
      have r25414 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
      have b25415 := hb (x 3 1)
      have b25416 := hb (x 4 14)
      clear * - r25414 b25415 b25416 d25409
      omega
    have d25417 : (x 4 1 && x 4 14).toNat = 0 := by
      have r25418 := hand2 (x 4 1) (x 4 14)
      have b25419 := hb (x 4 14)
      have b25420 := hb (x 4 1 && x 4 14)
      clear * - r25418 b25419 b25420 d25413
      omega
    have d25421 : (x 5 13).toNat = 1 := by
      have r25422 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
      have b25423 := hb (x 3 2)
      have b25424 := hb (x 5 13)
      have b25425 := hb (x 4 1 && x 4 14)
      clear * - r25422 b25423 b25424 b25425 d25417 g17
      omega
    have d25426 : (x 5 1).toNat = 1 := by
      have r25427 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
      have b25428 := hb (x 5 1)
      have b25429 := hb (x 5 13)
      clear * - r25427 b25428 b25429 d25421
      omega
    have d25430 : (x 6 14).toNat = 0 := by
      have r25431 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
      have b25432 := hb (x 5 1)
      have b25433 := hb (x 6 14)
      clear * - r25431 b25432 b25433 d25426
      omega
    have d25434 : (x 6 1 && x 6 14).toNat = 0 := by
      have r25435 := hand2 (x 6 1) (x 6 14)
      have b25436 := hb (x 6 14)
      have b25437 := hb (x 6 1 && x 6 14)
      clear * - r25435 b25436 b25437 d25430
      omega
    have d25438 : (x 6 2).toNat = 0 := by
      have r25439 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b25440 := hb (x 6 2)
      have b25441 := hb (x 6 14)
      clear * - r25439 b25440 b25441 d25430
      omega
    have d25442 : (x 6 2 && x 6 13).toNat = 0 := by
      have r25443 := hand1 (x 6 2) (x 6 13)
      have b25444 := hb (x 6 2)
      have b25445 := hb (x 6 2 && x 6 13)
      clear * - r25443 b25444 b25445 d25438
      omega
    have d25446 : (x 6 12).toNat = 0 := by
      have r25447 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e25448 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e25449 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b25450 := hb (x 3 3)
      have b25451 := hb (x 4 2)
      have b25452 := hb (x 5 13)
      have b25453 := hb (x 6 12)
      clear * - r25447 e25448 e25449 b25450 b25451 b25452 b25453 d25421
      omega
    have d25454 : (x 6 1 && x 6 12).toNat = 0 := by
      have r25455 := hand2 (x 6 1) (x 6 12)
      have b25456 := hb (x 6 12)
      have b25457 := hb (x 6 1 && x 6 12)
      clear * - r25455 b25456 b25457 d25446
      omega
    have d25458 : (x 4 2).toNat = 0 := by
      have r25459 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e25460 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e25461 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b25462 := hb (x 3 3)
      have b25463 := hb (x 4 2)
      have b25464 := hb (x 5 13)
      have b25465 := hb (x 6 12)
      clear * - r25459 e25460 e25461 b25462 b25463 b25464 b25465 d25446 d25421
      omega
    have d25466 : (x 4 3 && x 4 14).toNat = 0 := by
      have r25467 := hand2 (x 4 3) (x 4 14)
      have b25468 := hb (x 4 14)
      have b25469 := hb (x 4 3 && x 4 14)
      clear * - r25467 b25468 b25469 d25413
      omega
    have d25470 : (x 4 12).toNat = 0 := by
      have r25471 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e25472 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e25473 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b25474 := hb (x 1 3)
      have b25475 := hb (x 2 2)
      have b25476 := hb (x 3 13)
      have b25477 := hb (x 4 12)
      clear * - r25471 e25472 e25473 b25474 b25475 b25476 b25477 d25404
      omega
    have d25478 : (x 4 4).toNat = 0 := by
      have r25479 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b25480 := hb (x 4 4)
      have b25481 := hb (x 4 12)
      clear * - r25479 b25480 b25481 d25470
      omega
    have d25482 : (x 2 2).toNat = 0 := by
      have r25483 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e25484 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e25485 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b25486 := hb (x 1 3)
      have b25487 := hb (x 2 2)
      have b25488 := hb (x 3 13)
      have b25489 := hb (x 4 12)
      clear * - r25483 e25484 e25485 b25486 b25487 b25488 b25489 d25470 d25404
      omega
    have d25490 : (x 2 2 && x 2 13).toNat = 0 := by
      have r25491 := hand1 (x 2 2) (x 2 13)
      have b25492 := hb (x 2 2)
      have b25493 := hb (x 2 2 && x 2 13)
      clear * - r25491 b25492 b25493 d25482
      omega
    have d25494 : (x 4 11).toNat = 1 := by
      have r25495 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
      have b25496 := hb (x 0 4)
      have b25497 := hb (x 4 11)
      have b25498 := hb (x 3 1 && x 3 12)
      have b25499 := hb (x 2 2 && x 2 13)
      have b25500 := hb (x 1 3 && x 1 14)
      clear * - r25495 b25496 b25497 b25498 b25499 b25500 g54 d25490 g55 g6
      omega
    have d25501 : (x 4 3).toNat = 1 := by
      have r25502 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b25503 := hb (x 4 3)
      have b25504 := hb (x 4 11)
      clear * - r25502 b25503 b25504 d25494
      omega
    have d25505 : (x 7 12).toNat = 0 := by
      have r25506 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e25507 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e25508 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b25509 := hb (x 4 3)
      have b25510 := hb (x 5 2)
      have b25511 := hb (x 6 13)
      have b25512 := hb (x 7 12)
      clear * - r25506 e25507 e25508 b25509 b25510 b25511 b25512 d25501
      omega
    have d25513 : (x 7 1 && x 7 12).toNat = 0 := by
      have r25514 := hand2 (x 7 1) (x 7 12)
      have b25515 := hb (x 7 12)
      have b25516 := hb (x 7 1 && x 7 12)
      clear * - r25514 b25515 b25516 d25505
      omega
    have d25517 : (x 7 2 && x 7 12).toNat = 0 := by
      have r25518 := hand2 (x 7 2) (x 7 12)
      have b25519 := hb (x 7 12)
      have b25520 := hb (x 7 2 && x 7 12)
      clear * - r25518 b25519 b25520 d25505
      omega
    have d25521 : (x 6 13).toNat = 0 := by
      have r25522 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e25523 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e25524 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b25525 := hb (x 4 3)
      have b25526 := hb (x 5 2)
      have b25527 := hb (x 6 13)
      have b25528 := hb (x 7 12)
      clear * - r25522 e25523 e25524 b25525 b25526 b25527 b25528 d25505 d25501
      omega
    have d25529 : (x 6 3 && x 6 13).toNat = 0 := by
      have r25530 := hand2 (x 6 3) (x 6 13)
      have b25531 := hb (x 6 13)
      have b25532 := hb (x 6 3 && x 6 13)
      clear * - r25530 b25531 b25532 d25521
      omega
    have d25533 : (x 5 1 && x 5 14).toNat = 1 := by
      have r25534 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
      have b25535 := hb (x 4 2)
      have b25536 := hb (x 6 13)
      have b25537 := hb (x 5 1 && x 5 14)
      clear * - r25534 b25535 b25536 b25537 d25521 d25458
      omega
    have d25538 : (x 5 14).toNat = 1 := by
      have r25539 := hand2 (x 5 1) (x 5 14)
      have b25540 := hb (x 5 14)
      have b25541 := hb (x 5 1 && x 5 14)
      clear * - r25539 b25540 b25541 d25533
      omega
    have d25542 : (x 4 1).toNat = 0 := by
      have r25543 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
      have b25544 := hb (x 4 1)
      have b25545 := hb (x 5 14)
      clear * - r25543 b25544 b25545 d25538
      omega
    have d25546 : (x 4 1 && x 4 11).toNat = 0 := by
      have r25547 := hand1 (x 4 1) (x 4 11)
      have b25548 := hb (x 4 1)
      have b25549 := hb (x 4 1 && x 4 11)
      clear * - r25547 b25548 b25549 d25542
      omega
    have d25550 : (x 4 13).toNat = 0 := by
      have r25551 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b25552 := hb (x 4 1)
      have b25553 := hb (x 4 13)
      clear * - r25551 b25552 b25553 d25542
      omega
    have d25554 : (x 4 5).toNat = 0 := by
      have r25555 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
      have b25556 := hb (x 4 5)
      have b25557 := hb (x 4 13)
      clear * - r25555 b25556 b25557 d25550
      omega
    have d25558 : (x 5 2).toNat = 0 := by
      have r25559 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e25560 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e25561 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b25562 := hb (x 4 3)
      have b25563 := hb (x 5 2)
      have b25564 := hb (x 6 13)
      have b25565 := hb (x 7 12)
      clear * - r25559 e25560 e25561 b25562 b25563 b25564 b25565 d25505 d25521 d25501
      omega
    have d25566 : (x 5 2 && x 5 13).toNat = 0 := by
      have r25567 := hand1 (x 5 2) (x 5 13)
      have b25568 := hb (x 5 2)
      have b25569 := hb (x 5 2 && x 5 13)
      clear * - r25567 b25568 b25569 d25558
      omega
    have d25570 : (x 7 11).toNat = 1 := by
      have r25571 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
      have b25572 := hb (x 3 4)
      have b25573 := hb (x 7 11)
      have b25574 := hb (x 6 1 && x 6 12)
      have b25575 := hb (x 5 2 && x 5 13)
      have b25576 := hb (x 4 3 && x 4 14)
      clear * - r25571 b25572 b25573 b25574 b25575 b25576 d25454 d25566 d25466 g18
      omega
    have d25577 : (x 7 3).toNat = 1 := by
      have r25578 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b25579 := hb (x 7 3)
      have b25580 := hb (x 7 11)
      clear * - r25578 b25579 b25580 d25570
      omega
    have d25581 : (x 10 12).toNat = 0 := by
      have r25582 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e25583 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e25584 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b25585 := hb (x 7 3)
      have b25586 := hb (x 8 2)
      have b25587 := hb (x 9 13)
      have b25588 := hb (x 10 12)
      clear * - r25582 e25583 e25584 b25585 b25586 b25587 b25588 d25577
      omega
    have d25589 : (x 9 13).toNat = 0 := by
      have r25590 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e25591 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e25592 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b25593 := hb (x 7 3)
      have b25594 := hb (x 8 2)
      have b25595 := hb (x 9 13)
      have b25596 := hb (x 10 12)
      clear * - r25590 e25591 e25592 b25593 b25594 b25595 b25596 d25581 d25577
      omega
    have d25597 : (x 8 2).toNat = 0 := by
      have r25598 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e25599 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e25600 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b25601 := hb (x 7 3)
      have b25602 := hb (x 8 2)
      have b25603 := hb (x 9 13)
      have b25604 := hb (x 10 12)
      clear * - r25598 e25599 e25600 b25601 b25602 b25603 b25604 d25581 d25589 d25577
      omega
    have d25605 : (x 5 10).toNat = 0 := by
      have r25606 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
      have b25607 := hb (x 5 2)
      have b25608 := hb (x 5 10)
      clear * - r25606 b25607 b25608 d25558
      omega
    have d25609 : (x 2 3 && x 2 13).toNat = 1 := by
      have r25610 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
      have b25611 := hb (x 0 5)
      have b25612 := hb (x 5 10)
      have b25613 := hb (x 4 1 && x 4 11)
      have b25614 := hb (x 3 2 && x 3 12)
      have b25615 := hb (x 2 3 && x 2 13)
      have b25616 := hb (x 1 4 && x 1 14)
      clear * - r25610 b25611 b25612 b25613 b25614 b25615 b25616 d25605 d25546 g52 g53 g7
      omega
    have d25617 : (x 2 3).toNat = 1 := by
      have r25618 := hand1 (x 2 3) (x 2 13)
      have b25619 := hb (x 2 3)
      have b25620 := hb (x 2 3 && x 2 13)
      clear * - r25618 b25619 b25620 d25609
      omega
    have d25621 : (x 5 12).toNat = 0 := by
      have r25622 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
      have e25623 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e25624 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b25625 := hb (x 2 3)
      have b25626 := hb (x 3 2)
      have b25627 := hb (x 4 13)
      have b25628 := hb (x 5 12)
      clear * - r25622 e25623 e25624 b25625 b25626 b25627 b25628 d25550 g17 d25617
      omega
    have d25629 : (x 5 4).toNat = 0 := by
      have r25630 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b25631 := hb (x 5 4)
      have b25632 := hb (x 5 12)
      clear * - r25630 b25631 b25632 d25621
      omega
    have d25633 : (x 5 4 && x 5 14).toNat = 0 := by
      have r25634 := hand1 (x 5 4) (x 5 14)
      have b25635 := hb (x 5 4)
      have b25636 := hb (x 5 4 && x 5 14)
      clear * - r25634 b25635 b25636 d25629
      omega
    have d25637 : (x 7 13).toNat = 1 := by
      have r25638 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
      have b25639 := hb (x 5 2)
      have b25640 := hb (x 7 13)
      have b25641 := hb (x 6 1 && x 6 14)
      clear * - r25638 b25639 b25640 b25641 d25434 d25558
      omega
    have d25642 : (x 8 12).toNat = 0 := by
      have r25643 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
      have e25644 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e25645 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b25646 := hb (x 5 3)
      have b25647 := hb (x 6 2)
      have b25648 := hb (x 7 13)
      have b25649 := hb (x 8 12)
      clear * - r25643 e25644 e25645 b25646 b25647 b25648 b25649 d25637 d25438
      omega
    have d25650 : (x 5 3).toNat = 0 := by
      have r25651 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
      have e25652 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e25653 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b25654 := hb (x 5 3)
      have b25655 := hb (x 6 2)
      have b25656 := hb (x 7 13)
      have b25657 := hb (x 8 12)
      clear * - r25651 e25652 e25653 b25654 b25655 b25656 b25657 d25642 d25637 d25438
      omega
    have d25658 : (x 5 3 && x 5 14).toNat = 0 := by
      have r25659 := hand1 (x 5 3) (x 5 14)
      have b25660 := hb (x 5 3)
      have b25661 := hb (x 5 3 && x 5 14)
      clear * - r25659 b25660 b25661 d25650
      omega
    have d25662 : (x 8 11).toNat = 1 := by
      have r25663 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
      have b25664 := hb (x 4 4)
      have b25665 := hb (x 8 11)
      have b25666 := hb (x 7 1 && x 7 12)
      have b25667 := hb (x 6 2 && x 6 13)
      have b25668 := hb (x 5 3 && x 5 14)
      clear * - r25663 b25664 b25665 b25666 b25667 b25668 d25513 d25442 d25658 d25478
      omega
    have d25669 : (x 8 3).toNat = 1 := by
      have r25670 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b25671 := hb (x 8 3)
      have b25672 := hb (x 8 11)
      clear * - r25670 b25671 b25672 d25662
      omega
    have d25673 : (x 11 12).toNat = 0 := by
      have r25674 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
      have e25675 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e25676 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b25677 := hb (x 8 3)
      have b25678 := hb (x 9 2)
      have b25679 := hb (x 10 13)
      have b25680 := hb (x 11 12)
      clear * - r25674 e25675 e25676 b25677 b25678 b25679 b25680 d25669
      omega
    have d25681 : (x 10 13).toNat = 0 := by
      have r25682 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
      have e25683 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e25684 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b25685 := hb (x 8 3)
      have b25686 := hb (x 9 2)
      have b25687 := hb (x 10 13)
      have b25688 := hb (x 11 12)
      clear * - r25682 e25683 e25684 b25685 b25686 b25687 b25688 d25673 d25669
      omega
    have d25689 : (x 9 1 && x 9 14).toNat = 1 := by
      have r25690 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
      have b25691 := hb (x 8 2)
      have b25692 := hb (x 10 13)
      have b25693 := hb (x 9 1 && x 9 14)
      clear * - r25690 b25691 b25692 b25693 d25681 d25597
      omega
    have d25694 : (x 9 14).toNat = 1 := by
      have r25695 := hand2 (x 9 1) (x 9 14)
      have b25696 := hb (x 9 14)
      have b25697 := hb (x 9 1 && x 9 14)
      clear * - r25695 b25696 b25697 d25689
      omega
    have d25698 : (x 8 1).toNat = 0 := by
      have r25699 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
      have b25700 := hb (x 8 1)
      have b25701 := hb (x 9 14)
      clear * - r25699 b25700 b25701 d25694
      omega
    have d25702 : (x 8 1 && x 8 11).toNat = 0 := by
      have r25703 := hand1 (x 8 1) (x 8 11)
      have b25704 := hb (x 8 1)
      have b25705 := hb (x 8 1 && x 8 11)
      clear * - r25703 b25704 b25705 d25698
      omega
    have d25706 : (x 9 10).toNat = 1 := by
      have r25707 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := hcov10 9
      have b25708 := hb (x 4 5)
      have b25709 := hb (x 9 10)
      have b25710 := hb (x 8 1 && x 8 11)
      have b25711 := hb (x 7 2 && x 7 12)
      have b25712 := hb (x 6 3 && x 6 13)
      have b25713 := hb (x 5 4 && x 5 14)
      clear * - r25707 b25708 b25709 b25710 b25711 b25712 b25713 d25702 d25517 d25529 d25633 d25554
      omega
    have d25714 : (x 9 2).toNat = 1 := by
      have r25715 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
      have b25716 := hb (x 9 2)
      have b25717 := hb (x 9 10)
      clear * - r25715 b25716 b25717 d25706
      omega
    have r25718 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e25719 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e25720 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b25721 := hb (x 8 3)
    have b25722 := hb (x 9 2)
    have b25723 := hb (x 10 13)
    have b25724 := hb (x 11 12)
    linarith only [r25718, e25719, e25720, b25721, b25722, b25723, b25724, d25673, d25681, d25714, d25669]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 1).toNat = 1)
    (g1 : (x (-1) 3).toNat = 0)
    (g2 : (x (-1) 11).toNat = 0)
    (g3 : (x (-1) 13).toNat = 1)
    (g4 : (x 0 1).toNat = 1)
    (g5 : (x 0 2).toNat = 0)
    (g6 : (x 0 4).toNat = 0)
    (g7 : (x 0 5).toNat = 0)
    (g8 : (x 0 6).toNat = 0)
    (g9 : (x 0 8).toNat = 0)
    (g10 : (x 0 10).toNat = 0)
    (g11 : (x 0 11).toNat = 0)
    (g12 : (x 0 13).toNat = 0)
    (g13 : (x 0 14).toNat = 0)
    (g14 : (x 1 2).toNat = 0)
    (g15 : (x 1 6).toNat = 0)
    (g16 : (x 1 10).toNat = 0)
    (g17 : (x 3 2).toNat = 0)
    (g18 : (x 3 4).toNat = 0)
    (g19 : (x 3 6).toNat = 0)
    (g20 : (x 3 10).toNat = 0)
    (g21 : (x 0 1 && x 0 2).toNat = 0)
    (g22 : (x (-1) 2 && x (-1) 3).toNat = 0)
    (g23 : (x 1 9 && x 1 10).toNat = 0)
    (g24 : (x 0 10 && x 0 11).toNat = 0)
    (g25 : (x (-1) 11 && x (-1) 12).toNat = 0)
    (g26 : (x (-1) 1 && x (-1) 3).toNat = 0)
    (g27 : (x 0 1 && x 0 3).toNat = 0)
    (g28 : (x 3 7 && x 3 10).toNat = 0)
    (g29 : (x 0 10 && x 0 13).toNat = 0)
    (g30 : (x (-1) 11 && x (-1) 14).toNat = 0)
    (g31 : (x 3 6 && x 3 10).toNat = 0)
    (g32 : (x 0 9 && x 0 13).toNat = 0)
    (g33 : (x 0 1 && x 0 6).toNat = 0)
    (g34 : (x 3 5 && x 3 10).toNat = 0)
    (g35 : (x 0 8 && x 0 13).toNat = 0)
    (g36 : (x 0 1 && x 0 7).toNat = 0)
    (g37 : (x 3 6 && x 3 13).toNat = 0)
    (g38 : (x 0 1 && x 0 10).toNat = 0)
    (g39 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g40 : (x 1 1 && x 1 10).toNat = 0)
    (g41 : (x 0 2 && x 0 11).toNat = 0)
    (g42 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g43 : (x 1 2 && x 1 11).toNat = 0)
    (g44 : (x 0 3 && x 0 12).toNat = 0)
    (g45 : (x 3 5 && x 3 14).toNat = 0)
    (g46 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g47 : (x 0 1 && x 0 11).toNat = 0)
    (g48 : (x 0 2 && x 0 12).toNat = 0)
    (g49 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g50 : (x 1 2 && x 1 12).toNat = 0)
    (g51 : (x 0 3 && x 0 13).toNat = 0)
    (g52 : (x 3 2 && x 3 12).toNat = 0)
    (g53 : (x 1 4 && x 1 14).toNat = 0)
    (g54 : (x 3 1 && x 3 12).toNat = 0)
    (g55 : (x 1 3 && x 1 14).toNat = 0)
    (g56 : (x 3 2 && x 3 13).toNat = 0)
    (g57 : (x 3 3 && x 3 14).toNat = 0)
    (g58 : (x 0 1 && x 0 14).toNat = 0)
    (g59 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59
