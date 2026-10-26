import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a011

Topic: combinatorics   Node: 8d5db8f8c8d5

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 5 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a011_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 1)
    (g1 : (x 1 2).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 0 1 && x 0 14).toNat = 0)
    (g4 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d48610 : (x 0 13).toNat = 1 := by
    have r48611 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
    have b48612 := hb (x 0 5)
    have b48613 := hb (x 0 13)
    clear * - r48611 b48612 b48613 g0
    omega
  have d48614 : (x 1 12).toNat = 0 := by
    have r48615 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e48616 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e48617 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b48618 := hb (x (-2) 3)
    have b48619 := hb (x (-1) 2)
    have b48620 := hb (x 0 13)
    have b48621 := hb (x 1 12)
    clear * - r48615 e48616 e48617 b48618 b48619 b48620 b48621 d48610
    omega
  have d48622 : (x (-1) 2).toNat = 0 := by
    have r48623 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e48624 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e48625 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b48626 := hb (x (-2) 3)
    have b48627 := hb (x (-1) 2)
    have b48628 := hb (x 0 13)
    have b48629 := hb (x 1 12)
    clear * - r48623 e48624 e48625 b48626 b48627 b48628 b48629 d48614 d48610
    omega
  have d48630 : (x 1 13).toNat = 1 := by
    have r48631 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
    have b48632 := hb (x (-1) 2)
    have b48633 := hb (x 1 13)
    have b48634 := hb (x 0 1 && x 0 14)
    clear * - r48631 b48632 b48633 b48634 g3 d48622
    omega
  have d48635 : (x 1 1).toNat = 1 := by
    have r48636 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b48637 := hb (x 1 1)
    have b48638 := hb (x 1 13)
    clear * - r48636 b48637 b48638 d48630
    omega
  have d48639 : (x 2 14).toNat = 0 := by
    have r48640 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
    have b48641 := hb (x 1 1)
    have b48642 := hb (x 2 14)
    clear * - r48640 b48641 b48642 d48635
    omega
  have d48643 : (x 2 1 && x 2 14).toNat = 0 := by
    have r48644 := hand2 (x 2 1) (x 2 14)
    have b48645 := hb (x 2 14)
    have b48646 := hb (x 2 1 && x 2 14)
    clear * - r48644 b48645 b48646 d48639
    omega
  have d48647 : (x 3 13).toNat = 1 := by
    have r48648 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
    have b48649 := hb (x 1 2)
    have b48650 := hb (x 3 13)
    have b48651 := hb (x 2 1 && x 2 14)
    clear * - r48648 b48649 b48650 b48651 d48643 g1
    omega
  have d48652 : (x 3 1).toNat = 1 := by
    have r48653 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b48654 := hb (x 3 1)
    have b48655 := hb (x 3 13)
    clear * - r48653 b48654 b48655 d48647
    omega
  have d48656 : (x 4 14).toNat = 0 := by
    have r48657 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
    have b48658 := hb (x 3 1)
    have b48659 := hb (x 4 14)
    clear * - r48657 b48658 b48659 d48652
    omega
  have d48660 : (x 4 1 && x 4 14).toNat = 0 := by
    have r48661 := hand2 (x 4 1) (x 4 14)
    have b48662 := hb (x 4 14)
    have b48663 := hb (x 4 1 && x 4 14)
    clear * - r48661 b48662 b48663 d48656
    omega
  have d48664 : (x 5 13).toNat = 1 := by
    have r48665 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
    have b48666 := hb (x 3 2)
    have b48667 := hb (x 5 13)
    have b48668 := hb (x 4 1 && x 4 14)
    clear * - r48665 b48666 b48667 b48668 d48660 g2
    omega
  have d48669 : (x 5 1).toNat = 1 := by
    have r48670 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b48671 := hb (x 5 1)
    have b48672 := hb (x 5 13)
    clear * - r48670 b48671 b48672 d48664
    omega
  have d48673 : (x 6 14).toNat = 0 := by
    have r48674 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
    have b48675 := hb (x 5 1)
    have b48676 := hb (x 6 14)
    clear * - r48674 b48675 b48676 d48669
    omega
  have d48677 : (x 6 1 && x 6 14).toNat = 0 := by
    have r48678 := hand2 (x 6 1) (x 6 14)
    have b48679 := hb (x 6 14)
    have b48680 := hb (x 6 1 && x 6 14)
    clear * - r48678 b48679 b48680 d48673
    omega
  have d48681 : (x 6 2).toNat = 0 := by
    have r48682 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b48683 := hb (x 6 2)
    have b48684 := hb (x 6 14)
    clear * - r48682 b48683 b48684 d48673
    omega
  have d48685 : (x 6 12).toNat = 0 := by
    have r48686 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e48687 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e48688 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b48689 := hb (x 3 3)
    have b48690 := hb (x 4 2)
    have b48691 := hb (x 5 13)
    have b48692 := hb (x 6 12)
    clear * - r48686 e48687 e48688 b48689 b48690 b48691 b48692 d48664
    omega
  have d48693 : (x 4 2).toNat = 0 := by
    have r48694 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e48695 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e48696 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b48697 := hb (x 3 3)
    have b48698 := hb (x 4 2)
    have b48699 := hb (x 5 13)
    have b48700 := hb (x 6 12)
    clear * - r48694 e48695 e48696 b48697 b48698 b48699 b48700 d48685 d48664
    omega
  have d48701 : (x 4 12).toNat = 0 := by
    have r48702 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e48703 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e48704 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b48705 := hb (x 1 3)
    have b48706 := hb (x 2 2)
    have b48707 := hb (x 3 13)
    have b48708 := hb (x 4 12)
    clear * - r48702 e48703 e48704 b48705 b48706 b48707 b48708 d48647
    omega
  have d48709 : (x 2 2).toNat = 0 := by
    have r48710 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e48711 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e48712 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b48713 := hb (x 1 3)
    have b48714 := hb (x 2 2)
    have b48715 := hb (x 3 13)
    have b48716 := hb (x 4 12)
    clear * - r48710 e48711 e48712 b48713 b48714 b48715 b48716 d48701 d48647
    omega
  have d48717 : (x 4 13).toNat = 1 := by
    have r48718 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b48719 := hb (x 2 2)
    have b48720 := hb (x 4 13)
    have b48721 := hb (x 3 1 && x 3 14)
    clear * - r48718 b48719 b48720 b48721 g4 d48709
    omega
  have d48722 : (x 4 1).toNat = 1 := by
    have r48723 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b48724 := hb (x 4 1)
    have b48725 := hb (x 4 13)
    clear * - r48723 b48724 b48725 d48717
    omega
  have d48726 : (x 5 14).toNat = 0 := by
    have r48727 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
    have b48728 := hb (x 4 1)
    have b48729 := hb (x 5 14)
    clear * - r48727 b48728 b48729 d48722
    omega
  have d48730 : (x 5 1 && x 5 14).toNat = 0 := by
    have r48731 := hand2 (x 5 1) (x 5 14)
    have b48732 := hb (x 5 14)
    have b48733 := hb (x 5 1 && x 5 14)
    clear * - r48731 b48732 b48733 d48726
    omega
  have d48734 : (x 6 13).toNat = 1 := by
    have r48735 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
    have b48736 := hb (x 4 2)
    have b48737 := hb (x 6 13)
    have b48738 := hb (x 5 1 && x 5 14)
    clear * - r48735 b48736 b48737 b48738 d48730 d48693
    omega
  have d48739 : (x 6 1).toNat = 1 := by
    have r48740 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b48741 := hb (x 6 1)
    have b48742 := hb (x 6 13)
    clear * - r48740 b48741 b48742 d48734
    omega
  have d48743 : (x 7 14).toNat = 0 := by
    have r48744 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
    have b48745 := hb (x 6 1)
    have b48746 := hb (x 7 14)
    clear * - r48744 b48745 b48746 d48739
    omega
  have d48747 : (x 7 1 && x 7 14).toNat = 0 := by
    have r48748 := hand2 (x 7 1) (x 7 14)
    have b48749 := hb (x 7 14)
    have b48750 := hb (x 7 1 && x 7 14)
    clear * - r48748 b48749 b48750 d48743
    omega
  have d48751 : (x 8 13).toNat = 1 := by
    have r48752 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
    have b48753 := hb (x 6 2)
    have b48754 := hb (x 8 13)
    have b48755 := hb (x 7 1 && x 7 14)
    clear * - r48752 b48753 b48754 b48755 d48747 d48681
    omega
  have d48756 : (x 8 1).toNat = 1 := by
    have r48757 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b48758 := hb (x 8 1)
    have b48759 := hb (x 8 13)
    clear * - r48757 b48758 b48759 d48751
    omega
  have d48760 : (x 9 14).toNat = 0 := by
    have r48761 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
    have b48762 := hb (x 8 1)
    have b48763 := hb (x 9 14)
    clear * - r48761 b48762 b48763 d48756
    omega
  have d48764 : (x 9 1 && x 9 14).toNat = 0 := by
    have r48765 := hand2 (x 9 1) (x 9 14)
    have b48766 := hb (x 9 14)
    have b48767 := hb (x 9 1 && x 9 14)
    clear * - r48765 b48766 b48767 d48760
    omega
  have d48768 : (x 9 2).toNat = 0 := by
    have r48769 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b48770 := hb (x 9 2)
    have b48771 := hb (x 9 14)
    clear * - r48769 b48770 b48771 d48760
    omega
  have d48772 : (x 9 12).toNat = 0 := by
    have r48773 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e48774 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e48775 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b48776 := hb (x 6 3)
    have b48777 := hb (x 7 2)
    have b48778 := hb (x 8 13)
    have b48779 := hb (x 9 12)
    clear * - r48773 e48774 e48775 b48776 b48777 b48778 b48779 d48751
    omega
  have d48780 : (x 7 2).toNat = 0 := by
    have r48781 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e48782 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e48783 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b48784 := hb (x 6 3)
    have b48785 := hb (x 7 2)
    have b48786 := hb (x 8 13)
    have b48787 := hb (x 9 12)
    clear * - r48781 e48782 e48783 b48784 b48785 b48786 b48787 d48772 d48751
    omega
  have d48788 : (x 7 12).toNat = 0 := by
    have r48789 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e48790 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e48791 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b48792 := hb (x 4 3)
    have b48793 := hb (x 5 2)
    have b48794 := hb (x 6 13)
    have b48795 := hb (x 7 12)
    clear * - r48789 e48790 e48791 b48792 b48793 b48794 b48795 d48734
    omega
  have d48796 : (x 5 2).toNat = 0 := by
    have r48797 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e48798 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e48799 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b48800 := hb (x 4 3)
    have b48801 := hb (x 5 2)
    have b48802 := hb (x 6 13)
    have b48803 := hb (x 7 12)
    clear * - r48797 e48798 e48799 b48800 b48801 b48802 b48803 d48788 d48734
    omega
  have d48804 : (x 7 13).toNat = 1 := by
    have r48805 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
    have b48806 := hb (x 5 2)
    have b48807 := hb (x 7 13)
    have b48808 := hb (x 6 1 && x 6 14)
    clear * - r48805 b48806 b48807 b48808 d48677 d48796
    omega
  have d48809 : (x 7 1).toNat = 1 := by
    have r48810 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b48811 := hb (x 7 1)
    have b48812 := hb (x 7 13)
    clear * - r48810 b48811 b48812 d48804
    omega
  have d48813 : (x 8 14).toNat = 0 := by
    have r48814 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
    have b48815 := hb (x 7 1)
    have b48816 := hb (x 8 14)
    clear * - r48814 b48815 b48816 d48809
    omega
  have d48817 : (x 8 1 && x 8 14).toNat = 0 := by
    have r48818 := hand2 (x 8 1) (x 8 14)
    have b48819 := hb (x 8 14)
    have b48820 := hb (x 8 1 && x 8 14)
    clear * - r48818 b48819 b48820 d48813
    omega
  have d48821 : (x 9 13).toNat = 1 := by
    have r48822 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
    have b48823 := hb (x 7 2)
    have b48824 := hb (x 9 13)
    have b48825 := hb (x 8 1 && x 8 14)
    clear * - r48822 b48823 b48824 b48825 d48817 d48780
    omega
  have d48826 : (x 9 1).toNat = 1 := by
    have r48827 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b48828 := hb (x 9 1)
    have b48829 := hb (x 9 13)
    clear * - r48827 b48828 b48829 d48821
    omega
  have d48830 : (x 10 14).toNat = 0 := by
    have r48831 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
    have b48832 := hb (x 9 1)
    have b48833 := hb (x 10 14)
    clear * - r48831 b48832 b48833 d48826
    omega
  have d48834 : (x 10 1 && x 10 14).toNat = 0 := by
    have r48835 := hand2 (x 10 1) (x 10 14)
    have b48836 := hb (x 10 14)
    have b48837 := hb (x 10 1 && x 10 14)
    clear * - r48835 b48836 b48837 d48830
    omega
  have d48838 : (x 11 13).toNat = 1 := by
    have r48839 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
    have b48840 := hb (x 9 2)
    have b48841 := hb (x 11 13)
    have b48842 := hb (x 10 1 && x 10 14)
    clear * - r48839 b48840 b48841 b48842 d48834 d48768
    omega
  have d48843 : (x 11 1).toNat = 1 := by
    have r48844 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b48845 := hb (x 11 1)
    have b48846 := hb (x 11 13)
    clear * - r48844 b48845 b48846 d48838
    omega
  have d48847 : (x 12 14).toNat = 0 := by
    have r48848 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
    have b48849 := hb (x 11 1)
    have b48850 := hb (x 12 14)
    clear * - r48848 b48849 b48850 d48843
    omega
  have d48851 : (x 12 1 && x 12 14).toNat = 0 := by
    have r48852 := hand2 (x 12 1) (x 12 14)
    have b48853 := hb (x 12 14)
    have b48854 := hb (x 12 1 && x 12 14)
    clear * - r48852 b48853 b48854 d48847
    omega
  have d48855 : (x 12 2).toNat = 0 := by
    have r48856 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
    have b48857 := hb (x 12 2)
    have b48858 := hb (x 12 14)
    clear * - r48856 b48857 b48858 d48847
    omega
  have d48859 : (x 12 12).toNat = 0 := by
    have r48860 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e48861 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e48862 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b48863 := hb (x 9 3)
    have b48864 := hb (x 10 2)
    have b48865 := hb (x 11 13)
    have b48866 := hb (x 12 12)
    clear * - r48860 e48861 e48862 b48863 b48864 b48865 b48866 d48838
    omega
  have d48867 : (x 10 2).toNat = 0 := by
    have r48868 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e48869 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e48870 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b48871 := hb (x 9 3)
    have b48872 := hb (x 10 2)
    have b48873 := hb (x 11 13)
    have b48874 := hb (x 12 12)
    clear * - r48868 e48869 e48870 b48871 b48872 b48873 b48874 d48859 d48838
    omega
  have d48875 : (x 10 12).toNat = 0 := by
    have r48876 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e48877 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e48878 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b48879 := hb (x 7 3)
    have b48880 := hb (x 8 2)
    have b48881 := hb (x 9 13)
    have b48882 := hb (x 10 12)
    clear * - r48876 e48877 e48878 b48879 b48880 b48881 b48882 d48821
    omega
  have d48883 : (x 8 2).toNat = 0 := by
    have r48884 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e48885 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e48886 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b48887 := hb (x 7 3)
    have b48888 := hb (x 8 2)
    have b48889 := hb (x 9 13)
    have b48890 := hb (x 10 12)
    clear * - r48884 e48885 e48886 b48887 b48888 b48889 b48890 d48875 d48821
    omega
  have d48891 : (x 10 13).toNat = 1 := by
    have r48892 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
    have b48893 := hb (x 8 2)
    have b48894 := hb (x 10 13)
    have b48895 := hb (x 9 1 && x 9 14)
    clear * - r48892 b48893 b48894 b48895 d48764 d48883
    omega
  have d48896 : (x 10 1).toNat = 1 := by
    have r48897 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b48898 := hb (x 10 1)
    have b48899 := hb (x 10 13)
    clear * - r48897 b48898 b48899 d48891
    omega
  have d48900 : (x 11 14).toNat = 0 := by
    have r48901 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
    have b48902 := hb (x 10 1)
    have b48903 := hb (x 11 14)
    clear * - r48901 b48902 b48903 d48896
    omega
  have d48904 : (x 11 1 && x 11 14).toNat = 0 := by
    have r48905 := hand2 (x 11 1) (x 11 14)
    have b48906 := hb (x 11 14)
    have b48907 := hb (x 11 1 && x 11 14)
    clear * - r48905 b48906 b48907 d48900
    omega
  have d48908 : (x 12 13).toNat = 1 := by
    have r48909 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
    have b48910 := hb (x 10 2)
    have b48911 := hb (x 12 13)
    have b48912 := hb (x 11 1 && x 11 14)
    clear * - r48909 b48910 b48911 b48912 d48904 d48867
    omega
  have d48913 : (x 12 1).toNat = 1 := by
    have r48914 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b48915 := hb (x 12 1)
    have b48916 := hb (x 12 13)
    clear * - r48914 b48915 b48916 d48908
    omega
  have d48917 : (x 13 14).toNat = 0 := by
    have r48918 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
    have b48919 := hb (x 12 1)
    have b48920 := hb (x 13 14)
    clear * - r48918 b48919 b48920 d48913
    omega
  have d48921 : (x 13 1 && x 13 14).toNat = 0 := by
    have r48922 := hand2 (x 13 1) (x 13 14)
    have b48923 := hb (x 13 14)
    have b48924 := hb (x 13 1 && x 13 14)
    clear * - r48922 b48923 b48924 d48917
    omega
  have d48925 : (x 14 13).toNat = 1 := by
    have r48926 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
    have b48927 := hb (x 12 2)
    have b48928 := hb (x 14 13)
    have b48929 := hb (x 13 1 && x 13 14)
    clear * - r48926 b48927 b48928 b48929 d48921 d48855
    omega
  have d48930 : (x 14 1).toNat = 1 := by
    have r48931 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b48932 := hb (x 14 1)
    have b48933 := hb (x 14 13)
    clear * - r48931 b48932 b48933 d48925
    omega
  have d48934 : (x 15 14).toNat = 0 := by
    have r48935 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
    have b48936 := hb (x 14 1)
    have b48937 := hb (x 15 14)
    clear * - r48935 b48936 b48937 d48930
    omega
  have d48938 : (x 15 1 && x 15 14).toNat = 0 := by
    have r48939 := hand2 (x 15 1) (x 15 14)
    have b48940 := hb (x 15 14)
    have b48941 := hb (x 15 1 && x 15 14)
    clear * - r48939 b48940 b48941 d48934
    omega
  have d48942 : (x 15 2).toNat = 0 := by
    have r48943 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b48944 := hb (x 15 2)
    have b48945 := hb (x 15 14)
    clear * - r48943 b48944 b48945 d48934
    omega
  have d48946 : (x 15 2 && x 15 13).toNat = 0 := by
    have r48947 := hand1 (x 15 2) (x 15 13)
    have b48948 := hb (x 15 2)
    have b48949 := hb (x 15 2 && x 15 13)
    clear * - r48947 b48948 b48949 d48942
    omega
  have d48950 : (x 15 12).toNat = 0 := by
    have r48951 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e48952 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e48953 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b48954 := hb (x 12 3)
    have b48955 := hb (x 13 2)
    have b48956 := hb (x 14 13)
    have b48957 := hb (x 15 12)
    clear * - r48951 e48952 e48953 b48954 b48955 b48956 b48957 d48925
    omega
  have d48958 : (x 13 2).toNat = 0 := by
    have r48959 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e48960 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e48961 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b48962 := hb (x 12 3)
    have b48963 := hb (x 13 2)
    have b48964 := hb (x 14 13)
    have b48965 := hb (x 15 12)
    clear * - r48959 e48960 e48961 b48962 b48963 b48964 b48965 d48950 d48925
    omega
  have d48966 : (x 13 12).toNat = 0 := by
    have r48967 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e48968 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e48969 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b48970 := hb (x 10 3)
    have b48971 := hb (x 11 2)
    have b48972 := hb (x 12 13)
    have b48973 := hb (x 13 12)
    clear * - r48967 e48968 e48969 b48970 b48971 b48972 b48973 d48908
    omega
  have d48974 : (x 13 4).toNat = 0 := by
    have r48975 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b48976 := hb (x 13 4)
    have b48977 := hb (x 13 12)
    clear * - r48975 b48976 b48977 d48966
    omega
  have d48978 : (x 11 2).toNat = 0 := by
    have r48979 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e48980 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e48981 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b48982 := hb (x 10 3)
    have b48983 := hb (x 11 2)
    have b48984 := hb (x 12 13)
    have b48985 := hb (x 13 12)
    clear * - r48979 e48980 e48981 b48982 b48983 b48984 b48985 d48966 d48908
    omega
  have d48986 : (x 13 13).toNat = 1 := by
    have r48987 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
    have b48988 := hb (x 11 2)
    have b48989 := hb (x 13 13)
    have b48990 := hb (x 12 1 && x 12 14)
    clear * - r48987 b48988 b48989 b48990 d48851 d48978
    omega
  have d48991 : (x 13 1).toNat = 1 := by
    have r48992 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
    have b48993 := hb (x 13 1)
    have b48994 := hb (x 13 13)
    clear * - r48992 b48993 b48994 d48986
    omega
  have d48995 : (x 14 14).toNat = 0 := by
    have r48996 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
    have b48997 := hb (x 13 1)
    have b48998 := hb (x 14 14)
    clear * - r48996 b48997 b48998 d48991
    omega
  have d48999 : (x 14 1 && x 14 14).toNat = 0 := by
    have r49000 := hand2 (x 14 1) (x 14 14)
    have b49001 := hb (x 14 14)
    have b49002 := hb (x 14 1 && x 14 14)
    clear * - r49000 b49001 b49002 d48995
    omega
  have d49003 : (x 15 13).toNat = 1 := by
    have r49004 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
    have b49005 := hb (x 13 2)
    have b49006 := hb (x 15 13)
    have b49007 := hb (x 14 1 && x 14 14)
    clear * - r49004 b49005 b49006 b49007 d48999 d48958
    omega
  have d49008 : (x 15 1).toNat = 1 := by
    have r49009 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have b49010 := hb (x 15 1)
    have b49011 := hb (x 15 13)
    clear * - r49009 b49010 b49011 d49003
    omega
  have d49012 : (x 16 14).toNat = 0 := by
    have r49013 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
    have b49014 := hb (x 15 1)
    have b49015 := hb (x 16 14)
    clear * - r49013 b49014 b49015 d49008
    omega
  have d49016 : (x 16 1 && x 16 14).toNat = 0 := by
    have r49017 := hand2 (x 16 1) (x 16 14)
    have b49018 := hb (x 16 14)
    have b49019 := hb (x 16 1 && x 16 14)
    clear * - r49017 b49018 b49019 d49012
    omega
  have d49020 : (x 17 13).toNat = 1 := by
    have r49021 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
    have b49022 := hb (x 15 2)
    have b49023 := hb (x 17 13)
    have b49024 := hb (x 16 1 && x 16 14)
    clear * - r49021 b49022 b49023 b49024 d49016 d48942
    omega
  have d49025 : (x 17 1).toNat = 1 := by
    have r49026 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
    have b49027 := hb (x 17 1)
    have b49028 := hb (x 17 13)
    clear * - r49026 b49027 b49028 d49020
    omega
  have d49029 : (x 18 14).toNat = 0 := by
    have r49030 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
    have b49031 := hb (x 17 1)
    have b49032 := hb (x 18 14)
    clear * - r49030 b49031 b49032 d49025
    omega
  have d49033 : (x 18 1 && x 18 14).toNat = 0 := by
    have r49034 := hand2 (x 18 1) (x 18 14)
    have b49035 := hb (x 18 14)
    have b49036 := hb (x 18 1 && x 18 14)
    clear * - r49034 b49035 b49036 d49029
    omega
  have d49037 : (x 18 2).toNat = 0 := by
    have r49038 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
    have b49039 := hb (x 18 2)
    have b49040 := hb (x 18 14)
    clear * - r49038 b49039 b49040 d49029
    omega
  have d49041 : (x 18 12).toNat = 0 := by
    have r49042 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e49043 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e49044 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b49045 := hb (x 15 3)
    have b49046 := hb (x 16 2)
    have b49047 := hb (x 17 13)
    have b49048 := hb (x 18 12)
    clear * - r49042 e49043 e49044 b49045 b49046 b49047 b49048 d49020
    omega
  have d49049 : (x 16 2).toNat = 0 := by
    have r49050 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e49051 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e49052 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b49053 := hb (x 15 3)
    have b49054 := hb (x 16 2)
    have b49055 := hb (x 17 13)
    have b49056 := hb (x 18 12)
    clear * - r49050 e49051 e49052 b49053 b49054 b49055 b49056 d49041 d49020
    omega
  have d49057 : (x 16 12).toNat = 0 := by
    have r49058 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e49059 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e49060 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b49061 := hb (x 13 3)
    have b49062 := hb (x 14 2)
    have b49063 := hb (x 15 13)
    have b49064 := hb (x 16 12)
    clear * - r49058 e49059 e49060 b49061 b49062 b49063 b49064 d49003
    omega
  have d49065 : (x 16 1 && x 16 12).toNat = 0 := by
    have r49066 := hand2 (x 16 1) (x 16 12)
    have b49067 := hb (x 16 12)
    have b49068 := hb (x 16 1 && x 16 12)
    clear * - r49066 b49067 b49068 d49057
    omega
  have d49069 : (x 14 2).toNat = 0 := by
    have r49070 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e49071 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e49072 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b49073 := hb (x 13 3)
    have b49074 := hb (x 14 2)
    have b49075 := hb (x 15 13)
    have b49076 := hb (x 16 12)
    clear * - r49070 e49071 e49072 b49073 b49074 b49075 b49076 d49057 d49003
    omega
  have d49077 : (x 16 13).toNat = 1 := by
    have r49078 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
    have b49079 := hb (x 14 2)
    have b49080 := hb (x 16 13)
    have b49081 := hb (x 15 1 && x 15 14)
    clear * - r49078 b49079 b49080 b49081 d48938 d49069
    omega
  have d49082 : (x 16 1).toNat = 1 := by
    have r49083 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
    have b49084 := hb (x 16 1)
    have b49085 := hb (x 16 13)
    clear * - r49083 b49084 b49085 d49077
    omega
  have d49086 : (x 17 14).toNat = 0 := by
    have r49087 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
    have b49088 := hb (x 16 1)
    have b49089 := hb (x 17 14)
    clear * - r49087 b49088 b49089 d49082
    omega
  have d49090 : (x 17 1 && x 17 14).toNat = 0 := by
    have r49091 := hand2 (x 17 1) (x 17 14)
    have b49092 := hb (x 17 14)
    have b49093 := hb (x 17 1 && x 17 14)
    clear * - r49091 b49092 b49093 d49086
    omega
  have d49094 : (x 18 13).toNat = 1 := by
    have r49095 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := hcov13 18
    have b49096 := hb (x 16 2)
    have b49097 := hb (x 18 13)
    have b49098 := hb (x 17 1 && x 17 14)
    clear * - r49095 b49096 b49097 b49098 d49090 d49049
    omega
  have d49099 : (x 19 12).toNat = 0 := by
    have r49100 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e49101 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e49102 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b49103 := hb (x 16 3)
    have b49104 := hb (x 17 2)
    have b49105 := hb (x 18 13)
    have b49106 := hb (x 19 12)
    clear * - r49100 e49101 e49102 b49103 b49104 b49105 b49106 d49094
    omega
  have d49107 : (x 17 2).toNat = 0 := by
    have r49108 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e49109 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e49110 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b49111 := hb (x 16 3)
    have b49112 := hb (x 17 2)
    have b49113 := hb (x 18 13)
    have b49114 := hb (x 19 12)
    clear * - r49108 e49109 e49110 b49111 b49112 b49113 b49114 d49099 d49094
    omega
  have d49115 : (x 19 13).toNat = 1 := by
    have r49116 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
    have b49117 := hb (x 17 2)
    have b49118 := hb (x 19 13)
    have b49119 := hb (x 18 1 && x 18 14)
    clear * - r49116 b49117 b49118 b49119 d49033 d49107
    omega
  have d49120 : (x 20 12).toNat = 0 := by
    have r49121 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e49122 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e49123 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b49124 := hb (x 17 3)
    have b49125 := hb (x 18 2)
    have b49126 := hb (x 19 13)
    have b49127 := hb (x 20 12)
    clear * - r49121 e49122 e49123 b49124 b49125 b49126 b49127 d49115 d49037
    omega
  have d49128 : (x 17 3).toNat = 0 := by
    have r49129 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e49130 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e49131 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b49132 := hb (x 17 3)
    have b49133 := hb (x 18 2)
    have b49134 := hb (x 19 13)
    have b49135 := hb (x 20 12)
    clear * - r49129 e49130 e49131 b49132 b49133 b49134 b49135 d49120 d49115 d49037
    omega
  have d49136 : (x 17 11).toNat = 0 := by
    have r49137 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b49138 := hb (x 17 3)
    have b49139 := hb (x 17 11)
    clear * - r49137 b49138 b49139 d49128
    omega
  have d49140 : (x 17 12).toNat = 0 := by
    have r49141 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e49142 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e49143 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b49144 := hb (x 14 3)
    have b49145 := hb (x 15 2)
    have b49146 := hb (x 16 13)
    have b49147 := hb (x 17 12)
    clear * - r49141 e49142 e49143 b49144 b49145 b49146 b49147 d49077 d48942
    omega
  have d49148 : (x 14 3).toNat = 0 := by
    have r49149 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e49150 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e49151 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b49152 := hb (x 14 3)
    have b49153 := hb (x 15 2)
    have b49154 := hb (x 16 13)
    have b49155 := hb (x 17 12)
    clear * - r49149 e49150 e49151 b49152 b49153 b49154 b49155 d49140 d49077 d48942
    omega
  have d49156 : (x 14 3 && x 14 14).toNat = 0 := by
    have r49157 := hand1 (x 14 3) (x 14 14)
    have b49158 := hb (x 14 3)
    have b49159 := hb (x 14 3 && x 14 14)
    clear * - r49157 b49158 b49159 d49148
    omega
  have r49160 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
  have b49161 := hb (x 13 4)
  have b49162 := hb (x 17 11)
  have b49163 := hb (x 16 1 && x 16 12)
  have b49164 := hb (x 15 2 && x 15 13)
  have b49165 := hb (x 14 3 && x 14 14)
  linarith only [r49160, b49161, b49162, b49163, b49164, b49165, d49136, d49065, d48946, d49156, d48974]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a011 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 1)
    (g1 : (x 1 2).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 0 1 && x 0 14).toNat = 0)
    (g4 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a011_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4
