import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a01

Topic: combinatorics   Node: c75718e10143

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 36 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a01_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 5).toNat = 0)
    (g1 : (x (-1) 9).toNat = 0)
    (g2 : (x (-1) 13).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 7).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 13).toNat = 1)
    (g7 : (x 1 5).toNat = 0)
    (g8 : (x 2 4).toNat = 0)
    (g9 : (x 3 11).toNat = 0)
    (g10 : (x 4 10).toNat = 0)
    (g11 : (x 5 9).toNat = 0)
    (g12 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g13 : (x 6 4 && x 6 8).toNat = 0)
    (g14 : (x 5 5 && x 5 9).toNat = 0)
    (g15 : (x 4 6 && x 4 10).toNat = 0)
    (g16 : (x 3 7 && x 3 11).toNat = 0)
    (g17 : (x 6 2 && x 6 8).toNat = 0)
    (g18 : (x 5 3 && x 5 9).toNat = 0)
    (g19 : (x 4 4 && x 4 10).toNat = 0)
    (g20 : (x 3 5 && x 3 11).toNat = 0)
    (g21 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g22 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g23 : (x 0 3 && x 0 12).toNat = 0)
    (g24 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g25 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g26 : (x 4 1 && x 4 10).toNat = 0)
    (g27 : (x 3 2 && x 3 11).toNat = 0)
    (g28 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g29 : (x 0 1 && x 0 11).toNat = 0)
    (g30 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g31 : (x 0 3 && x 0 13).toNat = 0)
    (g32 : (x 3 1 && x 3 11).toNat = 0)
    (g33 : (x 2 4 && x 2 14).toNat = 0)
    (g34 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g35 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d31670 : (x 0 1).toNat = 1 := by
    have r31671 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b31672 := hb (x 0 1)
    have b31673 := hb (x 0 13)
    clear * - r31671 b31672 b31673 g6
    omega
  have d31674 : (x 1 14).toNat = 0 := by
    have r31675 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b31676 := hb (x 0 1)
    have b31677 := hb (x 1 14)
    clear * - r31675 b31676 b31677 d31670
    omega
  have d31678 : (x 1 1 && x 1 14).toNat = 0 := by
    have r31679 := hand2 (x 1 1) (x 1 14)
    have b31680 := hb (x 1 14)
    have b31681 := hb (x 1 1 && x 1 14)
    clear * - r31679 b31680 b31681 d31674
    omega
  have d31682 : (x 1 2).toNat = 0 := by
    have r31683 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b31684 := hb (x 1 2)
    have b31685 := hb (x 1 14)
    clear * - r31683 b31684 b31685 d31674
    omega
  have d31686 : (x 1 2 && x 1 13).toNat = 0 := by
    have r31687 := hand1 (x 1 2) (x 1 13)
    have b31688 := hb (x 1 2)
    have b31689 := hb (x 1 2 && x 1 13)
    clear * - r31687 b31688 b31689 d31682
    omega
  have d31690 : (x 1 2 && x 1 12).toNat = 0 := by
    have r31691 := hand1 (x 1 2) (x 1 12)
    have b31692 := hb (x 1 2)
    have b31693 := hb (x 1 2 && x 1 12)
    clear * - r31691 b31692 b31693 d31682
    omega
  have d31694 : (x 1 2 && x 1 11).toNat = 0 := by
    have r31695 := hand1 (x 1 2) (x 1 11)
    have b31696 := hb (x 1 2)
    have b31697 := hb (x 1 2 && x 1 11)
    clear * - r31695 b31696 b31697 d31682
    omega
  have d31698 : (x 1 10).toNat = 0 := by
    have r31699 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
    have b31700 := hb (x 1 2)
    have b31701 := hb (x 1 10)
    clear * - r31699 b31700 b31701 d31682
    omega
  have d31702 : (x 1 12).toNat = 0 := by
    have r31703 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e31704 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e31705 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b31706 := hb (x (-2) 3)
    have b31707 := hb (x (-1) 2)
    have b31708 := hb (x 0 13)
    have b31709 := hb (x 1 12)
    clear * - r31703 e31704 e31705 b31706 b31707 b31708 b31709 g6
    omega
  have d31710 : (x 1 1 && x 1 12).toNat = 0 := by
    have r31711 := hand2 (x 1 1) (x 1 12)
    have b31712 := hb (x 1 12)
    have b31713 := hb (x 1 1 && x 1 12)
    clear * - r31711 b31712 b31713 d31702
    omega
  have d31714 : (x 1 3 && x 1 12).toNat = 0 := by
    have r31715 := hand2 (x 1 3) (x 1 12)
    have b31716 := hb (x 1 12)
    have b31717 := hb (x 1 3 && x 1 12)
    clear * - r31715 b31716 b31717 d31702
    omega
  have d31718 : (x 1 8 && x 1 12).toNat = 0 := by
    have r31719 := hand2 (x 1 8) (x 1 12)
    have b31720 := hb (x 1 12)
    have b31721 := hb (x 1 8 && x 1 12)
    clear * - r31719 b31720 b31721 d31702
    omega
  have d31722 : (x 1 4).toNat = 0 := by
    have r31723 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b31724 := hb (x 1 4)
    have b31725 := hb (x 1 12)
    clear * - r31723 b31724 b31725 d31702
    omega
  have d31726 : (x 1 4 && x 1 13).toNat = 0 := by
    have r31727 := hand1 (x 1 4) (x 1 13)
    have b31728 := hb (x 1 4)
    have b31729 := hb (x 1 4 && x 1 13)
    clear * - r31727 b31728 b31729 d31722
    omega
  have d31730 : (x 1 4 && x 1 8).toNat = 0 := by
    have r31731 := hand1 (x 1 4) (x 1 8)
    have b31732 := hb (x 1 4)
    have b31733 := hb (x 1 4 && x 1 8)
    clear * - r31731 b31732 b31733 d31722
    omega
  have d31734 : (x (-1) 2).toNat = 0 := by
    have r31735 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e31736 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e31737 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b31738 := hb (x (-2) 3)
    have b31739 := hb (x (-1) 2)
    have b31740 := hb (x 0 13)
    have b31741 := hb (x 1 12)
    clear * - r31735 e31736 e31737 b31738 b31739 b31740 b31741 d31702 g6
    omega
  have d31742 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r31743 := hand1 (x (-1) 2) (x (-1) 12)
    have b31744 := hb (x (-1) 2)
    have b31745 := hb (x (-1) 2 && x (-1) 12)
    clear * - r31743 b31744 b31745 d31734
    omega
  have d31746 : (x (-1) 10).toNat = 0 := by
    have r31747 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b31748 := hb (x (-1) 2)
    have b31749 := hb (x (-1) 10)
    clear * - r31747 b31748 b31749 d31734
    omega
  have d31750 : (x (-1) 6 && x (-1) 10).toNat = 0 := by
    have r31751 := hand2 (x (-1) 6) (x (-1) 10)
    have b31752 := hb (x (-1) 10)
    have b31753 := hb (x (-1) 6 && x (-1) 10)
    clear * - r31751 b31752 b31753 d31746
    omega
  have d31754 : (x (-2) 3).toNat = 0 := by
    have r31755 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e31756 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e31757 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b31758 := hb (x (-2) 3)
    have b31759 := hb (x (-1) 2)
    have b31760 := hb (x 0 13)
    have b31761 := hb (x 1 12)
    clear * - r31755 e31756 e31757 b31758 b31759 b31760 b31761 d31702 g6 d31734
    omega
  have d31762 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r31763 := hand1 (x (-2) 3) (x (-2) 13)
    have b31764 := hb (x (-2) 3)
    have b31765 := hb (x (-2) 3 && x (-2) 13)
    clear * - r31763 b31764 b31765 d31754
    omega
  have d31766 : (x (-2) 11).toNat = 0 := by
    have r31767 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b31768 := hb (x (-2) 3)
    have b31769 := hb (x (-2) 11)
    clear * - r31767 b31768 b31769 d31754
    omega
  have d31770 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
    have r31771 := hand2 (x (-2) 1) (x (-2) 11)
    have b31772 := hb (x (-2) 11)
    have b31773 := hb (x (-2) 1 && x (-2) 11)
    clear * - r31771 b31772 b31773 d31766
    omega
  have d31774 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r31775 := hand2 (x (-2) 2) (x (-2) 11)
    have b31776 := hb (x (-2) 11)
    have b31777 := hb (x (-2) 2 && x (-2) 11)
    clear * - r31775 b31776 b31777 d31766
    omega
  have d31778 : (x (-2) 7 && x (-2) 11).toNat = 0 := by
    have r31779 := hand2 (x (-2) 7) (x (-2) 11)
    have b31780 := hb (x (-2) 11)
    have b31781 := hb (x (-2) 7 && x (-2) 11)
    clear * - r31779 b31780 b31781 d31766
    omega
  cases h31782 : x 0 2
  · have f31783 : (x 0 2).toNat = 0 := by rw [h31782]; rfl
    have d31784 : (x 0 2 && x 0 13).toNat = 0 := by
      have r31785 := hand1 (x 0 2) (x 0 13)
      have b31786 := hb (x 0 2)
      have b31787 := hb (x 0 2 && x 0 13)
      clear * - r31785 b31786 b31787 f31783
      omega
    have d31788 : (x 0 2 && x 0 12).toNat = 0 := by
      have r31789 := hand1 (x 0 2) (x 0 12)
      have b31790 := hb (x 0 2)
      have b31791 := hb (x 0 2 && x 0 12)
      clear * - r31789 b31790 b31791 f31783
      omega
    have d31792 : (x 0 2 && x 0 6).toNat = 0 := by
      have r31793 := hand1 (x 0 2) (x 0 6)
      have b31794 := hb (x 0 2)
      have b31795 := hb (x 0 2 && x 0 6)
      clear * - r31793 b31794 b31795 f31783
      omega
    have d31796 : (x 0 10).toNat = 0 := by
      have r31797 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
      have b31798 := hb (x 0 2)
      have b31799 := hb (x 0 10)
      clear * - r31797 b31798 b31799 f31783
      omega
    have d31800 : (x 2 13).toNat = 1 := by
      have r31801 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b31802 := hb (x 0 2)
      have b31803 := hb (x 2 13)
      have b31804 := hb (x 1 1 && x 1 14)
      clear * - r31801 b31802 b31803 b31804 d31678 f31783
      omega
    have d31805 : (x 2 1).toNat = 1 := by
      have r31806 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b31807 := hb (x 2 1)
      have b31808 := hb (x 2 13)
      clear * - r31806 b31807 b31808 d31800
      omega
    have d31809 : (x 3 14).toNat = 0 := by
      have r31810 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b31811 := hb (x 2 1)
      have b31812 := hb (x 3 14)
      clear * - r31810 b31811 b31812 d31805
      omega
    have d31813 : (x 3 1 && x 3 14).toNat = 0 := by
      have r31814 := hand2 (x 3 1) (x 3 14)
      have b31815 := hb (x 3 14)
      have b31816 := hb (x 3 1 && x 3 14)
      clear * - r31814 b31815 b31816 d31809
      omega
    have d31817 : (x 3 3 && x 3 14).toNat = 0 := by
      have r31818 := hand2 (x 3 3) (x 3 14)
      have b31819 := hb (x 3 14)
      have b31820 := hb (x 3 3 && x 3 14)
      clear * - r31818 b31819 b31820 d31809
      omega
    have d31821 : (x 3 6).toNat = 0 := by
      have r31822 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
      have b31823 := hb (x 3 6)
      have b31824 := hb (x 3 14)
      clear * - r31822 b31823 b31824 d31809
      omega
    have d31825 : (x 3 6 && x 3 10).toNat = 0 := by
      have r31826 := hand1 (x 3 6) (x 3 10)
      have b31827 := hb (x 3 6)
      have b31828 := hb (x 3 6 && x 3 10)
      clear * - r31826 b31827 b31828 d31821
      omega
    have d31829 : (x 3 2 && x 3 6).toNat = 0 := by
      have r31830 := hand2 (x 3 2) (x 3 6)
      have b31831 := hb (x 3 6)
      have b31832 := hb (x 3 2 && x 3 6)
      clear * - r31830 b31831 b31832 d31821
      omega
    have d31833 : (x 3 2).toNat = 0 := by
      have r31834 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b31835 := hb (x 3 2)
      have b31836 := hb (x 3 14)
      clear * - r31834 b31835 b31836 d31809
      omega
    have d31837 : (x 3 2 && x 3 13).toNat = 0 := by
      have r31838 := hand1 (x 3 2) (x 3 13)
      have b31839 := hb (x 3 2)
      have b31840 := hb (x 3 2 && x 3 13)
      clear * - r31838 b31839 b31840 d31833
      omega
    have d31841 : (x 3 10).toNat = 0 := by
      have r31842 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
      have b31843 := hb (x 3 2)
      have b31844 := hb (x 3 10)
      clear * - r31842 b31843 b31844 d31833
      omega
    have d31845 : (x 3 1 && x 3 10).toNat = 0 := by
      have r31846 := hand2 (x 3 1) (x 3 10)
      have b31847 := hb (x 3 10)
      have b31848 := hb (x 3 1 && x 3 10)
      clear * - r31846 b31847 b31848 d31841
      omega
    cases h31849 : x 0 4
    · have f31850 : (x 0 4).toNat = 0 := by rw [h31849]; rfl
      have d31851 : (x 0 4 && x 0 14).toNat = 0 := by
        have r31852 := hand1 (x 0 4) (x 0 14)
        have b31853 := hb (x 0 4)
        have b31854 := hb (x 0 4 && x 0 14)
        clear * - r31852 b31853 b31854 f31850
        omega
      have d31855 : (x 0 4 && x 0 13).toNat = 0 := by
        have r31856 := hand1 (x 0 4) (x 0 13)
        have b31857 := hb (x 0 4)
        have b31858 := hb (x 0 4 && x 0 13)
        clear * - r31856 b31857 b31858 f31850
        omega
      cases h31859 : x 0 5
      · have f31860 : (x 0 5).toNat = 0 := by rw [h31859]; rfl
        have d31861 : (x 0 5 && x 0 14).toNat = 0 := by
          have r31862 := hand1 (x 0 5) (x 0 14)
          have b31863 := hb (x 0 5)
          have b31864 := hb (x 0 5 && x 0 14)
          clear * - r31862 b31863 b31864 f31860
          omega
        have d31865 : (x 0 5 && x 0 9).toNat = 0 := by
          have r31866 := hand1 (x 0 5) (x 0 9)
          have b31867 := hb (x 0 5)
          have b31868 := hb (x 0 5 && x 0 9)
          clear * - r31866 b31867 b31868 f31860
          omega
        cases h31869 : x 0 8
        · have f31870 : (x 0 8).toNat = 0 := by rw [h31869]; rfl
          have d31871 : (x 0 8 && x 0 14).toNat = 0 := by
            have r31872 := hand1 (x 0 8) (x 0 14)
            have b31873 := hb (x 0 8)
            have b31874 := hb (x 0 8 && x 0 14)
            clear * - r31872 b31873 b31874 f31870
            omega
          cases h31875 : x 0 9
          · have f31876 : (x 0 9).toNat = 0 := by rw [h31875]; rfl
            have d31877 : (x 0 9 && x 0 13).toNat = 0 := by
              have r31878 := hand1 (x 0 9) (x 0 13)
              have b31879 := hb (x 0 9)
              have b31880 := hb (x 0 9 && x 0 13)
              clear * - r31878 b31879 b31880 f31876
              omega
            cases h31881 : x 1 3
            · have f31882 : (x 1 3).toNat = 0 := by rw [h31881]; rfl
              have d31883 : (x 1 3 && x 1 13).toNat = 0 := by
                have r31884 := hand1 (x 1 3) (x 1 13)
                have b31885 := hb (x 1 3)
                have b31886 := hb (x 1 3 && x 1 13)
                clear * - r31884 b31885 b31886 f31882
                omega
              have d31887 : (x 2 2 && x 2 12).toNat = 1 := by
                have r31888 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b31889 := hb (x (-1) 5)
                have b31890 := hb (x 4 10)
                have b31891 := hb (x 3 1 && x 3 11)
                have b31892 := hb (x 2 2 && x 2 12)
                have b31893 := hb (x 1 3 && x 1 13)
                have b31894 := hb (x 0 4 && x 0 14)
                clear * - r31888 b31889 b31890 b31891 b31892 b31893 b31894 g10 g32 d31883 d31851 g0
                omega
              have d31895 : (x 2 12).toNat = 1 := by
                have r31896 := hand2 (x 2 2) (x 2 12)
                have b31897 := hb (x 2 12)
                have b31898 := hb (x 2 2 && x 2 12)
                clear * - r31896 b31897 b31898 d31887
                omega
              have d31899 : (x 1 13).toNat = 0 := by
                have r31900 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e31901 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                have e31902 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                have b31903 := hb (x (-1) 3)
                have b31904 := hb (x 0 2)
                have b31905 := hb (x 1 13)
                have b31906 := hb (x 2 12)
                clear * - r31900 e31901 e31902 b31903 b31904 b31905 b31906 d31895 f31783
                omega
              have d31907 : (x 1 7 && x 1 13).toNat = 0 := by
                have r31908 := hand2 (x 1 7) (x 1 13)
                have b31909 := hb (x 1 13)
                have b31910 := hb (x 1 7 && x 1 13)
                clear * - r31908 b31909 b31910 d31899
                omega
              have d31911 : (x 1 9 && x 1 13).toNat = 0 := by
                have r31912 := hand2 (x 1 9) (x 1 13)
                have b31913 := hb (x 1 13)
                have b31914 := hb (x 1 9 && x 1 13)
                clear * - r31912 b31913 b31914 d31899
                omega
              have d31915 : (x (-1) 3).toNat = 0 := by
                have r31916 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e31917 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                have e31918 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                have b31919 := hb (x (-1) 3)
                have b31920 := hb (x 0 2)
                have b31921 := hb (x 1 13)
                have b31922 := hb (x 2 12)
                clear * - r31916 e31917 e31918 b31919 b31920 b31921 b31922 d31895 d31899 f31783
                omega
              have d31923 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
                have r31924 := hand1 (x (-1) 3) (x (-1) 14)
                have b31925 := hb (x (-1) 3)
                have b31926 := hb (x (-1) 3 && x (-1) 14)
                clear * - r31924 b31925 b31926 d31915
                omega
              have d31927 : (x (-1) 11).toNat = 0 := by
                have r31928 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
                have b31929 := hb (x (-1) 3)
                have b31930 := hb (x (-1) 11)
                clear * - r31928 b31929 b31930 d31915
                omega
              have d31931 : (x 2 2).toNat = 1 := by
                have r31932 := hand1 (x 2 2) (x 2 12)
                have b31933 := hb (x 2 2)
                have b31934 := hb (x 2 2 && x 2 12)
                clear * - r31932 b31933 b31934 d31887
                omega
              have d31935 : (x 2 14).toNat = 1 := by
                have r31936 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
                have b31937 := hb (x 2 2)
                have b31938 := hb (x 2 14)
                clear * - r31936 b31937 b31938 d31931
                omega
              have d31939 : (x 1 1).toNat = 0 := by
                have r31940 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b31941 := hb (x 1 1)
                have b31942 := hb (x 2 14)
                clear * - r31940 b31941 b31942 d31935
                omega
              have d31943 : (x 1 9).toNat = 0 := by
                have r31944 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
                have b31945 := hb (x 1 1)
                have b31946 := hb (x 1 9)
                clear * - r31944 b31945 b31946 d31939
                omega
              have d31947 : (x 4 12).toNat = 0 := by
                have r31948 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e31949 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e31950 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b31951 := hb (x 1 3)
                have b31952 := hb (x 2 2)
                have b31953 := hb (x 3 13)
                have b31954 := hb (x 4 12)
                clear * - r31948 e31949 e31950 b31951 b31952 b31953 b31954 d31931 f31882
                omega
              have d31955 : (x 4 2 && x 4 12).toNat = 0 := by
                have r31956 := hand2 (x 4 2) (x 4 12)
                have b31957 := hb (x 4 12)
                have b31958 := hb (x 4 2 && x 4 12)
                clear * - r31956 b31957 b31958 d31947
                omega
              have d31959 : (x 4 4).toNat = 0 := by
                have r31960 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b31961 := hb (x 4 4)
                have b31962 := hb (x 4 12)
                clear * - r31960 b31961 b31962 d31947
                omega
              have d31963 : (x 3 13).toNat = 0 := by
                have r31964 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e31965 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e31966 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b31967 := hb (x 1 3)
                have b31968 := hb (x 2 2)
                have b31969 := hb (x 3 13)
                have b31970 := hb (x 4 12)
                clear * - r31964 e31965 e31966 b31967 b31968 b31969 b31970 d31947 d31931 f31882
                omega
              have d31971 : (x 3 3 && x 3 13).toNat = 0 := by
                have r31972 := hand2 (x 3 3) (x 3 13)
                have b31973 := hb (x 3 13)
                have b31974 := hb (x 3 3 && x 3 13)
                clear * - r31972 b31973 b31974 d31963
                omega
              have d31975 : (x 3 5).toNat = 0 := by
                have r31976 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                have b31977 := hb (x 3 5)
                have b31978 := hb (x 3 13)
                clear * - r31976 b31977 b31978 d31963
                omega
              have r31979 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r31980 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31981 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
              have e31982 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
              have e31983 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
              have e31984 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
              have e31985 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
              have e31986 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
              have r31987 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31988 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e31989 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e31990 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e31991 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e31992 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e31993 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have r31994 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31995 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e31996 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e31997 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e31998 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e31999 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e32000 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have r32001 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32002 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e32003 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e32004 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e32005 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e32006 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e32007 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have r32008 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32009 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e32010 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have r32011 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32012 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e32013 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have r32014 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32015 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e32016 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have r32017 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32018 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e32019 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have r32020 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32021 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
              have e32022 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
              have r32023 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32024 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
              have e32025 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
              have r32026 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r32027 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r32028 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r32029 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r32030 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r32031 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r32032 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r32033 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
              have r32034 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have r32035 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
              have r32036 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
              have r32037 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
              have r32038 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have r32039 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
              have r32040 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
              have r32041 := hand1 (x 7 2) (x 7 6)
              have r32042 := hand2 (x 6 3) (x 6 7)
              have r32043 := hand1 (x 5 4) (x 5 8)
              have r32044 := hand1 (x 4 5) (x 4 9)
              have r32045 := hand1 (x 2 7) (x 2 11)
              have r32046 := hand1 (x 8 2) (x 8 6)
              have r32047 := hand1 (x 7 3) (x 7 7)
              have r32048 := hand1 (x 2 8) (x 2 12)
              have r32049 := hand2 (x 7 1) (x 7 7)
              have r32050 := hand1 (x 2 6) (x 2 12)
              have r32051 := hand1 (x 2 3) (x 2 12)
              have r32052 := hand2 (x 12 1) (x 12 10)
              have r32053 := hand2 (x 11 2) (x 11 11)
              have r32054 := hand1 (x 10 3) (x 10 12)
              have r32055 := hand1 (x 9 4) (x 9 13)
              have r32056 := hand1 (x 8 5) (x 8 14)
              have r32057 := hand2 (x 5 1) (x 5 11)
              have r32058 := hand2 (x 11 1) (x 11 11)
              have r32059 := hand2 (x 10 2) (x 10 12)
              have r32060 := hand2 (x 9 3) (x 9 13)
              have r32061 := hand1 (x 8 4) (x 8 14)
              have r32062 := hand2 (x 5 1) (x 5 12)
              have r32063 := hand2 (x 4 2) (x 4 13)
              linarith only [r31979, r31980, e31981, e31982, e31983, e31984, e31985, e31986, r31987, e31988, e31989, e31990, e31991, e31992, e31993, r31994, e31995, e31996, e31997, e31998, e31999, e32000, r32001, e32002, e32003, e32004, e32005, e32006, e32007, r32008, e32009, e32010, r32011, e32012, e32013, r32014, e32015, e32016, r32017, e32018, e32019, r32020, e32021, e32022, r32023, e32024, e32025, r32026, r32027, r32028, r32029, r32030, r32031, r32032, r32033, r32034, r32035, r32036, r32037, r32038, r32039, r32040, r32041, r32042, r32043, r32044, r32045, r32046, r32047, r32048, r32049, r32050, r32051, r32052, r32053, r32054, r32055, r32056, r32057, r32058, r32059, r32060, r32061, r32062, r32063, d31766, g1, d31746, d31927, d31796, g6, g7, d31943, d31702, g8, d31833, d31975, d31821, d31841, d31959, g11, d31825, d31718, d31877, g13, g14, g15, g16, d31911, g17, g18, g19, g20, d31907, d31871, g26, g27, d31726, d31861, d31955, d31971, g33, d31710, d31784, d31923, d31817]
            · have f32183 : (x 1 3).toNat = 1 := by rw [h31881]; rfl
              have d32184 : (x 4 12).toNat = 0 := by
                have r32185 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32186 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e32187 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b32188 := hb (x 1 3)
                have b32189 := hb (x 2 2)
                have b32190 := hb (x 3 13)
                have b32191 := hb (x 4 12)
                clear * - r32185 e32186 e32187 b32188 b32189 b32190 b32191 f32183
                omega
              have d32192 : (x 4 1 && x 4 12).toNat = 0 := by
                have r32193 := hand2 (x 4 1) (x 4 12)
                have b32194 := hb (x 4 12)
                have b32195 := hb (x 4 1 && x 4 12)
                clear * - r32193 b32194 b32195 d32184
                omega
              have d32196 : (x 4 4).toNat = 0 := by
                have r32197 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b32198 := hb (x 4 4)
                have b32199 := hb (x 4 12)
                clear * - r32197 b32198 b32199 d32184
                omega
              have d32200 : (x 3 13).toNat = 0 := by
                have r32201 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32202 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e32203 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b32204 := hb (x 1 3)
                have b32205 := hb (x 2 2)
                have b32206 := hb (x 3 13)
                have b32207 := hb (x 4 12)
                clear * - r32201 e32202 e32203 b32204 b32205 b32206 b32207 d32184 f32183
                omega
              have d32208 : (x 2 2).toNat = 0 := by
                have r32209 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32210 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e32211 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b32212 := hb (x 1 3)
                have b32213 := hb (x 2 2)
                have b32214 := hb (x 3 13)
                have b32215 := hb (x 4 12)
                clear * - r32209 e32210 e32211 b32212 b32213 b32214 b32215 d32184 d32200 f32183
                omega
              have d32216 : (x 4 13).toNat = 1 := by
                have r32217 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32218 := hb (x 2 2)
                have b32219 := hb (x 4 13)
                have b32220 := hb (x 3 1 && x 3 14)
                clear * - r32217 b32218 b32219 b32220 d31813 d32208
                omega
              have d32221 : (x 4 1).toNat = 1 := by
                have r32222 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                have b32223 := hb (x 4 1)
                have b32224 := hb (x 4 13)
                clear * - r32222 b32223 b32224 d32216
                omega
              have d32225 : (x 5 14).toNat = 0 := by
                have r32226 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32227 := hb (x 4 1)
                have b32228 := hb (x 5 14)
                clear * - r32226 b32227 b32228 d32221
                omega
              have d32229 : (x 5 3 && x 5 14).toNat = 0 := by
                have r32230 := hand2 (x 5 3) (x 5 14)
                have b32231 := hb (x 5 14)
                have b32232 := hb (x 5 3 && x 5 14)
                clear * - r32230 b32231 b32232 d32225
                omega
              have d32233 : (x 5 2).toNat = 0 := by
                have r32234 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b32235 := hb (x 5 2)
                have b32236 := hb (x 5 14)
                clear * - r32234 b32235 b32236 d32225
                omega
              have d32237 : (x 5 12).toNat = 0 := by
                have r32238 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32239 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e32240 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b32241 := hb (x 2 3)
                have b32242 := hb (x 3 2)
                have b32243 := hb (x 4 13)
                have b32244 := hb (x 5 12)
                clear * - r32238 e32239 e32240 b32241 b32242 b32243 b32244 d32216 d31833
                omega
              have d32245 : (x 5 4).toNat = 0 := by
                have r32246 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                have b32247 := hb (x 5 4)
                have b32248 := hb (x 5 12)
                clear * - r32246 b32247 b32248 d32237
                omega
              have d32249 : (x 2 3).toNat = 0 := by
                have r32250 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32251 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e32252 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b32253 := hb (x 2 3)
                have b32254 := hb (x 3 2)
                have b32255 := hb (x 4 13)
                have b32256 := hb (x 5 12)
                clear * - r32250 e32251 e32252 b32253 b32254 b32255 b32256 d32237 d32216 d31833
                omega
              have d32257 : (x 2 3 && x 2 14).toNat = 0 := by
                have r32258 := hand1 (x 2 3) (x 2 14)
                have b32259 := hb (x 2 3)
                have b32260 := hb (x 2 3 && x 2 14)
                clear * - r32258 b32259 b32260 d32249
                omega
              have d32261 : (x 5 11).toNat = 1 := by
                have r32262 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32263 := hb (x 1 4)
                have b32264 := hb (x 5 11)
                have b32265 := hb (x 4 1 && x 4 12)
                have b32266 := hb (x 3 2 && x 3 13)
                have b32267 := hb (x 2 3 && x 2 14)
                clear * - r32262 b32263 b32264 b32265 b32266 b32267 d32192 d31837 d32257 d31722
                omega
              have d32268 : (x 5 3).toNat = 1 := by
                have r32269 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                have b32270 := hb (x 5 3)
                have b32271 := hb (x 5 11)
                clear * - r32269 b32270 b32271 d32261
                omega
              have d32272 : (x 8 12).toNat = 0 := by
                have r32273 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32274 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e32275 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b32276 := hb (x 5 3)
                have b32277 := hb (x 6 2)
                have b32278 := hb (x 7 13)
                have b32279 := hb (x 8 12)
                clear * - r32273 e32274 e32275 b32276 b32277 b32278 b32279 d32268
                omega
              have d32280 : (x 8 1 && x 8 12).toNat = 0 := by
                have r32281 := hand2 (x 8 1) (x 8 12)
                have b32282 := hb (x 8 12)
                have b32283 := hb (x 8 1 && x 8 12)
                clear * - r32281 b32282 b32283 d32272
                omega
              have d32284 : (x 8 4).toNat = 0 := by
                have r32285 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have b32286 := hb (x 8 4)
                have b32287 := hb (x 8 12)
                clear * - r32285 b32286 b32287 d32272
                omega
              have d32288 : (x 7 13).toNat = 0 := by
                have r32289 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32290 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e32291 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b32292 := hb (x 5 3)
                have b32293 := hb (x 6 2)
                have b32294 := hb (x 7 13)
                have b32295 := hb (x 8 12)
                clear * - r32289 e32290 e32291 b32292 b32293 b32294 b32295 d32272 d32268
                omega
              have d32296 : (x 7 2 && x 7 13).toNat = 0 := by
                have r32297 := hand2 (x 7 2) (x 7 13)
                have b32298 := hb (x 7 13)
                have b32299 := hb (x 7 2 && x 7 13)
                clear * - r32297 b32298 b32299 d32288
                omega
              have d32300 : (x 6 1 && x 6 14).toNat = 1 := by
                have r32301 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32302 := hb (x 5 2)
                have b32303 := hb (x 7 13)
                have b32304 := hb (x 6 1 && x 6 14)
                clear * - r32301 b32302 b32303 b32304 d32288 d32233
                omega
              have d32305 : (x 6 1).toNat = 1 := by
                have r32306 := hand1 (x 6 1) (x 6 14)
                have b32307 := hb (x 6 1)
                have b32308 := hb (x 6 1 && x 6 14)
                clear * - r32306 b32307 b32308 d32300
                omega
              have d32309 : (x 7 14).toNat = 0 := by
                have r32310 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32311 := hb (x 6 1)
                have b32312 := hb (x 7 14)
                clear * - r32310 b32311 b32312 d32305
                omega
              have d32313 : (x 7 1 && x 7 14).toNat = 0 := by
                have r32314 := hand2 (x 7 1) (x 7 14)
                have b32315 := hb (x 7 14)
                have b32316 := hb (x 7 1 && x 7 14)
                clear * - r32314 b32315 b32316 d32309
                omega
              have d32317 : (x 7 2).toNat = 0 := by
                have r32318 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b32319 := hb (x 7 2)
                have b32320 := hb (x 7 14)
                clear * - r32318 b32319 b32320 d32309
                omega
              have d32321 : (x 6 2).toNat = 0 := by
                have r32322 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32323 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e32324 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b32325 := hb (x 5 3)
                have b32326 := hb (x 6 2)
                have b32327 := hb (x 7 13)
                have b32328 := hb (x 8 12)
                clear * - r32322 e32323 e32324 b32325 b32326 b32327 b32328 d32272 d32288 d32268
                omega
              have d32329 : (x 6 2 && x 6 13).toNat = 0 := by
                have r32330 := hand1 (x 6 2) (x 6 13)
                have b32331 := hb (x 6 2)
                have b32332 := hb (x 6 2 && x 6 13)
                clear * - r32330 b32331 b32332 d32321
                omega
              have d32333 : (x 8 13).toNat = 1 := by
                have r32334 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32335 := hb (x 6 2)
                have b32336 := hb (x 8 13)
                have b32337 := hb (x 7 1 && x 7 14)
                clear * - r32334 b32335 b32336 b32337 d32313 d32321
                omega
              have d32338 : (x 8 1).toNat = 1 := by
                have r32339 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                have b32340 := hb (x 8 1)
                have b32341 := hb (x 8 13)
                clear * - r32339 b32340 b32341 d32333
                omega
              have d32342 : (x 9 14).toNat = 0 := by
                have r32343 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32344 := hb (x 8 1)
                have b32345 := hb (x 9 14)
                clear * - r32343 b32344 b32345 d32338
                omega
              have d32346 : (x 9 3 && x 9 14).toNat = 0 := by
                have r32347 := hand2 (x 9 3) (x 9 14)
                have b32348 := hb (x 9 14)
                have b32349 := hb (x 9 3 && x 9 14)
                clear * - r32347 b32348 b32349 d32342
                omega
              have d32350 : (x 9 2).toNat = 0 := by
                have r32351 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b32352 := hb (x 9 2)
                have b32353 := hb (x 9 14)
                clear * - r32351 b32352 b32353 d32342
                omega
              have d32354 : (x 9 12).toNat = 0 := by
                have r32355 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32356 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e32357 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b32358 := hb (x 6 3)
                have b32359 := hb (x 7 2)
                have b32360 := hb (x 8 13)
                have b32361 := hb (x 9 12)
                clear * - r32355 e32356 e32357 b32358 b32359 b32360 b32361 d32333 d32317
                omega
              have d32362 : (x 9 4).toNat = 0 := by
                have r32363 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have b32364 := hb (x 9 4)
                have b32365 := hb (x 9 12)
                clear * - r32363 b32364 b32365 d32354
                omega
              have d32366 : (x 6 3).toNat = 0 := by
                have r32367 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32368 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e32369 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b32370 := hb (x 6 3)
                have b32371 := hb (x 7 2)
                have b32372 := hb (x 8 13)
                have b32373 := hb (x 9 12)
                clear * - r32367 e32368 e32369 b32370 b32371 b32372 b32373 d32354 d32333 d32317
                omega
              have d32374 : (x 6 3 && x 6 14).toNat = 0 := by
                have r32375 := hand1 (x 6 3) (x 6 14)
                have b32376 := hb (x 6 3)
                have b32377 := hb (x 6 3 && x 6 14)
                clear * - r32375 b32376 b32377 d32366
                omega
              have d32378 : (x 9 11).toNat = 1 := by
                have r32379 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32380 := hb (x 5 4)
                have b32381 := hb (x 9 11)
                have b32382 := hb (x 8 1 && x 8 12)
                have b32383 := hb (x 7 2 && x 7 13)
                have b32384 := hb (x 6 3 && x 6 14)
                clear * - r32379 b32380 b32381 b32382 b32383 b32384 d32280 d32296 d32374 d32245
                omega
              have d32385 : (x 9 3).toNat = 1 := by
                have r32386 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
                have b32387 := hb (x 9 3)
                have b32388 := hb (x 9 11)
                clear * - r32386 b32387 b32388 d32378
                omega
              have d32389 : (x 12 12).toNat = 0 := by
                have r32390 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32391 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e32392 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b32393 := hb (x 9 3)
                have b32394 := hb (x 10 2)
                have b32395 := hb (x 11 13)
                have b32396 := hb (x 12 12)
                clear * - r32390 e32391 e32392 b32393 b32394 b32395 b32396 d32385
                omega
              have d32397 : (x 12 1 && x 12 12).toNat = 0 := by
                have r32398 := hand2 (x 12 1) (x 12 12)
                have b32399 := hb (x 12 12)
                have b32400 := hb (x 12 1 && x 12 12)
                clear * - r32398 b32399 b32400 d32389
                omega
              have d32401 : (x 12 4).toNat = 0 := by
                have r32402 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
                have b32403 := hb (x 12 4)
                have b32404 := hb (x 12 12)
                clear * - r32402 b32403 b32404 d32389
                omega
              have d32405 : (x 11 13).toNat = 0 := by
                have r32406 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32407 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e32408 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b32409 := hb (x 9 3)
                have b32410 := hb (x 10 2)
                have b32411 := hb (x 11 13)
                have b32412 := hb (x 12 12)
                clear * - r32406 e32407 e32408 b32409 b32410 b32411 b32412 d32389 d32385
                omega
              have d32413 : (x 11 2 && x 11 13).toNat = 0 := by
                have r32414 := hand2 (x 11 2) (x 11 13)
                have b32415 := hb (x 11 13)
                have b32416 := hb (x 11 2 && x 11 13)
                clear * - r32414 b32415 b32416 d32405
                omega
              have d32417 : (x 10 1 && x 10 14).toNat = 1 := by
                have r32418 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32419 := hb (x 9 2)
                have b32420 := hb (x 11 13)
                have b32421 := hb (x 10 1 && x 10 14)
                clear * - r32418 b32419 b32420 b32421 d32405 d32350
                omega
              have d32422 : (x 10 14).toNat = 1 := by
                have r32423 := hand2 (x 10 1) (x 10 14)
                have b32424 := hb (x 10 14)
                have b32425 := hb (x 10 1 && x 10 14)
                clear * - r32423 b32424 b32425 d32417
                omega
              have d32426 : (x 9 1).toNat = 0 := by
                have r32427 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32428 := hb (x 9 1)
                have b32429 := hb (x 10 14)
                clear * - r32427 b32428 b32429 d32422
                omega
              have d32430 : (x 9 13).toNat = 0 := by
                have r32431 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                have b32432 := hb (x 9 1)
                have b32433 := hb (x 9 13)
                clear * - r32431 b32432 b32433 d32426
                omega
              have d32434 : (x 8 1 && x 8 14).toNat = 1 := by
                have r32435 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32436 := hb (x 7 2)
                have b32437 := hb (x 9 13)
                have b32438 := hb (x 8 1 && x 8 14)
                clear * - r32435 b32436 b32437 b32438 d32430 d32317
                omega
              have d32439 : (x 8 14).toNat = 1 := by
                have r32440 := hand2 (x 8 1) (x 8 14)
                have b32441 := hb (x 8 14)
                have b32442 := hb (x 8 1 && x 8 14)
                clear * - r32440 b32441 b32442 d32434
                omega
              have d32443 : (x 7 1).toNat = 0 := by
                have r32444 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32445 := hb (x 7 1)
                have b32446 := hb (x 8 14)
                clear * - r32444 b32445 b32446 d32439
                omega
              have d32447 : (x 7 1 && x 7 12).toNat = 0 := by
                have r32448 := hand1 (x 7 1) (x 7 12)
                have b32449 := hb (x 7 1)
                have b32450 := hb (x 7 1 && x 7 12)
                clear * - r32448 b32449 b32450 d32443
                omega
              have d32451 : (x 8 11).toNat = 1 := by
                have r32452 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32453 := hb (x 4 4)
                have b32454 := hb (x 8 11)
                have b32455 := hb (x 7 1 && x 7 12)
                have b32456 := hb (x 6 2 && x 6 13)
                have b32457 := hb (x 5 3 && x 5 14)
                clear * - r32452 b32453 b32454 b32455 b32456 b32457 d32447 d32329 d32229 d32196
                omega
              have d32458 : (x 8 3).toNat = 1 := by
                have r32459 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                have b32460 := hb (x 8 3)
                have b32461 := hb (x 8 11)
                clear * - r32459 b32460 b32461 d32451
                omega
              have d32462 : (x 11 12).toNat = 0 := by
                have r32463 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32464 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e32465 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b32466 := hb (x 8 3)
                have b32467 := hb (x 9 2)
                have b32468 := hb (x 10 13)
                have b32469 := hb (x 11 12)
                clear * - r32463 e32464 e32465 b32466 b32467 b32468 b32469 d32350 d32458
                omega
              have d32470 : (x 11 1 && x 11 12).toNat = 0 := by
                have r32471 := hand2 (x 11 1) (x 11 12)
                have b32472 := hb (x 11 12)
                have b32473 := hb (x 11 1 && x 11 12)
                clear * - r32471 b32472 b32473 d32462
                omega
              have d32474 : (x 10 13).toNat = 0 := by
                have r32475 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32476 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e32477 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b32478 := hb (x 8 3)
                have b32479 := hb (x 9 2)
                have b32480 := hb (x 10 13)
                have b32481 := hb (x 11 12)
                clear * - r32475 e32476 e32477 b32478 b32479 b32480 b32481 d32462 d32350 d32458
                omega
              have d32482 : (x 10 2 && x 10 13).toNat = 0 := by
                have r32483 := hand2 (x 10 2) (x 10 13)
                have b32484 := hb (x 10 13)
                have b32485 := hb (x 10 2 && x 10 13)
                clear * - r32483 b32484 b32485 d32474
                omega
              have d32486 : (x 12 11).toNat = 1 := by
                have r32487 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32488 := hb (x 8 4)
                have b32489 := hb (x 12 11)
                have b32490 := hb (x 11 1 && x 11 12)
                have b32491 := hb (x 10 2 && x 10 13)
                have b32492 := hb (x 9 3 && x 9 14)
                clear * - r32487 b32488 b32489 b32490 b32491 b32492 d32470 d32482 d32346 d32284
                omega
              have d32493 : (x 12 3).toNat = 1 := by
                have r32494 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
                have b32495 := hb (x 12 3)
                have b32496 := hb (x 12 11)
                clear * - r32494 b32495 b32496 d32486
                omega
              have d32497 : (x 15 12).toNat = 0 := by
                have r32498 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32499 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e32500 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b32501 := hb (x 12 3)
                have b32502 := hb (x 13 2)
                have b32503 := hb (x 14 13)
                have b32504 := hb (x 15 12)
                clear * - r32498 e32499 e32500 b32501 b32502 b32503 b32504 d32493
                omega
              have d32505 : (x 15 1 && x 15 12).toNat = 0 := by
                have r32506 := hand2 (x 15 1) (x 15 12)
                have b32507 := hb (x 15 12)
                have b32508 := hb (x 15 1 && x 15 12)
                clear * - r32506 b32507 b32508 d32497
                omega
              have d32509 : (x 14 13).toNat = 0 := by
                have r32510 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32511 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e32512 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b32513 := hb (x 12 3)
                have b32514 := hb (x 13 2)
                have b32515 := hb (x 14 13)
                have b32516 := hb (x 15 12)
                clear * - r32510 e32511 e32512 b32513 b32514 b32515 b32516 d32497 d32493
                omega
              have d32517 : (x 14 2 && x 14 13).toNat = 0 := by
                have r32518 := hand2 (x 14 2) (x 14 13)
                have b32519 := hb (x 14 13)
                have b32520 := hb (x 14 2 && x 14 13)
                clear * - r32518 b32519 b32520 d32509
                omega
              have d32521 : (x 13 2).toNat = 0 := by
                have r32522 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32523 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e32524 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b32525 := hb (x 12 3)
                have b32526 := hb (x 13 2)
                have b32527 := hb (x 14 13)
                have b32528 := hb (x 15 12)
                clear * - r32522 e32523 e32524 b32525 b32526 b32527 b32528 d32497 d32509 d32493
                omega
              have d32529 : (x 10 1).toNat = 1 := by
                have r32530 := hand1 (x 10 1) (x 10 14)
                have b32531 := hb (x 10 1)
                have b32532 := hb (x 10 1 && x 10 14)
                clear * - r32530 b32531 b32532 d32417
                omega
              have d32533 : (x 11 14).toNat = 0 := by
                have r32534 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32535 := hb (x 10 1)
                have b32536 := hb (x 11 14)
                clear * - r32534 b32535 b32536 d32529
                omega
              have d32537 : (x 11 1 && x 11 14).toNat = 0 := by
                have r32538 := hand2 (x 11 1) (x 11 14)
                have b32539 := hb (x 11 14)
                have b32540 := hb (x 11 1 && x 11 14)
                clear * - r32538 b32539 b32540 d32533
                omega
              have d32541 : (x 11 2).toNat = 0 := by
                have r32542 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                have b32543 := hb (x 11 2)
                have b32544 := hb (x 11 14)
                clear * - r32542 b32543 b32544 d32533
                omega
              have d32545 : (x 10 2).toNat = 0 := by
                have r32546 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32547 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e32548 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b32549 := hb (x 9 3)
                have b32550 := hb (x 10 2)
                have b32551 := hb (x 11 13)
                have b32552 := hb (x 12 12)
                clear * - r32546 e32547 e32548 b32549 b32550 b32551 b32552 d32389 d32405 d32385
                omega
              have d32553 : (x 12 13).toNat = 1 := by
                have r32554 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32555 := hb (x 10 2)
                have b32556 := hb (x 12 13)
                have b32557 := hb (x 11 1 && x 11 14)
                clear * - r32554 b32555 b32556 b32557 d32537 d32545
                omega
              have d32558 : (x 12 1).toNat = 1 := by
                have r32559 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                have b32560 := hb (x 12 1)
                have b32561 := hb (x 12 13)
                clear * - r32559 b32560 b32561 d32553
                omega
              have d32562 : (x 13 14).toNat = 0 := by
                have r32563 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32564 := hb (x 12 1)
                have b32565 := hb (x 13 14)
                clear * - r32563 b32564 b32565 d32558
                omega
              have d32566 : (x 13 1 && x 13 14).toNat = 0 := by
                have r32567 := hand2 (x 13 1) (x 13 14)
                have b32568 := hb (x 13 14)
                have b32569 := hb (x 13 1 && x 13 14)
                clear * - r32567 b32568 b32569 d32562
                omega
              have d32570 : (x 12 2).toNat = 1 := by
                have r32571 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32572 := hb (x 12 2)
                have b32573 := hb (x 14 13)
                have b32574 := hb (x 13 1 && x 13 14)
                clear * - r32571 b32572 b32573 b32574 d32509 d32566
                omega
              have d32575 : (x 14 12).toNat = 0 := by
                have r32576 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32577 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e32578 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b32579 := hb (x 11 3)
                have b32580 := hb (x 12 2)
                have b32581 := hb (x 13 13)
                have b32582 := hb (x 14 12)
                clear * - r32576 e32577 e32578 b32579 b32580 b32581 b32582 d32570
                omega
              have d32583 : (x 14 4).toNat = 0 := by
                have r32584 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
                have b32585 := hb (x 14 4)
                have b32586 := hb (x 14 12)
                clear * - r32584 b32585 b32586 d32575
                omega
              have d32587 : (x 14 4 && x 14 14).toNat = 0 := by
                have r32588 := hand1 (x 14 4) (x 14 14)
                have b32589 := hb (x 14 4)
                have b32590 := hb (x 14 4 && x 14 14)
                clear * - r32588 b32589 b32590 d32583
                omega
              have d32591 : (x 13 13).toNat = 0 := by
                have r32592 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32593 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e32594 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b32595 := hb (x 11 3)
                have b32596 := hb (x 12 2)
                have b32597 := hb (x 13 13)
                have b32598 := hb (x 14 12)
                clear * - r32592 e32593 e32594 b32595 b32596 b32597 b32598 d32575 d32570
                omega
              have d32599 : (x 13 5).toNat = 0 := by
                have r32600 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
                have b32601 := hb (x 13 5)
                have b32602 := hb (x 13 13)
                clear * - r32600 b32601 b32602 d32591
                omega
              have d32603 : (x 13 3 && x 13 14).toNat = 0 := by
                have r32604 := hand2 (x 13 3) (x 13 14)
                have b32605 := hb (x 13 14)
                have b32606 := hb (x 13 3 && x 13 14)
                clear * - r32604 b32605 b32606 d32562
                omega
              have d32607 : (x 16 11).toNat = 1 := by
                have r32608 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32609 := hb (x 12 4)
                have b32610 := hb (x 16 11)
                have b32611 := hb (x 15 1 && x 15 12)
                have b32612 := hb (x 14 2 && x 14 13)
                have b32613 := hb (x 13 3 && x 13 14)
                clear * - r32608 b32609 b32610 b32611 b32612 b32613 d32505 d32517 d32603 d32401
                omega
              have d32614 : (x 16 3).toNat = 1 := by
                have r32615 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
                have b32616 := hb (x 16 3)
                have b32617 := hb (x 16 11)
                clear * - r32615 b32616 b32617 d32607
                omega
              have d32618 : (x 19 12).toNat = 0 := by
                have r32619 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32620 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e32621 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b32622 := hb (x 16 3)
                have b32623 := hb (x 17 2)
                have b32624 := hb (x 18 13)
                have b32625 := hb (x 19 12)
                clear * - r32619 e32620 e32621 b32622 b32623 b32624 b32625 d32614
                omega
              have d32626 : (x 18 13).toNat = 0 := by
                have r32627 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32628 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e32629 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b32630 := hb (x 16 3)
                have b32631 := hb (x 17 2)
                have b32632 := hb (x 18 13)
                have b32633 := hb (x 19 12)
                clear * - r32627 e32628 e32629 b32630 b32631 b32632 b32633 d32618 d32614
                omega
              have d32634 : (x 17 2).toNat = 0 := by
                have r32635 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32636 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e32637 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b32638 := hb (x 16 3)
                have b32639 := hb (x 17 2)
                have b32640 := hb (x 18 13)
                have b32641 := hb (x 19 12)
                clear * - r32635 e32636 e32637 b32638 b32639 b32640 b32641 d32618 d32626 d32614
                omega
              have d32642 : (x 13 12).toNat = 0 := by
                have r32643 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32644 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e32645 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b32646 := hb (x 10 3)
                have b32647 := hb (x 11 2)
                have b32648 := hb (x 12 13)
                have b32649 := hb (x 13 12)
                clear * - r32643 e32644 e32645 b32646 b32647 b32648 b32649 d32553 d32541
                omega
              have d32650 : (x 13 4).toNat = 0 := by
                have r32651 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
                have b32652 := hb (x 13 4)
                have b32653 := hb (x 13 12)
                clear * - r32651 b32652 b32653 d32642
                omega
              have d32654 : (x 10 3).toNat = 0 := by
                have r32655 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32656 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e32657 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b32658 := hb (x 10 3)
                have b32659 := hb (x 11 2)
                have b32660 := hb (x 12 13)
                have b32661 := hb (x 13 12)
                clear * - r32655 e32656 e32657 b32658 b32659 b32660 b32661 d32642 d32553 d32541
                omega
              have d32662 : (x 10 3 && x 10 14).toNat = 0 := by
                have r32663 := hand1 (x 10 3) (x 10 14)
                have b32664 := hb (x 10 3)
                have b32665 := hb (x 10 3 && x 10 14)
                clear * - r32663 b32664 b32665 d32654
                omega
              have d32666 : (x 13 11).toNat = 1 := by
                have r32667 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32668 := hb (x 9 4)
                have b32669 := hb (x 13 11)
                have b32670 := hb (x 12 1 && x 12 12)
                have b32671 := hb (x 11 2 && x 11 13)
                have b32672 := hb (x 10 3 && x 10 14)
                clear * - r32667 b32668 b32669 b32670 b32671 b32672 d32397 d32413 d32662 d32362
                omega
              have d32673 : (x 13 3).toNat = 1 := by
                have r32674 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have b32675 := hb (x 13 3)
                have b32676 := hb (x 13 11)
                clear * - r32674 b32675 b32676 d32666
                omega
              have d32677 : (x 16 12).toNat = 0 := by
                have r32678 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32679 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e32680 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b32681 := hb (x 13 3)
                have b32682 := hb (x 14 2)
                have b32683 := hb (x 15 13)
                have b32684 := hb (x 16 12)
                clear * - r32678 e32679 e32680 b32681 b32682 b32683 b32684 d32673
                omega
              have d32685 : (x 16 1 && x 16 12).toNat = 0 := by
                have r32686 := hand2 (x 16 1) (x 16 12)
                have b32687 := hb (x 16 12)
                have b32688 := hb (x 16 1 && x 16 12)
                clear * - r32686 b32687 b32688 d32677
                omega
              have d32689 : (x 16 2 && x 16 12).toNat = 0 := by
                have r32690 := hand2 (x 16 2) (x 16 12)
                have b32691 := hb (x 16 12)
                have b32692 := hb (x 16 2 && x 16 12)
                clear * - r32690 b32691 b32692 d32677
                omega
              have d32693 : (x 15 13).toNat = 0 := by
                have r32694 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32695 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e32696 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b32697 := hb (x 13 3)
                have b32698 := hb (x 14 2)
                have b32699 := hb (x 15 13)
                have b32700 := hb (x 16 12)
                clear * - r32694 e32695 e32696 b32697 b32698 b32699 b32700 d32677 d32673
                omega
              have d32701 : (x 15 2 && x 15 13).toNat = 0 := by
                have r32702 := hand2 (x 15 2) (x 15 13)
                have b32703 := hb (x 15 13)
                have b32704 := hb (x 15 2 && x 15 13)
                clear * - r32702 b32703 b32704 d32693
                omega
              have d32705 : (x 15 3 && x 15 13).toNat = 0 := by
                have r32706 := hand2 (x 15 3) (x 15 13)
                have b32707 := hb (x 15 13)
                have b32708 := hb (x 15 3 && x 15 13)
                clear * - r32706 b32707 b32708 d32693
                omega
              have d32709 : (x 14 1 && x 14 14).toNat = 1 := by
                have r32710 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32711 := hb (x 13 2)
                have b32712 := hb (x 15 13)
                have b32713 := hb (x 14 1 && x 14 14)
                clear * - r32710 b32711 b32712 b32713 d32693 d32521
                omega
              have d32714 : (x 14 1).toNat = 1 := by
                have r32715 := hand1 (x 14 1) (x 14 14)
                have b32716 := hb (x 14 1)
                have b32717 := hb (x 14 1 && x 14 14)
                clear * - r32715 b32716 b32717 d32709
                omega
              have d32718 : (x 15 14).toNat = 0 := by
                have r32719 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32720 := hb (x 14 1)
                have b32721 := hb (x 15 14)
                clear * - r32719 b32720 b32721 d32714
                omega
              have d32722 : (x 15 1 && x 15 14).toNat = 0 := by
                have r32723 := hand2 (x 15 1) (x 15 14)
                have b32724 := hb (x 15 14)
                have b32725 := hb (x 15 1 && x 15 14)
                clear * - r32723 b32724 b32725 d32718
                omega
              have d32726 : (x 15 2).toNat = 0 := by
                have r32727 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                have b32728 := hb (x 15 2)
                have b32729 := hb (x 15 14)
                clear * - r32727 b32728 b32729 d32718
                omega
              have d32730 : (x 14 2).toNat = 0 := by
                have r32731 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32732 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e32733 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b32734 := hb (x 13 3)
                have b32735 := hb (x 14 2)
                have b32736 := hb (x 15 13)
                have b32737 := hb (x 16 12)
                clear * - r32731 e32732 e32733 b32734 b32735 b32736 b32737 d32677 d32693 d32673
                omega
              have d32738 : (x 16 13).toNat = 1 := by
                have r32739 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32740 := hb (x 14 2)
                have b32741 := hb (x 16 13)
                have b32742 := hb (x 15 1 && x 15 14)
                clear * - r32739 b32740 b32741 b32742 d32722 d32730
                omega
              have d32743 : (x 17 12).toNat = 0 := by
                have r32744 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32745 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e32746 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b32747 := hb (x 14 3)
                have b32748 := hb (x 15 2)
                have b32749 := hb (x 16 13)
                have b32750 := hb (x 17 12)
                clear * - r32744 e32745 e32746 b32747 b32748 b32749 b32750 d32738 d32726
                omega
              have d32751 : (x 14 3).toNat = 0 := by
                have r32752 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32753 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e32754 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b32755 := hb (x 14 3)
                have b32756 := hb (x 15 2)
                have b32757 := hb (x 16 13)
                have b32758 := hb (x 17 12)
                clear * - r32752 e32753 e32754 b32755 b32756 b32757 b32758 d32743 d32738 d32726
                omega
              have d32759 : (x 14 3 && x 14 14).toNat = 0 := by
                have r32760 := hand1 (x 14 3) (x 14 14)
                have b32761 := hb (x 14 3)
                have b32762 := hb (x 14 3 && x 14 14)
                clear * - r32760 b32761 b32762 d32751
                omega
              have d32763 : (x 17 11).toNat = 1 := by
                have r32764 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32765 := hb (x 13 4)
                have b32766 := hb (x 17 11)
                have b32767 := hb (x 16 1 && x 16 12)
                have b32768 := hb (x 15 2 && x 15 13)
                have b32769 := hb (x 14 3 && x 14 14)
                clear * - r32764 b32765 b32766 b32767 b32768 b32769 d32685 d32701 d32759 d32650
                omega
              have d32770 : (x 17 3).toNat = 1 := by
                have r32771 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
                have b32772 := hb (x 17 3)
                have b32773 := hb (x 17 11)
                clear * - r32771 b32772 b32773 d32763
                omega
              have d32774 : (x 20 12).toNat = 0 := by
                have r32775 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32776 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e32777 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b32778 := hb (x 17 3)
                have b32779 := hb (x 18 2)
                have b32780 := hb (x 19 13)
                have b32781 := hb (x 20 12)
                clear * - r32775 e32776 e32777 b32778 b32779 b32780 b32781 d32770
                omega
              have d32782 : (x 19 13).toNat = 0 := by
                have r32783 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32784 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e32785 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b32786 := hb (x 17 3)
                have b32787 := hb (x 18 2)
                have b32788 := hb (x 19 13)
                have b32789 := hb (x 20 12)
                clear * - r32783 e32784 e32785 b32786 b32787 b32788 b32789 d32774 d32770
                omega
              have d32790 : (x 18 1 && x 18 14).toNat = 1 := by
                have r32791 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32792 := hb (x 17 2)
                have b32793 := hb (x 19 13)
                have b32794 := hb (x 18 1 && x 18 14)
                clear * - r32791 b32792 b32793 b32794 d32782 d32634
                omega
              have d32795 : (x 18 14).toNat = 1 := by
                have r32796 := hand2 (x 18 1) (x 18 14)
                have b32797 := hb (x 18 14)
                have b32798 := hb (x 18 1 && x 18 14)
                clear * - r32796 b32797 b32798 d32790
                omega
              have d32799 : (x 17 1).toNat = 0 := by
                have r32800 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b32801 := hb (x 17 1)
                have b32802 := hb (x 18 14)
                clear * - r32800 b32801 b32802 d32795
                omega
              have d32803 : (x 17 1 && x 17 11).toNat = 0 := by
                have r32804 := hand1 (x 17 1) (x 17 11)
                have b32805 := hb (x 17 1)
                have b32806 := hb (x 17 1 && x 17 11)
                clear * - r32804 b32805 b32806 d32799
                omega
              have d32807 : (x 18 2).toNat = 0 := by
                have r32808 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e32809 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e32810 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b32811 := hb (x 17 3)
                have b32812 := hb (x 18 2)
                have b32813 := hb (x 19 13)
                have b32814 := hb (x 20 12)
                clear * - r32808 e32809 e32810 b32811 b32812 b32813 b32814 d32774 d32782 d32770
                omega
              have d32815 : (x 18 10).toNat = 0 := by
                have r32816 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
                have b32817 := hb (x 18 2)
                have b32818 := hb (x 18 10)
                clear * - r32816 b32817 b32818 d32807
                omega
              have r32819 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b32820 := hb (x 13 5)
              have b32821 := hb (x 18 10)
              have b32822 := hb (x 17 1 && x 17 11)
              have b32823 := hb (x 16 2 && x 16 12)
              have b32824 := hb (x 15 3 && x 15 13)
              have b32825 := hb (x 14 4 && x 14 14)
              linarith only [r32819, b32820, b32821, b32822, b32823, b32824, b32825, d32815, d32803, d32689, d32705, d32587, d32599]
          · have f32826 : (x 0 9).toNat = 1 := by rw [h31875]; rfl
            have d32827 : (x 1 8).toNat = 0 := by
              have r32828 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32829 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e32830 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e32831 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e32832 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e32833 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e32834 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b32835 := hb (x (-6) 7)
              have b32836 := hb (x (-5) 6)
              have b32837 := hb (x (-4) 5)
              have b32838 := hb (x (-3) 4)
              have b32839 := hb (x (-2) 11)
              have b32840 := hb (x (-1) 10)
              have b32841 := hb (x 0 9)
              have b32842 := hb (x 1 8)
              clear * - r32828 e32829 e32830 e32831 e32832 e32833 e32834 b32835 b32836 b32837 b32838 b32839 b32840 b32841 b32842 f32826 d31746 d31766
              omega
            have d32843 : (x (-3) 4).toNat = 0 := by
              have r32844 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e32845 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e32846 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e32847 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e32848 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e32849 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e32850 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b32851 := hb (x (-6) 7)
              have b32852 := hb (x (-5) 6)
              have b32853 := hb (x (-4) 5)
              have b32854 := hb (x (-3) 4)
              have b32855 := hb (x (-2) 11)
              have b32856 := hb (x (-1) 10)
              have b32857 := hb (x 0 9)
              have b32858 := hb (x 1 8)
              clear * - r32844 e32845 e32846 e32847 e32848 e32849 e32850 b32851 b32852 b32853 b32854 b32855 b32856 b32857 b32858 d32827 f32826 d31746 d31766
              omega
            have d32859 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
              have r32860 := hand1 (x (-3) 4) (x (-3) 14)
              have b32861 := hb (x (-3) 4)
              have b32862 := hb (x (-3) 4 && x (-3) 14)
              clear * - r32860 b32861 b32862 d32843
              omega
            have d32863 : (x (-4) 5).toNat = 1 := by
              have r32864 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b32865 := hb (x (-4) 5)
              have b32866 := hb (x 1 10)
              have b32867 := hb (x 0 1 && x 0 11)
              have b32868 := hb (x (-1) 2 && x (-1) 12)
              have b32869 := hb (x (-2) 3 && x (-2) 13)
              have b32870 := hb (x (-3) 4 && x (-3) 14)
              clear * - r32864 b32865 b32866 b32867 b32868 b32869 b32870 d31698 g29 d31742 d31762 d32859
              omega
            have r32871 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e32872 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e32873 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e32874 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e32875 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e32876 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e32877 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b32878 := hb (x (-6) 7)
            have b32879 := hb (x (-5) 6)
            have b32880 := hb (x (-4) 5)
            have b32881 := hb (x (-3) 4)
            have b32882 := hb (x (-2) 11)
            have b32883 := hb (x (-1) 10)
            have b32884 := hb (x 0 9)
            have b32885 := hb (x 1 8)
            linarith only [r32871, e32872, e32873, e32874, e32875, e32876, e32877, b32878, b32879, b32880, b32881, b32882, b32883, b32884, b32885, d32827, f32826, d31746, d31766, d32843, d32863]
        · have f32886 : (x 0 8).toNat = 1 := by rw [h31869]; rfl
          have d32887 : (x (-2) 10).toNat = 0 := by
            have r32888 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e32889 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e32890 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e32891 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e32892 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e32893 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e32894 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have b32895 := hb (x (-7) 7)
            have b32896 := hb (x (-6) 6)
            have b32897 := hb (x (-5) 5)
            have b32898 := hb (x (-4) 4)
            have b32899 := hb (x (-3) 11)
            have b32900 := hb (x (-2) 10)
            have b32901 := hb (x (-1) 9)
            have b32902 := hb (x 0 8)
            clear * - r32888 e32889 e32890 e32891 e32892 e32893 e32894 b32895 b32896 b32897 b32898 b32899 b32900 b32901 b32902 f32886 g1
            omega
          have d32903 : (x (-3) 11).toNat = 0 := by
            have r32904 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e32905 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e32906 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e32907 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e32908 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e32909 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e32910 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have b32911 := hb (x (-7) 7)
            have b32912 := hb (x (-6) 6)
            have b32913 := hb (x (-5) 5)
            have b32914 := hb (x (-4) 4)
            have b32915 := hb (x (-3) 11)
            have b32916 := hb (x (-2) 10)
            have b32917 := hb (x (-1) 9)
            have b32918 := hb (x 0 8)
            clear * - r32904 e32905 e32906 e32907 e32908 e32909 e32910 b32911 b32912 b32913 b32914 b32915 b32916 b32917 b32918 f32886 g1 d32887
            omega
          have d32919 : (x (-4) 4).toNat = 0 := by
            have r32920 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e32921 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e32922 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e32923 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e32924 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e32925 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e32926 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have b32927 := hb (x (-7) 7)
            have b32928 := hb (x (-6) 6)
            have b32929 := hb (x (-5) 5)
            have b32930 := hb (x (-4) 4)
            have b32931 := hb (x (-3) 11)
            have b32932 := hb (x (-2) 10)
            have b32933 := hb (x (-1) 9)
            have b32934 := hb (x 0 8)
            clear * - r32920 e32921 e32922 e32923 e32924 e32925 e32926 b32927 b32928 b32929 b32930 b32931 b32932 b32933 b32934 f32886 g1 d32887 d32903
            omega
          have d32935 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
            have r32936 := hand1 (x (-4) 4) (x (-4) 14)
            have b32937 := hb (x (-4) 4)
            have b32938 := hb (x (-4) 4 && x (-4) 14)
            clear * - r32936 b32937 b32938 d32919
            omega
          have d32939 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
            have r32940 := hand1 (x (-4) 4) (x (-4) 13)
            have b32941 := hb (x (-4) 4)
            have b32942 := hb (x (-4) 4 && x (-4) 13)
            clear * - r32940 b32941 b32942 d32919
            omega
          have d32943 : (x (-5) 5).toNat = 0 := by
            have r32944 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e32945 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e32946 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e32947 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e32948 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e32949 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e32950 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have b32951 := hb (x (-7) 7)
            have b32952 := hb (x (-6) 6)
            have b32953 := hb (x (-5) 5)
            have b32954 := hb (x (-4) 4)
            have b32955 := hb (x (-3) 11)
            have b32956 := hb (x (-2) 10)
            have b32957 := hb (x (-1) 9)
            have b32958 := hb (x 0 8)
            clear * - r32944 e32945 e32946 e32947 e32948 e32949 e32950 b32951 b32952 b32953 b32954 b32955 b32956 b32957 b32958 f32886 g1 d32887 d32903 d32919
            omega
          have d32959 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
            have r32960 := hand1 (x (-5) 5) (x (-5) 14)
            have b32961 := hb (x (-5) 5)
            have b32962 := hb (x (-5) 5 && x (-5) 14)
            clear * - r32960 b32961 b32962 d32943
            omega
          have d32963 : (x (-6) 6).toNat = 0 := by
            have r32964 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e32965 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e32966 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e32967 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e32968 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e32969 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e32970 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have b32971 := hb (x (-7) 7)
            have b32972 := hb (x (-6) 6)
            have b32973 := hb (x (-5) 5)
            have b32974 := hb (x (-4) 4)
            have b32975 := hb (x (-3) 11)
            have b32976 := hb (x (-2) 10)
            have b32977 := hb (x (-1) 9)
            have b32978 := hb (x 0 8)
            clear * - r32964 e32965 e32966 e32967 e32968 e32969 e32970 b32971 b32972 b32973 b32974 b32975 b32976 b32977 b32978 f32886 g1 d32887 d32903 d32919 d32943
            omega
          have r32979 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32980 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e32981 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e32982 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e32983 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e32984 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e32985 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have r32986 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32987 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e32988 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e32989 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e32990 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e32991 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e32992 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have r32993 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e32994 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e32995 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e32996 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e32997 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e32998 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e32999 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have r33000 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33001 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e33002 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e33003 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e33004 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e33005 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e33006 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have r33007 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33008 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e33009 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have r33010 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33011 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e33012 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have r33013 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33014 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e33015 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have r33016 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33017 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33018 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33019 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
          have e33020 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
          have r33021 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33022 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33023 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33024 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33025 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33026 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33027 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r33028 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
          have r33029 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have r33030 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
          have r33031 := hand2 (x 2 3) (x 2 7)
          have r33032 := hand1 (x (-3) 8) (x (-3) 12)
          have r33033 := hand1 (x (-4) 9) (x (-4) 13)
          have r33034 := hand1 (x (-3) 3) (x (-3) 12)
          have r33035 := hand2 (x (-3) 3) (x (-3) 12)
          have r33036 := hand2 (x 2 2) (x 2 11)
          have r33037 := hand1 (x 2 3) (x 2 12)
          have r33038 := hand1 (x (-2) 2) (x (-2) 12)
          have r33039 := hand2 (x (-3) 3) (x (-3) 13)
          have r33040 := hand1 (x (-3) 4) (x (-3) 14)
          have r33041 := hand2 (x (-3) 4) (x (-3) 14)
          have r33042 := hand1 (x (-4) 1) (x (-4) 12)
          have r33043 := hand1 (x (-5) 2) (x (-5) 13)
          have r33044 := hand1 (x (-6) 3) (x (-6) 14)
          have r33045 := hand2 (x 5 1) (x 5 12)
          have r33046 := hand2 (x 4 2) (x 4 13)
          linarith only [r32979, e32980, e32981, e32982, e32983, e32984, e32985, r32986, e32987, e32988, e32989, e32990, e32991, e32992, r32993, e32994, e32995, e32996, e32997, e32998, e32999, r33000, e33001, e33002, e33003, e33004, e33005, e33006, r33007, e33008, e33009, r33010, e33011, e33012, r33013, e33014, e33015, r33016, r33017, r33018, e33019, e33020, r33021, r33022, r33023, r33024, r33025, r33026, r33027, r33028, r33029, r33030, r33031, r33032, r33033, r33034, r33035, r33036, r33037, r33038, r33039, r33040, r33041, r33042, r33043, r33044, r33045, r33046, d32963, d32943, d32903, d31766, d31746, g2, f31860, d31796, d31722, d31698, g8, d31833, d31821, d31841, g11, d31829, d31730, d31865, d31750, d31778, g22, d31774, d32939, d32959, d31845, d31714, d31855, g25, g26, g27, d31726, d31861, g28, d32935, g29, d31742, d31762, d31817]
      · have f33141 : (x 0 5).toNat = 1 := by rw [h31859]; rfl
        have d33142 : (x 5 8).toNat = 0 := by
          have r33143 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33144 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e33145 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e33146 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e33147 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e33148 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e33149 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b33150 := hb (x (-2) 7)
          have b33151 := hb (x (-1) 6)
          have b33152 := hb (x 0 5)
          have b33153 := hb (x 1 4)
          have b33154 := hb (x 2 11)
          have b33155 := hb (x 3 10)
          have b33156 := hb (x 4 9)
          have b33157 := hb (x 5 8)
          clear * - r33143 e33144 e33145 e33146 e33147 e33148 e33149 b33150 b33151 b33152 b33153 b33154 b33155 b33156 b33157 d31841 d31722 f33141
          omega
        have d33158 : (x 4 9).toNat = 0 := by
          have r33159 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33160 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e33161 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e33162 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e33163 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e33164 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e33165 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b33166 := hb (x (-2) 7)
          have b33167 := hb (x (-1) 6)
          have b33168 := hb (x 0 5)
          have b33169 := hb (x 1 4)
          have b33170 := hb (x 2 11)
          have b33171 := hb (x 3 10)
          have b33172 := hb (x 4 9)
          have b33173 := hb (x 5 8)
          clear * - r33159 e33160 e33161 e33162 e33163 e33164 e33165 b33166 b33167 b33168 b33169 b33170 b33171 b33172 b33173 d33142 d31841 d31722 f33141
          omega
        have d33174 : (x 2 11).toNat = 0 := by
          have r33175 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33176 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e33177 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e33178 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e33179 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e33180 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e33181 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b33182 := hb (x (-2) 7)
          have b33183 := hb (x (-1) 6)
          have b33184 := hb (x 0 5)
          have b33185 := hb (x 1 4)
          have b33186 := hb (x 2 11)
          have b33187 := hb (x 3 10)
          have b33188 := hb (x 4 9)
          have b33189 := hb (x 5 8)
          clear * - r33175 e33176 e33177 e33178 e33179 e33180 e33181 b33182 b33183 b33184 b33185 b33186 b33187 b33188 b33189 d33142 d33158 d31841 d31722 f33141
          omega
        have d33190 : (x 2 1 && x 2 11).toNat = 0 := by
          have r33191 := hand2 (x 2 1) (x 2 11)
          have b33192 := hb (x 2 11)
          have b33193 := hb (x 2 1 && x 2 11)
          clear * - r33191 b33192 b33193 d33174
          omega
        have d33194 : (x 2 2 && x 2 11).toNat = 0 := by
          have r33195 := hand2 (x 2 2) (x 2 11)
          have b33196 := hb (x 2 11)
          have b33197 := hb (x 2 2 && x 2 11)
          clear * - r33195 b33196 b33197 d33174
          omega
        have d33198 : (x (-2) 6).toNat = 1 := by
          have r33199 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33200 := hb (x (-2) 6)
          have b33201 := hb (x 4 9)
          have b33202 := hb (x 3 1 && x 3 10)
          have b33203 := hb (x 2 2 && x 2 11)
          have b33204 := hb (x 1 3 && x 1 12)
          have b33205 := hb (x 0 4 && x 0 13)
          have b33206 := hb (x (-1) 5 && x (-1) 14)
          clear * - r33199 b33200 b33201 b33202 b33203 b33204 b33205 b33206 d33158 d31845 d33194 d31714 d31855 g25
          omega
        have d33207 : (x (-2) 14).toNat = 1 := by
          have r33208 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
          have b33209 := hb (x (-2) 6)
          have b33210 := hb (x (-2) 14)
          clear * - r33208 b33209 b33210 d33198
          omega
        have d33211 : (x (-3) 1).toNat = 0 := by
          have r33212 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33213 := hb (x (-3) 1)
          have b33214 := hb (x (-2) 14)
          clear * - r33212 b33213 b33214 d33207
          omega
        have d33215 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
          have r33216 := hand1 (x (-3) 1) (x (-3) 14)
          have b33217 := hb (x (-3) 1)
          have b33218 := hb (x (-3) 1 && x (-3) 14)
          clear * - r33216 b33217 b33218 d33211
          omega
        have d33219 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
          have r33220 := hand1 (x (-3) 1) (x (-3) 12)
          have b33221 := hb (x (-3) 1)
          have b33222 := hb (x (-3) 1 && x (-3) 12)
          clear * - r33220 b33221 b33222 d33211
          omega
        have d33223 : (x (-3) 13).toNat = 0 := by
          have r33224 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b33225 := hb (x (-3) 1)
          have b33226 := hb (x (-3) 13)
          clear * - r33224 b33225 b33226 d33211
          omega
        have d33227 : (x (-3) 5).toNat = 0 := by
          have r33228 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
          have b33229 := hb (x (-3) 5)
          have b33230 := hb (x (-3) 13)
          clear * - r33228 b33229 b33230 d33223
          omega
        have d33231 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
          have r33232 := hand1 (x (-3) 5) (x (-3) 9)
          have b33233 := hb (x (-3) 5)
          have b33234 := hb (x (-3) 5 && x (-3) 9)
          clear * - r33232 b33233 b33234 d33227
          omega
        have d33235 : (x (-3) 9).toNat = 0 := by
          have r33236 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
          have b33237 := hb (x (-3) 1)
          have b33238 := hb (x (-3) 9)
          clear * - r33236 b33237 b33238 d33211
          omega
        have d33239 : (x 4 8).toNat = 0 := by
          have r33240 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33241 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e33242 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e33243 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e33244 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e33245 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e33246 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b33247 := hb (x (-3) 7)
          have b33248 := hb (x (-2) 6)
          have b33249 := hb (x (-1) 5)
          have b33250 := hb (x 0 4)
          have b33251 := hb (x 1 11)
          have b33252 := hb (x 2 10)
          have b33253 := hb (x 3 9)
          have b33254 := hb (x 4 8)
          clear * - r33240 e33241 e33242 e33243 e33244 e33245 e33246 b33247 b33248 b33249 b33250 b33251 b33252 b33253 b33254 f31850 g0 d33198
          omega
        have d33255 : (x 3 9).toNat = 0 := by
          have r33256 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33257 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e33258 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e33259 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e33260 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e33261 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e33262 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b33263 := hb (x (-3) 7)
          have b33264 := hb (x (-2) 6)
          have b33265 := hb (x (-1) 5)
          have b33266 := hb (x 0 4)
          have b33267 := hb (x 1 11)
          have b33268 := hb (x 2 10)
          have b33269 := hb (x 3 9)
          have b33270 := hb (x 4 8)
          clear * - r33256 e33257 e33258 e33259 e33260 e33261 e33262 b33263 b33264 b33265 b33266 b33267 b33268 b33269 b33270 d33239 f31850 g0 d33198
          omega
        have d33271 : (x 2 10).toNat = 0 := by
          have r33272 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33273 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e33274 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e33275 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e33276 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e33277 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e33278 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b33279 := hb (x (-3) 7)
          have b33280 := hb (x (-2) 6)
          have b33281 := hb (x (-1) 5)
          have b33282 := hb (x 0 4)
          have b33283 := hb (x 1 11)
          have b33284 := hb (x 2 10)
          have b33285 := hb (x 3 9)
          have b33286 := hb (x 4 8)
          clear * - r33272 e33273 e33274 e33275 e33276 e33277 e33278 b33279 b33280 b33281 b33282 b33283 b33284 b33285 b33286 d33239 d33255 f31850 g0 d33198
          omega
        have d33287 : (x 1 11).toNat = 0 := by
          have r33288 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33289 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e33290 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e33291 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e33292 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e33293 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e33294 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b33295 := hb (x (-3) 7)
          have b33296 := hb (x (-2) 6)
          have b33297 := hb (x (-1) 5)
          have b33298 := hb (x 0 4)
          have b33299 := hb (x 1 11)
          have b33300 := hb (x 2 10)
          have b33301 := hb (x 3 9)
          have b33302 := hb (x 4 8)
          clear * - r33288 e33289 e33290 e33291 e33292 e33293 e33294 b33295 b33296 b33297 b33298 b33299 b33300 b33301 b33302 d33239 d33255 d33271 f31850 g0 d33198
          omega
        have d33303 : (x 1 1 && x 1 11).toNat = 0 := by
          have r33304 := hand2 (x 1 1) (x 1 11)
          have b33305 := hb (x 1 11)
          have b33306 := hb (x 1 1 && x 1 11)
          clear * - r33304 b33305 b33306 d33287
          omega
        have d33307 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
          have r33308 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33309 := hb (x (-3) 5)
          have b33310 := hb (x 2 10)
          have b33311 := hb (x 1 1 && x 1 11)
          have b33312 := hb (x 0 2 && x 0 12)
          have b33313 := hb (x (-1) 3 && x (-1) 13)
          have b33314 := hb (x (-2) 4 && x (-2) 14)
          clear * - r33308 b33309 b33310 b33311 b33312 b33313 b33314 d33271 d33303 d31788 g30 d33227
          omega
        have d33315 : (x (-2) 4).toNat = 1 := by
          have r33316 := hand1 (x (-2) 4) (x (-2) 14)
          have b33317 := hb (x (-2) 4)
          have b33318 := hb (x (-2) 4 && x (-2) 14)
          clear * - r33316 b33317 b33318 d33307
          omega
        have d33319 : (x (-2) 12).toNat = 1 := by
          have r33320 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
          have b33321 := hb (x (-2) 4)
          have b33322 := hb (x (-2) 12)
          clear * - r33320 b33321 b33322 d33315
          omega
        have d33323 : (x (-4) 2).toNat = 0 := by
          have r33324 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33325 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e33326 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b33327 := hb (x (-5) 3)
          have b33328 := hb (x (-4) 2)
          have b33329 := hb (x (-3) 13)
          have b33330 := hb (x (-2) 12)
          clear * - r33324 e33325 e33326 b33327 b33328 b33329 b33330 d33319 d33223
          omega
        have d33331 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
          have r33332 := hand1 (x (-4) 2) (x (-4) 13)
          have b33333 := hb (x (-4) 2)
          have b33334 := hb (x (-4) 2 && x (-4) 13)
          clear * - r33332 b33333 b33334 d33323
          omega
        have d33335 : (x (-4) 10).toNat = 0 := by
          have r33336 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
          have b33337 := hb (x (-4) 2)
          have b33338 := hb (x (-4) 10)
          clear * - r33336 b33337 b33338 d33323
          omega
        have d33339 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
          have r33340 := hand2 (x (-4) 6) (x (-4) 10)
          have b33341 := hb (x (-4) 10)
          have b33342 := hb (x (-4) 6 && x (-4) 10)
          clear * - r33340 b33341 b33342 d33335
          omega
        have d33343 : (x (-2) 13).toNat = 1 := by
          have r33344 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33345 := hb (x (-4) 2)
          have b33346 := hb (x (-2) 13)
          have b33347 := hb (x (-3) 1 && x (-3) 14)
          clear * - r33344 b33345 b33346 b33347 d33215 d33323
          omega
        have d33348 : (x (-2) 1).toNat = 1 := by
          have r33349 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b33350 := hb (x (-2) 1)
          have b33351 := hb (x (-2) 13)
          clear * - r33349 b33350 b33351 d33343
          omega
        have d33352 : (x (-1) 14).toNat = 0 := by
          have r33353 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33354 := hb (x (-2) 1)
          have b33355 := hb (x (-1) 14)
          clear * - r33353 b33354 b33355 d33348
          omega
        have d33356 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
          have r33357 := hand2 (x (-1) 4) (x (-1) 14)
          have b33358 := hb (x (-1) 14)
          have b33359 := hb (x (-1) 4 && x (-1) 14)
          clear * - r33357 b33358 b33359 d33352
          omega
        have d33360 : (x (-2) 5).toNat = 1 := by
          have r33361 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33362 := hb (x (-2) 5)
          have b33363 := hb (x 3 10)
          have b33364 := hb (x 2 1 && x 2 11)
          have b33365 := hb (x 1 2 && x 1 12)
          have b33366 := hb (x 0 3 && x 0 13)
          have b33367 := hb (x (-1) 4 && x (-1) 14)
          clear * - r33361 b33362 b33363 b33364 b33365 b33366 b33367 d31841 d33190 d31690 g31 d33356
          omega
        have d33368 : (x (-1) 12).toNat = 0 := by
          have r33369 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33370 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e33371 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b33372 := hb (x (-4) 3)
          have b33373 := hb (x (-3) 2)
          have b33374 := hb (x (-2) 13)
          have b33375 := hb (x (-1) 12)
          clear * - r33369 e33370 e33371 b33372 b33373 b33374 b33375 d33343
          omega
        have d33376 : (x (-1) 4).toNat = 0 := by
          have r33377 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b33378 := hb (x (-1) 4)
          have b33379 := hb (x (-1) 12)
          clear * - r33377 b33378 b33379 d33368
          omega
        have d33380 : (x 2 1 && x 2 12).toNat = 1 := by
          have r33381 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33382 := hb (x (-1) 4)
          have b33383 := hb (x 3 11)
          have b33384 := hb (x 2 1 && x 2 12)
          have b33385 := hb (x 1 2 && x 1 13)
          have b33386 := hb (x 0 3 && x 0 14)
          clear * - r33381 b33382 b33383 b33384 b33385 b33386 g9 d31686 g35 d33376
          omega
        have d33387 : (x 2 12).toNat = 1 := by
          have r33388 := hand2 (x 2 1) (x 2 12)
          have b33389 := hb (x 2 12)
          have b33390 := hb (x 2 1 && x 2 12)
          clear * - r33388 b33389 b33390 d33380
          omega
        have d33391 : (x 1 13).toNat = 0 := by
          have r33392 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33393 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e33394 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b33395 := hb (x (-1) 3)
          have b33396 := hb (x 0 2)
          have b33397 := hb (x 1 13)
          have b33398 := hb (x 2 12)
          clear * - r33392 e33393 e33394 b33395 b33396 b33397 b33398 d33387 f31783
          omega
        have d33399 : (x 1 3 && x 1 13).toNat = 0 := by
          have r33400 := hand2 (x 1 3) (x 1 13)
          have b33401 := hb (x 1 13)
          have b33402 := hb (x 1 3 && x 1 13)
          clear * - r33400 b33401 b33402 d33391
          omega
        have d33403 : (x 2 2 && x 2 12).toNat = 1 := by
          have r33404 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33405 := hb (x (-1) 5)
          have b33406 := hb (x 4 10)
          have b33407 := hb (x 3 1 && x 3 11)
          have b33408 := hb (x 2 2 && x 2 12)
          have b33409 := hb (x 1 3 && x 1 13)
          have b33410 := hb (x 0 4 && x 0 14)
          clear * - r33404 b33405 b33406 b33407 b33408 b33409 b33410 g10 g32 d33399 d31851 g0
          omega
        have d33411 : (x 2 2).toNat = 1 := by
          have r33412 := hand1 (x 2 2) (x 2 12)
          have b33413 := hb (x 2 2)
          have b33414 := hb (x 2 2 && x 2 12)
          clear * - r33412 b33413 b33414 d33403
          omega
        have d33415 : (x 4 12).toNat = 0 := by
          have r33416 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33417 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e33418 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b33419 := hb (x 1 3)
          have b33420 := hb (x 2 2)
          have b33421 := hb (x 3 13)
          have b33422 := hb (x 4 12)
          clear * - r33416 e33417 e33418 b33419 b33420 b33421 b33422 d33411
          omega
        have d33423 : (x 3 13).toNat = 0 := by
          have r33424 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33425 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e33426 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b33427 := hb (x 1 3)
          have b33428 := hb (x 2 2)
          have b33429 := hb (x 3 13)
          have b33430 := hb (x 4 12)
          clear * - r33424 e33425 e33426 b33427 b33428 b33429 b33430 d33415 d33411
          omega
        have d33431 : (x 1 3).toNat = 0 := by
          have r33432 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33433 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e33434 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b33435 := hb (x 1 3)
          have b33436 := hb (x 2 2)
          have b33437 := hb (x 3 13)
          have b33438 := hb (x 4 12)
          clear * - r33432 e33433 e33434 b33435 b33436 b33437 b33438 d33415 d33423 d33411
          omega
        have d33439 : (x (-5) 3).toNat = 0 := by
          have r33440 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33441 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e33442 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b33443 := hb (x (-5) 3)
          have b33444 := hb (x (-4) 2)
          have b33445 := hb (x (-3) 13)
          have b33446 := hb (x (-2) 12)
          clear * - r33440 e33441 e33442 b33443 b33444 b33445 b33446 d33319 d33223 d33323
          omega
        have d33447 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
          have r33448 := hand1 (x (-5) 3) (x (-5) 14)
          have b33449 := hb (x (-5) 3)
          have b33450 := hb (x (-5) 3 && x (-5) 14)
          clear * - r33448 b33449 b33450 d33439
          omega
        have d33451 : (x (-6) 4).toNat = 1 := by
          have r33452 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b33453 := hb (x (-6) 4)
          have b33454 := hb (x (-2) 11)
          have b33455 := hb (x (-3) 1 && x (-3) 12)
          have b33456 := hb (x (-4) 2 && x (-4) 13)
          have b33457 := hb (x (-5) 3 && x (-5) 14)
          clear * - r33452 b33453 b33454 b33455 b33456 b33457 d31766 d33219 d33331 d33447
          omega
        have d33458 : (x (-6) 12).toNat = 1 := by
          have r33459 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
          have b33460 := hb (x (-6) 4)
          have b33461 := hb (x (-6) 12)
          clear * - r33459 b33460 b33461 d33451
          omega
        have d33462 : (x (-7) 13).toNat = 0 := by
          have r33463 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33464 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e33465 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b33466 := hb (x (-9) 3)
          have b33467 := hb (x (-8) 2)
          have b33468 := hb (x (-7) 13)
          have b33469 := hb (x (-6) 12)
          clear * - r33463 e33464 e33465 b33466 b33467 b33468 b33469 d33458
          omega
        have d33470 : (x (-7) 9 && x (-7) 13).toNat = 0 := by
          have r33471 := hand2 (x (-7) 9) (x (-7) 13)
          have b33472 := hb (x (-7) 13)
          have b33473 := hb (x (-7) 9 && x (-7) 13)
          clear * - r33471 b33472 b33473 d33462
          omega
        have d33474 : (x (-7) 5).toNat = 0 := by
          have r33475 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
          have b33476 := hb (x (-7) 5)
          have b33477 := hb (x (-7) 13)
          clear * - r33475 b33476 b33477 d33462
          omega
        have d33478 : (x (-8) 2).toNat = 0 := by
          have r33479 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33480 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e33481 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b33482 := hb (x (-9) 3)
          have b33483 := hb (x (-8) 2)
          have b33484 := hb (x (-7) 13)
          have b33485 := hb (x (-6) 12)
          clear * - r33479 e33480 e33481 b33482 b33483 b33484 b33485 d33458 d33462
          omega
        have d33486 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
          have r33487 := hand1 (x (-8) 2) (x (-8) 12)
          have b33488 := hb (x (-8) 2)
          have b33489 := hb (x (-8) 2 && x (-8) 12)
          clear * - r33487 b33488 b33489 d33478
          omega
        have d33490 : (x (-8) 2 && x (-8) 11).toNat = 0 := by
          have r33491 := hand1 (x (-8) 2) (x (-8) 11)
          have b33492 := hb (x (-8) 2)
          have b33493 := hb (x (-8) 2 && x (-8) 11)
          clear * - r33491 b33492 b33493 d33478
          omega
        have d33494 : (x (-8) 10).toNat = 0 := by
          have r33495 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
          have b33496 := hb (x (-8) 2)
          have b33497 := hb (x (-8) 10)
          clear * - r33495 b33496 b33497 d33478
          omega
        have d33498 : (x (-9) 3).toNat = 0 := by
          have r33499 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33500 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e33501 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b33502 := hb (x (-9) 3)
          have b33503 := hb (x (-8) 2)
          have b33504 := hb (x (-7) 13)
          have b33505 := hb (x (-6) 12)
          clear * - r33499 e33500 e33501 b33502 b33503 b33504 b33505 d33458 d33462 d33478
          omega
        have d33506 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
          have r33507 := hand1 (x (-9) 3) (x (-9) 13)
          have b33508 := hb (x (-9) 3)
          have b33509 := hb (x (-9) 3 && x (-9) 13)
          clear * - r33507 b33508 b33509 d33498
          omega
        have d33510 : (x (-9) 3 && x (-9) 12).toNat = 0 := by
          have r33511 := hand1 (x (-9) 3) (x (-9) 12)
          have b33512 := hb (x (-9) 3)
          have b33513 := hb (x (-9) 3 && x (-9) 12)
          clear * - r33511 b33512 b33513 d33498
          omega
        have d33514 : (x (-9) 11).toNat = 0 := by
          have r33515 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
          have b33516 := hb (x (-9) 3)
          have b33517 := hb (x (-9) 11)
          clear * - r33515 b33516 b33517 d33498
          omega
        have d33518 : (x (-5) 11).toNat = 0 := by
          have r33519 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
          have b33520 := hb (x (-5) 3)
          have b33521 := hb (x (-5) 11)
          clear * - r33519 b33520 b33521 d33439
          omega
        have d33522 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
          have r33523 := hand2 (x (-5) 7) (x (-5) 11)
          have b33524 := hb (x (-5) 11)
          have b33525 := hb (x (-5) 7 && x (-5) 11)
          clear * - r33523 b33524 b33525 d33518
          omega
        have d33526 : (x (-3) 7).toNat = 0 := by
          have r33527 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33528 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e33529 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e33530 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e33531 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e33532 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e33533 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b33534 := hb (x (-3) 7)
          have b33535 := hb (x (-2) 6)
          have b33536 := hb (x (-1) 5)
          have b33537 := hb (x 0 4)
          have b33538 := hb (x 1 11)
          have b33539 := hb (x 2 10)
          have b33540 := hb (x 3 9)
          have b33541 := hb (x 4 8)
          clear * - r33527 e33528 e33529 e33530 e33531 e33532 e33533 b33534 b33535 b33536 b33537 b33538 b33539 b33540 b33541 d33239 d33255 d33271 d33287 f31850 g0 d33198
          omega
        have d33542 : (x 3 8).toNat = 0 := by
          have r33543 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33544 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e33545 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e33546 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e33547 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e33548 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e33549 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b33550 := hb (x (-4) 7)
          have b33551 := hb (x (-3) 6)
          have b33552 := hb (x (-2) 5)
          have b33553 := hb (x (-1) 4)
          have b33554 := hb (x 0 11)
          have b33555 := hb (x 1 10)
          have b33556 := hb (x 2 9)
          have b33557 := hb (x 3 8)
          clear * - r33543 e33544 e33545 e33546 e33547 e33548 e33549 b33550 b33551 b33552 b33553 b33554 b33555 b33556 b33557 d31698 g5 d33376 d33360
          omega
        have d33558 : (x 2 9).toNat = 0 := by
          have r33559 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33560 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e33561 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e33562 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e33563 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e33564 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e33565 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b33566 := hb (x (-4) 7)
          have b33567 := hb (x (-3) 6)
          have b33568 := hb (x (-2) 5)
          have b33569 := hb (x (-1) 4)
          have b33570 := hb (x 0 11)
          have b33571 := hb (x 1 10)
          have b33572 := hb (x 2 9)
          have b33573 := hb (x 3 8)
          clear * - r33559 e33560 e33561 e33562 e33563 e33564 e33565 b33566 b33567 b33568 b33569 b33570 b33571 b33572 b33573 d33542 d31698 g5 d33376 d33360
          omega
        have d33574 : (x (-3) 6).toNat = 0 := by
          have r33575 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33576 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e33577 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e33578 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e33579 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e33580 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e33581 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b33582 := hb (x (-4) 7)
          have b33583 := hb (x (-3) 6)
          have b33584 := hb (x (-2) 5)
          have b33585 := hb (x (-1) 4)
          have b33586 := hb (x 0 11)
          have b33587 := hb (x 1 10)
          have b33588 := hb (x 2 9)
          have b33589 := hb (x 3 8)
          clear * - r33575 e33576 e33577 e33578 e33579 e33580 e33581 b33582 b33583 b33584 b33585 b33586 b33587 b33588 b33589 d33542 d33558 d31698 g5 d33376 d33360
          omega
        have d33590 : (x (-4) 7).toNat = 0 := by
          have r33591 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33592 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e33593 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e33594 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e33595 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e33596 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e33597 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b33598 := hb (x (-4) 7)
          have b33599 := hb (x (-3) 6)
          have b33600 := hb (x (-2) 5)
          have b33601 := hb (x (-1) 4)
          have b33602 := hb (x 0 11)
          have b33603 := hb (x 1 10)
          have b33604 := hb (x 2 9)
          have b33605 := hb (x 3 8)
          clear * - r33591 e33592 e33593 e33594 e33595 e33596 e33597 b33598 b33599 b33600 b33601 b33602 b33603 b33604 b33605 d33542 d33558 d31698 g5 d33376 d33360 d33574
          omega
        have d33606 : (x (-2) 8).toNat = 0 := by
          have r33607 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33608 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e33609 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e33610 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e33611 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e33612 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e33613 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have b33614 := hb (x (-9) 7)
          have b33615 := hb (x (-8) 6)
          have b33616 := hb (x (-7) 5)
          have b33617 := hb (x (-6) 4)
          have b33618 := hb (x (-5) 11)
          have b33619 := hb (x (-4) 10)
          have b33620 := hb (x (-3) 9)
          have b33621 := hb (x (-2) 8)
          clear * - r33607 e33608 e33609 e33610 e33611 e33612 e33613 b33614 b33615 b33616 b33617 b33618 b33619 b33620 b33621 d33235 d33335 d33518 d33451 d33474
          omega
        have d33622 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
          have r33623 := hand2 (x (-2) 4) (x (-2) 8)
          have b33624 := hb (x (-2) 8)
          have b33625 := hb (x (-2) 4 && x (-2) 8)
          clear * - r33623 b33624 b33625 d33606
          omega
        have d33626 : (x (-6) 8 && x (-6) 12).toNat = 1 := by
          have r33627 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33628 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
          have e33629 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
          have b33630 := hb (x (-9) 11)
          have b33631 := hb (x (-8) 10)
          have b33632 := hb (x 1 5)
          have b33633 := hb (x 2 4)
          have b33634 := hb (x 0 2 && x 0 6)
          have b33635 := hb (x (-1) 3 && x (-1) 7)
          have b33636 := hb (x (-2) 4 && x (-2) 8)
          have b33637 := hb (x (-3) 5 && x (-3) 9)
          have b33638 := hb (x (-4) 6 && x (-4) 10)
          have b33639 := hb (x (-5) 7 && x (-5) 11)
          have b33640 := hb (x (-6) 8 && x (-6) 12)
          have b33641 := hb (x (-7) 9 && x (-7) 13)
          clear * - r33627 e33628 e33629 b33630 b33631 b33632 b33633 b33634 b33635 b33636 b33637 b33638 b33639 b33640 b33641 g8 g7 d31792 g12 d33622 d33231 d33339 d33522 d33470 d33494 d33514
          omega
        have d33642 : (x (-6) 8).toNat = 1 := by
          have r33643 := hand1 (x (-6) 8) (x (-6) 12)
          have b33644 := hb (x (-6) 8)
          have b33645 := hb (x (-6) 8 && x (-6) 12)
          clear * - r33643 b33644 b33645 d33626
          omega
        have d33646 : (x (-7) 9).toNat = 0 := by
          have r33647 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33648 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e33649 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e33650 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e33651 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e33652 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e33653 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have b33654 := hb (x (-13) 7)
          have b33655 := hb (x (-12) 6)
          have b33656 := hb (x (-11) 5)
          have b33657 := hb (x (-10) 4)
          have b33658 := hb (x (-9) 11)
          have b33659 := hb (x (-8) 10)
          have b33660 := hb (x (-7) 9)
          have b33661 := hb (x (-6) 8)
          clear * - r33647 e33648 e33649 e33650 e33651 e33652 e33653 b33654 b33655 b33656 b33657 b33658 b33659 b33660 b33661 d33642 d33494 d33514
          omega
        have d33662 : (x (-10) 4).toNat = 0 := by
          have r33663 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33664 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e33665 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e33666 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e33667 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e33668 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e33669 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have b33670 := hb (x (-13) 7)
          have b33671 := hb (x (-12) 6)
          have b33672 := hb (x (-11) 5)
          have b33673 := hb (x (-10) 4)
          have b33674 := hb (x (-9) 11)
          have b33675 := hb (x (-8) 10)
          have b33676 := hb (x (-7) 9)
          have b33677 := hb (x (-6) 8)
          clear * - r33663 e33664 e33665 e33666 e33667 e33668 e33669 b33670 b33671 b33672 b33673 b33674 b33675 b33676 b33677 d33642 d33646 d33494 d33514
          omega
        have d33678 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
          have r33679 := hand1 (x (-10) 4) (x (-10) 14)
          have b33680 := hb (x (-10) 4)
          have b33681 := hb (x (-10) 4 && x (-10) 14)
          clear * - r33679 b33680 b33681 d33662
          omega
        have d33682 : (x (-10) 4 && x (-10) 13).toNat = 0 := by
          have r33683 := hand1 (x (-10) 4) (x (-10) 13)
          have b33684 := hb (x (-10) 4)
          have b33685 := hb (x (-10) 4 && x (-10) 13)
          clear * - r33683 b33684 b33685 d33662
          omega
        have d33686 : (x (-11) 5).toNat = 0 := by
          have r33687 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33688 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e33689 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e33690 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e33691 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e33692 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e33693 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have b33694 := hb (x (-13) 7)
          have b33695 := hb (x (-12) 6)
          have b33696 := hb (x (-11) 5)
          have b33697 := hb (x (-10) 4)
          have b33698 := hb (x (-9) 11)
          have b33699 := hb (x (-8) 10)
          have b33700 := hb (x (-7) 9)
          have b33701 := hb (x (-6) 8)
          clear * - r33687 e33688 e33689 e33690 e33691 e33692 e33693 b33694 b33695 b33696 b33697 b33698 b33699 b33700 b33701 d33642 d33646 d33494 d33514 d33662
          omega
        have d33702 : (x (-11) 5 && x (-11) 14).toNat = 0 := by
          have r33703 := hand1 (x (-11) 5) (x (-11) 14)
          have b33704 := hb (x (-11) 5)
          have b33705 := hb (x (-11) 5 && x (-11) 14)
          clear * - r33703 b33704 b33705 d33686
          omega
        have d33706 : (x (-12) 6).toNat = 0 := by
          have r33707 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e33708 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e33709 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e33710 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e33711 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e33712 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e33713 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have b33714 := hb (x (-13) 7)
          have b33715 := hb (x (-12) 6)
          have b33716 := hb (x (-11) 5)
          have b33717 := hb (x (-10) 4)
          have b33718 := hb (x (-9) 11)
          have b33719 := hb (x (-8) 10)
          have b33720 := hb (x (-7) 9)
          have b33721 := hb (x (-6) 8)
          clear * - r33707 e33708 e33709 e33710 e33711 e33712 e33713 b33714 b33715 b33716 b33717 b33718 b33719 b33720 b33721 d33642 d33646 d33494 d33514 d33662 d33686
          omega
        have r33722 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r33723 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r33724 : 1 ≤ (x (-6) 9).toNat + (x (-7) 1 && x (-7) 10).toNat + (x (-8) 2 && x (-8) 11).toNat + (x (-9) 3 && x (-9) 12).toNat + (x (-10) 4 && x (-10) 13).toNat + (x (-11) 5 && x (-11) 14).toNat + (x (-12) 6).toNat := by have q := hcov9 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r33725 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r33726 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r33727 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
        have r33728 := hand2 (x (-7) 1) (x (-7) 10)
        have r33729 := hand2 (x (-7) 1) (x (-7) 11)
        have r33730 := hand2 (x (-10) 1) (x (-10) 14)
        linarith only [r33722, r33723, r33724, r33725, r33726, r33727, r33728, r33729, r33730, d33706, d33686, d33590, d33574, d33526, d33360, d33198, d33376, g0, g3, f31850, d31682, d33431, d31805, d33411, d33490, d33510, d33682, d33702, d33486, d33506, d33678]
    · have f33772 : (x 0 4).toNat = 1 := by rw [h31849]; rfl
      have d33773 : (x 0 12).toNat = 1 := by
        have r33774 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
        have b33775 := hb (x 0 4)
        have b33776 := hb (x 0 12)
        clear * - r33774 b33775 b33776 f33772
        omega
      have d33777 : (x (-2) 2).toNat = 0 := by
        have r33778 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e33779 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e33780 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b33781 := hb (x (-3) 3)
        have b33782 := hb (x (-2) 2)
        have b33783 := hb (x (-1) 13)
        have b33784 := hb (x 0 12)
        clear * - r33778 e33779 e33780 b33781 b33782 b33783 b33784 d33773 g2
        omega
      have d33785 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
        have r33786 := hand1 (x (-2) 2) (x (-2) 13)
        have b33787 := hb (x (-2) 2)
        have b33788 := hb (x (-2) 2 && x (-2) 13)
        clear * - r33786 b33787 b33788 d33777
        omega
      have d33789 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
        have r33790 := hand1 (x (-2) 2) (x (-2) 12)
        have b33791 := hb (x (-2) 2)
        have b33792 := hb (x (-2) 2 && x (-2) 12)
        clear * - r33790 b33791 b33792 d33777
        omega
      have d33793 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
        have r33794 := hand1 (x (-2) 2) (x (-2) 9)
        have b33795 := hb (x (-2) 2)
        have b33796 := hb (x (-2) 2 && x (-2) 9)
        clear * - r33794 b33795 b33796 d33777
        omega
      have d33797 : (x (-2) 10).toNat = 0 := by
        have r33798 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
        have b33799 := hb (x (-2) 2)
        have b33800 := hb (x (-2) 10)
        clear * - r33798 b33799 b33800 d33777
        omega
      have d33801 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
        have r33802 := hand2 (x (-2) 1) (x (-2) 10)
        have b33803 := hb (x (-2) 10)
        have b33804 := hb (x (-2) 1 && x (-2) 10)
        clear * - r33802 b33803 b33804 d33797
        omega
      have d33805 : (x (-3) 3).toNat = 0 := by
        have r33806 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e33807 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e33808 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b33809 := hb (x (-3) 3)
        have b33810 := hb (x (-2) 2)
        have b33811 := hb (x (-1) 13)
        have b33812 := hb (x 0 12)
        clear * - r33806 e33807 e33808 b33809 b33810 b33811 b33812 d33773 g2 d33777
        omega
      have d33813 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
        have r33814 := hand1 (x (-3) 3) (x (-3) 14)
        have b33815 := hb (x (-3) 3)
        have b33816 := hb (x (-3) 3 && x (-3) 14)
        clear * - r33814 b33815 b33816 d33805
        omega
      have d33817 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
        have r33818 := hand1 (x (-3) 3) (x (-3) 13)
        have b33819 := hb (x (-3) 3)
        have b33820 := hb (x (-3) 3 && x (-3) 13)
        clear * - r33818 b33819 b33820 d33805
        omega
      have d33821 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
        have r33822 := hand1 (x (-3) 3) (x (-3) 10)
        have b33823 := hb (x (-3) 3)
        have b33824 := hb (x (-3) 3 && x (-3) 10)
        clear * - r33822 b33823 b33824 d33805
        omega
      have d33825 : (x (-3) 11).toNat = 0 := by
        have r33826 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
        have b33827 := hb (x (-3) 3)
        have b33828 := hb (x (-3) 11)
        clear * - r33826 b33827 b33828 d33805
        omega
      have d33829 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
        have r33830 := hand2 (x (-3) 1) (x (-3) 11)
        have b33831 := hb (x (-3) 11)
        have b33832 := hb (x (-3) 1 && x (-3) 11)
        clear * - r33830 b33831 b33832 d33825
        omega
      have d33833 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
        have r33834 := hand2 (x (-3) 2) (x (-3) 11)
        have b33835 := hb (x (-3) 11)
        have b33836 := hb (x (-3) 2 && x (-3) 11)
        clear * - r33834 b33835 b33836 d33825
        omega
      have d33837 : (x (-4) 4).toNat = 1 := by
        have r33838 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b33839 := hb (x (-4) 4)
        have b33840 := hb (x 0 11)
        have b33841 := hb (x (-1) 1 && x (-1) 12)
        have b33842 := hb (x (-2) 2 && x (-2) 13)
        have b33843 := hb (x (-3) 3 && x (-3) 14)
        clear * - r33838 b33839 b33840 b33841 b33842 b33843 g5 g34 d33785 d33813
        omega
      have d33844 : (x (-4) 12).toNat = 1 := by
        have r33845 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have b33846 := hb (x (-4) 4)
        have b33847 := hb (x (-4) 12)
        clear * - r33845 b33846 b33847 d33837
        omega
      have d33848 : (x (-5) 13).toNat = 0 := by
        have r33849 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e33850 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e33851 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b33852 := hb (x (-7) 3)
        have b33853 := hb (x (-6) 2)
        have b33854 := hb (x (-5) 13)
        have b33855 := hb (x (-4) 12)
        clear * - r33849 e33850 e33851 b33852 b33853 b33854 b33855 d33844
        omega
      have d33856 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
        have r33857 := hand2 (x (-5) 3) (x (-5) 13)
        have b33858 := hb (x (-5) 13)
        have b33859 := hb (x (-5) 3 && x (-5) 13)
        clear * - r33857 b33858 b33859 d33848
        omega
      have d33860 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
        have r33861 := hand2 (x (-5) 4) (x (-5) 13)
        have b33862 := hb (x (-5) 13)
        have b33863 := hb (x (-5) 4 && x (-5) 13)
        clear * - r33861 b33862 b33863 d33848
        omega
      have d33864 : (x (-5) 5).toNat = 0 := by
        have r33865 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
        have b33866 := hb (x (-5) 5)
        have b33867 := hb (x (-5) 13)
        clear * - r33865 b33866 b33867 d33848
        omega
      have d33868 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
        have r33869 := hand1 (x (-5) 5) (x (-5) 12)
        have b33870 := hb (x (-5) 5)
        have b33871 := hb (x (-5) 5 && x (-5) 12)
        clear * - r33869 b33870 b33871 d33864
        omega
      have d33872 : (x (-6) 2).toNat = 0 := by
        have r33873 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e33874 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e33875 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b33876 := hb (x (-7) 3)
        have b33877 := hb (x (-6) 2)
        have b33878 := hb (x (-5) 13)
        have b33879 := hb (x (-4) 12)
        clear * - r33873 e33874 e33875 b33876 b33877 b33878 b33879 d33844 d33848
        omega
      have d33880 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
        have r33881 := hand1 (x (-6) 2) (x (-6) 13)
        have b33882 := hb (x (-6) 2)
        have b33883 := hb (x (-6) 2 && x (-6) 13)
        clear * - r33881 b33882 b33883 d33872
        omega
      have d33884 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
        have r33885 := hand1 (x (-6) 2) (x (-6) 12)
        have b33886 := hb (x (-6) 2)
        have b33887 := hb (x (-6) 2 && x (-6) 12)
        clear * - r33885 b33886 b33887 d33872
        omega
      have d33888 : (x (-6) 10).toNat = 0 := by
        have r33889 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have b33890 := hb (x (-6) 2)
        have b33891 := hb (x (-6) 10)
        clear * - r33889 b33890 b33891 d33872
        omega
      have d33892 : (x (-7) 3).toNat = 0 := by
        have r33893 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e33894 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e33895 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b33896 := hb (x (-7) 3)
        have b33897 := hb (x (-6) 2)
        have b33898 := hb (x (-5) 13)
        have b33899 := hb (x (-4) 12)
        clear * - r33893 e33894 e33895 b33896 b33897 b33898 b33899 d33844 d33848 d33872
        omega
      have d33900 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
        have r33901 := hand1 (x (-7) 3) (x (-7) 14)
        have b33902 := hb (x (-7) 3)
        have b33903 := hb (x (-7) 3 && x (-7) 14)
        clear * - r33901 b33902 b33903 d33892
        omega
      have d33904 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
        have r33905 := hand1 (x (-7) 3) (x (-7) 13)
        have b33906 := hb (x (-7) 3)
        have b33907 := hb (x (-7) 3 && x (-7) 13)
        clear * - r33905 b33906 b33907 d33892
        omega
      have d33908 : (x (-7) 11).toNat = 0 := by
        have r33909 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have b33910 := hb (x (-7) 3)
        have b33911 := hb (x (-7) 11)
        clear * - r33909 b33910 b33911 d33892
        omega
      have d33912 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
        have r33913 := hand2 (x (-7) 1) (x (-7) 11)
        have b33914 := hb (x (-7) 11)
        have b33915 := hb (x (-7) 1 && x (-7) 11)
        clear * - r33913 b33914 b33915 d33908
        omega
      have d33916 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
        have r33917 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b33918 := hb (x (-5) 5)
        have b33919 := hb (x 0 10)
        have b33920 := hb (x (-1) 1 && x (-1) 11)
        have b33921 := hb (x (-2) 2 && x (-2) 12)
        have b33922 := hb (x (-3) 3 && x (-3) 13)
        have b33923 := hb (x (-4) 4 && x (-4) 14)
        clear * - r33917 b33918 b33919 b33920 b33921 b33922 b33923 d31796 g28 d33789 d33817 d33864
        omega
      have d33924 : (x (-4) 14).toNat = 1 := by
        have r33925 := hand2 (x (-4) 4) (x (-4) 14)
        have b33926 := hb (x (-4) 14)
        have b33927 := hb (x (-4) 4 && x (-4) 14)
        clear * - r33925 b33926 b33927 d33916
        omega
      have d33928 : (x (-5) 1).toNat = 0 := by
        have r33929 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b33930 := hb (x (-5) 1)
        have b33931 := hb (x (-4) 14)
        clear * - r33929 b33930 b33931 d33924
        omega
      have d33932 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
        have r33933 := hand1 (x (-5) 1) (x (-5) 14)
        have b33934 := hb (x (-5) 1)
        have b33935 := hb (x (-5) 1 && x (-5) 14)
        clear * - r33933 b33934 b33935 d33928
        omega
      have d33936 : (x (-4) 13).toNat = 1 := by
        have r33937 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b33938 := hb (x (-6) 2)
        have b33939 := hb (x (-4) 13)
        have b33940 := hb (x (-5) 1 && x (-5) 14)
        clear * - r33937 b33938 b33939 b33940 d33932 d33872
        omega
      have d33941 : (x (-4) 1).toNat = 1 := by
        have r33942 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b33943 := hb (x (-4) 1)
        have b33944 := hb (x (-4) 13)
        clear * - r33942 b33943 b33944 d33936
        omega
      have d33945 : (x (-3) 14).toNat = 0 := by
        have r33946 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b33947 := hb (x (-4) 1)
        have b33948 := hb (x (-3) 14)
        clear * - r33946 b33947 b33948 d33941
        omega
      have d33949 : (x (-3) 6).toNat = 0 := by
        have r33950 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
        have b33951 := hb (x (-3) 6)
        have b33952 := hb (x (-3) 14)
        clear * - r33950 b33951 b33952 d33945
        omega
      have d33953 : (x (-3) 2).toNat = 0 := by
        have r33954 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b33955 := hb (x (-3) 2)
        have b33956 := hb (x (-3) 14)
        clear * - r33954 b33955 b33956 d33945
        omega
      have d33957 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
        have r33958 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b33959 := hb (x (-3) 2)
        have b33960 := hb (x (-1) 13)
        have b33961 := hb (x (-2) 1 && x (-2) 14)
        clear * - r33958 b33959 b33960 b33961 g2 d33953
        omega
      have d33962 : (x (-2) 14).toNat = 1 := by
        have r33963 := hand2 (x (-2) 1) (x (-2) 14)
        have b33964 := hb (x (-2) 14)
        have b33965 := hb (x (-2) 1 && x (-2) 14)
        clear * - r33963 b33964 b33965 d33957
        omega
      have d33966 : (x (-3) 1).toNat = 0 := by
        have r33967 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b33968 := hb (x (-3) 1)
        have b33969 := hb (x (-2) 14)
        clear * - r33967 b33968 b33969 d33962
        omega
      have d33970 : (x (-3) 13).toNat = 0 := by
        have r33971 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
        have b33972 := hb (x (-3) 1)
        have b33973 := hb (x (-3) 13)
        clear * - r33971 b33972 b33973 d33966
        omega
      have d33974 : (x (-3) 5).toNat = 0 := by
        have r33975 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
        have b33976 := hb (x (-3) 5)
        have b33977 := hb (x (-3) 13)
        clear * - r33975 b33976 b33977 d33970
        omega
      have d33978 : (x (-3) 12).toNat = 0 := by
        have r33979 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e33980 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e33981 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b33982 := hb (x (-6) 3)
        have b33983 := hb (x (-5) 2)
        have b33984 := hb (x (-4) 13)
        have b33985 := hb (x (-3) 12)
        clear * - r33979 e33980 e33981 b33982 b33983 b33984 b33985 d33936
        omega
      have d33986 : (x (-5) 2).toNat = 0 := by
        have r33987 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e33988 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e33989 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b33990 := hb (x (-6) 3)
        have b33991 := hb (x (-5) 2)
        have b33992 := hb (x (-4) 13)
        have b33993 := hb (x (-3) 12)
        clear * - r33987 e33988 e33989 b33990 b33991 b33992 b33993 d33978 d33936
        omega
      have d33994 : (x (-6) 3).toNat = 0 := by
        have r33995 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e33996 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e33997 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b33998 := hb (x (-6) 3)
        have b33999 := hb (x (-5) 2)
        have b34000 := hb (x (-4) 13)
        have b34001 := hb (x (-3) 12)
        clear * - r33995 e33996 e33997 b33998 b33999 b34000 b34001 d33978 d33936 d33986
        omega
      have d34002 : (x (-6) 11).toNat = 0 := by
        have r34003 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
        have b34004 := hb (x (-6) 3)
        have b34005 := hb (x (-6) 11)
        clear * - r34003 b34004 b34005 d33994
        omega
      have d34006 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
        have r34007 := hand1 (x (-5) 1) (x (-5) 12)
        have b34008 := hb (x (-5) 1)
        have b34009 := hb (x (-5) 1 && x (-5) 12)
        clear * - r34007 b34008 b34009 d33928
        omega
      have d34010 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
        have r34011 := hand1 (x (-5) 1) (x (-5) 11)
        have b34012 := hb (x (-5) 1)
        have b34013 := hb (x (-5) 1 && x (-5) 11)
        clear * - r34011 b34012 b34013 d33928
        omega
      have d34014 : (x 4 8).toNat = 0 := by
        have r34015 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34016 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e34017 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e34018 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e34019 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e34020 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e34021 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b34022 := hb (x (-3) 7)
        have b34023 := hb (x (-2) 6)
        have b34024 := hb (x (-1) 5)
        have b34025 := hb (x 0 4)
        have b34026 := hb (x 1 11)
        have b34027 := hb (x 2 10)
        have b34028 := hb (x 3 9)
        have b34029 := hb (x 4 8)
        clear * - r34015 e34016 e34017 e34018 e34019 e34020 e34021 b34022 b34023 b34024 b34025 b34026 b34027 b34028 b34029 f33772 g0
        omega
      have d34030 : (x 3 9).toNat = 0 := by
        have r34031 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34032 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e34033 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e34034 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e34035 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e34036 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e34037 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b34038 := hb (x (-3) 7)
        have b34039 := hb (x (-2) 6)
        have b34040 := hb (x (-1) 5)
        have b34041 := hb (x 0 4)
        have b34042 := hb (x 1 11)
        have b34043 := hb (x 2 10)
        have b34044 := hb (x 3 9)
        have b34045 := hb (x 4 8)
        clear * - r34031 e34032 e34033 e34034 e34035 e34036 e34037 b34038 b34039 b34040 b34041 b34042 b34043 b34044 b34045 d34014 f33772 g0
        omega
      have d34046 : (x 2 10).toNat = 0 := by
        have r34047 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34048 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e34049 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e34050 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e34051 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e34052 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e34053 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b34054 := hb (x (-3) 7)
        have b34055 := hb (x (-2) 6)
        have b34056 := hb (x (-1) 5)
        have b34057 := hb (x 0 4)
        have b34058 := hb (x 1 11)
        have b34059 := hb (x 2 10)
        have b34060 := hb (x 3 9)
        have b34061 := hb (x 4 8)
        clear * - r34047 e34048 e34049 e34050 e34051 e34052 e34053 b34054 b34055 b34056 b34057 b34058 b34059 b34060 b34061 d34014 d34030 f33772 g0
        omega
      have d34062 : (x 2 1 && x 2 10).toNat = 0 := by
        have r34063 := hand2 (x 2 1) (x 2 10)
        have b34064 := hb (x 2 10)
        have b34065 := hb (x 2 1 && x 2 10)
        clear * - r34063 b34064 b34065 d34046
        omega
      have d34066 : (x (-2) 5 && x (-2) 14).toNat = 1 := by
        have r34067 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34068 := hb (x (-3) 6)
        have b34069 := hb (x 3 9)
        have b34070 := hb (x 2 1 && x 2 10)
        have b34071 := hb (x 1 2 && x 1 11)
        have b34072 := hb (x 0 3 && x 0 12)
        have b34073 := hb (x (-1) 4 && x (-1) 13)
        have b34074 := hb (x (-2) 5 && x (-2) 14)
        clear * - r34067 b34068 b34069 b34070 b34071 b34072 b34073 b34074 d34030 d34062 d31694 g23 g24 d33949
        omega
      have d34075 : (x (-2) 5).toNat = 1 := by
        have r34076 := hand1 (x (-2) 5) (x (-2) 14)
        have b34077 := hb (x (-2) 5)
        have b34078 := hb (x (-2) 5 && x (-2) 14)
        clear * - r34076 b34077 b34078 d34066
        omega
      have d34079 : (x (-2) 13).toNat = 1 := by
        have r34080 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
        have b34081 := hb (x (-2) 5)
        have b34082 := hb (x (-2) 13)
        clear * - r34080 b34081 b34082 d34075
        omega
      have d34083 : (x (-1) 12).toNat = 0 := by
        have r34084 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34085 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e34086 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b34087 := hb (x (-4) 3)
        have b34088 := hb (x (-3) 2)
        have b34089 := hb (x (-2) 13)
        have b34090 := hb (x (-1) 12)
        clear * - r34084 e34085 e34086 b34087 b34088 b34089 b34090 d34079 d33953
        omega
      have d34091 : (x (-4) 3).toNat = 0 := by
        have r34092 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34093 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e34094 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b34095 := hb (x (-4) 3)
        have b34096 := hb (x (-3) 2)
        have b34097 := hb (x (-2) 13)
        have b34098 := hb (x (-1) 12)
        clear * - r34092 e34093 e34094 b34095 b34096 b34097 b34098 d34083 d34079 d33953
        omega
      have d34099 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
        have r34100 := hand1 (x (-4) 3) (x (-4) 12)
        have b34101 := hb (x (-4) 3)
        have b34102 := hb (x (-4) 3 && x (-4) 12)
        clear * - r34100 b34101 b34102 d34091
        omega
      have d34103 : (x (-4) 11).toNat = 0 := by
        have r34104 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
        have b34105 := hb (x (-4) 3)
        have b34106 := hb (x (-4) 11)
        clear * - r34104 b34105 b34106 d34091
        omega
      have d34107 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
        have r34108 := hand2 (x (-4) 4) (x (-4) 11)
        have b34109 := hb (x (-4) 11)
        have b34110 := hb (x (-4) 4 && x (-4) 11)
        clear * - r34108 b34109 b34110 d34103
        omega
      have d34111 : (x (-8) 4).toNat = 1 := by
        have r34112 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34113 := hb (x (-8) 4)
        have b34114 := hb (x (-4) 11)
        have b34115 := hb (x (-5) 1 && x (-5) 12)
        have b34116 := hb (x (-6) 2 && x (-6) 13)
        have b34117 := hb (x (-7) 3 && x (-7) 14)
        clear * - r34112 b34113 b34114 b34115 b34116 b34117 d34103 d34006 d33880 d33900
        omega
      have d34118 : (x (-8) 12).toNat = 1 := by
        have r34119 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
        have b34120 := hb (x (-8) 4)
        have b34121 := hb (x (-8) 12)
        clear * - r34119 b34120 b34121 d34111
        omega
      have d34122 : (x (-9) 13).toNat = 0 := by
        have r34123 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34124 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e34125 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b34126 := hb (x (-11) 3)
        have b34127 := hb (x (-10) 2)
        have b34128 := hb (x (-9) 13)
        have b34129 := hb (x (-8) 12)
        clear * - r34123 e34124 e34125 b34126 b34127 b34128 b34129 d34118
        omega
      have d34130 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
        have r34131 := hand2 (x (-9) 3) (x (-9) 13)
        have b34132 := hb (x (-9) 13)
        have b34133 := hb (x (-9) 3 && x (-9) 13)
        clear * - r34131 b34132 b34133 d34122
        omega
      have d34134 : (x (-9) 5).toNat = 0 := by
        have r34135 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
        have b34136 := hb (x (-9) 5)
        have b34137 := hb (x (-9) 13)
        clear * - r34135 b34136 b34137 d34122
        omega
      have d34138 : (x (-10) 2).toNat = 0 := by
        have r34139 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34140 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e34141 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b34142 := hb (x (-11) 3)
        have b34143 := hb (x (-10) 2)
        have b34144 := hb (x (-9) 13)
        have b34145 := hb (x (-8) 12)
        clear * - r34139 e34140 e34141 b34142 b34143 b34144 b34145 d34118 d34122
        omega
      have d34146 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
        have r34147 := hand1 (x (-10) 2) (x (-10) 13)
        have b34148 := hb (x (-10) 2)
        have b34149 := hb (x (-10) 2 && x (-10) 13)
        clear * - r34147 b34148 b34149 d34138
        omega
      have d34150 : (x (-10) 10).toNat = 0 := by
        have r34151 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
        have b34152 := hb (x (-10) 2)
        have b34153 := hb (x (-10) 10)
        clear * - r34151 b34152 b34153 d34138
        omega
      have d34154 : (x (-11) 3).toNat = 0 := by
        have r34155 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34156 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e34157 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b34158 := hb (x (-11) 3)
        have b34159 := hb (x (-10) 2)
        have b34160 := hb (x (-9) 13)
        have b34161 := hb (x (-8) 12)
        clear * - r34155 e34156 e34157 b34158 b34159 b34160 b34161 d34118 d34122 d34138
        omega
      have d34162 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
        have r34163 := hand1 (x (-11) 3) (x (-11) 14)
        have b34164 := hb (x (-11) 3)
        have b34165 := hb (x (-11) 3 && x (-11) 14)
        clear * - r34163 b34164 b34165 d34154
        omega
      have d34166 : (x (-11) 11).toNat = 0 := by
        have r34167 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
        have b34168 := hb (x (-11) 3)
        have b34169 := hb (x (-11) 11)
        clear * - r34167 b34168 b34169 d34154
        omega
      have d34170 : (x 1 11).toNat = 0 := by
        have r34171 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34172 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e34173 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e34174 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e34175 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e34176 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e34177 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have b34178 := hb (x (-3) 7)
        have b34179 := hb (x (-2) 6)
        have b34180 := hb (x (-1) 5)
        have b34181 := hb (x 0 4)
        have b34182 := hb (x 1 11)
        have b34183 := hb (x 2 10)
        have b34184 := hb (x 3 9)
        have b34185 := hb (x 4 8)
        clear * - r34171 e34172 e34173 e34174 e34175 e34176 e34177 b34178 b34179 b34180 b34181 b34182 b34183 b34184 b34185 d34014 d34030 d34046 f33772 g0
        omega
      have d34186 : (x 1 1 && x 1 11).toNat = 0 := by
        have r34187 := hand2 (x 1 1) (x 1 11)
        have b34188 := hb (x 1 11)
        have b34189 := hb (x 1 1 && x 1 11)
        clear * - r34187 b34188 b34189 d34170
        omega
      have d34190 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
        have r34191 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34192 := hb (x (-3) 5)
        have b34193 := hb (x 2 10)
        have b34194 := hb (x 1 1 && x 1 11)
        have b34195 := hb (x 0 2 && x 0 12)
        have b34196 := hb (x (-1) 3 && x (-1) 13)
        have b34197 := hb (x (-2) 4 && x (-2) 14)
        clear * - r34191 b34192 b34193 b34194 b34195 b34196 b34197 d34046 d34186 d31788 g30 d33974
        omega
      have d34198 : (x (-2) 4).toNat = 1 := by
        have r34199 := hand1 (x (-2) 4) (x (-2) 14)
        have b34200 := hb (x (-2) 4)
        have b34201 := hb (x (-2) 4 && x (-2) 14)
        clear * - r34199 b34200 b34201 d34190
        omega
      have d34202 : (x (-2) 12).toNat = 1 := by
        have r34203 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have b34204 := hb (x (-2) 4)
        have b34205 := hb (x (-2) 12)
        clear * - r34203 b34204 b34205 d34198
        omega
      have d34206 : (x (-4) 2).toNat = 0 := by
        have r34207 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34208 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e34209 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b34210 := hb (x (-5) 3)
        have b34211 := hb (x (-4) 2)
        have b34212 := hb (x (-3) 13)
        have b34213 := hb (x (-2) 12)
        clear * - r34207 e34208 e34209 b34210 b34211 b34212 b34213 d34202 d33970
        omega
      have d34214 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
        have r34215 := hand1 (x (-4) 2) (x (-4) 12)
        have b34216 := hb (x (-4) 2)
        have b34217 := hb (x (-4) 2 && x (-4) 12)
        clear * - r34215 b34216 b34217 d34206
        omega
      have d34218 : (x (-4) 10).toNat = 0 := by
        have r34219 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
        have b34220 := hb (x (-4) 2)
        have b34221 := hb (x (-4) 10)
        clear * - r34219 b34220 b34221 d34206
        omega
      have d34222 : (x (-8) 4 && x (-8) 14).toNat = 1 := by
        have r34223 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34224 := hb (x (-9) 5)
        have b34225 := hb (x (-4) 10)
        have b34226 := hb (x (-5) 1 && x (-5) 11)
        have b34227 := hb (x (-6) 2 && x (-6) 12)
        have b34228 := hb (x (-7) 3 && x (-7) 13)
        have b34229 := hb (x (-8) 4 && x (-8) 14)
        clear * - r34223 b34224 b34225 b34226 b34227 b34228 b34229 d34218 d34010 d33884 d33904 d34134
        omega
      have d34230 : (x (-8) 14).toNat = 1 := by
        have r34231 := hand2 (x (-8) 4) (x (-8) 14)
        have b34232 := hb (x (-8) 14)
        have b34233 := hb (x (-8) 4 && x (-8) 14)
        clear * - r34231 b34232 b34233 d34222
        omega
      have d34234 : (x (-9) 1).toNat = 0 := by
        have r34235 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34236 := hb (x (-9) 1)
        have b34237 := hb (x (-8) 14)
        clear * - r34235 b34236 b34237 d34230
        omega
      have d34238 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
        have r34239 := hand1 (x (-9) 1) (x (-9) 14)
        have b34240 := hb (x (-9) 1)
        have b34241 := hb (x (-9) 1 && x (-9) 14)
        clear * - r34239 b34240 b34241 d34234
        omega
      have d34242 : (x (-8) 13).toNat = 1 := by
        have r34243 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34244 := hb (x (-10) 2)
        have b34245 := hb (x (-8) 13)
        have b34246 := hb (x (-9) 1 && x (-9) 14)
        clear * - r34243 b34244 b34245 b34246 d34238 d34138
        omega
      have d34247 : (x (-8) 1).toNat = 1 := by
        have r34248 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b34249 := hb (x (-8) 1)
        have b34250 := hb (x (-8) 13)
        clear * - r34248 b34249 b34250 d34242
        omega
      have d34251 : (x (-7) 14).toNat = 0 := by
        have r34252 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34253 := hb (x (-8) 1)
        have b34254 := hb (x (-7) 14)
        clear * - r34252 b34253 b34254 d34247
        omega
      have d34255 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
        have r34256 := hand2 (x (-7) 1) (x (-7) 14)
        have b34257 := hb (x (-7) 14)
        have b34258 := hb (x (-7) 1 && x (-7) 14)
        clear * - r34256 b34257 b34258 d34251
        omega
      have d34259 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
        have r34260 := hand2 (x (-7) 7) (x (-7) 14)
        have b34261 := hb (x (-7) 14)
        have b34262 := hb (x (-7) 7 && x (-7) 14)
        clear * - r34260 b34261 b34262 d34251
        omega
      have d34263 : (x (-7) 6).toNat = 0 := by
        have r34264 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
        have b34265 := hb (x (-7) 6)
        have b34266 := hb (x (-7) 14)
        clear * - r34264 b34265 b34266 d34251
        omega
      have d34267 : (x (-6) 5 && x (-6) 14).toNat = 1 := by
        have r34268 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34269 := hb (x (-7) 6)
        have b34270 := hb (x (-1) 9)
        have b34271 := hb (x (-2) 1 && x (-2) 10)
        have b34272 := hb (x (-3) 2 && x (-3) 11)
        have b34273 := hb (x (-4) 3 && x (-4) 12)
        have b34274 := hb (x (-5) 4 && x (-5) 13)
        have b34275 := hb (x (-6) 5 && x (-6) 14)
        clear * - r34268 b34269 b34270 b34271 b34272 b34273 b34274 b34275 g1 d33801 d33833 d34099 d33860 d34263
        omega
      have d34276 : (x (-6) 14).toNat = 1 := by
        have r34277 := hand2 (x (-6) 5) (x (-6) 14)
        have b34278 := hb (x (-6) 14)
        have b34279 := hb (x (-6) 5 && x (-6) 14)
        clear * - r34277 b34278 b34279 d34267
        omega
      have d34280 : (x (-7) 1).toNat = 0 := by
        have r34281 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34282 := hb (x (-7) 1)
        have b34283 := hb (x (-6) 14)
        clear * - r34281 b34282 b34283 d34276
        omega
      have d34284 : (x (-7) 1 && x (-7) 12).toNat = 0 := by
        have r34285 := hand1 (x (-7) 1) (x (-7) 12)
        have b34286 := hb (x (-7) 1)
        have b34287 := hb (x (-7) 1 && x (-7) 12)
        clear * - r34285 b34286 b34287 d34280
        omega
      have d34288 : (x (-7) 13).toNat = 0 := by
        have r34289 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
        have b34290 := hb (x (-7) 1)
        have b34291 := hb (x (-7) 13)
        clear * - r34289 b34290 b34291 d34280
        omega
      have d34292 : (x (-7) 5).toNat = 0 := by
        have r34293 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
        have b34294 := hb (x (-7) 5)
        have b34295 := hb (x (-7) 13)
        clear * - r34293 b34294 b34295 d34288
        omega
      have d34296 : (x (-6) 4 && x (-6) 14).toNat = 1 := by
        have r34297 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34298 := hb (x (-7) 5)
        have b34299 := hb (x (-2) 10)
        have b34300 := hb (x (-3) 1 && x (-3) 11)
        have b34301 := hb (x (-4) 2 && x (-4) 12)
        have b34302 := hb (x (-5) 3 && x (-5) 13)
        have b34303 := hb (x (-6) 4 && x (-6) 14)
        clear * - r34297 b34298 b34299 b34300 b34301 b34302 b34303 d33797 d33829 d34214 d33856 d34292
        omega
      have d34304 : (x (-6) 4).toNat = 1 := by
        have r34305 := hand1 (x (-6) 4) (x (-6) 14)
        have b34306 := hb (x (-6) 4)
        have b34307 := hb (x (-6) 4 && x (-6) 14)
        clear * - r34305 b34306 b34307 d34296
        omega
      have d34308 : (x (-6) 12).toNat = 1 := by
        have r34309 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
        have b34310 := hb (x (-6) 4)
        have b34311 := hb (x (-6) 12)
        clear * - r34309 b34310 b34311 d34304
        omega
      have d34312 : (x (-8) 2).toNat = 0 := by
        have r34313 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34314 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e34315 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b34316 := hb (x (-9) 3)
        have b34317 := hb (x (-8) 2)
        have b34318 := hb (x (-7) 13)
        have b34319 := hb (x (-6) 12)
        clear * - r34313 e34314 e34315 b34316 b34317 b34318 b34319 d34308 d34288
        omega
      have d34320 : (x (-8) 2 && x (-8) 13).toNat = 0 := by
        have r34321 := hand1 (x (-8) 2) (x (-8) 13)
        have b34322 := hb (x (-8) 2)
        have b34323 := hb (x (-8) 2 && x (-8) 13)
        clear * - r34321 b34322 b34323 d34312
        omega
      have d34324 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
        have r34325 := hand1 (x (-8) 2) (x (-8) 12)
        have b34326 := hb (x (-8) 2)
        have b34327 := hb (x (-8) 2 && x (-8) 12)
        clear * - r34325 b34326 b34327 d34312
        omega
      have d34328 : (x (-6) 13).toNat = 1 := by
        have r34329 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34330 := hb (x (-8) 2)
        have b34331 := hb (x (-6) 13)
        have b34332 := hb (x (-7) 1 && x (-7) 14)
        clear * - r34329 b34330 b34331 b34332 d34255 d34312
        omega
      have d34333 : (x (-5) 12).toNat = 0 := by
        have r34334 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34335 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e34336 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b34337 := hb (x (-8) 3)
        have b34338 := hb (x (-7) 2)
        have b34339 := hb (x (-6) 13)
        have b34340 := hb (x (-5) 12)
        clear * - r34334 e34335 e34336 b34337 b34338 b34339 b34340 d34328
        omega
      have d34341 : (x (-7) 2).toNat = 0 := by
        have r34342 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34343 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e34344 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b34345 := hb (x (-8) 3)
        have b34346 := hb (x (-7) 2)
        have b34347 := hb (x (-6) 13)
        have b34348 := hb (x (-5) 12)
        clear * - r34342 e34343 e34344 b34345 b34346 b34347 b34348 d34333 d34328
        omega
      have d34349 : (x (-8) 3).toNat = 0 := by
        have r34350 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34351 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e34352 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b34353 := hb (x (-8) 3)
        have b34354 := hb (x (-7) 2)
        have b34355 := hb (x (-6) 13)
        have b34356 := hb (x (-5) 12)
        clear * - r34350 e34351 e34352 b34353 b34354 b34355 b34356 d34333 d34328 d34341
        omega
      have d34357 : (x (-8) 11).toNat = 0 := by
        have r34358 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
        have b34359 := hb (x (-8) 3)
        have b34360 := hb (x (-8) 11)
        clear * - r34358 b34359 b34360 d34349
        omega
      have d34361 : (x (-9) 3).toNat = 0 := by
        have r34362 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34363 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e34364 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b34365 := hb (x (-9) 3)
        have b34366 := hb (x (-8) 2)
        have b34367 := hb (x (-7) 13)
        have b34368 := hb (x (-6) 12)
        clear * - r34362 e34363 e34364 b34365 b34366 b34367 b34368 d34308 d34288 d34312
        omega
      have d34369 : (x (-9) 3 && x (-9) 14).toNat = 0 := by
        have r34370 := hand1 (x (-9) 3) (x (-9) 14)
        have b34371 := hb (x (-9) 3)
        have b34372 := hb (x (-9) 3 && x (-9) 14)
        clear * - r34370 b34371 b34372 d34361
        omega
      have d34373 : (x (-10) 4).toNat = 1 := by
        have r34374 : 1 ≤ (x (-6) 11).toNat + (x (-7) 1 && x (-7) 12).toNat + (x (-8) 2 && x (-8) 13).toNat + (x (-9) 3 && x (-9) 14).toNat + (x (-10) 4).toNat := by have q := hcov11 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34375 := hb (x (-10) 4)
        have b34376 := hb (x (-6) 11)
        have b34377 := hb (x (-7) 1 && x (-7) 12)
        have b34378 := hb (x (-8) 2 && x (-8) 13)
        have b34379 := hb (x (-9) 3 && x (-9) 14)
        clear * - r34374 b34375 b34376 b34377 b34378 b34379 d34002 d34284 d34320 d34369
        omega
      have d34380 : (x (-10) 12).toNat = 1 := by
        have r34381 : (x (-10) 4).toNat ≤ (x (-10) 12).toNat := himp _ _ (hp4 (-10))
        have b34382 := hb (x (-10) 4)
        have b34383 := hb (x (-10) 12)
        clear * - r34381 b34382 b34383 d34373
        omega
      have d34384 : (x (-11) 13).toNat = 0 := by
        have r34385 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34386 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
        have e34387 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
        have b34388 := hb (x (-13) 3)
        have b34389 := hb (x (-12) 2)
        have b34390 := hb (x (-11) 13)
        have b34391 := hb (x (-10) 12)
        clear * - r34385 e34386 e34387 b34388 b34389 b34390 b34391 d34380
        omega
      have d34392 : (x (-11) 5).toNat = 0 := by
        have r34393 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
        have b34394 := hb (x (-11) 5)
        have b34395 := hb (x (-11) 13)
        clear * - r34393 b34394 b34395 d34384
        omega
      have d34396 : (x (-10) 4 && x (-10) 14).toNat = 1 := by
        have r34397 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34398 := hb (x (-11) 5)
        have b34399 := hb (x (-6) 10)
        have b34400 := hb (x (-7) 1 && x (-7) 11)
        have b34401 := hb (x (-8) 2 && x (-8) 12)
        have b34402 := hb (x (-9) 3 && x (-9) 13)
        have b34403 := hb (x (-10) 4 && x (-10) 14)
        clear * - r34397 b34398 b34399 b34400 b34401 b34402 b34403 d33888 d33912 d34324 d34130 d34392
        omega
      have d34404 : (x (-10) 14).toNat = 1 := by
        have r34405 := hand2 (x (-10) 4) (x (-10) 14)
        have b34406 := hb (x (-10) 14)
        have b34407 := hb (x (-10) 4 && x (-10) 14)
        clear * - r34405 b34406 b34407 d34396
        omega
      have d34408 : (x (-11) 1).toNat = 0 := by
        have r34409 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34410 := hb (x (-11) 1)
        have b34411 := hb (x (-10) 14)
        clear * - r34409 b34410 b34411 d34404
        omega
      have d34412 : (x (-11) 1 && x (-11) 14).toNat = 0 := by
        have r34413 := hand1 (x (-11) 1) (x (-11) 14)
        have b34414 := hb (x (-11) 1)
        have b34415 := hb (x (-11) 1 && x (-11) 14)
        clear * - r34413 b34414 b34415 d34408
        omega
      have d34416 : (x (-12) 2).toNat = 0 := by
        have r34417 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34418 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
        have e34419 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
        have b34420 := hb (x (-13) 3)
        have b34421 := hb (x (-12) 2)
        have b34422 := hb (x (-11) 13)
        have b34423 := hb (x (-10) 12)
        clear * - r34417 e34418 e34419 b34420 b34421 b34422 b34423 d34380 d34384
        omega
      have d34424 : (x (-10) 13).toNat = 1 := by
        have r34425 : 1 ≤ (x (-10) 13).toNat + (x (-11) 1 && x (-11) 14).toNat + (x (-12) 2).toNat := by have q := hcov13 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34426 := hb (x (-12) 2)
        have b34427 := hb (x (-10) 13)
        have b34428 := hb (x (-11) 1 && x (-11) 14)
        clear * - r34425 b34426 b34427 b34428 d34412 d34416
        omega
      have d34429 : (x (-9) 12).toNat = 0 := by
        have r34430 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34431 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
        have e34432 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
        have b34433 := hb (x (-12) 3)
        have b34434 := hb (x (-11) 2)
        have b34435 := hb (x (-10) 13)
        have b34436 := hb (x (-9) 12)
        clear * - r34430 e34431 e34432 b34433 b34434 b34435 b34436 d34424
        omega
      have d34437 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
        have r34438 := hand2 (x (-9) 1) (x (-9) 12)
        have b34439 := hb (x (-9) 12)
        have b34440 := hb (x (-9) 1 && x (-9) 12)
        clear * - r34438 b34439 b34440 d34429
        omega
      have d34441 : (x (-12) 4).toNat = 1 := by
        have r34442 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34443 := hb (x (-12) 4)
        have b34444 := hb (x (-8) 11)
        have b34445 := hb (x (-9) 1 && x (-9) 12)
        have b34446 := hb (x (-10) 2 && x (-10) 13)
        have b34447 := hb (x (-11) 3 && x (-11) 14)
        clear * - r34442 b34443 b34444 b34445 b34446 b34447 d34357 d34437 d34146 d34162
        omega
      have d34448 : (x (-12) 12).toNat = 1 := by
        have r34449 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
        have b34450 := hb (x (-12) 4)
        have b34451 := hb (x (-12) 12)
        clear * - r34449 b34450 b34451 d34441
        omega
      have d34452 : (x (-13) 13).toNat = 0 := by
        have r34453 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34454 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
        have e34455 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
        have b34456 := hb (x (-15) 3)
        have b34457 := hb (x (-14) 2)
        have b34458 := hb (x (-13) 13)
        have b34459 := hb (x (-12) 12)
        clear * - r34453 e34454 e34455 b34456 b34457 b34458 b34459 d34448
        omega
      have d34460 : (x (-13) 5).toNat = 0 := by
        have r34461 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
        have b34462 := hb (x (-13) 5)
        have b34463 := hb (x (-13) 13)
        clear * - r34461 b34462 b34463 d34452
        omega
      have d34464 : (x (-9) 9).toNat = 0 := by
        have r34465 : (x (-9) 9).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp9 (-9))
        have b34466 := hb (x (-9) 1)
        have b34467 := hb (x (-9) 9)
        clear * - r34465 b34466 b34467 d34234
        omega
      have d34468 : (x 0 8).toNat = 0 := by
        have r34469 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34470 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e34471 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e34472 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e34473 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e34474 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e34475 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b34476 := hb (x (-7) 7)
        have b34477 := hb (x (-6) 6)
        have b34478 := hb (x (-5) 5)
        have b34479 := hb (x (-4) 4)
        have b34480 := hb (x (-3) 11)
        have b34481 := hb (x (-2) 10)
        have b34482 := hb (x (-1) 9)
        have b34483 := hb (x 0 8)
        clear * - r34469 e34470 e34471 e34472 e34473 e34474 e34475 b34476 b34477 b34478 b34479 b34480 b34481 b34482 b34483 g1 d33797 d33825 d33837 d33864
        omega
      have d34484 : (x (-6) 6).toNat = 0 := by
        have r34485 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34486 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e34487 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e34488 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e34489 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e34490 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e34491 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have b34492 := hb (x (-7) 7)
        have b34493 := hb (x (-6) 6)
        have b34494 := hb (x (-5) 5)
        have b34495 := hb (x (-4) 4)
        have b34496 := hb (x (-3) 11)
        have b34497 := hb (x (-2) 10)
        have b34498 := hb (x (-1) 9)
        have b34499 := hb (x 0 8)
        clear * - r34485 e34486 e34487 e34488 e34489 e34490 e34491 b34492 b34493 b34494 b34495 b34496 b34497 b34498 b34499 d34468 g1 d33797 d33825 d33837 d33864
        omega
      have d34500 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
        have r34501 := hand1 (x (-6) 6) (x (-6) 13)
        have b34502 := hb (x (-6) 6)
        have b34503 := hb (x (-6) 6 && x (-6) 13)
        clear * - r34501 b34502 b34503 d34484
        omega
      have d34504 : (x (-8) 8).toNat = 0 := by
        have r34505 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34506 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e34507 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e34508 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e34509 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e34510 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e34511 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b34512 := hb (x (-15) 7)
        have b34513 := hb (x (-14) 6)
        have b34514 := hb (x (-13) 5)
        have b34515 := hb (x (-12) 4)
        have b34516 := hb (x (-11) 11)
        have b34517 := hb (x (-10) 10)
        have b34518 := hb (x (-9) 9)
        have b34519 := hb (x (-8) 8)
        clear * - r34505 e34506 e34507 e34508 e34509 e34510 e34511 b34512 b34513 b34514 b34515 b34516 b34517 b34518 b34519 d34464 d34150 d34166 d34441 d34460
        omega
      have r34520 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34521 := hb (x (-8) 8)
      have b34522 := hb (x 0 7)
      have b34523 := hb (x (-1) 1 && x (-1) 8)
      have b34524 := hb (x (-2) 2 && x (-2) 9)
      have b34525 := hb (x (-3) 3 && x (-3) 10)
      have b34526 := hb (x (-4) 4 && x (-4) 11)
      have b34527 := hb (x (-5) 5 && x (-5) 12)
      have b34528 := hb (x (-6) 6 && x (-6) 13)
      have b34529 := hb (x (-7) 7 && x (-7) 14)
      linarith only [r34520, b34521, b34522, b34523, b34524, b34525, b34526, b34527, b34528, b34529, g4, g21, d33793, d33821, d34107, d33868, d34500, d34259, d34504]
  · have f34530 : (x 0 2).toNat = 1 := by rw [h31782]; rfl
    have d34531 : (x 2 12).toNat = 0 := by
      have r34532 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34533 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e34534 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b34535 := hb (x (-1) 3)
      have b34536 := hb (x 0 2)
      have b34537 := hb (x 1 13)
      have b34538 := hb (x 2 12)
      clear * - r34532 e34533 e34534 b34535 b34536 b34537 b34538 f34530
      omega
    have d34539 : (x 2 1 && x 2 12).toNat = 0 := by
      have r34540 := hand2 (x 2 1) (x 2 12)
      have b34541 := hb (x 2 12)
      have b34542 := hb (x 2 1 && x 2 12)
      clear * - r34540 b34541 b34542 d34531
      omega
    have d34543 : (x 1 13).toNat = 0 := by
      have r34544 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34545 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e34546 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b34547 := hb (x (-1) 3)
      have b34548 := hb (x 0 2)
      have b34549 := hb (x 1 13)
      have b34550 := hb (x 2 12)
      clear * - r34544 e34545 e34546 b34547 b34548 b34549 b34550 d34531 f34530
      omega
    have d34551 : (x (-1) 3).toNat = 0 := by
      have r34552 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34553 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e34554 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b34555 := hb (x (-1) 3)
      have b34556 := hb (x 0 2)
      have b34557 := hb (x 1 13)
      have b34558 := hb (x 2 12)
      clear * - r34552 e34553 e34554 b34555 b34556 b34557 b34558 d34531 d34543 f34530
      omega
    have d34559 : (x (-1) 11).toNat = 0 := by
      have r34560 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b34561 := hb (x (-1) 3)
      have b34562 := hb (x (-1) 11)
      clear * - r34560 b34561 b34562 d34551
      omega
    have d34563 : (x (-1) 4).toNat = 1 := by
      have r34564 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34565 := hb (x (-1) 4)
      have b34566 := hb (x 3 11)
      have b34567 := hb (x 2 1 && x 2 12)
      have b34568 := hb (x 1 2 && x 1 13)
      have b34569 := hb (x 0 3 && x 0 14)
      clear * - r34564 b34565 b34566 b34567 b34568 b34569 g9 d34539 d31686 g35
      omega
    have d34570 : (x (-1) 12).toNat = 1 := by
      have r34571 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b34572 := hb (x (-1) 4)
      have b34573 := hb (x (-1) 12)
      clear * - r34571 b34572 b34573 d34563
      omega
    have d34574 : (x (-2) 13).toNat = 0 := by
      have r34575 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34576 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e34577 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b34578 := hb (x (-4) 3)
      have b34579 := hb (x (-3) 2)
      have b34580 := hb (x (-2) 13)
      have b34581 := hb (x (-1) 12)
      clear * - r34575 e34576 e34577 b34578 b34579 b34580 b34581 d34570
      omega
    have d34582 : (x (-3) 2).toNat = 0 := by
      have r34583 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34584 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e34585 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b34586 := hb (x (-4) 3)
      have b34587 := hb (x (-3) 2)
      have b34588 := hb (x (-2) 13)
      have b34589 := hb (x (-1) 12)
      clear * - r34583 e34584 e34585 b34586 b34587 b34588 b34589 d34570 d34574
      omega
    have d34590 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
      have r34591 := hand1 (x (-3) 2) (x (-3) 13)
      have b34592 := hb (x (-3) 2)
      have b34593 := hb (x (-3) 2 && x (-3) 13)
      clear * - r34591 b34592 b34593 d34582
      omega
    have d34594 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
      have r34595 := hand1 (x (-3) 2) (x (-3) 12)
      have b34596 := hb (x (-3) 2)
      have b34597 := hb (x (-3) 2 && x (-3) 12)
      clear * - r34595 b34596 b34597 d34582
      omega
    have d34598 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
      have r34599 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34600 := hb (x (-3) 2)
      have b34601 := hb (x (-1) 13)
      have b34602 := hb (x (-2) 1 && x (-2) 14)
      clear * - r34599 b34600 b34601 b34602 g2 d34582
      omega
    have d34603 : (x (-2) 14).toNat = 1 := by
      have r34604 := hand2 (x (-2) 1) (x (-2) 14)
      have b34605 := hb (x (-2) 14)
      have b34606 := hb (x (-2) 1 && x (-2) 14)
      clear * - r34604 b34605 b34606 d34598
      omega
    have d34607 : (x (-3) 1).toNat = 0 := by
      have r34608 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34609 := hb (x (-3) 1)
      have b34610 := hb (x (-2) 14)
      clear * - r34608 b34609 b34610 d34603
      omega
    have d34611 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
      have r34612 := hand1 (x (-3) 1) (x (-3) 14)
      have b34613 := hb (x (-3) 1)
      have b34614 := hb (x (-3) 1 && x (-3) 14)
      clear * - r34612 b34613 b34614 d34607
      omega
    have d34615 : (x (-4) 2).toNat = 1 := by
      have r34616 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34617 := hb (x (-4) 2)
      have b34618 := hb (x (-2) 13)
      have b34619 := hb (x (-3) 1 && x (-3) 14)
      clear * - r34616 b34617 b34618 b34619 d34574 d34611
      omega
    have d34620 : (x (-4) 14).toNat = 1 := by
      have r34621 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
      have b34622 := hb (x (-4) 2)
      have b34623 := hb (x (-4) 14)
      clear * - r34621 b34622 b34623 d34615
      omega
    have d34624 : (x (-5) 1).toNat = 0 := by
      have r34625 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34626 := hb (x (-5) 1)
      have b34627 := hb (x (-4) 14)
      clear * - r34625 b34626 b34627 d34620
      omega
    have d34628 : (x (-5) 13).toNat = 0 := by
      have r34629 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
      have b34630 := hb (x (-5) 1)
      have b34631 := hb (x (-5) 13)
      clear * - r34629 b34630 b34631 d34624
      omega
    have d34632 : (x (-2) 12).toNat = 0 := by
      have r34633 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34634 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e34635 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b34636 := hb (x (-5) 3)
      have b34637 := hb (x (-4) 2)
      have b34638 := hb (x (-3) 13)
      have b34639 := hb (x (-2) 12)
      clear * - r34633 e34634 e34635 b34636 b34637 b34638 b34639 d34615
      omega
    have d34640 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
      have r34641 := hand2 (x (-2) 1) (x (-2) 12)
      have b34642 := hb (x (-2) 12)
      have b34643 := hb (x (-2) 1 && x (-2) 12)
      clear * - r34641 b34642 b34643 d34632
      omega
    have d34644 : (x (-4) 3).toNat = 0 := by
      have r34645 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34646 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e34647 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b34648 := hb (x (-4) 3)
      have b34649 := hb (x (-3) 2)
      have b34650 := hb (x (-2) 13)
      have b34651 := hb (x (-1) 12)
      clear * - r34645 e34646 e34647 b34648 b34649 b34650 b34651 d34570 d34574 d34582
      omega
    have d34652 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
      have r34653 := hand1 (x (-4) 3) (x (-4) 14)
      have b34654 := hb (x (-4) 3)
      have b34655 := hb (x (-4) 3 && x (-4) 14)
      clear * - r34653 b34654 b34655 d34644
      omega
    have d34656 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
      have r34657 := hand1 (x (-4) 3) (x (-4) 13)
      have b34658 := hb (x (-4) 3)
      have b34659 := hb (x (-4) 3 && x (-4) 13)
      clear * - r34657 b34658 b34659 d34644
      omega
    have d34660 : (x (-5) 4).toNat = 1 := by
      have r34661 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34662 := hb (x (-5) 4)
      have b34663 := hb (x (-1) 11)
      have b34664 := hb (x (-2) 1 && x (-2) 12)
      have b34665 := hb (x (-3) 2 && x (-3) 13)
      have b34666 := hb (x (-4) 3 && x (-4) 14)
      clear * - r34661 b34662 b34663 b34664 b34665 b34666 d34559 d34640 d34590 d34652
      omega
    have d34667 : (x (-5) 12).toNat = 1 := by
      have r34668 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
      have b34669 := hb (x (-5) 4)
      have b34670 := hb (x (-5) 12)
      clear * - r34668 b34669 b34670 d34660
      omega
    have d34671 : (x (-6) 13).toNat = 0 := by
      have r34672 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34673 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e34674 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b34675 := hb (x (-8) 3)
      have b34676 := hb (x (-7) 2)
      have b34677 := hb (x (-6) 13)
      have b34678 := hb (x (-5) 12)
      clear * - r34672 e34673 e34674 b34675 b34676 b34677 b34678 d34667
      omega
    have d34679 : (x (-6) 5).toNat = 0 := by
      have r34680 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
      have b34681 := hb (x (-6) 5)
      have b34682 := hb (x (-6) 13)
      clear * - r34680 b34681 b34682 d34671
      omega
    have d34683 : (x (-7) 2).toNat = 0 := by
      have r34684 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34685 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e34686 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b34687 := hb (x (-8) 3)
      have b34688 := hb (x (-7) 2)
      have b34689 := hb (x (-6) 13)
      have b34690 := hb (x (-5) 12)
      clear * - r34684 e34685 e34686 b34687 b34688 b34689 b34690 d34667 d34671
      omega
    have d34691 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
      have r34692 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34693 := hb (x (-7) 2)
      have b34694 := hb (x (-5) 13)
      have b34695 := hb (x (-6) 1 && x (-6) 14)
      clear * - r34692 b34693 b34694 b34695 d34628 d34683
      omega
    have d34696 : (x (-6) 1).toNat = 1 := by
      have r34697 := hand1 (x (-6) 1) (x (-6) 14)
      have b34698 := hb (x (-6) 1)
      have b34699 := hb (x (-6) 1 && x (-6) 14)
      clear * - r34697 b34698 b34699 d34691
      omega
    have d34700 : (x (-5) 14).toNat = 0 := by
      have r34701 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34702 := hb (x (-6) 1)
      have b34703 := hb (x (-5) 14)
      clear * - r34701 b34702 b34703 d34696
      omega
    have d34704 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
      have r34705 := hand2 (x (-5) 4) (x (-5) 14)
      have b34706 := hb (x (-5) 14)
      have b34707 := hb (x (-5) 4 && x (-5) 14)
      clear * - r34705 b34706 b34707 d34700
      omega
    have r34708 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b34709 := hb (x (-6) 5)
    have b34710 := hb (x (-1) 10)
    have b34711 := hb (x (-2) 1 && x (-2) 11)
    have b34712 := hb (x (-3) 2 && x (-3) 12)
    have b34713 := hb (x (-4) 3 && x (-4) 13)
    have b34714 := hb (x (-5) 4 && x (-5) 14)
    linarith only [r34708, b34709, b34710, b34711, b34712, b34713, b34714, d31746, d31770, d34594, d34656, d34704, d34679]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a01 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 5).toNat = 0)
    (g1 : (x (-1) 9).toNat = 0)
    (g2 : (x (-1) 13).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 7).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 13).toNat = 1)
    (g7 : (x 1 5).toNat = 0)
    (g8 : (x 2 4).toNat = 0)
    (g9 : (x 3 11).toNat = 0)
    (g10 : (x 4 10).toNat = 0)
    (g11 : (x 5 9).toNat = 0)
    (g12 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g13 : (x 6 4 && x 6 8).toNat = 0)
    (g14 : (x 5 5 && x 5 9).toNat = 0)
    (g15 : (x 4 6 && x 4 10).toNat = 0)
    (g16 : (x 3 7 && x 3 11).toNat = 0)
    (g17 : (x 6 2 && x 6 8).toNat = 0)
    (g18 : (x 5 3 && x 5 9).toNat = 0)
    (g19 : (x 4 4 && x 4 10).toNat = 0)
    (g20 : (x 3 5 && x 3 11).toNat = 0)
    (g21 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g22 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g23 : (x 0 3 && x 0 12).toNat = 0)
    (g24 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g25 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g26 : (x 4 1 && x 4 10).toNat = 0)
    (g27 : (x 3 2 && x 3 11).toNat = 0)
    (g28 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g29 : (x 0 1 && x 0 11).toNat = 0)
    (g30 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g31 : (x 0 3 && x 0 13).toNat = 0)
    (g32 : (x 3 1 && x 3 11).toNat = 0)
    (g33 : (x 2 4 && x 2 14).toNat = 0)
    (g34 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g35 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a01_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35
