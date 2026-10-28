import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b01

Topic: combinatorics   Node: 19bec0af7a4e

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 38 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b01_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 1).toNat = 0)
    (g1 : (x 0 5).toNat = 0)
    (g2 : (x 0 6).toNat = 0)
    (g3 : (x 0 8).toNat = 1)
    (g4 : (x 0 9).toNat = 0)
    (g5 : (x 0 13).toNat = 0)
    (g6 : (x 1 6).toNat = 0)
    (g7 : (x 1 14).toNat = 1)
    (g8 : (x 2 5).toNat = 0)
    (g9 : (x 3 4).toNat = 0)
    (g10 : (x 4 11).toNat = 0)
    (g11 : (x 5 10).toNat = 0)
    (g12 : (x 6 9).toNat = 0)
    (g13 : (x 7 8).toNat = 0)
    (g14 : (x 7 7 && x 7 8).toNat = 0)
    (g15 : (x 6 8 && x 6 9).toNat = 0)
    (g16 : (x 5 9 && x 5 10).toNat = 0)
    (g17 : (x 4 10 && x 4 11).toNat = 0)
    (g18 : (x 0 6 && x 0 10).toNat = 0)
    (g19 : (x 0 9 && x 0 14).toNat = 0)
    (g20 : (x 7 3 && x 7 8).toNat = 0)
    (g21 : (x 6 4 && x 6 9).toNat = 0)
    (g22 : (x 5 5 && x 5 10).toNat = 0)
    (g23 : (x 4 6 && x 4 11).toNat = 0)
    (g24 : (x 0 1 && x 0 8).toNat = 0)
    (g25 : (x 3 4 && x 3 11).toNat = 0)
    (g26 : (x 2 5 && x 2 12).toNat = 0)
    (g27 : (x 1 6 && x 1 13).toNat = 0)
    (g28 : (x 0 5 && x 0 14).toNat = 0)
    (g29 : (x 5 1 && x 5 10).toNat = 0)
    (g30 : (x 4 2 && x 4 11).toNat = 0)
    (g31 : (x 3 4 && x 3 13).toNat = 0)
    (g32 : (x 2 5 && x 2 14).toNat = 0)
    (g33 : (x 4 1 && x 4 11).toNat = 0)
    (g34 : (x 3 4 && x 3 14).toNat = 0)
    (g35 : (x 0 1 && x 0 12).toNat = 0)
    (g36 : (x 0 2 && x 0 13).toNat = 0)
    (g37 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d9651 : (x (-1) 9).toNat = 0 := by
    have r9652 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9653 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9654 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9655 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9656 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9657 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9658 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9659 := hb (x (-7) 7)
    have b9660 := hb (x (-6) 6)
    have b9661 := hb (x (-5) 5)
    have b9662 := hb (x (-4) 4)
    have b9663 := hb (x (-3) 11)
    have b9664 := hb (x (-2) 10)
    have b9665 := hb (x (-1) 9)
    have b9666 := hb (x 0 8)
    clear * - r9652 e9653 e9654 e9655 e9656 e9657 e9658 b9659 b9660 b9661 b9662 b9663 b9664 b9665 b9666 g3
    omega
  have d9667 : (x (-1) 2 && x (-1) 9).toNat = 0 := by
    have r9668 := hand2 (x (-1) 2) (x (-1) 9)
    have b9669 := hb (x (-1) 9)
    have b9670 := hb (x (-1) 2 && x (-1) 9)
    clear * - r9668 b9669 b9670 d9651
    omega
  have d9671 : (x (-1) 5 && x (-1) 9).toNat = 0 := by
    have r9672 := hand2 (x (-1) 5) (x (-1) 9)
    have b9673 := hb (x (-1) 9)
    have b9674 := hb (x (-1) 5 && x (-1) 9)
    clear * - r9672 b9673 b9674 d9651
    omega
  have d9675 : (x (-2) 10).toNat = 0 := by
    have r9676 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9677 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9678 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9679 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9680 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9681 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9682 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9683 := hb (x (-7) 7)
    have b9684 := hb (x (-6) 6)
    have b9685 := hb (x (-5) 5)
    have b9686 := hb (x (-4) 4)
    have b9687 := hb (x (-3) 11)
    have b9688 := hb (x (-2) 10)
    have b9689 := hb (x (-1) 9)
    have b9690 := hb (x 0 8)
    clear * - r9676 e9677 e9678 e9679 e9680 e9681 e9682 b9683 b9684 b9685 b9686 b9687 b9688 b9689 b9690 g3 d9651
    omega
  have d9691 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r9692 := hand2 (x (-2) 1) (x (-2) 10)
    have b9693 := hb (x (-2) 10)
    have b9694 := hb (x (-2) 1 && x (-2) 10)
    clear * - r9692 b9693 b9694 d9675
    omega
  have d9695 : (x (-2) 3 && x (-2) 10).toNat = 0 := by
    have r9696 := hand2 (x (-2) 3) (x (-2) 10)
    have b9697 := hb (x (-2) 10)
    have b9698 := hb (x (-2) 3 && x (-2) 10)
    clear * - r9696 b9697 b9698 d9675
    omega
  have d9699 : (x (-2) 6 && x (-2) 10).toNat = 0 := by
    have r9700 := hand2 (x (-2) 6) (x (-2) 10)
    have b9701 := hb (x (-2) 10)
    have b9702 := hb (x (-2) 6 && x (-2) 10)
    clear * - r9700 b9701 b9702 d9675
    omega
  have d9703 : (x (-3) 11).toNat = 0 := by
    have r9704 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9705 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9706 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9707 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9708 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9709 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9710 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9711 := hb (x (-7) 7)
    have b9712 := hb (x (-6) 6)
    have b9713 := hb (x (-5) 5)
    have b9714 := hb (x (-4) 4)
    have b9715 := hb (x (-3) 11)
    have b9716 := hb (x (-2) 10)
    have b9717 := hb (x (-1) 9)
    have b9718 := hb (x 0 8)
    clear * - r9704 e9705 e9706 e9707 e9708 e9709 e9710 b9711 b9712 b9713 b9714 b9715 b9716 b9717 b9718 g3 d9651 d9675
    omega
  have d9719 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
    have r9720 := hand2 (x (-3) 1) (x (-3) 11)
    have b9721 := hb (x (-3) 11)
    have b9722 := hb (x (-3) 1 && x (-3) 11)
    clear * - r9720 b9721 b9722 d9703
    omega
  have d9723 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r9724 := hand2 (x (-3) 2) (x (-3) 11)
    have b9725 := hb (x (-3) 11)
    have b9726 := hb (x (-3) 2 && x (-3) 11)
    clear * - r9724 b9725 b9726 d9703
    omega
  have d9727 : (x (-3) 4 && x (-3) 11).toNat = 0 := by
    have r9728 := hand2 (x (-3) 4) (x (-3) 11)
    have b9729 := hb (x (-3) 11)
    have b9730 := hb (x (-3) 4 && x (-3) 11)
    clear * - r9728 b9729 b9730 d9703
    omega
  have d9731 : (x (-3) 7 && x (-3) 11).toNat = 0 := by
    have r9732 := hand2 (x (-3) 7) (x (-3) 11)
    have b9733 := hb (x (-3) 11)
    have b9734 := hb (x (-3) 7 && x (-3) 11)
    clear * - r9732 b9733 b9734 d9703
    omega
  have d9735 : (x (-4) 4).toNat = 0 := by
    have r9736 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9737 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9738 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9739 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9740 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9741 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9742 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9743 := hb (x (-7) 7)
    have b9744 := hb (x (-6) 6)
    have b9745 := hb (x (-5) 5)
    have b9746 := hb (x (-4) 4)
    have b9747 := hb (x (-3) 11)
    have b9748 := hb (x (-2) 10)
    have b9749 := hb (x (-1) 9)
    have b9750 := hb (x 0 8)
    clear * - r9736 e9737 e9738 e9739 e9740 e9741 e9742 b9743 b9744 b9745 b9746 b9747 b9748 b9749 b9750 g3 d9651 d9675 d9703
    omega
  have d9751 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r9752 := hand1 (x (-4) 4) (x (-4) 14)
    have b9753 := hb (x (-4) 4)
    have b9754 := hb (x (-4) 4 && x (-4) 14)
    clear * - r9752 b9753 b9754 d9735
    omega
  have d9755 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
    have r9756 := hand1 (x (-4) 4) (x (-4) 13)
    have b9757 := hb (x (-4) 4)
    have b9758 := hb (x (-4) 4 && x (-4) 13)
    clear * - r9756 b9757 b9758 d9735
    omega
  have d9759 : (x (-4) 4 && x (-4) 10).toNat = 0 := by
    have r9760 := hand1 (x (-4) 4) (x (-4) 10)
    have b9761 := hb (x (-4) 4)
    have b9762 := hb (x (-4) 4 && x (-4) 10)
    clear * - r9760 b9761 b9762 d9735
    omega
  have d9763 : (x (-4) 4 && x (-4) 8).toNat = 0 := by
    have r9764 := hand1 (x (-4) 4) (x (-4) 8)
    have b9765 := hb (x (-4) 4)
    have b9766 := hb (x (-4) 4 && x (-4) 8)
    clear * - r9764 b9765 b9766 d9735
    omega
  have d9767 : (x (-5) 5).toNat = 0 := by
    have r9768 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9769 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9770 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9771 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9772 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9773 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9774 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9775 := hb (x (-7) 7)
    have b9776 := hb (x (-6) 6)
    have b9777 := hb (x (-5) 5)
    have b9778 := hb (x (-4) 4)
    have b9779 := hb (x (-3) 11)
    have b9780 := hb (x (-2) 10)
    have b9781 := hb (x (-1) 9)
    have b9782 := hb (x 0 8)
    clear * - r9768 e9769 e9770 e9771 e9772 e9773 e9774 b9775 b9776 b9777 b9778 b9779 b9780 b9781 b9782 g3 d9651 d9675 d9703 d9735
    omega
  have d9783 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
    have r9784 := hand1 (x (-5) 5) (x (-5) 14)
    have b9785 := hb (x (-5) 5)
    have b9786 := hb (x (-5) 5 && x (-5) 14)
    clear * - r9784 b9785 b9786 d9767
    omega
  have d9787 : (x (-5) 5 && x (-5) 11).toNat = 0 := by
    have r9788 := hand1 (x (-5) 5) (x (-5) 11)
    have b9789 := hb (x (-5) 5)
    have b9790 := hb (x (-5) 5 && x (-5) 11)
    clear * - r9788 b9789 b9790 d9767
    omega
  have d9791 : (x (-5) 5 && x (-5) 9).toNat = 0 := by
    have r9792 := hand1 (x (-5) 5) (x (-5) 9)
    have b9793 := hb (x (-5) 5)
    have b9794 := hb (x (-5) 5 && x (-5) 9)
    clear * - r9792 b9793 b9794 d9767
    omega
  have d9795 : (x (-6) 6).toNat = 0 := by
    have r9796 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9797 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9798 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9799 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9800 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9801 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9802 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9803 := hb (x (-7) 7)
    have b9804 := hb (x (-6) 6)
    have b9805 := hb (x (-5) 5)
    have b9806 := hb (x (-4) 4)
    have b9807 := hb (x (-3) 11)
    have b9808 := hb (x (-2) 10)
    have b9809 := hb (x (-1) 9)
    have b9810 := hb (x 0 8)
    clear * - r9796 e9797 e9798 e9799 e9800 e9801 e9802 b9803 b9804 b9805 b9806 b9807 b9808 b9809 b9810 g3 d9651 d9675 d9703 d9735 d9767
    omega
  have d9811 : (x (-6) 6 && x (-6) 12).toNat = 0 := by
    have r9812 := hand1 (x (-6) 6) (x (-6) 12)
    have b9813 := hb (x (-6) 6)
    have b9814 := hb (x (-6) 6 && x (-6) 12)
    clear * - r9812 b9813 b9814 d9795
    omega
  have d9815 : (x (-6) 6 && x (-6) 10).toNat = 0 := by
    have r9816 := hand1 (x (-6) 6) (x (-6) 10)
    have b9817 := hb (x (-6) 6)
    have b9818 := hb (x (-6) 6 && x (-6) 10)
    clear * - r9816 b9817 b9818 d9795
    omega
  have d9819 : (x (-7) 7).toNat = 0 := by
    have r9820 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9821 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9822 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9823 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9824 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9825 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9826 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9827 := hb (x (-7) 7)
    have b9828 := hb (x (-6) 6)
    have b9829 := hb (x (-5) 5)
    have b9830 := hb (x (-4) 4)
    have b9831 := hb (x (-3) 11)
    have b9832 := hb (x (-2) 10)
    have b9833 := hb (x (-1) 9)
    have b9834 := hb (x 0 8)
    clear * - r9820 e9821 e9822 e9823 e9824 e9825 e9826 b9827 b9828 b9829 b9830 b9831 b9832 b9833 b9834 g3 d9651 d9675 d9703 d9735 d9767 d9795
    omega
  have d9835 : (x (-7) 7 && x (-7) 13).toNat = 0 := by
    have r9836 := hand1 (x (-7) 7) (x (-7) 13)
    have b9837 := hb (x (-7) 7)
    have b9838 := hb (x (-7) 7 && x (-7) 13)
    clear * - r9836 b9837 b9838 d9819
    omega
  have d9839 : (x (-7) 7 && x (-7) 11).toNat = 0 := by
    have r9840 := hand1 (x (-7) 7) (x (-7) 11)
    have b9841 := hb (x (-7) 7)
    have b9842 := hb (x (-7) 7 && x (-7) 11)
    clear * - r9840 b9841 b9842 d9819
    omega
  cases h9843 : x 0 2
  · have f9844 : (x 0 2).toNat = 0 := by rw [h9843]; rfl
    have d9845 : (x 0 2 && x 0 12).toNat = 0 := by
      have r9846 := hand1 (x 0 2) (x 0 12)
      have b9847 := hb (x 0 2)
      have b9848 := hb (x 0 2 && x 0 12)
      clear * - r9846 b9847 b9848 f9844
      omega
    have d9849 : (x 0 2 && x 0 11).toNat = 0 := by
      have r9850 := hand1 (x 0 2) (x 0 11)
      have b9851 := hb (x 0 2)
      have b9852 := hb (x 0 2 && x 0 11)
      clear * - r9850 b9851 b9852 f9844
      omega
    have d9853 : (x 0 10).toNat = 0 := by
      have r9854 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
      have b9855 := hb (x 0 2)
      have b9856 := hb (x 0 10)
      clear * - r9854 b9855 b9856 f9844
      omega
    cases h9857 : x 0 3
    · have f9858 : (x 0 3).toNat = 0 := by rw [h9857]; rfl
      have d9859 : (x 0 11).toNat = 0 := by
        have r9860 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
        have b9861 := hb (x 0 3)
        have b9862 := hb (x 0 11)
        clear * - r9860 b9861 b9862 f9858
        omega
      cases h9863 : x 0 4
      · have f9864 : (x 0 4).toNat = 0 := by rw [h9863]; rfl
        have d9865 : (x 0 4 && x 0 14).toNat = 0 := by
          have r9866 := hand1 (x 0 4) (x 0 14)
          have b9867 := hb (x 0 4)
          have b9868 := hb (x 0 4 && x 0 14)
          clear * - r9866 b9867 b9868 f9864
          omega
        have d9869 : (x 0 4 && x 0 8).toNat = 0 := by
          have r9870 := hand1 (x 0 4) (x 0 8)
          have b9871 := hb (x 0 4)
          have b9872 := hb (x 0 4 && x 0 8)
          clear * - r9870 b9871 b9872 f9864
          omega
        cases h9873 : x 0 12
        · have f9874 : (x 0 12).toNat = 0 := by rw [h9873]; rfl
          cases h9875 : x 0 14
          · have f9876 : (x 0 14).toNat = 0 := by rw [h9875]; rfl
            have d9877 : (x 0 7 && x 0 14).toNat = 0 := by
              have r9878 := hand2 (x 0 7) (x 0 14)
              have b9879 := hb (x 0 14)
              have b9880 := hb (x 0 7 && x 0 14)
              clear * - r9878 b9879 b9880 f9876
              omega
            cases h9881 : x 1 1
            · have f9882 : (x 1 1).toNat = 0 := by rw [h9881]; rfl
              have d9883 : (x 1 1 && x 1 14).toNat = 0 := by
                have r9884 := hand1 (x 1 1) (x 1 14)
                have b9885 := hb (x 1 1)
                have b9886 := hb (x 1 1 && x 1 14)
                clear * - r9884 b9885 b9886 f9882
                omega
              have d9887 : (x 1 13).toNat = 0 := by
                have r9888 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
                have b9889 := hb (x 1 1)
                have b9890 := hb (x 1 13)
                clear * - r9888 b9889 b9890 f9882
                omega
              have d9891 : (x 1 5).toNat = 0 := by
                have r9892 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
                have b9893 := hb (x 1 5)
                have b9894 := hb (x 1 13)
                clear * - r9892 b9893 b9894 d9887
                omega
              have d9895 : (x 1 5 && x 1 14).toNat = 0 := by
                have r9896 := hand1 (x 1 5) (x 1 14)
                have b9897 := hb (x 1 5)
                have b9898 := hb (x 1 5 && x 1 14)
                clear * - r9896 b9897 b9898 d9891
                omega
              have d9899 : (x 2 13).toNat = 1 := by
                have r9900 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9901 := hb (x 0 2)
                have b9902 := hb (x 2 13)
                have b9903 := hb (x 1 1 && x 1 14)
                clear * - r9900 b9901 b9902 b9903 d9883 f9844
                omega
              have d9904 : (x 2 1).toNat = 1 := by
                have r9905 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
                have b9906 := hb (x 2 1)
                have b9907 := hb (x 2 13)
                clear * - r9905 b9906 b9907 d9899
                omega
              have d9908 : (x 3 14).toNat = 0 := by
                have r9909 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9910 := hb (x 2 1)
                have b9911 := hb (x 3 14)
                clear * - r9909 b9910 b9911 d9904
                omega
              have d9912 : (x 3 1 && x 3 14).toNat = 0 := by
                have r9913 := hand2 (x 3 1) (x 3 14)
                have b9914 := hb (x 3 14)
                have b9915 := hb (x 3 1 && x 3 14)
                clear * - r9913 b9914 b9915 d9908
                omega
              have d9916 : (x 3 2).toNat = 0 := by
                have r9917 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                have b9918 := hb (x 3 2)
                have b9919 := hb (x 3 14)
                clear * - r9917 b9918 b9919 d9908
                omega
              have d9920 : (x 3 2 && x 3 12).toNat = 0 := by
                have r9921 := hand1 (x 3 2) (x 3 12)
                have b9922 := hb (x 3 2)
                have b9923 := hb (x 3 2 && x 3 12)
                clear * - r9921 b9922 b9923 d9916
                omega
              have d9924 : (x (-1) 2).toNat = 1 := by
                have r9925 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9926 := hb (x (-1) 2)
                have b9927 := hb (x 1 13)
                have b9928 := hb (x 0 1 && x 0 14)
                clear * - r9925 b9926 b9927 b9928 d9887 g37
                omega
              have d9929 : (x 3 12).toNat = 0 := by
                have r9930 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9931 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                have e9932 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                have b9933 := hb (x 0 3)
                have b9934 := hb (x 1 2)
                have b9935 := hb (x 2 13)
                have b9936 := hb (x 3 12)
                clear * - r9930 e9931 e9932 b9933 b9934 b9935 b9936 d9899 f9858
                omega
              have d9937 : (x 3 3 && x 3 12).toNat = 0 := by
                have r9938 := hand2 (x 3 3) (x 3 12)
                have b9939 := hb (x 3 12)
                have b9940 := hb (x 3 3 && x 3 12)
                clear * - r9938 b9939 b9940 d9929
                omega
              have d9941 : (x 1 12).toNat = 0 := by
                have r9942 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9943 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                have e9944 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                have b9945 := hb (x (-2) 3)
                have b9946 := hb (x (-1) 2)
                have b9947 := hb (x 0 13)
                have b9948 := hb (x 1 12)
                clear * - r9942 e9943 e9944 b9945 b9946 b9947 b9948 g5 d9924
                omega
              have d9949 : (x 1 4).toNat = 0 := by
                have r9950 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                have b9951 := hb (x 1 4)
                have b9952 := hb (x 1 12)
                clear * - r9950 b9951 b9952 d9941
                omega
              have d9953 : (x 1 4 && x 1 14).toNat = 0 := by
                have r9954 := hand1 (x 1 4) (x 1 14)
                have b9955 := hb (x 1 4)
                have b9956 := hb (x 1 4 && x 1 14)
                clear * - r9954 b9955 b9956 d9949
                omega
              have d9957 : (x (-2) 3).toNat = 0 := by
                have r9958 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9959 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                have e9960 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                have b9961 := hb (x (-2) 3)
                have b9962 := hb (x (-1) 2)
                have b9963 := hb (x 0 13)
                have b9964 := hb (x 1 12)
                clear * - r9958 e9959 e9960 b9961 b9962 b9963 b9964 d9941 g5 d9924
                omega
              have d9965 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                have r9966 := hand1 (x (-2) 3) (x (-2) 14)
                have b9967 := hb (x (-2) 3)
                have b9968 := hb (x (-2) 3 && x (-2) 14)
                clear * - r9966 b9967 b9968 d9957
                omega
              have d9969 : (x 2 3 && x 2 13).toNat = 1 := by
                have r9970 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9971 := hb (x 0 5)
                have b9972 := hb (x 5 10)
                have b9973 := hb (x 4 1 && x 4 11)
                have b9974 := hb (x 3 2 && x 3 12)
                have b9975 := hb (x 2 3 && x 2 13)
                have b9976 := hb (x 1 4 && x 1 14)
                clear * - r9970 b9971 b9972 b9973 b9974 b9975 b9976 g11 g33 d9920 d9953 g1
                omega
              have d9977 : (x 2 3).toNat = 1 := by
                have r9978 := hand1 (x 2 3) (x 2 13)
                have b9979 := hb (x 2 3)
                have b9980 := hb (x 2 3 && x 2 13)
                clear * - r9978 b9979 b9980 d9969
                omega
              have d9981 : (x 5 12).toNat = 0 := by
                have r9982 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9983 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e9984 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b9985 := hb (x 2 3)
                have b9986 := hb (x 3 2)
                have b9987 := hb (x 4 13)
                have b9988 := hb (x 5 12)
                clear * - r9982 e9983 e9984 b9985 b9986 b9987 b9988 d9916 d9977
                omega
              have d9989 : (x 4 13).toNat = 0 := by
                have r9990 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e9991 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e9992 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b9993 := hb (x 2 3)
                have b9994 := hb (x 3 2)
                have b9995 := hb (x 4 13)
                have b9996 := hb (x 5 12)
                clear * - r9990 e9991 e9992 b9993 b9994 b9995 b9996 d9981 d9916 d9977
                omega
              have d9997 : (x 2 2).toNat = 1 := by
                have r9998 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b9999 := hb (x 2 2)
                have b10000 := hb (x 4 13)
                have b10001 := hb (x 3 1 && x 3 14)
                clear * - r9998 b9999 b10000 b10001 d9989 d9912
                omega
              have d10002 : (x 4 12).toNat = 0 := by
                have r10003 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10004 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e10005 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b10006 := hb (x 1 3)
                have b10007 := hb (x 2 2)
                have b10008 := hb (x 3 13)
                have b10009 := hb (x 4 12)
                clear * - r10003 e10004 e10005 b10006 b10007 b10008 b10009 d9997
                omega
              have d10010 : (x 4 3 && x 4 12).toNat = 0 := by
                have r10011 := hand2 (x 4 3) (x 4 12)
                have b10012 := hb (x 4 12)
                have b10013 := hb (x 4 3 && x 4 12)
                clear * - r10011 b10012 b10013 d10002
                omega
              have d10014 : (x 4 4).toNat = 0 := by
                have r10015 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b10016 := hb (x 4 4)
                have b10017 := hb (x 4 12)
                clear * - r10015 b10016 b10017 d10002
                omega
              have d10018 : (x 3 13).toNat = 0 := by
                have r10019 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10020 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e10021 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b10022 := hb (x 1 3)
                have b10023 := hb (x 2 2)
                have b10024 := hb (x 3 13)
                have b10025 := hb (x 4 12)
                clear * - r10019 e10020 e10021 b10022 b10023 b10024 b10025 d10002 d9997
                omega
              have d10026 : (x 3 5).toNat = 0 := by
                have r10027 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                have b10028 := hb (x 3 5)
                have b10029 := hb (x 3 13)
                clear * - r10027 b10028 b10029 d10018
                omega
              have d10030 : (x 1 3).toNat = 0 := by
                have r10031 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10032 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e10033 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b10034 := hb (x 1 3)
                have b10035 := hb (x 2 2)
                have b10036 := hb (x 3 13)
                have b10037 := hb (x 4 12)
                clear * - r10031 e10032 e10033 b10034 b10035 b10036 b10037 d10002 d10018 d9997
                omega
              have d10038 : (x 1 11).toNat = 0 := by
                have r10039 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                have b10040 := hb (x 1 3)
                have b10041 := hb (x 1 11)
                clear * - r10039 b10040 b10041 d10030
                omega
              have d10042 : (x 2 4 && x 2 13).toNat = 1 := by
                have r10043 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b10044 := hb (x 0 6)
                have b10045 := hb (x 6 9)
                have b10046 := hb (x 5 1 && x 5 10)
                have b10047 := hb (x 4 2 && x 4 11)
                have b10048 := hb (x 3 3 && x 3 12)
                have b10049 := hb (x 2 4 && x 2 13)
                have b10050 := hb (x 1 5 && x 1 14)
                clear * - r10043 b10044 b10045 b10046 b10047 b10048 b10049 b10050 g12 g29 g30 d9937 d9895 g2
                omega
              have d10051 : (x 2 4).toNat = 1 := by
                have r10052 := hand1 (x 2 4) (x 2 13)
                have b10053 := hb (x 2 4)
                have b10054 := hb (x 2 4 && x 2 13)
                clear * - r10052 b10053 b10054 d10042
                omega
              have d10055 : (x 2 12).toNat = 1 := by
                have r10056 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
                have b10057 := hb (x 2 4)
                have b10058 := hb (x 2 12)
                clear * - r10056 b10057 b10058 d10051
                omega
              have d10059 : (x (-1) 3).toNat = 0 := by
                have r10060 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10061 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                have e10062 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                have b10063 := hb (x (-1) 3)
                have b10064 := hb (x 0 2)
                have b10065 := hb (x 1 13)
                have b10066 := hb (x 2 12)
                clear * - r10060 e10061 e10062 b10063 b10064 b10065 b10066 d10055 d9887 f9844
                omega
              have d10067 : (x (-1) 11).toNat = 0 := by
                have r10068 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
                have b10069 := hb (x (-1) 3)
                have b10070 := hb (x (-1) 11)
                clear * - r10068 b10069 b10070 d10059
                omega
              have d10071 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
                have r10072 := hand2 (x (-1) 1) (x (-1) 11)
                have b10073 := hb (x (-1) 11)
                have b10074 := hb (x (-1) 1 && x (-1) 11)
                clear * - r10072 b10073 b10074 d10067
                omega
              have d10075 : (x 6 8).toNat = 0 := by
                have r10076 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10077 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e10078 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e10079 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e10080 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e10081 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e10082 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b10083 := hb (x (-1) 7)
                have b10084 := hb (x 0 6)
                have b10085 := hb (x 1 5)
                have b10086 := hb (x 2 4)
                have b10087 := hb (x 3 11)
                have b10088 := hb (x 4 10)
                have b10089 := hb (x 5 9)
                have b10090 := hb (x 6 8)
                clear * - r10076 e10077 e10078 e10079 e10080 e10081 e10082 b10083 b10084 b10085 b10086 b10087 b10088 b10089 b10090 d10051 d9891 g2
                omega
              have d10091 : (x 5 9).toNat = 0 := by
                have r10092 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10093 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e10094 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e10095 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e10096 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e10097 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e10098 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b10099 := hb (x (-1) 7)
                have b10100 := hb (x 0 6)
                have b10101 := hb (x 1 5)
                have b10102 := hb (x 2 4)
                have b10103 := hb (x 3 11)
                have b10104 := hb (x 4 10)
                have b10105 := hb (x 5 9)
                have b10106 := hb (x 6 8)
                clear * - r10092 e10093 e10094 e10095 e10096 e10097 e10098 b10099 b10100 b10101 b10102 b10103 b10104 b10105 b10106 d10075 d10051 d9891 g2
                omega
              have d10107 : (x 4 10).toNat = 0 := by
                have r10108 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10109 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e10110 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e10111 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e10112 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e10113 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e10114 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b10115 := hb (x (-1) 7)
                have b10116 := hb (x 0 6)
                have b10117 := hb (x 1 5)
                have b10118 := hb (x 2 4)
                have b10119 := hb (x 3 11)
                have b10120 := hb (x 4 10)
                have b10121 := hb (x 5 9)
                have b10122 := hb (x 6 8)
                clear * - r10108 e10109 e10110 e10111 e10112 e10113 e10114 b10115 b10116 b10117 b10118 b10119 b10120 b10121 b10122 d10075 d10091 d10051 d9891 g2
                omega
              have d10123 : (x 3 11).toNat = 0 := by
                have r10124 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10125 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e10126 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e10127 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e10128 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e10129 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e10130 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b10131 := hb (x (-1) 7)
                have b10132 := hb (x 0 6)
                have b10133 := hb (x 1 5)
                have b10134 := hb (x 2 4)
                have b10135 := hb (x 3 11)
                have b10136 := hb (x 4 10)
                have b10137 := hb (x 5 9)
                have b10138 := hb (x 6 8)
                clear * - r10124 e10125 e10126 e10127 e10128 e10129 e10130 b10131 b10132 b10133 b10134 b10135 b10136 b10137 b10138 d10075 d10091 d10107 d10051 d9891 g2
                omega
              have d10139 : (x (-1) 7).toNat = 0 := by
                have r10140 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e10141 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e10142 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e10143 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e10144 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e10145 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e10146 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b10147 := hb (x (-1) 7)
                have b10148 := hb (x 0 6)
                have b10149 := hb (x 1 5)
                have b10150 := hb (x 2 4)
                have b10151 := hb (x 3 11)
                have b10152 := hb (x 4 10)
                have b10153 := hb (x 5 9)
                have b10154 := hb (x 6 8)
                clear * - r10140 e10141 e10142 e10143 e10144 e10145 e10146 b10147 b10148 b10149 b10150 b10151 b10152 b10153 b10154 d10075 d10091 d10107 d10123 d10051 d9891 g2
                omega
              have d10155 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
                have r10156 := hand2 (x (-1) 1) (x (-1) 7)
                have b10157 := hb (x (-1) 7)
                have b10158 := hb (x (-1) 1 && x (-1) 7)
                clear * - r10156 b10157 b10158 d10139
                omega
              have r10159 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r10160 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e10161 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
              have e10162 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
              have e10163 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
              have e10164 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
              have e10165 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
              have e10166 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
              have r10167 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e10168 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e10169 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e10170 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e10171 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e10172 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e10173 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have r10174 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e10175 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e10176 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e10177 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e10178 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e10179 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e10180 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have r10181 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e10182 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e10183 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have r10184 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e10185 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e10186 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have r10187 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r10188 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r10189 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r10190 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r10191 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r10192 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r10193 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r10194 := hand2 (x (-2) 2) (x (-2) 8)
              have r10195 := hand2 (x (-3) 3) (x (-3) 9)
              have r10196 := hand1 (x (-8) 8) (x (-8) 14)
              have r10197 := hand1 (x (-4) 5) (x (-4) 12)
              have r10198 := hand1 (x (-5) 6) (x (-5) 13)
              have r10199 := hand1 (x (-6) 7) (x (-6) 14)
              have r10200 := hand2 (x (-9) 1) (x (-9) 10)
              have r10201 := hand2 (x (-10) 2) (x (-10) 11)
              have r10202 := hand2 (x (-11) 3) (x (-11) 12)
              have r10203 := hand1 (x (-12) 4) (x (-12) 13)
              have r10204 := hand1 (x (-13) 5) (x (-13) 14)
              have r10205 := hand2 (x 6 1) (x 6 10)
              have r10206 := hand2 (x 5 2) (x 5 11)
              have r10207 := hand1 (x (-4) 2) (x (-4) 12)
              have r10208 := hand1 (x (-5) 3) (x (-5) 13)
              have r10209 := hand1 (x (-6) 4) (x (-6) 14)
              have r10210 := hand1 (x (-2) 2) (x (-2) 12)
              have r10211 := hand2 (x (-2) 2) (x (-2) 12)
              have r10212 := hand1 (x (-3) 3) (x (-3) 13)
              have r10213 := hand2 (x (-3) 3) (x (-3) 13)
              have r10214 := hand2 (x (-1) 2) (x (-1) 13)
              linarith only [r10159, r10160, e10161, e10162, e10163, e10164, e10165, e10166, r10167, e10168, e10169, e10170, e10171, e10172, e10173, r10174, e10175, e10176, e10177, e10178, e10179, e10180, r10181, e10182, e10183, r10184, e10185, e10186, r10187, r10188, r10189, r10190, r10191, r10192, r10193, r10194, r10195, r10196, r10197, r10198, r10199, r10200, r10201, r10202, r10203, r10204, r10205, r10206, r10207, r10208, r10209, r10210, r10211, r10212, r10213, r10214, d9767, d9957, d9675, d9924, g0, g2, d9853, f9874, g6, d10038, d10026, d10014, d10155, d9759, d9787, d9811, d9835, g24, d9667, d9695, d9727, d10010, g31, g32, d9719, d10071, d9751, g35, d9965]
            · have f10303 : (x 1 1).toNat = 1 := by rw [h9881]; rfl
              have d10304 : (x 2 14).toNat = 0 := by
                have r10305 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b10306 := hb (x 1 1)
                have b10307 := hb (x 2 14)
                clear * - r10305 b10306 b10307 f10303
                omega
              have d10308 : (x 2 1 && x 2 14).toNat = 0 := by
                have r10309 := hand2 (x 2 1) (x 2 14)
                have b10310 := hb (x 2 14)
                have b10311 := hb (x 2 1 && x 2 14)
                clear * - r10309 b10310 b10311 d10304
                omega
              have d10312 : (x 2 6).toNat = 0 := by
                have r10313 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
                have b10314 := hb (x 2 6)
                have b10315 := hb (x 2 14)
                clear * - r10313 b10314 b10315 d10304
                omega
              have d10316 : (x 2 2 && x 2 6).toNat = 0 := by
                have r10317 := hand2 (x 2 2) (x 2 6)
                have b10318 := hb (x 2 6)
                have b10319 := hb (x 2 2 && x 2 6)
                clear * - r10317 b10318 b10319 d10312
                omega
              have d10320 : (x 2 2).toNat = 0 := by
                have r10321 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
                have b10322 := hb (x 2 2)
                have b10323 := hb (x 2 14)
                clear * - r10321 b10322 b10323 d10304
                omega
              have d10324 : (x 2 2 && x 2 13).toNat = 0 := by
                have r10325 := hand1 (x 2 2) (x 2 13)
                have b10326 := hb (x 2 2)
                have b10327 := hb (x 2 2 && x 2 13)
                clear * - r10325 b10326 b10327 d10320
                omega
              have d10328 : (x 2 2 && x 2 12).toNat = 0 := by
                have r10329 := hand1 (x 2 2) (x 2 12)
                have b10330 := hb (x 2 2)
                have b10331 := hb (x 2 2 && x 2 12)
                clear * - r10329 b10330 b10331 d10320
                omega
              have d10332 : (x 2 10).toNat = 0 := by
                have r10333 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
                have b10334 := hb (x 2 2)
                have b10335 := hb (x 2 10)
                clear * - r10333 b10334 b10335 d10320
                omega
              cases h10336 : x (-1) 2
              · have f10337 : (x (-1) 2).toNat = 0 := by rw [h10336]; rfl
                have d10338 : (x (-1) 10).toNat = 0 := by
                  have r10339 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
                  have b10340 := hb (x (-1) 2)
                  have b10341 := hb (x (-1) 10)
                  clear * - r10339 b10340 b10341 f10337
                  omega
                have d10342 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
                  have r10343 := hand2 (x (-1) 1) (x (-1) 10)
                  have b10344 := hb (x (-1) 10)
                  have b10345 := hb (x (-1) 1 && x (-1) 10)
                  clear * - r10343 b10344 b10345 d10338
                  omega
                have d10346 : (x 1 13).toNat = 1 := by
                  have r10347 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b10348 := hb (x (-1) 2)
                  have b10349 := hb (x 1 13)
                  have b10350 := hb (x 0 1 && x 0 14)
                  clear * - r10347 b10348 b10349 b10350 g37 f10337
                  omega
                have d10351 : (x 2 12).toNat = 0 := by
                  have r10352 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10353 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                  have e10354 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                  have b10355 := hb (x (-1) 3)
                  have b10356 := hb (x 0 2)
                  have b10357 := hb (x 1 13)
                  have b10358 := hb (x 2 12)
                  clear * - r10352 e10353 e10354 b10355 b10356 b10357 b10358 d10346 f9844
                  omega
                have d10359 : (x 2 4).toNat = 0 := by
                  have r10360 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
                  have b10361 := hb (x 2 4)
                  have b10362 := hb (x 2 12)
                  clear * - r10360 b10361 b10362 d10351
                  omega
                have d10363 : (x 2 4 && x 2 13).toNat = 0 := by
                  have r10364 := hand1 (x 2 4) (x 2 13)
                  have b10365 := hb (x 2 4)
                  have b10366 := hb (x 2 4 && x 2 13)
                  clear * - r10364 b10365 b10366 d10359
                  omega
                have d10367 : (x 2 4 && x 2 8).toNat = 0 := by
                  have r10368 := hand1 (x 2 4) (x 2 8)
                  have b10369 := hb (x 2 4)
                  have b10370 := hb (x 2 4 && x 2 8)
                  clear * - r10368 b10369 b10370 d10359
                  omega
                have d10371 : (x (-1) 3).toNat = 0 := by
                  have r10372 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10373 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                  have e10374 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                  have b10375 := hb (x (-1) 3)
                  have b10376 := hb (x 0 2)
                  have b10377 := hb (x 1 13)
                  have b10378 := hb (x 2 12)
                  clear * - r10372 e10373 e10374 b10375 b10376 b10377 b10378 d10351 d10346 f9844
                  omega
                have d10379 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
                  have r10380 := hand1 (x (-1) 3) (x (-1) 13)
                  have b10381 := hb (x (-1) 3)
                  have b10382 := hb (x (-1) 3 && x (-1) 13)
                  clear * - r10380 b10381 b10382 d10371
                  omega
                have d10383 : (x (-1) 11).toNat = 0 := by
                  have r10384 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
                  have b10385 := hb (x (-1) 3)
                  have b10386 := hb (x (-1) 11)
                  clear * - r10384 b10385 b10386 d10371
                  omega
                have d10387 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
                  have r10388 := hand2 (x (-1) 1) (x (-1) 11)
                  have b10389 := hb (x (-1) 11)
                  have b10390 := hb (x (-1) 1 && x (-1) 11)
                  clear * - r10388 b10389 b10390 d10383
                  omega
                have d10391 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
                  have r10392 := hand2 (x (-1) 7) (x (-1) 11)
                  have b10393 := hb (x (-1) 11)
                  have b10394 := hb (x (-1) 7 && x (-1) 11)
                  clear * - r10392 b10393 b10394 d10383
                  omega
                cases h10395 : x 1 2
                · have f10396 : (x 1 2).toNat = 0 := by rw [h10395]; rfl
                  have d10397 : (x 3 13).toNat = 1 := by
                    have r10398 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10399 := hb (x 1 2)
                    have b10400 := hb (x 3 13)
                    have b10401 := hb (x 2 1 && x 2 14)
                    clear * - r10398 b10399 b10400 b10401 d10308 f10396
                    omega
                  have d10402 : (x 3 1).toNat = 1 := by
                    have r10403 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                    have b10404 := hb (x 3 1)
                    have b10405 := hb (x 3 13)
                    clear * - r10403 b10404 b10405 d10397
                    omega
                  have d10406 : (x 4 14).toNat = 0 := by
                    have r10407 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10408 := hb (x 3 1)
                    have b10409 := hb (x 4 14)
                    clear * - r10407 b10408 b10409 d10402
                    omega
                  have d10410 : (x 4 3 && x 4 14).toNat = 0 := by
                    have r10411 := hand2 (x 4 3) (x 4 14)
                    have b10412 := hb (x 4 14)
                    have b10413 := hb (x 4 3 && x 4 14)
                    clear * - r10411 b10412 b10413 d10406
                    omega
                  have d10414 : (x 4 6).toNat = 0 := by
                    have r10415 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
                    have b10416 := hb (x 4 6)
                    have b10417 := hb (x 4 14)
                    clear * - r10415 b10416 b10417 d10406
                    omega
                  have d10418 : (x 4 2 && x 4 6).toNat = 0 := by
                    have r10419 := hand2 (x 4 2) (x 4 6)
                    have b10420 := hb (x 4 6)
                    have b10421 := hb (x 4 2 && x 4 6)
                    clear * - r10419 b10420 b10421 d10414
                    omega
                  have d10422 : (x 4 2).toNat = 0 := by
                    have r10423 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                    have b10424 := hb (x 4 2)
                    have b10425 := hb (x 4 14)
                    clear * - r10423 b10424 b10425 d10406
                    omega
                  have d10426 : (x 4 10).toNat = 0 := by
                    have r10427 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                    have b10428 := hb (x 4 2)
                    have b10429 := hb (x 4 10)
                    clear * - r10427 b10428 b10429 d10422
                    omega
                  have d10430 : (x 4 12).toNat = 0 := by
                    have r10431 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10432 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e10433 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b10434 := hb (x 1 3)
                    have b10435 := hb (x 2 2)
                    have b10436 := hb (x 3 13)
                    have b10437 := hb (x 4 12)
                    clear * - r10431 e10432 e10433 b10434 b10435 b10436 b10437 d10397 d10320
                    omega
                  have d10438 : (x 1 3).toNat = 0 := by
                    have r10439 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10440 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e10441 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b10442 := hb (x 1 3)
                    have b10443 := hb (x 2 2)
                    have b10444 := hb (x 3 13)
                    have b10445 := hb (x 4 12)
                    clear * - r10439 e10440 e10441 b10442 b10443 b10444 b10445 d10430 d10397 d10320
                    omega
                  have d10446 : (x 1 3 && x 1 13).toNat = 0 := by
                    have r10447 := hand1 (x 1 3) (x 1 13)
                    have b10448 := hb (x 1 3)
                    have b10449 := hb (x 1 3 && x 1 13)
                    clear * - r10447 b10448 b10449 d10438
                    omega
                  have d10450 : (x 1 11).toNat = 0 := by
                    have r10451 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                    have b10452 := hb (x 1 3)
                    have b10453 := hb (x 1 11)
                    clear * - r10451 b10452 b10453 d10438
                    omega
                  have d10454 : (x 1 1 && x 1 11).toNat = 0 := by
                    have r10455 := hand2 (x 1 1) (x 1 11)
                    have b10456 := hb (x 1 11)
                    have b10457 := hb (x 1 1 && x 1 11)
                    clear * - r10455 b10456 b10457 d10450
                    omega
                  have r10458 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10459 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e10460 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e10461 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e10462 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e10463 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e10464 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have r10465 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10466 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e10467 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e10468 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e10469 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e10470 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e10471 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have r10472 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10473 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                  have e10474 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                  have e10475 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                  have e10476 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                  have e10477 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                  have e10478 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                  have r10479 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10480 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e10481 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have r10482 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10483 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                  have e10484 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                  have r10485 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10486 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e10487 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have r10488 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e10489 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
                  have e10490 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
                  have r10491 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r10492 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r10493 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r10494 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r10495 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r10496 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r10497 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
                  have r10498 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                  have r10499 := hand2 (x 3 3) (x 3 7)
                  have r10500 := hand2 (x 1 5) (x 1 9)
                  have r10501 := hand1 (x (-2) 8) (x (-2) 12)
                  have r10502 := hand1 (x (-3) 9) (x (-3) 13)
                  have r10503 := hand1 (x (-2) 2) (x (-2) 11)
                  have r10504 := hand1 (x (-3) 3) (x (-3) 12)
                  have r10505 := hand1 (x (-4) 2) (x (-4) 12)
                  have r10506 := hand1 (x (-5) 3) (x (-5) 13)
                  have r10507 := hand1 (x (-6) 4) (x (-6) 14)
                  have r10508 := hand2 (x (-2) 2) (x (-2) 12)
                  have r10509 := hand2 (x (-3) 3) (x (-3) 13)
                  have r10510 := hand1 (x (-2) 4) (x (-2) 14)
                  have r10511 := hand2 (x 3 1) (x 3 11)
                  have r10512 := hand2 (x 6 1) (x 6 12)
                  have r10513 := hand2 (x 5 2) (x 5 13)
                  linarith only [r10458, e10459, e10460, e10461, e10462, e10463, e10464, r10465, e10466, e10467, e10468, e10469, e10470, e10471, r10472, e10473, e10474, e10475, e10476, e10477, e10478, r10479, e10480, e10481, r10482, e10483, e10484, r10485, e10486, e10487, r10488, e10489, e10490, r10491, r10492, r10493, r10494, r10495, r10496, r10497, r10498, r10499, r10500, r10501, r10502, r10503, r10504, r10505, r10506, r10507, r10508, r10509, r10510, r10511, r10512, r10513, d9795, d9767, d9675, d10383, g4, d9853, f9874, d10332, g9, d10422, d10414, d10426, d10418, d10367, g18, d10391, d10342, d9755, d9783, d9719, d10387, d9751, d10454, d9845, d10379, d10328, d10446, d9865, d10410]
                · have f10591 : (x 1 2).toNat = 1 := by rw [h10395]; rfl
                  have d10592 : (x 3 12).toNat = 0 := by
                    have r10593 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10594 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e10595 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b10596 := hb (x 0 3)
                    have b10597 := hb (x 1 2)
                    have b10598 := hb (x 2 13)
                    have b10599 := hb (x 3 12)
                    clear * - r10593 e10594 e10595 b10596 b10597 b10598 b10599 f10591 f9858
                    omega
                  have d10600 : (x 3 1 && x 3 12).toNat = 0 := by
                    have r10601 := hand2 (x 3 1) (x 3 12)
                    have b10602 := hb (x 3 12)
                    have b10603 := hb (x 3 1 && x 3 12)
                    clear * - r10601 b10602 b10603 d10592
                    omega
                  have d10604 : (x 3 2 && x 3 12).toNat = 0 := by
                    have r10605 := hand2 (x 3 2) (x 3 12)
                    have b10606 := hb (x 3 12)
                    have b10607 := hb (x 3 2 && x 3 12)
                    clear * - r10605 b10606 b10607 d10592
                    omega
                  have d10608 : (x 3 3 && x 3 12).toNat = 0 := by
                    have r10609 := hand2 (x 3 3) (x 3 12)
                    have b10610 := hb (x 3 12)
                    have b10611 := hb (x 3 3 && x 3 12)
                    clear * - r10609 b10610 b10611 d10592
                    omega
                  have d10612 : (x 2 13).toNat = 0 := by
                    have r10613 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10614 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e10615 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b10616 := hb (x 0 3)
                    have b10617 := hb (x 1 2)
                    have b10618 := hb (x 2 13)
                    have b10619 := hb (x 3 12)
                    clear * - r10613 e10614 e10615 b10616 b10617 b10618 b10619 d10592 f10591 f9858
                    omega
                  have d10620 : (x 2 3 && x 2 13).toNat = 0 := by
                    have r10621 := hand2 (x 2 3) (x 2 13)
                    have b10622 := hb (x 2 13)
                    have b10623 := hb (x 2 3 && x 2 13)
                    clear * - r10621 b10622 b10623 d10612
                    omega
                  have d10624 : (x 1 3 && x 1 14).toNat = 1 := by
                    have r10625 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10626 := hb (x 0 4)
                    have b10627 := hb (x 4 11)
                    have b10628 := hb (x 3 1 && x 3 12)
                    have b10629 := hb (x 2 2 && x 2 13)
                    have b10630 := hb (x 1 3 && x 1 14)
                    clear * - r10625 b10626 b10627 b10628 b10629 b10630 g10 d10600 d10324 f9864
                    omega
                  have d10631 : (x 1 3).toNat = 1 := by
                    have r10632 := hand1 (x 1 3) (x 1 14)
                    have b10633 := hb (x 1 3)
                    have b10634 := hb (x 1 3 && x 1 14)
                    clear * - r10632 b10633 b10634 d10624
                    omega
                  have d10635 : (x 4 12).toNat = 0 := by
                    have r10636 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10637 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e10638 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b10639 := hb (x 1 3)
                    have b10640 := hb (x 2 2)
                    have b10641 := hb (x 3 13)
                    have b10642 := hb (x 4 12)
                    clear * - r10636 e10637 e10638 b10639 b10640 b10641 b10642 d10320 d10631
                    omega
                  have d10643 : (x 4 3 && x 4 12).toNat = 0 := by
                    have r10644 := hand2 (x 4 3) (x 4 12)
                    have b10645 := hb (x 4 12)
                    have b10646 := hb (x 4 3 && x 4 12)
                    clear * - r10644 b10645 b10646 d10635
                    omega
                  have d10647 : (x 4 4).toNat = 0 := by
                    have r10648 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                    have b10649 := hb (x 4 4)
                    have b10650 := hb (x 4 12)
                    clear * - r10648 b10649 b10650 d10635
                    omega
                  have d10651 : (x 3 13).toNat = 0 := by
                    have r10652 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10653 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e10654 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b10655 := hb (x 1 3)
                    have b10656 := hb (x 2 2)
                    have b10657 := hb (x 3 13)
                    have b10658 := hb (x 4 12)
                    clear * - r10652 e10653 e10654 b10655 b10656 b10657 b10658 d10635 d10320 d10631
                    omega
                  have d10659 : (x 3 5).toNat = 0 := by
                    have r10660 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                    have b10661 := hb (x 3 5)
                    have b10662 := hb (x 3 13)
                    clear * - r10660 b10661 b10662 d10651
                    omega
                  have d10663 : (x 1 4 && x 1 14).toNat = 1 := by
                    have r10664 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10665 := hb (x 0 5)
                    have b10666 := hb (x 5 10)
                    have b10667 := hb (x 4 1 && x 4 11)
                    have b10668 := hb (x 3 2 && x 3 12)
                    have b10669 := hb (x 2 3 && x 2 13)
                    have b10670 := hb (x 1 4 && x 1 14)
                    clear * - r10664 b10665 b10666 b10667 b10668 b10669 b10670 g11 g33 d10604 d10620 g1
                    omega
                  have d10671 : (x 1 4).toNat = 1 := by
                    have r10672 := hand1 (x 1 4) (x 1 14)
                    have b10673 := hb (x 1 4)
                    have b10674 := hb (x 1 4 && x 1 14)
                    clear * - r10672 b10673 b10674 d10663
                    omega
                  have d10675 : (x 1 12).toNat = 1 := by
                    have r10676 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                    have b10677 := hb (x 1 4)
                    have b10678 := hb (x 1 12)
                    clear * - r10676 b10677 b10678 d10671
                    omega
                  have d10679 : (x (-2) 3).toNat = 0 := by
                    have r10680 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10681 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                    have e10682 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                    have b10683 := hb (x (-2) 3)
                    have b10684 := hb (x (-1) 2)
                    have b10685 := hb (x 0 13)
                    have b10686 := hb (x 1 12)
                    clear * - r10680 e10681 e10682 b10683 b10684 b10685 b10686 d10675 g5 f10337
                    omega
                  have d10687 : (x (-2) 11).toNat = 0 := by
                    have r10688 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
                    have b10689 := hb (x (-2) 3)
                    have b10690 := hb (x (-2) 11)
                    clear * - r10688 b10689 b10690 d10679
                    omega
                  have d10691 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
                    have r10692 := hand2 (x (-2) 2) (x (-2) 11)
                    have b10693 := hb (x (-2) 11)
                    have b10694 := hb (x (-2) 2 && x (-2) 11)
                    clear * - r10692 b10693 b10694 d10687
                    omega
                  have d10695 : (x 1 5 && x 1 14).toNat = 1 := by
                    have r10696 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10697 := hb (x 0 6)
                    have b10698 := hb (x 6 9)
                    have b10699 := hb (x 5 1 && x 5 10)
                    have b10700 := hb (x 4 2 && x 4 11)
                    have b10701 := hb (x 3 3 && x 3 12)
                    have b10702 := hb (x 2 4 && x 2 13)
                    have b10703 := hb (x 1 5 && x 1 14)
                    clear * - r10696 b10697 b10698 b10699 b10700 b10701 b10702 b10703 g12 g29 g30 d10608 d10363 g2
                    omega
                  have d10704 : (x 1 5).toNat = 1 := by
                    have r10705 := hand1 (x 1 5) (x 1 14)
                    have b10706 := hb (x 1 5)
                    have b10707 := hb (x 1 5 && x 1 14)
                    clear * - r10705 b10706 b10707 d10695
                    omega
                  have d10708 : (x (-3) 3 && x (-3) 12).toNat = 1 := by
                    have r10709 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10710 := hb (x (-6) 6)
                    have b10711 := hb (x 0 9)
                    have b10712 := hb (x (-1) 1 && x (-1) 10)
                    have b10713 := hb (x (-2) 2 && x (-2) 11)
                    have b10714 := hb (x (-3) 3 && x (-3) 12)
                    have b10715 := hb (x (-4) 4 && x (-4) 13)
                    have b10716 := hb (x (-5) 5 && x (-5) 14)
                    clear * - r10709 b10710 b10711 b10712 b10713 b10714 b10715 b10716 g4 d10342 d10691 d9755 d9783 d9795
                    omega
                  have d10717 : (x (-3) 12).toNat = 1 := by
                    have r10718 := hand2 (x (-3) 3) (x (-3) 12)
                    have b10719 := hb (x (-3) 12)
                    have b10720 := hb (x (-3) 3 && x (-3) 12)
                    clear * - r10718 b10719 b10720 d10708
                    omega
                  have d10721 : (x (-4) 13).toNat = 0 := by
                    have r10722 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10723 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e10724 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b10725 := hb (x (-6) 3)
                    have b10726 := hb (x (-5) 2)
                    have b10727 := hb (x (-4) 13)
                    have b10728 := hb (x (-3) 12)
                    clear * - r10722 e10723 e10724 b10725 b10726 b10727 b10728 d10717
                    omega
                  have d10729 : (x (-5) 2).toNat = 0 := by
                    have r10730 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10731 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e10732 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b10733 := hb (x (-6) 3)
                    have b10734 := hb (x (-5) 2)
                    have b10735 := hb (x (-4) 13)
                    have b10736 := hb (x (-3) 12)
                    clear * - r10730 e10731 e10732 b10733 b10734 b10735 b10736 d10717 d10721
                    omega
                  have d10737 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
                    have r10738 := hand1 (x (-5) 2) (x (-5) 13)
                    have b10739 := hb (x (-5) 2)
                    have b10740 := hb (x (-5) 2 && x (-5) 13)
                    clear * - r10738 b10739 b10740 d10729
                    omega
                  have d10741 : (x (-5) 10).toNat = 0 := by
                    have r10742 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
                    have b10743 := hb (x (-5) 2)
                    have b10744 := hb (x (-5) 10)
                    clear * - r10742 b10743 b10744 d10729
                    omega
                  have d10745 : (x (-6) 3).toNat = 0 := by
                    have r10746 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10747 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e10748 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b10749 := hb (x (-6) 3)
                    have b10750 := hb (x (-5) 2)
                    have b10751 := hb (x (-4) 13)
                    have b10752 := hb (x (-3) 12)
                    clear * - r10746 e10747 e10748 b10749 b10750 b10751 b10752 d10717 d10721 d10729
                    omega
                  have d10753 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
                    have r10754 := hand1 (x (-6) 3) (x (-6) 14)
                    have b10755 := hb (x (-6) 3)
                    have b10756 := hb (x (-6) 3 && x (-6) 14)
                    clear * - r10754 b10755 b10756 d10745
                    omega
                  have d10757 : (x (-6) 11).toNat = 0 := by
                    have r10758 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
                    have b10759 := hb (x (-6) 3)
                    have b10760 := hb (x (-6) 11)
                    clear * - r10758 b10759 b10760 d10745
                    omega
                  have d10761 : (x (-3) 3).toNat = 1 := by
                    have r10762 := hand1 (x (-3) 3) (x (-3) 12)
                    have b10763 := hb (x (-3) 3)
                    have b10764 := hb (x (-3) 3 && x (-3) 12)
                    clear * - r10762 b10763 b10764 d10708
                    omega
                  have d10765 : (x (-1) 13).toNat = 0 := by
                    have r10766 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10767 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                    have e10768 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                    have b10769 := hb (x (-3) 3)
                    have b10770 := hb (x (-2) 2)
                    have b10771 := hb (x (-1) 13)
                    have b10772 := hb (x 0 12)
                    clear * - r10766 e10767 e10768 b10769 b10770 b10771 b10772 f9874 d10761
                    omega
                  have d10773 : (x (-1) 5).toNat = 0 := by
                    have r10774 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
                    have b10775 := hb (x (-1) 5)
                    have b10776 := hb (x (-1) 13)
                    clear * - r10774 b10775 b10776 d10765
                    omega
                  have d10777 : (x (-2) 2).toNat = 0 := by
                    have r10778 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10779 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                    have e10780 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                    have b10781 := hb (x (-3) 3)
                    have b10782 := hb (x (-2) 2)
                    have b10783 := hb (x (-1) 13)
                    have b10784 := hb (x 0 12)
                    clear * - r10778 e10779 e10780 b10781 b10782 b10783 b10784 f9874 d10765 d10761
                    omega
                  have d10785 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
                    have r10786 := hand1 (x (-2) 2) (x (-2) 12)
                    have b10787 := hb (x (-2) 2)
                    have b10788 := hb (x (-2) 2 && x (-2) 12)
                    clear * - r10786 b10787 b10788 d10777
                    omega
                  have d10789 : (x (-3) 3 && x (-3) 13).toNat = 1 := by
                    have r10790 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10791 := hb (x (-5) 5)
                    have b10792 := hb (x 0 10)
                    have b10793 := hb (x (-1) 1 && x (-1) 11)
                    have b10794 := hb (x (-2) 2 && x (-2) 12)
                    have b10795 := hb (x (-3) 3 && x (-3) 13)
                    have b10796 := hb (x (-4) 4 && x (-4) 14)
                    clear * - r10790 b10791 b10792 b10793 b10794 b10795 b10796 d9853 d10387 d10785 d9751 d9767
                    omega
                  have d10797 : (x (-3) 13).toNat = 1 := by
                    have r10798 := hand2 (x (-3) 3) (x (-3) 13)
                    have b10799 := hb (x (-3) 13)
                    have b10800 := hb (x (-3) 3 && x (-3) 13)
                    clear * - r10798 b10799 b10800 d10789
                    omega
                  have d10801 : (x (-3) 1).toNat = 1 := by
                    have r10802 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                    have b10803 := hb (x (-3) 1)
                    have b10804 := hb (x (-3) 13)
                    clear * - r10802 b10803 b10804 d10797
                    omega
                  have d10805 : (x (-2) 14).toNat = 0 := by
                    have r10806 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10807 := hb (x (-3) 1)
                    have b10808 := hb (x (-2) 14)
                    clear * - r10806 b10807 b10808 d10801
                    omega
                  have d10809 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                    have r10810 := hand2 (x (-2) 1) (x (-2) 14)
                    have b10811 := hb (x (-2) 14)
                    have b10812 := hb (x (-2) 1 && x (-2) 14)
                    clear * - r10810 b10811 b10812 d10805
                    omega
                  have d10813 : (x (-3) 2).toNat = 1 := by
                    have r10814 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10815 := hb (x (-3) 2)
                    have b10816 := hb (x (-1) 13)
                    have b10817 := hb (x (-2) 1 && x (-2) 14)
                    clear * - r10814 b10815 b10816 b10817 d10765 d10809
                    omega
                  have d10818 : (x (-3) 14).toNat = 1 := by
                    have r10819 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                    have b10820 := hb (x (-3) 2)
                    have b10821 := hb (x (-3) 14)
                    clear * - r10819 b10820 b10821 d10813
                    omega
                  have d10822 : (x (-4) 1).toNat = 0 := by
                    have r10823 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10824 := hb (x (-4) 1)
                    have b10825 := hb (x (-3) 14)
                    clear * - r10823 b10824 b10825 d10818
                    omega
                  have d10826 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
                    have r10827 := hand1 (x (-4) 1) (x (-4) 12)
                    have b10828 := hb (x (-4) 1)
                    have b10829 := hb (x (-4) 1 && x (-4) 12)
                    clear * - r10827 b10828 b10829 d10822
                    omega
                  have d10830 : (x (-7) 4).toNat = 1 := by
                    have r10831 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b10832 := hb (x (-7) 4)
                    have b10833 := hb (x (-3) 11)
                    have b10834 := hb (x (-4) 1 && x (-4) 12)
                    have b10835 := hb (x (-5) 2 && x (-5) 13)
                    have b10836 := hb (x (-6) 3 && x (-6) 14)
                    clear * - r10831 b10832 b10833 b10834 b10835 b10836 d9703 d10826 d10737 d10753
                    omega
                  have d10837 : (x (-7) 12).toNat = 1 := by
                    have r10838 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                    have b10839 := hb (x (-7) 4)
                    have b10840 := hb (x (-7) 12)
                    clear * - r10838 b10839 b10840 d10830
                    omega
                  have d10841 : (x (-8) 13).toNat = 0 := by
                    have r10842 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10843 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                    have e10844 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                    have b10845 := hb (x (-10) 3)
                    have b10846 := hb (x (-9) 2)
                    have b10847 := hb (x (-8) 13)
                    have b10848 := hb (x (-7) 12)
                    clear * - r10842 e10843 e10844 b10845 b10846 b10847 b10848 d10837
                    omega
                  have d10849 : (x (-8) 5).toNat = 0 := by
                    have r10850 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
                    have b10851 := hb (x (-8) 5)
                    have b10852 := hb (x (-8) 13)
                    clear * - r10850 b10851 b10852 d10841
                    omega
                  have d10853 : (x (-4) 9).toNat = 0 := by
                    have r10854 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
                    have b10855 := hb (x (-4) 1)
                    have b10856 := hb (x (-4) 9)
                    clear * - r10854 b10855 b10856 d10822
                    omega
                  have d10857 : (x (-2) 6).toNat = 0 := by
                    have r10858 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
                    have b10859 := hb (x (-2) 6)
                    have b10860 := hb (x (-2) 14)
                    clear * - r10858 b10859 b10860 d10805
                    omega
                  have d10861 : (x (-2) 2 && x (-2) 6).toNat = 0 := by
                    have r10862 := hand2 (x (-2) 2) (x (-2) 6)
                    have b10863 := hb (x (-2) 6)
                    have b10864 := hb (x (-2) 2 && x (-2) 6)
                    clear * - r10862 b10863 b10864 d10857
                    omega
                  have d10865 : (x (-2) 12).toNat = 0 := by
                    have r10866 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10867 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e10868 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b10869 := hb (x (-5) 3)
                    have b10870 := hb (x (-4) 2)
                    have b10871 := hb (x (-3) 13)
                    have b10872 := hb (x (-2) 12)
                    clear * - r10866 e10867 e10868 b10869 b10870 b10871 b10872 d10797
                    omega
                  have d10873 : (x (-4) 2).toNat = 0 := by
                    have r10874 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10875 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e10876 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b10877 := hb (x (-5) 3)
                    have b10878 := hb (x (-4) 2)
                    have b10879 := hb (x (-3) 13)
                    have b10880 := hb (x (-2) 12)
                    clear * - r10874 e10875 e10876 b10877 b10878 b10879 b10880 d10865 d10797
                    omega
                  have d10881 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
                    have r10882 := hand1 (x (-4) 2) (x (-4) 12)
                    have b10883 := hb (x (-4) 2)
                    have b10884 := hb (x (-4) 2 && x (-4) 12)
                    clear * - r10882 b10883 b10884 d10873
                    omega
                  have d10885 : (x (-4) 10).toNat = 0 := by
                    have r10886 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
                    have b10887 := hb (x (-4) 2)
                    have b10888 := hb (x (-4) 10)
                    clear * - r10886 b10887 b10888 d10873
                    omega
                  have d10889 : (x (-5) 3).toNat = 0 := by
                    have r10890 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10891 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e10892 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b10893 := hb (x (-5) 3)
                    have b10894 := hb (x (-4) 2)
                    have b10895 := hb (x (-3) 13)
                    have b10896 := hb (x (-2) 12)
                    clear * - r10890 e10891 e10892 b10893 b10894 b10895 b10896 d10865 d10797 d10873
                    omega
                  have d10897 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
                    have r10898 := hand1 (x (-5) 3) (x (-5) 13)
                    have b10899 := hb (x (-5) 3)
                    have b10900 := hb (x (-5) 3 && x (-5) 13)
                    clear * - r10898 b10899 b10900 d10889
                    omega
                  have d10901 : (x (-5) 11).toNat = 0 := by
                    have r10902 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                    have b10903 := hb (x (-5) 3)
                    have b10904 := hb (x (-5) 11)
                    clear * - r10902 b10903 b10904 d10889
                    omega
                  have d10905 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
                    have r10906 := hand1 (x (-2) 2) (x (-2) 8)
                    have b10907 := hb (x (-2) 2)
                    have b10908 := hb (x (-2) 2 && x (-2) 8)
                    clear * - r10906 b10907 b10908 d10777
                    omega
                  have d10909 : (x 6 8).toNat = 0 := by
                    have r10910 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10911 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e10912 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e10913 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e10914 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e10915 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e10916 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b10917 := hb (x (-1) 7)
                    have b10918 := hb (x 0 6)
                    have b10919 := hb (x 1 5)
                    have b10920 := hb (x 2 4)
                    have b10921 := hb (x 3 11)
                    have b10922 := hb (x 4 10)
                    have b10923 := hb (x 5 9)
                    have b10924 := hb (x 6 8)
                    clear * - r10910 e10911 e10912 e10913 e10914 e10915 e10916 b10917 b10918 b10919 b10920 b10921 b10922 b10923 b10924 d10359 d10704 g2
                    omega
                  have d10925 : (x 5 9).toNat = 0 := by
                    have r10926 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10927 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e10928 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e10929 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e10930 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e10931 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e10932 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b10933 := hb (x (-1) 7)
                    have b10934 := hb (x 0 6)
                    have b10935 := hb (x 1 5)
                    have b10936 := hb (x 2 4)
                    have b10937 := hb (x 3 11)
                    have b10938 := hb (x 4 10)
                    have b10939 := hb (x 5 9)
                    have b10940 := hb (x 6 8)
                    clear * - r10926 e10927 e10928 e10929 e10930 e10931 e10932 b10933 b10934 b10935 b10936 b10937 b10938 b10939 b10940 d10909 d10359 d10704 g2
                    omega
                  have d10941 : (x 4 10).toNat = 0 := by
                    have r10942 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10943 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e10944 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e10945 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e10946 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e10947 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e10948 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b10949 := hb (x (-1) 7)
                    have b10950 := hb (x 0 6)
                    have b10951 := hb (x 1 5)
                    have b10952 := hb (x 2 4)
                    have b10953 := hb (x 3 11)
                    have b10954 := hb (x 4 10)
                    have b10955 := hb (x 5 9)
                    have b10956 := hb (x 6 8)
                    clear * - r10942 e10943 e10944 e10945 e10946 e10947 e10948 b10949 b10950 b10951 b10952 b10953 b10954 b10955 b10956 d10909 d10925 d10359 d10704 g2
                    omega
                  have d10957 : (x 3 11).toNat = 0 := by
                    have r10958 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10959 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e10960 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e10961 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e10962 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e10963 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e10964 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b10965 := hb (x (-1) 7)
                    have b10966 := hb (x 0 6)
                    have b10967 := hb (x 1 5)
                    have b10968 := hb (x 2 4)
                    have b10969 := hb (x 3 11)
                    have b10970 := hb (x 4 10)
                    have b10971 := hb (x 5 9)
                    have b10972 := hb (x 6 8)
                    clear * - r10958 e10959 e10960 e10961 e10962 e10963 e10964 b10965 b10966 b10967 b10968 b10969 b10970 b10971 b10972 d10909 d10925 d10941 d10359 d10704 g2
                    omega
                  have d10973 : (x (-1) 7).toNat = 0 := by
                    have r10974 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10975 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e10976 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e10977 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e10978 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e10979 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e10980 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b10981 := hb (x (-1) 7)
                    have b10982 := hb (x 0 6)
                    have b10983 := hb (x 1 5)
                    have b10984 := hb (x 2 4)
                    have b10985 := hb (x 3 11)
                    have b10986 := hb (x 4 10)
                    have b10987 := hb (x 5 9)
                    have b10988 := hb (x 6 8)
                    clear * - r10974 e10975 e10976 e10977 e10978 e10979 e10980 b10981 b10982 b10983 b10984 b10985 b10986 b10987 b10988 d10909 d10925 d10941 d10957 d10359 d10704 g2
                    omega
                  have d10989 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
                    have r10990 := hand2 (x (-1) 1) (x (-1) 7)
                    have b10991 := hb (x (-1) 7)
                    have b10992 := hb (x (-1) 1 && x (-1) 7)
                    clear * - r10990 b10991 b10992 d10973
                    omega
                  have d10993 : (x 5 8).toNat = 0 := by
                    have r10994 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e10995 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e10996 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e10997 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e10998 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e10999 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e11000 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b11001 := hb (x (-2) 7)
                    have b11002 := hb (x (-1) 6)
                    have b11003 := hb (x 0 5)
                    have b11004 := hb (x 1 4)
                    have b11005 := hb (x 2 11)
                    have b11006 := hb (x 3 10)
                    have b11007 := hb (x 4 9)
                    have b11008 := hb (x 5 8)
                    clear * - r10994 e10995 e10996 e10997 e10998 e10999 e11000 b11001 b11002 b11003 b11004 b11005 b11006 b11007 b11008 d10671 g1
                    omega
                  have d11009 : (x 4 9).toNat = 0 := by
                    have r11010 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11011 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e11012 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e11013 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e11014 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e11015 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e11016 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b11017 := hb (x (-2) 7)
                    have b11018 := hb (x (-1) 6)
                    have b11019 := hb (x 0 5)
                    have b11020 := hb (x 1 4)
                    have b11021 := hb (x 2 11)
                    have b11022 := hb (x 3 10)
                    have b11023 := hb (x 4 9)
                    have b11024 := hb (x 5 8)
                    clear * - r11010 e11011 e11012 e11013 e11014 e11015 e11016 b11017 b11018 b11019 b11020 b11021 b11022 b11023 b11024 d10993 d10671 g1
                    omega
                  have d11025 : (x 3 10).toNat = 0 := by
                    have r11026 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11027 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e11028 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e11029 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e11030 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e11031 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e11032 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b11033 := hb (x (-2) 7)
                    have b11034 := hb (x (-1) 6)
                    have b11035 := hb (x 0 5)
                    have b11036 := hb (x 1 4)
                    have b11037 := hb (x 2 11)
                    have b11038 := hb (x 3 10)
                    have b11039 := hb (x 4 9)
                    have b11040 := hb (x 5 8)
                    clear * - r11026 e11027 e11028 e11029 e11030 e11031 e11032 b11033 b11034 b11035 b11036 b11037 b11038 b11039 b11040 d10993 d11009 d10671 g1
                    omega
                  have d11041 : (x 2 11).toNat = 0 := by
                    have r11042 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11043 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e11044 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e11045 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e11046 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e11047 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e11048 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b11049 := hb (x (-2) 7)
                    have b11050 := hb (x (-1) 6)
                    have b11051 := hb (x 0 5)
                    have b11052 := hb (x 1 4)
                    have b11053 := hb (x 2 11)
                    have b11054 := hb (x 3 10)
                    have b11055 := hb (x 4 9)
                    have b11056 := hb (x 5 8)
                    clear * - r11042 e11043 e11044 e11045 e11046 e11047 e11048 b11049 b11050 b11051 b11052 b11053 b11054 b11055 b11056 d10993 d11009 d11025 d10671 g1
                    omega
                  have d11057 : (x (-1) 6).toNat = 0 := by
                    have r11058 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11059 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e11060 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e11061 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e11062 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e11063 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e11064 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b11065 := hb (x (-2) 7)
                    have b11066 := hb (x (-1) 6)
                    have b11067 := hb (x 0 5)
                    have b11068 := hb (x 1 4)
                    have b11069 := hb (x 2 11)
                    have b11070 := hb (x 3 10)
                    have b11071 := hb (x 4 9)
                    have b11072 := hb (x 5 8)
                    clear * - r11058 e11059 e11060 e11061 e11062 e11063 e11064 b11065 b11066 b11067 b11068 b11069 b11070 b11071 b11072 d10993 d11009 d11025 d11041 d10671 g1
                    omega
                  have d11073 : (x (-2) 7).toNat = 0 := by
                    have r11074 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11075 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e11076 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e11077 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e11078 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e11079 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e11080 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b11081 := hb (x (-2) 7)
                    have b11082 := hb (x (-1) 6)
                    have b11083 := hb (x 0 5)
                    have b11084 := hb (x 1 4)
                    have b11085 := hb (x 2 11)
                    have b11086 := hb (x 3 10)
                    have b11087 := hb (x 4 9)
                    have b11088 := hb (x 5 8)
                    clear * - r11074 e11075 e11076 e11077 e11078 e11079 e11080 b11081 b11082 b11083 b11084 b11085 b11086 b11087 b11088 d10993 d11009 d11025 d11041 d10671 g1 d11057
                    omega
                  have d11089 : (x (-3) 8).toNat = 0 := by
                    have r11090 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11091 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                    have e11092 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                    have e11093 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                    have e11094 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                    have e11095 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                    have e11096 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                    have b11097 := hb (x (-10) 7)
                    have b11098 := hb (x (-9) 6)
                    have b11099 := hb (x (-8) 5)
                    have b11100 := hb (x (-7) 4)
                    have b11101 := hb (x (-6) 11)
                    have b11102 := hb (x (-5) 10)
                    have b11103 := hb (x (-4) 9)
                    have b11104 := hb (x (-3) 8)
                    clear * - r11090 e11091 e11092 e11093 e11094 e11095 e11096 b11097 b11098 b11099 b11100 b11101 b11102 b11103 b11104 d10853 d10741 d10757 d10830 d10849
                    omega
                  have r11105 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11106 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11107 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11108 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e11109 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e11110 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e11111 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e11112 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e11113 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have r11114 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11115 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e11116 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e11117 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e11118 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e11119 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e11120 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have r11121 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11122 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e11123 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e11124 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e11125 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e11126 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e11127 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have r11128 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11129 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
                  have e11130 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
                  have r11131 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11132 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                  have e11133 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                  have r11134 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11135 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11136 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11137 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11138 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r11139 : (x (-10) 2).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp2 (-10))
                  have r11140 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                  have r11141 := hand2 (x (-3) 3) (x (-3) 7)
                  have r11142 := hand2 (x (-8) 8) (x (-8) 12)
                  have r11143 := hand2 (x (-9) 9) (x (-9) 13)
                  have r11144 := hand2 (x 1 3) (x 1 7)
                  have r11145 := hand1 (x (-4) 8) (x (-4) 12)
                  have r11146 := hand1 (x (-5) 9) (x (-5) 13)
                  have r11147 := hand2 (x (-3) 3) (x (-3) 9)
                  have r11148 := hand1 (x (-8) 8) (x (-8) 14)
                  have r11149 := hand2 (x 6 1) (x 6 10)
                  have r11150 := hand2 (x 5 2) (x 5 11)
                  have r11151 := hand1 (x (-6) 4) (x (-6) 14)
                  have r11152 := hand2 (x (-9) 1) (x (-9) 14)
                  have r11153 := hand1 (x 3 1) (x 3 14)
                  linarith only [r11105, r11106, r11107, e11108, e11109, e11110, e11111, e11112, e11113, r11114, e11115, e11116, e11117, e11118, e11119, e11120, r11121, e11122, e11123, e11124, e11125, e11126, e11127, r11128, e11129, e11130, r11131, e11132, e11133, r11134, r11135, r11136, r11137, r11138, r11139, r11140, r11141, r11142, r11143, r11144, r11145, r11146, r11147, r11148, r11149, r11150, r11151, r11152, r11153, d10841, d10837, d10757, d10741, d10901, d10853, d10885, d11089, d10857, d11073, d9675, d10773, d11057, f9864, g1, g2, d10631, d10671, g6, d10320, d10312, d10659, d10647, d10861, d9763, d9791, d9815, d9839, d10316, d9869, d9671, d9699, d9731, d10989, d10905, d9759, d9787, d9811, d9835, d10643, g31, g32, d9719, d10881, d10897]
              · have f11246 : (x (-1) 2).toNat = 1 := by rw [h10336]; rfl
                have d11247 : (x (-1) 14).toNat = 1 := by
                  have r11248 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
                  have b11249 := hb (x (-1) 2)
                  have b11250 := hb (x (-1) 14)
                  clear * - r11248 b11249 b11250 f11246
                  omega
                have d11251 : (x (-2) 1).toNat = 0 := by
                  have r11252 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b11253 := hb (x (-2) 1)
                  have b11254 := hb (x (-1) 14)
                  clear * - r11252 b11253 b11254 d11247
                  omega
                have d11255 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                  have r11256 := hand1 (x (-2) 1) (x (-2) 14)
                  have b11257 := hb (x (-2) 1)
                  have b11258 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r11256 b11257 b11258 d11251
                  omega
                have d11259 : (x (-2) 13).toNat = 0 := by
                  have r11260 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                  have b11261 := hb (x (-2) 1)
                  have b11262 := hb (x (-2) 13)
                  clear * - r11260 b11261 b11262 d11251
                  omega
                have d11263 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
                  have r11264 := hand2 (x (-2) 4) (x (-2) 13)
                  have b11265 := hb (x (-2) 13)
                  have b11266 := hb (x (-2) 4 && x (-2) 13)
                  clear * - r11264 b11265 b11266 d11259
                  omega
                have d11267 : (x (-2) 9).toNat = 0 := by
                  have r11268 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                  have b11269 := hb (x (-2) 1)
                  have b11270 := hb (x (-2) 9)
                  clear * - r11268 b11269 b11270 d11251
                  omega
                have d11271 : (x 1 12).toNat = 0 := by
                  have r11272 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e11273 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                  have e11274 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                  have b11275 := hb (x (-2) 3)
                  have b11276 := hb (x (-1) 2)
                  have b11277 := hb (x 0 13)
                  have b11278 := hb (x 1 12)
                  clear * - r11272 e11273 e11274 b11275 b11276 b11277 b11278 g5 f11246
                  omega
                have d11279 : (x 1 1 && x 1 12).toNat = 0 := by
                  have r11280 := hand2 (x 1 1) (x 1 12)
                  have b11281 := hb (x 1 12)
                  have b11282 := hb (x 1 1 && x 1 12)
                  clear * - r11280 b11281 b11282 d11271
                  omega
                have d11283 : (x 1 4).toNat = 0 := by
                  have r11284 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                  have b11285 := hb (x 1 4)
                  have b11286 := hb (x 1 12)
                  clear * - r11284 b11285 b11286 d11271
                  omega
                have d11287 : (x 1 4 && x 1 14).toNat = 0 := by
                  have r11288 := hand1 (x 1 4) (x 1 14)
                  have b11289 := hb (x 1 4)
                  have b11290 := hb (x 1 4 && x 1 14)
                  clear * - r11288 b11289 b11290 d11283
                  omega
                cases h11291 : x 1 2
                · have f11292 : (x 1 2).toNat = 0 := by rw [h11291]; rfl
                  have d11293 : (x 1 10).toNat = 0 := by
                    have r11294 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
                    have b11295 := hb (x 1 2)
                    have b11296 := hb (x 1 10)
                    clear * - r11294 b11295 b11296 f11292
                    omega
                  have d11297 : (x 1 1 && x 1 10).toNat = 0 := by
                    have r11298 := hand2 (x 1 1) (x 1 10)
                    have b11299 := hb (x 1 10)
                    have b11300 := hb (x 1 1 && x 1 10)
                    clear * - r11298 b11299 b11300 d11293
                    omega
                  have d11301 : (x 3 13).toNat = 1 := by
                    have r11302 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b11303 := hb (x 1 2)
                    have b11304 := hb (x 3 13)
                    have b11305 := hb (x 2 1 && x 2 14)
                    clear * - r11302 b11303 b11304 b11305 d10308 f11292
                    omega
                  have d11306 : (x 3 1).toNat = 1 := by
                    have r11307 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                    have b11308 := hb (x 3 1)
                    have b11309 := hb (x 3 13)
                    clear * - r11307 b11308 b11309 d11301
                    omega
                  have d11310 : (x 4 14).toNat = 0 := by
                    have r11311 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b11312 := hb (x 3 1)
                    have b11313 := hb (x 4 14)
                    clear * - r11311 b11312 b11313 d11306
                    omega
                  have d11314 : (x 4 3 && x 4 14).toNat = 0 := by
                    have r11315 := hand2 (x 4 3) (x 4 14)
                    have b11316 := hb (x 4 14)
                    have b11317 := hb (x 4 3 && x 4 14)
                    clear * - r11315 b11316 b11317 d11310
                    omega
                  have d11318 : (x 4 6).toNat = 0 := by
                    have r11319 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
                    have b11320 := hb (x 4 6)
                    have b11321 := hb (x 4 14)
                    clear * - r11319 b11320 b11321 d11310
                    omega
                  have d11322 : (x 4 2).toNat = 0 := by
                    have r11323 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                    have b11324 := hb (x 4 2)
                    have b11325 := hb (x 4 14)
                    clear * - r11323 b11324 b11325 d11310
                    omega
                  have d11326 : (x 4 10).toNat = 0 := by
                    have r11327 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                    have b11328 := hb (x 4 2)
                    have b11329 := hb (x 4 10)
                    clear * - r11327 b11328 b11329 d11322
                    omega
                  have d11330 : (x 4 3 && x 4 10).toNat = 0 := by
                    have r11331 := hand2 (x 4 3) (x 4 10)
                    have b11332 := hb (x 4 10)
                    have b11333 := hb (x 4 3 && x 4 10)
                    clear * - r11331 b11332 b11333 d11326
                    omega
                  have d11334 : (x 4 12).toNat = 0 := by
                    have r11335 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11336 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e11337 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b11338 := hb (x 1 3)
                    have b11339 := hb (x 2 2)
                    have b11340 := hb (x 3 13)
                    have b11341 := hb (x 4 12)
                    clear * - r11335 e11336 e11337 b11338 b11339 b11340 b11341 d11301 d10320
                    omega
                  have d11342 : (x 1 3).toNat = 0 := by
                    have r11343 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11344 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e11345 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b11346 := hb (x 1 3)
                    have b11347 := hb (x 2 2)
                    have b11348 := hb (x 3 13)
                    have b11349 := hb (x 4 12)
                    clear * - r11343 e11344 e11345 b11346 b11347 b11348 b11349 d11334 d11301 d10320
                    omega
                  have d11350 : (x 1 3 && x 1 14).toNat = 0 := by
                    have r11351 := hand1 (x 1 3) (x 1 14)
                    have b11352 := hb (x 1 3)
                    have b11353 := hb (x 1 3 && x 1 14)
                    clear * - r11351 b11352 b11353 d11342
                    omega
                  have d11354 : (x 1 11).toNat = 0 := by
                    have r11355 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                    have b11356 := hb (x 1 3)
                    have b11357 := hb (x 1 11)
                    clear * - r11355 b11356 b11357 d11342
                    omega
                  have d11358 : (x 1 1 && x 1 11).toNat = 0 := by
                    have r11359 := hand2 (x 1 1) (x 1 11)
                    have b11360 := hb (x 1 11)
                    have b11361 := hb (x 1 1 && x 1 11)
                    clear * - r11359 b11360 b11361 d11354
                    omega
                  have d11362 : (x 3 1 && x 3 12).toNat = 1 := by
                    have r11363 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b11364 := hb (x 0 4)
                    have b11365 := hb (x 4 11)
                    have b11366 := hb (x 3 1 && x 3 12)
                    have b11367 := hb (x 2 2 && x 2 13)
                    have b11368 := hb (x 1 3 && x 1 14)
                    clear * - r11363 b11364 b11365 b11366 b11367 b11368 g10 d10324 d11350 f9864
                    omega
                  have d11369 : (x 3 12).toNat = 1 := by
                    have r11370 := hand2 (x 3 1) (x 3 12)
                    have b11371 := hb (x 3 12)
                    have b11372 := hb (x 3 1 && x 3 12)
                    clear * - r11370 b11371 b11372 d11362
                    omega
                  have d11373 : (x 2 13).toNat = 0 := by
                    have r11374 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11375 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e11376 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b11377 := hb (x 0 3)
                    have b11378 := hb (x 1 2)
                    have b11379 := hb (x 2 13)
                    have b11380 := hb (x 3 12)
                    clear * - r11374 e11375 e11376 b11377 b11378 b11379 b11380 d11369 f11292 f9858
                    omega
                  have d11381 : (x 2 3 && x 2 13).toNat = 0 := by
                    have r11382 := hand2 (x 2 3) (x 2 13)
                    have b11383 := hb (x 2 13)
                    have b11384 := hb (x 2 3 && x 2 13)
                    clear * - r11382 b11383 b11384 d11373
                    omega
                  have d11385 : (x 2 4 && x 2 13).toNat = 0 := by
                    have r11386 := hand2 (x 2 4) (x 2 13)
                    have b11387 := hb (x 2 13)
                    have b11388 := hb (x 2 4 && x 2 13)
                    clear * - r11386 b11387 b11388 d11373
                    omega
                  have d11389 : (x 2 8 && x 2 13).toNat = 0 := by
                    have r11390 := hand2 (x 2 8) (x 2 13)
                    have b11391 := hb (x 2 13)
                    have b11392 := hb (x 2 8 && x 2 13)
                    clear * - r11390 b11391 b11392 d11373
                    omega
                  have d11393 : (x 2 12 && x 2 13).toNat = 0 := by
                    have r11394 := hand2 (x 2 12) (x 2 13)
                    have b11395 := hb (x 2 13)
                    have b11396 := hb (x 2 12 && x 2 13)
                    clear * - r11394 b11395 b11396 d11373
                    omega
                  have d11397 : (x 3 2 && x 3 12).toNat = 1 := by
                    have r11398 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b11399 := hb (x 0 5)
                    have b11400 := hb (x 5 10)
                    have b11401 := hb (x 4 1 && x 4 11)
                    have b11402 := hb (x 3 2 && x 3 12)
                    have b11403 := hb (x 2 3 && x 2 13)
                    have b11404 := hb (x 1 4 && x 1 14)
                    clear * - r11398 b11399 b11400 b11401 b11402 b11403 b11404 g11 g33 d11381 d11287 g1
                    omega
                  have d11405 : (x 3 2).toNat = 1 := by
                    have r11406 := hand1 (x 3 2) (x 3 12)
                    have b11407 := hb (x 3 2)
                    have b11408 := hb (x 3 2 && x 3 12)
                    clear * - r11406 b11407 b11408 d11397
                    omega
                  have d11409 : (x 3 14).toNat = 1 := by
                    have r11410 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                    have b11411 := hb (x 3 2)
                    have b11412 := hb (x 3 14)
                    clear * - r11410 b11411 b11412 d11405
                    omega
                  have d11413 : (x 2 1).toNat = 0 := by
                    have r11414 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b11415 := hb (x 2 1)
                    have b11416 := hb (x 3 14)
                    clear * - r11414 b11415 b11416 d11409
                    omega
                  have d11417 : (x 2 9).toNat = 0 := by
                    have r11418 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
                    have b11419 := hb (x 2 1)
                    have b11420 := hb (x 2 9)
                    clear * - r11418 b11419 b11420 d11413
                    omega
                  have d11421 : (x 5 12).toNat = 0 := by
                    have r11422 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11423 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e11424 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b11425 := hb (x 2 3)
                    have b11426 := hb (x 3 2)
                    have b11427 := hb (x 4 13)
                    have b11428 := hb (x 5 12)
                    clear * - r11422 e11423 e11424 b11425 b11426 b11427 b11428 d11405
                    omega
                  have d11429 : (x 4 13).toNat = 0 := by
                    have r11430 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11431 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e11432 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b11433 := hb (x 2 3)
                    have b11434 := hb (x 3 2)
                    have b11435 := hb (x 4 13)
                    have b11436 := hb (x 5 12)
                    clear * - r11430 e11431 e11432 b11433 b11434 b11435 b11436 d11421 d11405
                    omega
                  have d11437 : (x 2 3).toNat = 0 := by
                    have r11438 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11439 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e11440 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b11441 := hb (x 2 3)
                    have b11442 := hb (x 3 2)
                    have b11443 := hb (x 4 13)
                    have b11444 := hb (x 5 12)
                    clear * - r11438 e11439 e11440 b11441 b11442 b11443 b11444 d11421 d11429 d11405
                    omega
                  have d11445 : (x 2 11).toNat = 0 := by
                    have r11446 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
                    have b11447 := hb (x 2 3)
                    have b11448 := hb (x 2 11)
                    clear * - r11446 b11447 b11448 d11437
                    omega
                  cases h11449 : x (-1) 3
                  · have f11450 : (x (-1) 3).toNat = 0 := by rw [h11449]; rfl
                    have d11451 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
                      have r11452 := hand1 (x (-1) 3) (x (-1) 14)
                      have b11453 := hb (x (-1) 3)
                      have b11454 := hb (x (-1) 3 && x (-1) 14)
                      clear * - r11452 b11453 b11454 f11450
                      omega
                    have d11455 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
                      have r11456 := hand1 (x (-1) 3) (x (-1) 13)
                      have b11457 := hb (x (-1) 3)
                      have b11458 := hb (x (-1) 3 && x (-1) 13)
                      clear * - r11456 b11457 b11458 f11450
                      omega
                    have d11459 : (x (-2) 4).toNat = 1 := by
                      have r11460 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b11461 := hb (x (-2) 4)
                      have b11462 := hb (x 2 11)
                      have b11463 := hb (x 1 1 && x 1 12)
                      have b11464 := hb (x 0 2 && x 0 13)
                      have b11465 := hb (x (-1) 3 && x (-1) 14)
                      clear * - r11460 b11461 b11462 b11463 b11464 b11465 d11445 d11279 g36 d11451
                      omega
                    have d11466 : (x (-2) 12).toNat = 1 := by
                      have r11467 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
                      have b11468 := hb (x (-2) 4)
                      have b11469 := hb (x (-2) 12)
                      clear * - r11467 b11468 b11469 d11459
                      omega
                    have d11470 : (x (-3) 13).toNat = 0 := by
                      have r11471 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11472 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e11473 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b11474 := hb (x (-5) 3)
                      have b11475 := hb (x (-4) 2)
                      have b11476 := hb (x (-3) 13)
                      have b11477 := hb (x (-2) 12)
                      clear * - r11471 e11472 e11473 b11474 b11475 b11476 b11477 d11466
                      omega
                    have d11478 : (x (-3) 5).toNat = 0 := by
                      have r11479 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
                      have b11480 := hb (x (-3) 5)
                      have b11481 := hb (x (-3) 13)
                      clear * - r11479 b11480 b11481 d11470
                      omega
                    have d11482 : (x (-4) 2).toNat = 0 := by
                      have r11483 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11484 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e11485 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b11486 := hb (x (-5) 3)
                      have b11487 := hb (x (-4) 2)
                      have b11488 := hb (x (-3) 13)
                      have b11489 := hb (x (-2) 12)
                      clear * - r11483 e11484 e11485 b11486 b11487 b11488 b11489 d11466 d11470
                      omega
                    have d11490 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
                      have r11491 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b11492 := hb (x (-4) 2)
                      have b11493 := hb (x (-2) 13)
                      have b11494 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r11491 b11492 b11493 b11494 d11259 d11482
                      omega
                    have d11495 : (x (-3) 1).toNat = 1 := by
                      have r11496 := hand1 (x (-3) 1) (x (-3) 14)
                      have b11497 := hb (x (-3) 1)
                      have b11498 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r11496 b11497 b11498 d11490
                      omega
                    have d11499 : (x (-2) 14).toNat = 0 := by
                      have r11500 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b11501 := hb (x (-3) 1)
                      have b11502 := hb (x (-2) 14)
                      clear * - r11500 b11501 b11502 d11495
                      omega
                    have d11503 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
                      have r11504 := hand2 (x (-2) 4) (x (-2) 14)
                      have b11505 := hb (x (-2) 14)
                      have b11506 := hb (x (-2) 4 && x (-2) 14)
                      clear * - r11504 b11505 b11506 d11499
                      omega
                    have r11507 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b11508 := hb (x (-3) 5)
                    have b11509 := hb (x 2 10)
                    have b11510 := hb (x 1 1 && x 1 11)
                    have b11511 := hb (x 0 2 && x 0 12)
                    have b11512 := hb (x (-1) 3 && x (-1) 13)
                    have b11513 := hb (x (-2) 4 && x (-2) 14)
                    linarith only [r11507, b11508, b11509, b11510, b11511, b11512, b11513, d10332, d11358, d9845, d11455, d11503, d11478]
                  · have f11514 : (x (-1) 3).toNat = 1 := by rw [h11449]; rfl
                    have d11515 : (x 2 12).toNat = 0 := by
                      have r11516 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11517 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                      have e11518 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                      have b11519 := hb (x (-1) 3)
                      have b11520 := hb (x 0 2)
                      have b11521 := hb (x 1 13)
                      have b11522 := hb (x 2 12)
                      clear * - r11516 e11517 e11518 b11519 b11520 b11521 b11522 f9844 f11514
                      omega
                    have d11523 : (x 1 13).toNat = 0 := by
                      have r11524 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11525 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                      have e11526 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                      have b11527 := hb (x (-1) 3)
                      have b11528 := hb (x 0 2)
                      have b11529 := hb (x 1 13)
                      have b11530 := hb (x 2 12)
                      clear * - r11524 e11525 e11526 b11527 b11528 b11529 b11530 d11515 f9844 f11514
                      omega
                    have d11531 : (x 1 13 && x 1 14).toNat = 0 := by
                      have r11532 := hand1 (x 1 13) (x 1 14)
                      have b11533 := hb (x 1 13)
                      have b11534 := hb (x 1 13 && x 1 14)
                      clear * - r11532 b11533 b11534 d11523
                      omega
                    have d11535 : (x 1 5).toNat = 0 := by
                      have r11536 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
                      have b11537 := hb (x 1 5)
                      have b11538 := hb (x 1 13)
                      clear * - r11536 b11537 b11538 d11523
                      omega
                    have d11539 : (x 1 5 && x 1 14).toNat = 0 := by
                      have r11540 := hand1 (x 1 5) (x 1 14)
                      have b11541 := hb (x 1 5)
                      have b11542 := hb (x 1 5 && x 1 14)
                      clear * - r11540 b11541 b11542 d11535
                      omega
                    have d11543 : (x 3 3 && x 3 12).toNat = 1 := by
                      have r11544 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b11545 := hb (x 0 6)
                      have b11546 := hb (x 6 9)
                      have b11547 := hb (x 5 1 && x 5 10)
                      have b11548 := hb (x 4 2 && x 4 11)
                      have b11549 := hb (x 3 3 && x 3 12)
                      have b11550 := hb (x 2 4 && x 2 13)
                      have b11551 := hb (x 1 5 && x 1 14)
                      clear * - r11544 b11545 b11546 b11547 b11548 b11549 b11550 b11551 g12 g29 g30 d11385 d11539 g2
                      omega
                    have d11552 : (x 3 3).toNat = 1 := by
                      have r11553 := hand1 (x 3 3) (x 3 12)
                      have b11554 := hb (x 3 3)
                      have b11555 := hb (x 3 3 && x 3 12)
                      clear * - r11553 b11554 b11555 d11543
                      omega
                    have d11556 : (x 6 12).toNat = 0 := by
                      have r11557 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11558 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e11559 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b11560 := hb (x 3 3)
                      have b11561 := hb (x 4 2)
                      have b11562 := hb (x 5 13)
                      have b11563 := hb (x 6 12)
                      clear * - r11557 e11558 e11559 b11560 b11561 b11562 b11563 d11322 d11552
                      omega
                    have d11564 : (x 6 1 && x 6 12).toNat = 0 := by
                      have r11565 := hand2 (x 6 1) (x 6 12)
                      have b11566 := hb (x 6 12)
                      have b11567 := hb (x 6 1 && x 6 12)
                      clear * - r11565 b11566 b11567 d11556
                      omega
                    have d11568 : (x 6 4).toNat = 0 := by
                      have r11569 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                      have b11570 := hb (x 6 4)
                      have b11571 := hb (x 6 12)
                      clear * - r11569 b11570 b11571 d11556
                      omega
                    have d11572 : (x 5 13).toNat = 0 := by
                      have r11573 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11574 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e11575 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b11576 := hb (x 3 3)
                      have b11577 := hb (x 4 2)
                      have b11578 := hb (x 5 13)
                      have b11579 := hb (x 6 12)
                      clear * - r11573 e11574 e11575 b11576 b11577 b11578 b11579 d11556 d11322 d11552
                      omega
                    have d11580 : (x 5 2 && x 5 13).toNat = 0 := by
                      have r11581 := hand2 (x 5 2) (x 5 13)
                      have b11582 := hb (x 5 13)
                      have b11583 := hb (x 5 2 && x 5 13)
                      clear * - r11581 b11582 b11583 d11572
                      omega
                    have d11584 : (x 7 11).toNat = 1 := by
                      have r11585 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b11586 := hb (x 3 4)
                      have b11587 := hb (x 7 11)
                      have b11588 := hb (x 6 1 && x 6 12)
                      have b11589 := hb (x 5 2 && x 5 13)
                      have b11590 := hb (x 4 3 && x 4 14)
                      clear * - r11585 b11586 b11587 b11588 b11589 b11590 d11564 d11580 d11314 g9
                      omega
                    have d11591 : (x 7 3).toNat = 1 := by
                      have r11592 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                      have b11593 := hb (x 7 3)
                      have b11594 := hb (x 7 11)
                      clear * - r11592 b11593 b11594 d11584
                      omega
                    have d11595 : (x 10 12).toNat = 0 := by
                      have r11596 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11597 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                      have e11598 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                      have b11599 := hb (x 7 3)
                      have b11600 := hb (x 8 2)
                      have b11601 := hb (x 9 13)
                      have b11602 := hb (x 10 12)
                      clear * - r11596 e11597 e11598 b11599 b11600 b11601 b11602 d11591
                      omega
                    have d11603 : (x 10 4).toNat = 0 := by
                      have r11604 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                      have b11605 := hb (x 10 4)
                      have b11606 := hb (x 10 12)
                      clear * - r11604 b11605 b11606 d11595
                      omega
                    have d11607 : (x 10 4 && x 10 13).toNat = 0 := by
                      have r11608 := hand1 (x 10 4) (x 10 13)
                      have b11609 := hb (x 10 4)
                      have b11610 := hb (x 10 4 && x 10 13)
                      clear * - r11608 b11609 b11610 d11603
                      omega
                    have d11611 : (x 10 4 && x 10 5).toNat = 0 := by
                      have r11612 := hand1 (x 10 4) (x 10 5)
                      have b11613 := hb (x 10 4)
                      have b11614 := hb (x 10 4 && x 10 5)
                      clear * - r11612 b11613 b11614 d11603
                      omega
                    have d11615 : (x 9 13).toNat = 0 := by
                      have r11616 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11617 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                      have e11618 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                      have b11619 := hb (x 7 3)
                      have b11620 := hb (x 8 2)
                      have b11621 := hb (x 9 13)
                      have b11622 := hb (x 10 12)
                      clear * - r11616 e11617 e11618 b11619 b11620 b11621 b11622 d11595 d11591
                      omega
                    have d11623 : (x 9 5).toNat = 0 := by
                      have r11624 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
                      have b11625 := hb (x 9 5)
                      have b11626 := hb (x 9 13)
                      clear * - r11624 b11625 b11626 d11615
                      omega
                    have d11627 : (x 9 5 && x 9 14).toNat = 0 := by
                      have r11628 := hand1 (x 9 5) (x 9 14)
                      have b11629 := hb (x 9 5)
                      have b11630 := hb (x 9 5 && x 9 14)
                      clear * - r11628 b11629 b11630 d11623
                      omega
                    have d11631 : (x 9 5 && x 9 6).toNat = 0 := by
                      have r11632 := hand1 (x 9 5) (x 9 6)
                      have b11633 := hb (x 9 5)
                      have b11634 := hb (x 9 5 && x 9 6)
                      clear * - r11632 b11633 b11634 d11623
                      omega
                    have d11635 : (x 8 2).toNat = 0 := by
                      have r11636 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11637 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                      have e11638 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                      have b11639 := hb (x 7 3)
                      have b11640 := hb (x 8 2)
                      have b11641 := hb (x 9 13)
                      have b11642 := hb (x 10 12)
                      clear * - r11636 e11637 e11638 b11639 b11640 b11641 b11642 d11595 d11615 d11591
                      omega
                    have d11643 : (x 8 2 && x 8 7).toNat = 0 := by
                      have r11644 := hand1 (x 8 2) (x 8 7)
                      have b11645 := hb (x 8 2)
                      have b11646 := hb (x 8 2 && x 8 7)
                      clear * - r11644 b11645 b11646 d11635
                      omega
                    have d11647 : (x 8 10).toNat = 0 := by
                      have r11648 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                      have b11649 := hb (x 8 2)
                      have b11650 := hb (x 8 10)
                      clear * - r11648 b11649 b11650 d11635
                      omega
                    have d11651 : (x 5 5).toNat = 0 := by
                      have r11652 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                      have b11653 := hb (x 5 5)
                      have b11654 := hb (x 5 13)
                      clear * - r11652 b11653 b11654 d11572
                      omega
                    have d11655 : (x 10 8).toNat = 0 := by
                      have r11656 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11657 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                      have e11658 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                      have e11659 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                      have e11660 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                      have e11661 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                      have e11662 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                      have b11663 := hb (x 3 7)
                      have b11664 := hb (x 4 6)
                      have b11665 := hb (x 5 5)
                      have b11666 := hb (x 6 4)
                      have b11667 := hb (x 7 11)
                      have b11668 := hb (x 8 10)
                      have b11669 := hb (x 9 9)
                      have b11670 := hb (x 10 8)
                      clear * - r11656 e11657 e11658 e11659 e11660 e11661 e11662 b11663 b11664 b11665 b11666 b11667 b11668 b11669 b11670 d11647 d11584 d11568 d11651 d11318
                      omega
                    have d11671 : (x 9 9).toNat = 0 := by
                      have r11672 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11673 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                      have e11674 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                      have e11675 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                      have e11676 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                      have e11677 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                      have e11678 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                      have b11679 := hb (x 3 7)
                      have b11680 := hb (x 4 6)
                      have b11681 := hb (x 5 5)
                      have b11682 := hb (x 6 4)
                      have b11683 := hb (x 7 11)
                      have b11684 := hb (x 8 10)
                      have b11685 := hb (x 9 9)
                      have b11686 := hb (x 10 8)
                      clear * - r11672 e11673 e11674 e11675 e11676 e11677 e11678 b11679 b11680 b11681 b11682 b11683 b11684 b11685 b11686 d11655 d11647 d11584 d11568 d11651 d11318
                      omega
                    have d11687 : (x 3 7).toNat = 0 := by
                      have r11688 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e11689 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                      have e11690 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                      have e11691 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                      have e11692 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                      have e11693 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                      have e11694 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                      have b11695 := hb (x 3 7)
                      have b11696 := hb (x 4 6)
                      have b11697 := hb (x 5 5)
                      have b11698 := hb (x 6 4)
                      have b11699 := hb (x 7 11)
                      have b11700 := hb (x 8 10)
                      have b11701 := hb (x 9 9)
                      have b11702 := hb (x 10 8)
                      clear * - r11688 e11689 e11690 e11691 e11692 e11693 e11694 b11695 b11696 b11697 b11698 b11699 b11700 b11701 b11702 d11655 d11671 d11647 d11584 d11568 d11651 d11318
                      omega
                    have d11703 : (x 3 7 && x 3 12).toNat = 0 := by
                      have r11704 := hand1 (x 3 7) (x 3 12)
                      have b11705 := hb (x 3 7)
                      have b11706 := hb (x 3 7 && x 3 12)
                      clear * - r11704 b11705 b11706 d11687
                      omega
                    have r11707 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11708 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11709 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11710 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                    have e11711 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                    have e11712 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                    have e11713 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                    have e11714 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                    have e11715 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                    have r11716 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11717 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                    have e11718 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                    have e11719 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                    have e11720 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                    have e11721 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                    have e11722 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                    have r11723 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11724 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e11725 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e11726 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e11727 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e11728 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e11729 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have r11730 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11731 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e11732 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have r11733 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11734 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                    have e11735 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                    have r11736 : 1 ≤ (x 14 1).toNat + (x 13 1 && x 13 2).toNat + (x 12 2 && x 12 3).toNat + (x 11 3 && x 11 4).toNat + (x 10 4 && x 10 5).toNat + (x 9 5 && x 9 6).toNat + (x 8 6 && x 8 7).toNat + (x 7 7 && x 7 8).toNat + (x 6 8 && x 6 9).toNat + (x 5 9 && x 5 10).toNat + (x 4 10 && x 4 11).toNat + (x 3 11 && x 3 12).toNat + (x 2 12 && x 2 13).toNat + (x 1 13 && x 1 14).toNat + (x 0 14).toNat := by have q := hcov1 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11737 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11738 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11739 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11740 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11741 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11742 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11743 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11744 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r11745 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
                    have r11746 := hand2 (x 13 1) (x 13 2)
                    have r11747 := hand2 (x 12 2) (x 12 3)
                    have r11748 := hand2 (x 11 3) (x 11 4)
                    have r11749 := hand2 (x 8 6) (x 8 7)
                    have r11750 := hand1 (x 3 11) (x 3 12)
                    have r11751 := hand2 (x 9 1) (x 9 6)
                    have r11752 := hand1 (x 1 9) (x 1 14)
                    have r11753 := hand2 (x 6 1) (x 6 8)
                    have r11754 := hand2 (x 5 2) (x 5 9)
                    have r11755 := hand1 (x (-4) 3) (x (-4) 12)
                    have r11756 := hand1 (x (-5) 4) (x (-5) 13)
                    have r11757 := hand1 (x (-6) 5) (x (-6) 14)
                    have r11758 := hand2 (x (-1) 3) (x (-1) 12)
                    have r11759 := hand1 (x (-3) 5) (x (-3) 14)
                    have r11760 := hand2 (x 13 1) (x 13 10)
                    have r11761 := hand2 (x 12 2) (x 12 11)
                    have r11762 := hand1 (x 11 3) (x 11 12)
                    have r11763 := hand2 (x (-1) 1) (x (-1) 11)
                    have r11764 := hand1 (x (-2) 2) (x (-2) 12)
                    have r11765 := hand1 (x (-3) 3) (x (-3) 13)
                    have r11766 := hand1 (x 13 1) (x 13 14)
                    linarith only [r11707, r11708, r11709, e11710, e11711, e11712, e11713, e11714, e11715, r11716, e11717, e11718, e11719, e11720, e11721, e11722, r11723, e11724, e11725, e11726, e11727, e11728, e11729, r11730, e11731, e11732, r11733, e11734, e11735, r11736, r11737, r11738, r11739, r11740, r11741, r11742, r11743, r11744, r11745, r11746, r11747, r11748, r11749, r11750, r11751, r11752, r11753, r11754, r11755, r11756, r11757, r11758, r11759, r11760, r11761, r11762, r11763, r11764, r11765, r11766, d9767, d11267, d11259, d9651, d9853, f9874, f9876, d11523, g7, d11417, d11515, d11373, d11369, d11326, g10, g11, g12, g13, d11623, d11603, d11611, d11631, g14, g15, g16, g17, d11393, d11531, d11643, g20, g21, g22, g23, d11703, d11389, d11330, g25, g26, g27, d9877, d9691, d9723, d11297, d9849, d11263, d11607, d11627, d9751, d11255]
                · have f11877 : (x 1 2).toNat = 1 := by rw [h11291]; rfl
                  have d11878 : (x 3 12).toNat = 0 := by
                    have r11879 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11880 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e11881 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b11882 := hb (x 0 3)
                    have b11883 := hb (x 1 2)
                    have b11884 := hb (x 2 13)
                    have b11885 := hb (x 3 12)
                    clear * - r11879 e11880 e11881 b11882 b11883 b11884 b11885 f11877 f9858
                    omega
                  have d11886 : (x 3 2 && x 3 12).toNat = 0 := by
                    have r11887 := hand2 (x 3 2) (x 3 12)
                    have b11888 := hb (x 3 12)
                    have b11889 := hb (x 3 2 && x 3 12)
                    clear * - r11887 b11888 b11889 d11878
                    omega
                  have d11890 : (x 2 13).toNat = 0 := by
                    have r11891 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e11892 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e11893 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b11894 := hb (x 0 3)
                    have b11895 := hb (x 1 2)
                    have b11896 := hb (x 2 13)
                    have b11897 := hb (x 3 12)
                    clear * - r11891 e11892 e11893 b11894 b11895 b11896 b11897 d11878 f11877 f9858
                    omega
                  have d11898 : (x 2 3 && x 2 13).toNat = 0 := by
                    have r11899 := hand2 (x 2 3) (x 2 13)
                    have b11900 := hb (x 2 13)
                    have b11901 := hb (x 2 3 && x 2 13)
                    clear * - r11899 b11900 b11901 d11890
                    omega
                  have r11902 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b11903 := hb (x 0 5)
                  have b11904 := hb (x 5 10)
                  have b11905 := hb (x 4 1 && x 4 11)
                  have b11906 := hb (x 3 2 && x 3 12)
                  have b11907 := hb (x 2 3 && x 2 13)
                  have b11908 := hb (x 1 4 && x 1 14)
                  linarith only [r11902, b11903, b11904, b11905, b11906, b11907, b11908, g11, g33, d11886, d11898, d11287, g1]
          · have f11909 : (x 0 14).toNat = 1 := by rw [h9875]; rfl
            have d11910 : (x (-1) 1).toNat = 0 := by
              have r11911 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b11912 := hb (x (-1) 1)
              have b11913 := hb (x 0 14)
              clear * - r11911 b11912 b11913 f11909
              omega
            have d11914 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
              have r11915 := hand1 (x (-1) 1) (x (-1) 14)
              have b11916 := hb (x (-1) 1)
              have b11917 := hb (x (-1) 1 && x (-1) 14)
              clear * - r11915 b11916 b11917 d11910
              omega
            have d11918 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
              have r11919 := hand1 (x (-1) 1) (x (-1) 12)
              have b11920 := hb (x (-1) 1)
              have b11921 := hb (x (-1) 1 && x (-1) 12)
              clear * - r11919 b11920 b11921 d11910
              omega
            have d11922 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
              have r11923 := hand1 (x (-1) 1) (x (-1) 10)
              have b11924 := hb (x (-1) 1)
              have b11925 := hb (x (-1) 1 && x (-1) 10)
              clear * - r11923 b11924 b11925 d11910
              omega
            have d11926 : (x (-1) 13).toNat = 0 := by
              have r11927 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
              have b11928 := hb (x (-1) 1)
              have b11929 := hb (x (-1) 13)
              clear * - r11927 b11928 b11929 d11910
              omega
            have d11930 : (x (-2) 2).toNat = 1 := by
              have r11931 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b11932 := hb (x (-2) 2)
              have b11933 := hb (x 0 13)
              have b11934 := hb (x (-1) 1 && x (-1) 14)
              clear * - r11931 b11932 b11933 b11934 g5 d11914
              omega
            have d11935 : (x (-3) 3).toNat = 0 := by
              have r11936 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e11937 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e11938 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have b11939 := hb (x (-3) 3)
              have b11940 := hb (x (-2) 2)
              have b11941 := hb (x (-1) 13)
              have b11942 := hb (x 0 12)
              clear * - r11936 e11937 e11938 b11939 b11940 b11941 b11942 f9874 d11926 d11930
              omega
            have d11943 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
              have r11944 := hand1 (x (-3) 3) (x (-3) 14)
              have b11945 := hb (x (-3) 3)
              have b11946 := hb (x (-3) 3 && x (-3) 14)
              clear * - r11944 b11945 b11946 d11935
              omega
            have d11947 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
              have r11948 := hand1 (x (-3) 3) (x (-3) 12)
              have b11949 := hb (x (-3) 3)
              have b11950 := hb (x (-3) 3 && x (-3) 12)
              clear * - r11948 b11949 b11950 d11935
              omega
            have d11951 : (x (-2) 2 && x (-2) 13).toNat = 1 := by
              have r11952 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b11953 := hb (x (-4) 4)
              have b11954 := hb (x 0 11)
              have b11955 := hb (x (-1) 1 && x (-1) 12)
              have b11956 := hb (x (-2) 2 && x (-2) 13)
              have b11957 := hb (x (-3) 3 && x (-3) 14)
              clear * - r11952 b11953 b11954 b11955 b11956 b11957 d9859 d11918 d11943 d9735
              omega
            have d11958 : (x (-2) 13).toNat = 1 := by
              have r11959 := hand2 (x (-2) 2) (x (-2) 13)
              have b11960 := hb (x (-2) 13)
              have b11961 := hb (x (-2) 2 && x (-2) 13)
              clear * - r11959 b11960 b11961 d11951
              omega
            have d11962 : (x (-2) 1).toNat = 1 := by
              have r11963 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b11964 := hb (x (-2) 1)
              have b11965 := hb (x (-2) 13)
              clear * - r11963 b11964 b11965 d11958
              omega
            have d11966 : (x (-1) 14).toNat = 0 := by
              have r11967 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b11968 := hb (x (-2) 1)
              have b11969 := hb (x (-1) 14)
              clear * - r11967 b11968 b11969 d11962
              omega
            have d11970 : (x (-1) 6).toNat = 0 := by
              have r11971 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
              have b11972 := hb (x (-1) 6)
              have b11973 := hb (x (-1) 14)
              clear * - r11971 b11972 b11973 d11966
              omega
            have d11974 : (x (-1) 2).toNat = 0 := by
              have r11975 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
              have b11976 := hb (x (-1) 2)
              have b11977 := hb (x (-1) 14)
              clear * - r11975 b11976 b11977 d11966
              omega
            have d11978 : (x (-1) 10).toNat = 0 := by
              have r11979 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
              have b11980 := hb (x (-1) 2)
              have b11981 := hb (x (-1) 10)
              clear * - r11979 b11980 b11981 d11974
              omega
            have d11982 : (x 1 13).toNat = 1 := by
              have r11983 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b11984 := hb (x (-1) 2)
              have b11985 := hb (x 1 13)
              have b11986 := hb (x 0 1 && x 0 14)
              clear * - r11983 b11984 b11985 b11986 g37 d11974
              omega
            have d11987 : (x 2 12).toNat = 0 := by
              have r11988 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e11989 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
              have e11990 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
              have b11991 := hb (x (-1) 3)
              have b11992 := hb (x 0 2)
              have b11993 := hb (x 1 13)
              have b11994 := hb (x 2 12)
              clear * - r11988 e11989 e11990 b11991 b11992 b11993 b11994 d11982 f9844
              omega
            have d11995 : (x 2 3 && x 2 12).toNat = 0 := by
              have r11996 := hand2 (x 2 3) (x 2 12)
              have b11997 := hb (x 2 12)
              have b11998 := hb (x 2 3 && x 2 12)
              clear * - r11996 b11997 b11998 d11987
              omega
            have d11999 : (x 2 7 && x 2 12).toNat = 0 := by
              have r12000 := hand2 (x 2 7) (x 2 12)
              have b12001 := hb (x 2 12)
              have b12002 := hb (x 2 7 && x 2 12)
              clear * - r12000 b12001 b12002 d11987
              omega
            have d12003 : (x (-2) 2 && x (-2) 11).toNat = 1 := by
              have r12004 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b12005 := hb (x (-6) 6)
              have b12006 := hb (x 0 9)
              have b12007 := hb (x (-1) 1 && x (-1) 10)
              have b12008 := hb (x (-2) 2 && x (-2) 11)
              have b12009 := hb (x (-3) 3 && x (-3) 12)
              have b12010 := hb (x (-4) 4 && x (-4) 13)
              have b12011 := hb (x (-5) 5 && x (-5) 14)
              clear * - r12004 b12005 b12006 b12007 b12008 b12009 b12010 b12011 g4 d11922 d11947 d9755 d9783 d9795
              omega
            have d12012 : (x (-2) 11).toNat = 1 := by
              have r12013 := hand2 (x (-2) 2) (x (-2) 11)
              have b12014 := hb (x (-2) 11)
              have b12015 := hb (x (-2) 2 && x (-2) 11)
              clear * - r12013 b12014 b12015 d12003
              omega
            have d12016 : (x (-2) 3).toNat = 1 := by
              have r12017 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
              have b12018 := hb (x (-2) 3)
              have b12019 := hb (x (-2) 11)
              clear * - r12017 b12018 b12019 d12012
              omega
            have d12020 : (x 1 12).toNat = 0 := by
              have r12021 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12022 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
              have e12023 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
              have b12024 := hb (x (-2) 3)
              have b12025 := hb (x (-1) 2)
              have b12026 := hb (x 0 13)
              have b12027 := hb (x 1 12)
              clear * - r12021 e12022 e12023 b12024 b12025 b12026 b12027 g5 d11974 d12016
              omega
            have d12028 : (x 1 4).toNat = 0 := by
              have r12029 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
              have b12030 := hb (x 1 4)
              have b12031 := hb (x 1 12)
              clear * - r12029 b12030 b12031 d12020
              omega
            have d12032 : (x 1 4 && x 1 14).toNat = 0 := by
              have r12033 := hand1 (x 1 4) (x 1 14)
              have b12034 := hb (x 1 4)
              have b12035 := hb (x 1 4 && x 1 14)
              clear * - r12033 b12034 b12035 d12028
              omega
            have d12036 : (x 1 4 && x 1 13).toNat = 0 := by
              have r12037 := hand1 (x 1 4) (x 1 13)
              have b12038 := hb (x 1 4)
              have b12039 := hb (x 1 4 && x 1 13)
              clear * - r12037 b12038 b12039 d12028
              omega
            have d12040 : (x 1 8).toNat = 0 := by
              have r12041 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e12042 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e12043 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e12044 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e12045 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e12046 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e12047 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b12048 := hb (x (-6) 7)
              have b12049 := hb (x (-5) 6)
              have b12050 := hb (x (-4) 5)
              have b12051 := hb (x (-3) 4)
              have b12052 := hb (x (-2) 11)
              have b12053 := hb (x (-1) 10)
              have b12054 := hb (x 0 9)
              have b12055 := hb (x 1 8)
              clear * - r12041 e12042 e12043 e12044 e12045 e12046 e12047 b12048 b12049 b12050 b12051 b12052 b12053 b12054 b12055 g4 d11978 d12012
              omega
            have d12056 : (x 1 8 && x 1 13).toNat = 0 := by
              have r12057 := hand1 (x 1 8) (x 1 13)
              have b12058 := hb (x 1 8)
              have b12059 := hb (x 1 8 && x 1 13)
              clear * - r12057 b12058 b12059 d12040
              omega
            have r12060 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12061 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12062 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e12063 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e12064 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e12065 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e12066 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e12067 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have r12068 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12069 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e12070 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have r12071 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12072 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12073 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12074 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r12075 := hand2 (x 8 1) (x 8 6)
            have r12076 := hand2 (x 7 2) (x 7 7)
            have r12077 := hand2 (x 6 3) (x 6 8)
            have r12078 := hand1 (x 5 4) (x 5 9)
            have r12079 := hand1 (x 4 5) (x 4 10)
            have r12080 := hand1 (x 3 6) (x 3 11)
            have r12081 := hand2 (x 4 1) (x 4 10)
            have r12082 := hand2 (x 3 2) (x 3 11)
            have r12083 := hand1 (x 3 2) (x 3 12)
            have r12084 := hand1 (x 2 3) (x 2 13)
            have r12085 := hand2 (x 6 1) (x 6 11)
            have r12086 := hand2 (x 5 2) (x 5 12)
            have r12087 := hand2 (x 4 3) (x 4 13)
            linarith only [r12060, r12061, e12062, e12063, e12064, e12065, e12066, e12067, r12068, e12069, e12070, r12071, r12072, r12073, r12074, r12075, r12076, r12077, r12078, r12079, r12080, r12081, r12082, r12083, r12084, r12085, r12086, r12087, d11970, d11978, g1, f11909, d11982, g8, d11987, g11, d11999, d12056, g19, d11995, d12036, g28, g33, d12032, g34]
        · have f12141 : (x 0 12).toNat = 1 := by rw [h9873]; rfl
          have d12142 : (x (-1) 13).toNat = 0 := by
            have r12143 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12144 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e12145 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b12146 := hb (x (-3) 3)
            have b12147 := hb (x (-2) 2)
            have b12148 := hb (x (-1) 13)
            have b12149 := hb (x 0 12)
            clear * - r12143 e12144 e12145 b12146 b12147 b12148 b12149 f12141
            omega
          have d12150 : (x (-2) 2).toNat = 0 := by
            have r12151 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12152 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e12153 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b12154 := hb (x (-3) 3)
            have b12155 := hb (x (-2) 2)
            have b12156 := hb (x (-1) 13)
            have b12157 := hb (x 0 12)
            clear * - r12151 e12152 e12153 b12154 b12155 b12156 b12157 f12141 d12142
            omega
          have d12158 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
            have r12159 := hand1 (x (-2) 2) (x (-2) 13)
            have b12160 := hb (x (-2) 2)
            have b12161 := hb (x (-2) 2 && x (-2) 13)
            clear * - r12159 b12160 b12161 d12150
            omega
          have d12162 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
            have r12163 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b12164 := hb (x (-2) 2)
            have b12165 := hb (x 0 13)
            have b12166 := hb (x (-1) 1 && x (-1) 14)
            clear * - r12163 b12164 b12165 b12166 g5 d12150
            omega
          have d12167 : (x (-1) 14).toNat = 1 := by
            have r12168 := hand2 (x (-1) 1) (x (-1) 14)
            have b12169 := hb (x (-1) 14)
            have b12170 := hb (x (-1) 1 && x (-1) 14)
            clear * - r12168 b12169 b12170 d12162
            omega
          have d12171 : (x (-2) 1).toNat = 0 := by
            have r12172 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b12173 := hb (x (-2) 1)
            have b12174 := hb (x (-1) 14)
            clear * - r12172 b12173 b12174 d12167
            omega
          have d12175 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r12176 := hand1 (x (-2) 1) (x (-2) 14)
            have b12177 := hb (x (-2) 1)
            have b12178 := hb (x (-2) 1 && x (-2) 14)
            clear * - r12176 b12177 b12178 d12171
            omega
          have d12179 : (x (-3) 2).toNat = 1 := by
            have r12180 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b12181 := hb (x (-3) 2)
            have b12182 := hb (x (-1) 13)
            have b12183 := hb (x (-2) 1 && x (-2) 14)
            clear * - r12180 b12181 b12182 b12183 d12142 d12175
            omega
          have d12184 : (x (-2) 13).toNat = 0 := by
            have r12185 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b12186 := hb (x (-2) 1)
            have b12187 := hb (x (-2) 13)
            clear * - r12185 b12186 b12187 d12171
            omega
          have d12188 : (x (-3) 3).toNat = 0 := by
            have r12189 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12190 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e12191 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b12192 := hb (x (-3) 3)
            have b12193 := hb (x (-2) 2)
            have b12194 := hb (x (-1) 13)
            have b12195 := hb (x 0 12)
            clear * - r12189 e12190 e12191 b12192 b12193 b12194 b12195 f12141 d12142 d12150
            omega
          have d12196 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
            have r12197 := hand1 (x (-3) 3) (x (-3) 14)
            have b12198 := hb (x (-3) 3)
            have b12199 := hb (x (-3) 3 && x (-3) 14)
            clear * - r12197 b12198 b12199 d12188
            omega
          have d12200 : (x (-1) 12).toNat = 0 := by
            have r12201 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e12202 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e12203 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b12204 := hb (x (-4) 3)
            have b12205 := hb (x (-3) 2)
            have b12206 := hb (x (-2) 13)
            have b12207 := hb (x (-1) 12)
            clear * - r12201 e12202 e12203 b12204 b12205 b12206 b12207 d12184 d12179
            omega
          have d12208 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
            have r12209 := hand2 (x (-1) 1) (x (-1) 12)
            have b12210 := hb (x (-1) 12)
            have b12211 := hb (x (-1) 1 && x (-1) 12)
            clear * - r12209 b12210 b12211 d12200
            omega
          have r12212 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12213 := hb (x (-4) 4)
          have b12214 := hb (x 0 11)
          have b12215 := hb (x (-1) 1 && x (-1) 12)
          have b12216 := hb (x (-2) 2 && x (-2) 13)
          have b12217 := hb (x (-3) 3 && x (-3) 14)
          linarith only [r12212, b12213, b12214, b12215, b12216, b12217, d9859, d12208, d12158, d12196, d9735]
      · have f12218 : (x 0 4).toNat = 1 := by rw [h9863]; rfl
        have d12219 : (x 0 12).toNat = 1 := by
          have r12220 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
          have b12221 := hb (x 0 4)
          have b12222 := hb (x 0 12)
          clear * - r12220 b12221 b12222 f12218
          omega
        have d12223 : (x (-1) 13).toNat = 0 := by
          have r12224 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12225 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e12226 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b12227 := hb (x (-3) 3)
          have b12228 := hb (x (-2) 2)
          have b12229 := hb (x (-1) 13)
          have b12230 := hb (x 0 12)
          clear * - r12224 e12225 e12226 b12227 b12228 b12229 b12230 d12219
          omega
        have d12231 : (x (-2) 2).toNat = 0 := by
          have r12232 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12233 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e12234 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b12235 := hb (x (-3) 3)
          have b12236 := hb (x (-2) 2)
          have b12237 := hb (x (-1) 13)
          have b12238 := hb (x 0 12)
          clear * - r12232 e12233 e12234 b12235 b12236 b12237 b12238 d12219 d12223
          omega
        have d12239 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
          have r12240 := hand1 (x (-2) 2) (x (-2) 13)
          have b12241 := hb (x (-2) 2)
          have b12242 := hb (x (-2) 2 && x (-2) 13)
          clear * - r12240 b12241 b12242 d12231
          omega
        have d12243 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
          have r12244 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12245 := hb (x (-2) 2)
          have b12246 := hb (x 0 13)
          have b12247 := hb (x (-1) 1 && x (-1) 14)
          clear * - r12244 b12245 b12246 b12247 g5 d12231
          omega
        have d12248 : (x (-1) 14).toNat = 1 := by
          have r12249 := hand2 (x (-1) 1) (x (-1) 14)
          have b12250 := hb (x (-1) 14)
          have b12251 := hb (x (-1) 1 && x (-1) 14)
          clear * - r12249 b12250 b12251 d12243
          omega
        have d12252 : (x (-2) 1).toNat = 0 := by
          have r12253 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12254 := hb (x (-2) 1)
          have b12255 := hb (x (-1) 14)
          clear * - r12253 b12254 b12255 d12248
          omega
        have d12256 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r12257 := hand1 (x (-2) 1) (x (-2) 14)
          have b12258 := hb (x (-2) 1)
          have b12259 := hb (x (-2) 1 && x (-2) 14)
          clear * - r12257 b12258 b12259 d12252
          omega
        have d12260 : (x (-3) 2).toNat = 1 := by
          have r12261 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12262 := hb (x (-3) 2)
          have b12263 := hb (x (-1) 13)
          have b12264 := hb (x (-2) 1 && x (-2) 14)
          clear * - r12261 b12262 b12263 b12264 d12223 d12256
          omega
        have d12265 : (x (-2) 13).toNat = 0 := by
          have r12266 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b12267 := hb (x (-2) 1)
          have b12268 := hb (x (-2) 13)
          clear * - r12266 b12267 b12268 d12252
          omega
        have d12269 : (x (-3) 3).toNat = 0 := by
          have r12270 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12271 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e12272 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b12273 := hb (x (-3) 3)
          have b12274 := hb (x (-2) 2)
          have b12275 := hb (x (-1) 13)
          have b12276 := hb (x 0 12)
          clear * - r12270 e12271 e12272 b12273 b12274 b12275 b12276 d12219 d12223 d12231
          omega
        have d12277 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
          have r12278 := hand1 (x (-3) 3) (x (-3) 14)
          have b12279 := hb (x (-3) 3)
          have b12280 := hb (x (-3) 3 && x (-3) 14)
          clear * - r12278 b12279 b12280 d12269
          omega
        have d12281 : (x (-1) 12).toNat = 0 := by
          have r12282 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12283 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e12284 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b12285 := hb (x (-4) 3)
          have b12286 := hb (x (-3) 2)
          have b12287 := hb (x (-2) 13)
          have b12288 := hb (x (-1) 12)
          clear * - r12282 e12283 e12284 b12285 b12286 b12287 b12288 d12265 d12260
          omega
        have d12289 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
          have r12290 := hand2 (x (-1) 1) (x (-1) 12)
          have b12291 := hb (x (-1) 12)
          have b12292 := hb (x (-1) 1 && x (-1) 12)
          clear * - r12290 b12291 b12292 d12281
          omega
        have r12293 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12294 := hb (x (-4) 4)
        have b12295 := hb (x 0 11)
        have b12296 := hb (x (-1) 1 && x (-1) 12)
        have b12297 := hb (x (-2) 2 && x (-2) 13)
        have b12298 := hb (x (-3) 3 && x (-3) 14)
        linarith only [r12293, b12294, b12295, b12296, b12297, b12298, d9859, d12289, d12239, d12277, d9735]
    · have f12299 : (x 0 3).toNat = 1 := by rw [h9857]; rfl
      have d12300 : (x 3 12).toNat = 0 := by
        have r12301 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12302 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e12303 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b12304 := hb (x 0 3)
        have b12305 := hb (x 1 2)
        have b12306 := hb (x 2 13)
        have b12307 := hb (x 3 12)
        clear * - r12301 e12302 e12303 b12304 b12305 b12306 b12307 f12299
        omega
      have d12308 : (x 3 1 && x 3 12).toNat = 0 := by
        have r12309 := hand2 (x 3 1) (x 3 12)
        have b12310 := hb (x 3 12)
        have b12311 := hb (x 3 1 && x 3 12)
        clear * - r12309 b12310 b12311 d12300
        omega
      have d12312 : (x 3 2 && x 3 12).toNat = 0 := by
        have r12313 := hand2 (x 3 2) (x 3 12)
        have b12314 := hb (x 3 12)
        have b12315 := hb (x 3 2 && x 3 12)
        clear * - r12313 b12314 b12315 d12300
        omega
      have d12316 : (x 2 13).toNat = 0 := by
        have r12317 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12318 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e12319 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b12320 := hb (x 0 3)
        have b12321 := hb (x 1 2)
        have b12322 := hb (x 2 13)
        have b12323 := hb (x 3 12)
        clear * - r12317 e12318 e12319 b12320 b12321 b12322 b12323 d12300 f12299
        omega
      have d12324 : (x 2 2 && x 2 13).toNat = 0 := by
        have r12325 := hand2 (x 2 2) (x 2 13)
        have b12326 := hb (x 2 13)
        have b12327 := hb (x 2 2 && x 2 13)
        clear * - r12325 b12326 b12327 d12316
        omega
      have d12328 : (x 2 3 && x 2 13).toNat = 0 := by
        have r12329 := hand2 (x 2 3) (x 2 13)
        have b12330 := hb (x 2 13)
        have b12331 := hb (x 2 3 && x 2 13)
        clear * - r12329 b12330 b12331 d12316
        omega
      have d12332 : (x 1 1 && x 1 14).toNat = 1 := by
        have r12333 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12334 := hb (x 0 2)
        have b12335 := hb (x 2 13)
        have b12336 := hb (x 1 1 && x 1 14)
        clear * - r12333 b12334 b12335 b12336 d12316 f9844
        omega
      have d12337 : (x 1 1).toNat = 1 := by
        have r12338 := hand1 (x 1 1) (x 1 14)
        have b12339 := hb (x 1 1)
        have b12340 := hb (x 1 1 && x 1 14)
        clear * - r12338 b12339 b12340 d12332
        omega
      have d12341 : (x 2 14).toNat = 0 := by
        have r12342 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12343 := hb (x 1 1)
        have b12344 := hb (x 2 14)
        clear * - r12342 b12343 b12344 d12337
        omega
      have d12345 : (x 2 1 && x 2 14).toNat = 0 := by
        have r12346 := hand2 (x 2 1) (x 2 14)
        have b12347 := hb (x 2 14)
        have b12348 := hb (x 2 1 && x 2 14)
        clear * - r12346 b12347 b12348 d12341
        omega
      have d12349 : (x 2 2).toNat = 0 := by
        have r12350 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b12351 := hb (x 2 2)
        have b12352 := hb (x 2 14)
        clear * - r12350 b12351 b12352 d12341
        omega
      have d12353 : (x 1 2).toNat = 0 := by
        have r12354 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12355 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e12356 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b12357 := hb (x 0 3)
        have b12358 := hb (x 1 2)
        have b12359 := hb (x 2 13)
        have b12360 := hb (x 3 12)
        clear * - r12354 e12355 e12356 b12357 b12358 b12359 b12360 d12300 d12316 f12299
        omega
      have d12361 : (x 3 13).toNat = 1 := by
        have r12362 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12363 := hb (x 1 2)
        have b12364 := hb (x 3 13)
        have b12365 := hb (x 2 1 && x 2 14)
        clear * - r12362 b12363 b12364 b12365 d12345 d12353
        omega
      have d12366 : (x 4 12).toNat = 0 := by
        have r12367 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12368 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e12369 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b12370 := hb (x 1 3)
        have b12371 := hb (x 2 2)
        have b12372 := hb (x 3 13)
        have b12373 := hb (x 4 12)
        clear * - r12367 e12368 e12369 b12370 b12371 b12372 b12373 d12361 d12349
        omega
      have d12374 : (x 1 3).toNat = 0 := by
        have r12375 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12376 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e12377 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b12378 := hb (x 1 3)
        have b12379 := hb (x 2 2)
        have b12380 := hb (x 3 13)
        have b12381 := hb (x 4 12)
        clear * - r12375 e12376 e12377 b12378 b12379 b12380 b12381 d12366 d12361 d12349
        omega
      have d12382 : (x 1 3 && x 1 14).toNat = 0 := by
        have r12383 := hand1 (x 1 3) (x 1 14)
        have b12384 := hb (x 1 3)
        have b12385 := hb (x 1 3 && x 1 14)
        clear * - r12383 b12384 b12385 d12374
        omega
      have d12386 : (x 0 4).toNat = 1 := by
        have r12387 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12388 := hb (x 0 4)
        have b12389 := hb (x 4 11)
        have b12390 := hb (x 3 1 && x 3 12)
        have b12391 := hb (x 2 2 && x 2 13)
        have b12392 := hb (x 1 3 && x 1 14)
        clear * - r12387 b12388 b12389 b12390 b12391 b12392 g10 d12308 d12324 d12382
        omega
      have d12393 : (x 0 12).toNat = 1 := by
        have r12394 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
        have b12395 := hb (x 0 4)
        have b12396 := hb (x 0 12)
        clear * - r12394 b12395 b12396 d12386
        omega
      have d12397 : (x (-1) 13).toNat = 0 := by
        have r12398 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12399 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e12400 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b12401 := hb (x (-3) 3)
        have b12402 := hb (x (-2) 2)
        have b12403 := hb (x (-1) 13)
        have b12404 := hb (x 0 12)
        clear * - r12398 e12399 e12400 b12401 b12402 b12403 b12404 d12393
        omega
      have d12405 : (x (-2) 2).toNat = 0 := by
        have r12406 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12407 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e12408 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b12409 := hb (x (-3) 3)
        have b12410 := hb (x (-2) 2)
        have b12411 := hb (x (-1) 13)
        have b12412 := hb (x 0 12)
        clear * - r12406 e12407 e12408 b12409 b12410 b12411 b12412 d12393 d12397
        omega
      have d12413 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
        have r12414 := hand1 (x (-2) 2) (x (-2) 12)
        have b12415 := hb (x (-2) 2)
        have b12416 := hb (x (-2) 2 && x (-2) 12)
        clear * - r12414 b12415 b12416 d12405
        omega
      have d12417 : (x (-3) 3).toNat = 0 := by
        have r12418 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12419 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e12420 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b12421 := hb (x (-3) 3)
        have b12422 := hb (x (-2) 2)
        have b12423 := hb (x (-1) 13)
        have b12424 := hb (x 0 12)
        clear * - r12418 e12419 e12420 b12421 b12422 b12423 b12424 d12393 d12397 d12405
        omega
      have d12425 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
        have r12426 := hand1 (x (-3) 3) (x (-3) 13)
        have b12427 := hb (x (-3) 3)
        have b12428 := hb (x (-3) 3 && x (-3) 13)
        clear * - r12426 b12427 b12428 d12417
        omega
      have d12429 : (x 1 4 && x 1 14).toNat = 1 := by
        have r12430 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12431 := hb (x 0 5)
        have b12432 := hb (x 5 10)
        have b12433 := hb (x 4 1 && x 4 11)
        have b12434 := hb (x 3 2 && x 3 12)
        have b12435 := hb (x 2 3 && x 2 13)
        have b12436 := hb (x 1 4 && x 1 14)
        clear * - r12430 b12431 b12432 b12433 b12434 b12435 b12436 g11 g33 d12312 d12328 g1
        omega
      have d12437 : (x 1 4).toNat = 1 := by
        have r12438 := hand1 (x 1 4) (x 1 14)
        have b12439 := hb (x 1 4)
        have b12440 := hb (x 1 4 && x 1 14)
        clear * - r12438 b12439 b12440 d12429
        omega
      have d12441 : (x 1 12).toNat = 1 := by
        have r12442 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
        have b12443 := hb (x 1 4)
        have b12444 := hb (x 1 12)
        clear * - r12442 b12443 b12444 d12437
        omega
      have d12445 : (x (-1) 2).toNat = 0 := by
        have r12446 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12447 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e12448 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b12449 := hb (x (-2) 3)
        have b12450 := hb (x (-1) 2)
        have b12451 := hb (x 0 13)
        have b12452 := hb (x 1 12)
        clear * - r12446 e12447 e12448 b12449 b12450 b12451 b12452 d12441 g5
        omega
      have d12453 : (x 1 13).toNat = 1 := by
        have r12454 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b12455 := hb (x (-1) 2)
        have b12456 := hb (x 1 13)
        have b12457 := hb (x 0 1 && x 0 14)
        clear * - r12454 b12455 b12456 b12457 g37 d12445
        omega
      have d12458 : (x 2 12).toNat = 0 := by
        have r12459 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12460 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e12461 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b12462 := hb (x (-1) 3)
        have b12463 := hb (x 0 2)
        have b12464 := hb (x 1 13)
        have b12465 := hb (x 2 12)
        clear * - r12459 e12460 e12461 b12462 b12463 b12464 b12465 d12453 f9844
        omega
      have d12466 : (x (-1) 3).toNat = 0 := by
        have r12467 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12468 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e12469 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b12470 := hb (x (-1) 3)
        have b12471 := hb (x 0 2)
        have b12472 := hb (x 1 13)
        have b12473 := hb (x 2 12)
        clear * - r12467 e12468 e12469 b12470 b12471 b12472 b12473 d12458 d12453 f9844
        omega
      have d12474 : (x (-1) 11).toNat = 0 := by
        have r12475 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
        have b12476 := hb (x (-1) 3)
        have b12477 := hb (x (-1) 11)
        clear * - r12475 b12476 b12477 d12466
        omega
      have d12478 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
        have r12479 := hand2 (x (-1) 1) (x (-1) 11)
        have b12480 := hb (x (-1) 11)
        have b12481 := hb (x (-1) 1 && x (-1) 11)
        clear * - r12479 b12480 b12481 d12474
        omega
      have r12482 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12483 := hb (x (-5) 5)
      have b12484 := hb (x 0 10)
      have b12485 := hb (x (-1) 1 && x (-1) 11)
      have b12486 := hb (x (-2) 2 && x (-2) 12)
      have b12487 := hb (x (-3) 3 && x (-3) 13)
      have b12488 := hb (x (-4) 4 && x (-4) 14)
      linarith only [r12482, b12483, b12484, b12485, b12486, b12487, b12488, d9853, d12478, d12413, d12425, d9751, d9767]
  · have f12489 : (x 0 2).toNat = 1 := by rw [h9843]; rfl
    have d12490 : (x 0 14).toNat = 1 := by
      have r12491 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b12492 := hb (x 0 2)
      have b12493 := hb (x 0 14)
      clear * - r12491 b12492 b12493 f12489
      omega
    have d12494 : (x (-1) 1).toNat = 0 := by
      have r12495 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12496 := hb (x (-1) 1)
      have b12497 := hb (x 0 14)
      clear * - r12495 b12496 b12497 d12490
      omega
    have d12498 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r12499 := hand1 (x (-1) 1) (x (-1) 14)
      have b12500 := hb (x (-1) 1)
      have b12501 := hb (x (-1) 1 && x (-1) 14)
      clear * - r12499 b12500 b12501 d12494
      omega
    have d12502 : (x (-1) 13).toNat = 0 := by
      have r12503 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b12504 := hb (x (-1) 1)
      have b12505 := hb (x (-1) 13)
      clear * - r12503 b12504 b12505 d12494
      omega
    have d12506 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
      have r12507 := hand2 (x (-1) 2) (x (-1) 13)
      have b12508 := hb (x (-1) 13)
      have b12509 := hb (x (-1) 2 && x (-1) 13)
      clear * - r12507 b12508 b12509 d12502
      omega
    have d12510 : (x (-2) 2).toNat = 1 := by
      have r12511 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12512 := hb (x (-2) 2)
      have b12513 := hb (x 0 13)
      have b12514 := hb (x (-1) 1 && x (-1) 14)
      clear * - r12511 b12512 b12513 b12514 g5 d12498
      omega
    have d12515 : (x (-2) 14).toNat = 1 := by
      have r12516 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
      have b12517 := hb (x (-2) 2)
      have b12518 := hb (x (-2) 14)
      clear * - r12516 b12517 b12518 d12510
      omega
    have d12519 : (x (-3) 1).toNat = 0 := by
      have r12520 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12521 := hb (x (-3) 1)
      have b12522 := hb (x (-2) 14)
      clear * - r12520 b12521 b12522 d12515
      omega
    have d12523 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
      have r12524 := hand1 (x (-3) 1) (x (-3) 14)
      have b12525 := hb (x (-3) 1)
      have b12526 := hb (x (-3) 1 && x (-3) 14)
      clear * - r12524 b12525 b12526 d12519
      omega
    have d12527 : (x (-3) 13).toNat = 0 := by
      have r12528 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b12529 := hb (x (-3) 1)
      have b12530 := hb (x (-3) 13)
      clear * - r12528 b12529 b12530 d12519
      omega
    have d12531 : (x 2 12).toNat = 0 := by
      have r12532 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12533 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e12534 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b12535 := hb (x (-1) 3)
      have b12536 := hb (x 0 2)
      have b12537 := hb (x 1 13)
      have b12538 := hb (x 2 12)
      clear * - r12532 e12533 e12534 b12535 b12536 b12537 b12538 f12489
      omega
    have d12539 : (x 2 1 && x 2 12).toNat = 0 := by
      have r12540 := hand2 (x 2 1) (x 2 12)
      have b12541 := hb (x 2 12)
      have b12542 := hb (x 2 1 && x 2 12)
      clear * - r12540 b12541 b12542 d12531
      omega
    have d12543 : (x 1 13).toNat = 0 := by
      have r12544 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12545 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e12546 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b12547 := hb (x (-1) 3)
      have b12548 := hb (x 0 2)
      have b12549 := hb (x 1 13)
      have b12550 := hb (x 2 12)
      clear * - r12544 e12545 e12546 b12547 b12548 b12549 b12550 d12531 f12489
      omega
    have d12551 : (x 1 2 && x 1 13).toNat = 0 := by
      have r12552 := hand2 (x 1 2) (x 1 13)
      have b12553 := hb (x 1 13)
      have b12554 := hb (x 1 2 && x 1 13)
      clear * - r12552 b12553 b12554 d12543
      omega
    have d12555 : (x (-1) 2).toNat = 1 := by
      have r12556 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12557 := hb (x (-1) 2)
      have b12558 := hb (x 1 13)
      have b12559 := hb (x 0 1 && x 0 14)
      clear * - r12556 b12557 b12558 b12559 d12543 g37
      omega
    have d12560 : (x (-1) 14).toNat = 1 := by
      have r12561 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
      have b12562 := hb (x (-1) 2)
      have b12563 := hb (x (-1) 14)
      clear * - r12561 b12562 b12563 d12555
      omega
    have d12564 : (x (-2) 1).toNat = 0 := by
      have r12565 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12566 := hb (x (-2) 1)
      have b12567 := hb (x (-1) 14)
      clear * - r12565 b12566 b12567 d12560
      omega
    have d12568 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r12569 := hand1 (x (-2) 1) (x (-2) 14)
      have b12570 := hb (x (-2) 1)
      have b12571 := hb (x (-2) 1 && x (-2) 14)
      clear * - r12569 b12570 b12571 d12564
      omega
    have d12572 : (x (-3) 2).toNat = 1 := by
      have r12573 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12574 := hb (x (-3) 2)
      have b12575 := hb (x (-1) 13)
      have b12576 := hb (x (-2) 1 && x (-2) 14)
      clear * - r12573 b12574 b12575 b12576 d12502 d12568
      omega
    have d12577 : (x (-3) 14).toNat = 1 := by
      have r12578 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b12579 := hb (x (-3) 2)
      have b12580 := hb (x (-3) 14)
      clear * - r12578 b12579 b12580 d12572
      omega
    have d12581 : (x (-4) 1).toNat = 0 := by
      have r12582 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12583 := hb (x (-4) 1)
      have b12584 := hb (x (-3) 14)
      clear * - r12582 b12583 b12584 d12577
      omega
    have d12585 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
      have r12586 := hand1 (x (-4) 1) (x (-4) 14)
      have b12587 := hb (x (-4) 1)
      have b12588 := hb (x (-4) 1 && x (-4) 14)
      clear * - r12586 b12587 b12588 d12581
      omega
    have d12589 : (x (-5) 2).toNat = 1 := by
      have r12590 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12591 := hb (x (-5) 2)
      have b12592 := hb (x (-3) 13)
      have b12593 := hb (x (-4) 1 && x (-4) 14)
      clear * - r12590 b12591 b12592 b12593 d12527 d12585
      omega
    have d12594 : (x (-4) 13).toNat = 0 := by
      have r12595 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b12596 := hb (x (-4) 1)
      have b12597 := hb (x (-4) 13)
      clear * - r12595 b12596 b12597 d12581
      omega
    have d12598 : (x (-2) 13).toNat = 0 := by
      have r12599 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b12600 := hb (x (-2) 1)
      have b12601 := hb (x (-2) 13)
      clear * - r12599 b12600 b12601 d12564
      omega
    have d12602 : (x (-4) 2).toNat = 1 := by
      have r12603 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12604 := hb (x (-4) 2)
      have b12605 := hb (x (-2) 13)
      have b12606 := hb (x (-3) 1 && x (-3) 14)
      clear * - r12603 b12604 b12605 b12606 d12598 d12523
      omega
    have d12607 : (x (-1) 3).toNat = 0 := by
      have r12608 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12609 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e12610 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b12611 := hb (x (-1) 3)
      have b12612 := hb (x 0 2)
      have b12613 := hb (x 1 13)
      have b12614 := hb (x 2 12)
      clear * - r12608 e12609 e12610 b12611 b12612 b12613 b12614 d12531 d12543 f12489
      omega
    have d12615 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
      have r12616 := hand1 (x (-1) 3) (x (-1) 14)
      have b12617 := hb (x (-1) 3)
      have b12618 := hb (x (-1) 3 && x (-1) 14)
      clear * - r12616 b12617 b12618 d12607
      omega
    have d12619 : (x 1 12).toNat = 0 := by
      have r12620 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12621 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e12622 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b12623 := hb (x (-2) 3)
      have b12624 := hb (x (-1) 2)
      have b12625 := hb (x 0 13)
      have b12626 := hb (x 1 12)
      clear * - r12620 e12621 e12622 b12623 b12624 b12625 b12626 g5 d12555
      omega
    have d12627 : (x 1 1 && x 1 12).toNat = 0 := by
      have r12628 := hand2 (x 1 1) (x 1 12)
      have b12629 := hb (x 1 12)
      have b12630 := hb (x 1 1 && x 1 12)
      clear * - r12628 b12629 b12630 d12619
      omega
    have d12631 : (x (-2) 3).toNat = 0 := by
      have r12632 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12633 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e12634 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b12635 := hb (x (-2) 3)
      have b12636 := hb (x (-1) 2)
      have b12637 := hb (x 0 13)
      have b12638 := hb (x 1 12)
      clear * - r12632 e12633 e12634 b12635 b12636 b12637 b12638 d12619 g5 d12555
      omega
    have d12639 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
      have r12640 := hand1 (x (-2) 3) (x (-2) 14)
      have b12641 := hb (x (-2) 3)
      have b12642 := hb (x (-2) 3 && x (-2) 14)
      clear * - r12640 b12641 b12642 d12631
      omega
    have d12643 : (x (-1) 12).toNat = 0 := by
      have r12644 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12645 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e12646 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b12647 := hb (x (-4) 3)
      have b12648 := hb (x (-3) 2)
      have b12649 := hb (x (-2) 13)
      have b12650 := hb (x (-1) 12)
      clear * - r12644 e12645 e12646 b12647 b12648 b12649 b12650 d12598 d12572
      omega
    have d12651 : (x (-1) 4).toNat = 0 := by
      have r12652 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b12653 := hb (x (-1) 4)
      have b12654 := hb (x (-1) 12)
      clear * - r12652 b12653 b12654 d12643
      omega
    have d12655 : (x (-2) 12).toNat = 0 := by
      have r12656 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12657 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e12658 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b12659 := hb (x (-5) 3)
      have b12660 := hb (x (-4) 2)
      have b12661 := hb (x (-3) 13)
      have b12662 := hb (x (-2) 12)
      clear * - r12656 e12657 e12658 b12659 b12660 b12661 b12662 d12527 d12602
      omega
    have d12663 : (x (-2) 4).toNat = 0 := by
      have r12664 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have b12665 := hb (x (-2) 4)
      have b12666 := hb (x (-2) 12)
      clear * - r12664 b12665 b12666 d12655
      omega
    have d12667 : (x (-3) 12).toNat = 0 := by
      have r12668 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12669 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e12670 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b12671 := hb (x (-6) 3)
      have b12672 := hb (x (-5) 2)
      have b12673 := hb (x (-4) 13)
      have b12674 := hb (x (-3) 12)
      clear * - r12668 e12669 e12670 b12671 b12672 b12673 b12674 d12594 d12589
      omega
    have d12675 : (x (-3) 4).toNat = 0 := by
      have r12676 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b12677 := hb (x (-3) 4)
      have b12678 := hb (x (-3) 12)
      clear * - r12676 b12677 b12678 d12667
      omega
    have d12679 : (x 2 11).toNat = 1 := by
      have r12680 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12681 := hb (x (-2) 4)
      have b12682 := hb (x 2 11)
      have b12683 := hb (x 1 1 && x 1 12)
      have b12684 := hb (x 0 2 && x 0 13)
      have b12685 := hb (x (-1) 3 && x (-1) 14)
      clear * - r12680 b12681 b12682 b12683 b12684 b12685 d12627 g36 d12615 d12663
      omega
    have d12686 : (x 2 3).toNat = 1 := by
      have r12687 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have b12688 := hb (x 2 3)
      have b12689 := hb (x 2 11)
      clear * - r12687 b12688 b12689 d12679
      omega
    have d12690 : (x 5 12).toNat = 0 := by
      have r12691 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12692 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e12693 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b12694 := hb (x 2 3)
      have b12695 := hb (x 3 2)
      have b12696 := hb (x 4 13)
      have b12697 := hb (x 5 12)
      clear * - r12691 e12692 e12693 b12694 b12695 b12696 b12697 d12686
      omega
    have d12698 : (x 4 13).toNat = 0 := by
      have r12699 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12700 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e12701 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b12702 := hb (x 2 3)
      have b12703 := hb (x 3 2)
      have b12704 := hb (x 4 13)
      have b12705 := hb (x 5 12)
      clear * - r12699 e12700 e12701 b12702 b12703 b12704 b12705 d12690 d12686
      omega
    have d12706 : (x 3 2).toNat = 0 := by
      have r12707 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12708 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e12709 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b12710 := hb (x 2 3)
      have b12711 := hb (x 3 2)
      have b12712 := hb (x 4 13)
      have b12713 := hb (x 5 12)
      clear * - r12707 e12708 e12709 b12710 b12711 b12712 b12713 d12690 d12698 d12686
      omega
    have d12714 : (x 1 11).toNat = 1 := by
      have r12715 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12716 := hb (x (-3) 4)
      have b12717 := hb (x 1 11)
      have b12718 := hb (x 0 1 && x 0 12)
      have b12719 := hb (x (-1) 2 && x (-1) 13)
      have b12720 := hb (x (-2) 3 && x (-2) 14)
      clear * - r12715 b12716 b12717 b12718 b12719 b12720 g35 d12506 d12639 d12675
      omega
    have d12721 : (x 1 3).toNat = 1 := by
      have r12722 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b12723 := hb (x 1 3)
      have b12724 := hb (x 1 11)
      clear * - r12722 b12723 b12724 d12714
      omega
    have d12725 : (x 4 12).toNat = 0 := by
      have r12726 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12727 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e12728 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b12729 := hb (x 1 3)
      have b12730 := hb (x 2 2)
      have b12731 := hb (x 3 13)
      have b12732 := hb (x 4 12)
      clear * - r12726 e12727 e12728 b12729 b12730 b12731 b12732 d12721
      omega
    have d12733 : (x 3 13).toNat = 0 := by
      have r12734 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12735 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e12736 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b12737 := hb (x 1 3)
      have b12738 := hb (x 2 2)
      have b12739 := hb (x 3 13)
      have b12740 := hb (x 4 12)
      clear * - r12734 e12735 e12736 b12737 b12738 b12739 b12740 d12725 d12721
      omega
    have d12741 : (x 2 2).toNat = 0 := by
      have r12742 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12743 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e12744 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b12745 := hb (x 1 3)
      have b12746 := hb (x 2 2)
      have b12747 := hb (x 3 13)
      have b12748 := hb (x 4 12)
      clear * - r12742 e12743 e12744 b12745 b12746 b12747 b12748 d12725 d12733 d12721
      omega
    have d12749 : (x 3 1 && x 3 14).toNat = 1 := by
      have r12750 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12751 := hb (x 2 2)
      have b12752 := hb (x 4 13)
      have b12753 := hb (x 3 1 && x 3 14)
      clear * - r12750 b12751 b12752 b12753 d12698 d12741
      omega
    have d12754 : (x 3 14).toNat = 1 := by
      have r12755 := hand2 (x 3 1) (x 3 14)
      have b12756 := hb (x 3 14)
      have b12757 := hb (x 3 1 && x 3 14)
      clear * - r12755 b12756 b12757 d12749
      omega
    have d12758 : (x 2 1).toNat = 0 := by
      have r12759 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12760 := hb (x 2 1)
      have b12761 := hb (x 3 14)
      clear * - r12759 b12760 b12761 d12754
      omega
    have d12762 : (x 2 1 && x 2 14).toNat = 0 := by
      have r12763 := hand1 (x 2 1) (x 2 14)
      have b12764 := hb (x 2 1)
      have b12765 := hb (x 2 1 && x 2 14)
      clear * - r12763 b12764 b12765 d12758
      omega
    have d12766 : (x 1 2).toNat = 1 := by
      have r12767 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12768 := hb (x 1 2)
      have b12769 := hb (x 3 13)
      have b12770 := hb (x 2 1 && x 2 14)
      clear * - r12767 b12768 b12769 b12770 d12733 d12762
      omega
    have d12771 : (x 3 12).toNat = 0 := by
      have r12772 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12773 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e12774 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b12775 := hb (x 0 3)
      have b12776 := hb (x 1 2)
      have b12777 := hb (x 2 13)
      have b12778 := hb (x 3 12)
      clear * - r12772 e12773 e12774 b12775 b12776 b12777 b12778 d12766
      omega
    have d12779 : (x 2 13).toNat = 0 := by
      have r12780 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12781 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e12782 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b12783 := hb (x 0 3)
      have b12784 := hb (x 1 2)
      have b12785 := hb (x 2 13)
      have b12786 := hb (x 3 12)
      clear * - r12780 e12781 e12782 b12783 b12784 b12785 b12786 d12771 d12766
      omega
    have d12787 : (x 0 3).toNat = 0 := by
      have r12788 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12789 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e12790 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b12791 := hb (x 0 3)
      have b12792 := hb (x 1 2)
      have b12793 := hb (x 2 13)
      have b12794 := hb (x 3 12)
      clear * - r12788 e12789 e12790 b12791 b12792 b12793 b12794 d12771 d12779 d12766
      omega
    have d12795 : (x 0 3 && x 0 14).toNat = 0 := by
      have r12796 := hand1 (x 0 3) (x 0 14)
      have b12797 := hb (x 0 3)
      have b12798 := hb (x 0 3 && x 0 14)
      clear * - r12796 b12797 b12798 d12787
      omega
    have d12799 : (x 3 11).toNat = 1 := by
      have r12800 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12801 := hb (x (-1) 4)
      have b12802 := hb (x 3 11)
      have b12803 := hb (x 2 1 && x 2 12)
      have b12804 := hb (x 1 2 && x 1 13)
      have b12805 := hb (x 0 3 && x 0 14)
      clear * - r12800 b12801 b12802 b12803 b12804 b12805 d12539 d12551 d12795 d12651
      omega
    have d12806 : (x 3 3).toNat = 1 := by
      have r12807 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b12808 := hb (x 3 3)
      have b12809 := hb (x 3 11)
      clear * - r12807 b12808 b12809 d12799
      omega
    have d12810 : (x 6 12).toNat = 0 := by
      have r12811 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12812 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e12813 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b12814 := hb (x 3 3)
      have b12815 := hb (x 4 2)
      have b12816 := hb (x 5 13)
      have b12817 := hb (x 6 12)
      clear * - r12811 e12812 e12813 b12814 b12815 b12816 b12817 d12806
      omega
    have d12818 : (x 5 13).toNat = 0 := by
      have r12819 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e12820 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e12821 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b12822 := hb (x 3 3)
      have b12823 := hb (x 4 2)
      have b12824 := hb (x 5 13)
      have b12825 := hb (x 6 12)
      clear * - r12819 e12820 e12821 b12822 b12823 b12824 b12825 d12810 d12806
      omega
    have d12826 : (x 4 1 && x 4 14).toNat = 1 := by
      have r12827 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12828 := hb (x 3 2)
      have b12829 := hb (x 5 13)
      have b12830 := hb (x 4 1 && x 4 14)
      clear * - r12827 b12828 b12829 b12830 d12818 d12706
      omega
    have d12831 : (x 4 14).toNat = 1 := by
      have r12832 := hand2 (x 4 1) (x 4 14)
      have b12833 := hb (x 4 14)
      have b12834 := hb (x 4 1 && x 4 14)
      clear * - r12832 b12833 b12834 d12826
      omega
    have d12835 : (x 3 1).toNat = 0 := by
      have r12836 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b12837 := hb (x 3 1)
      have b12838 := hb (x 4 14)
      clear * - r12836 b12837 b12838 d12831
      omega
    have r12839 := hand1 (x 3 1) (x 3 14)
    have b12840 := hb (x 3 1)
    have b12841 := hb (x 3 1 && x 3 14)
    linarith only [r12839, b12840, b12841, d12749, d12835]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b01 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 1).toNat = 0)
    (g1 : (x 0 5).toNat = 0)
    (g2 : (x 0 6).toNat = 0)
    (g3 : (x 0 8).toNat = 1)
    (g4 : (x 0 9).toNat = 0)
    (g5 : (x 0 13).toNat = 0)
    (g6 : (x 1 6).toNat = 0)
    (g7 : (x 1 14).toNat = 1)
    (g8 : (x 2 5).toNat = 0)
    (g9 : (x 3 4).toNat = 0)
    (g10 : (x 4 11).toNat = 0)
    (g11 : (x 5 10).toNat = 0)
    (g12 : (x 6 9).toNat = 0)
    (g13 : (x 7 8).toNat = 0)
    (g14 : (x 7 7 && x 7 8).toNat = 0)
    (g15 : (x 6 8 && x 6 9).toNat = 0)
    (g16 : (x 5 9 && x 5 10).toNat = 0)
    (g17 : (x 4 10 && x 4 11).toNat = 0)
    (g18 : (x 0 6 && x 0 10).toNat = 0)
    (g19 : (x 0 9 && x 0 14).toNat = 0)
    (g20 : (x 7 3 && x 7 8).toNat = 0)
    (g21 : (x 6 4 && x 6 9).toNat = 0)
    (g22 : (x 5 5 && x 5 10).toNat = 0)
    (g23 : (x 4 6 && x 4 11).toNat = 0)
    (g24 : (x 0 1 && x 0 8).toNat = 0)
    (g25 : (x 3 4 && x 3 11).toNat = 0)
    (g26 : (x 2 5 && x 2 12).toNat = 0)
    (g27 : (x 1 6 && x 1 13).toNat = 0)
    (g28 : (x 0 5 && x 0 14).toNat = 0)
    (g29 : (x 5 1 && x 5 10).toNat = 0)
    (g30 : (x 4 2 && x 4 11).toNat = 0)
    (g31 : (x 3 4 && x 3 13).toNat = 0)
    (g32 : (x 2 5 && x 2 14).toNat = 0)
    (g33 : (x 4 1 && x 4 11).toNat = 0)
    (g34 : (x 3 4 && x 3 14).toNat = 0)
    (g35 : (x 0 1 && x 0 12).toNat = 0)
    (g36 : (x 0 2 && x 0 13).toNat = 0)
    (g37 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b01_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37
