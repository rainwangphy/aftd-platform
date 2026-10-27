import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b01

Topic: combinatorics   Node: c2e1f91e038e

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core: under the layer-free tight-cover constraints for k = 15 and 35 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b01_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-1) 10).toNat = 0)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 0 8).toNat = 1)
    (g4 : (x 0 10).toNat = 0)
    (g5 : (x 0 12).toNat = 0)
    (g6 : (x 1 4).toNat = 0)
    (g7 : (x 1 6).toNat = 0)
    (g8 : (x 1 10).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 3 6).toNat = 0)
    (g12 : (x 3 10).toNat = 0)
    (g13 : (x 3 2 && x 3 6).toNat = 0)
    (g14 : (x 1 4 && x 1 8).toNat = 0)
    (g15 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g16 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g17 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g18 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g19 : (x 3 1 && x 3 10).toNat = 0)
    (g20 : (x 1 3 && x 1 12).toNat = 0)
    (g21 : (x 0 4 && x 0 13).toNat = 0)
    (g22 : (x 0 1 && x 0 11).toNat = 0)
    (g23 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g24 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g25 : (x 0 2 && x 0 12).toNat = 0)
    (g26 : (x 1 2 && x 1 12).toNat = 0)
    (g27 : (x 0 3 && x 0 13).toNat = 0)
    (g28 : (x 3 2 && x 3 12).toNat = 0)
    (g29 : (x 1 4 && x 1 14).toNat = 0)
    (g30 : (x 3 4 && x 3 14).toNat = 0)
    (g31 : (x 0 1 && x 0 12).toNat = 0)
    (g32 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g33 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g34 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d9688 : (x (-1) 9).toNat = 0 := by
    have r9689 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9690 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9691 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9692 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9693 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9694 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9695 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9696 := hb (x (-7) 7)
    have b9697 := hb (x (-6) 6)
    have b9698 := hb (x (-5) 5)
    have b9699 := hb (x (-4) 4)
    have b9700 := hb (x (-3) 11)
    have b9701 := hb (x (-2) 10)
    have b9702 := hb (x (-1) 9)
    have b9703 := hb (x 0 8)
    clear * - r9689 e9690 e9691 e9692 e9693 e9694 e9695 b9696 b9697 b9698 b9699 b9700 b9701 b9702 b9703 g3
    omega
  have d9704 : (x (-2) 10).toNat = 0 := by
    have r9705 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9706 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9707 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9708 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9709 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9710 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9711 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9712 := hb (x (-7) 7)
    have b9713 := hb (x (-6) 6)
    have b9714 := hb (x (-5) 5)
    have b9715 := hb (x (-4) 4)
    have b9716 := hb (x (-3) 11)
    have b9717 := hb (x (-2) 10)
    have b9718 := hb (x (-1) 9)
    have b9719 := hb (x 0 8)
    clear * - r9705 e9706 e9707 e9708 e9709 e9710 e9711 b9712 b9713 b9714 b9715 b9716 b9717 b9718 b9719 g3 d9688
    omega
  have d9720 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r9721 := hand2 (x (-2) 1) (x (-2) 10)
    have b9722 := hb (x (-2) 10)
    have b9723 := hb (x (-2) 1 && x (-2) 10)
    clear * - r9721 b9722 b9723 d9704
    omega
  have d9724 : (x (-3) 11).toNat = 0 := by
    have r9725 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9726 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9727 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9728 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9729 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9730 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9731 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9732 := hb (x (-7) 7)
    have b9733 := hb (x (-6) 6)
    have b9734 := hb (x (-5) 5)
    have b9735 := hb (x (-4) 4)
    have b9736 := hb (x (-3) 11)
    have b9737 := hb (x (-2) 10)
    have b9738 := hb (x (-1) 9)
    have b9739 := hb (x 0 8)
    clear * - r9725 e9726 e9727 e9728 e9729 e9730 e9731 b9732 b9733 b9734 b9735 b9736 b9737 b9738 b9739 g3 d9688 d9704
    omega
  have d9740 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r9741 := hand2 (x (-3) 2) (x (-3) 11)
    have b9742 := hb (x (-3) 11)
    have b9743 := hb (x (-3) 2 && x (-3) 11)
    clear * - r9741 b9742 b9743 d9724
    omega
  have d9744 : (x (-4) 4).toNat = 0 := by
    have r9745 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9746 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9747 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9748 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9749 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9750 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9751 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9752 := hb (x (-7) 7)
    have b9753 := hb (x (-6) 6)
    have b9754 := hb (x (-5) 5)
    have b9755 := hb (x (-4) 4)
    have b9756 := hb (x (-3) 11)
    have b9757 := hb (x (-2) 10)
    have b9758 := hb (x (-1) 9)
    have b9759 := hb (x 0 8)
    clear * - r9745 e9746 e9747 e9748 e9749 e9750 e9751 b9752 b9753 b9754 b9755 b9756 b9757 b9758 b9759 g3 d9688 d9704 d9724
    omega
  have d9760 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r9761 := hand1 (x (-4) 4) (x (-4) 14)
    have b9762 := hb (x (-4) 4)
    have b9763 := hb (x (-4) 4 && x (-4) 14)
    clear * - r9761 b9762 b9763 d9744
    omega
  have d9764 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
    have r9765 := hand1 (x (-4) 4) (x (-4) 13)
    have b9766 := hb (x (-4) 4)
    have b9767 := hb (x (-4) 4 && x (-4) 13)
    clear * - r9765 b9766 b9767 d9744
    omega
  have d9768 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
    have r9769 := hand1 (x (-4) 4) (x (-4) 11)
    have b9770 := hb (x (-4) 4)
    have b9771 := hb (x (-4) 4 && x (-4) 11)
    clear * - r9769 b9770 b9771 d9744
    omega
  have d9772 : (x (-4) 4 && x (-4) 9).toNat = 0 := by
    have r9773 := hand1 (x (-4) 4) (x (-4) 9)
    have b9774 := hb (x (-4) 4)
    have b9775 := hb (x (-4) 4 && x (-4) 9)
    clear * - r9773 b9774 b9775 d9744
    omega
  have d9776 : (x (-5) 5).toNat = 0 := by
    have r9777 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9778 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9779 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9780 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9781 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9782 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9783 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9784 := hb (x (-7) 7)
    have b9785 := hb (x (-6) 6)
    have b9786 := hb (x (-5) 5)
    have b9787 := hb (x (-4) 4)
    have b9788 := hb (x (-3) 11)
    have b9789 := hb (x (-2) 10)
    have b9790 := hb (x (-1) 9)
    have b9791 := hb (x 0 8)
    clear * - r9777 e9778 e9779 e9780 e9781 e9782 e9783 b9784 b9785 b9786 b9787 b9788 b9789 b9790 b9791 g3 d9688 d9704 d9724 d9744
    omega
  have d9792 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
    have r9793 := hand1 (x (-5) 5) (x (-5) 14)
    have b9794 := hb (x (-5) 5)
    have b9795 := hb (x (-5) 5 && x (-5) 14)
    clear * - r9793 b9794 b9795 d9776
    omega
  have d9796 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
    have r9797 := hand1 (x (-5) 5) (x (-5) 12)
    have b9798 := hb (x (-5) 5)
    have b9799 := hb (x (-5) 5 && x (-5) 12)
    clear * - r9797 b9798 b9799 d9776
    omega
  have d9800 : (x (-5) 5 && x (-5) 10).toNat = 0 := by
    have r9801 := hand1 (x (-5) 5) (x (-5) 10)
    have b9802 := hb (x (-5) 5)
    have b9803 := hb (x (-5) 5 && x (-5) 10)
    clear * - r9801 b9802 b9803 d9776
    omega
  have d9804 : (x (-6) 6).toNat = 0 := by
    have r9805 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9806 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9807 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9808 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9809 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9810 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9811 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9812 := hb (x (-7) 7)
    have b9813 := hb (x (-6) 6)
    have b9814 := hb (x (-5) 5)
    have b9815 := hb (x (-4) 4)
    have b9816 := hb (x (-3) 11)
    have b9817 := hb (x (-2) 10)
    have b9818 := hb (x (-1) 9)
    have b9819 := hb (x 0 8)
    clear * - r9805 e9806 e9807 e9808 e9809 e9810 e9811 b9812 b9813 b9814 b9815 b9816 b9817 b9818 b9819 g3 d9688 d9704 d9724 d9744 d9776
    omega
  have d9820 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
    have r9821 := hand1 (x (-6) 6) (x (-6) 13)
    have b9822 := hb (x (-6) 6)
    have b9823 := hb (x (-6) 6 && x (-6) 13)
    clear * - r9821 b9822 b9823 d9804
    omega
  have d9824 : (x (-6) 6 && x (-6) 11).toNat = 0 := by
    have r9825 := hand1 (x (-6) 6) (x (-6) 11)
    have b9826 := hb (x (-6) 6)
    have b9827 := hb (x (-6) 6 && x (-6) 11)
    clear * - r9825 b9826 b9827 d9804
    omega
  have d9828 : (x (-7) 7).toNat = 0 := by
    have r9829 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9830 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e9831 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e9832 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e9833 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e9834 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e9835 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b9836 := hb (x (-7) 7)
    have b9837 := hb (x (-6) 6)
    have b9838 := hb (x (-5) 5)
    have b9839 := hb (x (-4) 4)
    have b9840 := hb (x (-3) 11)
    have b9841 := hb (x (-2) 10)
    have b9842 := hb (x (-1) 9)
    have b9843 := hb (x 0 8)
    clear * - r9829 e9830 e9831 e9832 e9833 e9834 e9835 b9836 b9837 b9838 b9839 b9840 b9841 b9842 b9843 g3 d9688 d9704 d9724 d9744 d9776 d9804
    omega
  have d9844 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
    have r9845 := hand1 (x (-7) 7) (x (-7) 14)
    have b9846 := hb (x (-7) 7)
    have b9847 := hb (x (-7) 7 && x (-7) 14)
    clear * - r9845 b9846 b9847 d9828
    omega
  have d9848 : (x (-7) 7 && x (-7) 12).toNat = 0 := by
    have r9849 := hand1 (x (-7) 7) (x (-7) 12)
    have b9850 := hb (x (-7) 7)
    have b9851 := hb (x (-7) 7 && x (-7) 12)
    clear * - r9849 b9850 b9851 d9828
    omega
  cases h9852 : x 0 5
  · have f9853 : (x 0 5).toNat = 0 := by rw [h9852]; rfl
    have d9854 : (x 0 5 && x 0 9).toNat = 0 := by
      have r9855 := hand1 (x 0 5) (x 0 9)
      have b9856 := hb (x 0 5)
      have b9857 := hb (x 0 5 && x 0 9)
      clear * - r9855 b9856 b9857 f9853
      omega
    cases h9858 : x 0 7
    · have f9859 : (x 0 7).toNat = 0 := by rw [h9858]; rfl
      have r9860 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9861 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e9862 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e9863 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e9864 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e9865 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e9866 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have r9867 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9868 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e9869 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e9870 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e9871 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e9872 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e9873 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have r9874 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9875 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e9876 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e9877 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e9878 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e9879 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e9880 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have r9881 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9882 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e9883 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e9884 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e9885 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e9886 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e9887 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have r9888 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9889 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e9890 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e9891 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e9892 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e9893 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e9894 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have r9895 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9896 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e9897 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have r9898 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9899 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e9900 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have r9901 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9902 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e9903 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have r9904 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e9905 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e9906 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have r9907 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9908 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9909 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := by have q := hcov5 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9910 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9911 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9912 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9913 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9914 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9915 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9916 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9917 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r9918 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
      have r9919 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
      have r9920 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have r9921 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
      have r9922 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have r9923 := hand2 (x (-1) 1) (x (-1) 6)
      have r9924 := hand1 (x (-2) 2) (x (-2) 7)
      have r9925 := hand2 (x (-3) 3) (x (-3) 8)
      have r9926 := hand2 (x (-8) 8) (x (-8) 13)
      have r9927 := hand1 (x (-9) 9) (x (-9) 14)
      have r9928 := hand2 (x (-1) 1) (x (-1) 8)
      have r9929 := hand2 (x (-2) 2) (x (-2) 9)
      have r9930 := hand2 (x (-3) 3) (x (-3) 10)
      have r9931 := hand1 (x (-4) 3) (x (-4) 12)
      have r9932 := hand1 (x (-5) 4) (x (-5) 13)
      have r9933 := hand1 (x (-6) 5) (x (-6) 14)
      have r9934 := hand1 (x (-3) 3) (x (-3) 12)
      have r9935 := hand2 (x (-3) 3) (x (-3) 12)
      have r9936 := hand1 (x (-3) 4) (x (-3) 14)
      have r9937 := hand2 (x (-3) 4) (x (-3) 14)
      have r9938 := hand2 (x 2 1) (x 2 11)
      have r9939 := hand1 (x (-1) 4) (x (-1) 14)
      have r9940 := hand1 (x (-4) 1) (x (-4) 12)
      have r9941 := hand1 (x (-5) 2) (x (-5) 13)
      have r9942 := hand1 (x (-6) 3) (x (-6) 14)
      have r9943 := hand1 (x (-4) 1) (x (-4) 14)
      have r9944 := hand2 (x (-2) 1) (x (-2) 14)
      linarith only [r9860, e9861, e9862, e9863, e9864, e9865, e9866, r9867, e9868, e9869, e9870, e9871, e9872, e9873, r9874, e9875, e9876, e9877, e9878, e9879, e9880, r9881, e9882, e9883, e9884, e9885, e9886, e9887, r9888, e9889, e9890, e9891, e9892, e9893, e9894, r9895, e9896, e9897, r9898, e9899, e9900, r9901, e9902, e9903, r9904, e9905, e9906, r9907, r9908, r9909, r9910, r9911, r9912, r9913, r9914, r9915, r9916, r9917, r9918, r9919, r9920, r9921, r9922, r9923, r9924, r9925, r9926, r9927, r9928, r9929, r9930, r9931, r9932, r9933, r9934, r9935, r9936, r9937, r9938, r9939, r9940, r9941, r9942, r9943, r9944, d9804, d9724, g0, d9688, g1, f9853, f9859, g5, g6, g8, g12, d9772, d9800, d9824, d9848, d9768, d9796, d9820, d9844, d9720, d9740, g17, g18, d9764, d9792, g22, g23, g24, g26, g27]
    · have f10052 : (x 0 7).toNat = 1 := by rw [h9858]; rfl
      have d10053 : (x 7 8).toNat = 0 := by
        have r10054 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10055 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e10056 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e10057 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e10058 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e10059 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e10060 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b10061 := hb (x 0 7)
        have b10062 := hb (x 1 6)
        have b10063 := hb (x 2 5)
        have b10064 := hb (x 3 4)
        have b10065 := hb (x 4 11)
        have b10066 := hb (x 5 10)
        have b10067 := hb (x 6 9)
        have b10068 := hb (x 7 8)
        clear * - r10054 e10055 e10056 e10057 e10058 e10059 e10060 b10061 b10062 b10063 b10064 b10065 b10066 b10067 b10068 g10 g7 f10052
        omega
      have d10069 : (x 6 9).toNat = 0 := by
        have r10070 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10071 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e10072 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e10073 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e10074 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e10075 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e10076 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b10077 := hb (x 0 7)
        have b10078 := hb (x 1 6)
        have b10079 := hb (x 2 5)
        have b10080 := hb (x 3 4)
        have b10081 := hb (x 4 11)
        have b10082 := hb (x 5 10)
        have b10083 := hb (x 6 9)
        have b10084 := hb (x 7 8)
        clear * - r10070 e10071 e10072 e10073 e10074 e10075 e10076 b10077 b10078 b10079 b10080 b10081 b10082 b10083 b10084 d10053 g10 g7 f10052
        omega
      have d10085 : (x 5 10).toNat = 0 := by
        have r10086 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10087 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e10088 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e10089 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e10090 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e10091 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e10092 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b10093 := hb (x 0 7)
        have b10094 := hb (x 1 6)
        have b10095 := hb (x 2 5)
        have b10096 := hb (x 3 4)
        have b10097 := hb (x 4 11)
        have b10098 := hb (x 5 10)
        have b10099 := hb (x 6 9)
        have b10100 := hb (x 7 8)
        clear * - r10086 e10087 e10088 e10089 e10090 e10091 e10092 b10093 b10094 b10095 b10096 b10097 b10098 b10099 b10100 d10053 d10069 g10 g7 f10052
        omega
      have d10101 : (x 4 11).toNat = 0 := by
        have r10102 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10103 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e10104 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e10105 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e10106 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e10107 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e10108 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b10109 := hb (x 0 7)
        have b10110 := hb (x 1 6)
        have b10111 := hb (x 2 5)
        have b10112 := hb (x 3 4)
        have b10113 := hb (x 4 11)
        have b10114 := hb (x 5 10)
        have b10115 := hb (x 6 9)
        have b10116 := hb (x 7 8)
        clear * - r10102 e10103 e10104 e10105 e10106 e10107 e10108 b10109 b10110 b10111 b10112 b10113 b10114 b10115 b10116 d10053 d10069 d10085 g10 g7 f10052
        omega
      have d10117 : (x 4 1 && x 4 11).toNat = 0 := by
        have r10118 := hand2 (x 4 1) (x 4 11)
        have b10119 := hb (x 4 11)
        have b10120 := hb (x 4 1 && x 4 11)
        clear * - r10118 b10119 b10120 d10101
        omega
      have d10121 : (x 2 3 && x 2 13).toNat = 1 := by
        have r10122 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10123 := hb (x 0 5)
        have b10124 := hb (x 5 10)
        have b10125 := hb (x 4 1 && x 4 11)
        have b10126 := hb (x 3 2 && x 3 12)
        have b10127 := hb (x 2 3 && x 2 13)
        have b10128 := hb (x 1 4 && x 1 14)
        clear * - r10122 b10123 b10124 b10125 b10126 b10127 b10128 d10085 d10117 g28 g29 f9853
        omega
      have d10129 : (x 2 3).toNat = 1 := by
        have r10130 := hand1 (x 2 3) (x 2 13)
        have b10131 := hb (x 2 3)
        have b10132 := hb (x 2 3 && x 2 13)
        clear * - r10130 b10131 b10132 d10121
        omega
      have d10133 : (x 5 12).toNat = 0 := by
        have r10134 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10135 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e10136 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b10137 := hb (x 2 3)
        have b10138 := hb (x 3 2)
        have b10139 := hb (x 4 13)
        have b10140 := hb (x 5 12)
        clear * - r10134 e10135 e10136 b10137 b10138 b10139 b10140 g9 d10129
        omega
      have d10141 : (x 5 2 && x 5 12).toNat = 0 := by
        have r10142 := hand2 (x 5 2) (x 5 12)
        have b10143 := hb (x 5 12)
        have b10144 := hb (x 5 2 && x 5 12)
        clear * - r10142 b10143 b10144 d10133
        omega
      have d10145 : (x 5 4).toNat = 0 := by
        have r10146 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b10147 := hb (x 5 4)
        have b10148 := hb (x 5 12)
        clear * - r10146 b10147 b10148 d10133
        omega
      have d10149 : (x 4 13).toNat = 0 := by
        have r10150 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10151 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e10152 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b10153 := hb (x 2 3)
        have b10154 := hb (x 3 2)
        have b10155 := hb (x 4 13)
        have b10156 := hb (x 5 12)
        clear * - r10150 e10151 e10152 b10153 b10154 b10155 b10156 d10133 g9 d10129
        omega
      have d10157 : (x 4 3 && x 4 13).toNat = 0 := by
        have r10158 := hand2 (x 4 3) (x 4 13)
        have b10159 := hb (x 4 13)
        have b10160 := hb (x 4 3 && x 4 13)
        clear * - r10158 b10159 b10160 d10149
        omega
      have d10161 : (x 4 5).toNat = 0 := by
        have r10162 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
        have b10163 := hb (x 4 5)
        have b10164 := hb (x 4 13)
        clear * - r10162 b10163 b10164 d10149
        omega
      have d10165 : (x 2 2).toNat = 1 := by
        have r10166 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10167 := hb (x 2 2)
        have b10168 := hb (x 4 13)
        have b10169 := hb (x 3 1 && x 3 14)
        clear * - r10166 b10167 b10168 b10169 d10149 g34
        omega
      have d10170 : (x 4 12).toNat = 0 := by
        have r10171 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10172 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e10173 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b10174 := hb (x 1 3)
        have b10175 := hb (x 2 2)
        have b10176 := hb (x 3 13)
        have b10177 := hb (x 4 12)
        clear * - r10171 e10172 e10173 b10174 b10175 b10176 b10177 d10165
        omega
      have d10178 : (x 3 13).toNat = 0 := by
        have r10179 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10180 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e10181 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b10182 := hb (x 1 3)
        have b10183 := hb (x 2 2)
        have b10184 := hb (x 3 13)
        have b10185 := hb (x 4 12)
        clear * - r10179 e10180 e10181 b10182 b10183 b10184 b10185 d10170 d10165
        omega
      have d10186 : (x 1 3).toNat = 0 := by
        have r10187 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10188 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e10189 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b10190 := hb (x 1 3)
        have b10191 := hb (x 2 2)
        have b10192 := hb (x 3 13)
        have b10193 := hb (x 4 12)
        clear * - r10187 e10188 e10189 b10190 b10191 b10192 b10193 d10170 d10178 d10165
        omega
      have d10194 : (x 1 11).toNat = 0 := by
        have r10195 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
        have b10196 := hb (x 1 3)
        have b10197 := hb (x 1 11)
        clear * - r10195 b10196 b10197 d10186
        omega
      have d10198 : (x (-3) 4).toNat = 1 := by
        have r10199 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10200 := hb (x (-3) 4)
        have b10201 := hb (x 1 11)
        have b10202 := hb (x 0 1 && x 0 12)
        have b10203 := hb (x (-1) 2 && x (-1) 13)
        have b10204 := hb (x (-2) 3 && x (-2) 14)
        clear * - r10199 b10200 b10201 b10202 b10203 b10204 d10194 g31 g32 g33
        omega
      have d10205 : (x (-3) 12).toNat = 1 := by
        have r10206 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b10207 := hb (x (-3) 4)
        have b10208 := hb (x (-3) 12)
        clear * - r10206 b10207 b10208 d10198
        omega
      have d10209 : (x (-4) 13).toNat = 0 := by
        have r10210 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10211 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e10212 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b10213 := hb (x (-6) 3)
        have b10214 := hb (x (-5) 2)
        have b10215 := hb (x (-4) 13)
        have b10216 := hb (x (-3) 12)
        clear * - r10210 e10211 e10212 b10213 b10214 b10215 b10216 d10205
        omega
      have d10217 : (x (-4) 9 && x (-4) 13).toNat = 0 := by
        have r10218 := hand2 (x (-4) 9) (x (-4) 13)
        have b10219 := hb (x (-4) 13)
        have b10220 := hb (x (-4) 9 && x (-4) 13)
        clear * - r10218 b10219 b10220 d10209
        omega
      have d10221 : (x (-4) 5).toNat = 0 := by
        have r10222 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
        have b10223 := hb (x (-4) 5)
        have b10224 := hb (x (-4) 13)
        clear * - r10222 b10223 b10224 d10209
        omega
      have d10225 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
        have r10226 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10227 := hb (x (-4) 5)
        have b10228 := hb (x 1 10)
        have b10229 := hb (x 0 1 && x 0 11)
        have b10230 := hb (x (-1) 2 && x (-1) 12)
        have b10231 := hb (x (-2) 3 && x (-2) 13)
        have b10232 := hb (x (-3) 4 && x (-3) 14)
        clear * - r10226 b10227 b10228 b10229 b10230 b10231 b10232 g8 g22 g23 g24 d10221
        omega
      have d10233 : (x (-3) 14).toNat = 1 := by
        have r10234 := hand2 (x (-3) 4) (x (-3) 14)
        have b10235 := hb (x (-3) 14)
        have b10236 := hb (x (-3) 4 && x (-3) 14)
        clear * - r10234 b10235 b10236 d10225
        omega
      have d10237 : (x (-4) 1).toNat = 0 := by
        have r10238 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10239 := hb (x (-4) 1)
        have b10240 := hb (x (-3) 14)
        clear * - r10238 b10239 b10240 d10233
        omega
      have d10241 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
        have r10242 := hand1 (x (-4) 1) (x (-4) 12)
        have b10243 := hb (x (-4) 1)
        have b10244 := hb (x (-4) 1 && x (-4) 12)
        clear * - r10242 b10243 b10244 d10237
        omega
      have d10245 : (x (-4) 9).toNat = 0 := by
        have r10246 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
        have b10247 := hb (x (-4) 1)
        have b10248 := hb (x (-4) 9)
        clear * - r10246 b10247 b10248 d10237
        omega
      have d10249 : (x (-5) 2).toNat = 0 := by
        have r10250 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10251 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e10252 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b10253 := hb (x (-6) 3)
        have b10254 := hb (x (-5) 2)
        have b10255 := hb (x (-4) 13)
        have b10256 := hb (x (-3) 12)
        clear * - r10250 e10251 e10252 b10253 b10254 b10255 b10256 d10205 d10209
        omega
      have d10257 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
        have r10258 := hand1 (x (-5) 2) (x (-5) 13)
        have b10259 := hb (x (-5) 2)
        have b10260 := hb (x (-5) 2 && x (-5) 13)
        clear * - r10258 b10259 b10260 d10249
        omega
      have d10261 : (x (-5) 10).toNat = 0 := by
        have r10262 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
        have b10263 := hb (x (-5) 2)
        have b10264 := hb (x (-5) 10)
        clear * - r10262 b10263 b10264 d10249
        omega
      have d10265 : (x (-6) 3).toNat = 0 := by
        have r10266 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10267 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e10268 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b10269 := hb (x (-6) 3)
        have b10270 := hb (x (-5) 2)
        have b10271 := hb (x (-4) 13)
        have b10272 := hb (x (-3) 12)
        clear * - r10266 e10267 e10268 b10269 b10270 b10271 b10272 d10205 d10209 d10249
        omega
      have d10273 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
        have r10274 := hand1 (x (-6) 3) (x (-6) 14)
        have b10275 := hb (x (-6) 3)
        have b10276 := hb (x (-6) 3 && x (-6) 14)
        clear * - r10274 b10275 b10276 d10265
        omega
      have d10277 : (x (-7) 4).toNat = 1 := by
        have r10278 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10279 := hb (x (-7) 4)
        have b10280 := hb (x (-3) 11)
        have b10281 := hb (x (-4) 1 && x (-4) 12)
        have b10282 := hb (x (-5) 2 && x (-5) 13)
        have b10283 := hb (x (-6) 3 && x (-6) 14)
        clear * - r10278 b10279 b10280 b10281 b10282 b10283 d9724 d10241 d10257 d10273
        omega
      have d10284 : (x (-7) 12).toNat = 1 := by
        have r10285 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
        have b10286 := hb (x (-7) 4)
        have b10287 := hb (x (-7) 12)
        clear * - r10285 b10286 b10287 d10277
        omega
      have d10288 : (x (-8) 13).toNat = 0 := by
        have r10289 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10290 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e10291 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b10292 := hb (x (-10) 3)
        have b10293 := hb (x (-9) 2)
        have b10294 := hb (x (-8) 13)
        have b10295 := hb (x (-7) 12)
        clear * - r10289 e10290 e10291 b10292 b10293 b10294 b10295 d10284
        omega
      have d10296 : (x (-8) 5).toNat = 0 := by
        have r10297 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
        have b10298 := hb (x (-8) 5)
        have b10299 := hb (x (-8) 13)
        clear * - r10297 b10298 b10299 d10288
        omega
      have d10300 : (x (-6) 11).toNat = 0 := by
        have r10301 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
        have b10302 := hb (x (-6) 3)
        have b10303 := hb (x (-6) 11)
        clear * - r10301 b10302 b10303 d10265
        omega
      have d10304 : (x 2 5).toNat = 0 := by
        have r10305 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10306 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e10307 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e10308 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e10309 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e10310 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e10311 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b10312 := hb (x 0 7)
        have b10313 := hb (x 1 6)
        have b10314 := hb (x 2 5)
        have b10315 := hb (x 3 4)
        have b10316 := hb (x 4 11)
        have b10317 := hb (x 5 10)
        have b10318 := hb (x 6 9)
        have b10319 := hb (x 7 8)
        clear * - r10305 e10306 e10307 e10308 e10309 e10310 e10311 b10312 b10313 b10314 b10315 b10316 b10317 b10318 b10319 d10053 d10069 d10085 d10101 g10 g7 f10052
        omega
      have d10320 : (x (-3) 8).toNat = 0 := by
        have r10321 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10322 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
        have e10323 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
        have e10324 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
        have e10325 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
        have e10326 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
        have e10327 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
        have b10328 := hb (x (-10) 7)
        have b10329 := hb (x (-9) 6)
        have b10330 := hb (x (-8) 5)
        have b10331 := hb (x (-7) 4)
        have b10332 := hb (x (-6) 11)
        have b10333 := hb (x (-5) 10)
        have b10334 := hb (x (-4) 9)
        have b10335 := hb (x (-3) 8)
        clear * - r10321 e10322 e10323 e10324 e10325 e10326 e10327 b10328 b10329 b10330 b10331 b10332 b10333 b10334 b10335 d10245 d10261 d10300 d10277 d10296
        omega
      have d10336 : (x (-3) 8 && x (-3) 12).toNat = 0 := by
        have r10337 := hand1 (x (-3) 8) (x (-3) 12)
        have b10338 := hb (x (-3) 8)
        have b10339 := hb (x (-3) 8 && x (-3) 12)
        clear * - r10337 b10338 b10339 d10320
        omega
      have d10340 : (x 2 3 && x 2 7).toNat = 1 := by
        have r10341 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10342 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
        have e10343 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
        have b10344 := hb (x (-6) 11)
        have b10345 := hb (x (-5) 10)
        have b10346 := hb (x 4 5)
        have b10347 := hb (x 5 4)
        have b10348 := hb (x 3 2 && x 3 6)
        have b10349 := hb (x 2 3 && x 2 7)
        have b10350 := hb (x 1 4 && x 1 8)
        have b10351 := hb (x 0 5 && x 0 9)
        have b10352 := hb (x (-1) 6 && x (-1) 10)
        have b10353 := hb (x (-2) 7 && x (-2) 11)
        have b10354 := hb (x (-3) 8 && x (-3) 12)
        have b10355 := hb (x (-4) 9 && x (-4) 13)
        clear * - r10341 e10342 e10343 b10344 b10345 b10346 b10347 b10348 b10349 b10350 b10351 b10352 b10353 b10354 b10355 d10145 d10161 g13 g14 d9854 g15 g16 d10336 d10217 d10261 d10300
        omega
      have d10356 : (x 2 7).toNat = 1 := by
        have r10357 := hand2 (x 2 3) (x 2 7)
        have b10358 := hb (x 2 7)
        have b10359 := hb (x 2 3 && x 2 7)
        clear * - r10357 b10358 b10359 d10340
        omega
      have d10360 : (x 9 8).toNat = 0 := by
        have r10361 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10362 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e10363 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e10364 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e10365 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e10366 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e10367 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b10368 := hb (x 2 7)
        have b10369 := hb (x 3 6)
        have b10370 := hb (x 4 5)
        have b10371 := hb (x 5 4)
        have b10372 := hb (x 6 11)
        have b10373 := hb (x 7 10)
        have b10374 := hb (x 8 9)
        have b10375 := hb (x 9 8)
        clear * - r10361 e10362 e10363 e10364 e10365 e10366 e10367 b10368 b10369 b10370 b10371 b10372 b10373 b10374 b10375 d10145 d10161 g11 d10356
        omega
      have d10376 : (x 8 9).toNat = 0 := by
        have r10377 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10378 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e10379 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e10380 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e10381 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e10382 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e10383 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b10384 := hb (x 2 7)
        have b10385 := hb (x 3 6)
        have b10386 := hb (x 4 5)
        have b10387 := hb (x 5 4)
        have b10388 := hb (x 6 11)
        have b10389 := hb (x 7 10)
        have b10390 := hb (x 8 9)
        have b10391 := hb (x 9 8)
        clear * - r10377 e10378 e10379 e10380 e10381 e10382 e10383 b10384 b10385 b10386 b10387 b10388 b10389 b10390 b10391 d10360 d10145 d10161 g11 d10356
        omega
      have d10392 : (x 7 10).toNat = 0 := by
        have r10393 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e10394 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e10395 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e10396 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e10397 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e10398 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e10399 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b10400 := hb (x 2 7)
        have b10401 := hb (x 3 6)
        have b10402 := hb (x 4 5)
        have b10403 := hb (x 5 4)
        have b10404 := hb (x 6 11)
        have b10405 := hb (x 7 10)
        have b10406 := hb (x 8 9)
        have b10407 := hb (x 9 8)
        clear * - r10393 e10394 e10395 e10396 e10397 e10398 e10399 b10400 b10401 b10402 b10403 b10404 b10405 b10406 b10407 d10360 d10376 d10145 d10161 g11 d10356
        omega
      have d10408 : (x 6 1 && x 6 11).toNat = 1 := by
        have r10409 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b10410 := hb (x 2 5)
        have b10411 := hb (x 7 10)
        have b10412 := hb (x 6 1 && x 6 11)
        have b10413 := hb (x 5 2 && x 5 12)
        have b10414 := hb (x 4 3 && x 4 13)
        have b10415 := hb (x 3 4 && x 3 14)
        clear * - r10409 b10410 b10411 b10412 b10413 b10414 b10415 d10392 d10141 d10157 g30 d10304
        omega
      have d10416 : (x 6 11).toNat = 1 := by
        have r10417 := hand2 (x 6 1) (x 6 11)
        have b10418 := hb (x 6 11)
        have b10419 := hb (x 6 1 && x 6 11)
        clear * - r10417 b10418 b10419 d10408
        omega
      have r10420 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10421 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e10422 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e10423 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e10424 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e10425 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e10426 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b10427 := hb (x 2 7)
      have b10428 := hb (x 3 6)
      have b10429 := hb (x 4 5)
      have b10430 := hb (x 5 4)
      have b10431 := hb (x 6 11)
      have b10432 := hb (x 7 10)
      have b10433 := hb (x 8 9)
      have b10434 := hb (x 9 8)
      linarith only [r10420, e10421, e10422, e10423, e10424, e10425, e10426, b10427, b10428, b10429, b10430, b10431, b10432, b10433, b10434, d10360, d10376, d10392, d10416, d10145, d10161, g11, d10356]
  · have f10435 : (x 0 5).toNat = 1 := by rw [h9852]; rfl
    have d10436 : (x 5 8).toNat = 0 := by
      have r10437 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10438 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e10439 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e10440 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e10441 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e10442 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e10443 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b10444 := hb (x (-2) 7)
      have b10445 := hb (x (-1) 6)
      have b10446 := hb (x 0 5)
      have b10447 := hb (x 1 4)
      have b10448 := hb (x 2 11)
      have b10449 := hb (x 3 10)
      have b10450 := hb (x 4 9)
      have b10451 := hb (x 5 8)
      clear * - r10437 e10438 e10439 e10440 e10441 e10442 e10443 b10444 b10445 b10446 b10447 b10448 b10449 b10450 b10451 g12 g6 f10435
      omega
    have d10452 : (x 4 9).toNat = 0 := by
      have r10453 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10454 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e10455 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e10456 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e10457 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e10458 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e10459 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b10460 := hb (x (-2) 7)
      have b10461 := hb (x (-1) 6)
      have b10462 := hb (x 0 5)
      have b10463 := hb (x 1 4)
      have b10464 := hb (x 2 11)
      have b10465 := hb (x 3 10)
      have b10466 := hb (x 4 9)
      have b10467 := hb (x 5 8)
      clear * - r10453 e10454 e10455 e10456 e10457 e10458 e10459 b10460 b10461 b10462 b10463 b10464 b10465 b10466 b10467 d10436 g12 g6 f10435
      omega
    have d10468 : (x 2 11).toNat = 0 := by
      have r10469 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e10470 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e10471 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e10472 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e10473 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e10474 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e10475 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b10476 := hb (x (-2) 7)
      have b10477 := hb (x (-1) 6)
      have b10478 := hb (x 0 5)
      have b10479 := hb (x 1 4)
      have b10480 := hb (x 2 11)
      have b10481 := hb (x 3 10)
      have b10482 := hb (x 4 9)
      have b10483 := hb (x 5 8)
      clear * - r10469 e10470 e10471 e10472 e10473 e10474 e10475 b10476 b10477 b10478 b10479 b10480 b10481 b10482 b10483 d10436 d10452 g12 g6 f10435
      omega
    have d10484 : (x 2 2 && x 2 11).toNat = 0 := by
      have r10485 := hand2 (x 2 2) (x 2 11)
      have b10486 := hb (x 2 11)
      have b10487 := hb (x 2 2 && x 2 11)
      clear * - r10485 b10486 b10487 d10468
      omega
    have r10488 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10489 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e10490 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e10491 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e10492 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e10493 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e10494 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have r10495 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10496 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e10497 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e10498 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e10499 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e10500 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e10501 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have r10502 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10503 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e10504 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e10505 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e10506 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e10507 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e10508 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have r10509 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e10510 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e10511 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have r10512 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10513 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10514 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10515 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10516 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10517 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r10518 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have r10519 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have r10520 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have r10521 := hand1 (x (-3) 3) (x (-3) 12)
    have r10522 := hand1 (x (-1) 5) (x (-1) 14)
    have r10523 := hand2 (x (-1) 1) (x (-1) 11)
    have r10524 := hand1 (x (-2) 2) (x (-2) 12)
    have r10525 := hand2 (x (-3) 3) (x (-3) 13)
    have r10526 := hand2 (x 1 1) (x 1 11)
    have r10527 := hand2 (x (-1) 3) (x (-1) 13)
    have r10528 := hand1 (x (-2) 4) (x (-2) 14)
    linarith only [r10488, e10489, e10490, e10491, e10492, e10493, e10494, r10495, e10496, e10497, e10498, e10499, e10500, e10501, r10502, e10503, e10504, e10505, e10506, e10507, e10508, r10509, e10510, e10511, r10512, r10513, r10514, r10515, r10516, r10517, r10518, r10519, r10520, r10521, r10522, r10523, r10524, r10525, r10526, r10527, r10528, d9804, d9776, g0, g1, g2, g4, g5, d10452, g17, g18, d9764, d9792, g19, d10484, g20, g21, d9760, g25, g31, g32, g33]

theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b01 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-1) 10).toNat = 0)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 0 8).toNat = 1)
    (g4 : (x 0 10).toNat = 0)
    (g5 : (x 0 12).toNat = 0)
    (g6 : (x 1 4).toNat = 0)
    (g7 : (x 1 6).toNat = 0)
    (g8 : (x 1 10).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 3 6).toNat = 0)
    (g12 : (x 3 10).toNat = 0)
    (g13 : (x 3 2 && x 3 6).toNat = 0)
    (g14 : (x 1 4 && x 1 8).toNat = 0)
    (g15 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g16 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g17 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g18 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g19 : (x 3 1 && x 3 10).toNat = 0)
    (g20 : (x 1 3 && x 1 12).toNat = 0)
    (g21 : (x 0 4 && x 0 13).toNat = 0)
    (g22 : (x 0 1 && x 0 11).toNat = 0)
    (g23 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g24 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g25 : (x 0 2 && x 0 12).toNat = 0)
    (g26 : (x 1 2 && x 1 12).toNat = 0)
    (g27 : (x 0 3 && x 0 13).toNat = 0)
    (g28 : (x 3 2 && x 3 12).toNat = 0)
    (g29 : (x 1 4 && x 1 14).toNat = 0)
    (g30 : (x 3 4 && x 3 14).toNat = 0)
    (g31 : (x 0 1 && x 0 12).toNat = 0)
    (g32 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g33 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g34 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b01_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34
