import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000000

Topic: combinatorics   Node: 0c8e9d1a8365

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 19 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 13).toNat = 0)
    (g1 : (x 0 1).toNat = 1)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 0 5).toNat = 0)
    (g4 : (x 0 10).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 1 2).toNat = 0)
    (g8 : (x 1 10).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 10).toNat = 0)
    (g11 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g12 : (x 0 1 && x 0 11).toNat = 0)
    (g13 : (x 1 2 && x 1 12).toNat = 0)
    (g14 : (x 0 3 && x 0 13).toNat = 0)
    (g15 : (x 3 1 && x 3 12).toNat = 0)
    (g16 : (x 1 3 && x 1 14).toNat = 0)
    (g17 : (x 0 1 && x 0 14).toNat = 0)
    (g18 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d19742 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
    have r19743 := hand2 (x (-1) 2) (x (-1) 13)
    have b19744 := hb (x (-1) 13)
    have b19745 := hb (x (-1) 2 && x (-1) 13)
    clear * - r19743 b19744 b19745 g0
    omega
  cases h19746 : x 0 9
  · have f19747 : (x 0 9).toNat = 0 := by rw [h19746]; rfl
    cases h19748 : x 0 12
    · have f19749 : (x 0 12).toNat = 0 := by rw [h19748]; rfl
      have d19750 : (x 0 1 && x 0 12).toNat = 0 := by
        have r19751 := hand2 (x 0 1) (x 0 12)
        have b19752 := hb (x 0 12)
        have b19753 := hb (x 0 1 && x 0 12)
        clear * - r19751 b19752 b19753 f19749
        omega
      cases h19754 : x 1 1
      · have f19755 : (x 1 1).toNat = 0 := by rw [h19754]; rfl
        have d19756 : (x 1 13).toNat = 0 := by
          have r19757 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b19758 := hb (x 1 1)
          have b19759 := hb (x 1 13)
          clear * - r19757 b19758 b19759 f19755
          omega
        have d19760 : (x (-1) 2).toNat = 1 := by
          have r19761 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19762 := hb (x (-1) 2)
          have b19763 := hb (x 1 13)
          have b19764 := hb (x 0 1 && x 0 14)
          clear * - r19761 b19762 b19763 b19764 d19756 g17
          omega
        have d19765 : (x (-1) 14).toNat = 1 := by
          have r19766 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b19767 := hb (x (-1) 2)
          have b19768 := hb (x (-1) 14)
          clear * - r19766 b19767 b19768 d19760
          omega
        have d19769 : (x (-2) 1).toNat = 0 := by
          have r19770 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19771 := hb (x (-2) 1)
          have b19772 := hb (x (-1) 14)
          clear * - r19770 b19771 b19772 d19765
          omega
        have d19773 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r19774 := hand1 (x (-2) 1) (x (-2) 14)
          have b19775 := hb (x (-2) 1)
          have b19776 := hb (x (-2) 1 && x (-2) 14)
          clear * - r19774 b19775 b19776 d19769
          omega
        have d19777 : (x (-2) 13).toNat = 0 := by
          have r19778 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b19779 := hb (x (-2) 1)
          have b19780 := hb (x (-2) 13)
          clear * - r19778 b19779 b19780 d19769
          omega
        have d19781 : (x (-2) 5).toNat = 0 := by
          have r19782 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b19783 := hb (x (-2) 5)
          have b19784 := hb (x (-2) 13)
          clear * - r19782 b19783 b19784 d19777
          omega
        have d19785 : (x (-2) 9).toNat = 0 := by
          have r19786 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
          have b19787 := hb (x (-2) 1)
          have b19788 := hb (x (-2) 9)
          clear * - r19786 b19787 b19788 d19769
          omega
        have d19789 : (x (-3) 2).toNat = 1 := by
          have r19790 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19791 := hb (x (-3) 2)
          have b19792 := hb (x (-1) 13)
          have b19793 := hb (x (-2) 1 && x (-2) 14)
          clear * - r19790 b19791 b19792 b19793 g0 d19773
          omega
        have d19794 : (x (-3) 14).toNat = 1 := by
          have r19795 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b19796 := hb (x (-3) 2)
          have b19797 := hb (x (-3) 14)
          clear * - r19795 b19796 b19797 d19789
          omega
        have d19798 : (x (-4) 1).toNat = 0 := by
          have r19799 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19800 := hb (x (-4) 1)
          have b19801 := hb (x (-3) 14)
          clear * - r19799 b19800 b19801 d19794
          omega
        have d19802 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
          have r19803 := hand1 (x (-4) 1) (x (-4) 11)
          have b19804 := hb (x (-4) 1)
          have b19805 := hb (x (-4) 1 && x (-4) 11)
          clear * - r19803 b19804 b19805 d19798
          omega
        have d19806 : (x (-4) 13).toNat = 0 := by
          have r19807 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b19808 := hb (x (-4) 1)
          have b19809 := hb (x (-4) 13)
          clear * - r19807 b19808 b19809 d19798
          omega
        have d19810 : (x (-4) 5).toNat = 0 := by
          have r19811 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
          have b19812 := hb (x (-4) 5)
          have b19813 := hb (x (-4) 13)
          clear * - r19811 b19812 b19813 d19806
          omega
        have d19814 : (x (-4) 5 && x (-4) 9).toNat = 0 := by
          have r19815 := hand1 (x (-4) 5) (x (-4) 9)
          have b19816 := hb (x (-4) 5)
          have b19817 := hb (x (-4) 5 && x (-4) 9)
          clear * - r19815 b19816 b19817 d19810
          omega
        have d19818 : (x (-4) 9).toNat = 0 := by
          have r19819 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
          have b19820 := hb (x (-4) 1)
          have b19821 := hb (x (-4) 9)
          clear * - r19819 b19820 b19821 d19798
          omega
        have d19822 : (x 1 12).toNat = 0 := by
          have r19823 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19824 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e19825 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b19826 := hb (x (-2) 3)
          have b19827 := hb (x (-1) 2)
          have b19828 := hb (x 0 13)
          have b19829 := hb (x 1 12)
          clear * - r19823 e19824 e19825 b19826 b19827 b19828 b19829 g6 d19760
          omega
        have d19830 : (x 1 4).toNat = 0 := by
          have r19831 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b19832 := hb (x 1 4)
          have b19833 := hb (x 1 12)
          clear * - r19831 b19832 b19833 d19822
          omega
        have d19834 : (x (-2) 3).toNat = 0 := by
          have r19835 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19836 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e19837 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b19838 := hb (x (-2) 3)
          have b19839 := hb (x (-1) 2)
          have b19840 := hb (x 0 13)
          have b19841 := hb (x 1 12)
          clear * - r19835 e19836 e19837 b19838 b19839 b19840 b19841 d19822 g6 d19760
          omega
        have d19842 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
          have r19843 := hand1 (x (-2) 3) (x (-2) 14)
          have b19844 := hb (x (-2) 3)
          have b19845 := hb (x (-2) 3 && x (-2) 14)
          clear * - r19843 b19844 b19845 d19834
          omega
        have d19846 : (x (-2) 3 && x (-2) 7).toNat = 0 := by
          have r19847 := hand1 (x (-2) 3) (x (-2) 7)
          have b19848 := hb (x (-2) 3)
          have b19849 := hb (x (-2) 3 && x (-2) 7)
          clear * - r19847 b19848 b19849 d19834
          omega
        have d19850 : (x (-2) 11).toNat = 0 := by
          have r19851 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
          have b19852 := hb (x (-2) 3)
          have b19853 := hb (x (-2) 11)
          clear * - r19851 b19852 b19853 d19834
          omega
        have d19854 : (x (-1) 12).toNat = 0 := by
          have r19855 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19856 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e19857 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b19858 := hb (x (-4) 3)
          have b19859 := hb (x (-3) 2)
          have b19860 := hb (x (-2) 13)
          have b19861 := hb (x (-1) 12)
          clear * - r19855 e19856 e19857 b19858 b19859 b19860 b19861 d19777 d19789
          omega
        have d19862 : (x (-1) 4).toNat = 0 := by
          have r19863 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b19864 := hb (x (-1) 4)
          have b19865 := hb (x (-1) 12)
          clear * - r19863 b19864 b19865 d19854
          omega
        have d19866 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
          have r19867 := hand1 (x (-1) 4) (x (-1) 14)
          have b19868 := hb (x (-1) 4)
          have b19869 := hb (x (-1) 4 && x (-1) 14)
          clear * - r19867 b19868 b19869 d19862
          omega
        have d19870 : (x (-4) 3).toNat = 0 := by
          have r19871 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19872 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e19873 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b19874 := hb (x (-4) 3)
          have b19875 := hb (x (-3) 2)
          have b19876 := hb (x (-2) 13)
          have b19877 := hb (x (-1) 12)
          clear * - r19871 e19872 e19873 b19874 b19875 b19876 b19877 d19854 d19777 d19789
          omega
        have d19878 : (x (-4) 11).toNat = 0 := by
          have r19879 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b19880 := hb (x (-4) 3)
          have b19881 := hb (x (-4) 11)
          clear * - r19879 b19880 b19881 d19870
          omega
        have d19882 : (x 2 1 && x 2 11).toNat = 1 := by
          have r19883 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19884 := hb (x (-2) 5)
          have b19885 := hb (x 3 10)
          have b19886 := hb (x 2 1 && x 2 11)
          have b19887 := hb (x 1 2 && x 1 12)
          have b19888 := hb (x 0 3 && x 0 13)
          have b19889 := hb (x (-1) 4 && x (-1) 14)
          clear * - r19883 b19884 b19885 b19886 b19887 b19888 b19889 g10 g13 g14 d19866 d19781
          omega
        have d19890 : (x 2 11).toNat = 1 := by
          have r19891 := hand2 (x 2 1) (x 2 11)
          have b19892 := hb (x 2 11)
          have b19893 := hb (x 2 1 && x 2 11)
          clear * - r19891 b19892 b19893 d19882
          omega
        have d19894 : (x 2 3).toNat = 1 := by
          have r19895 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
          have b19896 := hb (x 2 3)
          have b19897 := hb (x 2 11)
          clear * - r19895 b19896 b19897 d19890
          omega
        have d19898 : (x 5 12).toNat = 0 := by
          have r19899 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19900 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e19901 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b19902 := hb (x 2 3)
          have b19903 := hb (x 3 2)
          have b19904 := hb (x 4 13)
          have b19905 := hb (x 5 12)
          clear * - r19899 e19900 e19901 b19902 b19903 b19904 b19905 g9 d19894
          omega
        have d19906 : (x 4 13).toNat = 0 := by
          have r19907 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19908 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e19909 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b19910 := hb (x 2 3)
          have b19911 := hb (x 3 2)
          have b19912 := hb (x 4 13)
          have b19913 := hb (x 5 12)
          clear * - r19907 e19908 e19909 b19910 b19911 b19912 b19913 d19898 g9 d19894
          omega
        have d19914 : (x 2 2).toNat = 1 := by
          have r19915 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19916 := hb (x 2 2)
          have b19917 := hb (x 4 13)
          have b19918 := hb (x 3 1 && x 3 14)
          clear * - r19915 b19916 b19917 b19918 d19906 g18
          omega
        have d19919 : (x 4 12).toNat = 0 := by
          have r19920 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19921 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e19922 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b19923 := hb (x 1 3)
          have b19924 := hb (x 2 2)
          have b19925 := hb (x 3 13)
          have b19926 := hb (x 4 12)
          clear * - r19920 e19921 e19922 b19923 b19924 b19925 b19926 d19914
          omega
        have d19927 : (x 3 13).toNat = 0 := by
          have r19928 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19929 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e19930 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b19931 := hb (x 1 3)
          have b19932 := hb (x 2 2)
          have b19933 := hb (x 3 13)
          have b19934 := hb (x 4 12)
          clear * - r19928 e19929 e19930 b19931 b19932 b19933 b19934 d19919 d19914
          omega
        have d19935 : (x 1 3).toNat = 0 := by
          have r19936 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19937 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e19938 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b19939 := hb (x 1 3)
          have b19940 := hb (x 2 2)
          have b19941 := hb (x 3 13)
          have b19942 := hb (x 4 12)
          clear * - r19936 e19937 e19938 b19939 b19940 b19941 b19942 d19919 d19927 d19914
          omega
        have d19943 : (x 1 11).toNat = 0 := by
          have r19944 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b19945 := hb (x 1 3)
          have b19946 := hb (x 1 11)
          clear * - r19944 b19945 b19946 d19935
          omega
        have d19947 : (x (-3) 4).toNat = 1 := by
          have r19948 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19949 := hb (x (-3) 4)
          have b19950 := hb (x 1 11)
          have b19951 := hb (x 0 1 && x 0 12)
          have b19952 := hb (x (-1) 2 && x (-1) 13)
          have b19953 := hb (x (-2) 3 && x (-2) 14)
          clear * - r19948 b19949 b19950 b19951 b19952 b19953 d19943 d19750 d19742 d19842
          omega
        have d19954 : (x (-3) 12).toNat = 1 := by
          have r19955 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b19956 := hb (x (-3) 4)
          have b19957 := hb (x (-3) 12)
          clear * - r19955 b19956 b19957 d19947
          omega
        have d19958 : (x (-5) 2).toNat = 0 := by
          have r19959 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19960 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e19961 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b19962 := hb (x (-6) 3)
          have b19963 := hb (x (-5) 2)
          have b19964 := hb (x (-4) 13)
          have b19965 := hb (x (-3) 12)
          clear * - r19959 e19960 e19961 b19962 b19963 b19964 b19965 d19954 d19806
          omega
        have d19966 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
          have r19967 := hand1 (x (-5) 2) (x (-5) 12)
          have b19968 := hb (x (-5) 2)
          have b19969 := hb (x (-5) 2 && x (-5) 12)
          clear * - r19967 b19968 b19969 d19958
          omega
        have d19970 : (x (-5) 10).toNat = 0 := by
          have r19971 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
          have b19972 := hb (x (-5) 2)
          have b19973 := hb (x (-5) 10)
          clear * - r19971 b19972 b19973 d19958
          omega
        have d19974 : (x (-5) 6 && x (-5) 10).toNat = 0 := by
          have r19975 := hand2 (x (-5) 6) (x (-5) 10)
          have b19976 := hb (x (-5) 10)
          have b19977 := hb (x (-5) 6 && x (-5) 10)
          clear * - r19975 b19976 b19977 d19970
          omega
        have d19978 : (x (-6) 3).toNat = 0 := by
          have r19979 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19980 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e19981 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b19982 := hb (x (-6) 3)
          have b19983 := hb (x (-5) 2)
          have b19984 := hb (x (-4) 13)
          have b19985 := hb (x (-3) 12)
          clear * - r19979 e19980 e19981 b19982 b19983 b19984 b19985 d19954 d19806 d19958
          omega
        have d19986 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
          have r19987 := hand1 (x (-6) 3) (x (-6) 13)
          have b19988 := hb (x (-6) 3)
          have b19989 := hb (x (-6) 3 && x (-6) 13)
          clear * - r19987 b19988 b19989 d19978
          omega
        have d19990 : (x (-6) 11).toNat = 0 := by
          have r19991 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
          have b19992 := hb (x (-6) 3)
          have b19993 := hb (x (-6) 11)
          clear * - r19991 b19992 b19993 d19978
          omega
        have d19994 : (x (-6) 7 && x (-6) 11).toNat = 0 := by
          have r19995 := hand2 (x (-6) 7) (x (-6) 11)
          have b19996 := hb (x (-6) 11)
          have b19997 := hb (x (-6) 7 && x (-6) 11)
          clear * - r19995 b19996 b19997 d19990
          omega
        have d19998 : (x 5 8).toNat = 0 := by
          have r19999 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20000 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e20001 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e20002 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e20003 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e20004 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e20005 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b20006 := hb (x (-2) 7)
          have b20007 := hb (x (-1) 6)
          have b20008 := hb (x 0 5)
          have b20009 := hb (x 1 4)
          have b20010 := hb (x 2 11)
          have b20011 := hb (x 3 10)
          have b20012 := hb (x 4 9)
          have b20013 := hb (x 5 8)
          clear * - r19999 e20000 e20001 e20002 e20003 e20004 e20005 b20006 b20007 b20008 b20009 b20010 b20011 b20012 b20013 g10 d19890 d19830 g3
          omega
        have d20014 : (x 4 9).toNat = 0 := by
          have r20015 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20016 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e20017 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e20018 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e20019 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e20020 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e20021 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b20022 := hb (x (-2) 7)
          have b20023 := hb (x (-1) 6)
          have b20024 := hb (x 0 5)
          have b20025 := hb (x 1 4)
          have b20026 := hb (x 2 11)
          have b20027 := hb (x 3 10)
          have b20028 := hb (x 4 9)
          have b20029 := hb (x 5 8)
          clear * - r20015 e20016 e20017 e20018 e20019 e20020 e20021 b20022 b20023 b20024 b20025 b20026 b20027 b20028 b20029 d19998 g10 d19890 d19830 g3
          omega
        have d20030 : (x (-1) 6).toNat = 0 := by
          have r20031 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20032 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e20033 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e20034 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e20035 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e20036 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e20037 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b20038 := hb (x (-2) 7)
          have b20039 := hb (x (-1) 6)
          have b20040 := hb (x 0 5)
          have b20041 := hb (x 1 4)
          have b20042 := hb (x 2 11)
          have b20043 := hb (x 3 10)
          have b20044 := hb (x 4 9)
          have b20045 := hb (x 5 8)
          clear * - r20031 e20032 e20033 e20034 e20035 e20036 e20037 b20038 b20039 b20040 b20041 b20042 b20043 b20044 b20045 d19998 d20014 g10 d19890 d19830 g3
          omega
        have d20046 : (x (-1) 2 && x (-1) 6).toNat = 0 := by
          have r20047 := hand2 (x (-1) 2) (x (-1) 6)
          have b20048 := hb (x (-1) 6)
          have b20049 := hb (x (-1) 2 && x (-1) 6)
          clear * - r20047 b20048 b20049 d20030
          omega
        have d20050 : (x 1 8).toNat = 0 := by
          have r20051 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20052 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e20053 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e20054 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e20055 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e20056 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e20057 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b20058 := hb (x (-6) 7)
          have b20059 := hb (x (-5) 6)
          have b20060 := hb (x (-4) 5)
          have b20061 := hb (x (-3) 4)
          have b20062 := hb (x (-2) 11)
          have b20063 := hb (x (-1) 10)
          have b20064 := hb (x 0 9)
          have b20065 := hb (x 1 8)
          clear * - r20051 e20052 e20053 e20054 e20055 e20056 e20057 b20058 b20059 b20060 b20061 b20062 b20063 b20064 b20065 f19747 d19850 d19947 d19810
          omega
        have d20066 : (x (-1) 10).toNat = 0 := by
          have r20067 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20068 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e20069 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e20070 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e20071 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e20072 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e20073 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b20074 := hb (x (-6) 7)
          have b20075 := hb (x (-5) 6)
          have b20076 := hb (x (-4) 5)
          have b20077 := hb (x (-3) 4)
          have b20078 := hb (x (-2) 11)
          have b20079 := hb (x (-1) 10)
          have b20080 := hb (x 0 9)
          have b20081 := hb (x 1 8)
          clear * - r20067 e20068 e20069 e20070 e20071 e20072 e20073 b20074 b20075 b20076 b20077 b20078 b20079 b20080 b20081 d20050 f19747 d19850 d19947 d19810
          omega
        have d20082 : (x (-5) 6).toNat = 0 := by
          have r20083 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20084 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e20085 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e20086 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e20087 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e20088 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e20089 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b20090 := hb (x (-6) 7)
          have b20091 := hb (x (-5) 6)
          have b20092 := hb (x (-4) 5)
          have b20093 := hb (x (-3) 4)
          have b20094 := hb (x (-2) 11)
          have b20095 := hb (x (-1) 10)
          have b20096 := hb (x 0 9)
          have b20097 := hb (x 1 8)
          clear * - r20083 e20084 e20085 e20086 e20087 e20088 e20089 b20090 b20091 b20092 b20093 b20094 b20095 b20096 b20097 d20050 f19747 d20066 d19850 d19947 d19810
          omega
        have d20098 : (x (-6) 7).toNat = 0 := by
          have r20099 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20100 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e20101 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e20102 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e20103 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e20104 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e20105 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b20106 := hb (x (-6) 7)
          have b20107 := hb (x (-5) 6)
          have b20108 := hb (x (-4) 5)
          have b20109 := hb (x (-3) 4)
          have b20110 := hb (x (-2) 11)
          have b20111 := hb (x (-1) 10)
          have b20112 := hb (x 0 9)
          have b20113 := hb (x 1 8)
          clear * - r20099 e20100 e20101 e20102 e20103 e20104 e20105 b20106 b20107 b20108 b20109 b20110 b20111 b20112 b20113 d20050 f19747 d20066 d19850 d19947 d19810 d20082
          omega
        have d20114 : (x (-7) 8).toNat = 0 := by
          have r20115 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20116 := hb (x (-13) 14)
          have b20117 := hb (x (-12) 13)
          have b20118 := hb (x (-11) 12)
          have b20119 := hb (x (-10) 11)
          have b20120 := hb (x (-9) 10)
          have b20121 := hb (x (-8) 9)
          have b20122 := hb (x (-7) 8)
          have b20123 := hb (x (-6) 7)
          have b20124 := hb (x (-5) 6)
          have b20125 := hb (x (-4) 5)
          have b20126 := hb (x (-3) 4)
          have b20127 := hb (x (-2) 3)
          have b20128 := hb (x (-1) 2)
          have b20129 := hb (x 0 1)
          clear * - r20115 b20116 b20117 b20118 b20119 b20120 b20121 b20122 b20123 b20124 b20125 b20126 b20127 b20128 b20129 g1 d19760 d19834 d19947 d19810 d20082 d20098
          omega
        have d20130 : (x (-7) 8 && x (-7) 12).toNat = 0 := by
          have r20131 := hand1 (x (-7) 8) (x (-7) 12)
          have b20132 := hb (x (-7) 8)
          have b20133 := hb (x (-7) 8 && x (-7) 12)
          clear * - r20131 b20132 b20133 d20114
          omega
        have d20134 : (x (-8) 9).toNat = 0 := by
          have r20135 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20136 := hb (x (-13) 14)
          have b20137 := hb (x (-12) 13)
          have b20138 := hb (x (-11) 12)
          have b20139 := hb (x (-10) 11)
          have b20140 := hb (x (-9) 10)
          have b20141 := hb (x (-8) 9)
          have b20142 := hb (x (-7) 8)
          have b20143 := hb (x (-6) 7)
          have b20144 := hb (x (-5) 6)
          have b20145 := hb (x (-4) 5)
          have b20146 := hb (x (-3) 4)
          have b20147 := hb (x (-2) 3)
          have b20148 := hb (x (-1) 2)
          have b20149 := hb (x 0 1)
          clear * - r20135 b20136 b20137 b20138 b20139 b20140 b20141 b20142 b20143 b20144 b20145 b20146 b20147 b20148 b20149 g1 d19760 d19834 d19947 d19810 d20082 d20098 d20114
          omega
        have d20150 : (x (-8) 9 && x (-8) 13).toNat = 0 := by
          have r20151 := hand1 (x (-8) 9) (x (-8) 13)
          have b20152 := hb (x (-8) 9)
          have b20153 := hb (x (-8) 9 && x (-8) 13)
          clear * - r20151 b20152 b20153 d20134
          omega
        have d20154 : (x (-9) 10).toNat = 0 := by
          have r20155 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20156 := hb (x (-13) 14)
          have b20157 := hb (x (-12) 13)
          have b20158 := hb (x (-11) 12)
          have b20159 := hb (x (-10) 11)
          have b20160 := hb (x (-9) 10)
          have b20161 := hb (x (-8) 9)
          have b20162 := hb (x (-7) 8)
          have b20163 := hb (x (-6) 7)
          have b20164 := hb (x (-5) 6)
          have b20165 := hb (x (-4) 5)
          have b20166 := hb (x (-3) 4)
          have b20167 := hb (x (-2) 3)
          have b20168 := hb (x (-1) 2)
          have b20169 := hb (x 0 1)
          clear * - r20155 b20156 b20157 b20158 b20159 b20160 b20161 b20162 b20163 b20164 b20165 b20166 b20167 b20168 b20169 g1 d19760 d19834 d19947 d19810 d20082 d20098 d20114 d20134
          omega
        have d20170 : (x (-9) 1 && x (-9) 10).toNat = 0 := by
          have r20171 := hand2 (x (-9) 1) (x (-9) 10)
          have b20172 := hb (x (-9) 10)
          have b20173 := hb (x (-9) 1 && x (-9) 10)
          clear * - r20171 b20172 b20173 d20154
          omega
        have d20174 : (x (-10) 11).toNat = 0 := by
          have r20175 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20176 := hb (x (-13) 14)
          have b20177 := hb (x (-12) 13)
          have b20178 := hb (x (-11) 12)
          have b20179 := hb (x (-10) 11)
          have b20180 := hb (x (-9) 10)
          have b20181 := hb (x (-8) 9)
          have b20182 := hb (x (-7) 8)
          have b20183 := hb (x (-6) 7)
          have b20184 := hb (x (-5) 6)
          have b20185 := hb (x (-4) 5)
          have b20186 := hb (x (-3) 4)
          have b20187 := hb (x (-2) 3)
          have b20188 := hb (x (-1) 2)
          have b20189 := hb (x 0 1)
          clear * - r20175 b20176 b20177 b20178 b20179 b20180 b20181 b20182 b20183 b20184 b20185 b20186 b20187 b20188 b20189 g1 d19760 d19834 d19947 d19810 d20082 d20098 d20114 d20134 d20154
          omega
        have d20190 : (x (-10) 1 && x (-10) 11).toNat = 0 := by
          have r20191 := hand2 (x (-10) 1) (x (-10) 11)
          have b20192 := hb (x (-10) 11)
          have b20193 := hb (x (-10) 1 && x (-10) 11)
          clear * - r20191 b20192 b20193 d20174
          omega
        have d20194 : (x (-10) 2 && x (-10) 11).toNat = 0 := by
          have r20195 := hand2 (x (-10) 2) (x (-10) 11)
          have b20196 := hb (x (-10) 11)
          have b20197 := hb (x (-10) 2 && x (-10) 11)
          clear * - r20195 b20196 b20197 d20174
          omega
        have d20198 : (x (-3) 4 && x (-3) 8).toNat = 1 := by
          have r20199 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := by have q := hcov4 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20200 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
          have e20201 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
          have b20202 := hb (x (-10) 11)
          have b20203 := hb (x (-9) 10)
          have b20204 := hb (x 0 5)
          have b20205 := hb (x 1 4)
          have b20206 := hb (x (-1) 2 && x (-1) 6)
          have b20207 := hb (x (-2) 3 && x (-2) 7)
          have b20208 := hb (x (-3) 4 && x (-3) 8)
          have b20209 := hb (x (-4) 5 && x (-4) 9)
          have b20210 := hb (x (-5) 6 && x (-5) 10)
          have b20211 := hb (x (-6) 7 && x (-6) 11)
          have b20212 := hb (x (-7) 8 && x (-7) 12)
          have b20213 := hb (x (-8) 9 && x (-8) 13)
          clear * - r20199 e20200 e20201 b20202 b20203 b20204 b20205 b20206 b20207 b20208 b20209 b20210 b20211 b20212 b20213 d19830 g3 d20046 d19846 d19814 d19974 d19994 d20130 d20150 d20154 d20174
          omega
        have d20214 : (x (-3) 8).toNat = 1 := by
          have r20215 := hand2 (x (-3) 4) (x (-3) 8)
          have b20216 := hb (x (-3) 8)
          have b20217 := hb (x (-3) 4 && x (-3) 8)
          clear * - r20215 b20216 b20217 d20198
          omega
        have d20218 : (x (-7) 4).toNat = 0 := by
          have r20219 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20220 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e20221 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e20222 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e20223 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e20224 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e20225 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have b20226 := hb (x (-10) 7)
          have b20227 := hb (x (-9) 6)
          have b20228 := hb (x (-8) 5)
          have b20229 := hb (x (-7) 4)
          have b20230 := hb (x (-6) 11)
          have b20231 := hb (x (-5) 10)
          have b20232 := hb (x (-4) 9)
          have b20233 := hb (x (-3) 8)
          clear * - r20219 e20220 e20221 e20222 e20223 e20224 e20225 b20226 b20227 b20228 b20229 b20230 b20231 b20232 b20233 d20214 d19818 d19970 d19990
          omega
        have d20234 : (x (-7) 4 && x (-7) 14).toNat = 0 := by
          have r20235 := hand1 (x (-7) 4) (x (-7) 14)
          have b20236 := hb (x (-7) 4)
          have b20237 := hb (x (-7) 4 && x (-7) 14)
          clear * - r20235 b20236 b20237 d20218
          omega
        have d20238 : (x (-8) 5).toNat = 0 := by
          have r20239 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20240 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e20241 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e20242 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e20243 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e20244 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e20245 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have b20246 := hb (x (-10) 7)
          have b20247 := hb (x (-9) 6)
          have b20248 := hb (x (-8) 5)
          have b20249 := hb (x (-7) 4)
          have b20250 := hb (x (-6) 11)
          have b20251 := hb (x (-5) 10)
          have b20252 := hb (x (-4) 9)
          have b20253 := hb (x (-3) 8)
          clear * - r20239 e20240 e20241 e20242 e20243 e20244 e20245 b20246 b20247 b20248 b20249 b20250 b20251 b20252 b20253 d20214 d19818 d19970 d19990 d20218
          omega
        have d20254 : (x (-3) 10).toNat = 1 := by
          have r20255 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20256 := hb (x (-8) 5)
          have b20257 := hb (x (-3) 10)
          have b20258 := hb (x (-4) 1 && x (-4) 11)
          have b20259 := hb (x (-5) 2 && x (-5) 12)
          have b20260 := hb (x (-6) 3 && x (-6) 13)
          have b20261 := hb (x (-7) 4 && x (-7) 14)
          clear * - r20255 b20256 b20257 b20258 b20259 b20260 b20261 d19802 d19966 d19986 d20234 d20238
          omega
        have d20262 : (x (-1) 8).toNat = 0 := by
          have r20263 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20264 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e20265 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e20266 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e20267 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e20268 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e20269 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b20270 := hb (x (-8) 7)
          have b20271 := hb (x (-7) 6)
          have b20272 := hb (x (-6) 5)
          have b20273 := hb (x (-5) 4)
          have b20274 := hb (x (-4) 11)
          have b20275 := hb (x (-3) 10)
          have b20276 := hb (x (-2) 9)
          have b20277 := hb (x (-1) 8)
          clear * - r20263 e20264 e20265 e20266 e20267 e20268 e20269 b20270 b20271 b20272 b20273 b20274 b20275 b20276 b20277 d19785 d20254 d19878
          omega
        have d20278 : (x (-5) 4).toNat = 0 := by
          have r20279 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20280 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e20281 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e20282 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e20283 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e20284 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e20285 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b20286 := hb (x (-8) 7)
          have b20287 := hb (x (-7) 6)
          have b20288 := hb (x (-6) 5)
          have b20289 := hb (x (-5) 4)
          have b20290 := hb (x (-4) 11)
          have b20291 := hb (x (-3) 10)
          have b20292 := hb (x (-2) 9)
          have b20293 := hb (x (-1) 8)
          clear * - r20279 e20280 e20281 e20282 e20283 e20284 e20285 b20286 b20287 b20288 b20289 b20290 b20291 b20292 b20293 d20262 d19785 d20254 d19878
          omega
        have d20294 : (x (-6) 5).toNat = 0 := by
          have r20295 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20296 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e20297 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e20298 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e20299 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e20300 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e20301 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b20302 := hb (x (-8) 7)
          have b20303 := hb (x (-7) 6)
          have b20304 := hb (x (-6) 5)
          have b20305 := hb (x (-5) 4)
          have b20306 := hb (x (-4) 11)
          have b20307 := hb (x (-3) 10)
          have b20308 := hb (x (-2) 9)
          have b20309 := hb (x (-1) 8)
          clear * - r20295 e20296 e20297 e20298 e20299 e20300 e20301 b20302 b20303 b20304 b20305 b20306 b20307 b20308 b20309 d20262 d19785 d20254 d19878 d20278
          omega
        have d20310 : (x (-7) 6).toNat = 0 := by
          have r20311 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20312 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e20313 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e20314 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e20315 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e20316 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e20317 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b20318 := hb (x (-8) 7)
          have b20319 := hb (x (-7) 6)
          have b20320 := hb (x (-6) 5)
          have b20321 := hb (x (-5) 4)
          have b20322 := hb (x (-4) 11)
          have b20323 := hb (x (-3) 10)
          have b20324 := hb (x (-2) 9)
          have b20325 := hb (x (-1) 8)
          clear * - r20311 e20312 e20313 e20314 e20315 e20316 e20317 b20318 b20319 b20320 b20321 b20322 b20323 b20324 b20325 d20262 d19785 d20254 d19878 d20278 d20294
          omega
        have d20326 : (x (-7) 1 && x (-7) 6).toNat = 0 := by
          have r20327 := hand2 (x (-7) 1) (x (-7) 6)
          have b20328 := hb (x (-7) 6)
          have b20329 := hb (x (-7) 1 && x (-7) 6)
          clear * - r20327 b20328 b20329 d20310
          omega
        have d20330 : (x (-8) 7).toNat = 0 := by
          have r20331 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20332 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e20333 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e20334 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e20335 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e20336 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e20337 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have b20338 := hb (x (-8) 7)
          have b20339 := hb (x (-7) 6)
          have b20340 := hb (x (-6) 5)
          have b20341 := hb (x (-5) 4)
          have b20342 := hb (x (-4) 11)
          have b20343 := hb (x (-3) 10)
          have b20344 := hb (x (-2) 9)
          have b20345 := hb (x (-1) 8)
          clear * - r20331 e20332 e20333 e20334 e20335 e20336 e20337 b20338 b20339 b20340 b20341 b20342 b20343 b20344 b20345 d20262 d19785 d20254 d19878 d20278 d20294 d20310
          omega
        have d20346 : (x (-8) 2 && x (-8) 7).toNat = 0 := by
          have r20347 := hand2 (x (-8) 2) (x (-8) 7)
          have b20348 := hb (x (-8) 7)
          have b20349 := hb (x (-8) 2 && x (-8) 7)
          clear * - r20347 b20348 b20349 d20330
          omega
        have d20350 : (x (-9) 6).toNat = 0 := by
          have r20351 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20352 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e20353 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e20354 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e20355 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e20356 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e20357 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have b20358 := hb (x (-10) 7)
          have b20359 := hb (x (-9) 6)
          have b20360 := hb (x (-8) 5)
          have b20361 := hb (x (-7) 4)
          have b20362 := hb (x (-6) 11)
          have b20363 := hb (x (-5) 10)
          have b20364 := hb (x (-4) 9)
          have b20365 := hb (x (-3) 8)
          clear * - r20351 e20352 e20353 e20354 e20355 e20356 e20357 b20358 b20359 b20360 b20361 b20362 b20363 b20364 b20365 d20214 d19818 d19970 d19990 d20218 d20238
          omega
        have d20366 : (x (-10) 7).toNat = 0 := by
          have r20367 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20368 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e20369 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e20370 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e20371 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e20372 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e20373 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have b20374 := hb (x (-10) 7)
          have b20375 := hb (x (-9) 6)
          have b20376 := hb (x (-8) 5)
          have b20377 := hb (x (-7) 4)
          have b20378 := hb (x (-6) 11)
          have b20379 := hb (x (-5) 10)
          have b20380 := hb (x (-4) 9)
          have b20381 := hb (x (-3) 8)
          clear * - r20367 e20368 e20369 e20370 e20371 e20372 e20373 b20374 b20375 b20376 b20377 b20378 b20379 b20380 b20381 d20214 d19818 d19970 d19990 d20218 d20238 d20350
          omega
        have d20382 : (x (-11) 12).toNat = 0 := by
          have r20383 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20384 := hb (x (-13) 14)
          have b20385 := hb (x (-12) 13)
          have b20386 := hb (x (-11) 12)
          have b20387 := hb (x (-10) 11)
          have b20388 := hb (x (-9) 10)
          have b20389 := hb (x (-8) 9)
          have b20390 := hb (x (-7) 8)
          have b20391 := hb (x (-6) 7)
          have b20392 := hb (x (-5) 6)
          have b20393 := hb (x (-4) 5)
          have b20394 := hb (x (-3) 4)
          have b20395 := hb (x (-2) 3)
          have b20396 := hb (x (-1) 2)
          have b20397 := hb (x 0 1)
          clear * - r20383 b20384 b20385 b20386 b20387 b20388 b20389 b20390 b20391 b20392 b20393 b20394 b20395 b20396 b20397 g1 d19760 d19834 d19947 d19810 d20082 d20098 d20114 d20134 d20154 d20174
          omega
        have d20398 : (x (-11) 2 && x (-11) 12).toNat = 0 := by
          have r20399 := hand2 (x (-11) 2) (x (-11) 12)
          have b20400 := hb (x (-11) 12)
          have b20401 := hb (x (-11) 2 && x (-11) 12)
          clear * - r20399 b20400 b20401 d20382
          omega
        have d20402 : (x (-11) 3 && x (-11) 12).toNat = 0 := by
          have r20403 := hand2 (x (-11) 3) (x (-11) 12)
          have b20404 := hb (x (-11) 12)
          have b20405 := hb (x (-11) 3 && x (-11) 12)
          clear * - r20403 b20404 b20405 d20382
          omega
        have d20406 : (x (-12) 13).toNat = 0 := by
          have r20407 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20408 := hb (x (-13) 14)
          have b20409 := hb (x (-12) 13)
          have b20410 := hb (x (-11) 12)
          have b20411 := hb (x (-10) 11)
          have b20412 := hb (x (-9) 10)
          have b20413 := hb (x (-8) 9)
          have b20414 := hb (x (-7) 8)
          have b20415 := hb (x (-6) 7)
          have b20416 := hb (x (-5) 6)
          have b20417 := hb (x (-4) 5)
          have b20418 := hb (x (-3) 4)
          have b20419 := hb (x (-2) 3)
          have b20420 := hb (x (-1) 2)
          have b20421 := hb (x 0 1)
          clear * - r20407 b20408 b20409 b20410 b20411 b20412 b20413 b20414 b20415 b20416 b20417 b20418 b20419 b20420 b20421 g1 d19760 d19834 d19947 d19810 d20082 d20098 d20114 d20134 d20154 d20174 d20382
          omega
        have d20422 : (x (-12) 3 && x (-12) 13).toNat = 0 := by
          have r20423 := hand2 (x (-12) 3) (x (-12) 13)
          have b20424 := hb (x (-12) 13)
          have b20425 := hb (x (-12) 3 && x (-12) 13)
          clear * - r20423 b20424 b20425 d20406
          omega
        have d20426 : (x (-12) 4 && x (-12) 13).toNat = 0 := by
          have r20427 := hand2 (x (-12) 4) (x (-12) 13)
          have b20428 := hb (x (-12) 13)
          have b20429 := hb (x (-12) 4 && x (-12) 13)
          clear * - r20427 b20428 b20429 d20406
          omega
        have d20430 : (x (-13) 14).toNat = 0 := by
          have r20431 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20432 := hb (x (-13) 14)
          have b20433 := hb (x (-12) 13)
          have b20434 := hb (x (-11) 12)
          have b20435 := hb (x (-10) 11)
          have b20436 := hb (x (-9) 10)
          have b20437 := hb (x (-8) 9)
          have b20438 := hb (x (-7) 8)
          have b20439 := hb (x (-6) 7)
          have b20440 := hb (x (-5) 6)
          have b20441 := hb (x (-4) 5)
          have b20442 := hb (x (-3) 4)
          have b20443 := hb (x (-2) 3)
          have b20444 := hb (x (-1) 2)
          have b20445 := hb (x 0 1)
          clear * - r20431 b20432 b20433 b20434 b20435 b20436 b20437 b20438 b20439 b20440 b20441 b20442 b20443 b20444 b20445 g1 d19760 d19834 d19947 d19810 d20082 d20098 d20114 d20134 d20154 d20174 d20382 d20406
          omega
        have d20446 : (x (-13) 1 && x (-13) 14).toNat = 0 := by
          have r20447 := hand2 (x (-13) 1) (x (-13) 14)
          have b20448 := hb (x (-13) 14)
          have b20449 := hb (x (-13) 1 && x (-13) 14)
          clear * - r20447 b20448 b20449 d20430
          omega
        have d20450 : (x (-14) 2).toNat = 1 := by
          have r20451 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20452 := hb (x (-14) 2)
          have b20453 := hb (x (-12) 13)
          have b20454 := hb (x (-13) 1 && x (-13) 14)
          clear * - r20451 b20452 b20453 b20454 d20406 d20446
          omega
        have d20455 : (x (-14) 14).toNat = 1 := by
          have r20456 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
          have b20457 := hb (x (-14) 2)
          have b20458 := hb (x (-14) 14)
          clear * - r20456 b20457 b20458 d20450
          omega
        have d20459 : (x (-15) 1).toNat = 0 := by
          have r20460 : (x (-14) 14).toNat + (x (-15) 1).toNat = 1 := by have q := hd14 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20461 := hb (x (-15) 1)
          have b20462 := hb (x (-14) 14)
          clear * - r20460 b20461 b20462 d20455
          omega
        have d20463 : (x (-15) 1 && x (-15) 14).toNat = 0 := by
          have r20464 := hand1 (x (-15) 1) (x (-15) 14)
          have b20465 := hb (x (-15) 1)
          have b20466 := hb (x (-15) 1 && x (-15) 14)
          clear * - r20464 b20465 b20466 d20459
          omega
        have d20467 : (x (-15) 1 && x (-15) 12).toNat = 0 := by
          have r20468 := hand1 (x (-15) 1) (x (-15) 12)
          have b20469 := hb (x (-15) 1)
          have b20470 := hb (x (-15) 1 && x (-15) 12)
          clear * - r20468 b20469 b20470 d20459
          omega
        have d20471 : (x (-15) 13).toNat = 0 := by
          have r20472 : (x (-15) 13).toNat ≤ (x (-15) 1).toNat := himp _ _ (hp13 (-15))
          have b20473 := hb (x (-15) 1)
          have b20474 := hb (x (-15) 13)
          clear * - r20472 b20473 b20474 d20459
          omega
        have d20475 : (x (-15) 5).toNat = 0 := by
          have r20476 : (x (-15) 5).toNat ≤ (x (-15) 13).toNat := himp _ _ (hp5 (-15))
          have b20477 := hb (x (-15) 5)
          have b20478 := hb (x (-15) 13)
          clear * - r20476 b20477 b20478 d20471
          omega
        have d20479 : (x (-15) 9).toNat = 0 := by
          have r20480 : (x (-15) 9).toNat ≤ (x (-15) 1).toNat := himp _ _ (hp9 (-15))
          have b20481 := hb (x (-15) 1)
          have b20482 := hb (x (-15) 9)
          clear * - r20480 b20481 b20482 d20459
          omega
        have d20483 : (x (-15) 9 && x (-15) 14).toNat = 0 := by
          have r20484 := hand1 (x (-15) 9) (x (-15) 14)
          have b20485 := hb (x (-15) 9)
          have b20486 := hb (x (-15) 9 && x (-15) 14)
          clear * - r20484 b20485 b20486 d20479
          omega
        have d20487 : (x (-12) 12).toNat = 0 := by
          have r20488 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20489 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
          have e20490 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
          have b20491 := hb (x (-15) 3)
          have b20492 := hb (x (-14) 2)
          have b20493 := hb (x (-13) 13)
          have b20494 := hb (x (-12) 12)
          clear * - r20488 e20489 e20490 b20491 b20492 b20493 b20494 d20450
          omega
        have d20495 : (x (-12) 2 && x (-12) 12).toNat = 0 := by
          have r20496 := hand2 (x (-12) 2) (x (-12) 12)
          have b20497 := hb (x (-12) 12)
          have b20498 := hb (x (-12) 2 && x (-12) 12)
          clear * - r20496 b20497 b20498 d20487
          omega
        have d20499 : (x (-12) 4).toNat = 0 := by
          have r20500 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
          have b20501 := hb (x (-12) 4)
          have b20502 := hb (x (-12) 12)
          clear * - r20500 b20501 b20502 d20487
          omega
        have d20503 : (x (-13) 13).toNat = 0 := by
          have r20504 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20505 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
          have e20506 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
          have b20507 := hb (x (-15) 3)
          have b20508 := hb (x (-14) 2)
          have b20509 := hb (x (-13) 13)
          have b20510 := hb (x (-12) 12)
          clear * - r20504 e20505 e20506 b20507 b20508 b20509 b20510 d20487 d20450
          omega
        have d20511 : (x (-13) 3 && x (-13) 13).toNat = 0 := by
          have r20512 := hand2 (x (-13) 3) (x (-13) 13)
          have b20513 := hb (x (-13) 13)
          have b20514 := hb (x (-13) 3 && x (-13) 13)
          clear * - r20512 b20513 b20514 d20503
          omega
        have d20515 : (x (-13) 5).toNat = 0 := by
          have r20516 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
          have b20517 := hb (x (-13) 5)
          have b20518 := hb (x (-13) 13)
          clear * - r20516 b20517 b20518 d20503
          omega
        have d20519 : (x (-13) 5 && x (-13) 14).toNat = 0 := by
          have r20520 := hand1 (x (-13) 5) (x (-13) 14)
          have b20521 := hb (x (-13) 5)
          have b20522 := hb (x (-13) 5 && x (-13) 14)
          clear * - r20520 b20521 b20522 d20515
          omega
        have d20523 : (x (-14) 6).toNat = 1 := by
          have r20524 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20525 := hb (x (-14) 6)
          have b20526 := hb (x (-8) 9)
          have b20527 := hb (x (-9) 1 && x (-9) 10)
          have b20528 := hb (x (-10) 2 && x (-10) 11)
          have b20529 := hb (x (-11) 3 && x (-11) 12)
          have b20530 := hb (x (-12) 4 && x (-12) 13)
          have b20531 := hb (x (-13) 5 && x (-13) 14)
          clear * - r20524 b20525 b20526 b20527 b20528 b20529 b20530 b20531 d20134 d20170 d20194 d20402 d20426 d20519
          omega
        have d20532 : (x (-8) 8).toNat = 0 := by
          have r20533 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20534 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
          have e20535 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
          have e20536 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
          have e20537 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
          have e20538 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
          have e20539 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
          have b20540 := hb (x (-15) 7)
          have b20541 := hb (x (-14) 6)
          have b20542 := hb (x (-13) 5)
          have b20543 := hb (x (-12) 4)
          have b20544 := hb (x (-11) 11)
          have b20545 := hb (x (-10) 10)
          have b20546 := hb (x (-9) 9)
          have b20547 := hb (x (-8) 8)
          clear * - r20533 e20534 e20535 e20536 e20537 e20538 e20539 b20540 b20541 b20542 b20543 b20544 b20545 b20546 b20547 d20499 d20515 d20523
          omega
        have d20548 : (x (-9) 9).toNat = 0 := by
          have r20549 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20550 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
          have e20551 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
          have e20552 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
          have e20553 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
          have e20554 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
          have e20555 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
          have b20556 := hb (x (-15) 7)
          have b20557 := hb (x (-14) 6)
          have b20558 := hb (x (-13) 5)
          have b20559 := hb (x (-12) 4)
          have b20560 := hb (x (-11) 11)
          have b20561 := hb (x (-10) 10)
          have b20562 := hb (x (-9) 9)
          have b20563 := hb (x (-8) 8)
          clear * - r20549 e20550 e20551 e20552 e20553 e20554 e20555 b20556 b20557 b20558 b20559 b20560 b20561 b20562 b20563 d20532 d20499 d20515 d20523
          omega
        have d20564 : (x (-10) 10).toNat = 0 := by
          have r20565 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20566 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
          have e20567 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
          have e20568 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
          have e20569 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
          have e20570 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
          have e20571 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
          have b20572 := hb (x (-15) 7)
          have b20573 := hb (x (-14) 6)
          have b20574 := hb (x (-13) 5)
          have b20575 := hb (x (-12) 4)
          have b20576 := hb (x (-11) 11)
          have b20577 := hb (x (-10) 10)
          have b20578 := hb (x (-9) 9)
          have b20579 := hb (x (-8) 8)
          clear * - r20565 e20566 e20567 e20568 e20569 e20570 e20571 b20572 b20573 b20574 b20575 b20576 b20577 b20578 b20579 d20532 d20548 d20499 d20515 d20523
          omega
        have d20580 : (x (-11) 11).toNat = 0 := by
          have r20581 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20582 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
          have e20583 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
          have e20584 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
          have e20585 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
          have e20586 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
          have e20587 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
          have b20588 := hb (x (-15) 7)
          have b20589 := hb (x (-14) 6)
          have b20590 := hb (x (-13) 5)
          have b20591 := hb (x (-12) 4)
          have b20592 := hb (x (-11) 11)
          have b20593 := hb (x (-10) 10)
          have b20594 := hb (x (-9) 9)
          have b20595 := hb (x (-8) 8)
          clear * - r20581 e20582 e20583 e20584 e20585 e20586 e20587 b20588 b20589 b20590 b20591 b20592 b20593 b20594 b20595 d20532 d20548 d20564 d20499 d20515 d20523
          omega
        have d20596 : (x (-11) 1 && x (-11) 11).toNat = 0 := by
          have r20597 := hand2 (x (-11) 1) (x (-11) 11)
          have b20598 := hb (x (-11) 11)
          have b20599 := hb (x (-11) 1 && x (-11) 11)
          clear * - r20597 b20598 b20599 d20580
          omega
        have d20600 : (x (-14) 4 && x (-14) 14).toNat = 1 := by
          have r20601 : 1 ≤ (x (-10) 10).toNat + (x (-11) 1 && x (-11) 11).toNat + (x (-12) 2 && x (-12) 12).toNat + (x (-13) 3 && x (-13) 13).toNat + (x (-14) 4 && x (-14) 14).toNat + (x (-15) 5).toNat := by have q := hcov10 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20602 := hb (x (-15) 5)
          have b20603 := hb (x (-10) 10)
          have b20604 := hb (x (-11) 1 && x (-11) 11)
          have b20605 := hb (x (-12) 2 && x (-12) 12)
          have b20606 := hb (x (-13) 3 && x (-13) 13)
          have b20607 := hb (x (-14) 4 && x (-14) 14)
          clear * - r20601 b20602 b20603 b20604 b20605 b20606 b20607 d20564 d20596 d20495 d20511 d20475
          omega
        have d20608 : (x (-14) 4).toNat = 1 := by
          have r20609 := hand1 (x (-14) 4) (x (-14) 14)
          have b20610 := hb (x (-14) 4)
          have b20611 := hb (x (-14) 4 && x (-14) 14)
          clear * - r20609 b20610 b20611 d20600
          omega
        have d20612 : (x (-14) 12).toNat = 1 := by
          have r20613 : (x (-14) 4).toNat ≤ (x (-14) 12).toNat := himp _ _ (hp4 (-14))
          have b20614 := hb (x (-14) 4)
          have b20615 := hb (x (-14) 12)
          clear * - r20613 b20614 b20615 d20608
          omega
        have d20616 : (x (-16) 2).toNat = 0 := by
          have r20617 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20618 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
          have e20619 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
          have b20620 := hb (x (-17) 3)
          have b20621 := hb (x (-16) 2)
          have b20622 := hb (x (-15) 13)
          have b20623 := hb (x (-14) 12)
          clear * - r20617 e20618 e20619 b20620 b20621 b20622 b20623 d20612 d20471
          omega
        have d20624 : (x (-16) 2 && x (-16) 13).toNat = 0 := by
          have r20625 := hand1 (x (-16) 2) (x (-16) 13)
          have b20626 := hb (x (-16) 2)
          have b20627 := hb (x (-16) 2 && x (-16) 13)
          clear * - r20625 b20626 b20627 d20616
          omega
        have d20628 : (x (-16) 10).toNat = 0 := by
          have r20629 : (x (-16) 10).toNat ≤ (x (-16) 2).toNat := himp _ _ (hp10 (-16))
          have b20630 := hb (x (-16) 2)
          have b20631 := hb (x (-16) 10)
          clear * - r20629 b20630 b20631 d20616
          omega
        have d20632 : (x (-14) 13).toNat = 1 := by
          have r20633 : 1 ≤ (x (-14) 13).toNat + (x (-15) 1 && x (-15) 14).toNat + (x (-16) 2).toNat := by have q := hcov13 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20634 := hb (x (-16) 2)
          have b20635 := hb (x (-14) 13)
          have b20636 := hb (x (-15) 1 && x (-15) 14)
          clear * - r20633 b20634 b20635 b20636 d20463 d20616
          omega
        have d20637 : (x (-13) 12).toNat = 0 := by
          have r20638 : (x (-13) 12).toNat + (x (-14) 1 && x (-14) 13).toNat + (x (-15) 2 && x (-15) 14).toNat + (x (-16) 3).toNat = 1 := by have q := hd12 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20639 : (x (-14) 1 && x (-14) 13).toNat = (x (-14) 13).toNat := handr _ _ (fun h => hp13 (-14) (h))
          have e20640 : (x (-15) 2 && x (-15) 14).toNat = (x (-15) 2).toNat := handl _ _ (fun h => hp2 (-15) (h))
          have b20641 := hb (x (-16) 3)
          have b20642 := hb (x (-15) 2)
          have b20643 := hb (x (-14) 13)
          have b20644 := hb (x (-13) 12)
          clear * - r20638 e20639 e20640 b20641 b20642 b20643 b20644 d20632
          omega
        have d20645 : (x (-13) 7 && x (-13) 12).toNat = 0 := by
          have r20646 := hand2 (x (-13) 7) (x (-13) 12)
          have b20647 := hb (x (-13) 12)
          have b20648 := hb (x (-13) 7 && x (-13) 12)
          clear * - r20646 b20647 b20648 d20637
          omega
        have d20649 : (x (-13) 4).toNat = 0 := by
          have r20650 : (x (-13) 4).toNat ≤ (x (-13) 12).toNat := himp _ _ (hp4 (-13))
          have b20651 := hb (x (-13) 4)
          have b20652 := hb (x (-13) 12)
          clear * - r20650 b20651 b20652 d20637
          omega
        have d20653 : (x (-13) 4 && x (-13) 14).toNat = 0 := by
          have r20654 := hand1 (x (-13) 4) (x (-13) 14)
          have b20655 := hb (x (-13) 4)
          have b20656 := hb (x (-13) 4 && x (-13) 14)
          clear * - r20654 b20655 b20656 d20649
          omega
        have d20657 : (x (-14) 5).toNat = 1 := by
          have r20658 : 1 ≤ (x (-9) 10).toNat + (x (-10) 1 && x (-10) 11).toNat + (x (-11) 2 && x (-11) 12).toNat + (x (-12) 3 && x (-12) 13).toNat + (x (-13) 4 && x (-13) 14).toNat + (x (-14) 5).toNat := by have q := hcov10 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20659 := hb (x (-14) 5)
          have b20660 := hb (x (-9) 10)
          have b20661 := hb (x (-10) 1 && x (-10) 11)
          have b20662 := hb (x (-11) 2 && x (-11) 12)
          have b20663 := hb (x (-12) 3 && x (-12) 13)
          have b20664 := hb (x (-13) 4 && x (-13) 14)
          clear * - r20658 b20659 b20660 b20661 b20662 b20663 b20664 d20154 d20190 d20398 d20422 d20653
          omega
        have d20665 : (x (-9) 8).toNat = 0 := by
          have r20666 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20667 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
          have e20668 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
          have e20669 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
          have e20670 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
          have e20671 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
          have e20672 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
          have b20673 := hb (x (-16) 7)
          have b20674 := hb (x (-15) 6)
          have b20675 := hb (x (-14) 5)
          have b20676 := hb (x (-13) 4)
          have b20677 := hb (x (-12) 11)
          have b20678 := hb (x (-11) 10)
          have b20679 := hb (x (-10) 9)
          have b20680 := hb (x (-9) 8)
          clear * - r20666 e20667 e20668 e20669 e20670 e20671 e20672 b20673 b20674 b20675 b20676 b20677 b20678 b20679 b20680 d20649 d20657
          omega
        have d20681 : (x (-9) 3 && x (-9) 8).toNat = 0 := by
          have r20682 := hand2 (x (-9) 3) (x (-9) 8)
          have b20683 := hb (x (-9) 8)
          have b20684 := hb (x (-9) 3 && x (-9) 8)
          clear * - r20682 b20683 b20684 d20665
          omega
        have d20685 : (x (-10) 9).toNat = 0 := by
          have r20686 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20687 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
          have e20688 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
          have e20689 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
          have e20690 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
          have e20691 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
          have e20692 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
          have b20693 := hb (x (-16) 7)
          have b20694 := hb (x (-15) 6)
          have b20695 := hb (x (-14) 5)
          have b20696 := hb (x (-13) 4)
          have b20697 := hb (x (-12) 11)
          have b20698 := hb (x (-11) 10)
          have b20699 := hb (x (-10) 9)
          have b20700 := hb (x (-9) 8)
          clear * - r20686 e20687 e20688 e20689 e20690 e20691 e20692 b20693 b20694 b20695 b20696 b20697 b20698 b20699 b20700 d20665 d20649 d20657
          omega
        have d20701 : (x (-10) 4 && x (-10) 9).toNat = 0 := by
          have r20702 := hand2 (x (-10) 4) (x (-10) 9)
          have b20703 := hb (x (-10) 9)
          have b20704 := hb (x (-10) 4 && x (-10) 9)
          clear * - r20702 b20703 b20704 d20685
          omega
        have d20705 : (x (-11) 10).toNat = 0 := by
          have r20706 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20707 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
          have e20708 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
          have e20709 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
          have e20710 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
          have e20711 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
          have e20712 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
          have b20713 := hb (x (-16) 7)
          have b20714 := hb (x (-15) 6)
          have b20715 := hb (x (-14) 5)
          have b20716 := hb (x (-13) 4)
          have b20717 := hb (x (-12) 11)
          have b20718 := hb (x (-11) 10)
          have b20719 := hb (x (-10) 9)
          have b20720 := hb (x (-9) 8)
          clear * - r20706 e20707 e20708 e20709 e20710 e20711 e20712 b20713 b20714 b20715 b20716 b20717 b20718 b20719 b20720 d20665 d20685 d20649 d20657
          omega
        have d20721 : (x (-11) 5 && x (-11) 10).toNat = 0 := by
          have r20722 := hand2 (x (-11) 5) (x (-11) 10)
          have b20723 := hb (x (-11) 10)
          have b20724 := hb (x (-11) 5 && x (-11) 10)
          clear * - r20722 b20723 b20724 d20705
          omega
        have d20725 : (x (-12) 11).toNat = 0 := by
          have r20726 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20727 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
          have e20728 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
          have e20729 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
          have e20730 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
          have e20731 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
          have e20732 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
          have b20733 := hb (x (-16) 7)
          have b20734 := hb (x (-15) 6)
          have b20735 := hb (x (-14) 5)
          have b20736 := hb (x (-13) 4)
          have b20737 := hb (x (-12) 11)
          have b20738 := hb (x (-11) 10)
          have b20739 := hb (x (-10) 9)
          have b20740 := hb (x (-9) 8)
          clear * - r20726 e20727 e20728 e20729 e20730 e20731 e20732 b20733 b20734 b20735 b20736 b20737 b20738 b20739 b20740 d20665 d20685 d20705 d20649 d20657
          omega
        have d20741 : (x (-12) 6 && x (-12) 11).toNat = 0 := by
          have r20742 := hand2 (x (-12) 6) (x (-12) 11)
          have b20743 := hb (x (-12) 11)
          have b20744 := hb (x (-12) 6 && x (-12) 11)
          clear * - r20742 b20743 b20744 d20725
          omega
        have d20745 : (x (-14) 8 && x (-14) 13).toNat = 1 := by
          have r20746 : 1 ≤ (x (-6) 5).toNat + (x (-7) 1 && x (-7) 6).toNat + (x (-8) 2 && x (-8) 7).toNat + (x (-9) 3 && x (-9) 8).toNat + (x (-10) 4 && x (-10) 9).toNat + (x (-11) 5 && x (-11) 10).toNat + (x (-12) 6 && x (-12) 11).toNat + (x (-13) 7 && x (-13) 12).toNat + (x (-14) 8 && x (-14) 13).toNat + (x (-15) 9 && x (-15) 14).toNat + (x (-16) 10).toNat := by have q := hcov5 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20747 := hb (x (-16) 10)
          have b20748 := hb (x (-6) 5)
          have b20749 := hb (x (-7) 1 && x (-7) 6)
          have b20750 := hb (x (-8) 2 && x (-8) 7)
          have b20751 := hb (x (-9) 3 && x (-9) 8)
          have b20752 := hb (x (-10) 4 && x (-10) 9)
          have b20753 := hb (x (-11) 5 && x (-11) 10)
          have b20754 := hb (x (-12) 6 && x (-12) 11)
          have b20755 := hb (x (-13) 7 && x (-13) 12)
          have b20756 := hb (x (-14) 8 && x (-14) 13)
          have b20757 := hb (x (-15) 9 && x (-15) 14)
          clear * - r20746 b20747 b20748 b20749 b20750 b20751 b20752 b20753 b20754 b20755 b20756 b20757 d20294 d20326 d20346 d20681 d20701 d20721 d20741 d20645 d20483 d20628
          omega
        have d20758 : (x (-14) 8).toNat = 1 := by
          have r20759 := hand1 (x (-14) 8) (x (-14) 13)
          have b20760 := hb (x (-14) 8)
          have b20761 := hb (x (-14) 8 && x (-14) 13)
          clear * - r20759 b20760 b20761 d20745
          omega
        have d20762 : (x (-17) 11).toNat = 0 := by
          have r20763 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20764 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
          have e20765 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
          have e20766 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
          have e20767 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
          have e20768 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
          have e20769 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
          have b20770 := hb (x (-21) 7)
          have b20771 := hb (x (-20) 6)
          have b20772 := hb (x (-19) 5)
          have b20773 := hb (x (-18) 4)
          have b20774 := hb (x (-17) 11)
          have b20775 := hb (x (-16) 10)
          have b20776 := hb (x (-15) 9)
          have b20777 := hb (x (-14) 8)
          clear * - r20763 e20764 e20765 e20766 e20767 e20768 e20769 b20770 b20771 b20772 b20773 b20774 b20775 b20776 b20777 d20758 d20479 d20628
          omega
        have d20778 : (x (-18) 4).toNat = 0 := by
          have r20779 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20780 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
          have e20781 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
          have e20782 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
          have e20783 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
          have e20784 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
          have e20785 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
          have b20786 := hb (x (-21) 7)
          have b20787 := hb (x (-20) 6)
          have b20788 := hb (x (-19) 5)
          have b20789 := hb (x (-18) 4)
          have b20790 := hb (x (-17) 11)
          have b20791 := hb (x (-16) 10)
          have b20792 := hb (x (-15) 9)
          have b20793 := hb (x (-14) 8)
          clear * - r20779 e20780 e20781 e20782 e20783 e20784 e20785 b20786 b20787 b20788 b20789 b20790 b20791 b20792 b20793 d20758 d20479 d20628 d20762
          omega
        have d20794 : (x (-17) 3).toNat = 0 := by
          have r20795 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20796 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
          have e20797 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
          have b20798 := hb (x (-17) 3)
          have b20799 := hb (x (-16) 2)
          have b20800 := hb (x (-15) 13)
          have b20801 := hb (x (-14) 12)
          clear * - r20795 e20796 e20797 b20798 b20799 b20800 b20801 d20612 d20471 d20616
          omega
        have d20802 : (x (-17) 3 && x (-17) 14).toNat = 0 := by
          have r20803 := hand1 (x (-17) 3) (x (-17) 14)
          have b20804 := hb (x (-17) 3)
          have b20805 := hb (x (-17) 3 && x (-17) 14)
          clear * - r20803 b20804 b20805 d20794
          omega
        have d20806 : (x (-14) 11).toNat = 1 := by
          have r20807 : 1 ≤ (x (-14) 11).toNat + (x (-15) 1 && x (-15) 12).toNat + (x (-16) 2 && x (-16) 13).toNat + (x (-17) 3 && x (-17) 14).toNat + (x (-18) 4).toNat := by have q := hcov11 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20808 := hb (x (-18) 4)
          have b20809 := hb (x (-14) 11)
          have b20810 := hb (x (-15) 1 && x (-15) 12)
          have b20811 := hb (x (-16) 2 && x (-16) 13)
          have b20812 := hb (x (-17) 3 && x (-17) 14)
          clear * - r20807 b20808 b20809 b20810 b20811 b20812 d20467 d20624 d20802 d20778
          omega
        have d20813 : (x (-14) 3).toNat = 1 := by
          have r20814 : (x (-14) 11).toNat ≤ (x (-14) 3).toNat := himp _ _ (hp11 (-14))
          have b20815 := hb (x (-14) 3)
          have b20816 := hb (x (-14) 11)
          clear * - r20814 b20815 b20816 d20806
          omega
        have d20817 : (x (-13) 2).toNat = 0 := by
          have r20818 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20819 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
          have e20820 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
          have b20821 := hb (x (-14) 3)
          have b20822 := hb (x (-13) 2)
          have b20823 := hb (x (-12) 13)
          have b20824 := hb (x (-11) 12)
          clear * - r20818 e20819 e20820 b20821 b20822 b20823 b20824 d20382 d20406 d20813
          omega
        have d20825 : (x (-13) 10).toNat = 0 := by
          have r20826 : (x (-13) 10).toNat ≤ (x (-13) 2).toNat := himp _ _ (hp10 (-13))
          have b20827 := hb (x (-13) 2)
          have b20828 := hb (x (-13) 10)
          clear * - r20826 b20827 b20828 d20817
          omega
        have d20829 : (x (-11) 8).toNat = 0 := by
          have r20830 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20831 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
          have e20832 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
          have e20833 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
          have e20834 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
          have e20835 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
          have e20836 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
          have b20837 := hb (x (-18) 7)
          have b20838 := hb (x (-17) 6)
          have b20839 := hb (x (-16) 5)
          have b20840 := hb (x (-15) 4)
          have b20841 := hb (x (-14) 11)
          have b20842 := hb (x (-13) 10)
          have b20843 := hb (x (-12) 9)
          have b20844 := hb (x (-11) 8)
          clear * - r20830 e20831 e20832 e20833 e20834 e20835 e20836 b20837 b20838 b20839 b20840 b20841 b20842 b20843 b20844 d20825 d20806
          omega
        have d20845 : (x (-12) 9).toNat = 0 := by
          have r20846 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20847 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
          have e20848 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
          have e20849 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
          have e20850 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
          have e20851 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
          have e20852 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
          have b20853 := hb (x (-18) 7)
          have b20854 := hb (x (-17) 6)
          have b20855 := hb (x (-16) 5)
          have b20856 := hb (x (-15) 4)
          have b20857 := hb (x (-14) 11)
          have b20858 := hb (x (-13) 10)
          have b20859 := hb (x (-12) 9)
          have b20860 := hb (x (-11) 8)
          clear * - r20846 e20847 e20848 e20849 e20850 e20851 e20852 b20853 b20854 b20855 b20856 b20857 b20858 b20859 b20860 d20829 d20825 d20806
          omega
        have d20861 : (x (-15) 14).toNat = 1 := by
          have r20862 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20863 := hb (x (-15) 14)
          have b20864 := hb (x (-14) 13)
          have b20865 := hb (x (-13) 12)
          have b20866 := hb (x (-12) 11)
          have b20867 := hb (x (-11) 10)
          have b20868 := hb (x (-10) 9)
          have b20869 := hb (x (-9) 8)
          have b20870 := hb (x (-8) 7)
          have b20871 := hb (x (-7) 6)
          have b20872 := hb (x (-6) 5)
          have b20873 := hb (x (-5) 4)
          have b20874 := hb (x (-4) 3)
          have b20875 := hb (x (-3) 2)
          have b20876 := hb (x (-2) 1)
          clear * - r20862 b20863 b20864 b20865 b20866 b20867 b20868 b20869 b20870 b20871 b20872 b20873 b20874 b20875 b20876 d19769 d19789 d19870 d20278 d20294 d20310 d20330 d20665 d20685 d20705 d20725 d20637 d20632
          omega
        have d20877 : (x (-16) 1).toNat = 0 := by
          have r20878 : (x (-15) 14).toNat + (x (-16) 1).toNat = 1 := by have q := hd14 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20879 := hb (x (-16) 1)
          have b20880 := hb (x (-15) 14)
          clear * - r20878 b20879 b20880 d20861
          omega
        have d20881 : (x (-16) 1 && x (-16) 14).toNat = 0 := by
          have r20882 := hand1 (x (-16) 1) (x (-16) 14)
          have b20883 := hb (x (-16) 1)
          have b20884 := hb (x (-16) 1 && x (-16) 14)
          clear * - r20882 b20883 b20884 d20877
          omega
        have d20885 : (x (-17) 2).toNat = 1 := by
          have r20886 : 1 ≤ (x (-15) 13).toNat + (x (-16) 1 && x (-16) 14).toNat + (x (-17) 2).toNat := by have q := hcov13 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20887 := hb (x (-17) 2)
          have b20888 := hb (x (-15) 13)
          have b20889 := hb (x (-16) 1 && x (-16) 14)
          clear * - r20886 b20887 b20888 b20889 d20471 d20881
          omega
        have d20890 : (x (-17) 14).toNat = 1 := by
          have r20891 : (x (-17) 2).toNat ≤ (x (-17) 14).toNat := himp _ _ (hp2 (-17))
          have b20892 := hb (x (-17) 2)
          have b20893 := hb (x (-17) 14)
          clear * - r20891 b20892 b20893 d20885
          omega
        have d20894 : (x (-15) 12).toNat = 0 := by
          have r20895 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20896 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
          have e20897 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
          have b20898 := hb (x (-18) 3)
          have b20899 := hb (x (-17) 2)
          have b20900 := hb (x (-16) 13)
          have b20901 := hb (x (-15) 12)
          clear * - r20895 e20896 e20897 b20898 b20899 b20900 b20901 d20885
          omega
        have d20902 : (x (-16) 13).toNat = 0 := by
          have r20903 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20904 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
          have e20905 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
          have b20906 := hb (x (-18) 3)
          have b20907 := hb (x (-17) 2)
          have b20908 := hb (x (-16) 13)
          have b20909 := hb (x (-15) 12)
          clear * - r20903 e20904 e20905 b20906 b20907 b20908 b20909 d20894 d20885
          omega
        have r20910 : (x (-4) 1).toNat + (x (-5) 2).toNat + (x (-6) 3).toNat + (x (-7) 4).toNat + (x (-8) 5).toNat + (x (-9) 6).toNat + (x (-10) 7).toNat + (x (-11) 8).toNat + (x (-12) 9).toNat + (x (-13) 10).toNat + (x (-14) 11).toNat + (x (-15) 12).toNat + (x (-16) 13).toNat + (x (-17) 14).toNat = 3 := by have q := hcount (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b20911 := hb (x (-17) 14)
        have b20912 := hb (x (-16) 13)
        have b20913 := hb (x (-15) 12)
        have b20914 := hb (x (-14) 11)
        have b20915 := hb (x (-13) 10)
        have b20916 := hb (x (-12) 9)
        have b20917 := hb (x (-11) 8)
        have b20918 := hb (x (-10) 7)
        have b20919 := hb (x (-9) 6)
        have b20920 := hb (x (-8) 5)
        have b20921 := hb (x (-7) 4)
        have b20922 := hb (x (-6) 3)
        have b20923 := hb (x (-5) 2)
        have b20924 := hb (x (-4) 1)
        linarith only [r20910, b20911, b20912, b20913, b20914, b20915, b20916, b20917, b20918, b20919, b20920, b20921, b20922, b20923, b20924, d19798, d19958, d19978, d20218, d20238, d20350, d20366, d20829, d20845, d20825, d20806, d20894, d20902, d20890]
      · have f20925 : (x 1 1).toNat = 1 := by rw [h19754]; rfl
        have d20926 : (x 2 14).toNat = 0 := by
          have r20927 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20928 := hb (x 1 1)
          have b20929 := hb (x 2 14)
          clear * - r20927 b20928 b20929 f20925
          omega
        have d20930 : (x 2 1 && x 2 14).toNat = 0 := by
          have r20931 := hand2 (x 2 1) (x 2 14)
          have b20932 := hb (x 2 14)
          have b20933 := hb (x 2 1 && x 2 14)
          clear * - r20931 b20932 b20933 d20926
          omega
        have d20934 : (x 2 2).toNat = 0 := by
          have r20935 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b20936 := hb (x 2 2)
          have b20937 := hb (x 2 14)
          clear * - r20935 b20936 b20937 d20926
          omega
        have d20938 : (x 4 13).toNat = 1 := by
          have r20939 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20940 := hb (x 2 2)
          have b20941 := hb (x 4 13)
          have b20942 := hb (x 3 1 && x 3 14)
          clear * - r20939 b20940 b20941 b20942 g18 d20934
          omega
        have d20943 : (x 4 1).toNat = 1 := by
          have r20944 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b20945 := hb (x 4 1)
          have b20946 := hb (x 4 13)
          clear * - r20944 b20945 b20946 d20938
          omega
        have d20947 : (x 5 14).toNat = 0 := by
          have r20948 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20949 := hb (x 4 1)
          have b20950 := hb (x 5 14)
          clear * - r20948 b20949 b20950 d20943
          omega
        have d20951 : (x 5 1 && x 5 14).toNat = 0 := by
          have r20952 := hand2 (x 5 1) (x 5 14)
          have b20953 := hb (x 5 14)
          have b20954 := hb (x 5 1 && x 5 14)
          clear * - r20952 b20953 b20954 d20947
          omega
        have d20955 : (x 5 2).toNat = 0 := by
          have r20956 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b20957 := hb (x 5 2)
          have b20958 := hb (x 5 14)
          clear * - r20956 b20957 b20958 d20947
          omega
        have d20959 : (x 3 13).toNat = 1 := by
          have r20960 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20961 := hb (x 1 2)
          have b20962 := hb (x 3 13)
          have b20963 := hb (x 2 1 && x 2 14)
          clear * - r20960 b20961 b20962 b20963 d20930 g7
          omega
        have d20964 : (x 3 1).toNat = 1 := by
          have r20965 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b20966 := hb (x 3 1)
          have b20967 := hb (x 3 13)
          clear * - r20965 b20966 b20967 d20959
          omega
        have d20968 : (x 4 14).toNat = 0 := by
          have r20969 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20970 := hb (x 3 1)
          have b20971 := hb (x 4 14)
          clear * - r20969 b20970 b20971 d20964
          omega
        have d20972 : (x 4 1 && x 4 14).toNat = 0 := by
          have r20973 := hand2 (x 4 1) (x 4 14)
          have b20974 := hb (x 4 14)
          have b20975 := hb (x 4 1 && x 4 14)
          clear * - r20973 b20974 b20975 d20968
          omega
        have d20976 : (x 5 13).toNat = 1 := by
          have r20977 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20978 := hb (x 3 2)
          have b20979 := hb (x 5 13)
          have b20980 := hb (x 4 1 && x 4 14)
          clear * - r20977 b20978 b20979 b20980 d20972 g9
          omega
        have d20981 : (x 5 1).toNat = 1 := by
          have r20982 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
          have b20983 := hb (x 5 1)
          have b20984 := hb (x 5 13)
          clear * - r20982 b20983 b20984 d20976
          omega
        have d20985 : (x 6 14).toNat = 0 := by
          have r20986 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20987 := hb (x 5 1)
          have b20988 := hb (x 6 14)
          clear * - r20986 b20987 b20988 d20981
          omega
        have d20989 : (x 6 1 && x 6 14).toNat = 0 := by
          have r20990 := hand2 (x 6 1) (x 6 14)
          have b20991 := hb (x 6 14)
          have b20992 := hb (x 6 1 && x 6 14)
          clear * - r20990 b20991 b20992 d20985
          omega
        have d20993 : (x 7 13).toNat = 1 := by
          have r20994 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20995 := hb (x 5 2)
          have b20996 := hb (x 7 13)
          have b20997 := hb (x 6 1 && x 6 14)
          clear * - r20994 b20995 b20996 b20997 d20989 d20955
          omega
        have d20998 : (x 7 1).toNat = 1 := by
          have r20999 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b21000 := hb (x 7 1)
          have b21001 := hb (x 7 13)
          clear * - r20999 b21000 b21001 d20993
          omega
        have d21002 : (x 8 14).toNat = 0 := by
          have r21003 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21004 := hb (x 7 1)
          have b21005 := hb (x 8 14)
          clear * - r21003 b21004 b21005 d20998
          omega
        have d21006 : (x 8 1 && x 8 14).toNat = 0 := by
          have r21007 := hand2 (x 8 1) (x 8 14)
          have b21008 := hb (x 8 14)
          have b21009 := hb (x 8 1 && x 8 14)
          clear * - r21007 b21008 b21009 d21002
          omega
        have d21010 : (x 8 2).toNat = 0 := by
          have r21011 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
          have b21012 := hb (x 8 2)
          have b21013 := hb (x 8 14)
          clear * - r21011 b21012 b21013 d21002
          omega
        have d21014 : (x 6 2).toNat = 0 := by
          have r21015 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
          have b21016 := hb (x 6 2)
          have b21017 := hb (x 6 14)
          clear * - r21015 b21016 b21017 d20985
          omega
        have d21018 : (x 4 2).toNat = 0 := by
          have r21019 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b21020 := hb (x 4 2)
          have b21021 := hb (x 4 14)
          clear * - r21019 b21020 b21021 d20968
          omega
        have d21022 : (x 6 13).toNat = 1 := by
          have r21023 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21024 := hb (x 4 2)
          have b21025 := hb (x 6 13)
          have b21026 := hb (x 5 1 && x 5 14)
          clear * - r21023 b21024 b21025 b21026 d20951 d21018
          omega
        have d21027 : (x 6 1).toNat = 1 := by
          have r21028 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b21029 := hb (x 6 1)
          have b21030 := hb (x 6 13)
          clear * - r21028 b21029 b21030 d21022
          omega
        have d21031 : (x 7 14).toNat = 0 := by
          have r21032 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21033 := hb (x 6 1)
          have b21034 := hb (x 7 14)
          clear * - r21032 b21033 b21034 d21027
          omega
        have d21035 : (x 7 1 && x 7 14).toNat = 0 := by
          have r21036 := hand2 (x 7 1) (x 7 14)
          have b21037 := hb (x 7 14)
          have b21038 := hb (x 7 1 && x 7 14)
          clear * - r21036 b21037 b21038 d21031
          omega
        have d21039 : (x 8 13).toNat = 1 := by
          have r21040 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21041 := hb (x 6 2)
          have b21042 := hb (x 8 13)
          have b21043 := hb (x 7 1 && x 7 14)
          clear * - r21040 b21041 b21042 b21043 d21035 d21014
          omega
        have d21044 : (x 8 1).toNat = 1 := by
          have r21045 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b21046 := hb (x 8 1)
          have b21047 := hb (x 8 13)
          clear * - r21045 b21046 b21047 d21039
          omega
        have d21048 : (x 9 14).toNat = 0 := by
          have r21049 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21050 := hb (x 8 1)
          have b21051 := hb (x 9 14)
          clear * - r21049 b21050 b21051 d21044
          omega
        have d21052 : (x 9 1 && x 9 14).toNat = 0 := by
          have r21053 := hand2 (x 9 1) (x 9 14)
          have b21054 := hb (x 9 14)
          have b21055 := hb (x 9 1 && x 9 14)
          clear * - r21053 b21054 b21055 d21048
          omega
        have d21056 : (x 10 13).toNat = 1 := by
          have r21057 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21058 := hb (x 8 2)
          have b21059 := hb (x 10 13)
          have b21060 := hb (x 9 1 && x 9 14)
          clear * - r21057 b21058 b21059 b21060 d21052 d21010
          omega
        have d21061 : (x 10 1).toNat = 1 := by
          have r21062 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b21063 := hb (x 10 1)
          have b21064 := hb (x 10 13)
          clear * - r21062 b21063 b21064 d21056
          omega
        have d21065 : (x 11 14).toNat = 0 := by
          have r21066 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21067 := hb (x 10 1)
          have b21068 := hb (x 11 14)
          clear * - r21066 b21067 b21068 d21061
          omega
        have d21069 : (x 11 1 && x 11 14).toNat = 0 := by
          have r21070 := hand2 (x 11 1) (x 11 14)
          have b21071 := hb (x 11 14)
          have b21072 := hb (x 11 1 && x 11 14)
          clear * - r21070 b21071 b21072 d21065
          omega
        have d21073 : (x 11 2).toNat = 0 := by
          have r21074 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b21075 := hb (x 11 2)
          have b21076 := hb (x 11 14)
          clear * - r21074 b21075 b21076 d21065
          omega
        have d21077 : (x 9 2).toNat = 0 := by
          have r21078 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b21079 := hb (x 9 2)
          have b21080 := hb (x 9 14)
          clear * - r21078 b21079 b21080 d21048
          omega
        have d21081 : (x 7 2).toNat = 0 := by
          have r21082 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b21083 := hb (x 7 2)
          have b21084 := hb (x 7 14)
          clear * - r21082 b21083 b21084 d21031
          omega
        have d21085 : (x 9 13).toNat = 1 := by
          have r21086 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21087 := hb (x 7 2)
          have b21088 := hb (x 9 13)
          have b21089 := hb (x 8 1 && x 8 14)
          clear * - r21086 b21087 b21088 b21089 d21006 d21081
          omega
        have d21090 : (x 9 1).toNat = 1 := by
          have r21091 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b21092 := hb (x 9 1)
          have b21093 := hb (x 9 13)
          clear * - r21091 b21092 b21093 d21085
          omega
        have d21094 : (x 10 14).toNat = 0 := by
          have r21095 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21096 := hb (x 9 1)
          have b21097 := hb (x 10 14)
          clear * - r21095 b21096 b21097 d21090
          omega
        have d21098 : (x 10 1 && x 10 14).toNat = 0 := by
          have r21099 := hand2 (x 10 1) (x 10 14)
          have b21100 := hb (x 10 14)
          have b21101 := hb (x 10 1 && x 10 14)
          clear * - r21099 b21100 b21101 d21094
          omega
        have d21102 : (x 11 13).toNat = 1 := by
          have r21103 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21104 := hb (x 9 2)
          have b21105 := hb (x 11 13)
          have b21106 := hb (x 10 1 && x 10 14)
          clear * - r21103 b21104 b21105 b21106 d21098 d21077
          omega
        have d21107 : (x 11 1).toNat = 1 := by
          have r21108 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
          have b21109 := hb (x 11 1)
          have b21110 := hb (x 11 13)
          clear * - r21108 b21109 b21110 d21102
          omega
        have d21111 : (x 12 14).toNat = 0 := by
          have r21112 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21113 := hb (x 11 1)
          have b21114 := hb (x 12 14)
          clear * - r21112 b21113 b21114 d21107
          omega
        have d21115 : (x 12 1 && x 12 14).toNat = 0 := by
          have r21116 := hand2 (x 12 1) (x 12 14)
          have b21117 := hb (x 12 14)
          have b21118 := hb (x 12 1 && x 12 14)
          clear * - r21116 b21117 b21118 d21111
          omega
        have d21119 : (x 13 13).toNat = 1 := by
          have r21120 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21121 := hb (x 11 2)
          have b21122 := hb (x 13 13)
          have b21123 := hb (x 12 1 && x 12 14)
          clear * - r21120 b21121 b21122 b21123 d21115 d21073
          omega
        have d21124 : (x 13 1).toNat = 1 := by
          have r21125 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have b21126 := hb (x 13 1)
          have b21127 := hb (x 13 13)
          clear * - r21125 b21126 b21127 d21119
          omega
        have d21128 : (x 14 14).toNat = 0 := by
          have r21129 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21130 := hb (x 13 1)
          have b21131 := hb (x 14 14)
          clear * - r21129 b21130 b21131 d21124
          omega
        have d21132 : (x 14 1 && x 14 14).toNat = 0 := by
          have r21133 := hand2 (x 14 1) (x 14 14)
          have b21134 := hb (x 14 14)
          have b21135 := hb (x 14 1 && x 14 14)
          clear * - r21133 b21134 b21135 d21128
          omega
        have d21136 : (x 14 3 && x 14 14).toNat = 0 := by
          have r21137 := hand2 (x 14 3) (x 14 14)
          have b21138 := hb (x 14 14)
          have b21139 := hb (x 14 3 && x 14 14)
          clear * - r21137 b21138 b21139 d21128
          omega
        have d21140 : (x 14 2).toNat = 0 := by
          have r21141 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
          have b21142 := hb (x 14 2)
          have b21143 := hb (x 14 14)
          clear * - r21141 b21142 b21143 d21128
          omega
        have d21144 : (x 12 2).toNat = 0 := by
          have r21145 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
          have b21146 := hb (x 12 2)
          have b21147 := hb (x 12 14)
          clear * - r21145 b21146 b21147 d21111
          omega
        have d21148 : (x 10 2).toNat = 0 := by
          have r21149 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
          have b21150 := hb (x 10 2)
          have b21151 := hb (x 10 14)
          clear * - r21149 b21150 b21151 d21094
          omega
        have d21152 : (x 12 13).toNat = 1 := by
          have r21153 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21154 := hb (x 10 2)
          have b21155 := hb (x 12 13)
          have b21156 := hb (x 11 1 && x 11 14)
          clear * - r21153 b21154 b21155 b21156 d21069 d21148
          omega
        have d21157 : (x 12 1).toNat = 1 := by
          have r21158 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b21159 := hb (x 12 1)
          have b21160 := hb (x 12 13)
          clear * - r21158 b21159 b21160 d21152
          omega
        have d21161 : (x 13 14).toNat = 0 := by
          have r21162 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21163 := hb (x 12 1)
          have b21164 := hb (x 13 14)
          clear * - r21162 b21163 b21164 d21157
          omega
        have d21165 : (x 13 1 && x 13 14).toNat = 0 := by
          have r21166 := hand2 (x 13 1) (x 13 14)
          have b21167 := hb (x 13 14)
          have b21168 := hb (x 13 1 && x 13 14)
          clear * - r21166 b21167 b21168 d21161
          omega
        have d21169 : (x 14 13).toNat = 1 := by
          have r21170 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21171 := hb (x 12 2)
          have b21172 := hb (x 14 13)
          have b21173 := hb (x 13 1 && x 13 14)
          clear * - r21170 b21171 b21172 b21173 d21165 d21144
          omega
        have d21174 : (x 14 1).toNat = 1 := by
          have r21175 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
          have b21176 := hb (x 14 1)
          have b21177 := hb (x 14 13)
          clear * - r21175 b21176 b21177 d21169
          omega
        have d21178 : (x 15 14).toNat = 0 := by
          have r21179 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21180 := hb (x 14 1)
          have b21181 := hb (x 15 14)
          clear * - r21179 b21180 b21181 d21174
          omega
        have d21182 : (x 15 1 && x 15 14).toNat = 0 := by
          have r21183 := hand2 (x 15 1) (x 15 14)
          have b21184 := hb (x 15 14)
          have b21185 := hb (x 15 1 && x 15 14)
          clear * - r21183 b21184 b21185 d21178
          omega
        have d21186 : (x 16 13).toNat = 1 := by
          have r21187 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21188 := hb (x 14 2)
          have b21189 := hb (x 16 13)
          have b21190 := hb (x 15 1 && x 15 14)
          clear * - r21187 b21188 b21189 b21190 d21182 d21140
          omega
        have d21191 : (x 16 1).toNat = 1 := by
          have r21192 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
          have b21193 := hb (x 16 1)
          have b21194 := hb (x 16 13)
          clear * - r21192 b21193 b21194 d21186
          omega
        have d21195 : (x 17 14).toNat = 0 := by
          have r21196 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21197 := hb (x 16 1)
          have b21198 := hb (x 17 14)
          clear * - r21196 b21197 b21198 d21191
          omega
        have d21199 : (x 17 2).toNat = 0 := by
          have r21200 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
          have b21201 := hb (x 17 2)
          have b21202 := hb (x 17 14)
          clear * - r21200 b21201 b21202 d21195
          omega
        have d21203 : (x 15 2).toNat = 0 := by
          have r21204 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b21205 := hb (x 15 2)
          have b21206 := hb (x 15 14)
          clear * - r21204 b21205 b21206 d21178
          omega
        have d21207 : (x 15 2 && x 15 13).toNat = 0 := by
          have r21208 := hand1 (x 15 2) (x 15 13)
          have b21209 := hb (x 15 2)
          have b21210 := hb (x 15 2 && x 15 13)
          clear * - r21208 b21209 b21210 d21203
          omega
        have d21211 : (x 13 2).toNat = 0 := by
          have r21212 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b21213 := hb (x 13 2)
          have b21214 := hb (x 13 14)
          clear * - r21212 b21213 b21214 d21161
          omega
        have d21215 : (x 15 13).toNat = 1 := by
          have r21216 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21217 := hb (x 13 2)
          have b21218 := hb (x 15 13)
          have b21219 := hb (x 14 1 && x 14 14)
          clear * - r21216 b21217 b21218 b21219 d21132 d21211
          omega
        have d21220 : (x 15 1).toNat = 1 := by
          have r21221 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
          have b21222 := hb (x 15 1)
          have b21223 := hb (x 15 13)
          clear * - r21221 b21222 b21223 d21215
          omega
        have d21224 : (x 16 14).toNat = 0 := by
          have r21225 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21226 := hb (x 15 1)
          have b21227 := hb (x 16 14)
          clear * - r21225 b21226 b21227 d21220
          omega
        have d21228 : (x 16 1 && x 16 14).toNat = 0 := by
          have r21229 := hand2 (x 16 1) (x 16 14)
          have b21230 := hb (x 16 14)
          have b21231 := hb (x 16 1 && x 16 14)
          clear * - r21229 b21230 b21231 d21224
          omega
        have d21232 : (x 17 13).toNat = 1 := by
          have r21233 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21234 := hb (x 15 2)
          have b21235 := hb (x 17 13)
          have b21236 := hb (x 16 1 && x 16 14)
          clear * - r21233 b21234 b21235 b21236 d21228 d21203
          omega
        have d21237 : (x 17 1).toNat = 1 := by
          have r21238 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
          have b21239 := hb (x 17 1)
          have b21240 := hb (x 17 13)
          clear * - r21238 b21239 b21240 d21232
          omega
        have d21241 : (x 18 14).toNat = 0 := by
          have r21242 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21243 := hb (x 17 1)
          have b21244 := hb (x 18 14)
          clear * - r21242 b21243 b21244 d21237
          omega
        have d21245 : (x 18 1 && x 18 14).toNat = 0 := by
          have r21246 := hand2 (x 18 1) (x 18 14)
          have b21247 := hb (x 18 14)
          have b21248 := hb (x 18 1 && x 18 14)
          clear * - r21246 b21247 b21248 d21241
          omega
        have d21249 : (x 19 13).toNat = 1 := by
          have r21250 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21251 := hb (x 17 2)
          have b21252 := hb (x 19 13)
          have b21253 := hb (x 18 1 && x 18 14)
          clear * - r21250 b21251 b21252 b21253 d21245 d21199
          omega
        have d21254 : (x 18 2).toNat = 0 := by
          have r21255 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
          have b21256 := hb (x 18 2)
          have b21257 := hb (x 18 14)
          clear * - r21255 b21256 b21257 d21241
          omega
        have d21258 : (x 20 12).toNat = 0 := by
          have r21259 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21260 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e21261 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b21262 := hb (x 17 3)
          have b21263 := hb (x 18 2)
          have b21264 := hb (x 19 13)
          have b21265 := hb (x 20 12)
          clear * - r21259 e21260 e21261 b21262 b21263 b21264 b21265 d21249 d21254
          omega
        have d21266 : (x 17 3).toNat = 0 := by
          have r21267 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21268 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e21269 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b21270 := hb (x 17 3)
          have b21271 := hb (x 18 2)
          have b21272 := hb (x 19 13)
          have b21273 := hb (x 20 12)
          clear * - r21267 e21268 e21269 b21270 b21271 b21272 b21273 d21258 d21249 d21254
          omega
        have d21274 : (x 17 11).toNat = 0 := by
          have r21275 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b21276 := hb (x 17 3)
          have b21277 := hb (x 17 11)
          clear * - r21275 b21276 b21277 d21266
          omega
        have d21278 : (x 16 12).toNat = 0 := by
          have r21279 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21280 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e21281 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b21282 := hb (x 13 3)
          have b21283 := hb (x 14 2)
          have b21284 := hb (x 15 13)
          have b21285 := hb (x 16 12)
          clear * - r21279 e21280 e21281 b21282 b21283 b21284 b21285 d21215 d21140
          omega
        have d21286 : (x 16 1 && x 16 12).toNat = 0 := by
          have r21287 := hand2 (x 16 1) (x 16 12)
          have b21288 := hb (x 16 12)
          have b21289 := hb (x 16 1 && x 16 12)
          clear * - r21287 b21288 b21289 d21278
          omega
        have d21290 : (x 13 12).toNat = 0 := by
          have r21291 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21292 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e21293 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b21294 := hb (x 10 3)
          have b21295 := hb (x 11 2)
          have b21296 := hb (x 12 13)
          have b21297 := hb (x 13 12)
          clear * - r21291 e21292 e21293 b21294 b21295 b21296 b21297 d21152 d21073
          omega
        have d21298 : (x 13 4).toNat = 0 := by
          have r21299 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b21300 := hb (x 13 4)
          have b21301 := hb (x 13 12)
          clear * - r21299 b21300 b21301 d21290
          omega
        have r21302 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21303 := hb (x 13 4)
        have b21304 := hb (x 17 11)
        have b21305 := hb (x 16 1 && x 16 12)
        have b21306 := hb (x 15 2 && x 15 13)
        have b21307 := hb (x 14 3 && x 14 14)
        linarith only [r21302, b21303, b21304, b21305, b21306, b21307, d21274, d21286, d21207, d21136, d21298]
    · have f21308 : (x 0 12).toNat = 1 := by rw [h19748]; rfl
      have d21309 : (x (-2) 2).toNat = 0 := by
        have r21310 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21311 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e21312 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b21313 := hb (x (-3) 3)
        have b21314 := hb (x (-2) 2)
        have b21315 := hb (x (-1) 13)
        have b21316 := hb (x 0 12)
        clear * - r21310 e21311 e21312 b21313 b21314 b21315 b21316 f21308 g0
        omega
      have d21317 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
        have r21318 := hand1 (x (-2) 2) (x (-2) 13)
        have b21319 := hb (x (-2) 2)
        have b21320 := hb (x (-2) 2 && x (-2) 13)
        clear * - r21318 b21319 b21320 d21309
        omega
      have d21321 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
        have r21322 := hand1 (x (-2) 2) (x (-2) 12)
        have b21323 := hb (x (-2) 2)
        have b21324 := hb (x (-2) 2 && x (-2) 12)
        clear * - r21322 b21323 b21324 d21309
        omega
      have d21325 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
        have r21326 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21327 := hb (x (-2) 2)
        have b21328 := hb (x 0 13)
        have b21329 := hb (x (-1) 1 && x (-1) 14)
        clear * - r21326 b21327 b21328 b21329 g6 d21309
        omega
      have d21330 : (x (-1) 14).toNat = 1 := by
        have r21331 := hand2 (x (-1) 1) (x (-1) 14)
        have b21332 := hb (x (-1) 14)
        have b21333 := hb (x (-1) 1 && x (-1) 14)
        clear * - r21331 b21332 b21333 d21325
        omega
      have d21334 : (x (-2) 1).toNat = 0 := by
        have r21335 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21336 := hb (x (-2) 1)
        have b21337 := hb (x (-1) 14)
        clear * - r21335 b21336 b21337 d21330
        omega
      have d21338 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r21339 := hand1 (x (-2) 1) (x (-2) 14)
        have b21340 := hb (x (-2) 1)
        have b21341 := hb (x (-2) 1 && x (-2) 14)
        clear * - r21339 b21340 b21341 d21334
        omega
      have d21342 : (x (-3) 2).toNat = 1 := by
        have r21343 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21344 := hb (x (-3) 2)
        have b21345 := hb (x (-1) 13)
        have b21346 := hb (x (-2) 1 && x (-2) 14)
        clear * - r21343 b21344 b21345 b21346 g0 d21338
        omega
      have d21347 : (x (-3) 14).toNat = 1 := by
        have r21348 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b21349 := hb (x (-3) 2)
        have b21350 := hb (x (-3) 14)
        clear * - r21348 b21349 b21350 d21342
        omega
      have d21351 : (x (-4) 1).toNat = 0 := by
        have r21352 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21353 := hb (x (-4) 1)
        have b21354 := hb (x (-3) 14)
        clear * - r21352 b21353 b21354 d21347
        omega
      have d21355 : (x (-4) 13).toNat = 0 := by
        have r21356 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b21357 := hb (x (-4) 1)
        have b21358 := hb (x (-4) 13)
        clear * - r21356 b21357 b21358 d21351
        omega
      have d21359 : (x (-2) 13).toNat = 0 := by
        have r21360 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b21361 := hb (x (-2) 1)
        have b21362 := hb (x (-2) 13)
        clear * - r21360 b21361 b21362 d21334
        omega
      have d21363 : (x (-3) 3).toNat = 0 := by
        have r21364 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21365 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e21366 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b21367 := hb (x (-3) 3)
        have b21368 := hb (x (-2) 2)
        have b21369 := hb (x (-1) 13)
        have b21370 := hb (x 0 12)
        clear * - r21364 e21365 e21366 b21367 b21368 b21369 b21370 f21308 g0 d21309
        omega
      have d21371 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
        have r21372 := hand1 (x (-3) 3) (x (-3) 14)
        have b21373 := hb (x (-3) 3)
        have b21374 := hb (x (-3) 3 && x (-3) 14)
        clear * - r21372 b21373 b21374 d21363
        omega
      have d21375 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
        have r21376 := hand1 (x (-3) 3) (x (-3) 13)
        have b21377 := hb (x (-3) 3)
        have b21378 := hb (x (-3) 3 && x (-3) 13)
        clear * - r21376 b21377 b21378 d21363
        omega
      have d21379 : (x (-1) 12).toNat = 0 := by
        have r21380 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21381 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e21382 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b21383 := hb (x (-4) 3)
        have b21384 := hb (x (-3) 2)
        have b21385 := hb (x (-2) 13)
        have b21386 := hb (x (-1) 12)
        clear * - r21380 e21381 e21382 b21383 b21384 b21385 b21386 d21359 d21342
        omega
      have d21387 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
        have r21388 := hand2 (x (-1) 1) (x (-1) 12)
        have b21389 := hb (x (-1) 12)
        have b21390 := hb (x (-1) 1 && x (-1) 12)
        clear * - r21388 b21389 b21390 d21379
        omega
      have d21391 : (x (-4) 4).toNat = 1 := by
        have r21392 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21393 := hb (x (-4) 4)
        have b21394 := hb (x 0 11)
        have b21395 := hb (x (-1) 1 && x (-1) 12)
        have b21396 := hb (x (-2) 2 && x (-2) 13)
        have b21397 := hb (x (-3) 3 && x (-3) 14)
        clear * - r21392 b21393 b21394 b21395 b21396 b21397 g5 d21387 d21317 d21371
        omega
      have d21398 : (x (-4) 12).toNat = 1 := by
        have r21399 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have b21400 := hb (x (-4) 4)
        have b21401 := hb (x (-4) 12)
        clear * - r21399 b21400 b21401 d21391
        omega
      have d21402 : (x (-5) 13).toNat = 0 := by
        have r21403 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21404 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e21405 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b21406 := hb (x (-7) 3)
        have b21407 := hb (x (-6) 2)
        have b21408 := hb (x (-5) 13)
        have b21409 := hb (x (-4) 12)
        clear * - r21403 e21404 e21405 b21406 b21407 b21408 b21409 d21398
        omega
      have d21410 : (x (-5) 5).toNat = 0 := by
        have r21411 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
        have b21412 := hb (x (-5) 5)
        have b21413 := hb (x (-5) 13)
        clear * - r21411 b21412 b21413 d21402
        omega
      have d21414 : (x (-6) 2).toNat = 0 := by
        have r21415 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21416 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e21417 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b21418 := hb (x (-7) 3)
        have b21419 := hb (x (-6) 2)
        have b21420 := hb (x (-5) 13)
        have b21421 := hb (x (-4) 12)
        clear * - r21415 e21416 e21417 b21418 b21419 b21420 b21421 d21398 d21402
        omega
      have d21422 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
        have r21423 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21424 := hb (x (-6) 2)
        have b21425 := hb (x (-4) 13)
        have b21426 := hb (x (-5) 1 && x (-5) 14)
        clear * - r21423 b21424 b21425 b21426 d21355 d21414
        omega
      have d21427 : (x (-5) 1).toNat = 1 := by
        have r21428 := hand1 (x (-5) 1) (x (-5) 14)
        have b21429 := hb (x (-5) 1)
        have b21430 := hb (x (-5) 1 && x (-5) 14)
        clear * - r21428 b21429 b21430 d21422
        omega
      have d21431 : (x (-4) 14).toNat = 0 := by
        have r21432 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21433 := hb (x (-5) 1)
        have b21434 := hb (x (-4) 14)
        clear * - r21432 b21433 b21434 d21427
        omega
      have d21435 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
        have r21436 := hand2 (x (-4) 4) (x (-4) 14)
        have b21437 := hb (x (-4) 14)
        have b21438 := hb (x (-4) 4 && x (-4) 14)
        clear * - r21436 b21437 b21438 d21431
        omega
      have r21439 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b21440 := hb (x (-5) 5)
      have b21441 := hb (x 0 10)
      have b21442 := hb (x (-1) 1 && x (-1) 11)
      have b21443 := hb (x (-2) 2 && x (-2) 12)
      have b21444 := hb (x (-3) 3 && x (-3) 13)
      have b21445 := hb (x (-4) 4 && x (-4) 14)
      linarith only [r21439, b21440, b21441, b21442, b21443, b21444, b21445, g4, g11, d21321, d21375, d21435, d21410]
  · have f21446 : (x 0 9).toNat = 1 := by rw [h19746]; rfl
    have d21447 : (x 1 8).toNat = 0 := by
      have r21448 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e21449 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e21450 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e21451 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e21452 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e21453 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e21454 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b21455 := hb (x (-6) 7)
      have b21456 := hb (x (-5) 6)
      have b21457 := hb (x (-4) 5)
      have b21458 := hb (x (-3) 4)
      have b21459 := hb (x (-2) 11)
      have b21460 := hb (x (-1) 10)
      have b21461 := hb (x 0 9)
      have b21462 := hb (x 1 8)
      clear * - r21448 e21449 e21450 e21451 e21452 e21453 e21454 b21455 b21456 b21457 b21458 b21459 b21460 b21461 b21462 f21446
      omega
    have d21463 : (x (-1) 10).toNat = 0 := by
      have r21464 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e21465 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e21466 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e21467 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e21468 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e21469 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e21470 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b21471 := hb (x (-6) 7)
      have b21472 := hb (x (-5) 6)
      have b21473 := hb (x (-4) 5)
      have b21474 := hb (x (-3) 4)
      have b21475 := hb (x (-2) 11)
      have b21476 := hb (x (-1) 10)
      have b21477 := hb (x 0 9)
      have b21478 := hb (x 1 8)
      clear * - r21464 e21465 e21466 e21467 e21468 e21469 e21470 b21471 b21472 b21473 b21474 b21475 b21476 b21477 b21478 d21447 f21446
      omega
    have d21479 : (x (-2) 11).toNat = 0 := by
      have r21480 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e21481 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e21482 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e21483 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e21484 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e21485 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e21486 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b21487 := hb (x (-6) 7)
      have b21488 := hb (x (-5) 6)
      have b21489 := hb (x (-4) 5)
      have b21490 := hb (x (-3) 4)
      have b21491 := hb (x (-2) 11)
      have b21492 := hb (x (-1) 10)
      have b21493 := hb (x 0 9)
      have b21494 := hb (x 1 8)
      clear * - r21480 e21481 e21482 e21483 e21484 e21485 e21486 b21487 b21488 b21489 b21490 b21491 b21492 b21493 b21494 d21447 f21446 d21463
      omega
    have d21495 : (x (-3) 4).toNat = 0 := by
      have r21496 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e21497 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e21498 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e21499 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e21500 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e21501 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e21502 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b21503 := hb (x (-6) 7)
      have b21504 := hb (x (-5) 6)
      have b21505 := hb (x (-4) 5)
      have b21506 := hb (x (-3) 4)
      have b21507 := hb (x (-2) 11)
      have b21508 := hb (x (-1) 10)
      have b21509 := hb (x 0 9)
      have b21510 := hb (x 1 8)
      clear * - r21496 e21497 e21498 e21499 e21500 e21501 e21502 b21503 b21504 b21505 b21506 b21507 b21508 b21509 b21510 d21447 f21446 d21463 d21479
      omega
    have d21511 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
      have r21512 := hand1 (x (-3) 4) (x (-3) 14)
      have b21513 := hb (x (-3) 4)
      have b21514 := hb (x (-3) 4 && x (-3) 14)
      clear * - r21512 b21513 b21514 d21495
      omega
    have d21515 : (x (-4) 5).toNat = 0 := by
      have r21516 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e21517 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e21518 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e21519 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e21520 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e21521 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e21522 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b21523 := hb (x (-6) 7)
      have b21524 := hb (x (-5) 6)
      have b21525 := hb (x (-4) 5)
      have b21526 := hb (x (-3) 4)
      have b21527 := hb (x (-2) 11)
      have b21528 := hb (x (-1) 10)
      have b21529 := hb (x 0 9)
      have b21530 := hb (x 1 8)
      clear * - r21516 e21517 e21518 e21519 e21520 e21521 e21522 b21523 b21524 b21525 b21526 b21527 b21528 b21529 b21530 d21447 f21446 d21463 d21479 d21495
      omega
    have r21531 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21532 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e21533 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have r21534 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21535 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e21536 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have r21537 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21538 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e21539 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have r21540 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21541 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21542 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21543 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21544 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21545 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21546 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21547 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21548 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21549 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21550 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21551 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r21552 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have r21553 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have r21554 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have r21555 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have r21556 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have r21557 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have r21558 := hand2 (x (-1) 2) (x (-1) 12)
    have r21559 := hand2 (x (-2) 3) (x (-2) 13)
    have r21560 := hand1 (x 2 2) (x 2 13)
    have r21561 := hand1 (x (-2) 1) (x (-2) 14)
    have r21562 := hand2 (x 2 1) (x 2 14)
    have r21563 := hand2 (x 4 1) (x 4 14)
    have r21564 := hand2 (x 5 1) (x 5 14)
    linarith only [r21531, e21532, e21533, r21534, e21535, e21536, r21537, e21538, e21539, r21540, r21541, r21542, r21543, r21544, r21545, r21546, r21547, r21548, r21549, r21550, r21551, r21552, r21553, r21554, r21555, r21556, r21557, r21558, r21559, r21560, r21561, r21562, r21563, r21564, d21515, g0, g2, g7, g8, g9, g12, d21511, g15, g16, g17, g18]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 13).toNat = 0)
    (g1 : (x 0 1).toNat = 1)
    (g2 : (x 0 4).toNat = 0)
    (g3 : (x 0 5).toNat = 0)
    (g4 : (x 0 10).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 1 2).toNat = 0)
    (g8 : (x 1 10).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 10).toNat = 0)
    (g11 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g12 : (x 0 1 && x 0 11).toNat = 0)
    (g13 : (x 1 2 && x 1 12).toNat = 0)
    (g14 : (x 0 3 && x 0 13).toNat = 0)
    (g15 : (x 3 1 && x 3 12).toNat = 0)
    (g16 : (x 1 3 && x 1 14).toNat = 0)
    (g17 : (x 0 1 && x 0 14).toNat = 0)
    (g18 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18
