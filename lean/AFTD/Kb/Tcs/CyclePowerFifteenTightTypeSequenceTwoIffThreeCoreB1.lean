import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b1

Topic: combinatorics   Node: fa554c363e98

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 26 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b1_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 4).toNat = 1)
    (g1 : (x 0 5).toNat = 0)
    (g2 : (x 0 9).toNat = 0)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 1 10).toNat = 0)
    (g5 : (x 1 11).toNat = 0)
    (g6 : (x 2 5).toNat = 0)
    (g7 : (x 2 10).toNat = 0)
    (g8 : (x 3 4).toNat = 0)
    (g9 : (x 4 2).toNat = 0)
    (g10 : (x 4 10).toNat = 0)
    (g11 : (x 2 3 && x 2 10).toNat = 0)
    (g12 : (x 1 4 && x 1 11).toNat = 0)
    (g13 : (x 0 5 && x 0 12).toNat = 0)
    (g14 : (x 4 3 && x 4 10).toNat = 0)
    (g15 : (x 3 4 && x 3 11).toNat = 0)
    (g16 : (x 2 5 && x 2 12).toNat = 0)
    (g17 : (x 0 1 && x 0 11).toNat = 0)
    (g18 : (x 1 2 && x 1 12).toNat = 0)
    (g19 : (x 0 3 && x 0 13).toNat = 0)
    (g20 : (x 2 2 && x 2 12).toNat = 0)
    (g21 : (x 1 3 && x 1 13).toNat = 0)
    (g22 : (x 3 2 && x 3 12).toNat = 0)
    (g23 : (x 2 3 && x 2 13).toNat = 0)
    (g24 : (x 4 3 && x 4 14).toNat = 0)
    (g25 : (x 4 1 && x 4 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d767 : (x 0 12).toNat = 1 := by
    have r768 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b769 := hb (x 0 4)
    have b770 := hb (x 0 12)
    clear * - r768 b769 b770 g0
    omega
  have d771 : (x (-1) 13).toNat = 0 := by
    have r772 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e773 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e774 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b775 := hb (x (-3) 3)
    have b776 := hb (x (-2) 2)
    have b777 := hb (x (-1) 13)
    have b778 := hb (x 0 12)
    clear * - r772 e773 e774 b775 b776 b777 b778 d767
    omega
  have d779 : (x (-1) 6 && x (-1) 13).toNat = 0 := by
    have r780 := hand2 (x (-1) 6) (x (-1) 13)
    have b781 := hb (x (-1) 13)
    have b782 := hb (x (-1) 6 && x (-1) 13)
    clear * - r780 b781 b782 d771
    omega
  have d783 : (x (-1) 5).toNat = 0 := by
    have r784 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b785 := hb (x (-1) 5)
    have b786 := hb (x (-1) 13)
    clear * - r784 b785 b786 d771
    omega
  have d787 : (x (-2) 2).toNat = 0 := by
    have r788 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e789 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e790 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b791 := hb (x (-3) 3)
    have b792 := hb (x (-2) 2)
    have b793 := hb (x (-1) 13)
    have b794 := hb (x 0 12)
    clear * - r788 e789 e790 b791 b792 b793 b794 d767 d771
    omega
  have d795 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r796 := hand1 (x (-2) 2) (x (-2) 11)
    have b797 := hb (x (-2) 2)
    have b798 := hb (x (-2) 2 && x (-2) 11)
    clear * - r796 b797 b798 d787
    omega
  have d799 : (x (-2) 10).toNat = 0 := by
    have r800 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b801 := hb (x (-2) 2)
    have b802 := hb (x (-2) 10)
    clear * - r800 b801 b802 d787
    omega
  have d803 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r804 := hand2 (x (-2) 1) (x (-2) 10)
    have b805 := hb (x (-2) 10)
    have b806 := hb (x (-2) 1 && x (-2) 10)
    clear * - r804 b805 b806 d799
    omega
  have d807 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
    have r808 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b809 := hb (x (-2) 2)
    have b810 := hb (x 0 13)
    have b811 := hb (x (-1) 1 && x (-1) 14)
    clear * - r808 b809 b810 b811 g3 d787
    omega
  have d812 : (x (-1) 14).toNat = 1 := by
    have r813 := hand2 (x (-1) 1) (x (-1) 14)
    have b814 := hb (x (-1) 14)
    have b815 := hb (x (-1) 1 && x (-1) 14)
    clear * - r813 b814 b815 d807
    omega
  have d816 : (x (-2) 1).toNat = 0 := by
    have r817 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b818 := hb (x (-2) 1)
    have b819 := hb (x (-1) 14)
    clear * - r817 b818 b819 d812
    omega
  have d820 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r821 := hand1 (x (-2) 1) (x (-2) 14)
    have b822 := hb (x (-2) 1)
    have b823 := hb (x (-2) 1 && x (-2) 14)
    clear * - r821 b822 b823 d816
    omega
  have d824 : (x (-3) 2).toNat = 1 := by
    have r825 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b826 := hb (x (-3) 2)
    have b827 := hb (x (-1) 13)
    have b828 := hb (x (-2) 1 && x (-2) 14)
    clear * - r825 b826 b827 b828 d771 d820
    omega
  have d829 : (x (-3) 14).toNat = 1 := by
    have r830 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b831 := hb (x (-3) 2)
    have b832 := hb (x (-3) 14)
    clear * - r830 b831 b832 d824
    omega
  have d833 : (x (-4) 1).toNat = 0 := by
    have r834 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b835 := hb (x (-4) 1)
    have b836 := hb (x (-3) 14)
    clear * - r834 b835 b836 d829
    omega
  have d837 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r838 := hand1 (x (-4) 1) (x (-4) 14)
    have b839 := hb (x (-4) 1)
    have b840 := hb (x (-4) 1 && x (-4) 14)
    clear * - r838 b839 b840 d833
    omega
  have d841 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
    have r842 := hand1 (x (-4) 1) (x (-4) 12)
    have b843 := hb (x (-4) 1)
    have b844 := hb (x (-4) 1 && x (-4) 12)
    clear * - r842 b843 b844 d833
    omega
  have d845 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
    have r846 := hand1 (x (-4) 1) (x (-4) 11)
    have b847 := hb (x (-4) 1)
    have b848 := hb (x (-4) 1 && x (-4) 11)
    clear * - r846 b847 b848 d833
    omega
  have d849 : (x (-4) 13).toNat = 0 := by
    have r850 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b851 := hb (x (-4) 1)
    have b852 := hb (x (-4) 13)
    clear * - r850 b851 b852 d833
    omega
  have d853 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
    have r854 := hand2 (x (-4) 4) (x (-4) 13)
    have b855 := hb (x (-4) 13)
    have b856 := hb (x (-4) 4 && x (-4) 13)
    clear * - r854 b855 b856 d849
    omega
  have d857 : (x (-4) 5).toNat = 0 := by
    have r858 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b859 := hb (x (-4) 5)
    have b860 := hb (x (-4) 13)
    clear * - r858 b859 b860 d849
    omega
  have d861 : (x (-4) 9).toNat = 0 := by
    have r862 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
    have b863 := hb (x (-4) 1)
    have b864 := hb (x (-4) 9)
    clear * - r862 b863 b864 d833
    omega
  have d865 : (x (-2) 13).toNat = 0 := by
    have r866 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b867 := hb (x (-2) 1)
    have b868 := hb (x (-2) 13)
    clear * - r866 b867 b868 d816
    omega
  have d869 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r870 := hand2 (x (-2) 3) (x (-2) 13)
    have b871 := hb (x (-2) 13)
    have b872 := hb (x (-2) 3 && x (-2) 13)
    clear * - r870 b871 b872 d865
    omega
  have d873 : (x (-2) 5).toNat = 0 := by
    have r874 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b875 := hb (x (-2) 5)
    have b876 := hb (x (-2) 13)
    clear * - r874 b875 b876 d865
    omega
  have d877 : (x (-2) 9).toNat = 0 := by
    have r878 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
    have b879 := hb (x (-2) 1)
    have b880 := hb (x (-2) 9)
    clear * - r878 b879 b880 d816
    omega
  have d881 : (x (-1) 1).toNat = 1 := by
    have r882 := hand1 (x (-1) 1) (x (-1) 14)
    have b883 := hb (x (-1) 1)
    have b884 := hb (x (-1) 1 && x (-1) 14)
    clear * - r882 b883 b884 d807
    omega
  have d885 : (x 0 14).toNat = 0 := by
    have r886 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b887 := hb (x (-1) 1)
    have b888 := hb (x 0 14)
    clear * - r886 b887 b888 d881
    omega
  have d889 : (x 0 4 && x 0 14).toNat = 0 := by
    have r890 := hand2 (x 0 4) (x 0 14)
    have b891 := hb (x 0 14)
    have b892 := hb (x 0 4 && x 0 14)
    clear * - r890 b891 b892 d885
    omega
  have d893 : (x 0 7 && x 0 14).toNat = 0 := by
    have r894 := hand2 (x 0 7) (x 0 14)
    have b895 := hb (x 0 14)
    have b896 := hb (x 0 7 && x 0 14)
    clear * - r894 b895 b896 d885
    omega
  have d897 : (x 0 6).toNat = 0 := by
    have r898 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
    have b899 := hb (x 0 6)
    have b900 := hb (x 0 14)
    clear * - r898 b899 b900 d885
    omega
  have d901 : (x (-3) 3).toNat = 0 := by
    have r902 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e903 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e904 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b905 := hb (x (-3) 3)
    have b906 := hb (x (-2) 2)
    have b907 := hb (x (-1) 13)
    have b908 := hb (x 0 12)
    clear * - r902 e903 e904 b905 b906 b907 b908 d767 d771 d787
    omega
  have d909 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
    have r910 := hand1 (x (-3) 3) (x (-3) 12)
    have b911 := hb (x (-3) 3)
    have b912 := hb (x (-3) 3 && x (-3) 12)
    clear * - r910 b911 b912 d901
    omega
  have d913 : (x (-3) 11).toNat = 0 := by
    have r914 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b915 := hb (x (-3) 3)
    have b916 := hb (x (-3) 11)
    clear * - r914 b915 b916 d901
    omega
  have d917 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r918 := hand2 (x (-3) 2) (x (-3) 11)
    have b919 := hb (x (-3) 11)
    have b920 := hb (x (-3) 2 && x (-3) 11)
    clear * - r918 b919 b920 d913
    omega
  have d921 : (x (-1) 12).toNat = 0 := by
    have r922 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e923 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e924 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b925 := hb (x (-4) 3)
    have b926 := hb (x (-3) 2)
    have b927 := hb (x (-2) 13)
    have b928 := hb (x (-1) 12)
    clear * - r922 e923 e924 b925 b926 b927 b928 d865 d824
    omega
  have d929 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r930 := hand2 (x (-1) 2) (x (-1) 12)
    have b931 := hb (x (-1) 12)
    have b932 := hb (x (-1) 2 && x (-1) 12)
    clear * - r930 b931 b932 d921
    omega
  have d933 : (x (-1) 4).toNat = 0 := by
    have r934 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b935 := hb (x (-1) 4)
    have b936 := hb (x (-1) 12)
    clear * - r934 b935 b936 d921
    omega
  have d937 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
    have r938 := hand1 (x (-1) 4) (x (-1) 14)
    have b939 := hb (x (-1) 4)
    have b940 := hb (x (-1) 4 && x (-1) 14)
    clear * - r938 b939 b940 d933
    omega
  have d941 : (x (-4) 3).toNat = 0 := by
    have r942 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e943 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e944 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b945 := hb (x (-4) 3)
    have b946 := hb (x (-3) 2)
    have b947 := hb (x (-2) 13)
    have b948 := hb (x (-1) 12)
    clear * - r942 e943 e944 b945 b946 b947 b948 d921 d865 d824
    omega
  have d949 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
    have r950 := hand1 (x (-4) 3) (x (-4) 12)
    have b951 := hb (x (-4) 3)
    have b952 := hb (x (-4) 3 && x (-4) 12)
    clear * - r950 b951 b952 d941
    omega
  have d953 : (x (-4) 11).toNat = 0 := by
    have r954 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b955 := hb (x (-4) 3)
    have b956 := hb (x (-4) 11)
    clear * - r954 b955 b956 d941
    omega
  have d957 : (x 3 1 && x 3 11).toNat = 1 := by
    have r958 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b959 := hb (x (-1) 5)
    have b960 := hb (x 4 10)
    have b961 := hb (x 3 1 && x 3 11)
    have b962 := hb (x 2 2 && x 2 12)
    have b963 := hb (x 1 3 && x 1 13)
    have b964 := hb (x 0 4 && x 0 14)
    clear * - r958 b959 b960 b961 b962 b963 b964 g10 g20 g21 d889 d783
    omega
  have d965 : (x 3 11).toNat = 1 := by
    have r966 := hand2 (x 3 1) (x 3 11)
    have b967 := hb (x 3 11)
    have b968 := hb (x 3 1 && x 3 11)
    clear * - r966 b967 b968 d957
    omega
  have d969 : (x 3 3).toNat = 1 := by
    have r970 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b971 := hb (x 3 3)
    have b972 := hb (x 3 11)
    clear * - r970 b971 b972 d965
    omega
  have d973 : (x 6 12).toNat = 0 := by
    have r974 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e975 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e976 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b977 := hb (x 3 3)
    have b978 := hb (x 4 2)
    have b979 := hb (x 5 13)
    have b980 := hb (x 6 12)
    clear * - r974 e975 e976 b977 b978 b979 b980 g9 d969
    omega
  have d981 : (x 6 1 && x 6 12).toNat = 0 := by
    have r982 := hand2 (x 6 1) (x 6 12)
    have b983 := hb (x 6 12)
    have b984 := hb (x 6 1 && x 6 12)
    clear * - r982 b983 b984 d973
    omega
  have d985 : (x 6 4).toNat = 0 := by
    have r986 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b987 := hb (x 6 4)
    have b988 := hb (x 6 12)
    clear * - r986 b987 b988 d973
    omega
  have d989 : (x 6 4 && x 6 14).toNat = 0 := by
    have r990 := hand1 (x 6 4) (x 6 14)
    have b991 := hb (x 6 4)
    have b992 := hb (x 6 4 && x 6 14)
    clear * - r990 b991 b992 d985
    omega
  have d993 : (x 5 13).toNat = 0 := by
    have r994 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e995 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e996 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b997 := hb (x 3 3)
    have b998 := hb (x 4 2)
    have b999 := hb (x 5 13)
    have b1000 := hb (x 6 12)
    clear * - r994 e995 e996 b997 b998 b999 b1000 d973 g9 d969
    omega
  have d1001 : (x 5 2 && x 5 13).toNat = 0 := by
    have r1002 := hand2 (x 5 2) (x 5 13)
    have b1003 := hb (x 5 13)
    have b1004 := hb (x 5 2 && x 5 13)
    clear * - r1002 b1003 b1004 d993
    omega
  have d1005 : (x 7 11).toNat = 1 := by
    have r1006 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1007 := hb (x 3 4)
    have b1008 := hb (x 7 11)
    have b1009 := hb (x 6 1 && x 6 12)
    have b1010 := hb (x 5 2 && x 5 13)
    have b1011 := hb (x 4 3 && x 4 14)
    clear * - r1006 b1007 b1008 b1009 b1010 b1011 d981 d1001 g24 g8
    omega
  have d1012 : (x 7 3).toNat = 1 := by
    have r1013 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b1014 := hb (x 7 3)
    have b1015 := hb (x 7 11)
    clear * - r1013 b1014 b1015 d1005
    omega
  have d1016 : (x 10 12).toNat = 0 := by
    have r1017 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1018 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e1019 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b1020 := hb (x 7 3)
    have b1021 := hb (x 8 2)
    have b1022 := hb (x 9 13)
    have b1023 := hb (x 10 12)
    clear * - r1017 e1018 e1019 b1020 b1021 b1022 b1023 d1012
    omega
  have d1024 : (x 10 1 && x 10 12).toNat = 0 := by
    have r1025 := hand2 (x 10 1) (x 10 12)
    have b1026 := hb (x 10 12)
    have b1027 := hb (x 10 1 && x 10 12)
    clear * - r1025 b1026 b1027 d1016
    omega
  have d1028 : (x 10 4).toNat = 0 := by
    have r1029 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have b1030 := hb (x 10 4)
    have b1031 := hb (x 10 12)
    clear * - r1029 b1030 b1031 d1016
    omega
  have d1032 : (x 9 13).toNat = 0 := by
    have r1033 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1034 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e1035 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b1036 := hb (x 7 3)
    have b1037 := hb (x 8 2)
    have b1038 := hb (x 9 13)
    have b1039 := hb (x 10 12)
    clear * - r1033 e1034 e1035 b1036 b1037 b1038 b1039 d1016 d1012
    omega
  have d1040 : (x 9 2 && x 9 13).toNat = 0 := by
    have r1041 := hand2 (x 9 2) (x 9 13)
    have b1042 := hb (x 9 13)
    have b1043 := hb (x 9 2 && x 9 13)
    clear * - r1041 b1042 b1043 d1032
    omega
  have d1044 : (x 9 5).toNat = 0 := by
    have r1045 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
    have b1046 := hb (x 9 5)
    have b1047 := hb (x 9 13)
    clear * - r1045 b1046 b1047 d1032
    omega
  have d1048 : (x 8 2).toNat = 0 := by
    have r1049 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1050 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e1051 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b1052 := hb (x 7 3)
    have b1053 := hb (x 8 2)
    have b1054 := hb (x 9 13)
    have b1055 := hb (x 10 12)
    clear * - r1049 e1050 e1051 b1052 b1053 b1054 b1055 d1016 d1032 d1012
    omega
  have d1056 : (x 8 2 && x 8 12).toNat = 0 := by
    have r1057 := hand1 (x 8 2) (x 8 12)
    have b1058 := hb (x 8 2)
    have b1059 := hb (x 8 2 && x 8 12)
    clear * - r1057 b1058 b1059 d1048
    omega
  have d1060 : (x 5 5).toNat = 0 := by
    have r1061 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b1062 := hb (x 5 5)
    have b1063 := hb (x 5 13)
    clear * - r1061 b1062 b1063 d993
    omega
  have d1064 : (x 3 2).toNat = 1 := by
    have r1065 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1066 := hb (x 3 2)
    have b1067 := hb (x 5 13)
    have b1068 := hb (x 4 1 && x 4 14)
    clear * - r1065 b1066 b1067 b1068 d993 g25
    omega
  have d1069 : (x 3 14).toNat = 1 := by
    have r1070 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b1071 := hb (x 3 2)
    have b1072 := hb (x 3 14)
    clear * - r1070 b1071 b1072 d1064
    omega
  have d1073 : (x 2 1).toNat = 0 := by
    have r1074 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1075 := hb (x 2 1)
    have b1076 := hb (x 3 14)
    clear * - r1074 b1075 b1076 d1069
    omega
  have d1077 : (x 2 1 && x 2 11).toNat = 0 := by
    have r1078 := hand1 (x 2 1) (x 2 11)
    have b1079 := hb (x 2 1)
    have b1080 := hb (x 2 1 && x 2 11)
    clear * - r1078 b1079 b1080 d1073
    omega
  have d1081 : (x 5 12).toNat = 0 := by
    have r1082 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1083 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e1084 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b1085 := hb (x 2 3)
    have b1086 := hb (x 3 2)
    have b1087 := hb (x 4 13)
    have b1088 := hb (x 5 12)
    clear * - r1082 e1083 e1084 b1085 b1086 b1087 b1088 d1064
    omega
  have d1089 : (x 4 13).toNat = 0 := by
    have r1090 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1091 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e1092 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b1093 := hb (x 2 3)
    have b1094 := hb (x 3 2)
    have b1095 := hb (x 4 13)
    have b1096 := hb (x 5 12)
    clear * - r1090 e1091 e1092 b1093 b1094 b1095 b1096 d1081 d1064
    omega
  have d1097 : (x 2 3).toNat = 0 := by
    have r1098 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1099 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e1100 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b1101 := hb (x 2 3)
    have b1102 := hb (x 3 2)
    have b1103 := hb (x 4 13)
    have b1104 := hb (x 5 12)
    clear * - r1098 e1099 e1100 b1101 b1102 b1103 b1104 d1081 d1089 d1064
    omega
  have d1105 : (x 2 11).toNat = 0 := by
    have r1106 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b1107 := hb (x 2 3)
    have b1108 := hb (x 2 11)
    clear * - r1106 b1107 b1108 d1097
    omega
  have d1109 : (x 3 10).toNat = 1 := by
    have r1110 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1111 := hb (x (-2) 5)
    have b1112 := hb (x 3 10)
    have b1113 := hb (x 2 1 && x 2 11)
    have b1114 := hb (x 1 2 && x 1 12)
    have b1115 := hb (x 0 3 && x 0 13)
    have b1116 := hb (x (-1) 4 && x (-1) 14)
    clear * - r1110 b1111 b1112 b1113 b1114 b1115 b1116 d1077 g18 g19 d937 d873
    omega
  have d1117 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r1118 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1119 := hb (x (-4) 5)
    have b1120 := hb (x 1 10)
    have b1121 := hb (x 0 1 && x 0 11)
    have b1122 := hb (x (-1) 2 && x (-1) 12)
    have b1123 := hb (x (-2) 3 && x (-2) 13)
    have b1124 := hb (x (-3) 4 && x (-3) 14)
    clear * - r1118 b1119 b1120 b1121 b1122 b1123 b1124 g4 g17 d929 d869 d857
    omega
  have d1125 : (x (-3) 4).toNat = 1 := by
    have r1126 := hand1 (x (-3) 4) (x (-3) 14)
    have b1127 := hb (x (-3) 4)
    have b1128 := hb (x (-3) 4 && x (-3) 14)
    clear * - r1126 b1127 b1128 d1117
    omega
  have d1129 : (x (-3) 12).toNat = 1 := by
    have r1130 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b1131 := hb (x (-3) 4)
    have b1132 := hb (x (-3) 12)
    clear * - r1130 b1131 b1132 d1125
    omega
  have d1133 : (x (-5) 2).toNat = 0 := by
    have r1134 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1135 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e1136 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b1137 := hb (x (-6) 3)
    have b1138 := hb (x (-5) 2)
    have b1139 := hb (x (-4) 13)
    have b1140 := hb (x (-3) 12)
    clear * - r1134 e1135 e1136 b1137 b1138 b1139 b1140 d1129 d849
    omega
  have d1141 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
    have r1142 := hand1 (x (-5) 2) (x (-5) 13)
    have b1143 := hb (x (-5) 2)
    have b1144 := hb (x (-5) 2 && x (-5) 13)
    clear * - r1142 b1143 b1144 d1133
    omega
  have d1145 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
    have r1146 := hand1 (x (-5) 2) (x (-5) 12)
    have b1147 := hb (x (-5) 2)
    have b1148 := hb (x (-5) 2 && x (-5) 12)
    clear * - r1146 b1147 b1148 d1133
    omega
  have d1149 : (x (-5) 10).toNat = 0 := by
    have r1150 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b1151 := hb (x (-5) 2)
    have b1152 := hb (x (-5) 10)
    clear * - r1150 b1151 b1152 d1133
    omega
  have d1153 : (x (-3) 13).toNat = 1 := by
    have r1154 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1155 := hb (x (-5) 2)
    have b1156 := hb (x (-3) 13)
    have b1157 := hb (x (-4) 1 && x (-4) 14)
    clear * - r1154 b1155 b1156 b1157 d837 d1133
    omega
  have d1158 : (x (-3) 1).toNat = 1 := by
    have r1159 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b1160 := hb (x (-3) 1)
    have b1161 := hb (x (-3) 13)
    clear * - r1159 b1160 b1161 d1153
    omega
  have d1162 : (x (-2) 14).toNat = 0 := by
    have r1163 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1164 := hb (x (-3) 1)
    have b1165 := hb (x (-2) 14)
    clear * - r1163 b1164 b1165 d1158
    omega
  have d1166 : (x (-2) 7 && x (-2) 14).toNat = 0 := by
    have r1167 := hand2 (x (-2) 7) (x (-2) 14)
    have b1168 := hb (x (-2) 14)
    have b1169 := hb (x (-2) 7 && x (-2) 14)
    clear * - r1167 b1168 b1169 d1162
    omega
  have d1170 : (x (-2) 6).toNat = 0 := by
    have r1171 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b1172 := hb (x (-2) 6)
    have b1173 := hb (x (-2) 14)
    clear * - r1171 b1172 b1173 d1162
    omega
  have d1174 : (x (-6) 3).toNat = 0 := by
    have r1175 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1176 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e1177 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b1178 := hb (x (-6) 3)
    have b1179 := hb (x (-5) 2)
    have b1180 := hb (x (-4) 13)
    have b1181 := hb (x (-3) 12)
    clear * - r1175 e1176 e1177 b1178 b1179 b1180 b1181 d1129 d849 d1133
    omega
  have d1182 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
    have r1183 := hand1 (x (-6) 3) (x (-6) 14)
    have b1184 := hb (x (-6) 3)
    have b1185 := hb (x (-6) 3 && x (-6) 14)
    clear * - r1183 b1184 b1185 d1174
    omega
  have d1186 : (x (-7) 4).toNat = 1 := by
    have r1187 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1188 := hb (x (-7) 4)
    have b1189 := hb (x (-3) 11)
    have b1190 := hb (x (-4) 1 && x (-4) 12)
    have b1191 := hb (x (-5) 2 && x (-5) 13)
    have b1192 := hb (x (-6) 3 && x (-6) 14)
    clear * - r1187 b1188 b1189 b1190 b1191 b1192 d913 d841 d1141 d1182
    omega
  have d1193 : (x (-7) 12).toNat = 1 := by
    have r1194 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
    have b1195 := hb (x (-7) 4)
    have b1196 := hb (x (-7) 12)
    clear * - r1194 b1195 b1196 d1186
    omega
  have d1197 : (x (-8) 13).toNat = 0 := by
    have r1198 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1199 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e1200 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b1201 := hb (x (-10) 3)
    have b1202 := hb (x (-9) 2)
    have b1203 := hb (x (-8) 13)
    have b1204 := hb (x (-7) 12)
    clear * - r1198 e1199 e1200 b1201 b1202 b1203 b1204 d1193
    omega
  have d1205 : (x (-8) 5).toNat = 0 := by
    have r1206 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
    have b1207 := hb (x (-8) 5)
    have b1208 := hb (x (-8) 13)
    clear * - r1206 b1207 b1208 d1197
    omega
  have d1209 : (x (-9) 2).toNat = 0 := by
    have r1210 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1211 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e1212 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b1213 := hb (x (-10) 3)
    have b1214 := hb (x (-9) 2)
    have b1215 := hb (x (-8) 13)
    have b1216 := hb (x (-7) 12)
    clear * - r1210 e1211 e1212 b1213 b1214 b1215 b1216 d1193 d1197
    omega
  have d1217 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
    have r1218 := hand1 (x (-6) 3) (x (-6) 13)
    have b1219 := hb (x (-6) 3)
    have b1220 := hb (x (-6) 3 && x (-6) 13)
    clear * - r1218 b1219 b1220 d1174
    omega
  have d1221 : (x (-6) 11).toNat = 0 := by
    have r1222 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
    have b1223 := hb (x (-6) 3)
    have b1224 := hb (x (-6) 11)
    clear * - r1222 b1223 b1224 d1174
    omega
  have d1225 : (x 6 8).toNat = 0 := by
    have r1226 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1227 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e1228 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e1229 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e1230 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e1231 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e1232 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b1233 := hb (x (-1) 7)
    have b1234 := hb (x 0 6)
    have b1235 := hb (x 1 5)
    have b1236 := hb (x 2 4)
    have b1237 := hb (x 3 11)
    have b1238 := hb (x 4 10)
    have b1239 := hb (x 5 9)
    have b1240 := hb (x 6 8)
    clear * - r1226 e1227 e1228 e1229 e1230 e1231 e1232 b1233 b1234 b1235 b1236 b1237 b1238 b1239 b1240 g10 d965 d897
    omega
  have d1241 : (x 6 1 && x 6 8).toNat = 0 := by
    have r1242 := hand2 (x 6 1) (x 6 8)
    have b1243 := hb (x 6 8)
    have b1244 := hb (x 6 1 && x 6 8)
    clear * - r1242 b1243 b1244 d1225
    omega
  have d1245 : (x 5 9).toNat = 0 := by
    have r1246 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1247 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e1248 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e1249 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e1250 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e1251 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e1252 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b1253 := hb (x (-1) 7)
    have b1254 := hb (x 0 6)
    have b1255 := hb (x 1 5)
    have b1256 := hb (x 2 4)
    have b1257 := hb (x 3 11)
    have b1258 := hb (x 4 10)
    have b1259 := hb (x 5 9)
    have b1260 := hb (x 6 8)
    clear * - r1246 e1247 e1248 e1249 e1250 e1251 e1252 b1253 b1254 b1255 b1256 b1257 b1258 b1259 b1260 d1225 g10 d965 d897
    omega
  have d1261 : (x 5 2 && x 5 9).toNat = 0 := by
    have r1262 := hand2 (x 5 2) (x 5 9)
    have b1263 := hb (x 5 9)
    have b1264 := hb (x 5 2 && x 5 9)
    clear * - r1262 b1263 b1264 d1245
    omega
  have d1265 : (x 5 8).toNat = 0 := by
    have r1266 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1267 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e1268 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e1269 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e1270 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e1271 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e1272 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b1273 := hb (x (-2) 7)
    have b1274 := hb (x (-1) 6)
    have b1275 := hb (x 0 5)
    have b1276 := hb (x 1 4)
    have b1277 := hb (x 2 11)
    have b1278 := hb (x 3 10)
    have b1279 := hb (x 4 9)
    have b1280 := hb (x 5 8)
    clear * - r1266 e1267 e1268 e1269 e1270 e1271 e1272 b1273 b1274 b1275 b1276 b1277 b1278 b1279 b1280 d1109 d1105 g1
    omega
  have d1281 : (x 4 9).toNat = 0 := by
    have r1282 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1283 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e1284 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e1285 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e1286 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e1287 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e1288 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b1289 := hb (x (-2) 7)
    have b1290 := hb (x (-1) 6)
    have b1291 := hb (x 0 5)
    have b1292 := hb (x 1 4)
    have b1293 := hb (x 2 11)
    have b1294 := hb (x 3 10)
    have b1295 := hb (x 4 9)
    have b1296 := hb (x 5 8)
    clear * - r1282 e1283 e1284 e1285 e1286 e1287 e1288 b1289 b1290 b1291 b1292 b1293 b1294 b1295 b1296 d1265 d1109 d1105 g1
    omega
  have d1297 : (x 1 4).toNat = 0 := by
    have r1298 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1299 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e1300 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e1301 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e1302 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e1303 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e1304 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b1305 := hb (x (-2) 7)
    have b1306 := hb (x (-1) 6)
    have b1307 := hb (x 0 5)
    have b1308 := hb (x 1 4)
    have b1309 := hb (x 2 11)
    have b1310 := hb (x 3 10)
    have b1311 := hb (x 4 9)
    have b1312 := hb (x 5 8)
    clear * - r1298 e1299 e1300 e1301 e1302 e1303 e1304 b1305 b1306 b1307 b1308 b1309 b1310 b1311 b1312 d1265 d1281 d1109 d1105 g1
    omega
  have d1313 : (x 1 4 && x 1 14).toNat = 0 := by
    have r1314 := hand1 (x 1 4) (x 1 14)
    have b1315 := hb (x 1 4)
    have b1316 := hb (x 1 4 && x 1 14)
    clear * - r1314 b1315 b1316 d1297
    omega
  have d1317 : (x 4 8).toNat = 0 := by
    have r1318 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1319 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e1320 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e1321 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e1322 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e1323 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e1324 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b1325 := hb (x (-3) 7)
    have b1326 := hb (x (-2) 6)
    have b1327 := hb (x (-1) 5)
    have b1328 := hb (x 0 4)
    have b1329 := hb (x 1 11)
    have b1330 := hb (x 2 10)
    have b1331 := hb (x 3 9)
    have b1332 := hb (x 4 8)
    clear * - r1318 e1319 e1320 e1321 e1322 e1323 e1324 b1325 b1326 b1327 b1328 b1329 b1330 b1331 b1332 g7 g5 g0 d783 d1170
    omega
  have d1333 : (x 4 1 && x 4 8).toNat = 0 := by
    have r1334 := hand2 (x 4 1) (x 4 8)
    have b1335 := hb (x 4 8)
    have b1336 := hb (x 4 1 && x 4 8)
    clear * - r1334 b1335 b1336 d1317
    omega
  have d1337 : (x 3 9).toNat = 0 := by
    have r1338 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1339 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e1340 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e1341 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e1342 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e1343 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e1344 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b1345 := hb (x (-3) 7)
    have b1346 := hb (x (-2) 6)
    have b1347 := hb (x (-1) 5)
    have b1348 := hb (x 0 4)
    have b1349 := hb (x 1 11)
    have b1350 := hb (x 2 10)
    have b1351 := hb (x 3 9)
    have b1352 := hb (x 4 8)
    clear * - r1338 e1339 e1340 e1341 e1342 e1343 e1344 b1345 b1346 b1347 b1348 b1349 b1350 b1351 b1352 d1317 g7 g5 g0 d783 d1170
    omega
  have d1353 : (x 3 2 && x 3 9).toNat = 0 := by
    have r1354 := hand2 (x 3 2) (x 3 9)
    have b1355 := hb (x 3 9)
    have b1356 := hb (x 3 2 && x 3 9)
    clear * - r1354 b1355 b1356 d1337
    omega
  have d1357 : (x 1 8).toNat = 0 := by
    have r1358 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1359 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e1360 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e1361 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e1362 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e1363 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e1364 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b1365 := hb (x (-6) 7)
    have b1366 := hb (x (-5) 6)
    have b1367 := hb (x (-4) 5)
    have b1368 := hb (x (-3) 4)
    have b1369 := hb (x (-2) 11)
    have b1370 := hb (x (-1) 10)
    have b1371 := hb (x 0 9)
    have b1372 := hb (x 1 8)
    clear * - r1358 e1359 e1360 e1361 e1362 e1363 e1364 b1365 b1366 b1367 b1368 b1369 b1370 b1371 b1372 g2 d1125 d857
    omega
  have d1373 : (x (-1) 10).toNat = 0 := by
    have r1374 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1375 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e1376 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e1377 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e1378 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e1379 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e1380 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b1381 := hb (x (-6) 7)
    have b1382 := hb (x (-5) 6)
    have b1383 := hb (x (-4) 5)
    have b1384 := hb (x (-3) 4)
    have b1385 := hb (x (-2) 11)
    have b1386 := hb (x (-1) 10)
    have b1387 := hb (x 0 9)
    have b1388 := hb (x 1 8)
    clear * - r1374 e1375 e1376 e1377 e1378 e1379 e1380 b1381 b1382 b1383 b1384 b1385 b1386 b1387 b1388 d1357 g2 d1125 d857
    omega
  have d1389 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
    have r1390 := hand2 (x (-1) 1) (x (-1) 10)
    have b1391 := hb (x (-1) 10)
    have b1392 := hb (x (-1) 1 && x (-1) 10)
    clear * - r1390 b1391 b1392 d1373
    omega
  have d1393 : (x (-3) 8).toNat = 0 := by
    have r1394 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1395 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
    have e1396 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
    have e1397 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
    have e1398 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
    have e1399 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
    have e1400 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
    have b1401 := hb (x (-10) 7)
    have b1402 := hb (x (-9) 6)
    have b1403 := hb (x (-8) 5)
    have b1404 := hb (x (-7) 4)
    have b1405 := hb (x (-6) 11)
    have b1406 := hb (x (-5) 10)
    have b1407 := hb (x (-4) 9)
    have b1408 := hb (x (-3) 8)
    clear * - r1394 e1395 e1396 e1397 e1398 e1399 e1400 b1401 b1402 b1403 b1404 b1405 b1406 b1407 b1408 d861 d1149 d1221 d1186 d1205
    omega
  have d1409 : (x 5 7).toNat = 1 := by
    have r1410 : 1 ≤ (x 5 7).toNat + (x 4 1 && x 4 8).toNat + (x 3 2 && x 3 9).toNat + (x 2 3 && x 2 10).toNat + (x 1 4 && x 1 11).toNat + (x 0 5 && x 0 12).toNat + (x (-1) 6 && x (-1) 13).toNat + (x (-2) 7 && x (-2) 14).toNat + (x (-3) 8).toNat := by have q := hcov7 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1411 := hb (x (-3) 8)
    have b1412 := hb (x 5 7)
    have b1413 := hb (x 4 1 && x 4 8)
    have b1414 := hb (x 3 2 && x 3 9)
    have b1415 := hb (x 2 3 && x 2 10)
    have b1416 := hb (x 1 4 && x 1 11)
    have b1417 := hb (x 0 5 && x 0 12)
    have b1418 := hb (x (-1) 6 && x (-1) 13)
    have b1419 := hb (x (-2) 7 && x (-2) 14)
    clear * - r1410 b1411 b1412 b1413 b1414 b1415 b1416 b1417 b1418 b1419 d1333 d1353 g11 g12 g13 d779 d1166 d1393
    omega
  have d1420 : (x 12 8).toNat = 0 := by
    have r1421 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1422 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e1423 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e1424 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e1425 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e1426 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e1427 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b1428 := hb (x 5 7)
    have b1429 := hb (x 6 6)
    have b1430 := hb (x 7 5)
    have b1431 := hb (x 8 4)
    have b1432 := hb (x 9 11)
    have b1433 := hb (x 10 10)
    have b1434 := hb (x 11 9)
    have b1435 := hb (x 12 8)
    clear * - r1421 e1422 e1423 e1424 e1425 e1426 e1427 b1428 b1429 b1430 b1431 b1432 b1433 b1434 b1435 d1409
    omega
  have d1436 : (x 11 9).toNat = 0 := by
    have r1437 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1438 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e1439 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e1440 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e1441 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e1442 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e1443 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b1444 := hb (x 5 7)
    have b1445 := hb (x 6 6)
    have b1446 := hb (x 7 5)
    have b1447 := hb (x 8 4)
    have b1448 := hb (x 9 11)
    have b1449 := hb (x 10 10)
    have b1450 := hb (x 11 9)
    have b1451 := hb (x 12 8)
    clear * - r1437 e1438 e1439 e1440 e1441 e1442 e1443 b1444 b1445 b1446 b1447 b1448 b1449 b1450 b1451 d1420 d1409
    omega
  have d1452 : (x 10 10).toNat = 0 := by
    have r1453 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1454 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e1455 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e1456 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e1457 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e1458 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e1459 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b1460 := hb (x 5 7)
    have b1461 := hb (x 6 6)
    have b1462 := hb (x 7 5)
    have b1463 := hb (x 8 4)
    have b1464 := hb (x 9 11)
    have b1465 := hb (x 10 10)
    have b1466 := hb (x 11 9)
    have b1467 := hb (x 12 8)
    clear * - r1453 e1454 e1455 e1456 e1457 e1458 e1459 b1460 b1461 b1462 b1463 b1464 b1465 b1466 b1467 d1420 d1436 d1409
    omega
  have d1468 : (x 9 11).toNat = 0 := by
    have r1469 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1470 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e1471 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e1472 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e1473 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e1474 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e1475 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b1476 := hb (x 5 7)
    have b1477 := hb (x 6 6)
    have b1478 := hb (x 7 5)
    have b1479 := hb (x 8 4)
    have b1480 := hb (x 9 11)
    have b1481 := hb (x 10 10)
    have b1482 := hb (x 11 9)
    have b1483 := hb (x 12 8)
    clear * - r1469 e1470 e1471 e1472 e1473 e1474 e1475 b1476 b1477 b1478 b1479 b1480 b1481 b1482 b1483 d1420 d1436 d1452 d1409
    omega
  have d1484 : (x 9 1 && x 9 11).toNat = 0 := by
    have r1485 := hand2 (x 9 1) (x 9 11)
    have b1486 := hb (x 9 11)
    have b1487 := hb (x 9 1 && x 9 11)
    clear * - r1485 b1486 b1487 d1468
    omega
  have d1488 : (x 7 3 && x 7 13).toNat = 1 := by
    have r1489 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1490 := hb (x 5 5)
    have b1491 := hb (x 10 10)
    have b1492 := hb (x 9 1 && x 9 11)
    have b1493 := hb (x 8 2 && x 8 12)
    have b1494 := hb (x 7 3 && x 7 13)
    have b1495 := hb (x 6 4 && x 6 14)
    clear * - r1489 b1490 b1491 b1492 b1493 b1494 b1495 d1452 d1484 d1056 d989 d1060
    omega
  have d1496 : (x 7 13).toNat = 1 := by
    have r1497 := hand2 (x 7 3) (x 7 13)
    have b1498 := hb (x 7 13)
    have b1499 := hb (x 7 3 && x 7 13)
    clear * - r1497 b1498 b1499 d1488
    omega
  have d1500 : (x 7 1).toNat = 1 := by
    have r1501 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b1502 := hb (x 7 1)
    have b1503 := hb (x 7 13)
    clear * - r1501 b1502 b1503 d1496
    omega
  have d1504 : (x 8 14).toNat = 0 := by
    have r1505 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1506 := hb (x 7 1)
    have b1507 := hb (x 8 14)
    clear * - r1505 b1506 b1507 d1500
    omega
  have d1508 : (x 8 1 && x 8 14).toNat = 0 := by
    have r1509 := hand2 (x 8 1) (x 8 14)
    have b1510 := hb (x 8 14)
    have b1511 := hb (x 8 1 && x 8 14)
    clear * - r1509 b1510 b1511 d1504
    omega
  have d1512 : (x 7 2).toNat = 1 := by
    have r1513 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1514 := hb (x 7 2)
    have b1515 := hb (x 9 13)
    have b1516 := hb (x 8 1 && x 8 14)
    clear * - r1513 b1514 b1515 b1516 d1032 d1508
    omega
  have d1517 : (x 7 14).toNat = 1 := by
    have r1518 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b1519 := hb (x 7 2)
    have b1520 := hb (x 7 14)
    clear * - r1518 b1519 b1520 d1512
    omega
  have d1521 : (x 6 1).toNat = 0 := by
    have r1522 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1523 := hb (x 6 1)
    have b1524 := hb (x 7 14)
    clear * - r1522 b1523 b1524 d1517
    omega
  have d1525 : (x 6 13).toNat = 0 := by
    have r1526 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b1527 := hb (x 6 1)
    have b1528 := hb (x 6 13)
    clear * - r1526 b1527 b1528 d1521
    omega
  have d1529 : (x 5 1 && x 5 14).toNat = 1 := by
    have r1530 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1531 := hb (x 4 2)
    have b1532 := hb (x 6 13)
    have b1533 := hb (x 5 1 && x 5 14)
    clear * - r1530 b1531 b1532 b1533 d1525 g9
    omega
  have d1534 : (x 5 14).toNat = 1 := by
    have r1535 := hand2 (x 5 1) (x 5 14)
    have b1536 := hb (x 5 14)
    have b1537 := hb (x 5 1 && x 5 14)
    clear * - r1535 b1536 b1537 d1529
    omega
  have d1538 : (x 4 1).toNat = 0 := by
    have r1539 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1540 := hb (x 4 1)
    have b1541 := hb (x 5 14)
    clear * - r1539 b1540 b1541 d1534
    omega
  have d1542 : (x 4 1 && x 4 11).toNat = 0 := by
    have r1543 := hand1 (x 4 1) (x 4 11)
    have b1544 := hb (x 4 1)
    have b1545 := hb (x 4 1 && x 4 11)
    clear * - r1543 b1544 b1545 d1538
    omega
  have d1546 : (x 5 10).toNat = 1 := by
    have r1547 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1548 := hb (x 0 5)
    have b1549 := hb (x 5 10)
    have b1550 := hb (x 4 1 && x 4 11)
    have b1551 := hb (x 3 2 && x 3 12)
    have b1552 := hb (x 2 3 && x 2 13)
    have b1553 := hb (x 1 4 && x 1 14)
    clear * - r1547 b1548 b1549 b1550 b1551 b1552 b1553 d1542 g22 g23 d1313 g1
    omega
  have d1554 : (x 5 2).toNat = 1 := by
    have r1555 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b1556 := hb (x 5 2)
    have b1557 := hb (x 5 10)
    clear * - r1555 b1556 b1557 d1546
    omega
  have d1558 : (x 7 8).toNat = 0 := by
    have r1559 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1560 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e1561 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e1562 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e1563 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e1564 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e1565 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b1566 := hb (x 0 7)
    have b1567 := hb (x 1 6)
    have b1568 := hb (x 2 5)
    have b1569 := hb (x 3 4)
    have b1570 := hb (x 4 11)
    have b1571 := hb (x 5 10)
    have b1572 := hb (x 6 9)
    have b1573 := hb (x 7 8)
    clear * - r1559 e1560 e1561 e1562 e1563 e1564 e1565 b1566 b1567 b1568 b1569 b1570 b1571 b1572 b1573 d1546 g8 g6
    omega
  have d1574 : (x 6 9).toNat = 0 := by
    have r1575 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1576 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e1577 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e1578 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e1579 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e1580 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e1581 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b1582 := hb (x 0 7)
    have b1583 := hb (x 1 6)
    have b1584 := hb (x 2 5)
    have b1585 := hb (x 3 4)
    have b1586 := hb (x 4 11)
    have b1587 := hb (x 5 10)
    have b1588 := hb (x 6 9)
    have b1589 := hb (x 7 8)
    clear * - r1575 e1576 e1577 e1578 e1579 e1580 e1581 b1582 b1583 b1584 b1585 b1586 b1587 b1588 b1589 d1558 d1546 g8 g6
    omega
  have d1590 : (x 4 11).toNat = 0 := by
    have r1591 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1592 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e1593 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e1594 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e1595 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e1596 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e1597 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b1598 := hb (x 0 7)
    have b1599 := hb (x 1 6)
    have b1600 := hb (x 2 5)
    have b1601 := hb (x 3 4)
    have b1602 := hb (x 4 11)
    have b1603 := hb (x 5 10)
    have b1604 := hb (x 6 9)
    have b1605 := hb (x 7 8)
    clear * - r1591 e1592 e1593 e1594 e1595 e1596 e1597 b1598 b1599 b1600 b1601 b1602 b1603 b1604 b1605 d1558 d1574 d1546 g8 g6
    omega
  have d1606 : (x 1 6).toNat = 0 := by
    have r1607 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1608 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e1609 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e1610 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e1611 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e1612 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e1613 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b1614 := hb (x 0 7)
    have b1615 := hb (x 1 6)
    have b1616 := hb (x 2 5)
    have b1617 := hb (x 3 4)
    have b1618 := hb (x 4 11)
    have b1619 := hb (x 5 10)
    have b1620 := hb (x 6 9)
    have b1621 := hb (x 7 8)
    clear * - r1607 e1608 e1609 e1610 e1611 e1612 e1613 b1614 b1615 b1616 b1617 b1618 b1619 b1620 b1621 d1558 d1574 d1546 d1590 g8 g6
    omega
  have d1622 : (x 1 6 && x 1 13).toNat = 0 := by
    have r1623 := hand1 (x 1 6) (x 1 13)
    have b1624 := hb (x 1 6)
    have b1625 := hb (x 1 6 && x 1 13)
    clear * - r1623 b1624 b1625 d1606
    omega
  have d1626 : (x 7 12).toNat = 0 := by
    have r1627 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1628 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e1629 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b1630 := hb (x 4 3)
    have b1631 := hb (x 5 2)
    have b1632 := hb (x 6 13)
    have b1633 := hb (x 7 12)
    clear * - r1627 e1628 e1629 b1630 b1631 b1632 b1633 d1525 d1554
    omega
  have d1634 : (x 7 4).toNat = 0 := by
    have r1635 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b1636 := hb (x 7 4)
    have b1637 := hb (x 7 12)
    clear * - r1635 b1636 b1637 d1626
    omega
  have d1638 : (x 8 3 && x 8 14).toNat = 0 := by
    have r1639 := hand2 (x 8 3) (x 8 14)
    have b1640 := hb (x 8 14)
    have b1641 := hb (x 8 3 && x 8 14)
    clear * - r1639 b1640 b1641 d1504
    omega
  have d1642 : (x 11 11).toNat = 1 := by
    have r1643 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1644 := hb (x 7 4)
    have b1645 := hb (x 11 11)
    have b1646 := hb (x 10 1 && x 10 12)
    have b1647 := hb (x 9 2 && x 9 13)
    have b1648 := hb (x 8 3 && x 8 14)
    clear * - r1643 b1644 b1645 b1646 b1647 b1648 d1024 d1040 d1638 d1634
    omega
  have d1649 : (x 11 3).toNat = 1 := by
    have r1650 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b1651 := hb (x 11 3)
    have b1652 := hb (x 11 11)
    clear * - r1650 b1651 b1652 d1642
    omega
  have d1653 : (x 14 12).toNat = 0 := by
    have r1654 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1655 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e1656 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b1657 := hb (x 11 3)
    have b1658 := hb (x 12 2)
    have b1659 := hb (x 13 13)
    have b1660 := hb (x 14 12)
    clear * - r1654 e1655 e1656 b1657 b1658 b1659 b1660 d1649
    omega
  have d1661 : (x 13 13).toNat = 0 := by
    have r1662 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1663 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e1664 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b1665 := hb (x 11 3)
    have b1666 := hb (x 12 2)
    have b1667 := hb (x 13 13)
    have b1668 := hb (x 14 12)
    clear * - r1662 e1663 e1664 b1665 b1666 b1667 b1668 d1653 d1649
    omega
  have d1669 : (x 12 2).toNat = 0 := by
    have r1670 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1671 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e1672 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b1673 := hb (x 11 3)
    have b1674 := hb (x 12 2)
    have b1675 := hb (x 13 13)
    have b1676 := hb (x 14 12)
    clear * - r1670 e1671 e1672 b1673 b1674 b1675 b1676 d1653 d1661 d1649
    omega
  have d1677 : (x 12 10).toNat = 0 := by
    have r1678 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
    have b1679 := hb (x 12 2)
    have b1680 := hb (x 12 10)
    clear * - r1678 b1679 b1680 d1669
    omega
  have d1681 : (x 14 8).toNat = 0 := by
    have r1682 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1683 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e1684 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e1685 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e1686 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e1687 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e1688 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b1689 := hb (x 7 7)
    have b1690 := hb (x 8 6)
    have b1691 := hb (x 9 5)
    have b1692 := hb (x 10 4)
    have b1693 := hb (x 11 11)
    have b1694 := hb (x 12 10)
    have b1695 := hb (x 13 9)
    have b1696 := hb (x 14 8)
    clear * - r1682 e1683 e1684 e1685 e1686 e1687 e1688 b1689 b1690 b1691 b1692 b1693 b1694 b1695 b1696 d1677 d1642 d1028 d1044
    omega
  have d1697 : (x 13 9).toNat = 0 := by
    have r1698 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1699 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e1700 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e1701 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e1702 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e1703 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e1704 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b1705 := hb (x 7 7)
    have b1706 := hb (x 8 6)
    have b1707 := hb (x 9 5)
    have b1708 := hb (x 10 4)
    have b1709 := hb (x 11 11)
    have b1710 := hb (x 12 10)
    have b1711 := hb (x 13 9)
    have b1712 := hb (x 14 8)
    clear * - r1698 e1699 e1700 e1701 e1702 e1703 e1704 b1705 b1706 b1707 b1708 b1709 b1710 b1711 b1712 d1681 d1677 d1642 d1028 d1044
    omega
  have d1713 : (x 8 6).toNat = 0 := by
    have r1714 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1715 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e1716 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e1717 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e1718 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e1719 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e1720 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b1721 := hb (x 7 7)
    have b1722 := hb (x 8 6)
    have b1723 := hb (x 9 5)
    have b1724 := hb (x 10 4)
    have b1725 := hb (x 11 11)
    have b1726 := hb (x 12 10)
    have b1727 := hb (x 13 9)
    have b1728 := hb (x 14 8)
    clear * - r1714 e1715 e1716 e1717 e1718 e1719 e1720 b1721 b1722 b1723 b1724 b1725 b1726 b1727 b1728 d1681 d1697 d1677 d1642 d1028 d1044
    omega
  have d1729 : (x 7 7).toNat = 0 := by
    have r1730 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1731 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e1732 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e1733 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e1734 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e1735 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e1736 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b1737 := hb (x 7 7)
    have b1738 := hb (x 8 6)
    have b1739 := hb (x 9 5)
    have b1740 := hb (x 10 4)
    have b1741 := hb (x 11 11)
    have b1742 := hb (x 12 10)
    have b1743 := hb (x 13 9)
    have b1744 := hb (x 14 8)
    clear * - r1730 e1731 e1732 e1733 e1734 e1735 e1736 b1737 b1738 b1739 b1740 b1741 b1742 b1743 b1744 d1681 d1697 d1677 d1642 d1028 d1044 d1713
    omega
  have d1745 : (x (-1) 8).toNat = 1 := by
    have r1746 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1747 := hb (x (-1) 8)
    have b1748 := hb (x 7 7)
    have b1749 := hb (x 6 1 && x 6 8)
    have b1750 := hb (x 5 2 && x 5 9)
    have b1751 := hb (x 4 3 && x 4 10)
    have b1752 := hb (x 3 4 && x 3 11)
    have b1753 := hb (x 2 5 && x 2 12)
    have b1754 := hb (x 1 6 && x 1 13)
    have b1755 := hb (x 0 7 && x 0 14)
    clear * - r1746 b1747 b1748 b1749 b1750 b1751 b1752 b1753 b1754 b1755 d1729 d1241 d1261 g14 g15 g16 d1622 d893
    omega
  have d1756 : (x (-3) 10).toNat = 0 := by
    have r1757 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1758 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e1759 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e1760 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e1761 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e1762 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e1763 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b1764 := hb (x (-8) 7)
    have b1765 := hb (x (-7) 6)
    have b1766 := hb (x (-6) 5)
    have b1767 := hb (x (-5) 4)
    have b1768 := hb (x (-4) 11)
    have b1769 := hb (x (-3) 10)
    have b1770 := hb (x (-2) 9)
    have b1771 := hb (x (-1) 8)
    clear * - r1757 e1758 e1759 e1760 e1761 e1762 e1763 b1764 b1765 b1766 b1767 b1768 b1769 b1770 b1771 d1745 d877 d953
    omega
  have d1772 : (x (-7) 4 && x (-7) 14).toNat = 1 := by
    have r1773 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1774 := hb (x (-8) 5)
    have b1775 := hb (x (-3) 10)
    have b1776 := hb (x (-4) 1 && x (-4) 11)
    have b1777 := hb (x (-5) 2 && x (-5) 12)
    have b1778 := hb (x (-6) 3 && x (-6) 13)
    have b1779 := hb (x (-7) 4 && x (-7) 14)
    clear * - r1773 b1774 b1775 b1776 b1777 b1778 b1779 d1756 d845 d1145 d1217 d1205
    omega
  have d1780 : (x (-7) 14).toNat = 1 := by
    have r1781 := hand2 (x (-7) 4) (x (-7) 14)
    have b1782 := hb (x (-7) 14)
    have b1783 := hb (x (-7) 4 && x (-7) 14)
    clear * - r1781 b1782 b1783 d1772
    omega
  have d1784 : (x (-8) 1).toNat = 0 := by
    have r1785 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1786 := hb (x (-8) 1)
    have b1787 := hb (x (-7) 14)
    clear * - r1785 b1786 b1787 d1780
    omega
  have d1788 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
    have r1789 := hand1 (x (-8) 1) (x (-8) 14)
    have b1790 := hb (x (-8) 1)
    have b1791 := hb (x (-8) 1 && x (-8) 14)
    clear * - r1789 b1790 b1791 d1784
    omega
  have d1792 : (x (-7) 13).toNat = 1 := by
    have r1793 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1794 := hb (x (-9) 2)
    have b1795 := hb (x (-7) 13)
    have b1796 := hb (x (-8) 1 && x (-8) 14)
    clear * - r1793 b1794 b1795 b1796 d1788 d1209
    omega
  have d1797 : (x (-7) 1).toNat = 1 := by
    have r1798 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
    have b1799 := hb (x (-7) 1)
    have b1800 := hb (x (-7) 13)
    clear * - r1798 b1799 b1800 d1792
    omega
  have d1801 : (x (-6) 14).toNat = 0 := by
    have r1802 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1803 := hb (x (-7) 1)
    have b1804 := hb (x (-6) 14)
    clear * - r1802 b1803 b1804 d1797
    omega
  have d1805 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
    have r1806 := hand2 (x (-6) 5) (x (-6) 14)
    have b1807 := hb (x (-6) 14)
    have b1808 := hb (x (-6) 5 && x (-6) 14)
    clear * - r1806 b1807 b1808 d1801
    omega
  have d1809 : (x (-6) 6).toNat = 0 := by
    have r1810 : (x (-6) 6).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp6 (-6))
    have b1811 := hb (x (-6) 6)
    have b1812 := hb (x (-6) 14)
    clear * - r1810 b1811 b1812 d1801
    omega
  have d1813 : (x (-5) 5 && x (-5) 14).toNat = 1 := by
    have r1814 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1815 := hb (x (-6) 6)
    have b1816 := hb (x 0 9)
    have b1817 := hb (x (-1) 1 && x (-1) 10)
    have b1818 := hb (x (-2) 2 && x (-2) 11)
    have b1819 := hb (x (-3) 3 && x (-3) 12)
    have b1820 := hb (x (-4) 4 && x (-4) 13)
    have b1821 := hb (x (-5) 5 && x (-5) 14)
    clear * - r1814 b1815 b1816 b1817 b1818 b1819 b1820 b1821 g2 d1389 d795 d909 d853 d1809
    omega
  have d1822 : (x (-5) 14).toNat = 1 := by
    have r1823 := hand2 (x (-5) 5) (x (-5) 14)
    have b1824 := hb (x (-5) 14)
    have b1825 := hb (x (-5) 5 && x (-5) 14)
    clear * - r1823 b1824 b1825 d1813
    omega
  have d1826 : (x (-6) 1).toNat = 0 := by
    have r1827 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1828 := hb (x (-6) 1)
    have b1829 := hb (x (-5) 14)
    clear * - r1827 b1828 b1829 d1822
    omega
  have d1830 : (x (-6) 13).toNat = 0 := by
    have r1831 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
    have b1832 := hb (x (-6) 1)
    have b1833 := hb (x (-6) 13)
    clear * - r1831 b1832 b1833 d1826
    omega
  have d1834 : (x (-6) 5).toNat = 0 := by
    have r1835 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
    have b1836 := hb (x (-6) 5)
    have b1837 := hb (x (-6) 13)
    clear * - r1835 b1836 b1837 d1830
    omega
  have d1838 : (x (-5) 5).toNat = 1 := by
    have r1839 := hand1 (x (-5) 5) (x (-5) 14)
    have b1840 := hb (x (-5) 5)
    have b1841 := hb (x (-5) 5 && x (-5) 14)
    clear * - r1839 b1840 b1841 d1813
    omega
  have d1842 : (x (-5) 13).toNat = 1 := by
    have r1843 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b1844 := hb (x (-5) 5)
    have b1845 := hb (x (-5) 13)
    clear * - r1843 b1844 b1845 d1838
    omega
  have d1846 : (x (-4) 12).toNat = 0 := by
    have r1847 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1848 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e1849 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b1850 := hb (x (-7) 3)
    have b1851 := hb (x (-6) 2)
    have b1852 := hb (x (-5) 13)
    have b1853 := hb (x (-4) 12)
    clear * - r1847 e1848 e1849 b1850 b1851 b1852 b1853 d1842
    omega
  have d1854 : (x (-4) 4).toNat = 0 := by
    have r1855 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b1856 := hb (x (-4) 4)
    have b1857 := hb (x (-4) 12)
    clear * - r1855 b1856 b1857 d1846
    omega
  have d1858 : (x 0 8).toNat = 0 := by
    have r1859 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1860 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e1861 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e1862 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e1863 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e1864 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e1865 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b1866 := hb (x (-7) 7)
    have b1867 := hb (x (-6) 6)
    have b1868 := hb (x (-5) 5)
    have b1869 := hb (x (-4) 4)
    have b1870 := hb (x (-3) 11)
    have b1871 := hb (x (-2) 10)
    have b1872 := hb (x (-1) 9)
    have b1873 := hb (x 0 8)
    clear * - r1859 e1860 e1861 e1862 e1863 e1864 e1865 b1866 b1867 b1868 b1869 b1870 b1871 b1872 b1873 d799 d913 d1854 d1838 d1809
    omega
  have d1874 : (x (-1) 9).toNat = 0 := by
    have r1875 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1876 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e1877 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e1878 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e1879 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e1880 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e1881 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b1882 := hb (x (-7) 7)
    have b1883 := hb (x (-6) 6)
    have b1884 := hb (x (-5) 5)
    have b1885 := hb (x (-4) 4)
    have b1886 := hb (x (-3) 11)
    have b1887 := hb (x (-2) 10)
    have b1888 := hb (x (-1) 9)
    have b1889 := hb (x 0 8)
    clear * - r1875 e1876 e1877 e1878 e1879 e1880 e1881 b1882 b1883 b1884 b1885 b1886 b1887 b1888 b1889 d1858 d799 d913 d1854 d1838 d1809
    omega
  have d1890 : (x (-5) 4).toNat = 0 := by
    have r1891 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1892 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e1893 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e1894 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e1895 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e1896 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e1897 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b1898 := hb (x (-8) 7)
    have b1899 := hb (x (-7) 6)
    have b1900 := hb (x (-6) 5)
    have b1901 := hb (x (-5) 4)
    have b1902 := hb (x (-4) 11)
    have b1903 := hb (x (-3) 10)
    have b1904 := hb (x (-2) 9)
    have b1905 := hb (x (-1) 8)
    clear * - r1891 e1892 e1893 e1894 e1895 e1896 e1897 b1898 b1899 b1900 b1901 b1902 b1903 b1904 b1905 d1745 d877 d1756 d953 d1834
    omega
  have d1906 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
    have r1907 := hand1 (x (-5) 4) (x (-5) 13)
    have b1908 := hb (x (-5) 4)
    have b1909 := hb (x (-5) 4 && x (-5) 13)
    clear * - r1907 b1908 b1909 d1890
    omega
  have d1910 : (x (-7) 6).toNat = 1 := by
    have r1911 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b1912 := hb (x (-7) 6)
    have b1913 := hb (x (-1) 9)
    have b1914 := hb (x (-2) 1 && x (-2) 10)
    have b1915 := hb (x (-3) 2 && x (-3) 11)
    have b1916 := hb (x (-4) 3 && x (-4) 12)
    have b1917 := hb (x (-5) 4 && x (-5) 13)
    have b1918 := hb (x (-6) 5 && x (-6) 14)
    clear * - r1911 b1912 b1913 b1914 b1915 b1916 b1917 b1918 d1874 d803 d917 d949 d1906 d1805
    omega
  have r1919 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e1920 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
  have e1921 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
  have e1922 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
  have e1923 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
  have e1924 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
  have e1925 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
  have b1926 := hb (x (-8) 7)
  have b1927 := hb (x (-7) 6)
  have b1928 := hb (x (-6) 5)
  have b1929 := hb (x (-5) 4)
  have b1930 := hb (x (-4) 11)
  have b1931 := hb (x (-3) 10)
  have b1932 := hb (x (-2) 9)
  have b1933 := hb (x (-1) 8)
  linarith only [r1919, e1920, e1921, e1922, e1923, e1924, e1925, b1926, b1927, b1928, b1929, b1930, b1931, b1932, b1933, d1745, d877, d1756, d953, d1890, d1834, d1910]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b1 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 4).toNat = 1)
    (g1 : (x 0 5).toNat = 0)
    (g2 : (x 0 9).toNat = 0)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 1 10).toNat = 0)
    (g5 : (x 1 11).toNat = 0)
    (g6 : (x 2 5).toNat = 0)
    (g7 : (x 2 10).toNat = 0)
    (g8 : (x 3 4).toNat = 0)
    (g9 : (x 4 2).toNat = 0)
    (g10 : (x 4 10).toNat = 0)
    (g11 : (x 2 3 && x 2 10).toNat = 0)
    (g12 : (x 1 4 && x 1 11).toNat = 0)
    (g13 : (x 0 5 && x 0 12).toNat = 0)
    (g14 : (x 4 3 && x 4 10).toNat = 0)
    (g15 : (x 3 4 && x 3 11).toNat = 0)
    (g16 : (x 2 5 && x 2 12).toNat = 0)
    (g17 : (x 0 1 && x 0 11).toNat = 0)
    (g18 : (x 1 2 && x 1 12).toNat = 0)
    (g19 : (x 0 3 && x 0 13).toNat = 0)
    (g20 : (x 2 2 && x 2 12).toNat = 0)
    (g21 : (x 1 3 && x 1 13).toNat = 0)
    (g22 : (x 3 2 && x 3 12).toNat = 0)
    (g23 : (x 2 3 && x 2 13).toNat = 0)
    (g24 : (x 4 3 && x 4 14).toNat = 0)
    (g25 : (x 4 1 && x 4 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b1_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25
