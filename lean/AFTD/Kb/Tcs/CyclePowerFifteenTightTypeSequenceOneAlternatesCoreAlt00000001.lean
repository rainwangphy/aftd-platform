import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000001

Topic: combinatorics   Node: fde7ad4cd50f

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 18 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt0000000001, cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt000000001.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt0000000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 3).toNat = 1)
    (g1 : (x (-1) 4).toNat = 0)
    (g2 : (x 0 2).toNat = 0)
    (g3 : (x 1 13).toNat = 0)
    (g4 : (x 3 2).toNat = 0)
    (g5 : (x 3 4).toNat = 0)
    (g6 : (x 1 2 && x 1 13).toNat = 0)
    (g7 : (x 0 3 && x 0 14).toNat = 0)
    (g8 : (x 5 1 && x 5 12).toNat = 0)
    (g9 : (x 4 2 && x 4 13).toNat = 0)
    (g10 : (x 3 3 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6806 : (x 2 12).toNat = 0 := by
    have r6807 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6808 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e6809 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b6810 := hb (x (-1) 3)
    have b6811 := hb (x 0 2)
    have b6812 := hb (x 1 13)
    have b6813 := hb (x 2 12)
    clear * - r6807 e6808 e6809 b6810 b6811 b6812 b6813 g3 g2 g0
    omega
  have d6814 : (x 2 1 && x 2 12).toNat = 0 := by
    have r6815 := hand2 (x 2 1) (x 2 12)
    have b6816 := hb (x 2 12)
    have b6817 := hb (x 2 1 && x 2 12)
    clear * - r6815 b6816 b6817 d6806
    omega
  have d6818 : (x 2 4).toNat = 0 := by
    have r6819 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b6820 := hb (x 2 4)
    have b6821 := hb (x 2 12)
    clear * - r6819 b6820 b6821 d6806
    omega
  have d6822 : (x 6 11).toNat = 1 := by
    have r6823 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6824 := hb (x 2 4)
    have b6825 := hb (x 6 11)
    have b6826 := hb (x 5 1 && x 5 12)
    have b6827 := hb (x 4 2 && x 4 13)
    have b6828 := hb (x 3 3 && x 3 14)
    clear * - r6823 b6824 b6825 b6826 b6827 b6828 g8 g9 g10 d6818
    omega
  have d6829 : (x 6 3).toNat = 1 := by
    have r6830 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
    have b6831 := hb (x 6 3)
    have b6832 := hb (x 6 11)
    clear * - r6830 b6831 b6832 d6822
    omega
  have d6833 : (x 9 12).toNat = 0 := by
    have r6834 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6835 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e6836 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b6837 := hb (x 6 3)
    have b6838 := hb (x 7 2)
    have b6839 := hb (x 8 13)
    have b6840 := hb (x 9 12)
    clear * - r6834 e6835 e6836 b6837 b6838 b6839 b6840 d6829
    omega
  have d6841 : (x 9 1 && x 9 12).toNat = 0 := by
    have r6842 := hand2 (x 9 1) (x 9 12)
    have b6843 := hb (x 9 12)
    have b6844 := hb (x 9 1 && x 9 12)
    clear * - r6842 b6843 b6844 d6833
    omega
  have d6845 : (x 8 13).toNat = 0 := by
    have r6846 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6847 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e6848 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b6849 := hb (x 6 3)
    have b6850 := hb (x 7 2)
    have b6851 := hb (x 8 13)
    have b6852 := hb (x 9 12)
    clear * - r6846 e6847 e6848 b6849 b6850 b6851 b6852 d6833 d6829
    omega
  have d6853 : (x 8 2 && x 8 13).toNat = 0 := by
    have r6854 := hand2 (x 8 2) (x 8 13)
    have b6855 := hb (x 8 13)
    have b6856 := hb (x 8 2 && x 8 13)
    clear * - r6854 b6855 b6856 d6845
    omega
  have d6857 : (x 7 2).toNat = 0 := by
    have r6858 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6859 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e6860 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b6861 := hb (x 6 3)
    have b6862 := hb (x 7 2)
    have b6863 := hb (x 8 13)
    have b6864 := hb (x 9 12)
    clear * - r6858 e6859 e6860 b6861 b6862 b6863 b6864 d6833 d6845 d6829
    omega
  have d6865 : (x 3 11).toNat = 1 := by
    have r6866 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6867 := hb (x (-1) 4)
    have b6868 := hb (x 3 11)
    have b6869 := hb (x 2 1 && x 2 12)
    have b6870 := hb (x 1 2 && x 1 13)
    have b6871 := hb (x 0 3 && x 0 14)
    clear * - r6866 b6867 b6868 b6869 b6870 b6871 d6814 g6 g7 g1
    omega
  have d6872 : (x 3 3).toNat = 1 := by
    have r6873 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b6874 := hb (x 3 3)
    have b6875 := hb (x 3 11)
    clear * - r6873 b6874 b6875 d6865
    omega
  have d6876 : (x 6 12).toNat = 0 := by
    have r6877 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6878 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e6879 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b6880 := hb (x 3 3)
    have b6881 := hb (x 4 2)
    have b6882 := hb (x 5 13)
    have b6883 := hb (x 6 12)
    clear * - r6877 e6878 e6879 b6880 b6881 b6882 b6883 d6872
    omega
  have d6884 : (x 6 1 && x 6 12).toNat = 0 := by
    have r6885 := hand2 (x 6 1) (x 6 12)
    have b6886 := hb (x 6 12)
    have b6887 := hb (x 6 1 && x 6 12)
    clear * - r6885 b6886 b6887 d6876
    omega
  have d6888 : (x 6 4).toNat = 0 := by
    have r6889 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b6890 := hb (x 6 4)
    have b6891 := hb (x 6 12)
    clear * - r6889 b6890 b6891 d6876
    omega
  have d6892 : (x 5 13).toNat = 0 := by
    have r6893 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6894 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e6895 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b6896 := hb (x 3 3)
    have b6897 := hb (x 4 2)
    have b6898 := hb (x 5 13)
    have b6899 := hb (x 6 12)
    clear * - r6893 e6894 e6895 b6896 b6897 b6898 b6899 d6876 d6872
    omega
  have d6900 : (x 5 2 && x 5 13).toNat = 0 := by
    have r6901 := hand2 (x 5 2) (x 5 13)
    have b6902 := hb (x 5 13)
    have b6903 := hb (x 5 2 && x 5 13)
    clear * - r6901 b6902 b6903 d6892
    omega
  have d6904 : (x 4 1 && x 4 14).toNat = 1 := by
    have r6905 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6906 := hb (x 3 2)
    have b6907 := hb (x 5 13)
    have b6908 := hb (x 4 1 && x 4 14)
    clear * - r6905 b6906 b6907 b6908 d6892 g4
    omega
  have d6909 : (x 4 1).toNat = 1 := by
    have r6910 := hand1 (x 4 1) (x 4 14)
    have b6911 := hb (x 4 1)
    have b6912 := hb (x 4 1 && x 4 14)
    clear * - r6910 b6911 b6912 d6904
    omega
  have d6913 : (x 5 14).toNat = 0 := by
    have r6914 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6915 := hb (x 4 1)
    have b6916 := hb (x 5 14)
    clear * - r6914 b6915 b6916 d6909
    omega
  have d6917 : (x 5 1 && x 5 14).toNat = 0 := by
    have r6918 := hand2 (x 5 1) (x 5 14)
    have b6919 := hb (x 5 14)
    have b6920 := hb (x 5 1 && x 5 14)
    clear * - r6918 b6919 b6920 d6913
    omega
  have d6921 : (x 5 2).toNat = 0 := by
    have r6922 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b6923 := hb (x 5 2)
    have b6924 := hb (x 5 14)
    clear * - r6922 b6923 b6924 d6913
    omega
  have d6925 : (x 4 2).toNat = 0 := by
    have r6926 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6927 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e6928 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b6929 := hb (x 3 3)
    have b6930 := hb (x 4 2)
    have b6931 := hb (x 5 13)
    have b6932 := hb (x 6 12)
    clear * - r6926 e6927 e6928 b6929 b6930 b6931 b6932 d6876 d6892 d6872
    omega
  have d6933 : (x 6 13).toNat = 1 := by
    have r6934 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6935 := hb (x 4 2)
    have b6936 := hb (x 6 13)
    have b6937 := hb (x 5 1 && x 5 14)
    clear * - r6934 b6935 b6936 b6937 d6917 d6925
    omega
  have d6938 : (x 6 1).toNat = 1 := by
    have r6939 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b6940 := hb (x 6 1)
    have b6941 := hb (x 6 13)
    clear * - r6939 b6940 b6941 d6933
    omega
  have d6942 : (x 7 14).toNat = 0 := by
    have r6943 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6944 := hb (x 6 1)
    have b6945 := hb (x 7 14)
    clear * - r6943 b6944 b6945 d6938
    omega
  have d6946 : (x 7 3 && x 7 14).toNat = 0 := by
    have r6947 := hand2 (x 7 3) (x 7 14)
    have b6948 := hb (x 7 14)
    have b6949 := hb (x 7 3 && x 7 14)
    clear * - r6947 b6948 b6949 d6942
    omega
  have d6950 : (x 10 11).toNat = 1 := by
    have r6951 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6952 := hb (x 6 4)
    have b6953 := hb (x 10 11)
    have b6954 := hb (x 9 1 && x 9 12)
    have b6955 := hb (x 8 2 && x 8 13)
    have b6956 := hb (x 7 3 && x 7 14)
    clear * - r6951 b6952 b6953 b6954 b6955 b6956 d6841 d6853 d6946 d6888
    omega
  have d6957 : (x 10 3).toNat = 1 := by
    have r6958 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
    have b6959 := hb (x 10 3)
    have b6960 := hb (x 10 11)
    clear * - r6958 b6959 b6960 d6950
    omega
  have d6961 : (x 13 12).toNat = 0 := by
    have r6962 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6963 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e6964 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b6965 := hb (x 10 3)
    have b6966 := hb (x 11 2)
    have b6967 := hb (x 12 13)
    have b6968 := hb (x 13 12)
    clear * - r6962 e6963 e6964 b6965 b6966 b6967 b6968 d6957
    omega
  have d6969 : (x 13 1 && x 13 12).toNat = 0 := by
    have r6970 := hand2 (x 13 1) (x 13 12)
    have b6971 := hb (x 13 12)
    have b6972 := hb (x 13 1 && x 13 12)
    clear * - r6970 b6971 b6972 d6961
    omega
  have d6973 : (x 12 13).toNat = 0 := by
    have r6974 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6975 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e6976 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b6977 := hb (x 10 3)
    have b6978 := hb (x 11 2)
    have b6979 := hb (x 12 13)
    have b6980 := hb (x 13 12)
    clear * - r6974 e6975 e6976 b6977 b6978 b6979 b6980 d6961 d6957
    omega
  have d6981 : (x 12 2 && x 12 13).toNat = 0 := by
    have r6982 := hand2 (x 12 2) (x 12 13)
    have b6983 := hb (x 12 13)
    have b6984 := hb (x 12 2 && x 12 13)
    clear * - r6982 b6983 b6984 d6973
    omega
  have d6985 : (x 11 2).toNat = 0 := by
    have r6986 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6987 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e6988 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b6989 := hb (x 10 3)
    have b6990 := hb (x 11 2)
    have b6991 := hb (x 12 13)
    have b6992 := hb (x 13 12)
    clear * - r6986 e6987 e6988 b6989 b6990 b6991 b6992 d6961 d6973 d6957
    omega
  have d6993 : (x 7 12).toNat = 0 := by
    have r6994 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6995 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e6996 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b6997 := hb (x 4 3)
    have b6998 := hb (x 5 2)
    have b6999 := hb (x 6 13)
    have b7000 := hb (x 7 12)
    clear * - r6994 e6995 e6996 b6997 b6998 b6999 b7000 d6933 d6921
    omega
  have d7001 : (x 7 4).toNat = 0 := by
    have r7002 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b7003 := hb (x 7 4)
    have b7004 := hb (x 7 12)
    clear * - r7002 b7003 b7004 d6993
    omega
  have d7005 : (x 4 3).toNat = 0 := by
    have r7006 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7007 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e7008 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b7009 := hb (x 4 3)
    have b7010 := hb (x 5 2)
    have b7011 := hb (x 6 13)
    have b7012 := hb (x 7 12)
    clear * - r7006 e7007 e7008 b7009 b7010 b7011 b7012 d6993 d6933 d6921
    omega
  have d7013 : (x 4 3 && x 4 14).toNat = 0 := by
    have r7014 := hand1 (x 4 3) (x 4 14)
    have b7015 := hb (x 4 3)
    have b7016 := hb (x 4 3 && x 4 14)
    clear * - r7014 b7015 b7016 d7005
    omega
  have d7017 : (x 7 11).toNat = 1 := by
    have r7018 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7019 := hb (x 3 4)
    have b7020 := hb (x 7 11)
    have b7021 := hb (x 6 1 && x 6 12)
    have b7022 := hb (x 5 2 && x 5 13)
    have b7023 := hb (x 4 3 && x 4 14)
    clear * - r7018 b7019 b7020 b7021 b7022 b7023 d6884 d6900 d7013 g5
    omega
  have d7024 : (x 7 3).toNat = 1 := by
    have r7025 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b7026 := hb (x 7 3)
    have b7027 := hb (x 7 11)
    clear * - r7025 b7026 b7027 d7017
    omega
  have d7028 : (x 10 12).toNat = 0 := by
    have r7029 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7030 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e7031 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b7032 := hb (x 7 3)
    have b7033 := hb (x 8 2)
    have b7034 := hb (x 9 13)
    have b7035 := hb (x 10 12)
    clear * - r7029 e7030 e7031 b7032 b7033 b7034 b7035 d7024
    omega
  have d7036 : (x 10 1 && x 10 12).toNat = 0 := by
    have r7037 := hand2 (x 10 1) (x 10 12)
    have b7038 := hb (x 10 12)
    have b7039 := hb (x 10 1 && x 10 12)
    clear * - r7037 b7038 b7039 d7028
    omega
  have d7040 : (x 10 4).toNat = 0 := by
    have r7041 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have b7042 := hb (x 10 4)
    have b7043 := hb (x 10 12)
    clear * - r7041 b7042 b7043 d7028
    omega
  have d7044 : (x 9 13).toNat = 0 := by
    have r7045 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7046 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e7047 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b7048 := hb (x 7 3)
    have b7049 := hb (x 8 2)
    have b7050 := hb (x 9 13)
    have b7051 := hb (x 10 12)
    clear * - r7045 e7046 e7047 b7048 b7049 b7050 b7051 d7028 d7024
    omega
  have d7052 : (x 9 2 && x 9 13).toNat = 0 := by
    have r7053 := hand2 (x 9 2) (x 9 13)
    have b7054 := hb (x 9 13)
    have b7055 := hb (x 9 2 && x 9 13)
    clear * - r7053 b7054 b7055 d7044
    omega
  have d7056 : (x 8 1 && x 8 14).toNat = 1 := by
    have r7057 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7058 := hb (x 7 2)
    have b7059 := hb (x 9 13)
    have b7060 := hb (x 8 1 && x 8 14)
    clear * - r7057 b7058 b7059 b7060 d7044 d6857
    omega
  have d7061 : (x 8 1).toNat = 1 := by
    have r7062 := hand1 (x 8 1) (x 8 14)
    have b7063 := hb (x 8 1)
    have b7064 := hb (x 8 1 && x 8 14)
    clear * - r7062 b7063 b7064 d7056
    omega
  have d7065 : (x 9 14).toNat = 0 := by
    have r7066 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7067 := hb (x 8 1)
    have b7068 := hb (x 9 14)
    clear * - r7066 b7067 b7068 d7061
    omega
  have d7069 : (x 9 1 && x 9 14).toNat = 0 := by
    have r7070 := hand2 (x 9 1) (x 9 14)
    have b7071 := hb (x 9 14)
    have b7072 := hb (x 9 1 && x 9 14)
    clear * - r7070 b7071 b7072 d7065
    omega
  have d7073 : (x 9 2).toNat = 0 := by
    have r7074 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b7075 := hb (x 9 2)
    have b7076 := hb (x 9 14)
    clear * - r7074 b7075 b7076 d7065
    omega
  have d7077 : (x 8 2).toNat = 0 := by
    have r7078 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7079 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e7080 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b7081 := hb (x 7 3)
    have b7082 := hb (x 8 2)
    have b7083 := hb (x 9 13)
    have b7084 := hb (x 10 12)
    clear * - r7078 e7079 e7080 b7081 b7082 b7083 b7084 d7028 d7044 d7024
    omega
  have d7085 : (x 10 13).toNat = 1 := by
    have r7086 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7087 := hb (x 8 2)
    have b7088 := hb (x 10 13)
    have b7089 := hb (x 9 1 && x 9 14)
    clear * - r7086 b7087 b7088 b7089 d7069 d7077
    omega
  have d7090 : (x 10 1).toNat = 1 := by
    have r7091 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b7092 := hb (x 10 1)
    have b7093 := hb (x 10 13)
    clear * - r7091 b7092 b7093 d7085
    omega
  have d7094 : (x 11 14).toNat = 0 := by
    have r7095 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7096 := hb (x 10 1)
    have b7097 := hb (x 11 14)
    clear * - r7095 b7096 b7097 d7090
    omega
  have d7098 : (x 11 1 && x 11 14).toNat = 0 := by
    have r7099 := hand2 (x 11 1) (x 11 14)
    have b7100 := hb (x 11 14)
    have b7101 := hb (x 11 1 && x 11 14)
    clear * - r7099 b7100 b7101 d7094
    omega
  have d7102 : (x 10 2).toNat = 1 := by
    have r7103 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7104 := hb (x 10 2)
    have b7105 := hb (x 12 13)
    have b7106 := hb (x 11 1 && x 11 14)
    clear * - r7103 b7104 b7105 b7106 d6973 d7098
    omega
  have d7107 : (x 12 12).toNat = 0 := by
    have r7108 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7109 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e7110 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b7111 := hb (x 9 3)
    have b7112 := hb (x 10 2)
    have b7113 := hb (x 11 13)
    have b7114 := hb (x 12 12)
    clear * - r7108 e7109 e7110 b7111 b7112 b7113 b7114 d7102
    omega
  have d7115 : (x 12 4).toNat = 0 := by
    have r7116 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b7117 := hb (x 12 4)
    have b7118 := hb (x 12 12)
    clear * - r7116 b7117 b7118 d7107
    omega
  have d7119 : (x 12 4 && x 12 14).toNat = 0 := by
    have r7120 := hand1 (x 12 4) (x 12 14)
    have b7121 := hb (x 12 4)
    have b7122 := hb (x 12 4 && x 12 14)
    clear * - r7120 b7121 b7122 d7115
    omega
  have d7123 : (x 11 13).toNat = 0 := by
    have r7124 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7125 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e7126 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b7127 := hb (x 9 3)
    have b7128 := hb (x 10 2)
    have b7129 := hb (x 11 13)
    have b7130 := hb (x 12 12)
    clear * - r7124 e7125 e7126 b7127 b7128 b7129 b7130 d7107 d7102
    omega
  have d7131 : (x 11 5).toNat = 0 := by
    have r7132 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
    have b7133 := hb (x 11 5)
    have b7134 := hb (x 11 13)
    clear * - r7132 b7133 b7134 d7123
    omega
  have d7135 : (x 11 3 && x 11 14).toNat = 0 := by
    have r7136 := hand2 (x 11 3) (x 11 14)
    have b7137 := hb (x 11 14)
    have b7138 := hb (x 11 3 && x 11 14)
    clear * - r7136 b7137 b7138 d7094
    omega
  have d7139 : (x 14 11).toNat = 1 := by
    have r7140 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7141 := hb (x 10 4)
    have b7142 := hb (x 14 11)
    have b7143 := hb (x 13 1 && x 13 12)
    have b7144 := hb (x 12 2 && x 12 13)
    have b7145 := hb (x 11 3 && x 11 14)
    clear * - r7140 b7141 b7142 b7143 b7144 b7145 d6969 d6981 d7135 d7040
    omega
  have d7146 : (x 14 3).toNat = 1 := by
    have r7147 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
    have b7148 := hb (x 14 3)
    have b7149 := hb (x 14 11)
    clear * - r7147 b7148 b7149 d7139
    omega
  have d7150 : (x 17 12).toNat = 0 := by
    have r7151 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7152 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e7153 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b7154 := hb (x 14 3)
    have b7155 := hb (x 15 2)
    have b7156 := hb (x 16 13)
    have b7157 := hb (x 17 12)
    clear * - r7151 e7152 e7153 b7154 b7155 b7156 b7157 d7146
    omega
  have d7158 : (x 16 13).toNat = 0 := by
    have r7159 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7160 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e7161 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b7162 := hb (x 14 3)
    have b7163 := hb (x 15 2)
    have b7164 := hb (x 16 13)
    have b7165 := hb (x 17 12)
    clear * - r7159 e7160 e7161 b7162 b7163 b7164 b7165 d7150 d7146
    omega
  have d7166 : (x 15 2).toNat = 0 := by
    have r7167 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7168 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e7169 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b7170 := hb (x 14 3)
    have b7171 := hb (x 15 2)
    have b7172 := hb (x 16 13)
    have b7173 := hb (x 17 12)
    clear * - r7167 e7168 e7169 b7170 b7171 b7172 b7173 d7150 d7158 d7146
    omega
  have d7174 : (x 11 12).toNat = 0 := by
    have r7175 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7176 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e7177 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b7178 := hb (x 8 3)
    have b7179 := hb (x 9 2)
    have b7180 := hb (x 10 13)
    have b7181 := hb (x 11 12)
    clear * - r7175 e7176 e7177 b7178 b7179 b7180 b7181 d7085 d7073
    omega
  have d7182 : (x 11 4).toNat = 0 := by
    have r7183 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b7184 := hb (x 11 4)
    have b7185 := hb (x 11 12)
    clear * - r7183 b7184 b7185 d7174
    omega
  have d7186 : (x 8 3).toNat = 0 := by
    have r7187 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7188 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e7189 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b7190 := hb (x 8 3)
    have b7191 := hb (x 9 2)
    have b7192 := hb (x 10 13)
    have b7193 := hb (x 11 12)
    clear * - r7187 e7188 e7189 b7190 b7191 b7192 b7193 d7174 d7085 d7073
    omega
  have d7194 : (x 8 3 && x 8 14).toNat = 0 := by
    have r7195 := hand1 (x 8 3) (x 8 14)
    have b7196 := hb (x 8 3)
    have b7197 := hb (x 8 3 && x 8 14)
    clear * - r7195 b7196 b7197 d7186
    omega
  have d7198 : (x 11 11).toNat = 1 := by
    have r7199 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7200 := hb (x 7 4)
    have b7201 := hb (x 11 11)
    have b7202 := hb (x 10 1 && x 10 12)
    have b7203 := hb (x 9 2 && x 9 13)
    have b7204 := hb (x 8 3 && x 8 14)
    clear * - r7199 b7200 b7201 b7202 b7203 b7204 d7036 d7052 d7194 d7001
    omega
  have d7205 : (x 11 3).toNat = 1 := by
    have r7206 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b7207 := hb (x 11 3)
    have b7208 := hb (x 11 11)
    clear * - r7206 b7207 b7208 d7198
    omega
  have d7209 : (x 14 12).toNat = 0 := by
    have r7210 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7211 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e7212 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b7213 := hb (x 11 3)
    have b7214 := hb (x 12 2)
    have b7215 := hb (x 13 13)
    have b7216 := hb (x 14 12)
    clear * - r7210 e7211 e7212 b7213 b7214 b7215 b7216 d7205
    omega
  have d7217 : (x 14 1 && x 14 12).toNat = 0 := by
    have r7218 := hand2 (x 14 1) (x 14 12)
    have b7219 := hb (x 14 12)
    have b7220 := hb (x 14 1 && x 14 12)
    clear * - r7218 b7219 b7220 d7209
    omega
  have d7221 : (x 14 2 && x 14 12).toNat = 0 := by
    have r7222 := hand2 (x 14 2) (x 14 12)
    have b7223 := hb (x 14 12)
    have b7224 := hb (x 14 2 && x 14 12)
    clear * - r7222 b7223 b7224 d7209
    omega
  have d7225 : (x 13 13).toNat = 0 := by
    have r7226 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7227 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e7228 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b7229 := hb (x 11 3)
    have b7230 := hb (x 12 2)
    have b7231 := hb (x 13 13)
    have b7232 := hb (x 14 12)
    clear * - r7226 e7227 e7228 b7229 b7230 b7231 b7232 d7209 d7205
    omega
  have d7233 : (x 13 2 && x 13 13).toNat = 0 := by
    have r7234 := hand2 (x 13 2) (x 13 13)
    have b7235 := hb (x 13 13)
    have b7236 := hb (x 13 2 && x 13 13)
    clear * - r7234 b7235 b7236 d7225
    omega
  have d7237 : (x 13 3 && x 13 13).toNat = 0 := by
    have r7238 := hand2 (x 13 3) (x 13 13)
    have b7239 := hb (x 13 13)
    have b7240 := hb (x 13 3 && x 13 13)
    clear * - r7238 b7239 b7240 d7225
    omega
  have d7241 : (x 12 1 && x 12 14).toNat = 1 := by
    have r7242 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7243 := hb (x 11 2)
    have b7244 := hb (x 13 13)
    have b7245 := hb (x 12 1 && x 12 14)
    clear * - r7242 b7243 b7244 b7245 d7225 d6985
    omega
  have d7246 : (x 12 1).toNat = 1 := by
    have r7247 := hand1 (x 12 1) (x 12 14)
    have b7248 := hb (x 12 1)
    have b7249 := hb (x 12 1 && x 12 14)
    clear * - r7247 b7248 b7249 d7241
    omega
  have d7250 : (x 13 14).toNat = 0 := by
    have r7251 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7252 := hb (x 12 1)
    have b7253 := hb (x 13 14)
    clear * - r7251 b7252 b7253 d7246
    omega
  have d7254 : (x 13 1 && x 13 14).toNat = 0 := by
    have r7255 := hand2 (x 13 1) (x 13 14)
    have b7256 := hb (x 13 14)
    have b7257 := hb (x 13 1 && x 13 14)
    clear * - r7255 b7256 b7257 d7250
    omega
  have d7258 : (x 13 2).toNat = 0 := by
    have r7259 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
    have b7260 := hb (x 13 2)
    have b7261 := hb (x 13 14)
    clear * - r7259 b7260 b7261 d7250
    omega
  have d7262 : (x 12 2).toNat = 0 := by
    have r7263 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7264 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e7265 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b7266 := hb (x 11 3)
    have b7267 := hb (x 12 2)
    have b7268 := hb (x 13 13)
    have b7269 := hb (x 14 12)
    clear * - r7263 e7264 e7265 b7266 b7267 b7268 b7269 d7209 d7225 d7205
    omega
  have d7270 : (x 14 13).toNat = 1 := by
    have r7271 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7272 := hb (x 12 2)
    have b7273 := hb (x 14 13)
    have b7274 := hb (x 13 1 && x 13 14)
    clear * - r7271 b7272 b7273 b7274 d7254 d7262
    omega
  have d7275 : (x 15 12).toNat = 0 := by
    have r7276 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7277 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e7278 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b7279 := hb (x 12 3)
    have b7280 := hb (x 13 2)
    have b7281 := hb (x 14 13)
    have b7282 := hb (x 15 12)
    clear * - r7276 e7277 e7278 b7279 b7280 b7281 b7282 d7270 d7258
    omega
  have d7283 : (x 12 3).toNat = 0 := by
    have r7284 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7285 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e7286 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b7287 := hb (x 12 3)
    have b7288 := hb (x 13 2)
    have b7289 := hb (x 14 13)
    have b7290 := hb (x 15 12)
    clear * - r7284 e7285 e7286 b7287 b7288 b7289 b7290 d7275 d7270 d7258
    omega
  have d7291 : (x 12 3 && x 12 14).toNat = 0 := by
    have r7292 := hand1 (x 12 3) (x 12 14)
    have b7293 := hb (x 12 3)
    have b7294 := hb (x 12 3 && x 12 14)
    clear * - r7292 b7293 b7294 d7283
    omega
  have d7295 : (x 15 11).toNat = 1 := by
    have r7296 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7297 := hb (x 11 4)
    have b7298 := hb (x 15 11)
    have b7299 := hb (x 14 1 && x 14 12)
    have b7300 := hb (x 13 2 && x 13 13)
    have b7301 := hb (x 12 3 && x 12 14)
    clear * - r7296 b7297 b7298 b7299 b7300 b7301 d7217 d7233 d7291 d7182
    omega
  have d7302 : (x 15 3).toNat = 1 := by
    have r7303 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
    have b7304 := hb (x 15 3)
    have b7305 := hb (x 15 11)
    clear * - r7303 b7304 b7305 d7295
    omega
  have d7306 : (x 18 12).toNat = 0 := by
    have r7307 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7308 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e7309 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b7310 := hb (x 15 3)
    have b7311 := hb (x 16 2)
    have b7312 := hb (x 17 13)
    have b7313 := hb (x 18 12)
    clear * - r7307 e7308 e7309 b7310 b7311 b7312 b7313 d7302
    omega
  have d7314 : (x 17 13).toNat = 0 := by
    have r7315 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7316 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e7317 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b7318 := hb (x 15 3)
    have b7319 := hb (x 16 2)
    have b7320 := hb (x 17 13)
    have b7321 := hb (x 18 12)
    clear * - r7315 e7316 e7317 b7318 b7319 b7320 b7321 d7306 d7302
    omega
  have d7322 : (x 16 1 && x 16 14).toNat = 1 := by
    have r7323 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7324 := hb (x 15 2)
    have b7325 := hb (x 17 13)
    have b7326 := hb (x 16 1 && x 16 14)
    clear * - r7323 b7324 b7325 b7326 d7314 d7166
    omega
  have d7327 : (x 16 14).toNat = 1 := by
    have r7328 := hand2 (x 16 1) (x 16 14)
    have b7329 := hb (x 16 14)
    have b7330 := hb (x 16 1 && x 16 14)
    clear * - r7328 b7329 b7330 d7322
    omega
  have d7331 : (x 15 1).toNat = 0 := by
    have r7332 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7333 := hb (x 15 1)
    have b7334 := hb (x 16 14)
    clear * - r7332 b7333 b7334 d7327
    omega
  have d7335 : (x 15 1 && x 15 11).toNat = 0 := by
    have r7336 := hand1 (x 15 1) (x 15 11)
    have b7337 := hb (x 15 1)
    have b7338 := hb (x 15 1 && x 15 11)
    clear * - r7336 b7337 b7338 d7331
    omega
  have d7339 : (x 16 2).toNat = 0 := by
    have r7340 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7341 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e7342 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b7343 := hb (x 15 3)
    have b7344 := hb (x 16 2)
    have b7345 := hb (x 17 13)
    have b7346 := hb (x 18 12)
    clear * - r7340 e7341 e7342 b7343 b7344 b7345 b7346 d7306 d7314 d7302
    omega
  have d7347 : (x 16 10).toNat = 0 := by
    have r7348 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
    have b7349 := hb (x 16 2)
    have b7350 := hb (x 16 10)
    clear * - r7348 b7349 b7350 d7339
    omega
  have r7351 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b7352 := hb (x 11 5)
  have b7353 := hb (x 16 10)
  have b7354 := hb (x 15 1 && x 15 11)
  have b7355 := hb (x 14 2 && x 14 12)
  have b7356 := hb (x 13 3 && x 13 13)
  have b7357 := hb (x 12 4 && x 12 14)
  linarith only [r7351, b7352, b7353, b7354, b7355, b7356, b7357, d7347, d7335, d7221, d7237, d7119, d7131]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt000000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 13).toNat = 0)
    (g1 : (x (-2) 2).toNat = 0)
    (g2 : (x (-1) 4).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 2).toNat = 0)
    (g5 : (x 0 10).toNat = 0)
    (g6 : (x 0 11).toNat = 0)
    (g7 : (x 0 12).toNat = 1)
    (g8 : (x 1 13).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 3 5).toNat = 0)
    (g12 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g13 : (x 4 4 && x 4 14).toNat = 0)
    (g14 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g15 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g16 : (x 1 2 && x 1 13).toNat = 0)
    (g17 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d7359 : (x (-3) 3).toNat = 0 := by
    have r7360 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7361 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e7362 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b7363 := hb (x (-3) 3)
    have b7364 := hb (x (-2) 2)
    have b7365 := hb (x (-1) 13)
    have b7366 := hb (x 0 12)
    clear * - r7360 e7361 e7362 b7363 b7364 b7365 b7366 g7 g3 g1
    omega
  have d7367 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r7368 := hand1 (x (-3) 3) (x (-3) 14)
    have b7369 := hb (x (-3) 3)
    have b7370 := hb (x (-3) 3 && x (-3) 14)
    clear * - r7368 b7369 b7370 d7359
    omega
  have d7371 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r7372 := hand1 (x (-3) 3) (x (-3) 13)
    have b7373 := hb (x (-3) 3)
    have b7374 := hb (x (-3) 3 && x (-3) 13)
    clear * - r7372 b7373 b7374 d7359
    omega
  have d7375 : (x (-4) 4).toNat = 1 := by
    have r7376 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7377 := hb (x (-4) 4)
    have b7378 := hb (x 0 11)
    have b7379 := hb (x (-1) 1 && x (-1) 12)
    have b7380 := hb (x (-2) 2 && x (-2) 13)
    have b7381 := hb (x (-3) 3 && x (-3) 14)
    clear * - r7376 b7377 b7378 b7379 b7380 b7381 g6 g14 g15 d7367
    omega
  have d7382 : (x (-4) 12).toNat = 1 := by
    have r7383 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b7384 := hb (x (-4) 4)
    have b7385 := hb (x (-4) 12)
    clear * - r7383 b7384 b7385 d7375
    omega
  have d7386 : (x (-5) 13).toNat = 0 := by
    have r7387 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7388 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e7389 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b7390 := hb (x (-7) 3)
    have b7391 := hb (x (-6) 2)
    have b7392 := hb (x (-5) 13)
    have b7393 := hb (x (-4) 12)
    clear * - r7387 e7388 e7389 b7390 b7391 b7392 b7393 d7382
    omega
  have d7394 : (x (-5) 5).toNat = 0 := by
    have r7395 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b7396 := hb (x (-5) 5)
    have b7397 := hb (x (-5) 13)
    clear * - r7395 b7396 b7397 d7386
    omega
  have d7398 : (x (-6) 2).toNat = 0 := by
    have r7399 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7400 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e7401 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b7402 := hb (x (-7) 3)
    have b7403 := hb (x (-6) 2)
    have b7404 := hb (x (-5) 13)
    have b7405 := hb (x (-4) 12)
    clear * - r7399 e7400 e7401 b7402 b7403 b7404 b7405 d7382 d7386
    omega
  have d7406 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
    have r7407 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7408 := hb (x (-6) 2)
    have b7409 := hb (x (-4) 13)
    have b7410 := hb (x (-5) 1 && x (-5) 14)
    clear * - r7407 b7408 b7409 b7410 g0 d7398
    omega
  have d7411 : (x (-5) 1).toNat = 1 := by
    have r7412 := hand1 (x (-5) 1) (x (-5) 14)
    have b7413 := hb (x (-5) 1)
    have b7414 := hb (x (-5) 1 && x (-5) 14)
    clear * - r7412 b7413 b7414 d7406
    omega
  have d7415 : (x (-4) 14).toNat = 0 := by
    have r7416 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7417 := hb (x (-5) 1)
    have b7418 := hb (x (-4) 14)
    clear * - r7416 b7417 b7418 d7411
    omega
  have d7419 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r7420 := hand2 (x (-4) 4) (x (-4) 14)
    have b7421 := hb (x (-4) 14)
    have b7422 := hb (x (-4) 4 && x (-4) 14)
    clear * - r7420 b7421 b7422 d7415
    omega
  have d7423 : (x (-1) 1 && x (-1) 11).toNat = 1 := by
    have r7424 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7425 := hb (x (-5) 5)
    have b7426 := hb (x 0 10)
    have b7427 := hb (x (-1) 1 && x (-1) 11)
    have b7428 := hb (x (-2) 2 && x (-2) 12)
    have b7429 := hb (x (-3) 3 && x (-3) 13)
    have b7430 := hb (x (-4) 4 && x (-4) 14)
    clear * - r7424 b7425 b7426 b7427 b7428 b7429 b7430 g5 g12 d7371 d7419 d7394
    omega
  have d7431 : (x (-1) 11).toNat = 1 := by
    have r7432 := hand2 (x (-1) 1) (x (-1) 11)
    have b7433 := hb (x (-1) 11)
    have b7434 := hb (x (-1) 1 && x (-1) 11)
    clear * - r7432 b7433 b7434 d7423
    omega
  have d7435 : (x (-1) 3).toNat = 1 := by
    have r7436 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b7437 := hb (x (-1) 3)
    have b7438 := hb (x (-1) 11)
    clear * - r7436 b7437 b7438 d7431
    omega
  have d7439 : (x 2 12).toNat = 0 := by
    have r7440 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7441 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e7442 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b7443 := hb (x (-1) 3)
    have b7444 := hb (x 0 2)
    have b7445 := hb (x 1 13)
    have b7446 := hb (x 2 12)
    clear * - r7440 e7441 e7442 b7443 b7444 b7445 b7446 g8 g4 d7435
    omega
  have d7447 : (x 2 1 && x 2 12).toNat = 0 := by
    have r7448 := hand2 (x 2 1) (x 2 12)
    have b7449 := hb (x 2 12)
    have b7450 := hb (x 2 1 && x 2 12)
    clear * - r7448 b7449 b7450 d7439
    omega
  have d7451 : (x 3 11).toNat = 1 := by
    have r7452 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7453 := hb (x (-1) 4)
    have b7454 := hb (x 3 11)
    have b7455 := hb (x 2 1 && x 2 12)
    have b7456 := hb (x 1 2 && x 1 13)
    have b7457 := hb (x 0 3 && x 0 14)
    clear * - r7452 b7453 b7454 b7455 b7456 b7457 d7447 g16 g17 g2
    omega
  have d7458 : (x 3 3).toNat = 1 := by
    have r7459 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b7460 := hb (x 3 3)
    have b7461 := hb (x 3 11)
    clear * - r7459 b7460 b7461 d7451
    omega
  have d7462 : (x 6 12).toNat = 0 := by
    have r7463 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7464 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7465 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7466 := hb (x 3 3)
    have b7467 := hb (x 4 2)
    have b7468 := hb (x 5 13)
    have b7469 := hb (x 6 12)
    clear * - r7463 e7464 e7465 b7466 b7467 b7468 b7469 d7458
    omega
  have d7470 : (x 6 1 && x 6 12).toNat = 0 := by
    have r7471 := hand2 (x 6 1) (x 6 12)
    have b7472 := hb (x 6 12)
    have b7473 := hb (x 6 1 && x 6 12)
    clear * - r7471 b7472 b7473 d7462
    omega
  have d7474 : (x 6 2 && x 6 12).toNat = 0 := by
    have r7475 := hand2 (x 6 2) (x 6 12)
    have b7476 := hb (x 6 12)
    have b7477 := hb (x 6 2 && x 6 12)
    clear * - r7475 b7476 b7477 d7462
    omega
  have d7478 : (x 5 13).toNat = 0 := by
    have r7479 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7480 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7481 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7482 := hb (x 3 3)
    have b7483 := hb (x 4 2)
    have b7484 := hb (x 5 13)
    have b7485 := hb (x 6 12)
    clear * - r7479 e7480 e7481 b7482 b7483 b7484 b7485 d7462 d7458
    omega
  have d7486 : (x 5 2 && x 5 13).toNat = 0 := by
    have r7487 := hand2 (x 5 2) (x 5 13)
    have b7488 := hb (x 5 13)
    have b7489 := hb (x 5 2 && x 5 13)
    clear * - r7487 b7488 b7489 d7478
    omega
  have d7490 : (x 5 3 && x 5 13).toNat = 0 := by
    have r7491 := hand2 (x 5 3) (x 5 13)
    have b7492 := hb (x 5 13)
    have b7493 := hb (x 5 3 && x 5 13)
    clear * - r7491 b7492 b7493 d7478
    omega
  have d7494 : (x 4 1 && x 4 14).toNat = 1 := by
    have r7495 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7496 := hb (x 3 2)
    have b7497 := hb (x 5 13)
    have b7498 := hb (x 4 1 && x 4 14)
    clear * - r7495 b7496 b7497 b7498 d7478 g9
    omega
  have d7499 : (x 4 1).toNat = 1 := by
    have r7500 := hand1 (x 4 1) (x 4 14)
    have b7501 := hb (x 4 1)
    have b7502 := hb (x 4 1 && x 4 14)
    clear * - r7500 b7501 b7502 d7494
    omega
  have d7503 : (x 5 14).toNat = 0 := by
    have r7504 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7505 := hb (x 4 1)
    have b7506 := hb (x 5 14)
    clear * - r7504 b7505 b7506 d7499
    omega
  have d7507 : (x 5 1 && x 5 14).toNat = 0 := by
    have r7508 := hand2 (x 5 1) (x 5 14)
    have b7509 := hb (x 5 14)
    have b7510 := hb (x 5 1 && x 5 14)
    clear * - r7508 b7509 b7510 d7503
    omega
  have d7511 : (x 5 2).toNat = 0 := by
    have r7512 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b7513 := hb (x 5 2)
    have b7514 := hb (x 5 14)
    clear * - r7512 b7513 b7514 d7503
    omega
  have d7515 : (x 4 2).toNat = 0 := by
    have r7516 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7517 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7518 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7519 := hb (x 3 3)
    have b7520 := hb (x 4 2)
    have b7521 := hb (x 5 13)
    have b7522 := hb (x 6 12)
    clear * - r7516 e7517 e7518 b7519 b7520 b7521 b7522 d7462 d7478 d7458
    omega
  have d7523 : (x 6 13).toNat = 1 := by
    have r7524 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7525 := hb (x 4 2)
    have b7526 := hb (x 6 13)
    have b7527 := hb (x 5 1 && x 5 14)
    clear * - r7524 b7525 b7526 b7527 d7507 d7515
    omega
  have d7528 : (x 6 1).toNat = 1 := by
    have r7529 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b7530 := hb (x 6 1)
    have b7531 := hb (x 6 13)
    clear * - r7529 b7530 b7531 d7523
    omega
  have d7532 : (x 7 14).toNat = 0 := by
    have r7533 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7534 := hb (x 6 1)
    have b7535 := hb (x 7 14)
    clear * - r7533 b7534 b7535 d7528
    omega
  have d7536 : (x 7 2).toNat = 0 := by
    have r7537 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b7538 := hb (x 7 2)
    have b7539 := hb (x 7 14)
    clear * - r7537 b7538 b7539 d7532
    omega
  have d7540 : (x 7 12).toNat = 0 := by
    have r7541 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7542 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e7543 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b7544 := hb (x 4 3)
    have b7545 := hb (x 5 2)
    have b7546 := hb (x 6 13)
    have b7547 := hb (x 7 12)
    clear * - r7541 e7542 e7543 b7544 b7545 b7546 b7547 d7523 d7511
    omega
  have d7548 : (x 4 3).toNat = 0 := by
    have r7549 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7550 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e7551 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b7552 := hb (x 4 3)
    have b7553 := hb (x 5 2)
    have b7554 := hb (x 6 13)
    have b7555 := hb (x 7 12)
    clear * - r7549 e7550 e7551 b7552 b7553 b7554 b7555 d7540 d7523 d7511
    omega
  have d7556 : (x 4 3 && x 4 14).toNat = 0 := by
    have r7557 := hand1 (x 4 3) (x 4 14)
    have b7558 := hb (x 4 3)
    have b7559 := hb (x 4 3 && x 4 14)
    clear * - r7557 b7558 b7559 d7548
    omega
  have d7560 : (x 7 11).toNat = 1 := by
    have r7561 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7562 := hb (x 3 4)
    have b7563 := hb (x 7 11)
    have b7564 := hb (x 6 1 && x 6 12)
    have b7565 := hb (x 5 2 && x 5 13)
    have b7566 := hb (x 4 3 && x 4 14)
    clear * - r7561 b7562 b7563 b7564 b7565 b7566 d7470 d7486 d7556 g10
    omega
  have d7567 : (x 7 3).toNat = 1 := by
    have r7568 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b7569 := hb (x 7 3)
    have b7570 := hb (x 7 11)
    clear * - r7568 b7569 b7570 d7560
    omega
  have d7571 : (x 10 12).toNat = 0 := by
    have r7572 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7573 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e7574 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b7575 := hb (x 7 3)
    have b7576 := hb (x 8 2)
    have b7577 := hb (x 9 13)
    have b7578 := hb (x 10 12)
    clear * - r7572 e7573 e7574 b7575 b7576 b7577 b7578 d7567
    omega
  have d7579 : (x 9 13).toNat = 0 := by
    have r7580 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7581 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e7582 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b7583 := hb (x 7 3)
    have b7584 := hb (x 8 2)
    have b7585 := hb (x 9 13)
    have b7586 := hb (x 10 12)
    clear * - r7580 e7581 e7582 b7583 b7584 b7585 b7586 d7571 d7567
    omega
  have d7587 : (x 8 1 && x 8 14).toNat = 1 := by
    have r7588 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7589 := hb (x 7 2)
    have b7590 := hb (x 9 13)
    have b7591 := hb (x 8 1 && x 8 14)
    clear * - r7588 b7589 b7590 b7591 d7579 d7536
    omega
  have d7592 : (x 8 14).toNat = 1 := by
    have r7593 := hand2 (x 8 1) (x 8 14)
    have b7594 := hb (x 8 14)
    have b7595 := hb (x 8 1 && x 8 14)
    clear * - r7593 b7594 b7595 d7587
    omega
  have d7596 : (x 7 1).toNat = 0 := by
    have r7597 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7598 := hb (x 7 1)
    have b7599 := hb (x 8 14)
    clear * - r7597 b7598 b7599 d7592
    omega
  have d7600 : (x 7 1 && x 7 11).toNat = 0 := by
    have r7601 := hand1 (x 7 1) (x 7 11)
    have b7602 := hb (x 7 1)
    have b7603 := hb (x 7 1 && x 7 11)
    clear * - r7601 b7602 b7603 d7596
    omega
  have d7604 : (x 8 10).toNat = 1 := by
    have r7605 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7606 := hb (x 3 5)
    have b7607 := hb (x 8 10)
    have b7608 := hb (x 7 1 && x 7 11)
    have b7609 := hb (x 6 2 && x 6 12)
    have b7610 := hb (x 5 3 && x 5 13)
    have b7611 := hb (x 4 4 && x 4 14)
    clear * - r7605 b7606 b7607 b7608 b7609 b7610 b7611 d7600 d7474 d7490 g13 g11
    omega
  have d7612 : (x 8 2).toNat = 1 := by
    have r7613 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
    have b7614 := hb (x 8 2)
    have b7615 := hb (x 8 10)
    clear * - r7613 b7614 b7615 d7604
    omega
  have r7616 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7617 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
  have e7618 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
  have b7619 := hb (x 7 3)
  have b7620 := hb (x 8 2)
  have b7621 := hb (x 9 13)
  have b7622 := hb (x 10 12)
  linarith only [r7616, e7617, e7618, b7619, b7620, b7621, b7622, d7571, d7579, d7612, d7567]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 13).toNat = 0)
    (g1 : (x (-2) 2).toNat = 0)
    (g2 : (x (-1) 4).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 2).toNat = 0)
    (g5 : (x 0 4).toNat = 1)
    (g6 : (x 0 10).toNat = 0)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 1 13).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 3 5).toNat = 0)
    (g12 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g13 : (x 4 4 && x 4 14).toNat = 0)
    (g14 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g15 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g16 : (x 1 2 && x 1 13).toNat = 0)
    (g17 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d7624 : (x 0 12).toNat = 1 := by
    have r7625 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b7626 := hb (x 0 4)
    have b7627 := hb (x 0 12)
    clear * - r7625 b7626 b7627 g5
    omega
  have d7628 : (x (-3) 3).toNat = 0 := by
    have r7629 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7630 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e7631 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b7632 := hb (x (-3) 3)
    have b7633 := hb (x (-2) 2)
    have b7634 := hb (x (-1) 13)
    have b7635 := hb (x 0 12)
    clear * - r7629 e7630 e7631 b7632 b7633 b7634 b7635 d7624 g3 g1
    omega
  have d7636 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r7637 := hand1 (x (-3) 3) (x (-3) 14)
    have b7638 := hb (x (-3) 3)
    have b7639 := hb (x (-3) 3 && x (-3) 14)
    clear * - r7637 b7638 b7639 d7628
    omega
  have d7640 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r7641 := hand1 (x (-3) 3) (x (-3) 13)
    have b7642 := hb (x (-3) 3)
    have b7643 := hb (x (-3) 3 && x (-3) 13)
    clear * - r7641 b7642 b7643 d7628
    omega
  have d7644 : (x (-4) 4).toNat = 1 := by
    have r7645 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7646 := hb (x (-4) 4)
    have b7647 := hb (x 0 11)
    have b7648 := hb (x (-1) 1 && x (-1) 12)
    have b7649 := hb (x (-2) 2 && x (-2) 13)
    have b7650 := hb (x (-3) 3 && x (-3) 14)
    clear * - r7645 b7646 b7647 b7648 b7649 b7650 g7 g14 g15 d7636
    omega
  have d7651 : (x (-4) 12).toNat = 1 := by
    have r7652 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b7653 := hb (x (-4) 4)
    have b7654 := hb (x (-4) 12)
    clear * - r7652 b7653 b7654 d7644
    omega
  have d7655 : (x (-5) 13).toNat = 0 := by
    have r7656 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7657 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e7658 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b7659 := hb (x (-7) 3)
    have b7660 := hb (x (-6) 2)
    have b7661 := hb (x (-5) 13)
    have b7662 := hb (x (-4) 12)
    clear * - r7656 e7657 e7658 b7659 b7660 b7661 b7662 d7651
    omega
  have d7663 : (x (-5) 5).toNat = 0 := by
    have r7664 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b7665 := hb (x (-5) 5)
    have b7666 := hb (x (-5) 13)
    clear * - r7664 b7665 b7666 d7655
    omega
  have d7667 : (x (-6) 2).toNat = 0 := by
    have r7668 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7669 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e7670 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b7671 := hb (x (-7) 3)
    have b7672 := hb (x (-6) 2)
    have b7673 := hb (x (-5) 13)
    have b7674 := hb (x (-4) 12)
    clear * - r7668 e7669 e7670 b7671 b7672 b7673 b7674 d7651 d7655
    omega
  have d7675 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
    have r7676 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7677 := hb (x (-6) 2)
    have b7678 := hb (x (-4) 13)
    have b7679 := hb (x (-5) 1 && x (-5) 14)
    clear * - r7676 b7677 b7678 b7679 g0 d7667
    omega
  have d7680 : (x (-5) 1).toNat = 1 := by
    have r7681 := hand1 (x (-5) 1) (x (-5) 14)
    have b7682 := hb (x (-5) 1)
    have b7683 := hb (x (-5) 1 && x (-5) 14)
    clear * - r7681 b7682 b7683 d7675
    omega
  have d7684 : (x (-4) 14).toNat = 0 := by
    have r7685 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7686 := hb (x (-5) 1)
    have b7687 := hb (x (-4) 14)
    clear * - r7685 b7686 b7687 d7680
    omega
  have d7688 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r7689 := hand2 (x (-4) 4) (x (-4) 14)
    have b7690 := hb (x (-4) 14)
    have b7691 := hb (x (-4) 4 && x (-4) 14)
    clear * - r7689 b7690 b7691 d7684
    omega
  have d7692 : (x (-1) 1 && x (-1) 11).toNat = 1 := by
    have r7693 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7694 := hb (x (-5) 5)
    have b7695 := hb (x 0 10)
    have b7696 := hb (x (-1) 1 && x (-1) 11)
    have b7697 := hb (x (-2) 2 && x (-2) 12)
    have b7698 := hb (x (-3) 3 && x (-3) 13)
    have b7699 := hb (x (-4) 4 && x (-4) 14)
    clear * - r7693 b7694 b7695 b7696 b7697 b7698 b7699 g6 g12 d7640 d7688 d7663
    omega
  have d7700 : (x (-1) 11).toNat = 1 := by
    have r7701 := hand2 (x (-1) 1) (x (-1) 11)
    have b7702 := hb (x (-1) 11)
    have b7703 := hb (x (-1) 1 && x (-1) 11)
    clear * - r7701 b7702 b7703 d7692
    omega
  have d7704 : (x (-1) 3).toNat = 1 := by
    have r7705 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b7706 := hb (x (-1) 3)
    have b7707 := hb (x (-1) 11)
    clear * - r7705 b7706 b7707 d7700
    omega
  have d7708 : (x 2 12).toNat = 0 := by
    have r7709 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7710 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e7711 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b7712 := hb (x (-1) 3)
    have b7713 := hb (x 0 2)
    have b7714 := hb (x 1 13)
    have b7715 := hb (x 2 12)
    clear * - r7709 e7710 e7711 b7712 b7713 b7714 b7715 g8 g4 d7704
    omega
  have d7716 : (x 2 1 && x 2 12).toNat = 0 := by
    have r7717 := hand2 (x 2 1) (x 2 12)
    have b7718 := hb (x 2 12)
    have b7719 := hb (x 2 1 && x 2 12)
    clear * - r7717 b7718 b7719 d7708
    omega
  have d7720 : (x 3 11).toNat = 1 := by
    have r7721 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7722 := hb (x (-1) 4)
    have b7723 := hb (x 3 11)
    have b7724 := hb (x 2 1 && x 2 12)
    have b7725 := hb (x 1 2 && x 1 13)
    have b7726 := hb (x 0 3 && x 0 14)
    clear * - r7721 b7722 b7723 b7724 b7725 b7726 d7716 g16 g17 g2
    omega
  have d7727 : (x 3 3).toNat = 1 := by
    have r7728 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b7729 := hb (x 3 3)
    have b7730 := hb (x 3 11)
    clear * - r7728 b7729 b7730 d7720
    omega
  have d7731 : (x 6 12).toNat = 0 := by
    have r7732 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7733 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7734 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7735 := hb (x 3 3)
    have b7736 := hb (x 4 2)
    have b7737 := hb (x 5 13)
    have b7738 := hb (x 6 12)
    clear * - r7732 e7733 e7734 b7735 b7736 b7737 b7738 d7727
    omega
  have d7739 : (x 6 1 && x 6 12).toNat = 0 := by
    have r7740 := hand2 (x 6 1) (x 6 12)
    have b7741 := hb (x 6 12)
    have b7742 := hb (x 6 1 && x 6 12)
    clear * - r7740 b7741 b7742 d7731
    omega
  have d7743 : (x 6 2 && x 6 12).toNat = 0 := by
    have r7744 := hand2 (x 6 2) (x 6 12)
    have b7745 := hb (x 6 12)
    have b7746 := hb (x 6 2 && x 6 12)
    clear * - r7744 b7745 b7746 d7731
    omega
  have d7747 : (x 5 13).toNat = 0 := by
    have r7748 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7749 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7750 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7751 := hb (x 3 3)
    have b7752 := hb (x 4 2)
    have b7753 := hb (x 5 13)
    have b7754 := hb (x 6 12)
    clear * - r7748 e7749 e7750 b7751 b7752 b7753 b7754 d7731 d7727
    omega
  have d7755 : (x 5 2 && x 5 13).toNat = 0 := by
    have r7756 := hand2 (x 5 2) (x 5 13)
    have b7757 := hb (x 5 13)
    have b7758 := hb (x 5 2 && x 5 13)
    clear * - r7756 b7757 b7758 d7747
    omega
  have d7759 : (x 5 3 && x 5 13).toNat = 0 := by
    have r7760 := hand2 (x 5 3) (x 5 13)
    have b7761 := hb (x 5 13)
    have b7762 := hb (x 5 3 && x 5 13)
    clear * - r7760 b7761 b7762 d7747
    omega
  have d7763 : (x 4 1 && x 4 14).toNat = 1 := by
    have r7764 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7765 := hb (x 3 2)
    have b7766 := hb (x 5 13)
    have b7767 := hb (x 4 1 && x 4 14)
    clear * - r7764 b7765 b7766 b7767 d7747 g9
    omega
  have d7768 : (x 4 1).toNat = 1 := by
    have r7769 := hand1 (x 4 1) (x 4 14)
    have b7770 := hb (x 4 1)
    have b7771 := hb (x 4 1 && x 4 14)
    clear * - r7769 b7770 b7771 d7763
    omega
  have d7772 : (x 5 14).toNat = 0 := by
    have r7773 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7774 := hb (x 4 1)
    have b7775 := hb (x 5 14)
    clear * - r7773 b7774 b7775 d7768
    omega
  have d7776 : (x 5 1 && x 5 14).toNat = 0 := by
    have r7777 := hand2 (x 5 1) (x 5 14)
    have b7778 := hb (x 5 14)
    have b7779 := hb (x 5 1 && x 5 14)
    clear * - r7777 b7778 b7779 d7772
    omega
  have d7780 : (x 5 2).toNat = 0 := by
    have r7781 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b7782 := hb (x 5 2)
    have b7783 := hb (x 5 14)
    clear * - r7781 b7782 b7783 d7772
    omega
  have d7784 : (x 4 2).toNat = 0 := by
    have r7785 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7786 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e7787 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b7788 := hb (x 3 3)
    have b7789 := hb (x 4 2)
    have b7790 := hb (x 5 13)
    have b7791 := hb (x 6 12)
    clear * - r7785 e7786 e7787 b7788 b7789 b7790 b7791 d7731 d7747 d7727
    omega
  have d7792 : (x 6 13).toNat = 1 := by
    have r7793 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7794 := hb (x 4 2)
    have b7795 := hb (x 6 13)
    have b7796 := hb (x 5 1 && x 5 14)
    clear * - r7793 b7794 b7795 b7796 d7776 d7784
    omega
  have d7797 : (x 6 1).toNat = 1 := by
    have r7798 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b7799 := hb (x 6 1)
    have b7800 := hb (x 6 13)
    clear * - r7798 b7799 b7800 d7792
    omega
  have d7801 : (x 7 14).toNat = 0 := by
    have r7802 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7803 := hb (x 6 1)
    have b7804 := hb (x 7 14)
    clear * - r7802 b7803 b7804 d7797
    omega
  have d7805 : (x 7 2).toNat = 0 := by
    have r7806 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b7807 := hb (x 7 2)
    have b7808 := hb (x 7 14)
    clear * - r7806 b7807 b7808 d7801
    omega
  have d7809 : (x 7 12).toNat = 0 := by
    have r7810 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7811 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e7812 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b7813 := hb (x 4 3)
    have b7814 := hb (x 5 2)
    have b7815 := hb (x 6 13)
    have b7816 := hb (x 7 12)
    clear * - r7810 e7811 e7812 b7813 b7814 b7815 b7816 d7792 d7780
    omega
  have d7817 : (x 4 3).toNat = 0 := by
    have r7818 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7819 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e7820 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b7821 := hb (x 4 3)
    have b7822 := hb (x 5 2)
    have b7823 := hb (x 6 13)
    have b7824 := hb (x 7 12)
    clear * - r7818 e7819 e7820 b7821 b7822 b7823 b7824 d7809 d7792 d7780
    omega
  have d7825 : (x 4 3 && x 4 14).toNat = 0 := by
    have r7826 := hand1 (x 4 3) (x 4 14)
    have b7827 := hb (x 4 3)
    have b7828 := hb (x 4 3 && x 4 14)
    clear * - r7826 b7827 b7828 d7817
    omega
  have d7829 : (x 7 11).toNat = 1 := by
    have r7830 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7831 := hb (x 3 4)
    have b7832 := hb (x 7 11)
    have b7833 := hb (x 6 1 && x 6 12)
    have b7834 := hb (x 5 2 && x 5 13)
    have b7835 := hb (x 4 3 && x 4 14)
    clear * - r7830 b7831 b7832 b7833 b7834 b7835 d7739 d7755 d7825 g10
    omega
  have d7836 : (x 7 3).toNat = 1 := by
    have r7837 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b7838 := hb (x 7 3)
    have b7839 := hb (x 7 11)
    clear * - r7837 b7838 b7839 d7829
    omega
  have d7840 : (x 10 12).toNat = 0 := by
    have r7841 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7842 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e7843 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b7844 := hb (x 7 3)
    have b7845 := hb (x 8 2)
    have b7846 := hb (x 9 13)
    have b7847 := hb (x 10 12)
    clear * - r7841 e7842 e7843 b7844 b7845 b7846 b7847 d7836
    omega
  have d7848 : (x 9 13).toNat = 0 := by
    have r7849 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7850 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e7851 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b7852 := hb (x 7 3)
    have b7853 := hb (x 8 2)
    have b7854 := hb (x 9 13)
    have b7855 := hb (x 10 12)
    clear * - r7849 e7850 e7851 b7852 b7853 b7854 b7855 d7840 d7836
    omega
  have d7856 : (x 8 1 && x 8 14).toNat = 1 := by
    have r7857 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7858 := hb (x 7 2)
    have b7859 := hb (x 9 13)
    have b7860 := hb (x 8 1 && x 8 14)
    clear * - r7857 b7858 b7859 b7860 d7848 d7805
    omega
  have d7861 : (x 8 14).toNat = 1 := by
    have r7862 := hand2 (x 8 1) (x 8 14)
    have b7863 := hb (x 8 14)
    have b7864 := hb (x 8 1 && x 8 14)
    clear * - r7862 b7863 b7864 d7856
    omega
  have d7865 : (x 7 1).toNat = 0 := by
    have r7866 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7867 := hb (x 7 1)
    have b7868 := hb (x 8 14)
    clear * - r7866 b7867 b7868 d7861
    omega
  have d7869 : (x 7 1 && x 7 11).toNat = 0 := by
    have r7870 := hand1 (x 7 1) (x 7 11)
    have b7871 := hb (x 7 1)
    have b7872 := hb (x 7 1 && x 7 11)
    clear * - r7870 b7871 b7872 d7865
    omega
  have d7873 : (x 8 10).toNat = 1 := by
    have r7874 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7875 := hb (x 3 5)
    have b7876 := hb (x 8 10)
    have b7877 := hb (x 7 1 && x 7 11)
    have b7878 := hb (x 6 2 && x 6 12)
    have b7879 := hb (x 5 3 && x 5 13)
    have b7880 := hb (x 4 4 && x 4 14)
    clear * - r7874 b7875 b7876 b7877 b7878 b7879 b7880 d7869 d7743 d7759 g13 g11
    omega
  have d7881 : (x 8 2).toNat = 1 := by
    have r7882 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
    have b7883 := hb (x 8 2)
    have b7884 := hb (x 8 10)
    clear * - r7882 b7883 b7884 d7873
    omega
  have r7885 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7886 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
  have e7887 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
  have b7888 := hb (x 7 3)
  have b7889 := hb (x 8 2)
  have b7890 := hb (x 9 13)
  have b7891 := hb (x 10 12)
  linarith only [r7885, e7886, e7887, b7888, b7889, b7890, b7891, d7840, d7848, d7881, d7836]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 13).toNat = 0)
    (g1 : (x (-2) 2).toNat = 0)
    (g2 : (x (-1) 4).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 2).toNat = 0)
    (g5 : (x 0 4).toNat = 1)
    (g6 : (x 0 10).toNat = 0)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 1 13).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 3 5).toNat = 0)
    (g12 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g13 : (x 4 4 && x 4 14).toNat = 0)
    (g14 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g15 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g16 : (x 1 2 && x 1 13).toNat = 0)
    (g17 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17
