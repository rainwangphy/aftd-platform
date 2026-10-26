import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a001

Topic: combinatorics   Node: 32570c213b79

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 5 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 13).toNat = 1)
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
  have d41831 : (x 1 12).toNat = 0 := by
    have r41832 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e41833 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e41834 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b41835 := hb (x (-2) 3)
    have b41836 := hb (x (-1) 2)
    have b41837 := hb (x 0 13)
    have b41838 := hb (x 1 12)
    clear * - r41832 e41833 e41834 b41835 b41836 b41837 b41838 g0
    omega
  have d41839 : (x (-1) 2).toNat = 0 := by
    have r41840 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e41841 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e41842 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b41843 := hb (x (-2) 3)
    have b41844 := hb (x (-1) 2)
    have b41845 := hb (x 0 13)
    have b41846 := hb (x 1 12)
    clear * - r41840 e41841 e41842 b41843 b41844 b41845 b41846 d41831 g0
    omega
  have d41847 : (x 1 13).toNat = 1 := by
    have r41848 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
    have b41849 := hb (x (-1) 2)
    have b41850 := hb (x 1 13)
    have b41851 := hb (x 0 1 && x 0 14)
    clear * - r41848 b41849 b41850 b41851 g3 d41839
    omega
  have d41852 : (x 1 1).toNat = 1 := by
    have r41853 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b41854 := hb (x 1 1)
    have b41855 := hb (x 1 13)
    clear * - r41853 b41854 b41855 d41847
    omega
  have d41856 : (x 2 14).toNat = 0 := by
    have r41857 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
    have b41858 := hb (x 1 1)
    have b41859 := hb (x 2 14)
    clear * - r41857 b41858 b41859 d41852
    omega
  have d41860 : (x 2 1 && x 2 14).toNat = 0 := by
    have r41861 := hand2 (x 2 1) (x 2 14)
    have b41862 := hb (x 2 14)
    have b41863 := hb (x 2 1 && x 2 14)
    clear * - r41861 b41862 b41863 d41856
    omega
  have d41864 : (x 3 13).toNat = 1 := by
    have r41865 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
    have b41866 := hb (x 1 2)
    have b41867 := hb (x 3 13)
    have b41868 := hb (x 2 1 && x 2 14)
    clear * - r41865 b41866 b41867 b41868 d41860 g1
    omega
  have d41869 : (x 3 1).toNat = 1 := by
    have r41870 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b41871 := hb (x 3 1)
    have b41872 := hb (x 3 13)
    clear * - r41870 b41871 b41872 d41864
    omega
  have d41873 : (x 4 14).toNat = 0 := by
    have r41874 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
    have b41875 := hb (x 3 1)
    have b41876 := hb (x 4 14)
    clear * - r41874 b41875 b41876 d41869
    omega
  have d41877 : (x 4 1 && x 4 14).toNat = 0 := by
    have r41878 := hand2 (x 4 1) (x 4 14)
    have b41879 := hb (x 4 14)
    have b41880 := hb (x 4 1 && x 4 14)
    clear * - r41878 b41879 b41880 d41873
    omega
  have d41881 : (x 5 13).toNat = 1 := by
    have r41882 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
    have b41883 := hb (x 3 2)
    have b41884 := hb (x 5 13)
    have b41885 := hb (x 4 1 && x 4 14)
    clear * - r41882 b41883 b41884 b41885 d41877 g2
    omega
  have d41886 : (x 5 1).toNat = 1 := by
    have r41887 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b41888 := hb (x 5 1)
    have b41889 := hb (x 5 13)
    clear * - r41887 b41888 b41889 d41881
    omega
  have d41890 : (x 6 14).toNat = 0 := by
    have r41891 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
    have b41892 := hb (x 5 1)
    have b41893 := hb (x 6 14)
    clear * - r41891 b41892 b41893 d41886
    omega
  have d41894 : (x 6 1 && x 6 14).toNat = 0 := by
    have r41895 := hand2 (x 6 1) (x 6 14)
    have b41896 := hb (x 6 14)
    have b41897 := hb (x 6 1 && x 6 14)
    clear * - r41895 b41896 b41897 d41890
    omega
  have d41898 : (x 6 2).toNat = 0 := by
    have r41899 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b41900 := hb (x 6 2)
    have b41901 := hb (x 6 14)
    clear * - r41899 b41900 b41901 d41890
    omega
  have d41902 : (x 6 12).toNat = 0 := by
    have r41903 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e41904 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e41905 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b41906 := hb (x 3 3)
    have b41907 := hb (x 4 2)
    have b41908 := hb (x 5 13)
    have b41909 := hb (x 6 12)
    clear * - r41903 e41904 e41905 b41906 b41907 b41908 b41909 d41881
    omega
  have d41910 : (x 4 2).toNat = 0 := by
    have r41911 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
    have e41912 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e41913 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b41914 := hb (x 3 3)
    have b41915 := hb (x 4 2)
    have b41916 := hb (x 5 13)
    have b41917 := hb (x 6 12)
    clear * - r41911 e41912 e41913 b41914 b41915 b41916 b41917 d41902 d41881
    omega
  have d41918 : (x 4 12).toNat = 0 := by
    have r41919 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e41920 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e41921 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b41922 := hb (x 1 3)
    have b41923 := hb (x 2 2)
    have b41924 := hb (x 3 13)
    have b41925 := hb (x 4 12)
    clear * - r41919 e41920 e41921 b41922 b41923 b41924 b41925 d41864
    omega
  have d41926 : (x 2 2).toNat = 0 := by
    have r41927 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e41928 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e41929 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b41930 := hb (x 1 3)
    have b41931 := hb (x 2 2)
    have b41932 := hb (x 3 13)
    have b41933 := hb (x 4 12)
    clear * - r41927 e41928 e41929 b41930 b41931 b41932 b41933 d41918 d41864
    omega
  have d41934 : (x 4 13).toNat = 1 := by
    have r41935 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b41936 := hb (x 2 2)
    have b41937 := hb (x 4 13)
    have b41938 := hb (x 3 1 && x 3 14)
    clear * - r41935 b41936 b41937 b41938 g4 d41926
    omega
  have d41939 : (x 4 1).toNat = 1 := by
    have r41940 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b41941 := hb (x 4 1)
    have b41942 := hb (x 4 13)
    clear * - r41940 b41941 b41942 d41934
    omega
  have d41943 : (x 5 14).toNat = 0 := by
    have r41944 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
    have b41945 := hb (x 4 1)
    have b41946 := hb (x 5 14)
    clear * - r41944 b41945 b41946 d41939
    omega
  have d41947 : (x 5 1 && x 5 14).toNat = 0 := by
    have r41948 := hand2 (x 5 1) (x 5 14)
    have b41949 := hb (x 5 14)
    have b41950 := hb (x 5 1 && x 5 14)
    clear * - r41948 b41949 b41950 d41943
    omega
  have d41951 : (x 6 13).toNat = 1 := by
    have r41952 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
    have b41953 := hb (x 4 2)
    have b41954 := hb (x 6 13)
    have b41955 := hb (x 5 1 && x 5 14)
    clear * - r41952 b41953 b41954 b41955 d41947 d41910
    omega
  have d41956 : (x 6 1).toNat = 1 := by
    have r41957 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b41958 := hb (x 6 1)
    have b41959 := hb (x 6 13)
    clear * - r41957 b41958 b41959 d41951
    omega
  have d41960 : (x 7 14).toNat = 0 := by
    have r41961 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
    have b41962 := hb (x 6 1)
    have b41963 := hb (x 7 14)
    clear * - r41961 b41962 b41963 d41956
    omega
  have d41964 : (x 7 1 && x 7 14).toNat = 0 := by
    have r41965 := hand2 (x 7 1) (x 7 14)
    have b41966 := hb (x 7 14)
    have b41967 := hb (x 7 1 && x 7 14)
    clear * - r41965 b41966 b41967 d41960
    omega
  have d41968 : (x 8 13).toNat = 1 := by
    have r41969 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
    have b41970 := hb (x 6 2)
    have b41971 := hb (x 8 13)
    have b41972 := hb (x 7 1 && x 7 14)
    clear * - r41969 b41970 b41971 b41972 d41964 d41898
    omega
  have d41973 : (x 8 1).toNat = 1 := by
    have r41974 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b41975 := hb (x 8 1)
    have b41976 := hb (x 8 13)
    clear * - r41974 b41975 b41976 d41968
    omega
  have d41977 : (x 9 14).toNat = 0 := by
    have r41978 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
    have b41979 := hb (x 8 1)
    have b41980 := hb (x 9 14)
    clear * - r41978 b41979 b41980 d41973
    omega
  have d41981 : (x 9 1 && x 9 14).toNat = 0 := by
    have r41982 := hand2 (x 9 1) (x 9 14)
    have b41983 := hb (x 9 14)
    have b41984 := hb (x 9 1 && x 9 14)
    clear * - r41982 b41983 b41984 d41977
    omega
  have d41985 : (x 9 2).toNat = 0 := by
    have r41986 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b41987 := hb (x 9 2)
    have b41988 := hb (x 9 14)
    clear * - r41986 b41987 b41988 d41977
    omega
  have d41989 : (x 9 12).toNat = 0 := by
    have r41990 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e41991 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e41992 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b41993 := hb (x 6 3)
    have b41994 := hb (x 7 2)
    have b41995 := hb (x 8 13)
    have b41996 := hb (x 9 12)
    clear * - r41990 e41991 e41992 b41993 b41994 b41995 b41996 d41968
    omega
  have d41997 : (x 7 2).toNat = 0 := by
    have r41998 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
    have e41999 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e42000 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b42001 := hb (x 6 3)
    have b42002 := hb (x 7 2)
    have b42003 := hb (x 8 13)
    have b42004 := hb (x 9 12)
    clear * - r41998 e41999 e42000 b42001 b42002 b42003 b42004 d41989 d41968
    omega
  have d42005 : (x 7 12).toNat = 0 := by
    have r42006 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e42007 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e42008 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b42009 := hb (x 4 3)
    have b42010 := hb (x 5 2)
    have b42011 := hb (x 6 13)
    have b42012 := hb (x 7 12)
    clear * - r42006 e42007 e42008 b42009 b42010 b42011 b42012 d41951
    omega
  have d42013 : (x 5 2).toNat = 0 := by
    have r42014 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e42015 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e42016 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b42017 := hb (x 4 3)
    have b42018 := hb (x 5 2)
    have b42019 := hb (x 6 13)
    have b42020 := hb (x 7 12)
    clear * - r42014 e42015 e42016 b42017 b42018 b42019 b42020 d42005 d41951
    omega
  have d42021 : (x 7 13).toNat = 1 := by
    have r42022 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
    have b42023 := hb (x 5 2)
    have b42024 := hb (x 7 13)
    have b42025 := hb (x 6 1 && x 6 14)
    clear * - r42022 b42023 b42024 b42025 d41894 d42013
    omega
  have d42026 : (x 7 1).toNat = 1 := by
    have r42027 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b42028 := hb (x 7 1)
    have b42029 := hb (x 7 13)
    clear * - r42027 b42028 b42029 d42021
    omega
  have d42030 : (x 8 14).toNat = 0 := by
    have r42031 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
    have b42032 := hb (x 7 1)
    have b42033 := hb (x 8 14)
    clear * - r42031 b42032 b42033 d42026
    omega
  have d42034 : (x 8 1 && x 8 14).toNat = 0 := by
    have r42035 := hand2 (x 8 1) (x 8 14)
    have b42036 := hb (x 8 14)
    have b42037 := hb (x 8 1 && x 8 14)
    clear * - r42035 b42036 b42037 d42030
    omega
  have d42038 : (x 9 13).toNat = 1 := by
    have r42039 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
    have b42040 := hb (x 7 2)
    have b42041 := hb (x 9 13)
    have b42042 := hb (x 8 1 && x 8 14)
    clear * - r42039 b42040 b42041 b42042 d42034 d41997
    omega
  have d42043 : (x 9 1).toNat = 1 := by
    have r42044 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b42045 := hb (x 9 1)
    have b42046 := hb (x 9 13)
    clear * - r42044 b42045 b42046 d42038
    omega
  have d42047 : (x 10 14).toNat = 0 := by
    have r42048 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
    have b42049 := hb (x 9 1)
    have b42050 := hb (x 10 14)
    clear * - r42048 b42049 b42050 d42043
    omega
  have d42051 : (x 10 1 && x 10 14).toNat = 0 := by
    have r42052 := hand2 (x 10 1) (x 10 14)
    have b42053 := hb (x 10 14)
    have b42054 := hb (x 10 1 && x 10 14)
    clear * - r42052 b42053 b42054 d42047
    omega
  have d42055 : (x 11 13).toNat = 1 := by
    have r42056 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
    have b42057 := hb (x 9 2)
    have b42058 := hb (x 11 13)
    have b42059 := hb (x 10 1 && x 10 14)
    clear * - r42056 b42057 b42058 b42059 d42051 d41985
    omega
  have d42060 : (x 11 1).toNat = 1 := by
    have r42061 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b42062 := hb (x 11 1)
    have b42063 := hb (x 11 13)
    clear * - r42061 b42062 b42063 d42055
    omega
  have d42064 : (x 12 14).toNat = 0 := by
    have r42065 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
    have b42066 := hb (x 11 1)
    have b42067 := hb (x 12 14)
    clear * - r42065 b42066 b42067 d42060
    omega
  have d42068 : (x 12 1 && x 12 14).toNat = 0 := by
    have r42069 := hand2 (x 12 1) (x 12 14)
    have b42070 := hb (x 12 14)
    have b42071 := hb (x 12 1 && x 12 14)
    clear * - r42069 b42070 b42071 d42064
    omega
  have d42072 : (x 12 2).toNat = 0 := by
    have r42073 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
    have b42074 := hb (x 12 2)
    have b42075 := hb (x 12 14)
    clear * - r42073 b42074 b42075 d42064
    omega
  have d42076 : (x 12 12).toNat = 0 := by
    have r42077 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e42078 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e42079 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b42080 := hb (x 9 3)
    have b42081 := hb (x 10 2)
    have b42082 := hb (x 11 13)
    have b42083 := hb (x 12 12)
    clear * - r42077 e42078 e42079 b42080 b42081 b42082 b42083 d42055
    omega
  have d42084 : (x 10 2).toNat = 0 := by
    have r42085 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e42086 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e42087 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b42088 := hb (x 9 3)
    have b42089 := hb (x 10 2)
    have b42090 := hb (x 11 13)
    have b42091 := hb (x 12 12)
    clear * - r42085 e42086 e42087 b42088 b42089 b42090 b42091 d42076 d42055
    omega
  have d42092 : (x 10 12).toNat = 0 := by
    have r42093 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e42094 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e42095 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b42096 := hb (x 7 3)
    have b42097 := hb (x 8 2)
    have b42098 := hb (x 9 13)
    have b42099 := hb (x 10 12)
    clear * - r42093 e42094 e42095 b42096 b42097 b42098 b42099 d42038
    omega
  have d42100 : (x 8 2).toNat = 0 := by
    have r42101 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e42102 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e42103 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b42104 := hb (x 7 3)
    have b42105 := hb (x 8 2)
    have b42106 := hb (x 9 13)
    have b42107 := hb (x 10 12)
    clear * - r42101 e42102 e42103 b42104 b42105 b42106 b42107 d42092 d42038
    omega
  have d42108 : (x 10 13).toNat = 1 := by
    have r42109 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
    have b42110 := hb (x 8 2)
    have b42111 := hb (x 10 13)
    have b42112 := hb (x 9 1 && x 9 14)
    clear * - r42109 b42110 b42111 b42112 d41981 d42100
    omega
  have d42113 : (x 10 1).toNat = 1 := by
    have r42114 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b42115 := hb (x 10 1)
    have b42116 := hb (x 10 13)
    clear * - r42114 b42115 b42116 d42108
    omega
  have d42117 : (x 11 14).toNat = 0 := by
    have r42118 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
    have b42119 := hb (x 10 1)
    have b42120 := hb (x 11 14)
    clear * - r42118 b42119 b42120 d42113
    omega
  have d42121 : (x 11 1 && x 11 14).toNat = 0 := by
    have r42122 := hand2 (x 11 1) (x 11 14)
    have b42123 := hb (x 11 14)
    have b42124 := hb (x 11 1 && x 11 14)
    clear * - r42122 b42123 b42124 d42117
    omega
  have d42125 : (x 12 13).toNat = 1 := by
    have r42126 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
    have b42127 := hb (x 10 2)
    have b42128 := hb (x 12 13)
    have b42129 := hb (x 11 1 && x 11 14)
    clear * - r42126 b42127 b42128 b42129 d42121 d42084
    omega
  have d42130 : (x 12 1).toNat = 1 := by
    have r42131 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b42132 := hb (x 12 1)
    have b42133 := hb (x 12 13)
    clear * - r42131 b42132 b42133 d42125
    omega
  have d42134 : (x 13 14).toNat = 0 := by
    have r42135 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
    have b42136 := hb (x 12 1)
    have b42137 := hb (x 13 14)
    clear * - r42135 b42136 b42137 d42130
    omega
  have d42138 : (x 13 1 && x 13 14).toNat = 0 := by
    have r42139 := hand2 (x 13 1) (x 13 14)
    have b42140 := hb (x 13 14)
    have b42141 := hb (x 13 1 && x 13 14)
    clear * - r42139 b42140 b42141 d42134
    omega
  have d42142 : (x 14 13).toNat = 1 := by
    have r42143 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
    have b42144 := hb (x 12 2)
    have b42145 := hb (x 14 13)
    have b42146 := hb (x 13 1 && x 13 14)
    clear * - r42143 b42144 b42145 b42146 d42138 d42072
    omega
  have d42147 : (x 14 1).toNat = 1 := by
    have r42148 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b42149 := hb (x 14 1)
    have b42150 := hb (x 14 13)
    clear * - r42148 b42149 b42150 d42142
    omega
  have d42151 : (x 15 14).toNat = 0 := by
    have r42152 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
    have b42153 := hb (x 14 1)
    have b42154 := hb (x 15 14)
    clear * - r42152 b42153 b42154 d42147
    omega
  have d42155 : (x 15 1 && x 15 14).toNat = 0 := by
    have r42156 := hand2 (x 15 1) (x 15 14)
    have b42157 := hb (x 15 14)
    have b42158 := hb (x 15 1 && x 15 14)
    clear * - r42156 b42157 b42158 d42151
    omega
  have d42159 : (x 15 2).toNat = 0 := by
    have r42160 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b42161 := hb (x 15 2)
    have b42162 := hb (x 15 14)
    clear * - r42160 b42161 b42162 d42151
    omega
  have d42163 : (x 15 2 && x 15 13).toNat = 0 := by
    have r42164 := hand1 (x 15 2) (x 15 13)
    have b42165 := hb (x 15 2)
    have b42166 := hb (x 15 2 && x 15 13)
    clear * - r42164 b42165 b42166 d42159
    omega
  have d42167 : (x 15 12).toNat = 0 := by
    have r42168 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e42169 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e42170 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b42171 := hb (x 12 3)
    have b42172 := hb (x 13 2)
    have b42173 := hb (x 14 13)
    have b42174 := hb (x 15 12)
    clear * - r42168 e42169 e42170 b42171 b42172 b42173 b42174 d42142
    omega
  have d42175 : (x 13 2).toNat = 0 := by
    have r42176 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e42177 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e42178 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b42179 := hb (x 12 3)
    have b42180 := hb (x 13 2)
    have b42181 := hb (x 14 13)
    have b42182 := hb (x 15 12)
    clear * - r42176 e42177 e42178 b42179 b42180 b42181 b42182 d42167 d42142
    omega
  have d42183 : (x 13 12).toNat = 0 := by
    have r42184 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e42185 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e42186 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b42187 := hb (x 10 3)
    have b42188 := hb (x 11 2)
    have b42189 := hb (x 12 13)
    have b42190 := hb (x 13 12)
    clear * - r42184 e42185 e42186 b42187 b42188 b42189 b42190 d42125
    omega
  have d42191 : (x 13 4).toNat = 0 := by
    have r42192 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b42193 := hb (x 13 4)
    have b42194 := hb (x 13 12)
    clear * - r42192 b42193 b42194 d42183
    omega
  have d42195 : (x 11 2).toNat = 0 := by
    have r42196 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e42197 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e42198 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b42199 := hb (x 10 3)
    have b42200 := hb (x 11 2)
    have b42201 := hb (x 12 13)
    have b42202 := hb (x 13 12)
    clear * - r42196 e42197 e42198 b42199 b42200 b42201 b42202 d42183 d42125
    omega
  have d42203 : (x 13 13).toNat = 1 := by
    have r42204 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
    have b42205 := hb (x 11 2)
    have b42206 := hb (x 13 13)
    have b42207 := hb (x 12 1 && x 12 14)
    clear * - r42204 b42205 b42206 b42207 d42068 d42195
    omega
  have d42208 : (x 13 1).toNat = 1 := by
    have r42209 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
    have b42210 := hb (x 13 1)
    have b42211 := hb (x 13 13)
    clear * - r42209 b42210 b42211 d42203
    omega
  have d42212 : (x 14 14).toNat = 0 := by
    have r42213 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
    have b42214 := hb (x 13 1)
    have b42215 := hb (x 14 14)
    clear * - r42213 b42214 b42215 d42208
    omega
  have d42216 : (x 14 1 && x 14 14).toNat = 0 := by
    have r42217 := hand2 (x 14 1) (x 14 14)
    have b42218 := hb (x 14 14)
    have b42219 := hb (x 14 1 && x 14 14)
    clear * - r42217 b42218 b42219 d42212
    omega
  have d42220 : (x 15 13).toNat = 1 := by
    have r42221 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
    have b42222 := hb (x 13 2)
    have b42223 := hb (x 15 13)
    have b42224 := hb (x 14 1 && x 14 14)
    clear * - r42221 b42222 b42223 b42224 d42216 d42175
    omega
  have d42225 : (x 15 1).toNat = 1 := by
    have r42226 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have b42227 := hb (x 15 1)
    have b42228 := hb (x 15 13)
    clear * - r42226 b42227 b42228 d42220
    omega
  have d42229 : (x 16 14).toNat = 0 := by
    have r42230 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
    have b42231 := hb (x 15 1)
    have b42232 := hb (x 16 14)
    clear * - r42230 b42231 b42232 d42225
    omega
  have d42233 : (x 16 1 && x 16 14).toNat = 0 := by
    have r42234 := hand2 (x 16 1) (x 16 14)
    have b42235 := hb (x 16 14)
    have b42236 := hb (x 16 1 && x 16 14)
    clear * - r42234 b42235 b42236 d42229
    omega
  have d42237 : (x 17 13).toNat = 1 := by
    have r42238 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
    have b42239 := hb (x 15 2)
    have b42240 := hb (x 17 13)
    have b42241 := hb (x 16 1 && x 16 14)
    clear * - r42238 b42239 b42240 b42241 d42233 d42159
    omega
  have d42242 : (x 17 1).toNat = 1 := by
    have r42243 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
    have b42244 := hb (x 17 1)
    have b42245 := hb (x 17 13)
    clear * - r42243 b42244 b42245 d42237
    omega
  have d42246 : (x 18 14).toNat = 0 := by
    have r42247 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
    have b42248 := hb (x 17 1)
    have b42249 := hb (x 18 14)
    clear * - r42247 b42248 b42249 d42242
    omega
  have d42250 : (x 18 1 && x 18 14).toNat = 0 := by
    have r42251 := hand2 (x 18 1) (x 18 14)
    have b42252 := hb (x 18 14)
    have b42253 := hb (x 18 1 && x 18 14)
    clear * - r42251 b42252 b42253 d42246
    omega
  have d42254 : (x 18 2).toNat = 0 := by
    have r42255 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
    have b42256 := hb (x 18 2)
    have b42257 := hb (x 18 14)
    clear * - r42255 b42256 b42257 d42246
    omega
  have d42258 : (x 18 12).toNat = 0 := by
    have r42259 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e42260 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e42261 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b42262 := hb (x 15 3)
    have b42263 := hb (x 16 2)
    have b42264 := hb (x 17 13)
    have b42265 := hb (x 18 12)
    clear * - r42259 e42260 e42261 b42262 b42263 b42264 b42265 d42237
    omega
  have d42266 : (x 16 2).toNat = 0 := by
    have r42267 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e42268 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e42269 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b42270 := hb (x 15 3)
    have b42271 := hb (x 16 2)
    have b42272 := hb (x 17 13)
    have b42273 := hb (x 18 12)
    clear * - r42267 e42268 e42269 b42270 b42271 b42272 b42273 d42258 d42237
    omega
  have d42274 : (x 16 12).toNat = 0 := by
    have r42275 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e42276 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e42277 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b42278 := hb (x 13 3)
    have b42279 := hb (x 14 2)
    have b42280 := hb (x 15 13)
    have b42281 := hb (x 16 12)
    clear * - r42275 e42276 e42277 b42278 b42279 b42280 b42281 d42220
    omega
  have d42282 : (x 16 1 && x 16 12).toNat = 0 := by
    have r42283 := hand2 (x 16 1) (x 16 12)
    have b42284 := hb (x 16 12)
    have b42285 := hb (x 16 1 && x 16 12)
    clear * - r42283 b42284 b42285 d42274
    omega
  have d42286 : (x 14 2).toNat = 0 := by
    have r42287 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e42288 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e42289 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b42290 := hb (x 13 3)
    have b42291 := hb (x 14 2)
    have b42292 := hb (x 15 13)
    have b42293 := hb (x 16 12)
    clear * - r42287 e42288 e42289 b42290 b42291 b42292 b42293 d42274 d42220
    omega
  have d42294 : (x 16 13).toNat = 1 := by
    have r42295 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
    have b42296 := hb (x 14 2)
    have b42297 := hb (x 16 13)
    have b42298 := hb (x 15 1 && x 15 14)
    clear * - r42295 b42296 b42297 b42298 d42155 d42286
    omega
  have d42299 : (x 16 1).toNat = 1 := by
    have r42300 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
    have b42301 := hb (x 16 1)
    have b42302 := hb (x 16 13)
    clear * - r42300 b42301 b42302 d42294
    omega
  have d42303 : (x 17 14).toNat = 0 := by
    have r42304 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
    have b42305 := hb (x 16 1)
    have b42306 := hb (x 17 14)
    clear * - r42304 b42305 b42306 d42299
    omega
  have d42307 : (x 17 1 && x 17 14).toNat = 0 := by
    have r42308 := hand2 (x 17 1) (x 17 14)
    have b42309 := hb (x 17 14)
    have b42310 := hb (x 17 1 && x 17 14)
    clear * - r42308 b42309 b42310 d42303
    omega
  have d42311 : (x 18 13).toNat = 1 := by
    have r42312 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := hcov13 18
    have b42313 := hb (x 16 2)
    have b42314 := hb (x 18 13)
    have b42315 := hb (x 17 1 && x 17 14)
    clear * - r42312 b42313 b42314 b42315 d42307 d42266
    omega
  have d42316 : (x 19 12).toNat = 0 := by
    have r42317 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e42318 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e42319 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b42320 := hb (x 16 3)
    have b42321 := hb (x 17 2)
    have b42322 := hb (x 18 13)
    have b42323 := hb (x 19 12)
    clear * - r42317 e42318 e42319 b42320 b42321 b42322 b42323 d42311
    omega
  have d42324 : (x 17 2).toNat = 0 := by
    have r42325 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e42326 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e42327 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b42328 := hb (x 16 3)
    have b42329 := hb (x 17 2)
    have b42330 := hb (x 18 13)
    have b42331 := hb (x 19 12)
    clear * - r42325 e42326 e42327 b42328 b42329 b42330 b42331 d42316 d42311
    omega
  have d42332 : (x 19 13).toNat = 1 := by
    have r42333 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
    have b42334 := hb (x 17 2)
    have b42335 := hb (x 19 13)
    have b42336 := hb (x 18 1 && x 18 14)
    clear * - r42333 b42334 b42335 b42336 d42250 d42324
    omega
  have d42337 : (x 20 12).toNat = 0 := by
    have r42338 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e42339 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e42340 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b42341 := hb (x 17 3)
    have b42342 := hb (x 18 2)
    have b42343 := hb (x 19 13)
    have b42344 := hb (x 20 12)
    clear * - r42338 e42339 e42340 b42341 b42342 b42343 b42344 d42332 d42254
    omega
  have d42345 : (x 17 3).toNat = 0 := by
    have r42346 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e42347 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e42348 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b42349 := hb (x 17 3)
    have b42350 := hb (x 18 2)
    have b42351 := hb (x 19 13)
    have b42352 := hb (x 20 12)
    clear * - r42346 e42347 e42348 b42349 b42350 b42351 b42352 d42337 d42332 d42254
    omega
  have d42353 : (x 17 11).toNat = 0 := by
    have r42354 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b42355 := hb (x 17 3)
    have b42356 := hb (x 17 11)
    clear * - r42354 b42355 b42356 d42345
    omega
  have d42357 : (x 17 12).toNat = 0 := by
    have r42358 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e42359 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e42360 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b42361 := hb (x 14 3)
    have b42362 := hb (x 15 2)
    have b42363 := hb (x 16 13)
    have b42364 := hb (x 17 12)
    clear * - r42358 e42359 e42360 b42361 b42362 b42363 b42364 d42294 d42159
    omega
  have d42365 : (x 14 3).toNat = 0 := by
    have r42366 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
    have e42367 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e42368 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b42369 := hb (x 14 3)
    have b42370 := hb (x 15 2)
    have b42371 := hb (x 16 13)
    have b42372 := hb (x 17 12)
    clear * - r42366 e42367 e42368 b42369 b42370 b42371 b42372 d42357 d42294 d42159
    omega
  have d42373 : (x 14 3 && x 14 14).toNat = 0 := by
    have r42374 := hand1 (x 14 3) (x 14 14)
    have b42375 := hb (x 14 3)
    have b42376 := hb (x 14 3 && x 14 14)
    clear * - r42374 b42375 b42376 d42365
    omega
  have r42377 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
  have b42378 := hb (x 13 4)
  have b42379 := hb (x 17 11)
  have b42380 := hb (x 16 1 && x 16 12)
  have b42381 := hb (x 15 2 && x 15 13)
  have b42382 := hb (x 14 3 && x 14 14)
  linarith only [r42377, b42378, b42379, b42380, b42381, b42382, d42353, d42282, d42163, d42373, d42191]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 13).toNat = 1)
    (g1 : (x 1 2).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 0 1 && x 0 14).toNat = 0)
    (g4 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4
