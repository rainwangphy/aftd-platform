import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b001

Topic: combinatorics   Node: 3c56d0e49d4f

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 24 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 11).toNat = 0)
    (g1 : (x (-3) 13).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 5).toNat = 0)
    (g5 : (x 0 7).toNat = 0)
    (g6 : (x 0 8).toNat = 1)
    (g7 : (x 0 9).toNat = 0)
    (g8 : (x 0 10).toNat = 0)
    (g9 : (x 0 13).toNat = 0)
    (g10 : (x 0 14).toNat = 1)
    (g11 : (x 0 13 && x 0 14).toNat = 0)
    (g12 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g13 : (x (-3) 3 && x (-3) 8).toNat = 0)
    (g14 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g15 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g16 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g17 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g18 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g19 : (x 0 5 && x 0 14).toNat = 0)
    (g20 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g21 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g22 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g23 : (x 0 1 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d14849 : (x (-2) 10).toNat = 0 := by
    have r14850 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
    have e14851 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e14852 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e14853 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e14854 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e14855 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e14856 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b14857 := hb (x (-7) 7)
    have b14858 := hb (x (-6) 6)
    have b14859 := hb (x (-5) 5)
    have b14860 := hb (x (-4) 4)
    have b14861 := hb (x (-3) 11)
    have b14862 := hb (x (-2) 10)
    have b14863 := hb (x (-1) 9)
    have b14864 := hb (x 0 8)
    clear * - r14850 e14851 e14852 e14853 e14854 e14855 e14856 b14857 b14858 b14859 b14860 b14861 b14862 b14863 b14864 g6 g2 g0
    omega
  have d14865 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r14866 := hand2 (x (-2) 1) (x (-2) 10)
    have b14867 := hb (x (-2) 10)
    have b14868 := hb (x (-2) 1 && x (-2) 10)
    clear * - r14866 b14867 b14868 d14849
    omega
  have d14869 : (x (-4) 4).toNat = 0 := by
    have r14870 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
    have e14871 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e14872 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e14873 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e14874 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e14875 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e14876 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b14877 := hb (x (-7) 7)
    have b14878 := hb (x (-6) 6)
    have b14879 := hb (x (-5) 5)
    have b14880 := hb (x (-4) 4)
    have b14881 := hb (x (-3) 11)
    have b14882 := hb (x (-2) 10)
    have b14883 := hb (x (-1) 9)
    have b14884 := hb (x 0 8)
    clear * - r14870 e14871 e14872 e14873 e14874 e14875 e14876 b14877 b14878 b14879 b14880 b14881 b14882 b14883 b14884 g6 g2 d14849 g0
    omega
  have d14885 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r14886 := hand1 (x (-4) 4) (x (-4) 14)
    have b14887 := hb (x (-4) 4)
    have b14888 := hb (x (-4) 4 && x (-4) 14)
    clear * - r14886 b14887 b14888 d14869
    omega
  have d14889 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
    have r14890 := hand1 (x (-4) 4) (x (-4) 13)
    have b14891 := hb (x (-4) 4)
    have b14892 := hb (x (-4) 4 && x (-4) 13)
    clear * - r14890 b14891 b14892 d14869
    omega
  have d14893 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
    have r14894 := hand1 (x (-4) 4) (x (-4) 11)
    have b14895 := hb (x (-4) 4)
    have b14896 := hb (x (-4) 4 && x (-4) 11)
    clear * - r14894 b14895 b14896 d14869
    omega
  have d14897 : (x (-4) 4 && x (-4) 9).toNat = 0 := by
    have r14898 := hand1 (x (-4) 4) (x (-4) 9)
    have b14899 := hb (x (-4) 4)
    have b14900 := hb (x (-4) 4 && x (-4) 9)
    clear * - r14898 b14899 b14900 d14869
    omega
  have d14901 : (x (-5) 5).toNat = 0 := by
    have r14902 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
    have e14903 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e14904 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e14905 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e14906 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e14907 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e14908 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b14909 := hb (x (-7) 7)
    have b14910 := hb (x (-6) 6)
    have b14911 := hb (x (-5) 5)
    have b14912 := hb (x (-4) 4)
    have b14913 := hb (x (-3) 11)
    have b14914 := hb (x (-2) 10)
    have b14915 := hb (x (-1) 9)
    have b14916 := hb (x 0 8)
    clear * - r14902 e14903 e14904 e14905 e14906 e14907 e14908 b14909 b14910 b14911 b14912 b14913 b14914 b14915 b14916 g6 g2 d14849 g0 d14869
    omega
  have d14917 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
    have r14918 := hand1 (x (-5) 5) (x (-5) 14)
    have b14919 := hb (x (-5) 5)
    have b14920 := hb (x (-5) 5 && x (-5) 14)
    clear * - r14918 b14919 b14920 d14901
    omega
  have d14921 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
    have r14922 := hand1 (x (-5) 5) (x (-5) 12)
    have b14923 := hb (x (-5) 5)
    have b14924 := hb (x (-5) 5 && x (-5) 12)
    clear * - r14922 b14923 b14924 d14901
    omega
  have d14925 : (x (-5) 5 && x (-5) 10).toNat = 0 := by
    have r14926 := hand1 (x (-5) 5) (x (-5) 10)
    have b14927 := hb (x (-5) 5)
    have b14928 := hb (x (-5) 5 && x (-5) 10)
    clear * - r14926 b14927 b14928 d14901
    omega
  have d14929 : (x (-2) 2 && x (-2) 12).toNat = 1 := by
    have r14930 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
    have b14931 := hb (x (-5) 5)
    have b14932 := hb (x 0 10)
    have b14933 := hb (x (-1) 1 && x (-1) 11)
    have b14934 := hb (x (-2) 2 && x (-2) 12)
    have b14935 := hb (x (-3) 3 && x (-3) 13)
    have b14936 := hb (x (-4) 4 && x (-4) 14)
    clear * - r14930 b14931 b14932 b14933 b14934 b14935 b14936 g8 g20 g21 d14885 d14901
    omega
  have d14937 : (x (-2) 12).toNat = 1 := by
    have r14938 := hand2 (x (-2) 2) (x (-2) 12)
    have b14939 := hb (x (-2) 12)
    have b14940 := hb (x (-2) 2 && x (-2) 12)
    clear * - r14938 b14939 b14940 d14929
    omega
  have d14941 : (x (-4) 2).toNat = 0 := by
    have r14942 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
    have e14943 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e14944 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b14945 := hb (x (-5) 3)
    have b14946 := hb (x (-4) 2)
    have b14947 := hb (x (-3) 13)
    have b14948 := hb (x (-2) 12)
    clear * - r14942 e14943 e14944 b14945 b14946 b14947 b14948 d14937 g1
    omega
  have d14949 : (x (-2) 13).toNat = 1 := by
    have r14950 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := hcov13 (-2)
    have b14951 := hb (x (-4) 2)
    have b14952 := hb (x (-2) 13)
    have b14953 := hb (x (-3) 1 && x (-3) 14)
    clear * - r14950 b14951 b14952 b14953 g22 d14941
    omega
  have d14954 : (x (-2) 1).toNat = 1 := by
    have r14955 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b14956 := hb (x (-2) 1)
    have b14957 := hb (x (-2) 13)
    clear * - r14955 b14956 b14957 d14949
    omega
  have d14958 : (x (-1) 14).toNat = 0 := by
    have r14959 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
    have b14960 := hb (x (-2) 1)
    have b14961 := hb (x (-1) 14)
    clear * - r14959 b14960 b14961 d14954
    omega
  have d14962 : (x (-1) 6).toNat = 0 := by
    have r14963 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b14964 := hb (x (-1) 6)
    have b14965 := hb (x (-1) 14)
    clear * - r14963 b14964 b14965 d14958
    omega
  have d14966 : (x (-1) 2 && x (-1) 6).toNat = 0 := by
    have r14967 := hand2 (x (-1) 2) (x (-1) 6)
    have b14968 := hb (x (-1) 6)
    have b14969 := hb (x (-1) 2 && x (-1) 6)
    clear * - r14967 b14968 b14969 d14962
    omega
  have d14970 : (x (-1) 2).toNat = 0 := by
    have r14971 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b14972 := hb (x (-1) 2)
    have b14973 := hb (x (-1) 14)
    clear * - r14971 b14972 b14973 d14958
    omega
  have d14974 : (x (-1) 10).toNat = 0 := by
    have r14975 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b14976 := hb (x (-1) 2)
    have b14977 := hb (x (-1) 10)
    clear * - r14975 b14976 b14977 d14970
    omega
  have d14978 : (x 1 13).toNat = 1 := by
    have r14979 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
    have b14980 := hb (x (-1) 2)
    have b14981 := hb (x 1 13)
    have b14982 := hb (x 0 1 && x 0 14)
    clear * - r14979 b14980 b14981 b14982 g23 d14970
    omega
  have d14983 : (x 2 12).toNat = 0 := by
    have r14984 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
    have e14985 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e14986 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b14987 := hb (x (-1) 3)
    have b14988 := hb (x 0 2)
    have b14989 := hb (x 1 13)
    have b14990 := hb (x 2 12)
    clear * - r14984 e14985 e14986 b14987 b14988 b14989 b14990 d14978 g3
    omega
  have d14991 : (x 2 3 && x 2 12).toNat = 0 := by
    have r14992 := hand2 (x 2 3) (x 2 12)
    have b14993 := hb (x 2 12)
    have b14994 := hb (x 2 3 && x 2 12)
    clear * - r14992 b14993 b14994 d14983
    omega
  have d14995 : (x 2 11 && x 2 12).toNat = 0 := by
    have r14996 := hand2 (x 2 11) (x 2 12)
    have b14997 := hb (x 2 12)
    have b14998 := hb (x 2 11 && x 2 12)
    clear * - r14996 b14997 b14998 d14983
    omega
  have d14999 : (x (-1) 12).toNat = 0 := by
    have r15000 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
    have e15001 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e15002 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b15003 := hb (x (-4) 3)
    have b15004 := hb (x (-3) 2)
    have b15005 := hb (x (-2) 13)
    have b15006 := hb (x (-1) 12)
    clear * - r15000 e15001 e15002 b15003 b15004 b15005 b15006 d14949
    omega
  have d15007 : (x (-3) 2).toNat = 0 := by
    have r15008 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
    have e15009 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e15010 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b15011 := hb (x (-4) 3)
    have b15012 := hb (x (-3) 2)
    have b15013 := hb (x (-2) 13)
    have b15014 := hb (x (-1) 12)
    clear * - r15008 e15009 e15010 b15011 b15012 b15013 b15014 d14999 d14949
    omega
  have d15015 : (x (-3) 10).toNat = 0 := by
    have r15016 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
    have b15017 := hb (x (-3) 2)
    have b15018 := hb (x (-3) 10)
    clear * - r15016 b15017 b15018 d15007
    omega
  have d15019 : (x (-4) 3).toNat = 0 := by
    have r15020 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
    have e15021 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e15022 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b15023 := hb (x (-4) 3)
    have b15024 := hb (x (-3) 2)
    have b15025 := hb (x (-2) 13)
    have b15026 := hb (x (-1) 12)
    clear * - r15020 e15021 e15022 b15023 b15024 b15025 b15026 d14999 d14949 d15007
    omega
  have d15027 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
    have r15028 := hand1 (x (-4) 3) (x (-4) 12)
    have b15029 := hb (x (-4) 3)
    have b15030 := hb (x (-4) 3 && x (-4) 12)
    clear * - r15028 b15029 b15030 d15019
    omega
  have d15031 : (x (-4) 11).toNat = 0 := by
    have r15032 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b15033 := hb (x (-4) 3)
    have b15034 := hb (x (-4) 11)
    clear * - r15032 b15033 b15034 d15019
    omega
  have d15035 : (x (-6) 6).toNat = 0 := by
    have r15036 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
    have e15037 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e15038 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e15039 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e15040 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e15041 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e15042 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b15043 := hb (x (-7) 7)
    have b15044 := hb (x (-6) 6)
    have b15045 := hb (x (-5) 5)
    have b15046 := hb (x (-4) 4)
    have b15047 := hb (x (-3) 11)
    have b15048 := hb (x (-2) 10)
    have b15049 := hb (x (-1) 9)
    have b15050 := hb (x 0 8)
    clear * - r15036 e15037 e15038 e15039 e15040 e15041 e15042 b15043 b15044 b15045 b15046 b15047 b15048 b15049 b15050 g6 g2 d14849 g0 d14869 d14901
    omega
  have d15051 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
    have r15052 := hand1 (x (-6) 6) (x (-6) 13)
    have b15053 := hb (x (-6) 6)
    have b15054 := hb (x (-6) 6 && x (-6) 13)
    clear * - r15052 b15053 b15054 d15035
    omega
  have d15055 : (x (-6) 6 && x (-6) 11).toNat = 0 := by
    have r15056 := hand1 (x (-6) 6) (x (-6) 11)
    have b15057 := hb (x (-6) 6)
    have b15058 := hb (x (-6) 6 && x (-6) 11)
    clear * - r15056 b15057 b15058 d15035
    omega
  have d15059 : (x (-2) 2 && x (-2) 11).toNat = 1 := by
    have r15060 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := hcov9 0
    have b15061 := hb (x (-6) 6)
    have b15062 := hb (x 0 9)
    have b15063 := hb (x (-1) 1 && x (-1) 10)
    have b15064 := hb (x (-2) 2 && x (-2) 11)
    have b15065 := hb (x (-3) 3 && x (-3) 12)
    have b15066 := hb (x (-4) 4 && x (-4) 13)
    have b15067 := hb (x (-5) 5 && x (-5) 14)
    clear * - r15060 b15061 b15062 b15063 b15064 b15065 b15066 b15067 g7 g17 g18 d14889 d14917 d15035
    omega
  have d15068 : (x (-2) 11).toNat = 1 := by
    have r15069 := hand2 (x (-2) 2) (x (-2) 11)
    have b15070 := hb (x (-2) 11)
    have b15071 := hb (x (-2) 2 && x (-2) 11)
    clear * - r15069 b15070 b15071 d15059
    omega
  have d15072 : (x (-2) 3).toNat = 1 := by
    have r15073 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b15074 := hb (x (-2) 3)
    have b15075 := hb (x (-2) 11)
    clear * - r15073 b15074 b15075 d15068
    omega
  have d15076 : (x 1 12).toNat = 0 := by
    have r15077 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e15078 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e15079 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b15080 := hb (x (-2) 3)
    have b15081 := hb (x (-1) 2)
    have b15082 := hb (x 0 13)
    have b15083 := hb (x 1 12)
    clear * - r15077 e15078 e15079 b15080 b15081 b15082 b15083 g9 d14970 d15072
    omega
  have d15084 : (x 1 12 && x 1 13).toNat = 0 := by
    have r15085 := hand1 (x 1 12) (x 1 13)
    have b15086 := hb (x 1 12)
    have b15087 := hb (x 1 12 && x 1 13)
    clear * - r15085 b15086 b15087 d15076
    omega
  have d15088 : (x 1 4).toNat = 0 := by
    have r15089 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b15090 := hb (x 1 4)
    have b15091 := hb (x 1 12)
    clear * - r15089 b15090 b15091 d15076
    omega
  have d15092 : (x 1 4 && x 1 13).toNat = 0 := by
    have r15093 := hand1 (x 1 4) (x 1 13)
    have b15094 := hb (x 1 4)
    have b15095 := hb (x 1 4 && x 1 13)
    clear * - r15093 b15094 b15095 d15088
    omega
  have d15096 : (x 1 8).toNat = 0 := by
    have r15097 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e15098 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e15099 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e15100 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e15101 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e15102 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e15103 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b15104 := hb (x (-6) 7)
    have b15105 := hb (x (-5) 6)
    have b15106 := hb (x (-4) 5)
    have b15107 := hb (x (-3) 4)
    have b15108 := hb (x (-2) 11)
    have b15109 := hb (x (-1) 10)
    have b15110 := hb (x 0 9)
    have b15111 := hb (x 1 8)
    clear * - r15097 e15098 e15099 e15100 e15101 e15102 e15103 b15104 b15105 b15106 b15107 b15108 b15109 b15110 b15111 g7 d14974 d15068
    omega
  have d15112 : (x (-3) 4).toNat = 0 := by
    have r15113 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e15114 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e15115 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e15116 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e15117 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e15118 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e15119 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b15120 := hb (x (-6) 7)
    have b15121 := hb (x (-5) 6)
    have b15122 := hb (x (-4) 5)
    have b15123 := hb (x (-3) 4)
    have b15124 := hb (x (-2) 11)
    have b15125 := hb (x (-1) 10)
    have b15126 := hb (x 0 9)
    have b15127 := hb (x 1 8)
    clear * - r15113 e15114 e15115 e15116 e15117 e15118 e15119 b15120 b15121 b15122 b15123 b15124 b15125 b15126 b15127 d15096 g7 d14974 d15068
    omega
  have d15128 : (x (-3) 4 && x (-3) 8).toNat = 0 := by
    have r15129 := hand1 (x (-3) 4) (x (-3) 8)
    have b15130 := hb (x (-3) 4)
    have b15131 := hb (x (-3) 4 && x (-3) 8)
    clear * - r15129 b15130 b15131 d15112
    omega
  have d15132 : (x (-4) 5).toNat = 0 := by
    have r15133 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e15134 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e15135 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e15136 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e15137 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e15138 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e15139 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b15140 := hb (x (-6) 7)
    have b15141 := hb (x (-5) 6)
    have b15142 := hb (x (-4) 5)
    have b15143 := hb (x (-3) 4)
    have b15144 := hb (x (-2) 11)
    have b15145 := hb (x (-1) 10)
    have b15146 := hb (x 0 9)
    have b15147 := hb (x 1 8)
    clear * - r15133 e15134 e15135 e15136 e15137 e15138 e15139 b15140 b15141 b15142 b15143 b15144 b15145 b15146 b15147 d15096 g7 d14974 d15068 d15112
    omega
  have d15148 : (x (-4) 5 && x (-4) 9).toNat = 0 := by
    have r15149 := hand1 (x (-4) 5) (x (-4) 9)
    have b15150 := hb (x (-4) 5)
    have b15151 := hb (x (-4) 5 && x (-4) 9)
    clear * - r15149 b15150 b15151 d15132
    omega
  have d15152 : (x (-5) 6).toNat = 0 := by
    have r15153 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e15154 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e15155 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e15156 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e15157 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e15158 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e15159 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b15160 := hb (x (-6) 7)
    have b15161 := hb (x (-5) 6)
    have b15162 := hb (x (-4) 5)
    have b15163 := hb (x (-3) 4)
    have b15164 := hb (x (-2) 11)
    have b15165 := hb (x (-1) 10)
    have b15166 := hb (x 0 9)
    have b15167 := hb (x 1 8)
    clear * - r15153 e15154 e15155 e15156 e15157 e15158 e15159 b15160 b15161 b15162 b15163 b15164 b15165 b15166 b15167 d15096 g7 d14974 d15068 d15112 d15132
    omega
  have d15168 : (x (-5) 6 && x (-5) 10).toNat = 0 := by
    have r15169 := hand1 (x (-5) 6) (x (-5) 10)
    have b15170 := hb (x (-5) 6)
    have b15171 := hb (x (-5) 6 && x (-5) 10)
    clear * - r15169 b15170 b15171 d15152
    omega
  have d15172 : (x (-6) 7).toNat = 0 := by
    have r15173 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
    have e15174 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e15175 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e15176 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e15177 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e15178 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e15179 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b15180 := hb (x (-6) 7)
    have b15181 := hb (x (-5) 6)
    have b15182 := hb (x (-4) 5)
    have b15183 := hb (x (-3) 4)
    have b15184 := hb (x (-2) 11)
    have b15185 := hb (x (-1) 10)
    have b15186 := hb (x 0 9)
    have b15187 := hb (x 1 8)
    clear * - r15173 e15174 e15175 e15176 e15177 e15178 e15179 b15180 b15181 b15182 b15183 b15184 b15185 b15186 b15187 d15096 g7 d14974 d15068 d15112 d15132 d15152
    omega
  have d15188 : (x (-6) 7 && x (-6) 11).toNat = 0 := by
    have r15189 := hand1 (x (-6) 7) (x (-6) 11)
    have b15190 := hb (x (-6) 7)
    have b15191 := hb (x (-6) 7 && x (-6) 11)
    clear * - r15189 b15190 b15191 d15172
    omega
  have d15192 : (x (-7) 7).toNat = 0 := by
    have r15193 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
    have e15194 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e15195 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e15196 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e15197 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e15198 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e15199 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b15200 := hb (x (-7) 7)
    have b15201 := hb (x (-6) 6)
    have b15202 := hb (x (-5) 5)
    have b15203 := hb (x (-4) 4)
    have b15204 := hb (x (-3) 11)
    have b15205 := hb (x (-2) 10)
    have b15206 := hb (x (-1) 9)
    have b15207 := hb (x 0 8)
    clear * - r15193 e15194 e15195 e15196 e15197 e15198 e15199 b15200 b15201 b15202 b15203 b15204 b15205 b15206 b15207 g6 g2 d14849 g0 d14869 d14901 d15035
    omega
  have d15208 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
    have r15209 := hand1 (x (-7) 7) (x (-7) 14)
    have b15210 := hb (x (-7) 7)
    have b15211 := hb (x (-7) 7 && x (-7) 14)
    clear * - r15209 b15210 b15211 d15192
    omega
  have d15212 : (x (-7) 7 && x (-7) 12).toNat = 0 := by
    have r15213 := hand1 (x (-7) 7) (x (-7) 12)
    have b15214 := hb (x (-7) 7)
    have b15215 := hb (x (-7) 7 && x (-7) 12)
    clear * - r15213 b15214 b15215 d15192
    omega
  have r15216 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := hcount 14
  have r15217 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := hd8 (-8)
  have e15218 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
  have e15219 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
  have e15220 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
  have e15221 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
  have e15222 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
  have e15223 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
  have r15224 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := hd8 (-7)
  have e15225 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
  have e15226 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
  have e15227 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
  have e15228 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
  have e15229 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
  have e15230 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
  have r15231 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := hd8 (-1)
  have e15232 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
  have e15233 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
  have e15234 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
  have e15235 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
  have e15236 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
  have e15237 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
  have r15238 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := hd8 5
  have e15239 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
  have e15240 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
  have e15241 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
  have e15242 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
  have e15243 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
  have e15244 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
  have r15245 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
  have e15246 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
  have e15247 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
  have r15248 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
  have e15249 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
  have e15250 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
  have r15251 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := hd14 (-7)
  have r15252 : 1 ≤ (x 13 1).toNat + (x 12 1 && x 12 2).toNat + (x 11 2 && x 11 3).toNat + (x 10 3 && x 10 4).toNat + (x 9 4 && x 9 5).toNat + (x 8 5 && x 8 6).toNat + (x 7 6 && x 7 7).toNat + (x 6 7 && x 6 8).toNat + (x 5 8 && x 5 9).toNat + (x 4 9 && x 4 10).toNat + (x 3 10 && x 3 11).toNat + (x 2 11 && x 2 12).toNat + (x 1 12 && x 1 13).toNat + (x 0 13 && x 0 14).toNat + (x (-1) 14).toNat := hcov1 13
  have r15253 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := hcov4 1
  have e15254 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
  have e15255 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
  have r15256 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := hcov5 0
  have r15257 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := hcov7 0
  have r15258 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := hcov9 (-1)
  have r15259 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := hcov9 5
  have r15260 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := hcov10 (-7)
  have r15261 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
  have r15262 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
  have r15263 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
  have r15264 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
  have r15265 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
  have r15266 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
  have r15267 := hand2 (x 12 1) (x 12 2)
  have r15268 := hand2 (x 11 2) (x 11 3)
  have r15269 := hand2 (x 10 3) (x 10 4)
  have r15270 := hand2 (x 9 4) (x 9 5)
  have r15271 := hand2 (x 8 5) (x 8 6)
  have r15272 := hand2 (x 7 6) (x 7 7)
  have r15273 := hand2 (x 6 7) (x 6 8)
  have r15274 := hand1 (x 5 8) (x 5 9)
  have r15275 := hand1 (x 4 9) (x 4 10)
  have r15276 := hand1 (x 3 10) (x 3 11)
  have r15277 := hand2 (x (-2) 3) (x (-2) 7)
  have r15278 := hand2 (x (-7) 8) (x (-7) 12)
  have r15279 := hand1 (x (-8) 9) (x (-8) 13)
  have r15280 := hand2 (x (-2) 2) (x (-2) 7)
  have r15281 := hand2 (x (-8) 8) (x (-8) 13)
  have r15282 := hand1 (x (-9) 9) (x (-9) 14)
  have r15283 := hand2 (x (-2) 2) (x (-2) 9)
  have r15284 := hand1 (x (-5) 4) (x (-5) 13)
  have r15285 := hand1 (x (-6) 5) (x (-6) 14)
  have r15286 := hand2 (x 4 1) (x 4 10)
  have r15287 := hand2 (x 3 2) (x 3 11)
  have r15288 := hand2 (x (-8) 1) (x (-8) 11)
  have r15289 := hand1 (x (-9) 2) (x (-9) 12)
  have r15290 := hand1 (x (-10) 3) (x (-10) 13)
  have r15291 := hand1 (x (-11) 4) (x (-11) 14)
  have b15292 := hb (x (-15) 7)
  have b15293 := hb (x (-14) 6)
  have b15294 := hb (x (-14) 7)
  have b15295 := hb (x (-13) 5)
  have b15296 := hb (x (-13) 6)
  have b15297 := hb (x (-12) 4)
  have b15298 := hb (x (-12) 5)
  have b15299 := hb (x (-11) 4)
  have b15300 := hb (x (-11) 11)
  have b15301 := hb (x (-10) 3)
  have b15302 := hb (x (-10) 10)
  have b15303 := hb (x (-10) 11)
  have b15304 := hb (x (-9) 2)
  have b15305 := hb (x (-9) 9)
  have b15306 := hb (x (-9) 10)
  have b15307 := hb (x (-8) 1)
  have b15308 := hb (x (-8) 3)
  have b15309 := hb (x (-8) 7)
  have b15310 := hb (x (-8) 8)
  have b15311 := hb (x (-8) 9)
  have b15312 := hb (x (-8) 11)
  have b15313 := hb (x (-8) 13)
  have b15314 := hb (x (-7) 2)
  have b15315 := hb (x (-7) 6)
  have b15316 := hb (x (-7) 8)
  have b15317 := hb (x (-7) 10)
  have b15318 := hb (x (-7) 12)
  have b15319 := hb (x (-7) 14)
  have b15320 := hb (x (-6) 5)
  have b15321 := hb (x (-6) 13)
  have b15322 := hb (x (-5) 4)
  have b15323 := hb (x (-5) 12)
  have b15324 := hb (x (-4) 11)
  have b15325 := hb (x (-3) 10)
  have b15326 := hb (x (-2) 7)
  have b15327 := hb (x (-2) 9)
  have b15328 := hb (x (-1) 6)
  have b15329 := hb (x (-1) 8)
  have b15330 := hb (x (-1) 9)
  have b15331 := hb (x (-1) 14)
  have b15332 := hb (x 0 5)
  have b15333 := hb (x 0 7)
  have b15334 := hb (x 0 14)
  have b15335 := hb (x 1 4)
  have b15336 := hb (x 1 13)
  have b15337 := hb (x 2 11)
  have b15338 := hb (x 2 12)
  have b15339 := hb (x 3 10)
  have b15340 := hb (x 3 11)
  have b15341 := hb (x 4 9)
  have b15342 := hb (x 4 10)
  have b15343 := hb (x 5 8)
  have b15344 := hb (x 5 9)
  have b15345 := hb (x 6 8)
  have b15346 := hb (x 7 7)
  have b15347 := hb (x 8 6)
  have b15348 := hb (x 9 5)
  have b15349 := hb (x 10 4)
  have b15350 := hb (x 11 3)
  have b15351 := hb (x 12 2)
  have b15352 := hb (x 13 1)
  have b15353 := hb (x 12 1 && x 12 2)
  have b15354 := hb (x 11 2 && x 11 3)
  have b15355 := hb (x 10 3 && x 10 4)
  have b15356 := hb (x 9 4 && x 9 5)
  have b15357 := hb (x 8 5 && x 8 6)
  have b15358 := hb (x 7 6 && x 7 7)
  have b15359 := hb (x 6 7 && x 6 8)
  have b15360 := hb (x 5 8 && x 5 9)
  have b15361 := hb (x 4 9 && x 4 10)
  have b15362 := hb (x 3 10 && x 3 11)
  have b15363 := hb (x 2 11 && x 2 12)
  have b15364 := hb (x 1 12 && x 1 13)
  have b15365 := hb (x 0 13 && x 0 14)
  have b15366 := hb (x (-1) 2 && x (-1) 6)
  have b15367 := hb (x (-2) 3 && x (-2) 7)
  have b15368 := hb (x (-3) 4 && x (-3) 8)
  have b15369 := hb (x (-4) 5 && x (-4) 9)
  have b15370 := hb (x (-5) 6 && x (-5) 10)
  have b15371 := hb (x (-6) 7 && x (-6) 11)
  have b15372 := hb (x (-7) 8 && x (-7) 12)
  have b15373 := hb (x (-8) 9 && x (-8) 13)
  have b15374 := hb (x (-1) 1 && x (-1) 6)
  have b15375 := hb (x (-2) 2 && x (-2) 7)
  have b15376 := hb (x (-3) 3 && x (-3) 8)
  have b15377 := hb (x (-4) 4 && x (-4) 9)
  have b15378 := hb (x (-5) 5 && x (-5) 10)
  have b15379 := hb (x (-6) 6 && x (-6) 11)
  have b15380 := hb (x (-7) 7 && x (-7) 12)
  have b15381 := hb (x (-8) 8 && x (-8) 13)
  have b15382 := hb (x (-9) 9 && x (-9) 14)
  have b15383 := hb (x (-1) 1 && x (-1) 8)
  have b15384 := hb (x (-2) 2 && x (-2) 9)
  have b15385 := hb (x (-3) 3 && x (-3) 10)
  have b15386 := hb (x (-4) 4 && x (-4) 11)
  have b15387 := hb (x (-5) 5 && x (-5) 12)
  have b15388 := hb (x (-6) 6 && x (-6) 13)
  have b15389 := hb (x (-7) 7 && x (-7) 14)
  have b15390 := hb (x (-2) 1 && x (-2) 10)
  have b15391 := hb (x (-3) 2 && x (-3) 11)
  have b15392 := hb (x (-4) 3 && x (-4) 12)
  have b15393 := hb (x (-5) 4 && x (-5) 13)
  have b15394 := hb (x (-6) 5 && x (-6) 14)
  have b15395 := hb (x 4 1 && x 4 10)
  have b15396 := hb (x 3 2 && x 3 11)
  have b15397 := hb (x 2 3 && x 2 12)
  have b15398 := hb (x 1 4 && x 1 13)
  have b15399 := hb (x 0 5 && x 0 14)
  have b15400 := hb (x (-8) 1 && x (-8) 11)
  have b15401 := hb (x (-9) 2 && x (-9) 12)
  have b15402 := hb (x (-10) 3 && x (-10) 13)
  have b15403 := hb (x (-11) 4 && x (-11) 14)
  linarith only [r15216, r15217, e15218, e15219, e15220, e15221, e15222, e15223, r15224, e15225, e15226, e15227, e15228, e15229, e15230, r15231, e15232, e15233, e15234, e15235, e15236, e15237, r15238, e15239, e15240, e15241, e15242, e15243, e15244, r15245, e15246, e15247, r15248, e15249, e15250, r15251, r15252, r15253, e15254, e15255, r15256, r15257, r15258, r15259, r15260, r15261, r15262, r15263, r15264, r15265, r15266, r15267, r15268, r15269, r15270, r15271, r15272, r15273, r15274, r15275, r15276, r15277, r15278, r15279, r15280, r15281, r15282, r15283, r15284, r15285, r15286, r15287, r15288, r15289, r15290, r15291, b15292, b15293, b15294, b15295, b15296, b15297, b15298, b15299, b15300, b15301, b15302, b15303, b15304, b15305, b15306, b15307, b15308, b15309, b15310, b15311, b15312, b15313, b15314, b15315, b15316, b15317, b15318, b15319, b15320, b15321, b15322, b15323, b15324, b15325, b15326, b15327, b15328, b15329, b15330, b15331, b15332, b15333, b15334, b15335, b15336, b15337, b15338, b15339, b15340, b15341, b15342, b15343, b15344, b15345, b15346, b15347, b15348, b15349, b15350, b15351, b15352, b15353, b15354, b15355, b15356, b15357, b15358, b15359, b15360, b15361, b15362, b15363, b15364, b15365, b15366, b15367, b15368, b15369, b15370, b15371, b15372, b15373, b15374, b15375, b15376, b15377, b15378, b15379, b15380, b15381, b15382, b15383, b15384, b15385, b15386, b15387, b15388, b15389, b15390, b15391, b15392, b15393, b15394, b15395, b15396, b15397, b15398, b15399, b15400, b15401, b15402, b15403, d15031, d15015, d14962, g2, d14958, g4, g5, g10, d15088, d14978, d14983, d14995, d15084, g11, d14966, d15128, d15148, d15168, d15188, g12, g13, d14897, d14925, d15055, d15212, g14, g15, d14893, d14921, d15051, d15208, d14865, g16, d15027, d14991, d15092, g19]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 11).toNat = 0)
    (g1 : (x (-3) 13).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 5).toNat = 0)
    (g5 : (x 0 7).toNat = 0)
    (g6 : (x 0 8).toNat = 1)
    (g7 : (x 0 9).toNat = 0)
    (g8 : (x 0 10).toNat = 0)
    (g9 : (x 0 13).toNat = 0)
    (g10 : (x 0 14).toNat = 1)
    (g11 : (x 0 13 && x 0 14).toNat = 0)
    (g12 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g13 : (x (-3) 3 && x (-3) 8).toNat = 0)
    (g14 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g15 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g16 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g17 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g18 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g19 : (x 0 5 && x 0 14).toNat = 0)
    (g20 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g21 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g22 : (x (-3) 1 && x (-3) 14).toNat = 0)
    (g23 : (x 0 1 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23
