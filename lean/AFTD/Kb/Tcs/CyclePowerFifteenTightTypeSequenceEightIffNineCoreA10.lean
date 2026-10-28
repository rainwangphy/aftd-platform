import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a10

Topic: combinatorics   Node: 9cef69728135

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 56 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0111101, cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a011111.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0111101 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x 0 6).toNat = 1)
    (g2 : (x 1 2).toNat = 0)
    (g3 : (x 1 5).toNat = 0)
    (g4 : (x 2 4).toNat = 0)
    (g5 : (x 3 4).toNat = 0)
    (g6 : (x 5 2).toNat = 0)
    (g7 : (x 6 13).toNat = 0)
    (g8 : (x 2 2 && x 2 12).toNat = 0)
    (g9 : (x 1 3 && x 1 13).toNat = 0)
    (g10 : (x 0 4 && x 0 14).toNat = 0)
    (g11 : (x 7 2 && x 7 12).toNat = 0)
    (g12 : (x 6 3 && x 6 13).toNat = 0)
    (g13 : (x 5 2 && x 5 13).toNat = 0)
    (g14 : (x 7 1 && x 7 12).toNat = 0)
    (g15 : (x 6 2 && x 6 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d53838 : (x 6 8).toNat = 0 := by
    have r53839 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e53840 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e53841 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e53842 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e53843 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e53844 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e53845 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b53846 := hb (x (-1) 7)
    have b53847 := hb (x 0 6)
    have b53848 := hb (x 1 5)
    have b53849 := hb (x 2 4)
    have b53850 := hb (x 3 11)
    have b53851 := hb (x 4 10)
    have b53852 := hb (x 5 9)
    have b53853 := hb (x 6 8)
    clear * - r53839 e53840 e53841 e53842 e53843 e53844 e53845 b53846 b53847 b53848 b53849 b53850 b53851 b53852 b53853 g4 g3 g1
    omega
  have d53854 : (x 5 9).toNat = 0 := by
    have r53855 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e53856 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e53857 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e53858 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e53859 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e53860 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e53861 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b53862 := hb (x (-1) 7)
    have b53863 := hb (x 0 6)
    have b53864 := hb (x 1 5)
    have b53865 := hb (x 2 4)
    have b53866 := hb (x 3 11)
    have b53867 := hb (x 4 10)
    have b53868 := hb (x 5 9)
    have b53869 := hb (x 6 8)
    clear * - r53855 e53856 e53857 e53858 e53859 e53860 e53861 b53862 b53863 b53864 b53865 b53866 b53867 b53868 b53869 d53838 g4 g3 g1
    omega
  have d53870 : (x 4 10).toNat = 0 := by
    have r53871 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e53872 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e53873 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e53874 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e53875 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e53876 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e53877 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b53878 := hb (x (-1) 7)
    have b53879 := hb (x 0 6)
    have b53880 := hb (x 1 5)
    have b53881 := hb (x 2 4)
    have b53882 := hb (x 3 11)
    have b53883 := hb (x 4 10)
    have b53884 := hb (x 5 9)
    have b53885 := hb (x 6 8)
    clear * - r53871 e53872 e53873 e53874 e53875 e53876 e53877 b53878 b53879 b53880 b53881 b53882 b53883 b53884 b53885 d53838 d53854 g4 g3 g1
    omega
  have d53886 : (x 3 1 && x 3 11).toNat = 1 := by
    have r53887 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b53888 := hb (x (-1) 5)
    have b53889 := hb (x 4 10)
    have b53890 := hb (x 3 1 && x 3 11)
    have b53891 := hb (x 2 2 && x 2 12)
    have b53892 := hb (x 1 3 && x 1 13)
    have b53893 := hb (x 0 4 && x 0 14)
    clear * - r53887 b53888 b53889 b53890 b53891 b53892 b53893 d53870 g8 g9 g10 g0
    omega
  have d53894 : (x 3 11).toNat = 1 := by
    have r53895 := hand2 (x 3 1) (x 3 11)
    have b53896 := hb (x 3 11)
    have b53897 := hb (x 3 1 && x 3 11)
    clear * - r53895 b53896 b53897 d53886
    omega
  have d53898 : (x 3 3).toNat = 1 := by
    have r53899 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b53900 := hb (x 3 3)
    have b53901 := hb (x 3 11)
    clear * - r53899 b53900 b53901 d53894
    omega
  have d53902 : (x 6 12).toNat = 0 := by
    have r53903 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e53904 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e53905 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b53906 := hb (x 3 3)
    have b53907 := hb (x 4 2)
    have b53908 := hb (x 5 13)
    have b53909 := hb (x 6 12)
    clear * - r53903 e53904 e53905 b53906 b53907 b53908 b53909 d53898
    omega
  have d53910 : (x 6 1 && x 6 12).toNat = 0 := by
    have r53911 := hand2 (x 6 1) (x 6 12)
    have b53912 := hb (x 6 12)
    have b53913 := hb (x 6 1 && x 6 12)
    clear * - r53911 b53912 b53913 d53902
    omega
  have d53914 : (x 5 13).toNat = 0 := by
    have r53915 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e53916 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e53917 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b53918 := hb (x 3 3)
    have b53919 := hb (x 4 2)
    have b53920 := hb (x 5 13)
    have b53921 := hb (x 6 12)
    clear * - r53915 e53916 e53917 b53918 b53919 b53920 b53921 d53902 d53898
    omega
  have d53922 : (x 4 2).toNat = 0 := by
    have r53923 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e53924 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e53925 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b53926 := hb (x 3 3)
    have b53927 := hb (x 4 2)
    have b53928 := hb (x 5 13)
    have b53929 := hb (x 6 12)
    clear * - r53923 e53924 e53925 b53926 b53927 b53928 b53929 d53902 d53914 d53898
    omega
  have d53930 : (x 5 1 && x 5 14).toNat = 1 := by
    have r53931 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b53932 := hb (x 4 2)
    have b53933 := hb (x 6 13)
    have b53934 := hb (x 5 1 && x 5 14)
    clear * - r53931 b53932 b53933 b53934 g7 d53922
    omega
  have d53935 : (x 5 14).toNat = 1 := by
    have r53936 := hand2 (x 5 1) (x 5 14)
    have b53937 := hb (x 5 14)
    have b53938 := hb (x 5 1 && x 5 14)
    clear * - r53936 b53937 b53938 d53930
    omega
  have d53939 : (x 4 1).toNat = 0 := by
    have r53940 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b53941 := hb (x 4 1)
    have b53942 := hb (x 5 14)
    clear * - r53940 b53941 b53942 d53935
    omega
  have d53943 : (x 4 1 && x 4 14).toNat = 0 := by
    have r53944 := hand1 (x 4 1) (x 4 14)
    have b53945 := hb (x 4 1)
    have b53946 := hb (x 4 1 && x 4 14)
    clear * - r53944 b53945 b53946 d53939
    omega
  have d53947 : (x 3 2).toNat = 1 := by
    have r53948 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b53949 := hb (x 3 2)
    have b53950 := hb (x 5 13)
    have b53951 := hb (x 4 1 && x 4 14)
    clear * - r53948 b53949 b53950 b53951 d53914 d53943
    omega
  have d53952 : (x 3 14).toNat = 1 := by
    have r53953 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b53954 := hb (x 3 2)
    have b53955 := hb (x 3 14)
    clear * - r53953 b53954 b53955 d53947
    omega
  have d53956 : (x 2 1).toNat = 0 := by
    have r53957 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b53958 := hb (x 2 1)
    have b53959 := hb (x 3 14)
    clear * - r53957 b53958 b53959 d53952
    omega
  have d53960 : (x 2 1 && x 2 14).toNat = 0 := by
    have r53961 := hand1 (x 2 1) (x 2 14)
    have b53962 := hb (x 2 1)
    have b53963 := hb (x 2 1 && x 2 14)
    clear * - r53961 b53962 b53963 d53956
    omega
  have d53964 : (x 3 13).toNat = 1 := by
    have r53965 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b53966 := hb (x 1 2)
    have b53967 := hb (x 3 13)
    have b53968 := hb (x 2 1 && x 2 14)
    clear * - r53965 b53966 b53967 b53968 d53960 g2
    omega
  have d53969 : (x 3 1).toNat = 1 := by
    have r53970 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b53971 := hb (x 3 1)
    have b53972 := hb (x 3 13)
    clear * - r53970 b53971 b53972 d53964
    omega
  have d53973 : (x 4 14).toNat = 0 := by
    have r53974 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b53975 := hb (x 3 1)
    have b53976 := hb (x 4 14)
    clear * - r53974 b53975 b53976 d53969
    omega
  have d53977 : (x 4 3 && x 4 14).toNat = 0 := by
    have r53978 := hand2 (x 4 3) (x 4 14)
    have b53979 := hb (x 4 14)
    have b53980 := hb (x 4 3 && x 4 14)
    clear * - r53978 b53979 b53980 d53973
    omega
  have d53981 : (x 7 11).toNat = 1 := by
    have r53982 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b53983 := hb (x 3 4)
    have b53984 := hb (x 7 11)
    have b53985 := hb (x 6 1 && x 6 12)
    have b53986 := hb (x 5 2 && x 5 13)
    have b53987 := hb (x 4 3 && x 4 14)
    clear * - r53982 b53983 b53984 b53985 b53986 b53987 d53910 g13 d53977 g5
    omega
  have d53988 : (x 7 3).toNat = 1 := by
    have r53989 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b53990 := hb (x 7 3)
    have b53991 := hb (x 7 11)
    clear * - r53989 b53990 b53991 d53981
    omega
  have d53992 : (x 10 12).toNat = 0 := by
    have r53993 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e53994 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e53995 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b53996 := hb (x 7 3)
    have b53997 := hb (x 8 2)
    have b53998 := hb (x 9 13)
    have b53999 := hb (x 10 12)
    clear * - r53993 e53994 e53995 b53996 b53997 b53998 b53999 d53988
    omega
  have d54000 : (x 9 13).toNat = 0 := by
    have r54001 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54002 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e54003 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b54004 := hb (x 7 3)
    have b54005 := hb (x 8 2)
    have b54006 := hb (x 9 13)
    have b54007 := hb (x 10 12)
    clear * - r54001 e54002 e54003 b54004 b54005 b54006 b54007 d53992 d53988
    omega
  have d54008 : (x 8 2).toNat = 0 := by
    have r54009 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54010 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e54011 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b54012 := hb (x 7 3)
    have b54013 := hb (x 8 2)
    have b54014 := hb (x 9 13)
    have b54015 := hb (x 10 12)
    clear * - r54009 e54010 e54011 b54012 b54013 b54014 b54015 d53992 d54000 d53988
    omega
  have d54016 : (x 4 12).toNat = 0 := by
    have r54017 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54018 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e54019 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b54020 := hb (x 1 3)
    have b54021 := hb (x 2 2)
    have b54022 := hb (x 3 13)
    have b54023 := hb (x 4 12)
    clear * - r54017 e54018 e54019 b54020 b54021 b54022 b54023 d53964
    omega
  have d54024 : (x 4 4).toNat = 0 := by
    have r54025 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b54026 := hb (x 4 4)
    have b54027 := hb (x 4 12)
    clear * - r54025 b54026 b54027 d54016
    omega
  have d54028 : (x 5 12).toNat = 0 := by
    have r54029 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54030 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e54031 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b54032 := hb (x 2 3)
    have b54033 := hb (x 3 2)
    have b54034 := hb (x 4 13)
    have b54035 := hb (x 5 12)
    clear * - r54029 e54030 e54031 b54032 b54033 b54034 b54035 d53947
    omega
  have d54036 : (x 5 4).toNat = 0 := by
    have r54037 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b54038 := hb (x 5 4)
    have b54039 := hb (x 5 12)
    clear * - r54037 b54038 b54039 d54028
    omega
  have d54040 : (x 5 4 && x 5 14).toNat = 0 := by
    have r54041 := hand1 (x 5 4) (x 5 14)
    have b54042 := hb (x 5 4)
    have b54043 := hb (x 5 4 && x 5 14)
    clear * - r54041 b54042 b54043 d54036
    omega
  have d54044 : (x 4 13).toNat = 0 := by
    have r54045 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54046 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e54047 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b54048 := hb (x 2 3)
    have b54049 := hb (x 3 2)
    have b54050 := hb (x 4 13)
    have b54051 := hb (x 5 12)
    clear * - r54045 e54046 e54047 b54048 b54049 b54050 b54051 d54028 d53947
    omega
  have d54052 : (x 4 5).toNat = 0 := by
    have r54053 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b54054 := hb (x 4 5)
    have b54055 := hb (x 4 13)
    clear * - r54053 b54054 b54055 d54044
    omega
  have d54056 : (x 5 1).toNat = 1 := by
    have r54057 := hand1 (x 5 1) (x 5 14)
    have b54058 := hb (x 5 1)
    have b54059 := hb (x 5 1 && x 5 14)
    clear * - r54057 b54058 b54059 d53930
    omega
  have d54060 : (x 6 14).toNat = 0 := by
    have r54061 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b54062 := hb (x 5 1)
    have b54063 := hb (x 6 14)
    clear * - r54061 b54062 b54063 d54056
    omega
  have d54064 : (x 6 1 && x 6 14).toNat = 0 := by
    have r54065 := hand2 (x 6 1) (x 6 14)
    have b54066 := hb (x 6 14)
    have b54067 := hb (x 6 1 && x 6 14)
    clear * - r54065 b54066 b54067 d54060
    omega
  have d54068 : (x 7 13).toNat = 1 := by
    have r54069 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b54070 := hb (x 5 2)
    have b54071 := hb (x 7 13)
    have b54072 := hb (x 6 1 && x 6 14)
    clear * - r54069 b54070 b54071 b54072 d54064 g6
    omega
  have d54073 : (x 8 12).toNat = 0 := by
    have r54074 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54075 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e54076 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b54077 := hb (x 5 3)
    have b54078 := hb (x 6 2)
    have b54079 := hb (x 7 13)
    have b54080 := hb (x 8 12)
    clear * - r54074 e54075 e54076 b54077 b54078 b54079 b54080 d54068
    omega
  have d54081 : (x 6 2).toNat = 0 := by
    have r54082 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54083 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e54084 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b54085 := hb (x 5 3)
    have b54086 := hb (x 6 2)
    have b54087 := hb (x 7 13)
    have b54088 := hb (x 8 12)
    clear * - r54082 e54083 e54084 b54085 b54086 b54087 b54088 d54073 d54068
    omega
  have d54089 : (x 5 3).toNat = 0 := by
    have r54090 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54091 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e54092 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b54093 := hb (x 5 3)
    have b54094 := hb (x 6 2)
    have b54095 := hb (x 7 13)
    have b54096 := hb (x 8 12)
    clear * - r54090 e54091 e54092 b54093 b54094 b54095 b54096 d54073 d54068 d54081
    omega
  have d54097 : (x 5 3 && x 5 14).toNat = 0 := by
    have r54098 := hand1 (x 5 3) (x 5 14)
    have b54099 := hb (x 5 3)
    have b54100 := hb (x 5 3 && x 5 14)
    clear * - r54098 b54099 b54100 d54089
    omega
  have d54101 : (x 8 11).toNat = 1 := by
    have r54102 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b54103 := hb (x 4 4)
    have b54104 := hb (x 8 11)
    have b54105 := hb (x 7 1 && x 7 12)
    have b54106 := hb (x 6 2 && x 6 13)
    have b54107 := hb (x 5 3 && x 5 14)
    clear * - r54102 b54103 b54104 b54105 b54106 b54107 g14 g15 d54097 d54024
    omega
  have d54108 : (x 8 3).toNat = 1 := by
    have r54109 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b54110 := hb (x 8 3)
    have b54111 := hb (x 8 11)
    clear * - r54109 b54110 b54111 d54101
    omega
  have d54112 : (x 11 12).toNat = 0 := by
    have r54113 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54114 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e54115 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b54116 := hb (x 8 3)
    have b54117 := hb (x 9 2)
    have b54118 := hb (x 10 13)
    have b54119 := hb (x 11 12)
    clear * - r54113 e54114 e54115 b54116 b54117 b54118 b54119 d54108
    omega
  have d54120 : (x 10 13).toNat = 0 := by
    have r54121 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54122 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e54123 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b54124 := hb (x 8 3)
    have b54125 := hb (x 9 2)
    have b54126 := hb (x 10 13)
    have b54127 := hb (x 11 12)
    clear * - r54121 e54122 e54123 b54124 b54125 b54126 b54127 d54112 d54108
    omega
  have d54128 : (x 9 1 && x 9 14).toNat = 1 := by
    have r54129 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b54130 := hb (x 8 2)
    have b54131 := hb (x 10 13)
    have b54132 := hb (x 9 1 && x 9 14)
    clear * - r54129 b54130 b54131 b54132 d54120 d54008
    omega
  have d54133 : (x 9 14).toNat = 1 := by
    have r54134 := hand2 (x 9 1) (x 9 14)
    have b54135 := hb (x 9 14)
    have b54136 := hb (x 9 1 && x 9 14)
    clear * - r54134 b54135 b54136 d54128
    omega
  have d54137 : (x 8 1).toNat = 0 := by
    have r54138 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b54139 := hb (x 8 1)
    have b54140 := hb (x 9 14)
    clear * - r54138 b54139 b54140 d54133
    omega
  have d54141 : (x 8 1 && x 8 11).toNat = 0 := by
    have r54142 := hand1 (x 8 1) (x 8 11)
    have b54143 := hb (x 8 1)
    have b54144 := hb (x 8 1 && x 8 11)
    clear * - r54142 b54143 b54144 d54137
    omega
  have d54145 : (x 9 10).toNat = 1 := by
    have r54146 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b54147 := hb (x 4 5)
    have b54148 := hb (x 9 10)
    have b54149 := hb (x 8 1 && x 8 11)
    have b54150 := hb (x 7 2 && x 7 12)
    have b54151 := hb (x 6 3 && x 6 13)
    have b54152 := hb (x 5 4 && x 5 14)
    clear * - r54146 b54147 b54148 b54149 b54150 b54151 b54152 d54141 g11 g12 d54040 d54052
    omega
  have d54153 : (x 9 2).toNat = 1 := by
    have r54154 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
    have b54155 := hb (x 9 2)
    have b54156 := hb (x 9 10)
    clear * - r54154 b54155 b54156 d54145
    omega
  have r54157 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e54158 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
  have e54159 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
  have b54160 := hb (x 8 3)
  have b54161 := hb (x 9 2)
  have b54162 := hb (x 10 13)
  have b54163 := hb (x 11 12)
  linarith only [r54157, e54158, e54159, b54160, b54161, b54162, b54163, d54112, d54120, d54153, d54108]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a011111 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 6).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 4).toNat = 1)
    (g3 : (x 0 9).toNat = 0)
    (g4 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g5 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g6 : (x (-5) 5 && x (-5) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d54165 : (x 0 12).toNat = 1 := by
    have r54166 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b54167 := hb (x 0 4)
    have b54168 := hb (x 0 12)
    clear * - r54166 b54167 b54168 g2
    omega
  have d54169 : (x (-2) 2).toNat = 0 := by
    have r54170 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54171 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e54172 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b54173 := hb (x (-3) 3)
    have b54174 := hb (x (-2) 2)
    have b54175 := hb (x (-1) 13)
    have b54176 := hb (x 0 12)
    clear * - r54170 e54171 e54172 b54173 b54174 b54175 b54176 d54165 g1
    omega
  have d54177 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
    have r54178 := hand1 (x (-2) 2) (x (-2) 11)
    have b54179 := hb (x (-2) 2)
    have b54180 := hb (x (-2) 2 && x (-2) 11)
    clear * - r54178 b54179 b54180 d54169
    omega
  have d54181 : (x (-3) 3).toNat = 0 := by
    have r54182 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e54183 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e54184 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b54185 := hb (x (-3) 3)
    have b54186 := hb (x (-2) 2)
    have b54187 := hb (x (-1) 13)
    have b54188 := hb (x 0 12)
    clear * - r54182 e54183 e54184 b54185 b54186 b54187 b54188 d54165 g1 d54169
    omega
  have d54189 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
    have r54190 := hand1 (x (-3) 3) (x (-3) 12)
    have b54191 := hb (x (-3) 3)
    have b54192 := hb (x (-3) 3 && x (-3) 12)
    clear * - r54190 b54191 b54192 d54181
    omega
  have r54193 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b54194 := hb (x (-6) 6)
  have b54195 := hb (x 0 9)
  have b54196 := hb (x (-1) 1 && x (-1) 10)
  have b54197 := hb (x (-2) 2 && x (-2) 11)
  have b54198 := hb (x (-3) 3 && x (-3) 12)
  have b54199 := hb (x (-4) 4 && x (-4) 13)
  have b54200 := hb (x (-5) 5 && x (-5) 14)
  linarith only [r54193, b54194, b54195, b54196, b54197, b54198, b54199, b54200, g3, g4, d54177, d54189, g5, g6, g0]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a10_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 6).toNat = 0)
    (g1 : (x (-5) 5).toNat = 0)
    (g2 : (x (-4) 4).toNat = 0)
    (g3 : (x (-3) 11).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x 0 6).toNat = 0)
    (g7 : (x 0 9).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 2 5).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 4 11).toNat = 0)
    (g12 : (x 5 10).toNat = 0)
    (g13 : (x 6 9).toNat = 0)
    (g14 : (x 7 8).toNat = 0)
    (g15 : (x 7 7 && x 7 8).toNat = 0)
    (g16 : (x 6 8 && x 6 9).toNat = 0)
    (g17 : (x 5 9 && x 5 10).toNat = 0)
    (g18 : (x 4 10 && x 4 11).toNat = 0)
    (g19 : (x (-4) 4 && x (-4) 8).toNat = 0)
    (g20 : (x (-5) 5 && x (-5) 9).toNat = 0)
    (g21 : (x (-6) 6 && x (-6) 10).toNat = 0)
    (g22 : (x (-7) 7 && x (-7) 11).toNat = 0)
    (g23 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g24 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g25 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g26 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g27 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g29 : (x 0 9 && x 0 14).toNat = 0)
    (g30 : (x 7 3 && x 7 8).toNat = 0)
    (g31 : (x 6 4 && x 6 9).toNat = 0)
    (g32 : (x 5 5 && x 5 10).toNat = 0)
    (g33 : (x 4 6 && x 4 11).toNat = 0)
    (g34 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g35 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g36 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g37 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g38 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g39 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g40 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g41 : (x 3 4 && x 3 11).toNat = 0)
    (g42 : (x 2 5 && x 2 12).toNat = 0)
    (g43 : (x 1 6 && x 1 13).toNat = 0)
    (g44 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g45 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g46 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g47 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g48 : (x 5 1 && x 5 10).toNat = 0)
    (g49 : (x 4 2 && x 4 11).toNat = 0)
    (g50 : (x 3 4 && x 3 13).toNat = 0)
    (g51 : (x 2 5 && x 2 14).toNat = 0)
    (g52 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g53 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g54 : (x 4 1 && x 4 11).toNat = 0)
    (g55 : (x 3 4 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d54416 : (x 0 1 && x 0 6).toNat = 0 := by
    have r54417 := hand2 (x 0 1) (x 0 6)
    have b54418 := hb (x 0 6)
    have b54419 := hb (x 0 1 && x 0 6)
    clear * - r54417 b54418 b54419 g6
    omega
  have d54420 : (x 0 6 && x 0 10).toNat = 0 := by
    have r54421 := hand1 (x 0 6) (x 0 10)
    have b54422 := hb (x 0 6)
    have b54423 := hb (x 0 6 && x 0 10)
    clear * - r54421 b54422 b54423 g6
    omega
  cases h54424 : x 0 14
  · have f54425 : (x 0 14).toNat = 0 := by rw [h54424]; rfl
    have d54426 : (x 0 1 && x 0 14).toNat = 0 := by
      have r54427 := hand2 (x 0 1) (x 0 14)
      have b54428 := hb (x 0 14)
      have b54429 := hb (x 0 1 && x 0 14)
      clear * - r54427 b54428 b54429 f54425
      omega
    have d54430 : (x 0 4 && x 0 14).toNat = 0 := by
      have r54431 := hand2 (x 0 4) (x 0 14)
      have b54432 := hb (x 0 14)
      have b54433 := hb (x 0 4 && x 0 14)
      clear * - r54431 b54432 b54433 f54425
      omega
    have d54434 : (x 0 7 && x 0 14).toNat = 0 := by
      have r54435 := hand2 (x 0 7) (x 0 14)
      have b54436 := hb (x 0 14)
      have b54437 := hb (x 0 7 && x 0 14)
      clear * - r54435 b54436 b54437 f54425
      omega
    have d54438 : (x 0 2).toNat = 0 := by
      have r54439 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b54440 := hb (x 0 2)
      have b54441 := hb (x 0 14)
      clear * - r54439 b54440 b54441 f54425
      omega
    have d54442 : (x 0 2 && x 0 13).toNat = 0 := by
      have r54443 := hand1 (x 0 2) (x 0 13)
      have b54444 := hb (x 0 2)
      have b54445 := hb (x 0 2 && x 0 13)
      clear * - r54443 b54444 b54445 d54438
      omega
    have d54446 : (x 0 2 && x 0 12).toNat = 0 := by
      have r54447 := hand1 (x 0 2) (x 0 12)
      have b54448 := hb (x 0 2)
      have b54449 := hb (x 0 2 && x 0 12)
      clear * - r54447 b54448 b54449 d54438
      omega
    have d54450 : (x 0 2 && x 0 11).toNat = 0 := by
      have r54451 := hand1 (x 0 2) (x 0 11)
      have b54452 := hb (x 0 2)
      have b54453 := hb (x 0 2 && x 0 11)
      clear * - r54451 b54452 b54453 d54438
      omega
    have d54454 : (x 0 10).toNat = 0 := by
      have r54455 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
      have b54456 := hb (x 0 2)
      have b54457 := hb (x 0 10)
      clear * - r54455 b54456 b54457 d54438
      omega
    have d54458 : (x 0 1 && x 0 10).toNat = 0 := by
      have r54459 := hand2 (x 0 1) (x 0 10)
      have b54460 := hb (x 0 10)
      have b54461 := hb (x 0 1 && x 0 10)
      clear * - r54459 b54460 b54461 d54454
      omega
    cases h54462 : x 0 1
    · have f54463 : (x 0 1).toNat = 0 := by rw [h54462]; rfl
      have d54464 : (x 0 1 && x 0 12).toNat = 0 := by
        have r54465 := hand1 (x 0 1) (x 0 12)
        have b54466 := hb (x 0 1)
        have b54467 := hb (x 0 1 && x 0 12)
        clear * - r54465 b54466 b54467 f54463
        omega
      have d54468 : (x 0 1 && x 0 8).toNat = 0 := by
        have r54469 := hand1 (x 0 1) (x 0 8)
        have b54470 := hb (x 0 1)
        have b54471 := hb (x 0 1 && x 0 8)
        clear * - r54469 b54470 b54471 f54463
        omega
      have d54472 : (x 0 13).toNat = 0 := by
        have r54473 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
        have b54474 := hb (x 0 1)
        have b54475 := hb (x 0 13)
        clear * - r54473 b54474 b54475 f54463
        omega
      have d54476 : (x 0 5).toNat = 0 := by
        have r54477 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
        have b54478 := hb (x 0 5)
        have b54479 := hb (x 0 13)
        clear * - r54477 b54478 b54479 d54472
        omega
      have d54480 : (x 1 14).toNat = 1 := by
        have r54481 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b54482 := hb (x 0 1)
        have b54483 := hb (x 1 14)
        clear * - r54481 b54482 b54483 f54463
        omega
      cases h54484 : x 0 3
      · have f54485 : (x 0 3).toNat = 0 := by rw [h54484]; rfl
        have d54486 : (x 0 11).toNat = 0 := by
          have r54487 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
          have b54488 := hb (x 0 3)
          have b54489 := hb (x 0 11)
          clear * - r54487 b54488 b54489 f54485
          omega
        cases h54490 : x 0 4
        · have f54491 : (x 0 4).toNat = 0 := by rw [h54490]; rfl
          have d54492 : (x 0 4 && x 0 8).toNat = 0 := by
            have r54493 := hand1 (x 0 4) (x 0 8)
            have b54494 := hb (x 0 4)
            have b54495 := hb (x 0 4 && x 0 8)
            clear * - r54493 b54494 b54495 f54491
            omega
          cases h54496 : x 0 12
          · have f54497 : (x 0 12).toNat = 0 := by rw [h54496]; rfl
            cases h54498 : x 1 1
            · have f54499 : (x 1 1).toNat = 0 := by rw [h54498]; rfl
              have d54500 : (x 1 1 && x 1 14).toNat = 0 := by
                have r54501 := hand1 (x 1 1) (x 1 14)
                have b54502 := hb (x 1 1)
                have b54503 := hb (x 1 1 && x 1 14)
                clear * - r54501 b54502 b54503 f54499
                omega
              have d54504 : (x 1 13).toNat = 0 := by
                have r54505 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
                have b54506 := hb (x 1 1)
                have b54507 := hb (x 1 13)
                clear * - r54505 b54506 b54507 f54499
                omega
              have d54508 : (x 1 5).toNat = 0 := by
                have r54509 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
                have b54510 := hb (x 1 5)
                have b54511 := hb (x 1 13)
                clear * - r54509 b54510 b54511 d54504
                omega
              have d54512 : (x 1 5 && x 1 14).toNat = 0 := by
                have r54513 := hand1 (x 1 5) (x 1 14)
                have b54514 := hb (x 1 5)
                have b54515 := hb (x 1 5 && x 1 14)
                clear * - r54513 b54514 b54515 d54508
                omega
              have d54516 : (x 2 13).toNat = 1 := by
                have r54517 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b54518 := hb (x 0 2)
                have b54519 := hb (x 2 13)
                have b54520 := hb (x 1 1 && x 1 14)
                clear * - r54517 b54518 b54519 b54520 d54500 d54438
                omega
              have d54521 : (x 2 1).toNat = 1 := by
                have r54522 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
                have b54523 := hb (x 2 1)
                have b54524 := hb (x 2 13)
                clear * - r54522 b54523 b54524 d54516
                omega
              have d54525 : (x 3 14).toNat = 0 := by
                have r54526 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b54527 := hb (x 2 1)
                have b54528 := hb (x 3 14)
                clear * - r54526 b54527 b54528 d54521
                omega
              have d54529 : (x 3 1 && x 3 14).toNat = 0 := by
                have r54530 := hand2 (x 3 1) (x 3 14)
                have b54531 := hb (x 3 14)
                have b54532 := hb (x 3 1 && x 3 14)
                clear * - r54530 b54531 b54532 d54525
                omega
              have d54533 : (x 3 2).toNat = 0 := by
                have r54534 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                have b54535 := hb (x 3 2)
                have b54536 := hb (x 3 14)
                clear * - r54534 b54535 b54536 d54525
                omega
              have d54537 : (x 3 2 && x 3 12).toNat = 0 := by
                have r54538 := hand1 (x 3 2) (x 3 12)
                have b54539 := hb (x 3 2)
                have b54540 := hb (x 3 2 && x 3 12)
                clear * - r54538 b54539 b54540 d54533
                omega
              have d54541 : (x (-1) 2).toNat = 1 := by
                have r54542 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b54543 := hb (x (-1) 2)
                have b54544 := hb (x 1 13)
                have b54545 := hb (x 0 1 && x 0 14)
                clear * - r54542 b54543 b54544 b54545 d54504 d54426
                omega
              have d54546 : (x 3 12).toNat = 0 := by
                have r54547 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54548 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                have e54549 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                have b54550 := hb (x 0 3)
                have b54551 := hb (x 1 2)
                have b54552 := hb (x 2 13)
                have b54553 := hb (x 3 12)
                clear * - r54547 e54548 e54549 b54550 b54551 b54552 b54553 d54516 f54485
                omega
              have d54554 : (x 3 3 && x 3 12).toNat = 0 := by
                have r54555 := hand2 (x 3 3) (x 3 12)
                have b54556 := hb (x 3 12)
                have b54557 := hb (x 3 3 && x 3 12)
                clear * - r54555 b54556 b54557 d54546
                omega
              have d54558 : (x 1 12).toNat = 0 := by
                have r54559 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54560 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                have e54561 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                have b54562 := hb (x (-2) 3)
                have b54563 := hb (x (-1) 2)
                have b54564 := hb (x 0 13)
                have b54565 := hb (x 1 12)
                clear * - r54559 e54560 e54561 b54562 b54563 b54564 b54565 d54472 d54541
                omega
              have d54566 : (x 1 4).toNat = 0 := by
                have r54567 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                have b54568 := hb (x 1 4)
                have b54569 := hb (x 1 12)
                clear * - r54567 b54568 b54569 d54558
                omega
              have d54570 : (x 1 4 && x 1 14).toNat = 0 := by
                have r54571 := hand1 (x 1 4) (x 1 14)
                have b54572 := hb (x 1 4)
                have b54573 := hb (x 1 4 && x 1 14)
                clear * - r54571 b54572 b54573 d54566
                omega
              have d54574 : (x (-2) 3).toNat = 0 := by
                have r54575 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54576 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                have e54577 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                have b54578 := hb (x (-2) 3)
                have b54579 := hb (x (-1) 2)
                have b54580 := hb (x 0 13)
                have b54581 := hb (x 1 12)
                clear * - r54575 e54576 e54577 b54578 b54579 b54580 b54581 d54558 d54472 d54541
                omega
              have d54582 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                have r54583 := hand1 (x (-2) 3) (x (-2) 14)
                have b54584 := hb (x (-2) 3)
                have b54585 := hb (x (-2) 3 && x (-2) 14)
                clear * - r54583 b54584 b54585 d54574
                omega
              have d54586 : (x 2 3 && x 2 13).toNat = 1 := by
                have r54587 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b54588 := hb (x 0 5)
                have b54589 := hb (x 5 10)
                have b54590 := hb (x 4 1 && x 4 11)
                have b54591 := hb (x 3 2 && x 3 12)
                have b54592 := hb (x 2 3 && x 2 13)
                have b54593 := hb (x 1 4 && x 1 14)
                clear * - r54587 b54588 b54589 b54590 b54591 b54592 b54593 g12 g54 d54537 d54570 d54476
                omega
              have d54594 : (x 2 3).toNat = 1 := by
                have r54595 := hand1 (x 2 3) (x 2 13)
                have b54596 := hb (x 2 3)
                have b54597 := hb (x 2 3 && x 2 13)
                clear * - r54595 b54596 b54597 d54586
                omega
              have d54598 : (x 5 12).toNat = 0 := by
                have r54599 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54600 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e54601 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b54602 := hb (x 2 3)
                have b54603 := hb (x 3 2)
                have b54604 := hb (x 4 13)
                have b54605 := hb (x 5 12)
                clear * - r54599 e54600 e54601 b54602 b54603 b54604 b54605 d54533 d54594
                omega
              have d54606 : (x 4 13).toNat = 0 := by
                have r54607 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54608 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e54609 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b54610 := hb (x 2 3)
                have b54611 := hb (x 3 2)
                have b54612 := hb (x 4 13)
                have b54613 := hb (x 5 12)
                clear * - r54607 e54608 e54609 b54610 b54611 b54612 b54613 d54598 d54533 d54594
                omega
              have d54614 : (x 2 2).toNat = 1 := by
                have r54615 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b54616 := hb (x 2 2)
                have b54617 := hb (x 4 13)
                have b54618 := hb (x 3 1 && x 3 14)
                clear * - r54615 b54616 b54617 b54618 d54606 d54529
                omega
              have d54619 : (x 4 12).toNat = 0 := by
                have r54620 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54621 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e54622 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b54623 := hb (x 1 3)
                have b54624 := hb (x 2 2)
                have b54625 := hb (x 3 13)
                have b54626 := hb (x 4 12)
                clear * - r54620 e54621 e54622 b54623 b54624 b54625 b54626 d54614
                omega
              have d54627 : (x 4 3 && x 4 12).toNat = 0 := by
                have r54628 := hand2 (x 4 3) (x 4 12)
                have b54629 := hb (x 4 12)
                have b54630 := hb (x 4 3 && x 4 12)
                clear * - r54628 b54629 b54630 d54619
                omega
              have d54631 : (x 4 4).toNat = 0 := by
                have r54632 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b54633 := hb (x 4 4)
                have b54634 := hb (x 4 12)
                clear * - r54632 b54633 b54634 d54619
                omega
              have d54635 : (x 3 13).toNat = 0 := by
                have r54636 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54637 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e54638 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b54639 := hb (x 1 3)
                have b54640 := hb (x 2 2)
                have b54641 := hb (x 3 13)
                have b54642 := hb (x 4 12)
                clear * - r54636 e54637 e54638 b54639 b54640 b54641 b54642 d54619 d54614
                omega
              have d54643 : (x 3 5).toNat = 0 := by
                have r54644 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                have b54645 := hb (x 3 5)
                have b54646 := hb (x 3 13)
                clear * - r54644 b54645 b54646 d54635
                omega
              have d54647 : (x 1 3).toNat = 0 := by
                have r54648 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54649 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e54650 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b54651 := hb (x 1 3)
                have b54652 := hb (x 2 2)
                have b54653 := hb (x 3 13)
                have b54654 := hb (x 4 12)
                clear * - r54648 e54649 e54650 b54651 b54652 b54653 b54654 d54619 d54635 d54614
                omega
              have d54655 : (x 1 11).toNat = 0 := by
                have r54656 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                have b54657 := hb (x 1 3)
                have b54658 := hb (x 1 11)
                clear * - r54656 b54657 b54658 d54647
                omega
              have d54659 : (x 2 4 && x 2 13).toNat = 1 := by
                have r54660 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b54661 := hb (x 0 6)
                have b54662 := hb (x 6 9)
                have b54663 := hb (x 5 1 && x 5 10)
                have b54664 := hb (x 4 2 && x 4 11)
                have b54665 := hb (x 3 3 && x 3 12)
                have b54666 := hb (x 2 4 && x 2 13)
                have b54667 := hb (x 1 5 && x 1 14)
                clear * - r54660 b54661 b54662 b54663 b54664 b54665 b54666 b54667 g13 g48 g49 d54554 d54512 g6
                omega
              have d54668 : (x 2 4).toNat = 1 := by
                have r54669 := hand1 (x 2 4) (x 2 13)
                have b54670 := hb (x 2 4)
                have b54671 := hb (x 2 4 && x 2 13)
                clear * - r54669 b54670 b54671 d54659
                omega
              have d54672 : (x 2 12).toNat = 1 := by
                have r54673 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
                have b54674 := hb (x 2 4)
                have b54675 := hb (x 2 12)
                clear * - r54673 b54674 b54675 d54668
                omega
              have d54676 : (x (-1) 3).toNat = 0 := by
                have r54677 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54678 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                have e54679 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                have b54680 := hb (x (-1) 3)
                have b54681 := hb (x 0 2)
                have b54682 := hb (x 1 13)
                have b54683 := hb (x 2 12)
                clear * - r54677 e54678 e54679 b54680 b54681 b54682 b54683 d54672 d54504 d54438
                omega
              have d54684 : (x (-1) 11).toNat = 0 := by
                have r54685 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
                have b54686 := hb (x (-1) 3)
                have b54687 := hb (x (-1) 11)
                clear * - r54685 b54686 b54687 d54676
                omega
              have d54688 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
                have r54689 := hand2 (x (-1) 1) (x (-1) 11)
                have b54690 := hb (x (-1) 11)
                have b54691 := hb (x (-1) 1 && x (-1) 11)
                clear * - r54689 b54690 b54691 d54684
                omega
              have d54692 : (x 6 8).toNat = 0 := by
                have r54693 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54694 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e54695 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e54696 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e54697 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e54698 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e54699 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b54700 := hb (x (-1) 7)
                have b54701 := hb (x 0 6)
                have b54702 := hb (x 1 5)
                have b54703 := hb (x 2 4)
                have b54704 := hb (x 3 11)
                have b54705 := hb (x 4 10)
                have b54706 := hb (x 5 9)
                have b54707 := hb (x 6 8)
                clear * - r54693 e54694 e54695 e54696 e54697 e54698 e54699 b54700 b54701 b54702 b54703 b54704 b54705 b54706 b54707 d54668 d54508 g6
                omega
              have d54708 : (x 5 9).toNat = 0 := by
                have r54709 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54710 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e54711 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e54712 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e54713 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e54714 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e54715 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b54716 := hb (x (-1) 7)
                have b54717 := hb (x 0 6)
                have b54718 := hb (x 1 5)
                have b54719 := hb (x 2 4)
                have b54720 := hb (x 3 11)
                have b54721 := hb (x 4 10)
                have b54722 := hb (x 5 9)
                have b54723 := hb (x 6 8)
                clear * - r54709 e54710 e54711 e54712 e54713 e54714 e54715 b54716 b54717 b54718 b54719 b54720 b54721 b54722 b54723 d54692 d54668 d54508 g6
                omega
              have d54724 : (x 4 10).toNat = 0 := by
                have r54725 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54726 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e54727 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e54728 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e54729 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e54730 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e54731 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b54732 := hb (x (-1) 7)
                have b54733 := hb (x 0 6)
                have b54734 := hb (x 1 5)
                have b54735 := hb (x 2 4)
                have b54736 := hb (x 3 11)
                have b54737 := hb (x 4 10)
                have b54738 := hb (x 5 9)
                have b54739 := hb (x 6 8)
                clear * - r54725 e54726 e54727 e54728 e54729 e54730 e54731 b54732 b54733 b54734 b54735 b54736 b54737 b54738 b54739 d54692 d54708 d54668 d54508 g6
                omega
              have d54740 : (x 3 11).toNat = 0 := by
                have r54741 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54742 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e54743 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e54744 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e54745 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e54746 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e54747 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b54748 := hb (x (-1) 7)
                have b54749 := hb (x 0 6)
                have b54750 := hb (x 1 5)
                have b54751 := hb (x 2 4)
                have b54752 := hb (x 3 11)
                have b54753 := hb (x 4 10)
                have b54754 := hb (x 5 9)
                have b54755 := hb (x 6 8)
                clear * - r54741 e54742 e54743 e54744 e54745 e54746 e54747 b54748 b54749 b54750 b54751 b54752 b54753 b54754 b54755 d54692 d54708 d54724 d54668 d54508 g6
                omega
              have d54756 : (x (-1) 7).toNat = 0 := by
                have r54757 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e54758 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e54759 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e54760 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e54761 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e54762 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e54763 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b54764 := hb (x (-1) 7)
                have b54765 := hb (x 0 6)
                have b54766 := hb (x 1 5)
                have b54767 := hb (x 2 4)
                have b54768 := hb (x 3 11)
                have b54769 := hb (x 4 10)
                have b54770 := hb (x 5 9)
                have b54771 := hb (x 6 8)
                clear * - r54757 e54758 e54759 e54760 e54761 e54762 e54763 b54764 b54765 b54766 b54767 b54768 b54769 b54770 b54771 d54692 d54708 d54724 d54740 d54668 d54508 g6
                omega
              have d54772 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
                have r54773 := hand2 (x (-1) 1) (x (-1) 7)
                have b54774 := hb (x (-1) 7)
                have b54775 := hb (x (-1) 1 && x (-1) 7)
                clear * - r54773 b54774 b54775 d54756
                omega
              have r54776 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r54777 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e54778 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
              have e54779 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
              have e54780 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
              have e54781 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
              have e54782 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
              have e54783 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
              have r54784 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e54785 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e54786 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e54787 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e54788 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e54789 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e54790 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have r54791 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e54792 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e54793 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e54794 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e54795 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e54796 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e54797 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have r54798 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e54799 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e54800 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have r54801 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e54802 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e54803 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have r54804 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r54805 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r54806 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r54807 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r54808 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r54809 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r54810 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r54811 := hand2 (x (-2) 2) (x (-2) 8)
              have r54812 := hand2 (x (-3) 3) (x (-3) 9)
              have r54813 := hand1 (x (-8) 8) (x (-8) 14)
              have r54814 := hand1 (x (-4) 5) (x (-4) 12)
              have r54815 := hand1 (x (-5) 6) (x (-5) 13)
              have r54816 := hand1 (x (-6) 7) (x (-6) 14)
              have r54817 := hand2 (x (-9) 1) (x (-9) 10)
              have r54818 := hand2 (x (-10) 2) (x (-10) 11)
              have r54819 := hand2 (x (-11) 3) (x (-11) 12)
              have r54820 := hand1 (x (-12) 4) (x (-12) 13)
              have r54821 := hand1 (x (-13) 5) (x (-13) 14)
              have r54822 := hand2 (x 6 1) (x 6 10)
              have r54823 := hand2 (x 5 2) (x 5 11)
              have r54824 := hand1 (x (-4) 2) (x (-4) 12)
              have r54825 := hand1 (x (-5) 3) (x (-5) 13)
              have r54826 := hand1 (x (-6) 4) (x (-6) 14)
              have r54827 := hand1 (x (-2) 2) (x (-2) 12)
              have r54828 := hand2 (x (-2) 2) (x (-2) 12)
              have r54829 := hand1 (x (-3) 3) (x (-3) 13)
              have r54830 := hand2 (x (-3) 3) (x (-3) 13)
              have r54831 := hand2 (x (-1) 2) (x (-1) 13)
              linarith only [r54776, r54777, e54778, e54779, e54780, e54781, e54782, e54783, r54784, e54785, e54786, e54787, e54788, e54789, e54790, r54791, e54792, e54793, e54794, e54795, e54796, e54797, r54798, e54799, e54800, r54801, e54802, e54803, r54804, r54805, r54806, r54807, r54808, r54809, r54810, r54811, r54812, r54813, r54814, r54815, r54816, r54817, r54818, r54819, r54820, r54821, r54822, r54823, r54824, r54825, r54826, r54827, r54828, r54829, r54830, r54831, g1, d54574, g4, d54541, f54463, g6, d54454, f54497, g8, d54655, d54643, d54631, d54772, g34, g35, g36, g37, d54468, g38, g39, g40, d54627, g50, g51, g52, d54688, g53, d54464, d54582]
            · have f54920 : (x 1 1).toNat = 1 := by rw [h54498]; rfl
              have d54921 : (x 2 14).toNat = 0 := by
                have r54922 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b54923 := hb (x 1 1)
                have b54924 := hb (x 2 14)
                clear * - r54922 b54923 b54924 f54920
                omega
              have d54925 : (x 2 1 && x 2 14).toNat = 0 := by
                have r54926 := hand2 (x 2 1) (x 2 14)
                have b54927 := hb (x 2 14)
                have b54928 := hb (x 2 1 && x 2 14)
                clear * - r54926 b54927 b54928 d54921
                omega
              have d54929 : (x 2 6).toNat = 0 := by
                have r54930 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
                have b54931 := hb (x 2 6)
                have b54932 := hb (x 2 14)
                clear * - r54930 b54931 b54932 d54921
                omega
              have d54933 : (x 2 2 && x 2 6).toNat = 0 := by
                have r54934 := hand2 (x 2 2) (x 2 6)
                have b54935 := hb (x 2 6)
                have b54936 := hb (x 2 2 && x 2 6)
                clear * - r54934 b54935 b54936 d54929
                omega
              have d54937 : (x 2 2).toNat = 0 := by
                have r54938 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
                have b54939 := hb (x 2 2)
                have b54940 := hb (x 2 14)
                clear * - r54938 b54939 b54940 d54921
                omega
              have d54941 : (x 2 2 && x 2 13).toNat = 0 := by
                have r54942 := hand1 (x 2 2) (x 2 13)
                have b54943 := hb (x 2 2)
                have b54944 := hb (x 2 2 && x 2 13)
                clear * - r54942 b54943 b54944 d54937
                omega
              have d54945 : (x 2 2 && x 2 12).toNat = 0 := by
                have r54946 := hand1 (x 2 2) (x 2 12)
                have b54947 := hb (x 2 2)
                have b54948 := hb (x 2 2 && x 2 12)
                clear * - r54946 b54947 b54948 d54937
                omega
              have d54949 : (x 2 10).toNat = 0 := by
                have r54950 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
                have b54951 := hb (x 2 2)
                have b54952 := hb (x 2 10)
                clear * - r54950 b54951 b54952 d54937
                omega
              cases h54953 : x (-1) 2
              · have f54954 : (x (-1) 2).toNat = 0 := by rw [h54953]; rfl
                have d54955 : (x (-1) 10).toNat = 0 := by
                  have r54956 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
                  have b54957 := hb (x (-1) 2)
                  have b54958 := hb (x (-1) 10)
                  clear * - r54956 b54957 b54958 f54954
                  omega
                have d54959 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
                  have r54960 := hand2 (x (-1) 1) (x (-1) 10)
                  have b54961 := hb (x (-1) 10)
                  have b54962 := hb (x (-1) 1 && x (-1) 10)
                  clear * - r54960 b54961 b54962 d54955
                  omega
                have d54963 : (x 1 13).toNat = 1 := by
                  have r54964 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b54965 := hb (x (-1) 2)
                  have b54966 := hb (x 1 13)
                  have b54967 := hb (x 0 1 && x 0 14)
                  clear * - r54964 b54965 b54966 b54967 d54426 f54954
                  omega
                have d54968 : (x 2 12).toNat = 0 := by
                  have r54969 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e54970 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                  have e54971 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                  have b54972 := hb (x (-1) 3)
                  have b54973 := hb (x 0 2)
                  have b54974 := hb (x 1 13)
                  have b54975 := hb (x 2 12)
                  clear * - r54969 e54970 e54971 b54972 b54973 b54974 b54975 d54963 d54438
                  omega
                have d54976 : (x 2 4).toNat = 0 := by
                  have r54977 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
                  have b54978 := hb (x 2 4)
                  have b54979 := hb (x 2 12)
                  clear * - r54977 b54978 b54979 d54968
                  omega
                have d54980 : (x 2 4 && x 2 13).toNat = 0 := by
                  have r54981 := hand1 (x 2 4) (x 2 13)
                  have b54982 := hb (x 2 4)
                  have b54983 := hb (x 2 4 && x 2 13)
                  clear * - r54981 b54982 b54983 d54976
                  omega
                have d54984 : (x 2 4 && x 2 8).toNat = 0 := by
                  have r54985 := hand1 (x 2 4) (x 2 8)
                  have b54986 := hb (x 2 4)
                  have b54987 := hb (x 2 4 && x 2 8)
                  clear * - r54985 b54986 b54987 d54976
                  omega
                have d54988 : (x (-1) 3).toNat = 0 := by
                  have r54989 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e54990 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                  have e54991 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                  have b54992 := hb (x (-1) 3)
                  have b54993 := hb (x 0 2)
                  have b54994 := hb (x 1 13)
                  have b54995 := hb (x 2 12)
                  clear * - r54989 e54990 e54991 b54992 b54993 b54994 b54995 d54968 d54963 d54438
                  omega
                have d54996 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
                  have r54997 := hand1 (x (-1) 3) (x (-1) 13)
                  have b54998 := hb (x (-1) 3)
                  have b54999 := hb (x (-1) 3 && x (-1) 13)
                  clear * - r54997 b54998 b54999 d54988
                  omega
                have d55000 : (x (-1) 11).toNat = 0 := by
                  have r55001 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
                  have b55002 := hb (x (-1) 3)
                  have b55003 := hb (x (-1) 11)
                  clear * - r55001 b55002 b55003 d54988
                  omega
                have d55004 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
                  have r55005 := hand2 (x (-1) 1) (x (-1) 11)
                  have b55006 := hb (x (-1) 11)
                  have b55007 := hb (x (-1) 1 && x (-1) 11)
                  clear * - r55005 b55006 b55007 d55000
                  omega
                have d55008 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
                  have r55009 := hand2 (x (-1) 7) (x (-1) 11)
                  have b55010 := hb (x (-1) 11)
                  have b55011 := hb (x (-1) 7 && x (-1) 11)
                  clear * - r55009 b55010 b55011 d55000
                  omega
                cases h55012 : x 1 2
                · have f55013 : (x 1 2).toNat = 0 := by rw [h55012]; rfl
                  have d55014 : (x 3 13).toNat = 1 := by
                    have r55015 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55016 := hb (x 1 2)
                    have b55017 := hb (x 3 13)
                    have b55018 := hb (x 2 1 && x 2 14)
                    clear * - r55015 b55016 b55017 b55018 d54925 f55013
                    omega
                  have d55019 : (x 3 1).toNat = 1 := by
                    have r55020 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                    have b55021 := hb (x 3 1)
                    have b55022 := hb (x 3 13)
                    clear * - r55020 b55021 b55022 d55014
                    omega
                  have d55023 : (x 4 14).toNat = 0 := by
                    have r55024 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55025 := hb (x 3 1)
                    have b55026 := hb (x 4 14)
                    clear * - r55024 b55025 b55026 d55019
                    omega
                  have d55027 : (x 4 3 && x 4 14).toNat = 0 := by
                    have r55028 := hand2 (x 4 3) (x 4 14)
                    have b55029 := hb (x 4 14)
                    have b55030 := hb (x 4 3 && x 4 14)
                    clear * - r55028 b55029 b55030 d55023
                    omega
                  have d55031 : (x 4 6).toNat = 0 := by
                    have r55032 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
                    have b55033 := hb (x 4 6)
                    have b55034 := hb (x 4 14)
                    clear * - r55032 b55033 b55034 d55023
                    omega
                  have d55035 : (x 4 2 && x 4 6).toNat = 0 := by
                    have r55036 := hand2 (x 4 2) (x 4 6)
                    have b55037 := hb (x 4 6)
                    have b55038 := hb (x 4 2 && x 4 6)
                    clear * - r55036 b55037 b55038 d55031
                    omega
                  have d55039 : (x 4 2).toNat = 0 := by
                    have r55040 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                    have b55041 := hb (x 4 2)
                    have b55042 := hb (x 4 14)
                    clear * - r55040 b55041 b55042 d55023
                    omega
                  have d55043 : (x 4 10).toNat = 0 := by
                    have r55044 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                    have b55045 := hb (x 4 2)
                    have b55046 := hb (x 4 10)
                    clear * - r55044 b55045 b55046 d55039
                    omega
                  have d55047 : (x 4 12).toNat = 0 := by
                    have r55048 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55049 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e55050 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b55051 := hb (x 1 3)
                    have b55052 := hb (x 2 2)
                    have b55053 := hb (x 3 13)
                    have b55054 := hb (x 4 12)
                    clear * - r55048 e55049 e55050 b55051 b55052 b55053 b55054 d55014 d54937
                    omega
                  have d55055 : (x 1 3).toNat = 0 := by
                    have r55056 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55057 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e55058 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b55059 := hb (x 1 3)
                    have b55060 := hb (x 2 2)
                    have b55061 := hb (x 3 13)
                    have b55062 := hb (x 4 12)
                    clear * - r55056 e55057 e55058 b55059 b55060 b55061 b55062 d55047 d55014 d54937
                    omega
                  have d55063 : (x 1 3 && x 1 13).toNat = 0 := by
                    have r55064 := hand1 (x 1 3) (x 1 13)
                    have b55065 := hb (x 1 3)
                    have b55066 := hb (x 1 3 && x 1 13)
                    clear * - r55064 b55065 b55066 d55055
                    omega
                  have d55067 : (x 1 11).toNat = 0 := by
                    have r55068 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                    have b55069 := hb (x 1 3)
                    have b55070 := hb (x 1 11)
                    clear * - r55068 b55069 b55070 d55055
                    omega
                  have d55071 : (x 1 1 && x 1 11).toNat = 0 := by
                    have r55072 := hand2 (x 1 1) (x 1 11)
                    have b55073 := hb (x 1 11)
                    have b55074 := hb (x 1 1 && x 1 11)
                    clear * - r55072 b55073 b55074 d55067
                    omega
                  have r55075 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55076 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e55077 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e55078 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e55079 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e55080 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e55081 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have r55082 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55083 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e55084 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e55085 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e55086 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e55087 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e55088 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have r55089 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55090 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                  have e55091 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                  have e55092 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                  have e55093 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                  have e55094 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                  have e55095 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                  have r55096 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55097 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e55098 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have r55099 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55100 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                  have e55101 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                  have r55102 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55103 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e55104 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have r55105 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55106 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
                  have e55107 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
                  have r55108 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55109 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55110 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55111 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55112 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55113 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55114 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
                  have r55115 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                  have r55116 := hand2 (x 3 3) (x 3 7)
                  have r55117 := hand2 (x 1 5) (x 1 9)
                  have r55118 := hand1 (x (-2) 8) (x (-2) 12)
                  have r55119 := hand1 (x (-3) 9) (x (-3) 13)
                  have r55120 := hand1 (x (-2) 2) (x (-2) 11)
                  have r55121 := hand1 (x (-3) 3) (x (-3) 12)
                  have r55122 := hand1 (x (-4) 2) (x (-4) 12)
                  have r55123 := hand1 (x (-5) 3) (x (-5) 13)
                  have r55124 := hand1 (x (-6) 4) (x (-6) 14)
                  have r55125 := hand2 (x (-2) 2) (x (-2) 12)
                  have r55126 := hand2 (x (-3) 3) (x (-3) 13)
                  have r55127 := hand1 (x (-2) 4) (x (-2) 14)
                  have r55128 := hand2 (x 3 1) (x 3 11)
                  have r55129 := hand2 (x 6 1) (x 6 12)
                  have r55130 := hand2 (x 5 2) (x 5 13)
                  linarith only [r55075, e55076, e55077, e55078, e55079, e55080, e55081, r55082, e55083, e55084, e55085, e55086, e55087, e55088, r55089, e55090, e55091, e55092, e55093, e55094, e55095, r55096, e55097, e55098, r55099, e55100, e55101, r55102, e55103, e55104, r55105, e55106, e55107, r55108, r55109, r55110, r55111, r55112, r55113, r55114, r55115, r55116, r55117, r55118, r55119, r55120, r55121, r55122, r55123, r55124, r55125, r55126, r55127, r55128, r55129, r55130, g0, g1, g4, d55000, g7, d54454, f54497, d54949, g10, d55039, d55031, d55043, d55035, d54984, d54420, d55008, d54959, g46, g47, g52, d55004, g53, d55071, d54446, d54996, d54945, d55063, d54430, d55027]
                · have f55208 : (x 1 2).toNat = 1 := by rw [h55012]; rfl
                  have d55209 : (x 3 12).toNat = 0 := by
                    have r55210 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55211 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e55212 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b55213 := hb (x 0 3)
                    have b55214 := hb (x 1 2)
                    have b55215 := hb (x 2 13)
                    have b55216 := hb (x 3 12)
                    clear * - r55210 e55211 e55212 b55213 b55214 b55215 b55216 f55208 f54485
                    omega
                  have d55217 : (x 3 1 && x 3 12).toNat = 0 := by
                    have r55218 := hand2 (x 3 1) (x 3 12)
                    have b55219 := hb (x 3 12)
                    have b55220 := hb (x 3 1 && x 3 12)
                    clear * - r55218 b55219 b55220 d55209
                    omega
                  have d55221 : (x 3 2 && x 3 12).toNat = 0 := by
                    have r55222 := hand2 (x 3 2) (x 3 12)
                    have b55223 := hb (x 3 12)
                    have b55224 := hb (x 3 2 && x 3 12)
                    clear * - r55222 b55223 b55224 d55209
                    omega
                  have d55225 : (x 3 3 && x 3 12).toNat = 0 := by
                    have r55226 := hand2 (x 3 3) (x 3 12)
                    have b55227 := hb (x 3 12)
                    have b55228 := hb (x 3 3 && x 3 12)
                    clear * - r55226 b55227 b55228 d55209
                    omega
                  have d55229 : (x 2 13).toNat = 0 := by
                    have r55230 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55231 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e55232 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b55233 := hb (x 0 3)
                    have b55234 := hb (x 1 2)
                    have b55235 := hb (x 2 13)
                    have b55236 := hb (x 3 12)
                    clear * - r55230 e55231 e55232 b55233 b55234 b55235 b55236 d55209 f55208 f54485
                    omega
                  have d55237 : (x 2 3 && x 2 13).toNat = 0 := by
                    have r55238 := hand2 (x 2 3) (x 2 13)
                    have b55239 := hb (x 2 13)
                    have b55240 := hb (x 2 3 && x 2 13)
                    clear * - r55238 b55239 b55240 d55229
                    omega
                  have d55241 : (x 1 3 && x 1 14).toNat = 1 := by
                    have r55242 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55243 := hb (x 0 4)
                    have b55244 := hb (x 4 11)
                    have b55245 := hb (x 3 1 && x 3 12)
                    have b55246 := hb (x 2 2 && x 2 13)
                    have b55247 := hb (x 1 3 && x 1 14)
                    clear * - r55242 b55243 b55244 b55245 b55246 b55247 g11 d55217 d54941 f54491
                    omega
                  have d55248 : (x 1 3).toNat = 1 := by
                    have r55249 := hand1 (x 1 3) (x 1 14)
                    have b55250 := hb (x 1 3)
                    have b55251 := hb (x 1 3 && x 1 14)
                    clear * - r55249 b55250 b55251 d55241
                    omega
                  have d55252 : (x 4 12).toNat = 0 := by
                    have r55253 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55254 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e55255 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b55256 := hb (x 1 3)
                    have b55257 := hb (x 2 2)
                    have b55258 := hb (x 3 13)
                    have b55259 := hb (x 4 12)
                    clear * - r55253 e55254 e55255 b55256 b55257 b55258 b55259 d54937 d55248
                    omega
                  have d55260 : (x 4 3 && x 4 12).toNat = 0 := by
                    have r55261 := hand2 (x 4 3) (x 4 12)
                    have b55262 := hb (x 4 12)
                    have b55263 := hb (x 4 3 && x 4 12)
                    clear * - r55261 b55262 b55263 d55252
                    omega
                  have d55264 : (x 4 4).toNat = 0 := by
                    have r55265 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                    have b55266 := hb (x 4 4)
                    have b55267 := hb (x 4 12)
                    clear * - r55265 b55266 b55267 d55252
                    omega
                  have d55268 : (x 3 13).toNat = 0 := by
                    have r55269 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55270 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e55271 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b55272 := hb (x 1 3)
                    have b55273 := hb (x 2 2)
                    have b55274 := hb (x 3 13)
                    have b55275 := hb (x 4 12)
                    clear * - r55269 e55270 e55271 b55272 b55273 b55274 b55275 d55252 d54937 d55248
                    omega
                  have d55276 : (x 3 5).toNat = 0 := by
                    have r55277 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                    have b55278 := hb (x 3 5)
                    have b55279 := hb (x 3 13)
                    clear * - r55277 b55278 b55279 d55268
                    omega
                  have d55280 : (x 1 4 && x 1 14).toNat = 1 := by
                    have r55281 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55282 := hb (x 0 5)
                    have b55283 := hb (x 5 10)
                    have b55284 := hb (x 4 1 && x 4 11)
                    have b55285 := hb (x 3 2 && x 3 12)
                    have b55286 := hb (x 2 3 && x 2 13)
                    have b55287 := hb (x 1 4 && x 1 14)
                    clear * - r55281 b55282 b55283 b55284 b55285 b55286 b55287 g12 g54 d55221 d55237 d54476
                    omega
                  have d55288 : (x 1 4).toNat = 1 := by
                    have r55289 := hand1 (x 1 4) (x 1 14)
                    have b55290 := hb (x 1 4)
                    have b55291 := hb (x 1 4 && x 1 14)
                    clear * - r55289 b55290 b55291 d55280
                    omega
                  have d55292 : (x 1 12).toNat = 1 := by
                    have r55293 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                    have b55294 := hb (x 1 4)
                    have b55295 := hb (x 1 12)
                    clear * - r55293 b55294 b55295 d55288
                    omega
                  have d55296 : (x (-2) 3).toNat = 0 := by
                    have r55297 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55298 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                    have e55299 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                    have b55300 := hb (x (-2) 3)
                    have b55301 := hb (x (-1) 2)
                    have b55302 := hb (x 0 13)
                    have b55303 := hb (x 1 12)
                    clear * - r55297 e55298 e55299 b55300 b55301 b55302 b55303 d55292 d54472 f54954
                    omega
                  have d55304 : (x (-2) 11).toNat = 0 := by
                    have r55305 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
                    have b55306 := hb (x (-2) 3)
                    have b55307 := hb (x (-2) 11)
                    clear * - r55305 b55306 b55307 d55296
                    omega
                  have d55308 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
                    have r55309 := hand2 (x (-2) 2) (x (-2) 11)
                    have b55310 := hb (x (-2) 11)
                    have b55311 := hb (x (-2) 2 && x (-2) 11)
                    clear * - r55309 b55310 b55311 d55304
                    omega
                  have d55312 : (x 1 5 && x 1 14).toNat = 1 := by
                    have r55313 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55314 := hb (x 0 6)
                    have b55315 := hb (x 6 9)
                    have b55316 := hb (x 5 1 && x 5 10)
                    have b55317 := hb (x 4 2 && x 4 11)
                    have b55318 := hb (x 3 3 && x 3 12)
                    have b55319 := hb (x 2 4 && x 2 13)
                    have b55320 := hb (x 1 5 && x 1 14)
                    clear * - r55313 b55314 b55315 b55316 b55317 b55318 b55319 b55320 g13 g48 g49 d55225 d54980 g6
                    omega
                  have d55321 : (x 1 5).toNat = 1 := by
                    have r55322 := hand1 (x 1 5) (x 1 14)
                    have b55323 := hb (x 1 5)
                    have b55324 := hb (x 1 5 && x 1 14)
                    clear * - r55322 b55323 b55324 d55312
                    omega
                  have d55325 : (x (-3) 3 && x (-3) 12).toNat = 1 := by
                    have r55326 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55327 := hb (x (-6) 6)
                    have b55328 := hb (x 0 9)
                    have b55329 := hb (x (-1) 1 && x (-1) 10)
                    have b55330 := hb (x (-2) 2 && x (-2) 11)
                    have b55331 := hb (x (-3) 3 && x (-3) 12)
                    have b55332 := hb (x (-4) 4 && x (-4) 13)
                    have b55333 := hb (x (-5) 5 && x (-5) 14)
                    clear * - r55326 b55327 b55328 b55329 b55330 b55331 b55332 b55333 g7 d54959 d55308 g46 g47 g0
                    omega
                  have d55334 : (x (-3) 12).toNat = 1 := by
                    have r55335 := hand2 (x (-3) 3) (x (-3) 12)
                    have b55336 := hb (x (-3) 12)
                    have b55337 := hb (x (-3) 3 && x (-3) 12)
                    clear * - r55335 b55336 b55337 d55325
                    omega
                  have d55338 : (x (-4) 13).toNat = 0 := by
                    have r55339 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55340 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e55341 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b55342 := hb (x (-6) 3)
                    have b55343 := hb (x (-5) 2)
                    have b55344 := hb (x (-4) 13)
                    have b55345 := hb (x (-3) 12)
                    clear * - r55339 e55340 e55341 b55342 b55343 b55344 b55345 d55334
                    omega
                  have d55346 : (x (-5) 2).toNat = 0 := by
                    have r55347 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55348 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e55349 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b55350 := hb (x (-6) 3)
                    have b55351 := hb (x (-5) 2)
                    have b55352 := hb (x (-4) 13)
                    have b55353 := hb (x (-3) 12)
                    clear * - r55347 e55348 e55349 b55350 b55351 b55352 b55353 d55334 d55338
                    omega
                  have d55354 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
                    have r55355 := hand1 (x (-5) 2) (x (-5) 13)
                    have b55356 := hb (x (-5) 2)
                    have b55357 := hb (x (-5) 2 && x (-5) 13)
                    clear * - r55355 b55356 b55357 d55346
                    omega
                  have d55358 : (x (-5) 10).toNat = 0 := by
                    have r55359 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
                    have b55360 := hb (x (-5) 2)
                    have b55361 := hb (x (-5) 10)
                    clear * - r55359 b55360 b55361 d55346
                    omega
                  have d55362 : (x (-6) 3).toNat = 0 := by
                    have r55363 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55364 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                    have e55365 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                    have b55366 := hb (x (-6) 3)
                    have b55367 := hb (x (-5) 2)
                    have b55368 := hb (x (-4) 13)
                    have b55369 := hb (x (-3) 12)
                    clear * - r55363 e55364 e55365 b55366 b55367 b55368 b55369 d55334 d55338 d55346
                    omega
                  have d55370 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
                    have r55371 := hand1 (x (-6) 3) (x (-6) 14)
                    have b55372 := hb (x (-6) 3)
                    have b55373 := hb (x (-6) 3 && x (-6) 14)
                    clear * - r55371 b55372 b55373 d55362
                    omega
                  have d55374 : (x (-6) 11).toNat = 0 := by
                    have r55375 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
                    have b55376 := hb (x (-6) 3)
                    have b55377 := hb (x (-6) 11)
                    clear * - r55375 b55376 b55377 d55362
                    omega
                  have d55378 : (x (-3) 3).toNat = 1 := by
                    have r55379 := hand1 (x (-3) 3) (x (-3) 12)
                    have b55380 := hb (x (-3) 3)
                    have b55381 := hb (x (-3) 3 && x (-3) 12)
                    clear * - r55379 b55380 b55381 d55325
                    omega
                  have d55382 : (x (-1) 13).toNat = 0 := by
                    have r55383 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55384 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                    have e55385 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                    have b55386 := hb (x (-3) 3)
                    have b55387 := hb (x (-2) 2)
                    have b55388 := hb (x (-1) 13)
                    have b55389 := hb (x 0 12)
                    clear * - r55383 e55384 e55385 b55386 b55387 b55388 b55389 f54497 d55378
                    omega
                  have d55390 : (x (-1) 5).toNat = 0 := by
                    have r55391 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
                    have b55392 := hb (x (-1) 5)
                    have b55393 := hb (x (-1) 13)
                    clear * - r55391 b55392 b55393 d55382
                    omega
                  have d55394 : (x (-2) 2).toNat = 0 := by
                    have r55395 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55396 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                    have e55397 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                    have b55398 := hb (x (-3) 3)
                    have b55399 := hb (x (-2) 2)
                    have b55400 := hb (x (-1) 13)
                    have b55401 := hb (x 0 12)
                    clear * - r55395 e55396 e55397 b55398 b55399 b55400 b55401 f54497 d55382 d55378
                    omega
                  have d55402 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
                    have r55403 := hand1 (x (-2) 2) (x (-2) 12)
                    have b55404 := hb (x (-2) 2)
                    have b55405 := hb (x (-2) 2 && x (-2) 12)
                    clear * - r55403 b55404 b55405 d55394
                    omega
                  have d55406 : (x (-3) 3 && x (-3) 13).toNat = 1 := by
                    have r55407 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55408 := hb (x (-5) 5)
                    have b55409 := hb (x 0 10)
                    have b55410 := hb (x (-1) 1 && x (-1) 11)
                    have b55411 := hb (x (-2) 2 && x (-2) 12)
                    have b55412 := hb (x (-3) 3 && x (-3) 13)
                    have b55413 := hb (x (-4) 4 && x (-4) 14)
                    clear * - r55407 b55408 b55409 b55410 b55411 b55412 b55413 d54454 d55004 d55402 g53 g1
                    omega
                  have d55414 : (x (-3) 13).toNat = 1 := by
                    have r55415 := hand2 (x (-3) 3) (x (-3) 13)
                    have b55416 := hb (x (-3) 13)
                    have b55417 := hb (x (-3) 3 && x (-3) 13)
                    clear * - r55415 b55416 b55417 d55406
                    omega
                  have d55418 : (x (-3) 1).toNat = 1 := by
                    have r55419 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                    have b55420 := hb (x (-3) 1)
                    have b55421 := hb (x (-3) 13)
                    clear * - r55419 b55420 b55421 d55414
                    omega
                  have d55422 : (x (-2) 14).toNat = 0 := by
                    have r55423 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55424 := hb (x (-3) 1)
                    have b55425 := hb (x (-2) 14)
                    clear * - r55423 b55424 b55425 d55418
                    omega
                  have d55426 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                    have r55427 := hand2 (x (-2) 1) (x (-2) 14)
                    have b55428 := hb (x (-2) 14)
                    have b55429 := hb (x (-2) 1 && x (-2) 14)
                    clear * - r55427 b55428 b55429 d55422
                    omega
                  have d55430 : (x (-3) 2).toNat = 1 := by
                    have r55431 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55432 := hb (x (-3) 2)
                    have b55433 := hb (x (-1) 13)
                    have b55434 := hb (x (-2) 1 && x (-2) 14)
                    clear * - r55431 b55432 b55433 b55434 d55382 d55426
                    omega
                  have d55435 : (x (-3) 14).toNat = 1 := by
                    have r55436 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                    have b55437 := hb (x (-3) 2)
                    have b55438 := hb (x (-3) 14)
                    clear * - r55436 b55437 b55438 d55430
                    omega
                  have d55439 : (x (-4) 1).toNat = 0 := by
                    have r55440 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55441 := hb (x (-4) 1)
                    have b55442 := hb (x (-3) 14)
                    clear * - r55440 b55441 b55442 d55435
                    omega
                  have d55443 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
                    have r55444 := hand1 (x (-4) 1) (x (-4) 12)
                    have b55445 := hb (x (-4) 1)
                    have b55446 := hb (x (-4) 1 && x (-4) 12)
                    clear * - r55444 b55445 b55446 d55439
                    omega
                  have d55447 : (x (-7) 4).toNat = 1 := by
                    have r55448 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55449 := hb (x (-7) 4)
                    have b55450 := hb (x (-3) 11)
                    have b55451 := hb (x (-4) 1 && x (-4) 12)
                    have b55452 := hb (x (-5) 2 && x (-5) 13)
                    have b55453 := hb (x (-6) 3 && x (-6) 14)
                    clear * - r55448 b55449 b55450 b55451 b55452 b55453 g3 d55443 d55354 d55370
                    omega
                  have d55454 : (x (-7) 12).toNat = 1 := by
                    have r55455 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                    have b55456 := hb (x (-7) 4)
                    have b55457 := hb (x (-7) 12)
                    clear * - r55455 b55456 b55457 d55447
                    omega
                  have d55458 : (x (-8) 13).toNat = 0 := by
                    have r55459 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55460 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                    have e55461 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                    have b55462 := hb (x (-10) 3)
                    have b55463 := hb (x (-9) 2)
                    have b55464 := hb (x (-8) 13)
                    have b55465 := hb (x (-7) 12)
                    clear * - r55459 e55460 e55461 b55462 b55463 b55464 b55465 d55454
                    omega
                  have d55466 : (x (-8) 5).toNat = 0 := by
                    have r55467 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
                    have b55468 := hb (x (-8) 5)
                    have b55469 := hb (x (-8) 13)
                    clear * - r55467 b55468 b55469 d55458
                    omega
                  have d55470 : (x (-4) 9).toNat = 0 := by
                    have r55471 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
                    have b55472 := hb (x (-4) 1)
                    have b55473 := hb (x (-4) 9)
                    clear * - r55471 b55472 b55473 d55439
                    omega
                  have d55474 : (x (-2) 6).toNat = 0 := by
                    have r55475 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
                    have b55476 := hb (x (-2) 6)
                    have b55477 := hb (x (-2) 14)
                    clear * - r55475 b55476 b55477 d55422
                    omega
                  have d55478 : (x (-2) 2 && x (-2) 6).toNat = 0 := by
                    have r55479 := hand2 (x (-2) 2) (x (-2) 6)
                    have b55480 := hb (x (-2) 6)
                    have b55481 := hb (x (-2) 2 && x (-2) 6)
                    clear * - r55479 b55480 b55481 d55474
                    omega
                  have d55482 : (x (-2) 12).toNat = 0 := by
                    have r55483 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55484 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e55485 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b55486 := hb (x (-5) 3)
                    have b55487 := hb (x (-4) 2)
                    have b55488 := hb (x (-3) 13)
                    have b55489 := hb (x (-2) 12)
                    clear * - r55483 e55484 e55485 b55486 b55487 b55488 b55489 d55414
                    omega
                  have d55490 : (x (-4) 2).toNat = 0 := by
                    have r55491 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55492 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e55493 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b55494 := hb (x (-5) 3)
                    have b55495 := hb (x (-4) 2)
                    have b55496 := hb (x (-3) 13)
                    have b55497 := hb (x (-2) 12)
                    clear * - r55491 e55492 e55493 b55494 b55495 b55496 b55497 d55482 d55414
                    omega
                  have d55498 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
                    have r55499 := hand1 (x (-4) 2) (x (-4) 12)
                    have b55500 := hb (x (-4) 2)
                    have b55501 := hb (x (-4) 2 && x (-4) 12)
                    clear * - r55499 b55500 b55501 d55490
                    omega
                  have d55502 : (x (-4) 10).toNat = 0 := by
                    have r55503 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
                    have b55504 := hb (x (-4) 2)
                    have b55505 := hb (x (-4) 10)
                    clear * - r55503 b55504 b55505 d55490
                    omega
                  have d55506 : (x (-5) 3).toNat = 0 := by
                    have r55507 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55508 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e55509 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have b55510 := hb (x (-5) 3)
                    have b55511 := hb (x (-4) 2)
                    have b55512 := hb (x (-3) 13)
                    have b55513 := hb (x (-2) 12)
                    clear * - r55507 e55508 e55509 b55510 b55511 b55512 b55513 d55482 d55414 d55490
                    omega
                  have d55514 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
                    have r55515 := hand1 (x (-5) 3) (x (-5) 13)
                    have b55516 := hb (x (-5) 3)
                    have b55517 := hb (x (-5) 3 && x (-5) 13)
                    clear * - r55515 b55516 b55517 d55506
                    omega
                  have d55518 : (x (-5) 11).toNat = 0 := by
                    have r55519 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                    have b55520 := hb (x (-5) 3)
                    have b55521 := hb (x (-5) 11)
                    clear * - r55519 b55520 b55521 d55506
                    omega
                  have d55522 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
                    have r55523 := hand1 (x (-2) 2) (x (-2) 8)
                    have b55524 := hb (x (-2) 2)
                    have b55525 := hb (x (-2) 2 && x (-2) 8)
                    clear * - r55523 b55524 b55525 d55394
                    omega
                  have d55526 : (x 6 8).toNat = 0 := by
                    have r55527 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55528 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e55529 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e55530 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e55531 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e55532 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e55533 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b55534 := hb (x (-1) 7)
                    have b55535 := hb (x 0 6)
                    have b55536 := hb (x 1 5)
                    have b55537 := hb (x 2 4)
                    have b55538 := hb (x 3 11)
                    have b55539 := hb (x 4 10)
                    have b55540 := hb (x 5 9)
                    have b55541 := hb (x 6 8)
                    clear * - r55527 e55528 e55529 e55530 e55531 e55532 e55533 b55534 b55535 b55536 b55537 b55538 b55539 b55540 b55541 d54976 d55321 g6
                    omega
                  have d55542 : (x 5 9).toNat = 0 := by
                    have r55543 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55544 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e55545 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e55546 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e55547 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e55548 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e55549 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b55550 := hb (x (-1) 7)
                    have b55551 := hb (x 0 6)
                    have b55552 := hb (x 1 5)
                    have b55553 := hb (x 2 4)
                    have b55554 := hb (x 3 11)
                    have b55555 := hb (x 4 10)
                    have b55556 := hb (x 5 9)
                    have b55557 := hb (x 6 8)
                    clear * - r55543 e55544 e55545 e55546 e55547 e55548 e55549 b55550 b55551 b55552 b55553 b55554 b55555 b55556 b55557 d55526 d54976 d55321 g6
                    omega
                  have d55558 : (x 4 10).toNat = 0 := by
                    have r55559 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55560 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e55561 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e55562 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e55563 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e55564 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e55565 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b55566 := hb (x (-1) 7)
                    have b55567 := hb (x 0 6)
                    have b55568 := hb (x 1 5)
                    have b55569 := hb (x 2 4)
                    have b55570 := hb (x 3 11)
                    have b55571 := hb (x 4 10)
                    have b55572 := hb (x 5 9)
                    have b55573 := hb (x 6 8)
                    clear * - r55559 e55560 e55561 e55562 e55563 e55564 e55565 b55566 b55567 b55568 b55569 b55570 b55571 b55572 b55573 d55526 d55542 d54976 d55321 g6
                    omega
                  have d55574 : (x 3 11).toNat = 0 := by
                    have r55575 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55576 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e55577 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e55578 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e55579 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e55580 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e55581 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b55582 := hb (x (-1) 7)
                    have b55583 := hb (x 0 6)
                    have b55584 := hb (x 1 5)
                    have b55585 := hb (x 2 4)
                    have b55586 := hb (x 3 11)
                    have b55587 := hb (x 4 10)
                    have b55588 := hb (x 5 9)
                    have b55589 := hb (x 6 8)
                    clear * - r55575 e55576 e55577 e55578 e55579 e55580 e55581 b55582 b55583 b55584 b55585 b55586 b55587 b55588 b55589 d55526 d55542 d55558 d54976 d55321 g6
                    omega
                  have d55590 : (x (-1) 7).toNat = 0 := by
                    have r55591 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55592 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                    have e55593 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                    have e55594 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                    have e55595 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                    have e55596 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                    have e55597 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                    have b55598 := hb (x (-1) 7)
                    have b55599 := hb (x 0 6)
                    have b55600 := hb (x 1 5)
                    have b55601 := hb (x 2 4)
                    have b55602 := hb (x 3 11)
                    have b55603 := hb (x 4 10)
                    have b55604 := hb (x 5 9)
                    have b55605 := hb (x 6 8)
                    clear * - r55591 e55592 e55593 e55594 e55595 e55596 e55597 b55598 b55599 b55600 b55601 b55602 b55603 b55604 b55605 d55526 d55542 d55558 d55574 d54976 d55321 g6
                    omega
                  have d55606 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
                    have r55607 := hand2 (x (-1) 1) (x (-1) 7)
                    have b55608 := hb (x (-1) 7)
                    have b55609 := hb (x (-1) 1 && x (-1) 7)
                    clear * - r55607 b55608 b55609 d55590
                    omega
                  have d55610 : (x 5 8).toNat = 0 := by
                    have r55611 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55612 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e55613 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e55614 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e55615 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e55616 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e55617 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b55618 := hb (x (-2) 7)
                    have b55619 := hb (x (-1) 6)
                    have b55620 := hb (x 0 5)
                    have b55621 := hb (x 1 4)
                    have b55622 := hb (x 2 11)
                    have b55623 := hb (x 3 10)
                    have b55624 := hb (x 4 9)
                    have b55625 := hb (x 5 8)
                    clear * - r55611 e55612 e55613 e55614 e55615 e55616 e55617 b55618 b55619 b55620 b55621 b55622 b55623 b55624 b55625 d55288 d54476
                    omega
                  have d55626 : (x 4 9).toNat = 0 := by
                    have r55627 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55628 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e55629 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e55630 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e55631 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e55632 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e55633 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b55634 := hb (x (-2) 7)
                    have b55635 := hb (x (-1) 6)
                    have b55636 := hb (x 0 5)
                    have b55637 := hb (x 1 4)
                    have b55638 := hb (x 2 11)
                    have b55639 := hb (x 3 10)
                    have b55640 := hb (x 4 9)
                    have b55641 := hb (x 5 8)
                    clear * - r55627 e55628 e55629 e55630 e55631 e55632 e55633 b55634 b55635 b55636 b55637 b55638 b55639 b55640 b55641 d55610 d55288 d54476
                    omega
                  have d55642 : (x 3 10).toNat = 0 := by
                    have r55643 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55644 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e55645 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e55646 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e55647 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e55648 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e55649 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b55650 := hb (x (-2) 7)
                    have b55651 := hb (x (-1) 6)
                    have b55652 := hb (x 0 5)
                    have b55653 := hb (x 1 4)
                    have b55654 := hb (x 2 11)
                    have b55655 := hb (x 3 10)
                    have b55656 := hb (x 4 9)
                    have b55657 := hb (x 5 8)
                    clear * - r55643 e55644 e55645 e55646 e55647 e55648 e55649 b55650 b55651 b55652 b55653 b55654 b55655 b55656 b55657 d55610 d55626 d55288 d54476
                    omega
                  have d55658 : (x 2 11).toNat = 0 := by
                    have r55659 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55660 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e55661 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e55662 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e55663 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e55664 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e55665 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b55666 := hb (x (-2) 7)
                    have b55667 := hb (x (-1) 6)
                    have b55668 := hb (x 0 5)
                    have b55669 := hb (x 1 4)
                    have b55670 := hb (x 2 11)
                    have b55671 := hb (x 3 10)
                    have b55672 := hb (x 4 9)
                    have b55673 := hb (x 5 8)
                    clear * - r55659 e55660 e55661 e55662 e55663 e55664 e55665 b55666 b55667 b55668 b55669 b55670 b55671 b55672 b55673 d55610 d55626 d55642 d55288 d54476
                    omega
                  have d55674 : (x (-1) 6).toNat = 0 := by
                    have r55675 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55676 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e55677 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e55678 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e55679 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e55680 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e55681 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b55682 := hb (x (-2) 7)
                    have b55683 := hb (x (-1) 6)
                    have b55684 := hb (x 0 5)
                    have b55685 := hb (x 1 4)
                    have b55686 := hb (x 2 11)
                    have b55687 := hb (x 3 10)
                    have b55688 := hb (x 4 9)
                    have b55689 := hb (x 5 8)
                    clear * - r55675 e55676 e55677 e55678 e55679 e55680 e55681 b55682 b55683 b55684 b55685 b55686 b55687 b55688 b55689 d55610 d55626 d55642 d55658 d55288 d54476
                    omega
                  have d55690 : (x (-2) 7).toNat = 0 := by
                    have r55691 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55692 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                    have e55693 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                    have e55694 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                    have e55695 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                    have e55696 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                    have e55697 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                    have b55698 := hb (x (-2) 7)
                    have b55699 := hb (x (-1) 6)
                    have b55700 := hb (x 0 5)
                    have b55701 := hb (x 1 4)
                    have b55702 := hb (x 2 11)
                    have b55703 := hb (x 3 10)
                    have b55704 := hb (x 4 9)
                    have b55705 := hb (x 5 8)
                    clear * - r55691 e55692 e55693 e55694 e55695 e55696 e55697 b55698 b55699 b55700 b55701 b55702 b55703 b55704 b55705 d55610 d55626 d55642 d55658 d55288 d54476 d55674
                    omega
                  have d55706 : (x (-3) 8).toNat = 0 := by
                    have r55707 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55708 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                    have e55709 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                    have e55710 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                    have e55711 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                    have e55712 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                    have e55713 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                    have b55714 := hb (x (-10) 7)
                    have b55715 := hb (x (-9) 6)
                    have b55716 := hb (x (-8) 5)
                    have b55717 := hb (x (-7) 4)
                    have b55718 := hb (x (-6) 11)
                    have b55719 := hb (x (-5) 10)
                    have b55720 := hb (x (-4) 9)
                    have b55721 := hb (x (-3) 8)
                    clear * - r55707 e55708 e55709 e55710 e55711 e55712 e55713 b55714 b55715 b55716 b55717 b55718 b55719 b55720 b55721 d55470 d55358 d55374 d55447 d55466
                    omega
                  have r55722 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55723 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55724 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55725 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e55726 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e55727 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e55728 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e55729 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e55730 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have r55731 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55732 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e55733 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e55734 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e55735 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e55736 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e55737 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have r55738 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55739 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                  have e55740 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                  have e55741 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                  have e55742 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                  have e55743 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                  have e55744 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                  have r55745 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55746 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
                  have e55747 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
                  have r55748 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55749 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                  have e55750 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                  have r55751 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55752 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55753 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55754 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55755 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r55756 : (x (-10) 2).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp2 (-10))
                  have r55757 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                  have r55758 := hand2 (x (-3) 3) (x (-3) 7)
                  have r55759 := hand2 (x (-8) 8) (x (-8) 12)
                  have r55760 := hand2 (x (-9) 9) (x (-9) 13)
                  have r55761 := hand2 (x 1 3) (x 1 7)
                  have r55762 := hand1 (x (-4) 8) (x (-4) 12)
                  have r55763 := hand1 (x (-5) 9) (x (-5) 13)
                  have r55764 := hand2 (x (-3) 3) (x (-3) 9)
                  have r55765 := hand1 (x (-8) 8) (x (-8) 14)
                  have r55766 := hand2 (x 6 1) (x 6 10)
                  have r55767 := hand2 (x 5 2) (x 5 11)
                  have r55768 := hand1 (x (-6) 4) (x (-6) 14)
                  have r55769 := hand2 (x (-9) 1) (x (-9) 14)
                  have r55770 := hand1 (x 3 1) (x 3 14)
                  linarith only [r55722, r55723, r55724, e55725, e55726, e55727, e55728, e55729, e55730, r55731, e55732, e55733, e55734, e55735, e55736, e55737, r55738, e55739, e55740, e55741, e55742, e55743, e55744, r55745, e55746, e55747, r55748, e55749, e55750, r55751, r55752, r55753, r55754, r55755, r55756, r55757, r55758, r55759, r55760, r55761, r55762, r55763, r55764, r55765, r55766, r55767, r55768, r55769, r55770, d55458, d55454, d55374, d55358, d55518, d55470, d55502, d55706, d55474, d55690, g4, d55390, d55674, f54491, d54476, g6, d55248, d55288, g8, d54937, d54929, d55276, d55264, d55478, g19, g20, g21, g22, d54933, d54492, g23, g24, g25, d55606, d55522, g34, g35, g36, g37, d55260, g50, g51, g52, d55498, d55514]
              · have f55863 : (x (-1) 2).toNat = 1 := by rw [h54953]; rfl
                have d55864 : (x (-1) 14).toNat = 1 := by
                  have r55865 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
                  have b55866 := hb (x (-1) 2)
                  have b55867 := hb (x (-1) 14)
                  clear * - r55865 b55866 b55867 f55863
                  omega
                have d55868 : (x (-2) 1).toNat = 0 := by
                  have r55869 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b55870 := hb (x (-2) 1)
                  have b55871 := hb (x (-1) 14)
                  clear * - r55869 b55870 b55871 d55864
                  omega
                have d55872 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                  have r55873 := hand1 (x (-2) 1) (x (-2) 14)
                  have b55874 := hb (x (-2) 1)
                  have b55875 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r55873 b55874 b55875 d55868
                  omega
                have d55876 : (x (-2) 13).toNat = 0 := by
                  have r55877 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                  have b55878 := hb (x (-2) 1)
                  have b55879 := hb (x (-2) 13)
                  clear * - r55877 b55878 b55879 d55868
                  omega
                have d55880 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
                  have r55881 := hand2 (x (-2) 4) (x (-2) 13)
                  have b55882 := hb (x (-2) 13)
                  have b55883 := hb (x (-2) 4 && x (-2) 13)
                  clear * - r55881 b55882 b55883 d55876
                  omega
                have d55884 : (x (-2) 9).toNat = 0 := by
                  have r55885 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                  have b55886 := hb (x (-2) 1)
                  have b55887 := hb (x (-2) 9)
                  clear * - r55885 b55886 b55887 d55868
                  omega
                have d55888 : (x 1 12).toNat = 0 := by
                  have r55889 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e55890 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                  have e55891 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                  have b55892 := hb (x (-2) 3)
                  have b55893 := hb (x (-1) 2)
                  have b55894 := hb (x 0 13)
                  have b55895 := hb (x 1 12)
                  clear * - r55889 e55890 e55891 b55892 b55893 b55894 b55895 d54472 f55863
                  omega
                have d55896 : (x 1 1 && x 1 12).toNat = 0 := by
                  have r55897 := hand2 (x 1 1) (x 1 12)
                  have b55898 := hb (x 1 12)
                  have b55899 := hb (x 1 1 && x 1 12)
                  clear * - r55897 b55898 b55899 d55888
                  omega
                have d55900 : (x 1 4).toNat = 0 := by
                  have r55901 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                  have b55902 := hb (x 1 4)
                  have b55903 := hb (x 1 12)
                  clear * - r55901 b55902 b55903 d55888
                  omega
                have d55904 : (x 1 4 && x 1 14).toNat = 0 := by
                  have r55905 := hand1 (x 1 4) (x 1 14)
                  have b55906 := hb (x 1 4)
                  have b55907 := hb (x 1 4 && x 1 14)
                  clear * - r55905 b55906 b55907 d55900
                  omega
                cases h55908 : x 1 2
                · have f55909 : (x 1 2).toNat = 0 := by rw [h55908]; rfl
                  have d55910 : (x 1 10).toNat = 0 := by
                    have r55911 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
                    have b55912 := hb (x 1 2)
                    have b55913 := hb (x 1 10)
                    clear * - r55911 b55912 b55913 f55909
                    omega
                  have d55914 : (x 1 1 && x 1 10).toNat = 0 := by
                    have r55915 := hand2 (x 1 1) (x 1 10)
                    have b55916 := hb (x 1 10)
                    have b55917 := hb (x 1 1 && x 1 10)
                    clear * - r55915 b55916 b55917 d55910
                    omega
                  have d55918 : (x 3 13).toNat = 1 := by
                    have r55919 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55920 := hb (x 1 2)
                    have b55921 := hb (x 3 13)
                    have b55922 := hb (x 2 1 && x 2 14)
                    clear * - r55919 b55920 b55921 b55922 d54925 f55909
                    omega
                  have d55923 : (x 3 1).toNat = 1 := by
                    have r55924 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                    have b55925 := hb (x 3 1)
                    have b55926 := hb (x 3 13)
                    clear * - r55924 b55925 b55926 d55918
                    omega
                  have d55927 : (x 4 14).toNat = 0 := by
                    have r55928 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55929 := hb (x 3 1)
                    have b55930 := hb (x 4 14)
                    clear * - r55928 b55929 b55930 d55923
                    omega
                  have d55931 : (x 4 3 && x 4 14).toNat = 0 := by
                    have r55932 := hand2 (x 4 3) (x 4 14)
                    have b55933 := hb (x 4 14)
                    have b55934 := hb (x 4 3 && x 4 14)
                    clear * - r55932 b55933 b55934 d55927
                    omega
                  have d55935 : (x 4 6).toNat = 0 := by
                    have r55936 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
                    have b55937 := hb (x 4 6)
                    have b55938 := hb (x 4 14)
                    clear * - r55936 b55937 b55938 d55927
                    omega
                  have d55939 : (x 4 2).toNat = 0 := by
                    have r55940 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                    have b55941 := hb (x 4 2)
                    have b55942 := hb (x 4 14)
                    clear * - r55940 b55941 b55942 d55927
                    omega
                  have d55943 : (x 4 10).toNat = 0 := by
                    have r55944 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                    have b55945 := hb (x 4 2)
                    have b55946 := hb (x 4 10)
                    clear * - r55944 b55945 b55946 d55939
                    omega
                  have d55947 : (x 4 3 && x 4 10).toNat = 0 := by
                    have r55948 := hand2 (x 4 3) (x 4 10)
                    have b55949 := hb (x 4 10)
                    have b55950 := hb (x 4 3 && x 4 10)
                    clear * - r55948 b55949 b55950 d55943
                    omega
                  have d55951 : (x 4 12).toNat = 0 := by
                    have r55952 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55953 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e55954 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b55955 := hb (x 1 3)
                    have b55956 := hb (x 2 2)
                    have b55957 := hb (x 3 13)
                    have b55958 := hb (x 4 12)
                    clear * - r55952 e55953 e55954 b55955 b55956 b55957 b55958 d55918 d54937
                    omega
                  have d55959 : (x 1 3).toNat = 0 := by
                    have r55960 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55961 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e55962 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b55963 := hb (x 1 3)
                    have b55964 := hb (x 2 2)
                    have b55965 := hb (x 3 13)
                    have b55966 := hb (x 4 12)
                    clear * - r55960 e55961 e55962 b55963 b55964 b55965 b55966 d55951 d55918 d54937
                    omega
                  have d55967 : (x 1 3 && x 1 14).toNat = 0 := by
                    have r55968 := hand1 (x 1 3) (x 1 14)
                    have b55969 := hb (x 1 3)
                    have b55970 := hb (x 1 3 && x 1 14)
                    clear * - r55968 b55969 b55970 d55959
                    omega
                  have d55971 : (x 1 11).toNat = 0 := by
                    have r55972 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                    have b55973 := hb (x 1 3)
                    have b55974 := hb (x 1 11)
                    clear * - r55972 b55973 b55974 d55959
                    omega
                  have d55975 : (x 1 1 && x 1 11).toNat = 0 := by
                    have r55976 := hand2 (x 1 1) (x 1 11)
                    have b55977 := hb (x 1 11)
                    have b55978 := hb (x 1 1 && x 1 11)
                    clear * - r55976 b55977 b55978 d55971
                    omega
                  have d55979 : (x 3 1 && x 3 12).toNat = 1 := by
                    have r55980 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b55981 := hb (x 0 4)
                    have b55982 := hb (x 4 11)
                    have b55983 := hb (x 3 1 && x 3 12)
                    have b55984 := hb (x 2 2 && x 2 13)
                    have b55985 := hb (x 1 3 && x 1 14)
                    clear * - r55980 b55981 b55982 b55983 b55984 b55985 g11 d54941 d55967 f54491
                    omega
                  have d55986 : (x 3 12).toNat = 1 := by
                    have r55987 := hand2 (x 3 1) (x 3 12)
                    have b55988 := hb (x 3 12)
                    have b55989 := hb (x 3 1 && x 3 12)
                    clear * - r55987 b55988 b55989 d55979
                    omega
                  have d55990 : (x 2 13).toNat = 0 := by
                    have r55991 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e55992 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e55993 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b55994 := hb (x 0 3)
                    have b55995 := hb (x 1 2)
                    have b55996 := hb (x 2 13)
                    have b55997 := hb (x 3 12)
                    clear * - r55991 e55992 e55993 b55994 b55995 b55996 b55997 d55986 f55909 f54485
                    omega
                  have d55998 : (x 2 3 && x 2 13).toNat = 0 := by
                    have r55999 := hand2 (x 2 3) (x 2 13)
                    have b56000 := hb (x 2 13)
                    have b56001 := hb (x 2 3 && x 2 13)
                    clear * - r55999 b56000 b56001 d55990
                    omega
                  have d56002 : (x 2 4 && x 2 13).toNat = 0 := by
                    have r56003 := hand2 (x 2 4) (x 2 13)
                    have b56004 := hb (x 2 13)
                    have b56005 := hb (x 2 4 && x 2 13)
                    clear * - r56003 b56004 b56005 d55990
                    omega
                  have d56006 : (x 2 8 && x 2 13).toNat = 0 := by
                    have r56007 := hand2 (x 2 8) (x 2 13)
                    have b56008 := hb (x 2 13)
                    have b56009 := hb (x 2 8 && x 2 13)
                    clear * - r56007 b56008 b56009 d55990
                    omega
                  have d56010 : (x 2 12 && x 2 13).toNat = 0 := by
                    have r56011 := hand2 (x 2 12) (x 2 13)
                    have b56012 := hb (x 2 13)
                    have b56013 := hb (x 2 12 && x 2 13)
                    clear * - r56011 b56012 b56013 d55990
                    omega
                  have d56014 : (x 3 2 && x 3 12).toNat = 1 := by
                    have r56015 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b56016 := hb (x 0 5)
                    have b56017 := hb (x 5 10)
                    have b56018 := hb (x 4 1 && x 4 11)
                    have b56019 := hb (x 3 2 && x 3 12)
                    have b56020 := hb (x 2 3 && x 2 13)
                    have b56021 := hb (x 1 4 && x 1 14)
                    clear * - r56015 b56016 b56017 b56018 b56019 b56020 b56021 g12 g54 d55998 d55904 d54476
                    omega
                  have d56022 : (x 3 2).toNat = 1 := by
                    have r56023 := hand1 (x 3 2) (x 3 12)
                    have b56024 := hb (x 3 2)
                    have b56025 := hb (x 3 2 && x 3 12)
                    clear * - r56023 b56024 b56025 d56014
                    omega
                  have d56026 : (x 3 14).toNat = 1 := by
                    have r56027 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                    have b56028 := hb (x 3 2)
                    have b56029 := hb (x 3 14)
                    clear * - r56027 b56028 b56029 d56022
                    omega
                  have d56030 : (x 2 1).toNat = 0 := by
                    have r56031 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b56032 := hb (x 2 1)
                    have b56033 := hb (x 3 14)
                    clear * - r56031 b56032 b56033 d56026
                    omega
                  have d56034 : (x 2 9).toNat = 0 := by
                    have r56035 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
                    have b56036 := hb (x 2 1)
                    have b56037 := hb (x 2 9)
                    clear * - r56035 b56036 b56037 d56030
                    omega
                  have d56038 : (x 5 12).toNat = 0 := by
                    have r56039 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56040 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e56041 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b56042 := hb (x 2 3)
                    have b56043 := hb (x 3 2)
                    have b56044 := hb (x 4 13)
                    have b56045 := hb (x 5 12)
                    clear * - r56039 e56040 e56041 b56042 b56043 b56044 b56045 d56022
                    omega
                  have d56046 : (x 4 13).toNat = 0 := by
                    have r56047 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56048 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e56049 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b56050 := hb (x 2 3)
                    have b56051 := hb (x 3 2)
                    have b56052 := hb (x 4 13)
                    have b56053 := hb (x 5 12)
                    clear * - r56047 e56048 e56049 b56050 b56051 b56052 b56053 d56038 d56022
                    omega
                  have d56054 : (x 2 3).toNat = 0 := by
                    have r56055 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56056 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e56057 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b56058 := hb (x 2 3)
                    have b56059 := hb (x 3 2)
                    have b56060 := hb (x 4 13)
                    have b56061 := hb (x 5 12)
                    clear * - r56055 e56056 e56057 b56058 b56059 b56060 b56061 d56038 d56046 d56022
                    omega
                  have d56062 : (x 2 11).toNat = 0 := by
                    have r56063 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
                    have b56064 := hb (x 2 3)
                    have b56065 := hb (x 2 11)
                    clear * - r56063 b56064 b56065 d56054
                    omega
                  cases h56066 : x (-1) 3
                  · have f56067 : (x (-1) 3).toNat = 0 := by rw [h56066]; rfl
                    have d56068 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
                      have r56069 := hand1 (x (-1) 3) (x (-1) 14)
                      have b56070 := hb (x (-1) 3)
                      have b56071 := hb (x (-1) 3 && x (-1) 14)
                      clear * - r56069 b56070 b56071 f56067
                      omega
                    have d56072 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
                      have r56073 := hand1 (x (-1) 3) (x (-1) 13)
                      have b56074 := hb (x (-1) 3)
                      have b56075 := hb (x (-1) 3 && x (-1) 13)
                      clear * - r56073 b56074 b56075 f56067
                      omega
                    have d56076 : (x (-2) 4).toNat = 1 := by
                      have r56077 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b56078 := hb (x (-2) 4)
                      have b56079 := hb (x 2 11)
                      have b56080 := hb (x 1 1 && x 1 12)
                      have b56081 := hb (x 0 2 && x 0 13)
                      have b56082 := hb (x (-1) 3 && x (-1) 14)
                      clear * - r56077 b56078 b56079 b56080 b56081 b56082 d56062 d55896 d54442 d56068
                      omega
                    have d56083 : (x (-2) 12).toNat = 1 := by
                      have r56084 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
                      have b56085 := hb (x (-2) 4)
                      have b56086 := hb (x (-2) 12)
                      clear * - r56084 b56085 b56086 d56076
                      omega
                    have d56087 : (x (-3) 13).toNat = 0 := by
                      have r56088 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56089 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e56090 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b56091 := hb (x (-5) 3)
                      have b56092 := hb (x (-4) 2)
                      have b56093 := hb (x (-3) 13)
                      have b56094 := hb (x (-2) 12)
                      clear * - r56088 e56089 e56090 b56091 b56092 b56093 b56094 d56083
                      omega
                    have d56095 : (x (-3) 5).toNat = 0 := by
                      have r56096 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
                      have b56097 := hb (x (-3) 5)
                      have b56098 := hb (x (-3) 13)
                      clear * - r56096 b56097 b56098 d56087
                      omega
                    have d56099 : (x (-4) 2).toNat = 0 := by
                      have r56100 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56101 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                      have e56102 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                      have b56103 := hb (x (-5) 3)
                      have b56104 := hb (x (-4) 2)
                      have b56105 := hb (x (-3) 13)
                      have b56106 := hb (x (-2) 12)
                      clear * - r56100 e56101 e56102 b56103 b56104 b56105 b56106 d56083 d56087
                      omega
                    have d56107 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
                      have r56108 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b56109 := hb (x (-4) 2)
                      have b56110 := hb (x (-2) 13)
                      have b56111 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r56108 b56109 b56110 b56111 d55876 d56099
                      omega
                    have d56112 : (x (-3) 1).toNat = 1 := by
                      have r56113 := hand1 (x (-3) 1) (x (-3) 14)
                      have b56114 := hb (x (-3) 1)
                      have b56115 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r56113 b56114 b56115 d56107
                      omega
                    have d56116 : (x (-2) 14).toNat = 0 := by
                      have r56117 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b56118 := hb (x (-3) 1)
                      have b56119 := hb (x (-2) 14)
                      clear * - r56117 b56118 b56119 d56112
                      omega
                    have d56120 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
                      have r56121 := hand2 (x (-2) 4) (x (-2) 14)
                      have b56122 := hb (x (-2) 14)
                      have b56123 := hb (x (-2) 4 && x (-2) 14)
                      clear * - r56121 b56122 b56123 d56116
                      omega
                    have r56124 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b56125 := hb (x (-3) 5)
                    have b56126 := hb (x 2 10)
                    have b56127 := hb (x 1 1 && x 1 11)
                    have b56128 := hb (x 0 2 && x 0 12)
                    have b56129 := hb (x (-1) 3 && x (-1) 13)
                    have b56130 := hb (x (-2) 4 && x (-2) 14)
                    linarith only [r56124, b56125, b56126, b56127, b56128, b56129, b56130, d54949, d55975, d54446, d56072, d56120, d56095]
                  · have f56131 : (x (-1) 3).toNat = 1 := by rw [h56066]; rfl
                    have d56132 : (x 2 12).toNat = 0 := by
                      have r56133 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56134 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                      have e56135 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                      have b56136 := hb (x (-1) 3)
                      have b56137 := hb (x 0 2)
                      have b56138 := hb (x 1 13)
                      have b56139 := hb (x 2 12)
                      clear * - r56133 e56134 e56135 b56136 b56137 b56138 b56139 d54438 f56131
                      omega
                    have d56140 : (x 1 13).toNat = 0 := by
                      have r56141 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56142 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
                      have e56143 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
                      have b56144 := hb (x (-1) 3)
                      have b56145 := hb (x 0 2)
                      have b56146 := hb (x 1 13)
                      have b56147 := hb (x 2 12)
                      clear * - r56141 e56142 e56143 b56144 b56145 b56146 b56147 d56132 d54438 f56131
                      omega
                    have d56148 : (x 1 13 && x 1 14).toNat = 0 := by
                      have r56149 := hand1 (x 1 13) (x 1 14)
                      have b56150 := hb (x 1 13)
                      have b56151 := hb (x 1 13 && x 1 14)
                      clear * - r56149 b56150 b56151 d56140
                      omega
                    have d56152 : (x 1 5).toNat = 0 := by
                      have r56153 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
                      have b56154 := hb (x 1 5)
                      have b56155 := hb (x 1 13)
                      clear * - r56153 b56154 b56155 d56140
                      omega
                    have d56156 : (x 1 5 && x 1 14).toNat = 0 := by
                      have r56157 := hand1 (x 1 5) (x 1 14)
                      have b56158 := hb (x 1 5)
                      have b56159 := hb (x 1 5 && x 1 14)
                      clear * - r56157 b56158 b56159 d56152
                      omega
                    have d56160 : (x 3 3 && x 3 12).toNat = 1 := by
                      have r56161 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b56162 := hb (x 0 6)
                      have b56163 := hb (x 6 9)
                      have b56164 := hb (x 5 1 && x 5 10)
                      have b56165 := hb (x 4 2 && x 4 11)
                      have b56166 := hb (x 3 3 && x 3 12)
                      have b56167 := hb (x 2 4 && x 2 13)
                      have b56168 := hb (x 1 5 && x 1 14)
                      clear * - r56161 b56162 b56163 b56164 b56165 b56166 b56167 b56168 g13 g48 g49 d56002 d56156 g6
                      omega
                    have d56169 : (x 3 3).toNat = 1 := by
                      have r56170 := hand1 (x 3 3) (x 3 12)
                      have b56171 := hb (x 3 3)
                      have b56172 := hb (x 3 3 && x 3 12)
                      clear * - r56170 b56171 b56172 d56160
                      omega
                    have d56173 : (x 6 12).toNat = 0 := by
                      have r56174 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56175 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e56176 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b56177 := hb (x 3 3)
                      have b56178 := hb (x 4 2)
                      have b56179 := hb (x 5 13)
                      have b56180 := hb (x 6 12)
                      clear * - r56174 e56175 e56176 b56177 b56178 b56179 b56180 d55939 d56169
                      omega
                    have d56181 : (x 6 1 && x 6 12).toNat = 0 := by
                      have r56182 := hand2 (x 6 1) (x 6 12)
                      have b56183 := hb (x 6 12)
                      have b56184 := hb (x 6 1 && x 6 12)
                      clear * - r56182 b56183 b56184 d56173
                      omega
                    have d56185 : (x 6 4).toNat = 0 := by
                      have r56186 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                      have b56187 := hb (x 6 4)
                      have b56188 := hb (x 6 12)
                      clear * - r56186 b56187 b56188 d56173
                      omega
                    have d56189 : (x 5 13).toNat = 0 := by
                      have r56190 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56191 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e56192 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b56193 := hb (x 3 3)
                      have b56194 := hb (x 4 2)
                      have b56195 := hb (x 5 13)
                      have b56196 := hb (x 6 12)
                      clear * - r56190 e56191 e56192 b56193 b56194 b56195 b56196 d56173 d55939 d56169
                      omega
                    have d56197 : (x 5 2 && x 5 13).toNat = 0 := by
                      have r56198 := hand2 (x 5 2) (x 5 13)
                      have b56199 := hb (x 5 13)
                      have b56200 := hb (x 5 2 && x 5 13)
                      clear * - r56198 b56199 b56200 d56189
                      omega
                    have d56201 : (x 7 11).toNat = 1 := by
                      have r56202 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b56203 := hb (x 3 4)
                      have b56204 := hb (x 7 11)
                      have b56205 := hb (x 6 1 && x 6 12)
                      have b56206 := hb (x 5 2 && x 5 13)
                      have b56207 := hb (x 4 3 && x 4 14)
                      clear * - r56202 b56203 b56204 b56205 b56206 b56207 d56181 d56197 d55931 g10
                      omega
                    have d56208 : (x 7 3).toNat = 1 := by
                      have r56209 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                      have b56210 := hb (x 7 3)
                      have b56211 := hb (x 7 11)
                      clear * - r56209 b56210 b56211 d56201
                      omega
                    have d56212 : (x 10 12).toNat = 0 := by
                      have r56213 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56214 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                      have e56215 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                      have b56216 := hb (x 7 3)
                      have b56217 := hb (x 8 2)
                      have b56218 := hb (x 9 13)
                      have b56219 := hb (x 10 12)
                      clear * - r56213 e56214 e56215 b56216 b56217 b56218 b56219 d56208
                      omega
                    have d56220 : (x 10 4).toNat = 0 := by
                      have r56221 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                      have b56222 := hb (x 10 4)
                      have b56223 := hb (x 10 12)
                      clear * - r56221 b56222 b56223 d56212
                      omega
                    have d56224 : (x 10 4 && x 10 13).toNat = 0 := by
                      have r56225 := hand1 (x 10 4) (x 10 13)
                      have b56226 := hb (x 10 4)
                      have b56227 := hb (x 10 4 && x 10 13)
                      clear * - r56225 b56226 b56227 d56220
                      omega
                    have d56228 : (x 10 4 && x 10 5).toNat = 0 := by
                      have r56229 := hand1 (x 10 4) (x 10 5)
                      have b56230 := hb (x 10 4)
                      have b56231 := hb (x 10 4 && x 10 5)
                      clear * - r56229 b56230 b56231 d56220
                      omega
                    have d56232 : (x 9 13).toNat = 0 := by
                      have r56233 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56234 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                      have e56235 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                      have b56236 := hb (x 7 3)
                      have b56237 := hb (x 8 2)
                      have b56238 := hb (x 9 13)
                      have b56239 := hb (x 10 12)
                      clear * - r56233 e56234 e56235 b56236 b56237 b56238 b56239 d56212 d56208
                      omega
                    have d56240 : (x 9 5).toNat = 0 := by
                      have r56241 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
                      have b56242 := hb (x 9 5)
                      have b56243 := hb (x 9 13)
                      clear * - r56241 b56242 b56243 d56232
                      omega
                    have d56244 : (x 9 5 && x 9 14).toNat = 0 := by
                      have r56245 := hand1 (x 9 5) (x 9 14)
                      have b56246 := hb (x 9 5)
                      have b56247 := hb (x 9 5 && x 9 14)
                      clear * - r56245 b56246 b56247 d56240
                      omega
                    have d56248 : (x 9 5 && x 9 6).toNat = 0 := by
                      have r56249 := hand1 (x 9 5) (x 9 6)
                      have b56250 := hb (x 9 5)
                      have b56251 := hb (x 9 5 && x 9 6)
                      clear * - r56249 b56250 b56251 d56240
                      omega
                    have d56252 : (x 8 2).toNat = 0 := by
                      have r56253 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56254 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                      have e56255 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                      have b56256 := hb (x 7 3)
                      have b56257 := hb (x 8 2)
                      have b56258 := hb (x 9 13)
                      have b56259 := hb (x 10 12)
                      clear * - r56253 e56254 e56255 b56256 b56257 b56258 b56259 d56212 d56232 d56208
                      omega
                    have d56260 : (x 8 2 && x 8 7).toNat = 0 := by
                      have r56261 := hand1 (x 8 2) (x 8 7)
                      have b56262 := hb (x 8 2)
                      have b56263 := hb (x 8 2 && x 8 7)
                      clear * - r56261 b56262 b56263 d56252
                      omega
                    have d56264 : (x 8 10).toNat = 0 := by
                      have r56265 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                      have b56266 := hb (x 8 2)
                      have b56267 := hb (x 8 10)
                      clear * - r56265 b56266 b56267 d56252
                      omega
                    have d56268 : (x 5 5).toNat = 0 := by
                      have r56269 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                      have b56270 := hb (x 5 5)
                      have b56271 := hb (x 5 13)
                      clear * - r56269 b56270 b56271 d56189
                      omega
                    have d56272 : (x 10 8).toNat = 0 := by
                      have r56273 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56274 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                      have e56275 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                      have e56276 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                      have e56277 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                      have e56278 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                      have e56279 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                      have b56280 := hb (x 3 7)
                      have b56281 := hb (x 4 6)
                      have b56282 := hb (x 5 5)
                      have b56283 := hb (x 6 4)
                      have b56284 := hb (x 7 11)
                      have b56285 := hb (x 8 10)
                      have b56286 := hb (x 9 9)
                      have b56287 := hb (x 10 8)
                      clear * - r56273 e56274 e56275 e56276 e56277 e56278 e56279 b56280 b56281 b56282 b56283 b56284 b56285 b56286 b56287 d56264 d56201 d56185 d56268 d55935
                      omega
                    have d56288 : (x 9 9).toNat = 0 := by
                      have r56289 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56290 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                      have e56291 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                      have e56292 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                      have e56293 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                      have e56294 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                      have e56295 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                      have b56296 := hb (x 3 7)
                      have b56297 := hb (x 4 6)
                      have b56298 := hb (x 5 5)
                      have b56299 := hb (x 6 4)
                      have b56300 := hb (x 7 11)
                      have b56301 := hb (x 8 10)
                      have b56302 := hb (x 9 9)
                      have b56303 := hb (x 10 8)
                      clear * - r56289 e56290 e56291 e56292 e56293 e56294 e56295 b56296 b56297 b56298 b56299 b56300 b56301 b56302 b56303 d56272 d56264 d56201 d56185 d56268 d55935
                      omega
                    have d56304 : (x 3 7).toNat = 0 := by
                      have r56305 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e56306 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                      have e56307 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                      have e56308 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                      have e56309 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                      have e56310 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                      have e56311 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                      have b56312 := hb (x 3 7)
                      have b56313 := hb (x 4 6)
                      have b56314 := hb (x 5 5)
                      have b56315 := hb (x 6 4)
                      have b56316 := hb (x 7 11)
                      have b56317 := hb (x 8 10)
                      have b56318 := hb (x 9 9)
                      have b56319 := hb (x 10 8)
                      clear * - r56305 e56306 e56307 e56308 e56309 e56310 e56311 b56312 b56313 b56314 b56315 b56316 b56317 b56318 b56319 d56272 d56288 d56264 d56201 d56185 d56268 d55935
                      omega
                    have d56320 : (x 3 7 && x 3 12).toNat = 0 := by
                      have r56321 := hand1 (x 3 7) (x 3 12)
                      have b56322 := hb (x 3 7)
                      have b56323 := hb (x 3 7 && x 3 12)
                      clear * - r56321 b56322 b56323 d56304
                      omega
                    have r56324 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56325 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56326 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56327 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                    have e56328 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                    have e56329 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                    have e56330 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                    have e56331 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                    have e56332 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                    have r56333 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56334 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                    have e56335 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                    have e56336 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                    have e56337 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                    have e56338 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                    have e56339 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                    have r56340 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56341 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e56342 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e56343 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e56344 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e56345 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e56346 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have r56347 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56348 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e56349 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have r56350 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56351 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                    have e56352 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                    have r56353 : 1 ≤ (x 14 1).toNat + (x 13 1 && x 13 2).toNat + (x 12 2 && x 12 3).toNat + (x 11 3 && x 11 4).toNat + (x 10 4 && x 10 5).toNat + (x 9 5 && x 9 6).toNat + (x 8 6 && x 8 7).toNat + (x 7 7 && x 7 8).toNat + (x 6 8 && x 6 9).toNat + (x 5 9 && x 5 10).toNat + (x 4 10 && x 4 11).toNat + (x 3 11 && x 3 12).toNat + (x 2 12 && x 2 13).toNat + (x 1 13 && x 1 14).toNat + (x 0 14).toNat := by have q := hcov1 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56354 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56355 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56356 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56357 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56358 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56359 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56360 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56361 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r56362 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
                    have r56363 := hand2 (x 13 1) (x 13 2)
                    have r56364 := hand2 (x 12 2) (x 12 3)
                    have r56365 := hand2 (x 11 3) (x 11 4)
                    have r56366 := hand2 (x 8 6) (x 8 7)
                    have r56367 := hand1 (x 3 11) (x 3 12)
                    have r56368 := hand2 (x 9 1) (x 9 6)
                    have r56369 := hand1 (x 1 9) (x 1 14)
                    have r56370 := hand2 (x 6 1) (x 6 8)
                    have r56371 := hand2 (x 5 2) (x 5 9)
                    have r56372 := hand1 (x (-4) 3) (x (-4) 12)
                    have r56373 := hand1 (x (-5) 4) (x (-5) 13)
                    have r56374 := hand1 (x (-6) 5) (x (-6) 14)
                    have r56375 := hand2 (x (-1) 3) (x (-1) 12)
                    have r56376 := hand1 (x (-3) 5) (x (-3) 14)
                    have r56377 := hand2 (x 13 1) (x 13 10)
                    have r56378 := hand2 (x 12 2) (x 12 11)
                    have r56379 := hand1 (x 11 3) (x 11 12)
                    have r56380 := hand2 (x (-1) 1) (x (-1) 11)
                    have r56381 := hand1 (x (-2) 2) (x (-2) 12)
                    have r56382 := hand1 (x (-3) 3) (x (-3) 13)
                    have r56383 := hand1 (x 13 1) (x 13 14)
                    linarith only [r56324, r56325, r56326, e56327, e56328, e56329, e56330, e56331, e56332, r56333, e56334, e56335, e56336, e56337, e56338, e56339, r56340, e56341, e56342, e56343, e56344, e56345, e56346, r56347, e56348, e56349, r56350, e56351, e56352, r56353, r56354, r56355, r56356, r56357, r56358, r56359, r56360, r56361, r56362, r56363, r56364, r56365, r56366, r56367, r56368, r56369, r56370, r56371, r56372, r56373, r56374, r56375, r56376, r56377, r56378, r56379, r56380, r56381, r56382, r56383, g1, d55884, d55876, g5, d54454, f54497, f54425, d56140, d54480, d56034, d56132, d55990, d55986, d55943, g11, g12, g13, g14, d56240, d56220, d56228, d56248, g15, g16, g17, g18, d56010, d56148, d56260, g30, g31, g32, g33, d56320, d56006, d55947, g41, g42, g43, d54434, g44, g45, d55914, d54450, d55880, d56224, d56244, g53, d55872]
                · have f56494 : (x 1 2).toNat = 1 := by rw [h55908]; rfl
                  have d56495 : (x 3 12).toNat = 0 := by
                    have r56496 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56497 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e56498 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b56499 := hb (x 0 3)
                    have b56500 := hb (x 1 2)
                    have b56501 := hb (x 2 13)
                    have b56502 := hb (x 3 12)
                    clear * - r56496 e56497 e56498 b56499 b56500 b56501 b56502 f56494 f54485
                    omega
                  have d56503 : (x 3 2 && x 3 12).toNat = 0 := by
                    have r56504 := hand2 (x 3 2) (x 3 12)
                    have b56505 := hb (x 3 12)
                    have b56506 := hb (x 3 2 && x 3 12)
                    clear * - r56504 b56505 b56506 d56495
                    omega
                  have d56507 : (x 2 13).toNat = 0 := by
                    have r56508 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e56509 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
                    have e56510 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
                    have b56511 := hb (x 0 3)
                    have b56512 := hb (x 1 2)
                    have b56513 := hb (x 2 13)
                    have b56514 := hb (x 3 12)
                    clear * - r56508 e56509 e56510 b56511 b56512 b56513 b56514 d56495 f56494 f54485
                    omega
                  have d56515 : (x 2 3 && x 2 13).toNat = 0 := by
                    have r56516 := hand2 (x 2 3) (x 2 13)
                    have b56517 := hb (x 2 13)
                    have b56518 := hb (x 2 3 && x 2 13)
                    clear * - r56516 b56517 b56518 d56507
                    omega
                  have r56519 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b56520 := hb (x 0 5)
                  have b56521 := hb (x 5 10)
                  have b56522 := hb (x 4 1 && x 4 11)
                  have b56523 := hb (x 3 2 && x 3 12)
                  have b56524 := hb (x 2 3 && x 2 13)
                  have b56525 := hb (x 1 4 && x 1 14)
                  linarith only [r56519, b56520, b56521, b56522, b56523, b56524, b56525, g12, g54, d56503, d56515, d55904, d54476]
          · have f56526 : (x 0 12).toNat = 1 := by rw [h54496]; rfl
            have d56527 : (x (-1) 13).toNat = 0 := by
              have r56528 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e56529 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e56530 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have b56531 := hb (x (-3) 3)
              have b56532 := hb (x (-2) 2)
              have b56533 := hb (x (-1) 13)
              have b56534 := hb (x 0 12)
              clear * - r56528 e56529 e56530 b56531 b56532 b56533 b56534 f56526
              omega
            have d56535 : (x (-2) 2).toNat = 0 := by
              have r56536 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e56537 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e56538 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have b56539 := hb (x (-3) 3)
              have b56540 := hb (x (-2) 2)
              have b56541 := hb (x (-1) 13)
              have b56542 := hb (x 0 12)
              clear * - r56536 e56537 e56538 b56539 b56540 b56541 b56542 f56526 d56527
              omega
            have d56543 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
              have r56544 := hand1 (x (-2) 2) (x (-2) 13)
              have b56545 := hb (x (-2) 2)
              have b56546 := hb (x (-2) 2 && x (-2) 13)
              clear * - r56544 b56545 b56546 d56535
              omega
            have d56547 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
              have r56548 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b56549 := hb (x (-2) 2)
              have b56550 := hb (x 0 13)
              have b56551 := hb (x (-1) 1 && x (-1) 14)
              clear * - r56548 b56549 b56550 b56551 d54472 d56535
              omega
            have d56552 : (x (-1) 14).toNat = 1 := by
              have r56553 := hand2 (x (-1) 1) (x (-1) 14)
              have b56554 := hb (x (-1) 14)
              have b56555 := hb (x (-1) 1 && x (-1) 14)
              clear * - r56553 b56554 b56555 d56547
              omega
            have d56556 : (x (-2) 1).toNat = 0 := by
              have r56557 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b56558 := hb (x (-2) 1)
              have b56559 := hb (x (-1) 14)
              clear * - r56557 b56558 b56559 d56552
              omega
            have d56560 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
              have r56561 := hand1 (x (-2) 1) (x (-2) 14)
              have b56562 := hb (x (-2) 1)
              have b56563 := hb (x (-2) 1 && x (-2) 14)
              clear * - r56561 b56562 b56563 d56556
              omega
            have d56564 : (x (-3) 2).toNat = 1 := by
              have r56565 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b56566 := hb (x (-3) 2)
              have b56567 := hb (x (-1) 13)
              have b56568 := hb (x (-2) 1 && x (-2) 14)
              clear * - r56565 b56566 b56567 b56568 d56527 d56560
              omega
            have d56569 : (x (-2) 13).toNat = 0 := by
              have r56570 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b56571 := hb (x (-2) 1)
              have b56572 := hb (x (-2) 13)
              clear * - r56570 b56571 b56572 d56556
              omega
            have d56573 : (x (-3) 3).toNat = 0 := by
              have r56574 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e56575 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e56576 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have b56577 := hb (x (-3) 3)
              have b56578 := hb (x (-2) 2)
              have b56579 := hb (x (-1) 13)
              have b56580 := hb (x 0 12)
              clear * - r56574 e56575 e56576 b56577 b56578 b56579 b56580 f56526 d56527 d56535
              omega
            have d56581 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
              have r56582 := hand1 (x (-3) 3) (x (-3) 14)
              have b56583 := hb (x (-3) 3)
              have b56584 := hb (x (-3) 3 && x (-3) 14)
              clear * - r56582 b56583 b56584 d56573
              omega
            have d56585 : (x (-1) 12).toNat = 0 := by
              have r56586 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e56587 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e56588 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b56589 := hb (x (-4) 3)
              have b56590 := hb (x (-3) 2)
              have b56591 := hb (x (-2) 13)
              have b56592 := hb (x (-1) 12)
              clear * - r56586 e56587 e56588 b56589 b56590 b56591 b56592 d56569 d56564
              omega
            have d56593 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
              have r56594 := hand2 (x (-1) 1) (x (-1) 12)
              have b56595 := hb (x (-1) 12)
              have b56596 := hb (x (-1) 1 && x (-1) 12)
              clear * - r56594 b56595 b56596 d56585
              omega
            have r56597 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b56598 := hb (x (-4) 4)
            have b56599 := hb (x 0 11)
            have b56600 := hb (x (-1) 1 && x (-1) 12)
            have b56601 := hb (x (-2) 2 && x (-2) 13)
            have b56602 := hb (x (-3) 3 && x (-3) 14)
            linarith only [r56597, b56598, b56599, b56600, b56601, b56602, d54486, d56593, d56543, d56581, g2]
        · have f56603 : (x 0 4).toNat = 1 := by rw [h54490]; rfl
          have d56604 : (x 0 12).toNat = 1 := by
            have r56605 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
            have b56606 := hb (x 0 4)
            have b56607 := hb (x 0 12)
            clear * - r56605 b56606 b56607 f56603
            omega
          have d56608 : (x (-1) 13).toNat = 0 := by
            have r56609 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e56610 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e56611 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b56612 := hb (x (-3) 3)
            have b56613 := hb (x (-2) 2)
            have b56614 := hb (x (-1) 13)
            have b56615 := hb (x 0 12)
            clear * - r56609 e56610 e56611 b56612 b56613 b56614 b56615 d56604
            omega
          have d56616 : (x (-2) 2).toNat = 0 := by
            have r56617 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e56618 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e56619 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b56620 := hb (x (-3) 3)
            have b56621 := hb (x (-2) 2)
            have b56622 := hb (x (-1) 13)
            have b56623 := hb (x 0 12)
            clear * - r56617 e56618 e56619 b56620 b56621 b56622 b56623 d56604 d56608
            omega
          have d56624 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
            have r56625 := hand1 (x (-2) 2) (x (-2) 13)
            have b56626 := hb (x (-2) 2)
            have b56627 := hb (x (-2) 2 && x (-2) 13)
            clear * - r56625 b56626 b56627 d56616
            omega
          have d56628 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
            have r56629 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b56630 := hb (x (-2) 2)
            have b56631 := hb (x 0 13)
            have b56632 := hb (x (-1) 1 && x (-1) 14)
            clear * - r56629 b56630 b56631 b56632 d54472 d56616
            omega
          have d56633 : (x (-1) 14).toNat = 1 := by
            have r56634 := hand2 (x (-1) 1) (x (-1) 14)
            have b56635 := hb (x (-1) 14)
            have b56636 := hb (x (-1) 1 && x (-1) 14)
            clear * - r56634 b56635 b56636 d56628
            omega
          have d56637 : (x (-2) 1).toNat = 0 := by
            have r56638 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b56639 := hb (x (-2) 1)
            have b56640 := hb (x (-1) 14)
            clear * - r56638 b56639 b56640 d56633
            omega
          have d56641 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r56642 := hand1 (x (-2) 1) (x (-2) 14)
            have b56643 := hb (x (-2) 1)
            have b56644 := hb (x (-2) 1 && x (-2) 14)
            clear * - r56642 b56643 b56644 d56637
            omega
          have d56645 : (x (-3) 2).toNat = 1 := by
            have r56646 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b56647 := hb (x (-3) 2)
            have b56648 := hb (x (-1) 13)
            have b56649 := hb (x (-2) 1 && x (-2) 14)
            clear * - r56646 b56647 b56648 b56649 d56608 d56641
            omega
          have d56650 : (x (-2) 13).toNat = 0 := by
            have r56651 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b56652 := hb (x (-2) 1)
            have b56653 := hb (x (-2) 13)
            clear * - r56651 b56652 b56653 d56637
            omega
          have d56654 : (x (-3) 3).toNat = 0 := by
            have r56655 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e56656 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e56657 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b56658 := hb (x (-3) 3)
            have b56659 := hb (x (-2) 2)
            have b56660 := hb (x (-1) 13)
            have b56661 := hb (x 0 12)
            clear * - r56655 e56656 e56657 b56658 b56659 b56660 b56661 d56604 d56608 d56616
            omega
          have d56662 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
            have r56663 := hand1 (x (-3) 3) (x (-3) 14)
            have b56664 := hb (x (-3) 3)
            have b56665 := hb (x (-3) 3 && x (-3) 14)
            clear * - r56663 b56664 b56665 d56654
            omega
          have d56666 : (x (-1) 12).toNat = 0 := by
            have r56667 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e56668 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e56669 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b56670 := hb (x (-4) 3)
            have b56671 := hb (x (-3) 2)
            have b56672 := hb (x (-2) 13)
            have b56673 := hb (x (-1) 12)
            clear * - r56667 e56668 e56669 b56670 b56671 b56672 b56673 d56650 d56645
            omega
          have d56674 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
            have r56675 := hand2 (x (-1) 1) (x (-1) 12)
            have b56676 := hb (x (-1) 12)
            have b56677 := hb (x (-1) 1 && x (-1) 12)
            clear * - r56675 b56676 b56677 d56666
            omega
          have r56678 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b56679 := hb (x (-4) 4)
          have b56680 := hb (x 0 11)
          have b56681 := hb (x (-1) 1 && x (-1) 12)
          have b56682 := hb (x (-2) 2 && x (-2) 13)
          have b56683 := hb (x (-3) 3 && x (-3) 14)
          linarith only [r56678, b56679, b56680, b56681, b56682, b56683, d54486, d56674, d56624, d56662, g2]
      · have f56684 : (x 0 3).toNat = 1 := by rw [h54484]; rfl
        have d56685 : (x 3 12).toNat = 0 := by
          have r56686 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56687 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e56688 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b56689 := hb (x 0 3)
          have b56690 := hb (x 1 2)
          have b56691 := hb (x 2 13)
          have b56692 := hb (x 3 12)
          clear * - r56686 e56687 e56688 b56689 b56690 b56691 b56692 f56684
          omega
        have d56693 : (x 3 1 && x 3 12).toNat = 0 := by
          have r56694 := hand2 (x 3 1) (x 3 12)
          have b56695 := hb (x 3 12)
          have b56696 := hb (x 3 1 && x 3 12)
          clear * - r56694 b56695 b56696 d56685
          omega
        have d56697 : (x 3 2 && x 3 12).toNat = 0 := by
          have r56698 := hand2 (x 3 2) (x 3 12)
          have b56699 := hb (x 3 12)
          have b56700 := hb (x 3 2 && x 3 12)
          clear * - r56698 b56699 b56700 d56685
          omega
        have d56701 : (x 2 13).toNat = 0 := by
          have r56702 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56703 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e56704 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b56705 := hb (x 0 3)
          have b56706 := hb (x 1 2)
          have b56707 := hb (x 2 13)
          have b56708 := hb (x 3 12)
          clear * - r56702 e56703 e56704 b56705 b56706 b56707 b56708 d56685 f56684
          omega
        have d56709 : (x 2 2 && x 2 13).toNat = 0 := by
          have r56710 := hand2 (x 2 2) (x 2 13)
          have b56711 := hb (x 2 13)
          have b56712 := hb (x 2 2 && x 2 13)
          clear * - r56710 b56711 b56712 d56701
          omega
        have d56713 : (x 2 3 && x 2 13).toNat = 0 := by
          have r56714 := hand2 (x 2 3) (x 2 13)
          have b56715 := hb (x 2 13)
          have b56716 := hb (x 2 3 && x 2 13)
          clear * - r56714 b56715 b56716 d56701
          omega
        have d56717 : (x 1 1 && x 1 14).toNat = 1 := by
          have r56718 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b56719 := hb (x 0 2)
          have b56720 := hb (x 2 13)
          have b56721 := hb (x 1 1 && x 1 14)
          clear * - r56718 b56719 b56720 b56721 d56701 d54438
          omega
        have d56722 : (x 1 1).toNat = 1 := by
          have r56723 := hand1 (x 1 1) (x 1 14)
          have b56724 := hb (x 1 1)
          have b56725 := hb (x 1 1 && x 1 14)
          clear * - r56723 b56724 b56725 d56717
          omega
        have d56726 : (x 2 14).toNat = 0 := by
          have r56727 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b56728 := hb (x 1 1)
          have b56729 := hb (x 2 14)
          clear * - r56727 b56728 b56729 d56722
          omega
        have d56730 : (x 2 1 && x 2 14).toNat = 0 := by
          have r56731 := hand2 (x 2 1) (x 2 14)
          have b56732 := hb (x 2 14)
          have b56733 := hb (x 2 1 && x 2 14)
          clear * - r56731 b56732 b56733 d56726
          omega
        have d56734 : (x 2 2).toNat = 0 := by
          have r56735 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b56736 := hb (x 2 2)
          have b56737 := hb (x 2 14)
          clear * - r56735 b56736 b56737 d56726
          omega
        have d56738 : (x 1 2).toNat = 0 := by
          have r56739 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56740 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e56741 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b56742 := hb (x 0 3)
          have b56743 := hb (x 1 2)
          have b56744 := hb (x 2 13)
          have b56745 := hb (x 3 12)
          clear * - r56739 e56740 e56741 b56742 b56743 b56744 b56745 d56685 d56701 f56684
          omega
        have d56746 : (x 3 13).toNat = 1 := by
          have r56747 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b56748 := hb (x 1 2)
          have b56749 := hb (x 3 13)
          have b56750 := hb (x 2 1 && x 2 14)
          clear * - r56747 b56748 b56749 b56750 d56730 d56738
          omega
        have d56751 : (x 4 12).toNat = 0 := by
          have r56752 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56753 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e56754 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b56755 := hb (x 1 3)
          have b56756 := hb (x 2 2)
          have b56757 := hb (x 3 13)
          have b56758 := hb (x 4 12)
          clear * - r56752 e56753 e56754 b56755 b56756 b56757 b56758 d56746 d56734
          omega
        have d56759 : (x 1 3).toNat = 0 := by
          have r56760 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56761 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e56762 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b56763 := hb (x 1 3)
          have b56764 := hb (x 2 2)
          have b56765 := hb (x 3 13)
          have b56766 := hb (x 4 12)
          clear * - r56760 e56761 e56762 b56763 b56764 b56765 b56766 d56751 d56746 d56734
          omega
        have d56767 : (x 1 3 && x 1 14).toNat = 0 := by
          have r56768 := hand1 (x 1 3) (x 1 14)
          have b56769 := hb (x 1 3)
          have b56770 := hb (x 1 3 && x 1 14)
          clear * - r56768 b56769 b56770 d56759
          omega
        have d56771 : (x 0 4).toNat = 1 := by
          have r56772 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b56773 := hb (x 0 4)
          have b56774 := hb (x 4 11)
          have b56775 := hb (x 3 1 && x 3 12)
          have b56776 := hb (x 2 2 && x 2 13)
          have b56777 := hb (x 1 3 && x 1 14)
          clear * - r56772 b56773 b56774 b56775 b56776 b56777 g11 d56693 d56709 d56767
          omega
        have d56778 : (x 0 12).toNat = 1 := by
          have r56779 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
          have b56780 := hb (x 0 4)
          have b56781 := hb (x 0 12)
          clear * - r56779 b56780 b56781 d56771
          omega
        have d56782 : (x (-1) 13).toNat = 0 := by
          have r56783 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56784 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e56785 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b56786 := hb (x (-3) 3)
          have b56787 := hb (x (-2) 2)
          have b56788 := hb (x (-1) 13)
          have b56789 := hb (x 0 12)
          clear * - r56783 e56784 e56785 b56786 b56787 b56788 b56789 d56778
          omega
        have d56790 : (x (-2) 2).toNat = 0 := by
          have r56791 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56792 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e56793 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b56794 := hb (x (-3) 3)
          have b56795 := hb (x (-2) 2)
          have b56796 := hb (x (-1) 13)
          have b56797 := hb (x 0 12)
          clear * - r56791 e56792 e56793 b56794 b56795 b56796 b56797 d56778 d56782
          omega
        have d56798 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
          have r56799 := hand1 (x (-2) 2) (x (-2) 12)
          have b56800 := hb (x (-2) 2)
          have b56801 := hb (x (-2) 2 && x (-2) 12)
          clear * - r56799 b56800 b56801 d56790
          omega
        have d56802 : (x (-3) 3).toNat = 0 := by
          have r56803 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56804 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e56805 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b56806 := hb (x (-3) 3)
          have b56807 := hb (x (-2) 2)
          have b56808 := hb (x (-1) 13)
          have b56809 := hb (x 0 12)
          clear * - r56803 e56804 e56805 b56806 b56807 b56808 b56809 d56778 d56782 d56790
          omega
        have d56810 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
          have r56811 := hand1 (x (-3) 3) (x (-3) 13)
          have b56812 := hb (x (-3) 3)
          have b56813 := hb (x (-3) 3 && x (-3) 13)
          clear * - r56811 b56812 b56813 d56802
          omega
        have d56814 : (x 1 4 && x 1 14).toNat = 1 := by
          have r56815 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b56816 := hb (x 0 5)
          have b56817 := hb (x 5 10)
          have b56818 := hb (x 4 1 && x 4 11)
          have b56819 := hb (x 3 2 && x 3 12)
          have b56820 := hb (x 2 3 && x 2 13)
          have b56821 := hb (x 1 4 && x 1 14)
          clear * - r56815 b56816 b56817 b56818 b56819 b56820 b56821 g12 g54 d56697 d56713 d54476
          omega
        have d56822 : (x 1 4).toNat = 1 := by
          have r56823 := hand1 (x 1 4) (x 1 14)
          have b56824 := hb (x 1 4)
          have b56825 := hb (x 1 4 && x 1 14)
          clear * - r56823 b56824 b56825 d56814
          omega
        have d56826 : (x 1 12).toNat = 1 := by
          have r56827 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b56828 := hb (x 1 4)
          have b56829 := hb (x 1 12)
          clear * - r56827 b56828 b56829 d56822
          omega
        have d56830 : (x (-1) 2).toNat = 0 := by
          have r56831 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56832 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e56833 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b56834 := hb (x (-2) 3)
          have b56835 := hb (x (-1) 2)
          have b56836 := hb (x 0 13)
          have b56837 := hb (x 1 12)
          clear * - r56831 e56832 e56833 b56834 b56835 b56836 b56837 d56826 d54472
          omega
        have d56838 : (x 1 13).toNat = 1 := by
          have r56839 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b56840 := hb (x (-1) 2)
          have b56841 := hb (x 1 13)
          have b56842 := hb (x 0 1 && x 0 14)
          clear * - r56839 b56840 b56841 b56842 d54426 d56830
          omega
        have d56843 : (x 2 12).toNat = 0 := by
          have r56844 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56845 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e56846 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b56847 := hb (x (-1) 3)
          have b56848 := hb (x 0 2)
          have b56849 := hb (x 1 13)
          have b56850 := hb (x 2 12)
          clear * - r56844 e56845 e56846 b56847 b56848 b56849 b56850 d56838 d54438
          omega
        have d56851 : (x (-1) 3).toNat = 0 := by
          have r56852 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e56853 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e56854 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b56855 := hb (x (-1) 3)
          have b56856 := hb (x 0 2)
          have b56857 := hb (x 1 13)
          have b56858 := hb (x 2 12)
          clear * - r56852 e56853 e56854 b56855 b56856 b56857 b56858 d56843 d56838 d54438
          omega
        have d56859 : (x (-1) 11).toNat = 0 := by
          have r56860 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
          have b56861 := hb (x (-1) 3)
          have b56862 := hb (x (-1) 11)
          clear * - r56860 b56861 b56862 d56851
          omega
        have d56863 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
          have r56864 := hand2 (x (-1) 1) (x (-1) 11)
          have b56865 := hb (x (-1) 11)
          have b56866 := hb (x (-1) 1 && x (-1) 11)
          clear * - r56864 b56865 b56866 d56859
          omega
        have r56867 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b56868 := hb (x (-5) 5)
        have b56869 := hb (x 0 10)
        have b56870 := hb (x (-1) 1 && x (-1) 11)
        have b56871 := hb (x (-2) 2 && x (-2) 12)
        have b56872 := hb (x (-3) 3 && x (-3) 13)
        have b56873 := hb (x (-4) 4 && x (-4) 14)
        linarith only [r56867, b56868, b56869, b56870, b56871, b56872, b56873, d54454, d56863, d56798, d56810, g53, g1]
    · have f56874 : (x 0 1).toNat = 1 := by rw [h54462]; rfl
      have d56875 : (x 1 14).toNat = 0 := by
        have r56876 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b56877 := hb (x 0 1)
        have b56878 := hb (x 1 14)
        clear * - r56876 b56877 b56878 f56874
        omega
      have d56879 : (x 1 1 && x 1 14).toNat = 0 := by
        have r56880 := hand2 (x 1 1) (x 1 14)
        have b56881 := hb (x 1 14)
        have b56882 := hb (x 1 1 && x 1 14)
        clear * - r56880 b56881 b56882 d56875
        omega
      have d56883 : (x 1 4 && x 1 14).toNat = 0 := by
        have r56884 := hand2 (x 1 4) (x 1 14)
        have b56885 := hb (x 1 14)
        have b56886 := hb (x 1 4 && x 1 14)
        clear * - r56884 b56885 b56886 d56875
        omega
      have d56887 : (x 1 5 && x 1 14).toNat = 0 := by
        have r56888 := hand2 (x 1 5) (x 1 14)
        have b56889 := hb (x 1 14)
        have b56890 := hb (x 1 5 && x 1 14)
        clear * - r56888 b56889 b56890 d56875
        omega
      have d56891 : (x 1 2).toNat = 0 := by
        have r56892 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
        have b56893 := hb (x 1 2)
        have b56894 := hb (x 1 14)
        clear * - r56892 b56893 b56894 d56875
        omega
      have d56895 : (x 2 13).toNat = 1 := by
        have r56896 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b56897 := hb (x 0 2)
        have b56898 := hb (x 2 13)
        have b56899 := hb (x 1 1 && x 1 14)
        clear * - r56896 b56897 b56898 b56899 d56879 d54438
        omega
      have d56900 : (x 2 1).toNat = 1 := by
        have r56901 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
        have b56902 := hb (x 2 1)
        have b56903 := hb (x 2 13)
        clear * - r56901 b56902 b56903 d56895
        omega
      have d56904 : (x 3 14).toNat = 0 := by
        have r56905 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b56906 := hb (x 2 1)
        have b56907 := hb (x 3 14)
        clear * - r56905 b56906 b56907 d56900
        omega
      have d56908 : (x 3 1 && x 3 14).toNat = 0 := by
        have r56909 := hand2 (x 3 1) (x 3 14)
        have b56910 := hb (x 3 14)
        have b56911 := hb (x 3 1 && x 3 14)
        clear * - r56909 b56910 b56911 d56904
        omega
      have d56912 : (x 3 2).toNat = 0 := by
        have r56913 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b56914 := hb (x 3 2)
        have b56915 := hb (x 3 14)
        clear * - r56913 b56914 b56915 d56904
        omega
      have d56916 : (x 3 2 && x 3 12).toNat = 0 := by
        have r56917 := hand1 (x 3 2) (x 3 12)
        have b56918 := hb (x 3 2)
        have b56919 := hb (x 3 2 && x 3 12)
        clear * - r56917 b56918 b56919 d56912
        omega
      have d56920 : (x 3 12).toNat = 0 := by
        have r56921 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e56922 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e56923 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b56924 := hb (x 0 3)
        have b56925 := hb (x 1 2)
        have b56926 := hb (x 2 13)
        have b56927 := hb (x 3 12)
        clear * - r56921 e56922 e56923 b56924 b56925 b56926 b56927 d56895 d56891
        omega
      have d56928 : (x 3 3 && x 3 12).toNat = 0 := by
        have r56929 := hand2 (x 3 3) (x 3 12)
        have b56930 := hb (x 3 12)
        have b56931 := hb (x 3 3 && x 3 12)
        clear * - r56929 b56930 b56931 d56920
        omega
      have d56932 : (x 2 4 && x 2 13).toNat = 1 := by
        have r56933 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b56934 := hb (x 0 6)
        have b56935 := hb (x 6 9)
        have b56936 := hb (x 5 1 && x 5 10)
        have b56937 := hb (x 4 2 && x 4 11)
        have b56938 := hb (x 3 3 && x 3 12)
        have b56939 := hb (x 2 4 && x 2 13)
        have b56940 := hb (x 1 5 && x 1 14)
        clear * - r56933 b56934 b56935 b56936 b56937 b56938 b56939 b56940 g13 g48 g49 d56928 d56887 g6
        omega
      have d56941 : (x 2 4).toNat = 1 := by
        have r56942 := hand1 (x 2 4) (x 2 13)
        have b56943 := hb (x 2 4)
        have b56944 := hb (x 2 4 && x 2 13)
        clear * - r56942 b56943 b56944 d56932
        omega
      have d56945 : (x 2 12).toNat = 1 := by
        have r56946 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
        have b56947 := hb (x 2 4)
        have b56948 := hb (x 2 12)
        clear * - r56946 b56947 b56948 d56941
        omega
      have d56949 : (x 1 13).toNat = 0 := by
        have r56950 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e56951 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e56952 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b56953 := hb (x (-1) 3)
        have b56954 := hb (x 0 2)
        have b56955 := hb (x 1 13)
        have b56956 := hb (x 2 12)
        clear * - r56950 e56951 e56952 b56953 b56954 b56955 b56956 d56945 d54438
        omega
      have d56957 : (x 1 5).toNat = 0 := by
        have r56958 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
        have b56959 := hb (x 1 5)
        have b56960 := hb (x 1 13)
        clear * - r56958 b56959 b56960 d56949
        omega
      have d56961 : (x (-1) 2).toNat = 1 := by
        have r56962 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b56963 := hb (x (-1) 2)
        have b56964 := hb (x 1 13)
        have b56965 := hb (x 0 1 && x 0 14)
        clear * - r56962 b56963 b56964 b56965 d56949 d54426
        omega
      have d56966 : (x 1 12).toNat = 0 := by
        have r56967 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e56968 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e56969 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b56970 := hb (x (-2) 3)
        have b56971 := hb (x (-1) 2)
        have b56972 := hb (x 0 13)
        have b56973 := hb (x 1 12)
        clear * - r56967 e56968 e56969 b56970 b56971 b56972 b56973 d56961
        omega
      have d56974 : (x 0 13).toNat = 0 := by
        have r56975 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e56976 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e56977 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b56978 := hb (x (-2) 3)
        have b56979 := hb (x (-1) 2)
        have b56980 := hb (x 0 13)
        have b56981 := hb (x 1 12)
        clear * - r56975 e56976 e56977 b56978 b56979 b56980 b56981 d56966 d56961
        omega
      have d56982 : (x 0 5).toNat = 0 := by
        have r56983 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
        have b56984 := hb (x 0 5)
        have b56985 := hb (x 0 13)
        clear * - r56983 b56984 b56985 d56974
        omega
      have d56986 : (x 2 3 && x 2 13).toNat = 1 := by
        have r56987 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b56988 := hb (x 0 5)
        have b56989 := hb (x 5 10)
        have b56990 := hb (x 4 1 && x 4 11)
        have b56991 := hb (x 3 2 && x 3 12)
        have b56992 := hb (x 2 3 && x 2 13)
        have b56993 := hb (x 1 4 && x 1 14)
        clear * - r56987 b56988 b56989 b56990 b56991 b56992 b56993 g12 g54 d56916 d56883 d56982
        omega
      have d56994 : (x 2 3).toNat = 1 := by
        have r56995 := hand1 (x 2 3) (x 2 13)
        have b56996 := hb (x 2 3)
        have b56997 := hb (x 2 3 && x 2 13)
        clear * - r56995 b56996 b56997 d56986
        omega
      have d56998 : (x 5 12).toNat = 0 := by
        have r56999 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57000 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e57001 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b57002 := hb (x 2 3)
        have b57003 := hb (x 3 2)
        have b57004 := hb (x 4 13)
        have b57005 := hb (x 5 12)
        clear * - r56999 e57000 e57001 b57002 b57003 b57004 b57005 d56912 d56994
        omega
      have d57006 : (x 4 13).toNat = 0 := by
        have r57007 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57008 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e57009 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b57010 := hb (x 2 3)
        have b57011 := hb (x 3 2)
        have b57012 := hb (x 4 13)
        have b57013 := hb (x 5 12)
        clear * - r57007 e57008 e57009 b57010 b57011 b57012 b57013 d56998 d56912 d56994
        omega
      have d57014 : (x 2 2).toNat = 1 := by
        have r57015 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57016 := hb (x 2 2)
        have b57017 := hb (x 4 13)
        have b57018 := hb (x 3 1 && x 3 14)
        clear * - r57015 b57016 b57017 b57018 d57006 d56908
        omega
      have d57019 : (x 2 14).toNat = 1 := by
        have r57020 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b57021 := hb (x 2 2)
        have b57022 := hb (x 2 14)
        clear * - r57020 b57021 b57022 d57014
        omega
      have d57023 : (x 1 1).toNat = 0 := by
        have r57024 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57025 := hb (x 1 1)
        have b57026 := hb (x 2 14)
        clear * - r57024 b57025 b57026 d57019
        omega
      have d57027 : (x 1 9).toNat = 0 := by
        have r57028 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
        have b57029 := hb (x 1 1)
        have b57030 := hb (x 1 9)
        clear * - r57028 b57029 b57030 d57023
        omega
      have d57031 : (x (-2) 3).toNat = 0 := by
        have r57032 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57033 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e57034 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b57035 := hb (x (-2) 3)
        have b57036 := hb (x (-1) 2)
        have b57037 := hb (x 0 13)
        have b57038 := hb (x 1 12)
        clear * - r57032 e57033 e57034 b57035 b57036 b57037 b57038 d56966 d56974 d56961
        omega
      have d57039 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
        have r57040 := hand1 (x (-2) 3) (x (-2) 12)
        have b57041 := hb (x (-2) 3)
        have b57042 := hb (x (-2) 3 && x (-2) 12)
        clear * - r57040 b57041 b57042 d57031
        omega
      have d57043 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
        have r57044 := hand1 (x (-2) 3) (x (-2) 8)
        have b57045 := hb (x (-2) 3)
        have b57046 := hb (x (-2) 3 && x (-2) 8)
        clear * - r57044 b57045 b57046 d57031
        omega
      have d57047 : (x (-1) 3).toNat = 0 := by
        have r57048 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57049 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e57050 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b57051 := hb (x (-1) 3)
        have b57052 := hb (x 0 2)
        have b57053 := hb (x 1 13)
        have b57054 := hb (x 2 12)
        clear * - r57048 e57049 e57050 b57051 b57052 b57053 b57054 d56945 d56949 d54438
        omega
      have d57055 : (x (-1) 11).toNat = 0 := by
        have r57056 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
        have b57057 := hb (x (-1) 3)
        have b57058 := hb (x (-1) 11)
        clear * - r57056 b57057 b57058 d57047
        omega
      have d57059 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
        have r57060 := hand2 (x (-1) 1) (x (-1) 11)
        have b57061 := hb (x (-1) 11)
        have b57062 := hb (x (-1) 1 && x (-1) 11)
        clear * - r57060 b57061 b57062 d57055
        omega
      have d57063 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
        have r57064 := hand2 (x (-1) 2) (x (-1) 11)
        have b57065 := hb (x (-1) 11)
        have b57066 := hb (x (-1) 2 && x (-1) 11)
        clear * - r57064 b57065 b57066 d57055
        omega
      have d57067 : (x 6 8).toNat = 0 := by
        have r57068 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57069 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e57070 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e57071 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e57072 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e57073 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e57074 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b57075 := hb (x (-1) 7)
        have b57076 := hb (x 0 6)
        have b57077 := hb (x 1 5)
        have b57078 := hb (x 2 4)
        have b57079 := hb (x 3 11)
        have b57080 := hb (x 4 10)
        have b57081 := hb (x 5 9)
        have b57082 := hb (x 6 8)
        clear * - r57068 e57069 e57070 e57071 e57072 e57073 e57074 b57075 b57076 b57077 b57078 b57079 b57080 b57081 b57082 d56941 d56957 g6
        omega
      have d57083 : (x 5 9).toNat = 0 := by
        have r57084 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57085 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e57086 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e57087 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e57088 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e57089 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e57090 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b57091 := hb (x (-1) 7)
        have b57092 := hb (x 0 6)
        have b57093 := hb (x 1 5)
        have b57094 := hb (x 2 4)
        have b57095 := hb (x 3 11)
        have b57096 := hb (x 4 10)
        have b57097 := hb (x 5 9)
        have b57098 := hb (x 6 8)
        clear * - r57084 e57085 e57086 e57087 e57088 e57089 e57090 b57091 b57092 b57093 b57094 b57095 b57096 b57097 b57098 d57067 d56941 d56957 g6
        omega
      have d57099 : (x 4 10).toNat = 0 := by
        have r57100 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57101 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e57102 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e57103 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e57104 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e57105 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e57106 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b57107 := hb (x (-1) 7)
        have b57108 := hb (x 0 6)
        have b57109 := hb (x 1 5)
        have b57110 := hb (x 2 4)
        have b57111 := hb (x 3 11)
        have b57112 := hb (x 4 10)
        have b57113 := hb (x 5 9)
        have b57114 := hb (x 6 8)
        clear * - r57100 e57101 e57102 e57103 e57104 e57105 e57106 b57107 b57108 b57109 b57110 b57111 b57112 b57113 b57114 d57067 d57083 d56941 d56957 g6
        omega
      have d57115 : (x 3 11).toNat = 0 := by
        have r57116 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57117 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e57118 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e57119 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e57120 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e57121 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e57122 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b57123 := hb (x (-1) 7)
        have b57124 := hb (x 0 6)
        have b57125 := hb (x 1 5)
        have b57126 := hb (x 2 4)
        have b57127 := hb (x 3 11)
        have b57128 := hb (x 4 10)
        have b57129 := hb (x 5 9)
        have b57130 := hb (x 6 8)
        clear * - r57116 e57117 e57118 e57119 e57120 e57121 e57122 b57123 b57124 b57125 b57126 b57127 b57128 b57129 b57130 d57067 d57083 d57099 d56941 d56957 g6
        omega
      have d57131 : (x (-1) 7).toNat = 0 := by
        have r57132 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57133 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e57134 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e57135 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e57136 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e57137 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e57138 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b57139 := hb (x (-1) 7)
        have b57140 := hb (x 0 6)
        have b57141 := hb (x 1 5)
        have b57142 := hb (x 2 4)
        have b57143 := hb (x 3 11)
        have b57144 := hb (x 4 10)
        have b57145 := hb (x 5 9)
        have b57146 := hb (x 6 8)
        clear * - r57132 e57133 e57134 e57135 e57136 e57137 e57138 b57139 b57140 b57141 b57142 b57143 b57144 b57145 b57146 d57067 d57083 d57099 d57115 d56941 d56957 g6
        omega
      have d57147 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
        have r57148 := hand2 (x (-1) 2) (x (-1) 7)
        have b57149 := hb (x (-1) 7)
        have b57150 := hb (x (-1) 2 && x (-1) 7)
        clear * - r57148 b57149 b57150 d57131
        omega
      have r57151 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57152 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e57153 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e57154 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e57155 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e57156 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e57157 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e57158 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have r57159 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e57160 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e57161 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have r57162 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57163 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57164 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57165 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57166 := hand2 (x (-3) 4) (x (-3) 9)
      have r57167 := hand2 (x (-4) 5) (x (-4) 10)
      have r57168 := hand2 (x (-5) 6) (x (-5) 11)
      have r57169 := hand1 (x (-6) 7) (x (-6) 12)
      have r57170 := hand1 (x (-7) 8) (x (-7) 13)
      have r57171 := hand1 (x (-8) 9) (x (-8) 14)
      have r57172 := hand1 (x (-3) 4) (x (-3) 13)
      have r57173 := hand1 (x (-4) 5) (x (-4) 14)
      have r57174 := hand1 (x (-4) 2) (x (-4) 12)
      have r57175 := hand1 (x (-5) 3) (x (-5) 13)
      have r57176 := hand1 (x (-6) 4) (x (-6) 14)
      have r57177 := hand2 (x (-2) 2) (x (-2) 12)
      have r57178 := hand2 (x (-3) 3) (x (-3) 13)
      linarith only [r57151, r57152, e57153, e57154, e57155, e57156, e57157, e57158, r57159, e57160, e57161, r57162, r57163, r57164, r57165, r57166, r57167, r57168, r57169, r57170, r57171, r57172, r57173, r57174, r57175, r57176, r57177, r57178, g1, d57031, g4, d56961, f56874, d54454, d56957, d57027, d54416, d57147, d57043, d54458, d57063, d57039, g52, d57059, g53]
  · have f57232 : (x 0 14).toNat = 1 := by rw [h54424]; rfl
    have d57233 : (x (-1) 1).toNat = 0 := by
      have r57234 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b57235 := hb (x (-1) 1)
      have b57236 := hb (x 0 14)
      clear * - r57234 b57235 b57236 f57232
      omega
    have d57237 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r57238 := hand1 (x (-1) 1) (x (-1) 14)
      have b57239 := hb (x (-1) 1)
      have b57240 := hb (x (-1) 1 && x (-1) 14)
      clear * - r57238 b57239 b57240 d57233
      omega
    have d57241 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r57242 := hand1 (x (-1) 1) (x (-1) 12)
      have b57243 := hb (x (-1) 1)
      have b57244 := hb (x (-1) 1 && x (-1) 12)
      clear * - r57242 b57243 b57244 d57233
      omega
    have d57245 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
      have r57246 := hand1 (x (-1) 1) (x (-1) 11)
      have b57247 := hb (x (-1) 1)
      have b57248 := hb (x (-1) 1 && x (-1) 11)
      clear * - r57246 b57247 b57248 d57233
      omega
    have d57249 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
      have r57250 := hand1 (x (-1) 1) (x (-1) 10)
      have b57251 := hb (x (-1) 1)
      have b57252 := hb (x (-1) 1 && x (-1) 10)
      clear * - r57250 b57251 b57252 d57233
      omega
    have d57253 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
      have r57254 := hand1 (x (-1) 1) (x (-1) 7)
      have b57255 := hb (x (-1) 1)
      have b57256 := hb (x (-1) 1 && x (-1) 7)
      clear * - r57254 b57255 b57256 d57233
      omega
    have d57257 : (x (-1) 13).toNat = 0 := by
      have r57258 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b57259 := hb (x (-1) 1)
      have b57260 := hb (x (-1) 13)
      clear * - r57258 b57259 b57260 d57233
      omega
    have d57261 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
      have r57262 := hand2 (x (-1) 4) (x (-1) 13)
      have b57263 := hb (x (-1) 13)
      have b57264 := hb (x (-1) 4 && x (-1) 13)
      clear * - r57262 b57263 b57264 d57257
      omega
    have d57265 : (x (-1) 5).toNat = 0 := by
      have r57266 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
      have b57267 := hb (x (-1) 5)
      have b57268 := hb (x (-1) 13)
      clear * - r57266 b57267 b57268 d57257
      omega
    cases h57269 : x 0 1
    · have f57270 : (x 0 1).toNat = 0 := by rw [h57269]; rfl
      have d57271 : (x 0 1 && x 0 14).toNat = 0 := by
        have r57272 := hand1 (x 0 1) (x 0 14)
        have b57273 := hb (x 0 1)
        have b57274 := hb (x 0 1 && x 0 14)
        clear * - r57272 b57273 b57274 f57270
        omega
      have d57275 : (x 0 13).toNat = 0 := by
        have r57276 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
        have b57277 := hb (x 0 1)
        have b57278 := hb (x 0 13)
        clear * - r57276 b57277 b57278 f57270
        omega
      have d57279 : (x 0 5).toNat = 0 := by
        have r57280 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
        have b57281 := hb (x 0 5)
        have b57282 := hb (x 0 13)
        clear * - r57280 b57281 b57282 d57275
        omega
      have d57283 : (x 0 5 && x 0 14).toNat = 0 := by
        have r57284 := hand1 (x 0 5) (x 0 14)
        have b57285 := hb (x 0 5)
        have b57286 := hb (x 0 5 && x 0 14)
        clear * - r57284 b57285 b57286 d57279
        omega
      have d57287 : (x (-2) 2).toNat = 1 := by
        have r57288 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57289 := hb (x (-2) 2)
        have b57290 := hb (x 0 13)
        have b57291 := hb (x (-1) 1 && x (-1) 14)
        clear * - r57288 b57289 b57290 b57291 d57275 d57237
        omega
      have d57292 : (x (-2) 14).toNat = 1 := by
        have r57293 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
        have b57294 := hb (x (-2) 2)
        have b57295 := hb (x (-2) 14)
        clear * - r57293 b57294 b57295 d57287
        omega
      have d57296 : (x (-3) 1).toNat = 0 := by
        have r57297 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57298 := hb (x (-3) 1)
        have b57299 := hb (x (-2) 14)
        clear * - r57297 b57298 b57299 d57292
        omega
      have d57300 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
        have r57301 := hand1 (x (-3) 1) (x (-3) 14)
        have b57302 := hb (x (-3) 1)
        have b57303 := hb (x (-3) 1 && x (-3) 14)
        clear * - r57301 b57302 b57303 d57296
        omega
      have d57304 : (x (-3) 13).toNat = 0 := by
        have r57305 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
        have b57306 := hb (x (-3) 1)
        have b57307 := hb (x (-3) 13)
        clear * - r57305 b57306 b57307 d57296
        omega
      have d57308 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
        have r57309 := hand2 (x (-3) 3) (x (-3) 13)
        have b57310 := hb (x (-3) 13)
        have b57311 := hb (x (-3) 3 && x (-3) 13)
        clear * - r57309 b57310 b57311 d57304
        omega
      have d57312 : (x 0 12).toNat = 0 := by
        have r57313 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57314 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e57315 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b57316 := hb (x (-3) 3)
        have b57317 := hb (x (-2) 2)
        have b57318 := hb (x (-1) 13)
        have b57319 := hb (x 0 12)
        clear * - r57313 e57314 e57315 b57316 b57317 b57318 b57319 d57257 d57287
        omega
      have d57320 : (x (-3) 3).toNat = 0 := by
        have r57321 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57322 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e57323 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b57324 := hb (x (-3) 3)
        have b57325 := hb (x (-2) 2)
        have b57326 := hb (x (-1) 13)
        have b57327 := hb (x 0 12)
        clear * - r57321 e57322 e57323 b57324 b57325 b57326 b57327 d57312 d57257 d57287
        omega
      have d57328 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
        have r57329 := hand1 (x (-3) 3) (x (-3) 12)
        have b57330 := hb (x (-3) 3)
        have b57331 := hb (x (-3) 3 && x (-3) 12)
        clear * - r57329 b57330 b57331 d57320
        omega
      have d57332 : (x (-2) 2 && x (-2) 11).toNat = 1 := by
        have r57333 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57334 := hb (x (-6) 6)
        have b57335 := hb (x 0 9)
        have b57336 := hb (x (-1) 1 && x (-1) 10)
        have b57337 := hb (x (-2) 2 && x (-2) 11)
        have b57338 := hb (x (-3) 3 && x (-3) 12)
        have b57339 := hb (x (-4) 4 && x (-4) 13)
        have b57340 := hb (x (-5) 5 && x (-5) 14)
        clear * - r57333 b57334 b57335 b57336 b57337 b57338 b57339 b57340 g7 d57249 d57328 g46 g47 g0
        omega
      have d57341 : (x (-2) 11).toNat = 1 := by
        have r57342 := hand2 (x (-2) 2) (x (-2) 11)
        have b57343 := hb (x (-2) 11)
        have b57344 := hb (x (-2) 2 && x (-2) 11)
        clear * - r57342 b57343 b57344 d57332
        omega
      have d57345 : (x (-2) 3).toNat = 1 := by
        have r57346 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
        have b57347 := hb (x (-2) 3)
        have b57348 := hb (x (-2) 11)
        clear * - r57346 b57347 b57348 d57341
        omega
      have d57349 : (x 1 12).toNat = 0 := by
        have r57350 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57351 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e57352 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b57353 := hb (x (-2) 3)
        have b57354 := hb (x (-1) 2)
        have b57355 := hb (x 0 13)
        have b57356 := hb (x 1 12)
        clear * - r57350 e57351 e57352 b57353 b57354 b57355 b57356 d57275 d57345
        omega
      have d57357 : (x 1 4).toNat = 0 := by
        have r57358 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
        have b57359 := hb (x 1 4)
        have b57360 := hb (x 1 12)
        clear * - r57358 b57359 b57360 d57349
        omega
      have d57361 : (x 1 4 && x 1 14).toNat = 0 := by
        have r57362 := hand1 (x 1 4) (x 1 14)
        have b57363 := hb (x 1 4)
        have b57364 := hb (x 1 4 && x 1 14)
        clear * - r57362 b57363 b57364 d57357
        omega
      have d57365 : (x 1 4 && x 1 13).toNat = 0 := by
        have r57366 := hand1 (x 1 4) (x 1 13)
        have b57367 := hb (x 1 4)
        have b57368 := hb (x 1 4 && x 1 13)
        clear * - r57366 b57367 b57368 d57357
        omega
      have d57369 : (x (-1) 2).toNat = 0 := by
        have r57370 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57371 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e57372 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b57373 := hb (x (-2) 3)
        have b57374 := hb (x (-1) 2)
        have b57375 := hb (x 0 13)
        have b57376 := hb (x 1 12)
        clear * - r57370 e57371 e57372 b57373 b57374 b57375 b57376 d57349 d57275 d57345
        omega
      have d57377 : (x (-1) 10).toNat = 0 := by
        have r57378 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
        have b57379 := hb (x (-1) 2)
        have b57380 := hb (x (-1) 10)
        clear * - r57378 b57379 b57380 d57369
        omega
      have d57381 : (x 1 13).toNat = 1 := by
        have r57382 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57383 := hb (x (-1) 2)
        have b57384 := hb (x 1 13)
        have b57385 := hb (x 0 1 && x 0 14)
        clear * - r57382 b57383 b57384 b57385 d57271 d57369
        omega
      have d57386 : (x 2 12).toNat = 0 := by
        have r57387 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57388 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e57389 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b57390 := hb (x (-1) 3)
        have b57391 := hb (x 0 2)
        have b57392 := hb (x 1 13)
        have b57393 := hb (x 2 12)
        clear * - r57387 e57388 e57389 b57390 b57391 b57392 b57393 d57381
        omega
      have d57394 : (x 2 3 && x 2 12).toNat = 0 := by
        have r57395 := hand2 (x 2 3) (x 2 12)
        have b57396 := hb (x 2 12)
        have b57397 := hb (x 2 3 && x 2 12)
        clear * - r57395 b57396 b57397 d57386
        omega
      have d57398 : (x 2 7 && x 2 12).toNat = 0 := by
        have r57399 := hand2 (x 2 7) (x 2 12)
        have b57400 := hb (x 2 12)
        have b57401 := hb (x 2 7 && x 2 12)
        clear * - r57399 b57400 b57401 d57386
        omega
      have d57402 : (x 0 2).toNat = 0 := by
        have r57403 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57404 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e57405 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b57406 := hb (x (-1) 3)
        have b57407 := hb (x 0 2)
        have b57408 := hb (x 1 13)
        have b57409 := hb (x 2 12)
        clear * - r57403 e57404 e57405 b57406 b57407 b57408 b57409 d57386 d57381
        omega
      have d57410 : (x 0 10).toNat = 0 := by
        have r57411 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
        have b57412 := hb (x 0 2)
        have b57413 := hb (x 0 10)
        clear * - r57411 b57412 b57413 d57402
        omega
      have d57414 : (x (-2) 2 && x (-2) 12).toNat = 1 := by
        have r57415 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57416 := hb (x (-5) 5)
        have b57417 := hb (x 0 10)
        have b57418 := hb (x (-1) 1 && x (-1) 11)
        have b57419 := hb (x (-2) 2 && x (-2) 12)
        have b57420 := hb (x (-3) 3 && x (-3) 13)
        have b57421 := hb (x (-4) 4 && x (-4) 14)
        clear * - r57415 b57416 b57417 b57418 b57419 b57420 b57421 d57410 d57245 d57308 g53 g1
        omega
      have d57422 : (x (-2) 12).toNat = 1 := by
        have r57423 := hand2 (x (-2) 2) (x (-2) 12)
        have b57424 := hb (x (-2) 12)
        have b57425 := hb (x (-2) 2 && x (-2) 12)
        clear * - r57423 b57424 b57425 d57414
        omega
      have d57426 : (x (-4) 2).toNat = 0 := by
        have r57427 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57428 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e57429 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b57430 := hb (x (-5) 3)
        have b57431 := hb (x (-4) 2)
        have b57432 := hb (x (-3) 13)
        have b57433 := hb (x (-2) 12)
        clear * - r57427 e57428 e57429 b57430 b57431 b57432 b57433 d57422 d57304
        omega
      have d57434 : (x (-2) 13).toNat = 1 := by
        have r57435 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57436 := hb (x (-4) 2)
        have b57437 := hb (x (-2) 13)
        have b57438 := hb (x (-3) 1 && x (-3) 14)
        clear * - r57435 b57436 b57437 b57438 d57300 d57426
        omega
      have d57439 : (x (-2) 1).toNat = 1 := by
        have r57440 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b57441 := hb (x (-2) 1)
        have b57442 := hb (x (-2) 13)
        clear * - r57440 b57441 b57442 d57434
        omega
      have d57443 : (x (-1) 14).toNat = 0 := by
        have r57444 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57445 := hb (x (-2) 1)
        have b57446 := hb (x (-1) 14)
        clear * - r57444 b57445 b57446 d57439
        omega
      have d57447 : (x (-1) 6).toNat = 0 := by
        have r57448 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
        have b57449 := hb (x (-1) 6)
        have b57450 := hb (x (-1) 14)
        clear * - r57448 b57449 b57450 d57443
        omega
      have d57451 : (x 1 8).toNat = 0 := by
        have r57452 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57453 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e57454 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e57455 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e57456 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e57457 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e57458 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b57459 := hb (x (-6) 7)
        have b57460 := hb (x (-5) 6)
        have b57461 := hb (x (-4) 5)
        have b57462 := hb (x (-3) 4)
        have b57463 := hb (x (-2) 11)
        have b57464 := hb (x (-1) 10)
        have b57465 := hb (x 0 9)
        have b57466 := hb (x 1 8)
        clear * - r57452 e57453 e57454 e57455 e57456 e57457 e57458 b57459 b57460 b57461 b57462 b57463 b57464 b57465 b57466 g7 d57377 d57341
        omega
      have d57467 : (x 1 8 && x 1 13).toNat = 0 := by
        have r57468 := hand1 (x 1 8) (x 1 13)
        have b57469 := hb (x 1 8)
        have b57470 := hb (x 1 8 && x 1 13)
        clear * - r57468 b57469 b57470 d57451
        omega
      have r57471 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57472 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e57473 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e57474 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e57475 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e57476 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e57477 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e57478 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have r57479 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e57480 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e57481 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have r57482 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57483 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57484 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57485 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r57486 := hand2 (x 8 1) (x 8 6)
      have r57487 := hand2 (x 7 2) (x 7 7)
      have r57488 := hand2 (x 6 3) (x 6 8)
      have r57489 := hand1 (x 5 4) (x 5 9)
      have r57490 := hand1 (x 4 5) (x 4 10)
      have r57491 := hand1 (x 3 6) (x 3 11)
      have r57492 := hand2 (x 4 1) (x 4 10)
      have r57493 := hand2 (x 3 2) (x 3 11)
      have r57494 := hand1 (x 3 2) (x 3 12)
      have r57495 := hand1 (x 2 3) (x 2 13)
      have r57496 := hand2 (x 6 1) (x 6 11)
      have r57497 := hand2 (x 5 2) (x 5 12)
      have r57498 := hand2 (x 4 3) (x 4 13)
      linarith only [r57471, r57472, e57473, e57474, e57475, e57476, e57477, e57478, r57479, e57480, e57481, r57482, r57483, r57484, r57485, r57486, r57487, r57488, r57489, r57490, r57491, r57492, r57493, r57494, r57495, r57496, r57497, r57498, d57447, d57377, d57279, f57232, d57381, g9, d57386, g12, d57398, d57467, g29, d57394, d57365, d57283, g54, d57361, g55]
    · have f57552 : (x 0 1).toNat = 1 := by rw [h57269]; rfl
      have d57553 : (x 1 14).toNat = 0 := by
        have r57554 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b57555 := hb (x 0 1)
        have b57556 := hb (x 1 14)
        clear * - r57554 b57555 b57556 f57552
        omega
      have d57557 : (x 1 1 && x 1 14).toNat = 0 := by
        have r57558 := hand2 (x 1 1) (x 1 14)
        have b57559 := hb (x 1 14)
        have b57560 := hb (x 1 1 && x 1 14)
        clear * - r57558 b57559 b57560 d57553
        omega
      have d57561 : (x 1 3 && x 1 14).toNat = 0 := by
        have r57562 := hand2 (x 1 3) (x 1 14)
        have b57563 := hb (x 1 14)
        have b57564 := hb (x 1 3 && x 1 14)
        clear * - r57562 b57563 b57564 d57553
        omega
      have d57565 : (x 1 5 && x 1 14).toNat = 0 := by
        have r57566 := hand2 (x 1 5) (x 1 14)
        have b57567 := hb (x 1 14)
        have b57568 := hb (x 1 5 && x 1 14)
        clear * - r57566 b57567 b57568 d57553
        omega
      have d57569 : (x 1 2).toNat = 0 := by
        have r57570 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
        have b57571 := hb (x 1 2)
        have b57572 := hb (x 1 14)
        clear * - r57570 b57571 b57572 d57553
        omega
      have d57573 : (x 1 2 && x 1 11).toNat = 0 := by
        have r57574 := hand1 (x 1 2) (x 1 11)
        have b57575 := hb (x 1 2)
        have b57576 := hb (x 1 2 && x 1 11)
        clear * - r57574 b57575 b57576 d57569
        omega
      have d57577 : (x 1 2 && x 1 7).toNat = 0 := by
        have r57578 := hand1 (x 1 2) (x 1 7)
        have b57579 := hb (x 1 2)
        have b57580 := hb (x 1 2 && x 1 7)
        clear * - r57578 b57579 b57580 d57569
        omega
      have d57581 : (x 1 10).toNat = 0 := by
        have r57582 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
        have b57583 := hb (x 1 2)
        have b57584 := hb (x 1 10)
        clear * - r57582 b57583 b57584 d57569
        omega
      have d57585 : (x 1 1 && x 1 10).toNat = 0 := by
        have r57586 := hand2 (x 1 1) (x 1 10)
        have b57587 := hb (x 1 10)
        have b57588 := hb (x 1 1 && x 1 10)
        clear * - r57586 b57587 b57588 d57581
        omega
      cases h57589 : x 0 2
      · have f57590 : (x 0 2).toNat = 0 := by rw [h57589]; rfl
        have d57591 : (x 0 10).toNat = 0 := by
          have r57592 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
          have b57593 := hb (x 0 2)
          have b57594 := hb (x 0 10)
          clear * - r57592 b57593 b57594 f57590
          omega
        have d57595 : (x 2 13).toNat = 1 := by
          have r57596 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b57597 := hb (x 0 2)
          have b57598 := hb (x 2 13)
          have b57599 := hb (x 1 1 && x 1 14)
          clear * - r57596 b57597 b57598 b57599 d57557 f57590
          omega
        have d57600 : (x 2 1).toNat = 1 := by
          have r57601 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
          have b57602 := hb (x 2 1)
          have b57603 := hb (x 2 13)
          clear * - r57601 b57602 b57603 d57595
          omega
        have d57604 : (x 3 12).toNat = 0 := by
          have r57605 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57606 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e57607 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b57608 := hb (x 0 3)
          have b57609 := hb (x 1 2)
          have b57610 := hb (x 2 13)
          have b57611 := hb (x 3 12)
          clear * - r57605 e57606 e57607 b57608 b57609 b57610 b57611 d57595 d57569
          omega
        have d57612 : (x 3 1 && x 3 12).toNat = 0 := by
          have r57613 := hand2 (x 3 1) (x 3 12)
          have b57614 := hb (x 3 12)
          have b57615 := hb (x 3 1 && x 3 12)
          clear * - r57613 b57614 b57615 d57604
          omega
        have d57616 : (x 0 3).toNat = 0 := by
          have r57617 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57618 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e57619 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b57620 := hb (x 0 3)
          have b57621 := hb (x 1 2)
          have b57622 := hb (x 2 13)
          have b57623 := hb (x 3 12)
          clear * - r57617 e57618 e57619 b57620 b57621 b57622 b57623 d57604 d57595 d57569
          omega
        have d57624 : (x 0 3 && x 0 12).toNat = 0 := by
          have r57625 := hand1 (x 0 3) (x 0 12)
          have b57626 := hb (x 0 3)
          have b57627 := hb (x 0 3 && x 0 12)
          clear * - r57625 b57626 b57627 d57616
          omega
        have d57628 : (x 0 3 && x 0 8).toNat = 0 := by
          have r57629 := hand1 (x 0 3) (x 0 8)
          have b57630 := hb (x 0 3)
          have b57631 := hb (x 0 3 && x 0 8)
          clear * - r57629 b57630 b57631 d57616
          omega
        have d57632 : (x 0 11).toNat = 0 := by
          have r57633 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
          have b57634 := hb (x 0 3)
          have b57635 := hb (x 0 11)
          clear * - r57633 b57634 b57635 d57616
          omega
        have r57636 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57637 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57638 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e57639 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e57640 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e57641 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e57642 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e57643 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have r57644 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57645 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e57646 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e57647 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e57648 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e57649 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e57650 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have r57651 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57652 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
        have e57653 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
        have e57654 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
        have e57655 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
        have e57656 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
        have e57657 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
        have r57658 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57659 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e57660 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e57661 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e57662 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e57663 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e57664 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have r57665 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57666 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e57667 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have r57668 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57669 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e57670 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have r57671 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57672 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e57673 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have r57674 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57675 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e57676 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have r57677 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57678 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e57679 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have r57680 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e57681 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
        have e57682 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
        have r57683 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57684 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57685 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57686 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57687 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57688 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57689 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57690 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57691 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57692 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r57693 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
        have r57694 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
        have r57695 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
        have r57696 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
        have r57697 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
        have r57698 := hand2 (x (-2) 2) (x (-2) 6)
        have r57699 := hand2 (x (-3) 3) (x (-3) 7)
        have r57700 := hand2 (x (-8) 8) (x (-8) 12)
        have r57701 := hand2 (x (-9) 9) (x (-9) 13)
        have r57702 := hand2 (x 2 1) (x 2 6)
        have r57703 := hand1 (x (-4) 7) (x (-4) 12)
        have r57704 := hand1 (x (-5) 8) (x (-5) 13)
        have r57705 := hand1 (x (-6) 9) (x (-6) 14)
        have r57706 := hand2 (x (-2) 2) (x (-2) 8)
        have r57707 := hand2 (x (-3) 3) (x (-3) 9)
        have r57708 := hand1 (x (-8) 8) (x (-8) 14)
        have r57709 := hand2 (x 2 1) (x 2 10)
        have r57710 := hand1 (x (-2) 5) (x (-2) 14)
        have r57711 := hand2 (x 6 1) (x 6 10)
        have r57712 := hand2 (x 5 2) (x 5 11)
        have r57713 := hand2 (x 4 3) (x 4 12)
        have r57714 := hand2 (x (-9) 1) (x (-9) 11)
        have r57715 := hand1 (x (-10) 2) (x (-10) 12)
        have r57716 := hand1 (x (-11) 3) (x (-11) 13)
        have r57717 := hand1 (x (-12) 4) (x (-12) 14)
        have r57718 := hand1 (x (-4) 2) (x (-4) 12)
        have r57719 := hand1 (x (-5) 3) (x (-5) 13)
        have r57720 := hand1 (x (-6) 4) (x (-6) 14)
        have r57721 := hand2 (x (-2) 2) (x (-2) 12)
        have r57722 := hand2 (x (-3) 3) (x (-3) 13)
        have r57723 := hand2 (x (-9) 1) (x (-9) 12)
        have r57724 := hand2 (x (-10) 2) (x (-10) 13)
        have r57725 := hand2 (x (-11) 3) (x (-11) 14)
        have r57726 := hand1 (x (-2) 2) (x (-2) 13)
        have r57727 := hand1 (x (-3) 3) (x (-3) 14)
        have r57728 := hand1 (x 2 2) (x 2 13)
        linarith only [r57636, r57637, e57638, e57639, e57640, e57641, e57642, e57643, r57644, e57645, e57646, e57647, e57648, e57649, e57650, r57651, e57652, e57653, e57654, e57655, e57656, e57657, r57658, e57659, e57660, e57661, e57662, e57663, e57664, r57665, e57666, e57667, r57668, e57669, e57670, r57671, e57672, e57673, r57674, e57675, e57676, r57677, e57678, e57679, r57680, e57681, e57682, r57683, r57684, r57685, r57686, r57687, r57688, r57689, r57690, r57691, r57692, r57693, r57694, r57695, r57696, r57697, r57698, r57699, r57700, r57701, r57702, r57703, r57704, r57705, r57706, r57707, r57708, r57709, r57710, r57711, r57712, r57713, r57714, r57715, r57716, r57717, r57718, r57719, r57720, r57721, r57722, r57723, r57724, r57725, r57726, r57727, r57728, g1, g2, g4, d57265, d57257, d57616, g6, d57591, d57632, d57569, g8, d57600, g11, g19, g20, g21, g22, d57577, d57628, g26, g27, g28, d57253, g34, g35, g36, g37, d57573, d57624, d57261, g50, g51, g52, d57245, g53, d57241, d57612, d57561]
      · have f57861 : (x 0 2).toNat = 1 := by rw [h57589]; rfl
        have d57862 : (x 2 12).toNat = 0 := by
          have r57863 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57864 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e57865 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b57866 := hb (x (-1) 3)
          have b57867 := hb (x 0 2)
          have b57868 := hb (x 1 13)
          have b57869 := hb (x 2 12)
          clear * - r57863 e57864 e57865 b57866 b57867 b57868 b57869 f57861
          omega
        have d57870 : (x 2 4).toNat = 0 := by
          have r57871 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
          have b57872 := hb (x 2 4)
          have b57873 := hb (x 2 12)
          clear * - r57871 b57872 b57873 d57862
          omega
        have d57874 : (x 2 4 && x 2 13).toNat = 0 := by
          have r57875 := hand1 (x 2 4) (x 2 13)
          have b57876 := hb (x 2 4)
          have b57877 := hb (x 2 4 && x 2 13)
          clear * - r57875 b57876 b57877 d57870
          omega
        have d57878 : (x 2 4 && x 2 8).toNat = 0 := by
          have r57879 := hand1 (x 2 4) (x 2 8)
          have b57880 := hb (x 2 4)
          have b57881 := hb (x 2 4 && x 2 8)
          clear * - r57879 b57880 b57881 d57870
          omega
        have d57882 : (x 1 13).toNat = 0 := by
          have r57883 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57884 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e57885 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b57886 := hb (x (-1) 3)
          have b57887 := hb (x 0 2)
          have b57888 := hb (x 1 13)
          have b57889 := hb (x 2 12)
          clear * - r57883 e57884 e57885 b57886 b57887 b57888 b57889 d57862 f57861
          omega
        have d57890 : (x 1 5).toNat = 0 := by
          have r57891 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
          have b57892 := hb (x 1 5)
          have b57893 := hb (x 1 13)
          clear * - r57891 b57892 b57893 d57882
          omega
        have d57894 : (x 1 5 && x 1 9).toNat = 0 := by
          have r57895 := hand1 (x 1 5) (x 1 9)
          have b57896 := hb (x 1 5)
          have b57897 := hb (x 1 5 && x 1 9)
          clear * - r57895 b57896 b57897 d57890
          omega
        have d57898 : (x (-1) 3).toNat = 0 := by
          have r57899 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57900 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e57901 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b57902 := hb (x (-1) 3)
          have b57903 := hb (x 0 2)
          have b57904 := hb (x 1 13)
          have b57905 := hb (x 2 12)
          clear * - r57899 e57900 e57901 b57902 b57903 b57904 b57905 d57862 d57882 f57861
          omega
        have d57906 : (x (-1) 3 && x (-1) 12).toNat = 0 := by
          have r57907 := hand1 (x (-1) 3) (x (-1) 12)
          have b57908 := hb (x (-1) 3)
          have b57909 := hb (x (-1) 3 && x (-1) 12)
          clear * - r57907 b57908 b57909 d57898
          omega
        have d57910 : (x (-1) 11).toNat = 0 := by
          have r57911 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
          have b57912 := hb (x (-1) 3)
          have b57913 := hb (x (-1) 11)
          clear * - r57911 b57912 b57913 d57898
          omega
        have d57914 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
          have r57915 := hand2 (x (-1) 7) (x (-1) 11)
          have b57916 := hb (x (-1) 11)
          have b57917 := hb (x (-1) 7 && x (-1) 11)
          clear * - r57915 b57916 b57917 d57910
          omega
        have d57918 : (x 3 3 && x 3 12).toNat = 1 := by
          have r57919 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b57920 := hb (x 0 6)
          have b57921 := hb (x 6 9)
          have b57922 := hb (x 5 1 && x 5 10)
          have b57923 := hb (x 4 2 && x 4 11)
          have b57924 := hb (x 3 3 && x 3 12)
          have b57925 := hb (x 2 4 && x 2 13)
          have b57926 := hb (x 1 5 && x 1 14)
          clear * - r57919 b57920 b57921 b57922 b57923 b57924 b57925 b57926 g13 g48 g49 d57874 d57565 g6
          omega
        have d57927 : (x 3 12).toNat = 1 := by
          have r57928 := hand2 (x 3 3) (x 3 12)
          have b57929 := hb (x 3 12)
          have b57930 := hb (x 3 3 && x 3 12)
          clear * - r57928 b57929 b57930 d57918
          omega
        have d57931 : (x 2 13).toNat = 0 := by
          have r57932 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57933 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e57934 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b57935 := hb (x 0 3)
          have b57936 := hb (x 1 2)
          have b57937 := hb (x 2 13)
          have b57938 := hb (x 3 12)
          clear * - r57932 e57933 e57934 b57935 b57936 b57937 b57938 d57927 d57569
          omega
        have d57939 : (x 2 2 && x 2 13).toNat = 0 := by
          have r57940 := hand2 (x 2 2) (x 2 13)
          have b57941 := hb (x 2 13)
          have b57942 := hb (x 2 2 && x 2 13)
          clear * - r57940 b57941 b57942 d57931
          omega
        have d57943 : (x 0 3).toNat = 0 := by
          have r57944 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57945 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
          have e57946 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
          have b57947 := hb (x 0 3)
          have b57948 := hb (x 1 2)
          have b57949 := hb (x 2 13)
          have b57950 := hb (x 3 12)
          clear * - r57944 e57945 e57946 b57947 b57948 b57949 b57950 d57927 d57931 d57569
          omega
        have d57951 : (x 0 11).toNat = 0 := by
          have r57952 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
          have b57953 := hb (x 0 3)
          have b57954 := hb (x 0 11)
          clear * - r57952 b57953 b57954 d57943
          omega
        have d57955 : (x 0 2 && x 0 11).toNat = 0 := by
          have r57956 := hand2 (x 0 2) (x 0 11)
          have b57957 := hb (x 0 11)
          have b57958 := hb (x 0 2 && x 0 11)
          clear * - r57956 b57957 b57958 d57951
          omega
        have d57959 : (x 3 3).toNat = 1 := by
          have r57960 := hand1 (x 3 3) (x 3 12)
          have b57961 := hb (x 3 3)
          have b57962 := hb (x 3 3 && x 3 12)
          clear * - r57960 b57961 b57962 d57918
          omega
        have d57963 : (x 6 12).toNat = 0 := by
          have r57964 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57965 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e57966 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b57967 := hb (x 3 3)
          have b57968 := hb (x 4 2)
          have b57969 := hb (x 5 13)
          have b57970 := hb (x 6 12)
          clear * - r57964 e57965 e57966 b57967 b57968 b57969 b57970 d57959
          omega
        have d57971 : (x 6 1 && x 6 12).toNat = 0 := by
          have r57972 := hand2 (x 6 1) (x 6 12)
          have b57973 := hb (x 6 12)
          have b57974 := hb (x 6 1 && x 6 12)
          clear * - r57972 b57973 b57974 d57963
          omega
        have d57975 : (x 6 4).toNat = 0 := by
          have r57976 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b57977 := hb (x 6 4)
          have b57978 := hb (x 6 12)
          clear * - r57976 b57977 b57978 d57963
          omega
        have d57979 : (x 5 13).toNat = 0 := by
          have r57980 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57981 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e57982 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b57983 := hb (x 3 3)
          have b57984 := hb (x 4 2)
          have b57985 := hb (x 5 13)
          have b57986 := hb (x 6 12)
          clear * - r57980 e57981 e57982 b57983 b57984 b57985 b57986 d57963 d57959
          omega
        have d57987 : (x 5 2 && x 5 13).toNat = 0 := by
          have r57988 := hand2 (x 5 2) (x 5 13)
          have b57989 := hb (x 5 13)
          have b57990 := hb (x 5 2 && x 5 13)
          clear * - r57988 b57989 b57990 d57979
          omega
        have d57991 : (x 5 5).toNat = 0 := by
          have r57992 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
          have b57993 := hb (x 5 5)
          have b57994 := hb (x 5 13)
          clear * - r57992 b57993 b57994 d57979
          omega
        have d57995 : (x 4 2).toNat = 0 := by
          have r57996 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e57997 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e57998 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b57999 := hb (x 3 3)
          have b58000 := hb (x 4 2)
          have b58001 := hb (x 5 13)
          have b58002 := hb (x 6 12)
          clear * - r57996 e57997 e57998 b57999 b58000 b58001 b58002 d57963 d57979 d57959
          omega
        have d58003 : (x 4 2 && x 4 6).toNat = 0 := by
          have r58004 := hand1 (x 4 2) (x 4 6)
          have b58005 := hb (x 4 2)
          have b58006 := hb (x 4 2 && x 4 6)
          clear * - r58004 b58005 b58006 d57995
          omega
        have r58007 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e58008 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e58009 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e58010 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e58011 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e58012 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e58013 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have r58014 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e58015 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e58016 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e58017 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e58018 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e58019 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e58020 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have r58021 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e58022 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e58023 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e58024 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e58025 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e58026 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e58027 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have r58028 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e58029 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e58030 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have r58031 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e58032 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e58033 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have r58034 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58035 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58036 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e58037 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
        have e58038 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
        have r58039 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58040 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58041 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58042 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58043 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58044 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58045 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r58046 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
        have r58047 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
        have r58048 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have r58049 := hand2 (x 3 3) (x 3 7)
        have r58050 := hand1 (x (-2) 8) (x (-2) 12)
        have r58051 := hand1 (x (-3) 9) (x (-3) 13)
        have r58052 := hand1 (x (-2) 2) (x (-2) 11)
        have r58053 := hand1 (x (-3) 3) (x (-3) 12)
        have r58054 := hand1 (x (-2) 4) (x (-2) 13)
        have r58055 := hand1 (x (-3) 5) (x (-3) 14)
        have r58056 := hand1 (x (-4) 2) (x (-4) 12)
        have r58057 := hand1 (x (-5) 3) (x (-5) 13)
        have r58058 := hand1 (x (-6) 4) (x (-6) 14)
        have r58059 := hand2 (x (-2) 2) (x (-2) 12)
        have r58060 := hand2 (x (-3) 3) (x (-3) 13)
        have r58061 := hand1 (x 3 1) (x 3 12)
        have r58062 := hand2 (x 4 3) (x 4 14)
        have r58063 := hand2 (x 4 1) (x 4 14)
        linarith only [r58007, e58008, e58009, e58010, e58011, e58012, e58013, r58014, e58015, e58016, e58017, e58018, e58019, e58020, r58021, e58022, e58023, e58024, e58025, e58026, e58027, r58028, e58029, e58030, r58031, e58032, e58033, r58034, r58035, r58036, e58037, e58038, r58039, r58040, r58041, r58042, r58043, r58044, r58045, r58046, r58047, r58048, r58049, r58050, r58051, r58052, r58053, r58054, r58055, r58056, r58057, r58058, r58059, r58060, r58061, r58062, r58063, g0, g1, g4, d57910, d57257, g7, g10, g11, d57991, d57979, d57975, d58003, d57878, d57894, d54420, d57914, d57249, g46, g47, d57585, d57955, d57906, g52, d57245, g53, d57939, d57561, d57971, d57987]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a10 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 6).toNat = 0)
    (g1 : (x (-5) 5).toNat = 0)
    (g2 : (x (-4) 4).toNat = 0)
    (g3 : (x (-3) 11).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x 0 6).toNat = 0)
    (g7 : (x 0 9).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 2 5).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 4 11).toNat = 0)
    (g12 : (x 5 10).toNat = 0)
    (g13 : (x 6 9).toNat = 0)
    (g14 : (x 7 8).toNat = 0)
    (g15 : (x 7 7 && x 7 8).toNat = 0)
    (g16 : (x 6 8 && x 6 9).toNat = 0)
    (g17 : (x 5 9 && x 5 10).toNat = 0)
    (g18 : (x 4 10 && x 4 11).toNat = 0)
    (g19 : (x (-4) 4 && x (-4) 8).toNat = 0)
    (g20 : (x (-5) 5 && x (-5) 9).toNat = 0)
    (g21 : (x (-6) 6 && x (-6) 10).toNat = 0)
    (g22 : (x (-7) 7 && x (-7) 11).toNat = 0)
    (g23 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g24 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g25 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g26 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g27 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g29 : (x 0 9 && x 0 14).toNat = 0)
    (g30 : (x 7 3 && x 7 8).toNat = 0)
    (g31 : (x 6 4 && x 6 9).toNat = 0)
    (g32 : (x 5 5 && x 5 10).toNat = 0)
    (g33 : (x 4 6 && x 4 11).toNat = 0)
    (g34 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g35 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g36 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g37 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g38 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g39 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g40 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g41 : (x 3 4 && x 3 11).toNat = 0)
    (g42 : (x 2 5 && x 2 12).toNat = 0)
    (g43 : (x 1 6 && x 1 13).toNat = 0)
    (g44 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g45 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g46 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g47 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g48 : (x 5 1 && x 5 10).toNat = 0)
    (g49 : (x 4 2 && x 4 11).toNat = 0)
    (g50 : (x 3 4 && x 3 13).toNat = 0)
    (g51 : (x 2 5 && x 2 14).toNat = 0)
    (g52 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g53 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g54 : (x 4 1 && x 4 11).toNat = 0)
    (g55 : (x 3 4 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a10_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55
