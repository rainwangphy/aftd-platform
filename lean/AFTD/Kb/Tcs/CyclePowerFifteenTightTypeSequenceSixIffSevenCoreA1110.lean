import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a1110

Topic: combinatorics   Node: 52cdd7937395

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 28 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a10, cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a110.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a10 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-1) 7).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 6).toNat = 1)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 1 2).toNat = 0)
    (g7 : (x 1 5).toNat = 0)
    (g8 : (x 1 10).toNat = 0)
    (g9 : (x 2 4).toNat = 0)
    (g10 : (x 2 5).toNat = 0)
    (g11 : (x 2 13).toNat = 0)
    (g12 : (x 4 10).toNat = 0)
    (g13 : (x 5 9).toNat = 0)
    (g14 : (x (-1) 5 && x (-1) 10).toNat = 0)
    (g15 : (x 6 3 && x 6 8).toNat = 0)
    (g16 : (x 5 4 && x 5 9).toNat = 0)
    (g17 : (x 4 5 && x 4 10).toNat = 0)
    (g18 : (x 3 6 && x 3 11).toNat = 0)
    (g19 : (x 6 2 && x 6 8).toNat = 0)
    (g20 : (x 5 3 && x 5 9).toNat = 0)
    (g21 : (x 4 4 && x 4 10).toNat = 0)
    (g22 : (x 3 5 && x 3 11).toNat = 0)
    (g23 : (x 1 3 && x 1 10).toNat = 0)
    (g24 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g25 : (x 6 1 && x 6 8).toNat = 0)
    (g26 : (x 5 2 && x 5 9).toNat = 0)
    (g27 : (x 4 3 && x 4 10).toNat = 0)
    (g28 : (x 3 4 && x 3 11).toNat = 0)
    (g29 : (x 2 5 && x 2 12).toNat = 0)
    (g30 : (x 0 7 && x 0 14).toNat = 0)
    (g31 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g32 : (x 4 1 && x 4 10).toNat = 0)
    (g33 : (x 3 2 && x 3 11).toNat = 0)
    (g34 : (x 3 4 && x 3 13).toNat = 0)
    (g35 : (x 2 5 && x 2 14).toNat = 0)
    (g36 : (x 3 1 && x 3 11).toNat = 0)
    (g37 : (x 2 4 && x 2 14).toNat = 0)
    (g38 : (x 3 4 && x 3 14).toNat = 0)
    (g39 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g40 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d34818 : (x 0 1 && x 0 11).toNat = 0 := by
    have r34819 := hand2 (x 0 1) (x 0 11)
    have b34820 := hb (x 0 11)
    have b34821 := hb (x 0 1 && x 0 11)
    clear * - r34819 b34820 b34821 g5
    omega
  have d34822 : (x 0 4 && x 0 11).toNat = 0 := by
    have r34823 := hand2 (x 0 4) (x 0 11)
    have b34824 := hb (x 0 11)
    have b34825 := hb (x 0 4 && x 0 11)
    clear * - r34823 b34824 b34825 g5
    omega
  cases h34826 : x 0 1
  · have f34827 : (x 0 1).toNat = 0 := by rw [h34826]; rfl
    have d34828 : (x 0 13).toNat = 0 := by
      have r34829 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
      have b34830 := hb (x 0 1)
      have b34831 := hb (x 0 13)
      clear * - r34829 b34830 b34831 f34827
      omega
    have d34832 : (x (-2) 2).toNat = 1 := by
      have r34833 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34834 := hb (x (-2) 2)
      have b34835 := hb (x 0 13)
      have b34836 := hb (x (-1) 1 && x (-1) 14)
      clear * - r34833 b34834 b34835 b34836 d34828 g40
      omega
    have d34837 : (x 0 12).toNat = 0 := by
      have r34838 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34839 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e34840 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b34841 := hb (x (-3) 3)
      have b34842 := hb (x (-2) 2)
      have b34843 := hb (x (-1) 13)
      have b34844 := hb (x 0 12)
      clear * - r34838 e34839 e34840 b34841 b34842 b34843 b34844 g3 d34832
      omega
    have d34845 : (x 0 4).toNat = 0 := by
      have r34846 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b34847 := hb (x 0 4)
      have b34848 := hb (x 0 12)
      clear * - r34846 b34847 b34848 d34837
      omega
    have d34849 : (x 0 4 && x 0 14).toNat = 0 := by
      have r34850 := hand1 (x 0 4) (x 0 14)
      have b34851 := hb (x 0 4)
      have b34852 := hb (x 0 4 && x 0 14)
      clear * - r34850 b34851 b34852 d34845
      omega
    have r34853 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e34854 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e34855 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have r34856 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e34857 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e34858 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have r34859 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r34860 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r34861 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r34862 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r34863 := hand1 (x 2 2) (x 2 12)
    have r34864 := hand2 (x 2 2) (x 2 12)
    have r34865 := hand1 (x 1 3) (x 1 13)
    have r34866 := hand2 (x 1 3) (x 1 13)
    have r34867 := hand1 (x 1 1) (x 1 14)
    have r34868 := hand2 (x 2 1) (x 2 14)
    linarith only [r34853, e34854, e34855, r34856, e34857, e34858, r34859, r34860, r34861, r34862, r34863, r34864, r34865, r34866, r34867, r34868, g0, g6, g11, g12, g36, d34849]
  · have f34889 : (x 0 1).toNat = 1 := by rw [h34826]; rfl
    have d34890 : (x 1 14).toNat = 0 := by
      have r34891 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34892 := hb (x 0 1)
      have b34893 := hb (x 1 14)
      clear * - r34891 b34892 b34893 f34889
      omega
    have d34894 : (x 1 1 && x 1 14).toNat = 0 := by
      have r34895 := hand2 (x 1 1) (x 1 14)
      have b34896 := hb (x 1 14)
      have b34897 := hb (x 1 1 && x 1 14)
      clear * - r34895 b34896 b34897 d34890
      omega
    have d34898 : (x 1 6).toNat = 0 := by
      have r34899 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
      have b34900 := hb (x 1 6)
      have b34901 := hb (x 1 14)
      clear * - r34899 b34900 b34901 d34890
      omega
    have d34902 : (x 1 6 && x 1 13).toNat = 0 := by
      have r34903 := hand1 (x 1 6) (x 1 13)
      have b34904 := hb (x 1 6)
      have b34905 := hb (x 1 6 && x 1 13)
      clear * - r34903 b34904 b34905 d34898
      omega
    have d34906 : (x 0 2).toNat = 1 := by
      have r34907 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34908 := hb (x 0 2)
      have b34909 := hb (x 2 13)
      have b34910 := hb (x 1 1 && x 1 14)
      clear * - r34907 b34908 b34909 b34910 g11 d34894
      omega
    have d34911 : (x 2 12).toNat = 0 := by
      have r34912 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34913 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e34914 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b34915 := hb (x (-1) 3)
      have b34916 := hb (x 0 2)
      have b34917 := hb (x 1 13)
      have b34918 := hb (x 2 12)
      clear * - r34912 e34913 e34914 b34915 b34916 b34917 b34918 d34906
      omega
    have d34919 : (x 2 2 && x 2 12).toNat = 0 := by
      have r34920 := hand2 (x 2 2) (x 2 12)
      have b34921 := hb (x 2 12)
      have b34922 := hb (x 2 2 && x 2 12)
      clear * - r34920 b34921 b34922 d34911
      omega
    have d34923 : (x 2 3 && x 2 12).toNat = 0 := by
      have r34924 := hand2 (x 2 3) (x 2 12)
      have b34925 := hb (x 2 12)
      have b34926 := hb (x 2 3 && x 2 12)
      clear * - r34924 b34925 b34926 d34911
      omega
    have d34927 : (x 2 6 && x 2 12).toNat = 0 := by
      have r34928 := hand2 (x 2 6) (x 2 12)
      have b34929 := hb (x 2 12)
      have b34930 := hb (x 2 6 && x 2 12)
      clear * - r34928 b34929 b34930 d34911
      omega
    have d34931 : (x 2 7 && x 2 12).toNat = 0 := by
      have r34932 := hand2 (x 2 7) (x 2 12)
      have b34933 := hb (x 2 12)
      have b34934 := hb (x 2 7 && x 2 12)
      clear * - r34932 b34933 b34934 d34911
      omega
    have d34935 : (x 1 13).toNat = 0 := by
      have r34936 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34937 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e34938 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b34939 := hb (x (-1) 3)
      have b34940 := hb (x 0 2)
      have b34941 := hb (x 1 13)
      have b34942 := hb (x 2 12)
      clear * - r34936 e34937 e34938 b34939 b34940 b34941 b34942 d34911 d34906
      omega
    have d34943 : (x 1 3 && x 1 13).toNat = 0 := by
      have r34944 := hand2 (x 1 3) (x 1 13)
      have b34945 := hb (x 1 13)
      have b34946 := hb (x 1 3 && x 1 13)
      clear * - r34944 b34945 b34946 d34935
      omega
    have d34947 : (x 1 4 && x 1 13).toNat = 0 := by
      have r34948 := hand2 (x 1 4) (x 1 13)
      have b34949 := hb (x 1 13)
      have b34950 := hb (x 1 4 && x 1 13)
      clear * - r34948 b34949 b34950 d34935
      omega
    have d34951 : (x 1 7 && x 1 13).toNat = 0 := by
      have r34952 := hand2 (x 1 7) (x 1 13)
      have b34953 := hb (x 1 13)
      have b34954 := hb (x 1 7 && x 1 13)
      clear * - r34952 b34953 b34954 d34935
      omega
    have d34955 : (x 1 8 && x 1 13).toNat = 0 := by
      have r34956 := hand2 (x 1 8) (x 1 13)
      have b34957 := hb (x 1 13)
      have b34958 := hb (x 1 8 && x 1 13)
      clear * - r34956 b34957 b34958 d34935
      omega
    have d34959 : (x 0 4 && x 0 14).toNat = 1 := by
      have r34960 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34961 := hb (x (-1) 5)
      have b34962 := hb (x 4 10)
      have b34963 := hb (x 3 1 && x 3 11)
      have b34964 := hb (x 2 2 && x 2 12)
      have b34965 := hb (x 1 3 && x 1 13)
      have b34966 := hb (x 0 4 && x 0 14)
      clear * - r34960 b34961 b34962 b34963 b34964 b34965 b34966 g12 g36 d34919 d34943 g0
      omega
    have d34967 : (x 0 4).toNat = 1 := by
      have r34968 := hand1 (x 0 4) (x 0 14)
      have b34969 := hb (x 0 4)
      have b34970 := hb (x 0 4 && x 0 14)
      clear * - r34968 b34969 b34970 d34959
      omega
    have d34971 : (x 0 12).toNat = 1 := by
      have r34972 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b34973 := hb (x 0 4)
      have b34974 := hb (x 0 12)
      clear * - r34972 b34973 b34974 d34967
      omega
    have d34975 : (x (-2) 2).toNat = 0 := by
      have r34976 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34977 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e34978 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b34979 := hb (x (-3) 3)
      have b34980 := hb (x (-2) 2)
      have b34981 := hb (x (-1) 13)
      have b34982 := hb (x 0 12)
      clear * - r34976 e34977 e34978 b34979 b34980 b34981 b34982 d34971 g3
      omega
    have d34983 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r34984 := hand1 (x (-2) 2) (x (-2) 13)
      have b34985 := hb (x (-2) 2)
      have b34986 := hb (x (-2) 2 && x (-2) 13)
      clear * - r34984 b34985 b34986 d34975
      omega
    have d34987 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
      have r34988 := hand1 (x (-2) 2) (x (-2) 11)
      have b34989 := hb (x (-2) 2)
      have b34990 := hb (x (-2) 2 && x (-2) 11)
      clear * - r34988 b34989 b34990 d34975
      omega
    have d34991 : (x (-2) 10).toNat = 0 := by
      have r34992 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
      have b34993 := hb (x (-2) 2)
      have b34994 := hb (x (-2) 10)
      clear * - r34992 b34993 b34994 d34975
      omega
    have d34995 : (x 0 13).toNat = 1 := by
      have r34996 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34997 := hb (x (-2) 2)
      have b34998 := hb (x 0 13)
      have b34999 := hb (x (-1) 1 && x (-1) 14)
      clear * - r34996 b34997 b34998 b34999 g40 d34975
      omega
    have d35000 : (x 1 12).toNat = 0 := by
      have r35001 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35002 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e35003 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b35004 := hb (x (-2) 3)
      have b35005 := hb (x (-1) 2)
      have b35006 := hb (x 0 13)
      have b35007 := hb (x 1 12)
      clear * - r35001 e35002 e35003 b35004 b35005 b35006 b35007 d34995
      omega
    have d35008 : (x 1 8 && x 1 12).toNat = 0 := by
      have r35009 := hand2 (x 1 8) (x 1 12)
      have b35010 := hb (x 1 12)
      have b35011 := hb (x 1 8 && x 1 12)
      clear * - r35009 b35010 b35011 d35000
      omega
    have d35012 : (x 1 4).toNat = 0 := by
      have r35013 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
      have b35014 := hb (x 1 4)
      have b35015 := hb (x 1 12)
      clear * - r35013 b35014 b35015 d35000
      omega
    have d35016 : (x (-1) 2).toNat = 0 := by
      have r35017 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35018 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e35019 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b35020 := hb (x (-2) 3)
      have b35021 := hb (x (-1) 2)
      have b35022 := hb (x 0 13)
      have b35023 := hb (x 1 12)
      clear * - r35017 e35018 e35019 b35020 b35021 b35022 b35023 d35000 d34995
      omega
    have d35024 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
      have r35025 := hand1 (x (-1) 2) (x (-1) 12)
      have b35026 := hb (x (-1) 2)
      have b35027 := hb (x (-1) 2 && x (-1) 12)
      clear * - r35025 b35026 b35027 d35016
      omega
    have d35028 : (x (-1) 10).toNat = 0 := by
      have r35029 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
      have b35030 := hb (x (-1) 2)
      have b35031 := hb (x (-1) 10)
      clear * - r35029 b35030 b35031 d35016
      omega
    have d35032 : (x (-2) 3).toNat = 0 := by
      have r35033 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35034 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e35035 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b35036 := hb (x (-2) 3)
      have b35037 := hb (x (-1) 2)
      have b35038 := hb (x 0 13)
      have b35039 := hb (x 1 12)
      clear * - r35033 e35034 e35035 b35036 b35037 b35038 b35039 d35000 d34995 d35016
      omega
    have d35040 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
      have r35041 := hand1 (x (-2) 3) (x (-2) 13)
      have b35042 := hb (x (-2) 3)
      have b35043 := hb (x (-2) 3 && x (-2) 13)
      clear * - r35041 b35042 b35043 d35032
      omega
    have d35044 : (x (-2) 11).toNat = 0 := by
      have r35045 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
      have b35046 := hb (x (-2) 3)
      have b35047 := hb (x (-2) 11)
      clear * - r35045 b35046 b35047 d35032
      omega
    have d35048 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
      have r35049 := hand2 (x (-2) 1) (x (-2) 11)
      have b35050 := hb (x (-2) 11)
      have b35051 := hb (x (-2) 1 && x (-2) 11)
      clear * - r35049 b35050 b35051 d35044
      omega
    have d35052 : (x (-2) 6 && x (-2) 11).toNat = 0 := by
      have r35053 := hand2 (x (-2) 6) (x (-2) 11)
      have b35054 := hb (x (-2) 11)
      have b35055 := hb (x (-2) 6 && x (-2) 11)
      clear * - r35053 b35054 b35055 d35044
      omega
    have d35056 : (x (-3) 3).toNat = 0 := by
      have r35057 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35058 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e35059 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b35060 := hb (x (-3) 3)
      have b35061 := hb (x (-2) 2)
      have b35062 := hb (x (-1) 13)
      have b35063 := hb (x 0 12)
      clear * - r35057 e35058 e35059 b35060 b35061 b35062 b35063 d34971 g3 d34975
      omega
    have d35064 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r35065 := hand1 (x (-3) 3) (x (-3) 14)
      have b35066 := hb (x (-3) 3)
      have b35067 := hb (x (-3) 3 && x (-3) 14)
      clear * - r35065 b35066 b35067 d35056
      omega
    have d35068 : (x (-4) 4).toNat = 1 := by
      have r35069 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b35070 := hb (x (-4) 4)
      have b35071 := hb (x 0 11)
      have b35072 := hb (x (-1) 1 && x (-1) 12)
      have b35073 := hb (x (-2) 2 && x (-2) 13)
      have b35074 := hb (x (-3) 3 && x (-3) 14)
      clear * - r35069 b35070 b35071 b35072 b35073 b35074 g5 g39 d34983 d35064
      omega
    have d35075 : (x (-4) 12).toNat = 1 := by
      have r35076 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b35077 := hb (x (-4) 4)
      have b35078 := hb (x (-4) 12)
      clear * - r35076 b35077 b35078 d35068
      omega
    have d35079 : (x (-5) 13).toNat = 0 := by
      have r35080 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35081 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e35082 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b35083 := hb (x (-7) 3)
      have b35084 := hb (x (-6) 2)
      have b35085 := hb (x (-5) 13)
      have b35086 := hb (x (-4) 12)
      clear * - r35080 e35081 e35082 b35083 b35084 b35085 b35086 d35075
      omega
    have d35087 : (x (-5) 5).toNat = 0 := by
      have r35088 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b35089 := hb (x (-5) 5)
      have b35090 := hb (x (-5) 13)
      clear * - r35088 b35089 b35090 d35079
      omega
    have d35091 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
      have r35092 := hand1 (x (-5) 5) (x (-5) 14)
      have b35093 := hb (x (-5) 5)
      have b35094 := hb (x (-5) 5 && x (-5) 14)
      clear * - r35092 b35093 b35094 d35087
      omega
    have d35095 : (x (-6) 2).toNat = 0 := by
      have r35096 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35097 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e35098 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b35099 := hb (x (-7) 3)
      have b35100 := hb (x (-6) 2)
      have b35101 := hb (x (-5) 13)
      have b35102 := hb (x (-4) 12)
      clear * - r35096 e35097 e35098 b35099 b35100 b35101 b35102 d35075 d35079
      omega
    have d35103 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
      have r35104 := hand1 (x (-6) 2) (x (-6) 13)
      have b35105 := hb (x (-6) 2)
      have b35106 := hb (x (-6) 2 && x (-6) 13)
      clear * - r35104 b35105 b35106 d35095
      omega
    have d35107 : (x (-6) 2 && x (-6) 12).toNat = 0 := by
      have r35108 := hand1 (x (-6) 2) (x (-6) 12)
      have b35109 := hb (x (-6) 2)
      have b35110 := hb (x (-6) 2 && x (-6) 12)
      clear * - r35108 b35109 b35110 d35095
      omega
    have d35111 : (x (-6) 2 && x (-6) 11).toNat = 0 := by
      have r35112 := hand1 (x (-6) 2) (x (-6) 11)
      have b35113 := hb (x (-6) 2)
      have b35114 := hb (x (-6) 2 && x (-6) 11)
      clear * - r35112 b35113 b35114 d35095
      omega
    have d35115 : (x (-6) 10).toNat = 0 := by
      have r35116 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
      have b35117 := hb (x (-6) 2)
      have b35118 := hb (x (-6) 10)
      clear * - r35116 b35117 b35118 d35095
      omega
    have d35119 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
      have r35120 := hand2 (x (-6) 5) (x (-6) 10)
      have b35121 := hb (x (-6) 10)
      have b35122 := hb (x (-6) 5 && x (-6) 10)
      clear * - r35120 b35121 b35122 d35115
      omega
    have d35123 : (x (-7) 3).toNat = 0 := by
      have r35124 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35125 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e35126 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b35127 := hb (x (-7) 3)
      have b35128 := hb (x (-6) 2)
      have b35129 := hb (x (-5) 13)
      have b35130 := hb (x (-4) 12)
      clear * - r35124 e35125 e35126 b35127 b35128 b35129 b35130 d35075 d35079 d35095
      omega
    have d35131 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
      have r35132 := hand1 (x (-7) 3) (x (-7) 14)
      have b35133 := hb (x (-7) 3)
      have b35134 := hb (x (-7) 3 && x (-7) 14)
      clear * - r35132 b35133 b35134 d35123
      omega
    have d35135 : (x (-7) 3 && x (-7) 13).toNat = 0 := by
      have r35136 := hand1 (x (-7) 3) (x (-7) 13)
      have b35137 := hb (x (-7) 3)
      have b35138 := hb (x (-7) 3 && x (-7) 13)
      clear * - r35136 b35137 b35138 d35123
      omega
    have d35139 : (x (-7) 3 && x (-7) 12).toNat = 0 := by
      have r35140 := hand1 (x (-7) 3) (x (-7) 12)
      have b35141 := hb (x (-7) 3)
      have b35142 := hb (x (-7) 3 && x (-7) 12)
      clear * - r35140 b35141 b35142 d35123
      omega
    have d35143 : (x (-7) 11).toNat = 0 := by
      have r35144 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have b35145 := hb (x (-7) 3)
      have b35146 := hb (x (-7) 11)
      clear * - r35144 b35145 b35146 d35123
      omega
    have d35147 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
      have r35148 := hand2 (x (-7) 6) (x (-7) 11)
      have b35149 := hb (x (-7) 11)
      have b35150 := hb (x (-7) 6 && x (-7) 11)
      clear * - r35148 b35149 b35150 d35143
      omega
    have d35151 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
      have r35152 := hand1 (x (-3) 3) (x (-3) 12)
      have b35153 := hb (x (-3) 3)
      have b35154 := hb (x (-3) 3 && x (-3) 12)
      clear * - r35152 b35153 b35154 d35056
      omega
    have d35155 : (x (-3) 11).toNat = 0 := by
      have r35156 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
      have b35157 := hb (x (-3) 3)
      have b35158 := hb (x (-3) 11)
      clear * - r35156 b35157 b35158 d35056
      omega
    have d35159 : (x 4 8).toNat = 0 := by
      have r35160 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35161 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e35162 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e35163 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e35164 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e35165 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e35166 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b35167 := hb (x (-3) 7)
      have b35168 := hb (x (-2) 6)
      have b35169 := hb (x (-1) 5)
      have b35170 := hb (x 0 4)
      have b35171 := hb (x 1 11)
      have b35172 := hb (x 2 10)
      have b35173 := hb (x 3 9)
      have b35174 := hb (x 4 8)
      clear * - r35160 e35161 e35162 e35163 e35164 e35165 e35166 b35167 b35168 b35169 b35170 b35171 b35172 b35173 b35174 d34967 g0
      omega
    have d35175 : (x 3 9).toNat = 0 := by
      have r35176 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35177 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e35178 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e35179 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e35180 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e35181 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e35182 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b35183 := hb (x (-3) 7)
      have b35184 := hb (x (-2) 6)
      have b35185 := hb (x (-1) 5)
      have b35186 := hb (x 0 4)
      have b35187 := hb (x 1 11)
      have b35188 := hb (x 2 10)
      have b35189 := hb (x 3 9)
      have b35190 := hb (x 4 8)
      clear * - r35176 e35177 e35178 e35179 e35180 e35181 e35182 b35183 b35184 b35185 b35186 b35187 b35188 b35189 b35190 d35159 d34967 g0
      omega
    have d35191 : (x 2 10).toNat = 0 := by
      have r35192 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35193 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e35194 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e35195 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e35196 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e35197 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e35198 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b35199 := hb (x (-3) 7)
      have b35200 := hb (x (-2) 6)
      have b35201 := hb (x (-1) 5)
      have b35202 := hb (x 0 4)
      have b35203 := hb (x 1 11)
      have b35204 := hb (x 2 10)
      have b35205 := hb (x 3 9)
      have b35206 := hb (x 4 8)
      clear * - r35192 e35193 e35194 e35195 e35196 e35197 e35198 b35199 b35200 b35201 b35202 b35203 b35204 b35205 b35206 d35159 d35175 d34967 g0
      omega
    have d35207 : (x 1 11).toNat = 0 := by
      have r35208 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35209 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e35210 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e35211 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e35212 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e35213 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e35214 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b35215 := hb (x (-3) 7)
      have b35216 := hb (x (-2) 6)
      have b35217 := hb (x (-1) 5)
      have b35218 := hb (x 0 4)
      have b35219 := hb (x 1 11)
      have b35220 := hb (x 2 10)
      have b35221 := hb (x 3 9)
      have b35222 := hb (x 4 8)
      clear * - r35208 e35209 e35210 e35211 e35212 e35213 e35214 b35215 b35216 b35217 b35218 b35219 b35220 b35221 b35222 d35159 d35175 d35191 d34967 g0
      omega
    have d35223 : (x (-2) 6).toNat = 0 := by
      have r35224 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35225 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e35226 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e35227 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e35228 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e35229 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e35230 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b35231 := hb (x (-3) 7)
      have b35232 := hb (x (-2) 6)
      have b35233 := hb (x (-1) 5)
      have b35234 := hb (x 0 4)
      have b35235 := hb (x 1 11)
      have b35236 := hb (x 2 10)
      have b35237 := hb (x 3 9)
      have b35238 := hb (x 4 8)
      clear * - r35224 e35225 e35226 e35227 e35228 e35229 e35230 b35231 b35232 b35233 b35234 b35235 b35236 b35237 b35238 d35159 d35175 d35191 d35207 d34967 g0
      omega
    have d35239 : (x (-2) 6 && x (-2) 13).toNat = 0 := by
      have r35240 := hand1 (x (-2) 6) (x (-2) 13)
      have b35241 := hb (x (-2) 6)
      have b35242 := hb (x (-2) 6 && x (-2) 13)
      clear * - r35240 b35241 b35242 d35223
      omega
    have d35243 : (x (-2) 1 && x (-2) 6).toNat = 0 := by
      have r35244 := hand2 (x (-2) 1) (x (-2) 6)
      have b35245 := hb (x (-2) 6)
      have b35246 := hb (x (-2) 1 && x (-2) 6)
      clear * - r35244 b35245 b35246 d35223
      omega
    have d35247 : (x (-3) 7).toNat = 0 := by
      have r35248 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35249 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
      have e35250 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
      have e35251 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
      have e35252 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
      have e35253 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
      have e35254 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
      have b35255 := hb (x (-3) 7)
      have b35256 := hb (x (-2) 6)
      have b35257 := hb (x (-1) 5)
      have b35258 := hb (x 0 4)
      have b35259 := hb (x 1 11)
      have b35260 := hb (x 2 10)
      have b35261 := hb (x 3 9)
      have b35262 := hb (x 4 8)
      clear * - r35248 e35249 e35250 e35251 e35252 e35253 e35254 b35255 b35256 b35257 b35258 b35259 b35260 b35261 b35262 d35159 d35175 d35191 d35207 d34967 g0 d35223
      omega
    have d35263 : (x (-3) 7 && x (-3) 14).toNat = 0 := by
      have r35264 := hand1 (x (-3) 7) (x (-3) 14)
      have b35265 := hb (x (-3) 7)
      have b35266 := hb (x (-3) 7 && x (-3) 14)
      clear * - r35264 b35265 b35266 d35247
      omega
    have d35267 : (x (-3) 7 && x (-3) 12).toNat = 0 := by
      have r35268 := hand1 (x (-3) 7) (x (-3) 12)
      have b35269 := hb (x (-3) 7)
      have b35270 := hb (x (-3) 7 && x (-3) 12)
      clear * - r35268 b35269 b35270 d35247
      omega
    have d35271 : (x (-3) 2 && x (-3) 7).toNat = 0 := by
      have r35272 := hand2 (x (-3) 2) (x (-3) 7)
      have b35273 := hb (x (-3) 7)
      have b35274 := hb (x (-3) 2 && x (-3) 7)
      clear * - r35272 b35273 b35274 d35247
      omega
    have d35275 : (x 0 8).toNat = 0 := by
      have r35276 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35277 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e35278 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e35279 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e35280 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e35281 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e35282 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b35283 := hb (x (-7) 7)
      have b35284 := hb (x (-6) 6)
      have b35285 := hb (x (-5) 5)
      have b35286 := hb (x (-4) 4)
      have b35287 := hb (x (-3) 11)
      have b35288 := hb (x (-2) 10)
      have b35289 := hb (x (-1) 9)
      have b35290 := hb (x 0 8)
      clear * - r35276 e35277 e35278 e35279 e35280 e35281 e35282 b35283 b35284 b35285 b35286 b35287 b35288 b35289 b35290 g2 d34991 d35155 d35068 d35087
      omega
    have d35291 : (x 0 8 && x 0 14).toNat = 0 := by
      have r35292 := hand1 (x 0 8) (x 0 14)
      have b35293 := hb (x 0 8)
      have b35294 := hb (x 0 8 && x 0 14)
      clear * - r35292 b35293 b35294 d35275
      omega
    have d35295 : (x (-6) 6).toNat = 0 := by
      have r35296 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35297 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e35298 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e35299 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e35300 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e35301 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e35302 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b35303 := hb (x (-7) 7)
      have b35304 := hb (x (-6) 6)
      have b35305 := hb (x (-5) 5)
      have b35306 := hb (x (-4) 4)
      have b35307 := hb (x (-3) 11)
      have b35308 := hb (x (-2) 10)
      have b35309 := hb (x (-1) 9)
      have b35310 := hb (x 0 8)
      clear * - r35296 e35297 e35298 e35299 e35300 e35301 e35302 b35303 b35304 b35305 b35306 b35307 b35308 b35309 b35310 d35275 g2 d34991 d35155 d35068 d35087
      omega
    cases h35311 : x 0 5
    · have f35312 : (x 0 5).toNat = 0 := by rw [h35311]; rfl
      have d35313 : (x 0 5 && x 0 14).toNat = 0 := by
        have r35314 := hand1 (x 0 5) (x 0 14)
        have b35315 := hb (x 0 5)
        have b35316 := hb (x 0 5 && x 0 14)
        clear * - r35314 b35315 b35316 f35312
        omega
      have d35317 : (x (-1) 6).toNat = 1 := by
        have r35318 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35319 := hb (x (-1) 6)
        have b35320 := hb (x 5 9)
        have b35321 := hb (x 4 1 && x 4 10)
        have b35322 := hb (x 3 2 && x 3 11)
        have b35323 := hb (x 2 3 && x 2 12)
        have b35324 := hb (x 1 4 && x 1 13)
        have b35325 := hb (x 0 5 && x 0 14)
        clear * - r35318 b35319 b35320 b35321 b35322 b35323 b35324 b35325 g13 g32 g33 d34923 d34947 d35313
        omega
      have d35326 : (x (-1) 14).toNat = 1 := by
        have r35327 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
        have b35328 := hb (x (-1) 6)
        have b35329 := hb (x (-1) 14)
        clear * - r35327 b35328 b35329 d35317
        omega
      have d35330 : (x (-2) 1).toNat = 0 := by
        have r35331 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35332 := hb (x (-2) 1)
        have b35333 := hb (x (-1) 14)
        clear * - r35331 b35332 b35333 d35326
        omega
      have d35334 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r35335 := hand1 (x (-2) 1) (x (-2) 14)
        have b35336 := hb (x (-2) 1)
        have b35337 := hb (x (-2) 1 && x (-2) 14)
        clear * - r35335 b35336 b35337 d35330
        omega
      have d35338 : (x (-3) 2).toNat = 1 := by
        have r35339 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35340 := hb (x (-3) 2)
        have b35341 := hb (x (-1) 13)
        have b35342 := hb (x (-2) 1 && x (-2) 14)
        clear * - r35339 b35340 b35341 b35342 g3 d35334
        omega
      have d35343 : (x (-3) 14).toNat = 1 := by
        have r35344 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b35345 := hb (x (-3) 2)
        have b35346 := hb (x (-3) 14)
        clear * - r35344 b35345 b35346 d35338
        omega
      have d35347 : (x (-4) 1).toNat = 0 := by
        have r35348 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35349 := hb (x (-4) 1)
        have b35350 := hb (x (-3) 14)
        clear * - r35348 b35349 b35350 d35343
        omega
      have d35351 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
        have r35352 := hand1 (x (-4) 1) (x (-4) 14)
        have b35353 := hb (x (-4) 1)
        have b35354 := hb (x (-4) 1 && x (-4) 14)
        clear * - r35352 b35353 b35354 d35347
        omega
      have d35355 : (x (-4) 13).toNat = 0 := by
        have r35356 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b35357 := hb (x (-4) 1)
        have b35358 := hb (x (-4) 13)
        clear * - r35356 b35357 b35358 d35347
        omega
      have d35359 : (x (-4) 5).toNat = 0 := by
        have r35360 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
        have b35361 := hb (x (-4) 5)
        have b35362 := hb (x (-4) 13)
        clear * - r35360 b35361 b35362 d35355
        omega
      have d35363 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
        have r35364 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35365 := hb (x (-4) 5)
        have b35366 := hb (x 1 10)
        have b35367 := hb (x 0 1 && x 0 11)
        have b35368 := hb (x (-1) 2 && x (-1) 12)
        have b35369 := hb (x (-2) 3 && x (-2) 13)
        have b35370 := hb (x (-3) 4 && x (-3) 14)
        clear * - r35364 b35365 b35366 b35367 b35368 b35369 b35370 g8 d34818 d35024 d35040 d35359
        omega
      have d35371 : (x (-3) 4).toNat = 1 := by
        have r35372 := hand1 (x (-3) 4) (x (-3) 14)
        have b35373 := hb (x (-3) 4)
        have b35374 := hb (x (-3) 4 && x (-3) 14)
        clear * - r35372 b35373 b35374 d35363
        omega
      have d35375 : (x (-3) 12).toNat = 1 := by
        have r35376 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b35377 := hb (x (-3) 4)
        have b35378 := hb (x (-3) 12)
        clear * - r35376 b35377 b35378 d35371
        omega
      have d35379 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
        have r35380 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35381 := hb (x (-6) 2)
        have b35382 := hb (x (-4) 13)
        have b35383 := hb (x (-5) 1 && x (-5) 14)
        clear * - r35380 b35381 b35382 b35383 d35355 d35095
        omega
      have d35384 : (x (-5) 14).toNat = 1 := by
        have r35385 := hand2 (x (-5) 1) (x (-5) 14)
        have b35386 := hb (x (-5) 14)
        have b35387 := hb (x (-5) 1 && x (-5) 14)
        clear * - r35385 b35386 b35387 d35379
        omega
      have d35388 : (x (-6) 1).toNat = 0 := by
        have r35389 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35390 := hb (x (-6) 1)
        have b35391 := hb (x (-5) 14)
        clear * - r35389 b35390 b35391 d35384
        omega
      have d35392 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
        have r35393 := hand1 (x (-6) 1) (x (-6) 14)
        have b35394 := hb (x (-6) 1)
        have b35395 := hb (x (-6) 1 && x (-6) 14)
        clear * - r35393 b35394 b35395 d35388
        omega
      have d35396 : (x (-7) 2).toNat = 1 := by
        have r35397 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35398 := hb (x (-7) 2)
        have b35399 := hb (x (-5) 13)
        have b35400 := hb (x (-6) 1 && x (-6) 14)
        clear * - r35397 b35398 b35399 b35400 d35079 d35392
        omega
      have d35401 : (x (-7) 14).toNat = 1 := by
        have r35402 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
        have b35403 := hb (x (-7) 2)
        have b35404 := hb (x (-7) 14)
        clear * - r35402 b35403 b35404 d35396
        omega
      have d35405 : (x (-8) 1).toNat = 0 := by
        have r35406 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35407 := hb (x (-8) 1)
        have b35408 := hb (x (-7) 14)
        clear * - r35406 b35407 b35408 d35401
        omega
      have d35409 : (x (-8) 13).toNat = 0 := by
        have r35410 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b35411 := hb (x (-8) 1)
        have b35412 := hb (x (-8) 13)
        clear * - r35410 b35411 b35412 d35405
        omega
      have d35413 : (x (-5) 12).toNat = 0 := by
        have r35414 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35415 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e35416 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b35417 := hb (x (-8) 3)
        have b35418 := hb (x (-7) 2)
        have b35419 := hb (x (-6) 13)
        have b35420 := hb (x (-5) 12)
        clear * - r35414 e35415 e35416 b35417 b35418 b35419 b35420 d35396
        omega
      have d35421 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
        have r35422 := hand2 (x (-5) 1) (x (-5) 12)
        have b35423 := hb (x (-5) 12)
        have b35424 := hb (x (-5) 1 && x (-5) 12)
        clear * - r35422 b35423 b35424 d35413
        omega
      have d35425 : (x (-5) 1).toNat = 1 := by
        have r35426 := hand1 (x (-5) 1) (x (-5) 14)
        have b35427 := hb (x (-5) 1)
        have b35428 := hb (x (-5) 1 && x (-5) 14)
        clear * - r35426 b35427 b35428 d35379
        omega
      have d35429 : (x (-4) 14).toNat = 0 := by
        have r35430 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35431 := hb (x (-5) 1)
        have b35432 := hb (x (-4) 14)
        clear * - r35430 b35431 b35432 d35425
        omega
      have d35433 : (x (-4) 2).toNat = 0 := by
        have r35434 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
        have b35435 := hb (x (-4) 2)
        have b35436 := hb (x (-4) 14)
        clear * - r35434 b35435 b35436 d35429
        omega
      have d35437 : (x (-4) 10).toNat = 0 := by
        have r35438 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
        have b35439 := hb (x (-4) 2)
        have b35440 := hb (x (-4) 10)
        clear * - r35438 b35439 b35440 d35433
        omega
      have d35441 : (x (-5) 2).toNat = 0 := by
        have r35442 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35443 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e35444 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b35445 := hb (x (-6) 3)
        have b35446 := hb (x (-5) 2)
        have b35447 := hb (x (-4) 13)
        have b35448 := hb (x (-3) 12)
        clear * - r35442 e35443 e35444 b35445 b35446 b35447 b35448 d35375 d35355
        omega
      have d35449 : (x (-3) 13).toNat = 1 := by
        have r35450 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35451 := hb (x (-5) 2)
        have b35452 := hb (x (-3) 13)
        have b35453 := hb (x (-4) 1 && x (-4) 14)
        clear * - r35450 b35451 b35452 b35453 d35351 d35441
        omega
      have d35454 : (x (-2) 12).toNat = 0 := by
        have r35455 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35456 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e35457 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b35458 := hb (x (-5) 3)
        have b35459 := hb (x (-4) 2)
        have b35460 := hb (x (-3) 13)
        have b35461 := hb (x (-2) 12)
        clear * - r35455 e35456 e35457 b35458 b35459 b35460 b35461 d35449 d35433
        omega
      have d35462 : (x (-5) 3).toNat = 0 := by
        have r35463 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35464 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e35465 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b35466 := hb (x (-5) 3)
        have b35467 := hb (x (-4) 2)
        have b35468 := hb (x (-3) 13)
        have b35469 := hb (x (-2) 12)
        clear * - r35463 e35464 e35465 b35466 b35467 b35468 b35469 d35454 d35449 d35433
        omega
      have d35470 : (x (-5) 11).toNat = 0 := by
        have r35471 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
        have b35472 := hb (x (-5) 3)
        have b35473 := hb (x (-5) 11)
        clear * - r35471 b35472 b35473 d35462
        omega
      have d35474 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
        have r35475 := hand2 (x (-5) 1) (x (-5) 11)
        have b35476 := hb (x (-5) 11)
        have b35477 := hb (x (-5) 1 && x (-5) 11)
        clear * - r35475 b35476 b35477 d35470
        omega
      have d35478 : (x (-1) 12).toNat = 0 := by
        have r35479 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35480 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e35481 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b35482 := hb (x (-4) 3)
        have b35483 := hb (x (-3) 2)
        have b35484 := hb (x (-2) 13)
        have b35485 := hb (x (-1) 12)
        clear * - r35479 e35480 e35481 b35482 b35483 b35484 b35485 d35338
        omega
      have d35486 : (x (-2) 13).toNat = 0 := by
        have r35487 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35488 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e35489 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b35490 := hb (x (-4) 3)
        have b35491 := hb (x (-3) 2)
        have b35492 := hb (x (-2) 13)
        have b35493 := hb (x (-1) 12)
        clear * - r35487 e35488 e35489 b35490 b35491 b35492 b35493 d35478 d35338
        omega
      have d35494 : (x (-4) 3).toNat = 0 := by
        have r35495 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35496 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e35497 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b35498 := hb (x (-4) 3)
        have b35499 := hb (x (-3) 2)
        have b35500 := hb (x (-2) 13)
        have b35501 := hb (x (-1) 12)
        clear * - r35495 e35496 e35497 b35498 b35499 b35500 b35501 d35478 d35486 d35338
        omega
      have d35502 : (x (-4) 11).toNat = 0 := by
        have r35503 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
        have b35504 := hb (x (-4) 3)
        have b35505 := hb (x (-4) 11)
        clear * - r35503 b35504 b35505 d35494
        omega
      have d35506 : (x (-8) 4).toNat = 1 := by
        have r35507 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35508 := hb (x (-8) 4)
        have b35509 := hb (x (-4) 11)
        have b35510 := hb (x (-5) 1 && x (-5) 12)
        have b35511 := hb (x (-6) 2 && x (-6) 13)
        have b35512 := hb (x (-7) 3 && x (-7) 14)
        clear * - r35507 b35508 b35509 b35510 b35511 b35512 d35502 d35421 d35103 d35131
        omega
      have d35513 : (x (-8) 12).toNat = 1 := by
        have r35514 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
        have b35515 := hb (x (-8) 4)
        have b35516 := hb (x (-8) 12)
        clear * - r35514 b35515 b35516 d35506
        omega
      have d35517 : (x (-9) 13).toNat = 0 := by
        have r35518 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35519 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e35520 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b35521 := hb (x (-11) 3)
        have b35522 := hb (x (-10) 2)
        have b35523 := hb (x (-9) 13)
        have b35524 := hb (x (-8) 12)
        clear * - r35518 e35519 e35520 b35521 b35522 b35523 b35524 d35513
        omega
      have d35525 : (x (-9) 5).toNat = 0 := by
        have r35526 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
        have b35527 := hb (x (-9) 5)
        have b35528 := hb (x (-9) 13)
        clear * - r35526 b35527 b35528 d35517
        omega
      have d35529 : (x (-8) 4 && x (-8) 14).toNat = 1 := by
        have r35530 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35531 := hb (x (-9) 5)
        have b35532 := hb (x (-4) 10)
        have b35533 := hb (x (-5) 1 && x (-5) 11)
        have b35534 := hb (x (-6) 2 && x (-6) 12)
        have b35535 := hb (x (-7) 3 && x (-7) 13)
        have b35536 := hb (x (-8) 4 && x (-8) 14)
        clear * - r35530 b35531 b35532 b35533 b35534 b35535 b35536 d35437 d35474 d35107 d35135 d35525
        omega
      have d35537 : (x (-8) 14).toNat = 1 := by
        have r35538 := hand2 (x (-8) 4) (x (-8) 14)
        have b35539 := hb (x (-8) 14)
        have b35540 := hb (x (-8) 4 && x (-8) 14)
        clear * - r35538 b35539 b35540 d35529
        omega
      have d35541 : (x (-9) 1).toNat = 0 := by
        have r35542 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35543 := hb (x (-9) 1)
        have b35544 := hb (x (-8) 14)
        clear * - r35542 b35543 b35544 d35537
        omega
      have d35545 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
        have r35546 := hand1 (x (-9) 1) (x (-9) 14)
        have b35547 := hb (x (-9) 1)
        have b35548 := hb (x (-9) 1 && x (-9) 14)
        clear * - r35546 b35547 b35548 d35541
        omega
      have d35549 : (x (-10) 2).toNat = 1 := by
        have r35550 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35551 := hb (x (-10) 2)
        have b35552 := hb (x (-8) 13)
        have b35553 := hb (x (-9) 1 && x (-9) 14)
        clear * - r35550 b35551 b35552 b35553 d35409 d35545
        omega
      have r35554 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e35555 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e35556 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b35557 := hb (x (-11) 3)
      have b35558 := hb (x (-10) 2)
      have b35559 := hb (x (-9) 13)
      have b35560 := hb (x (-8) 12)
      linarith only [r35554, e35555, e35556, b35557, b35558, b35559, b35560, d35513, d35517, d35549]
    · have f35561 : (x 0 5).toNat = 1 := by rw [h35311]; rfl
      have d35562 : (x 5 8).toNat = 0 := by
        have r35563 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35564 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e35565 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e35566 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e35567 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e35568 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e35569 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b35570 := hb (x (-2) 7)
        have b35571 := hb (x (-1) 6)
        have b35572 := hb (x 0 5)
        have b35573 := hb (x 1 4)
        have b35574 := hb (x 2 11)
        have b35575 := hb (x 3 10)
        have b35576 := hb (x 4 9)
        have b35577 := hb (x 5 8)
        clear * - r35563 e35564 e35565 e35566 e35567 e35568 e35569 b35570 b35571 b35572 b35573 b35574 b35575 b35576 b35577 d35012 f35561
        omega
      have d35578 : (x 5 8 && x 5 14).toNat = 0 := by
        have r35579 := hand1 (x 5 8) (x 5 14)
        have b35580 := hb (x 5 8)
        have b35581 := hb (x 5 8 && x 5 14)
        clear * - r35579 b35580 b35581 d35562
        omega
      have d35582 : (x 5 4 && x 5 8).toNat = 0 := by
        have r35583 := hand2 (x 5 4) (x 5 8)
        have b35584 := hb (x 5 8)
        have b35585 := hb (x 5 4 && x 5 8)
        clear * - r35583 b35584 b35585 d35562
        omega
      have d35586 : (x 4 9).toNat = 0 := by
        have r35587 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35588 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e35589 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e35590 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e35591 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e35592 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e35593 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b35594 := hb (x (-2) 7)
        have b35595 := hb (x (-1) 6)
        have b35596 := hb (x 0 5)
        have b35597 := hb (x 1 4)
        have b35598 := hb (x 2 11)
        have b35599 := hb (x 3 10)
        have b35600 := hb (x 4 9)
        have b35601 := hb (x 5 8)
        clear * - r35587 e35588 e35589 e35590 e35591 e35592 e35593 b35594 b35595 b35596 b35597 b35598 b35599 b35600 b35601 d35562 d35012 f35561
        omega
      have d35602 : (x 4 5 && x 4 9).toNat = 0 := by
        have r35603 := hand2 (x 4 5) (x 4 9)
        have b35604 := hb (x 4 9)
        have b35605 := hb (x 4 5 && x 4 9)
        clear * - r35603 b35604 b35605 d35586
        omega
      have d35606 : (x 3 10).toNat = 0 := by
        have r35607 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35608 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e35609 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e35610 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e35611 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e35612 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e35613 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b35614 := hb (x (-2) 7)
        have b35615 := hb (x (-1) 6)
        have b35616 := hb (x 0 5)
        have b35617 := hb (x 1 4)
        have b35618 := hb (x 2 11)
        have b35619 := hb (x 3 10)
        have b35620 := hb (x 4 9)
        have b35621 := hb (x 5 8)
        clear * - r35607 e35608 e35609 e35610 e35611 e35612 e35613 b35614 b35615 b35616 b35617 b35618 b35619 b35620 b35621 d35562 d35586 d35012 f35561
        omega
      have d35622 : (x 3 6 && x 3 10).toNat = 0 := by
        have r35623 := hand2 (x 3 6) (x 3 10)
        have b35624 := hb (x 3 10)
        have b35625 := hb (x 3 6 && x 3 10)
        clear * - r35623 b35624 b35625 d35606
        omega
      have d35626 : (x 2 11).toNat = 0 := by
        have r35627 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35628 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e35629 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e35630 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e35631 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e35632 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e35633 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b35634 := hb (x (-2) 7)
        have b35635 := hb (x (-1) 6)
        have b35636 := hb (x 0 5)
        have b35637 := hb (x 1 4)
        have b35638 := hb (x 2 11)
        have b35639 := hb (x 3 10)
        have b35640 := hb (x 4 9)
        have b35641 := hb (x 5 8)
        clear * - r35627 e35628 e35629 e35630 e35631 e35632 e35633 b35634 b35635 b35636 b35637 b35638 b35639 b35640 b35641 d35562 d35586 d35606 d35012 f35561
        omega
      have d35642 : (x 2 7 && x 2 11).toNat = 0 := by
        have r35643 := hand2 (x 2 7) (x 2 11)
        have b35644 := hb (x 2 11)
        have b35645 := hb (x 2 7 && x 2 11)
        clear * - r35643 b35644 b35645 d35626
        omega
      have d35646 : (x (-1) 6).toNat = 0 := by
        have r35647 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35648 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e35649 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e35650 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e35651 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e35652 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e35653 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b35654 := hb (x (-2) 7)
        have b35655 := hb (x (-1) 6)
        have b35656 := hb (x 0 5)
        have b35657 := hb (x 1 4)
        have b35658 := hb (x 2 11)
        have b35659 := hb (x 3 10)
        have b35660 := hb (x 4 9)
        have b35661 := hb (x 5 8)
        clear * - r35647 e35648 e35649 e35650 e35651 e35652 e35653 b35654 b35655 b35656 b35657 b35658 b35659 b35660 b35661 d35562 d35586 d35606 d35626 d35012 f35561
        omega
      have d35662 : (x (-2) 7).toNat = 0 := by
        have r35663 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35664 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e35665 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e35666 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e35667 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e35668 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e35669 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b35670 := hb (x (-2) 7)
        have b35671 := hb (x (-1) 6)
        have b35672 := hb (x 0 5)
        have b35673 := hb (x 1 4)
        have b35674 := hb (x 2 11)
        have b35675 := hb (x 3 10)
        have b35676 := hb (x 4 9)
        have b35677 := hb (x 5 8)
        clear * - r35663 e35664 e35665 e35666 e35667 e35668 e35669 b35670 b35671 b35672 b35673 b35674 b35675 b35676 b35677 d35562 d35586 d35606 d35626 d35012 f35561 d35646
        omega
      cases h35678 : x 0 9
      · have f35679 : (x 0 9).toNat = 0 := by rw [h35678]; rfl
        have d35680 : (x 0 9 && x 0 14).toNat = 0 := by
          have r35681 := hand1 (x 0 9) (x 0 14)
          have b35682 := hb (x 0 9)
          have b35683 := hb (x 0 9 && x 0 14)
          clear * - r35681 b35682 b35683 f35679
          omega
        have d35684 : (x 0 4 && x 0 9).toNat = 0 := by
          have r35685 := hand2 (x 0 4) (x 0 9)
          have b35686 := hb (x 0 9)
          have b35687 := hb (x 0 4 && x 0 9)
          clear * - r35685 b35686 b35687 f35679
          omega
        have d35688 : (x 0 9 && x 0 13).toNat = 0 := by
          have r35689 := hand1 (x 0 9) (x 0 13)
          have b35690 := hb (x 0 9)
          have b35691 := hb (x 0 9 && x 0 13)
          clear * - r35689 b35690 b35691 f35679
          omega
        have d35692 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
          have r35693 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b35694 := hb (x (-6) 6)
          have b35695 := hb (x 0 9)
          have b35696 := hb (x (-1) 1 && x (-1) 10)
          have b35697 := hb (x (-2) 2 && x (-2) 11)
          have b35698 := hb (x (-3) 3 && x (-3) 12)
          have b35699 := hb (x (-4) 4 && x (-4) 13)
          have b35700 := hb (x (-5) 5 && x (-5) 14)
          clear * - r35693 b35694 b35695 b35696 b35697 b35698 b35699 b35700 f35679 g31 d34987 d35151 d35091 d35295
          omega
        have d35701 : (x (-4) 13).toNat = 1 := by
          have r35702 := hand2 (x (-4) 4) (x (-4) 13)
          have b35703 := hb (x (-4) 13)
          have b35704 := hb (x (-4) 4 && x (-4) 13)
          clear * - r35702 b35703 b35704 d35692
          omega
        have d35705 : (x (-4) 1).toNat = 1 := by
          have r35706 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b35707 := hb (x (-4) 1)
          have b35708 := hb (x (-4) 13)
          clear * - r35706 b35707 b35708 d35701
          omega
        have d35709 : (x (-3) 14).toNat = 0 := by
          have r35710 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b35711 := hb (x (-4) 1)
          have b35712 := hb (x (-3) 14)
          clear * - r35710 b35711 b35712 d35705
          omega
        have d35713 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
          have r35714 := hand2 (x (-3) 1) (x (-3) 14)
          have b35715 := hb (x (-3) 14)
          have b35716 := hb (x (-3) 1 && x (-3) 14)
          clear * - r35714 b35715 b35716 d35709
          omega
        have d35717 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
          have r35718 := hand2 (x (-3) 4) (x (-3) 14)
          have b35719 := hb (x (-3) 14)
          have b35720 := hb (x (-3) 4 && x (-3) 14)
          clear * - r35718 b35719 b35720 d35709
          omega
        have d35721 : (x (-4) 5).toNat = 1 := by
          have r35722 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b35723 := hb (x (-4) 5)
          have b35724 := hb (x 1 10)
          have b35725 := hb (x 0 1 && x 0 11)
          have b35726 := hb (x (-1) 2 && x (-1) 12)
          have b35727 := hb (x (-2) 3 && x (-2) 13)
          have b35728 := hb (x (-3) 4 && x (-3) 14)
          clear * - r35722 b35723 b35724 b35725 b35726 b35727 b35728 g8 d34818 d35024 d35040 d35717
          omega
        have d35729 : (x (-3) 2).toNat = 0 := by
          have r35730 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b35731 := hb (x (-3) 2)
          have b35732 := hb (x (-3) 14)
          clear * - r35730 b35731 b35732 d35709
          omega
        have d35733 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
          have r35734 := hand1 (x (-3) 2) (x (-3) 12)
          have b35735 := hb (x (-3) 2)
          have b35736 := hb (x (-3) 2 && x (-3) 12)
          clear * - r35734 b35735 b35736 d35729
          omega
        have d35737 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
          have r35738 := hand1 (x (-3) 2) (x (-3) 9)
          have b35739 := hb (x (-3) 2)
          have b35740 := hb (x (-3) 2 && x (-3) 9)
          clear * - r35738 b35739 b35740 d35729
          omega
        have d35741 : (x (-3) 10).toNat = 0 := by
          have r35742 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
          have b35743 := hb (x (-3) 2)
          have b35744 := hb (x (-3) 10)
          clear * - r35742 b35743 b35744 d35729
          omega
        have d35745 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
          have r35746 := hand2 (x (-3) 1) (x (-3) 10)
          have b35747 := hb (x (-3) 10)
          have b35748 := hb (x (-3) 1 && x (-3) 10)
          clear * - r35746 b35747 b35748 d35741
          omega
        have d35749 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
          have r35750 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b35751 := hb (x (-3) 2)
          have b35752 := hb (x (-1) 13)
          have b35753 := hb (x (-2) 1 && x (-2) 14)
          clear * - r35750 b35751 b35752 b35753 g3 d35729
          omega
        have d35754 : (x (-2) 14).toNat = 1 := by
          have r35755 := hand2 (x (-2) 1) (x (-2) 14)
          have b35756 := hb (x (-2) 14)
          have b35757 := hb (x (-2) 1 && x (-2) 14)
          clear * - r35755 b35756 b35757 d35749
          omega
        have d35758 : (x (-3) 1).toNat = 0 := by
          have r35759 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b35760 := hb (x (-3) 1)
          have b35761 := hb (x (-2) 14)
          clear * - r35759 b35760 b35761 d35754
          omega
        have d35762 : (x (-3) 13).toNat = 0 := by
          have r35763 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b35764 := hb (x (-3) 1)
          have b35765 := hb (x (-3) 13)
          clear * - r35763 b35764 b35765 d35758
          omega
        have d35766 : (x (-3) 9).toNat = 0 := by
          have r35767 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
          have b35768 := hb (x (-3) 1)
          have b35769 := hb (x (-3) 9)
          clear * - r35767 b35768 b35769 d35758
          omega
        have d35770 : (x (-3) 12).toNat = 0 := by
          have r35771 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e35772 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e35773 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b35774 := hb (x (-6) 3)
          have b35775 := hb (x (-5) 2)
          have b35776 := hb (x (-4) 13)
          have b35777 := hb (x (-3) 12)
          clear * - r35771 e35772 e35773 b35774 b35775 b35776 b35777 d35701
          omega
        have d35778 : (x (-3) 4).toNat = 0 := by
          have r35779 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b35780 := hb (x (-3) 4)
          have b35781 := hb (x (-3) 12)
          clear * - r35779 b35780 b35781 d35770
          omega
        have d35782 : (x (-5) 2).toNat = 0 := by
          have r35783 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e35784 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e35785 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b35786 := hb (x (-6) 3)
          have b35787 := hb (x (-5) 2)
          have b35788 := hb (x (-4) 13)
          have b35789 := hb (x (-3) 12)
          clear * - r35783 e35784 e35785 b35786 b35787 b35788 b35789 d35770 d35701
          omega
        have d35790 : (x (-5) 10).toNat = 0 := by
          have r35791 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
          have b35792 := hb (x (-5) 2)
          have b35793 := hb (x (-5) 10)
          clear * - r35791 b35792 b35793 d35782
          omega
        have d35794 : (x (-5) 1 && x (-5) 10).toNat = 0 := by
          have r35795 := hand2 (x (-5) 1) (x (-5) 10)
          have b35796 := hb (x (-5) 10)
          have b35797 := hb (x (-5) 1 && x (-5) 10)
          clear * - r35795 b35796 b35797 d35790
          omega
        have d35798 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
          have r35799 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b35800 := hb (x (-5) 2)
          have b35801 := hb (x (-3) 13)
          have b35802 := hb (x (-4) 1 && x (-4) 14)
          clear * - r35799 b35800 b35801 b35802 d35762 d35782
          omega
        have d35803 : (x (-4) 14).toNat = 1 := by
          have r35804 := hand2 (x (-4) 1) (x (-4) 14)
          have b35805 := hb (x (-4) 14)
          have b35806 := hb (x (-4) 1 && x (-4) 14)
          clear * - r35804 b35805 b35806 d35798
          omega
        have d35807 : (x (-5) 1).toNat = 0 := by
          have r35808 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b35809 := hb (x (-5) 1)
          have b35810 := hb (x (-4) 14)
          clear * - r35808 b35809 b35810 d35803
          omega
        have d35811 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
          have r35812 := hand1 (x (-5) 1) (x (-5) 12)
          have b35813 := hb (x (-5) 1)
          have b35814 := hb (x (-5) 1 && x (-5) 12)
          clear * - r35812 b35813 b35814 d35807
          omega
        have d35815 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
          have r35816 := hand1 (x (-5) 1) (x (-5) 11)
          have b35817 := hb (x (-5) 1)
          have b35818 := hb (x (-5) 1 && x (-5) 11)
          clear * - r35816 b35817 b35818 d35807
          omega
        have d35819 : (x (-5) 9).toNat = 0 := by
          have r35820 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
          have b35821 := hb (x (-5) 1)
          have b35822 := hb (x (-5) 9)
          clear * - r35820 b35821 b35822 d35807
          omega
        have d35823 : (x (-5) 9 && x (-5) 14).toNat = 0 := by
          have r35824 := hand1 (x (-5) 9) (x (-5) 14)
          have b35825 := hb (x (-5) 9)
          have b35826 := hb (x (-5) 9 && x (-5) 14)
          clear * - r35824 b35825 b35826 d35819
          omega
        have d35827 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
          have r35828 := hand2 (x (-5) 4) (x (-5) 9)
          have b35829 := hb (x (-5) 9)
          have b35830 := hb (x (-5) 4 && x (-5) 9)
          clear * - r35828 b35829 b35830 d35819
          omega
        have d35831 : (x (-6) 3).toNat = 0 := by
          have r35832 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e35833 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e35834 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b35835 := hb (x (-6) 3)
          have b35836 := hb (x (-5) 2)
          have b35837 := hb (x (-4) 13)
          have b35838 := hb (x (-3) 12)
          clear * - r35832 e35833 e35834 b35835 b35836 b35837 b35838 d35770 d35701 d35782
          omega
        have d35839 : (x (-6) 11).toNat = 0 := by
          have r35840 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
          have b35841 := hb (x (-6) 3)
          have b35842 := hb (x (-6) 11)
          clear * - r35840 b35841 b35842 d35831
          omega
        have d35843 : (x 1 8).toNat = 0 := by
          have r35844 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e35845 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e35846 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e35847 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e35848 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e35849 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e35850 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b35851 := hb (x (-6) 7)
          have b35852 := hb (x (-5) 6)
          have b35853 := hb (x (-4) 5)
          have b35854 := hb (x (-3) 4)
          have b35855 := hb (x (-2) 11)
          have b35856 := hb (x (-1) 10)
          have b35857 := hb (x 0 9)
          have b35858 := hb (x 1 8)
          clear * - r35844 e35845 e35846 e35847 e35848 e35849 e35850 b35851 b35852 b35853 b35854 b35855 b35856 b35857 b35858 f35679 d35028 d35044 d35778 d35721
          omega
        have d35859 : (x 1 3 && x 1 8).toNat = 0 := by
          have r35860 := hand2 (x 1 3) (x 1 8)
          have b35861 := hb (x 1 8)
          have b35862 := hb (x 1 3 && x 1 8)
          clear * - r35860 b35861 b35862 d35843
          omega
        cases h35863 : x 1 7
        · have f35864 : (x 1 7).toNat = 0 := by rw [h35863]; rfl
          cases h35865 : x (-1) 8
          · have f35866 : (x (-1) 8).toNat = 0 := by rw [h35865]; rfl
            have d35867 : (x 7 7).toNat = 1 := by
              have r35868 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b35869 := hb (x (-1) 8)
              have b35870 := hb (x 7 7)
              have b35871 := hb (x 6 1 && x 6 8)
              have b35872 := hb (x 5 2 && x 5 9)
              have b35873 := hb (x 4 3 && x 4 10)
              have b35874 := hb (x 3 4 && x 3 11)
              have b35875 := hb (x 2 5 && x 2 12)
              have b35876 := hb (x 1 6 && x 1 13)
              have b35877 := hb (x 0 7 && x 0 14)
              clear * - r35868 b35869 b35870 b35871 b35872 b35873 b35874 b35875 b35876 b35877 g25 g26 g27 g28 g29 d34902 g30 f35866
              omega
            have d35878 : (x 14 8).toNat = 0 := by
              have r35879 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e35880 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e35881 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e35882 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e35883 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e35884 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e35885 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b35886 := hb (x 7 7)
              have b35887 := hb (x 8 6)
              have b35888 := hb (x 9 5)
              have b35889 := hb (x 10 4)
              have b35890 := hb (x 11 11)
              have b35891 := hb (x 12 10)
              have b35892 := hb (x 13 9)
              have b35893 := hb (x 14 8)
              clear * - r35879 e35880 e35881 e35882 e35883 e35884 e35885 b35886 b35887 b35888 b35889 b35890 b35891 b35892 b35893 d35867
              omega
            have d35894 : (x 13 9).toNat = 0 := by
              have r35895 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e35896 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e35897 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e35898 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e35899 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e35900 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e35901 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b35902 := hb (x 7 7)
              have b35903 := hb (x 8 6)
              have b35904 := hb (x 9 5)
              have b35905 := hb (x 10 4)
              have b35906 := hb (x 11 11)
              have b35907 := hb (x 12 10)
              have b35908 := hb (x 13 9)
              have b35909 := hb (x 14 8)
              clear * - r35895 e35896 e35897 e35898 e35899 e35900 e35901 b35902 b35903 b35904 b35905 b35906 b35907 b35908 b35909 d35878 d35867
              omega
            have d35910 : (x 12 10).toNat = 0 := by
              have r35911 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e35912 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e35913 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e35914 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e35915 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e35916 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e35917 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b35918 := hb (x 7 7)
              have b35919 := hb (x 8 6)
              have b35920 := hb (x 9 5)
              have b35921 := hb (x 10 4)
              have b35922 := hb (x 11 11)
              have b35923 := hb (x 12 10)
              have b35924 := hb (x 13 9)
              have b35925 := hb (x 14 8)
              clear * - r35911 e35912 e35913 e35914 e35915 e35916 e35917 b35918 b35919 b35920 b35921 b35922 b35923 b35924 b35925 d35878 d35894 d35867
              omega
            have d35926 : (x 11 11).toNat = 0 := by
              have r35927 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e35928 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e35929 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e35930 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e35931 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e35932 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e35933 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b35934 := hb (x 7 7)
              have b35935 := hb (x 8 6)
              have b35936 := hb (x 9 5)
              have b35937 := hb (x 10 4)
              have b35938 := hb (x 11 11)
              have b35939 := hb (x 12 10)
              have b35940 := hb (x 13 9)
              have b35941 := hb (x 14 8)
              clear * - r35927 e35928 e35929 e35930 e35931 e35932 e35933 b35934 b35935 b35936 b35937 b35938 b35939 b35940 b35941 d35878 d35894 d35910 d35867
              omega
            have d35942 : (x 10 4).toNat = 0 := by
              have r35943 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e35944 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e35945 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e35946 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e35947 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e35948 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e35949 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b35950 := hb (x 7 7)
              have b35951 := hb (x 8 6)
              have b35952 := hb (x 9 5)
              have b35953 := hb (x 10 4)
              have b35954 := hb (x 11 11)
              have b35955 := hb (x 12 10)
              have b35956 := hb (x 13 9)
              have b35957 := hb (x 14 8)
              clear * - r35943 e35944 e35945 e35946 e35947 e35948 e35949 b35950 b35951 b35952 b35953 b35954 b35955 b35956 b35957 d35878 d35894 d35910 d35926 d35867
              omega
            have d35958 : (x 9 5).toNat = 0 := by
              have r35959 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e35960 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e35961 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e35962 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e35963 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e35964 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e35965 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b35966 := hb (x 7 7)
              have b35967 := hb (x 8 6)
              have b35968 := hb (x 9 5)
              have b35969 := hb (x 10 4)
              have b35970 := hb (x 11 11)
              have b35971 := hb (x 12 10)
              have b35972 := hb (x 13 9)
              have b35973 := hb (x 14 8)
              clear * - r35959 e35960 e35961 e35962 e35963 e35964 e35965 b35966 b35967 b35968 b35969 b35970 b35971 b35972 b35973 d35878 d35894 d35910 d35926 d35942 d35867
              omega
            have d35974 : (x 8 6).toNat = 0 := by
              have r35975 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e35976 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e35977 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e35978 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e35979 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e35980 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e35981 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b35982 := hb (x 7 7)
              have b35983 := hb (x 8 6)
              have b35984 := hb (x 9 5)
              have b35985 := hb (x 10 4)
              have b35986 := hb (x 11 11)
              have b35987 := hb (x 12 10)
              have b35988 := hb (x 13 9)
              have b35989 := hb (x 14 8)
              clear * - r35975 e35976 e35977 e35978 e35979 e35980 e35981 b35982 b35983 b35984 b35985 b35986 b35987 b35988 b35989 d35878 d35894 d35910 d35926 d35942 d35958 d35867
              omega
            have d35990 : (x 8 1 && x 8 6).toNat = 0 := by
              have r35991 := hand2 (x 8 1) (x 8 6)
              have b35992 := hb (x 8 6)
              have b35993 := hb (x 8 1 && x 8 6)
              clear * - r35991 b35992 b35993 d35974
              omega
            have d35994 : (x 7 1 && x 7 7).toNat = 1 := by
              have r35995 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b35996 := hb (x (-1) 9)
              have b35997 := hb (x 8 6)
              have b35998 := hb (x 7 1 && x 7 7)
              have b35999 := hb (x 6 2 && x 6 8)
              have b36000 := hb (x 5 3 && x 5 9)
              have b36001 := hb (x 4 4 && x 4 10)
              have b36002 := hb (x 3 5 && x 3 11)
              have b36003 := hb (x 2 6 && x 2 12)
              have b36004 := hb (x 1 7 && x 1 13)
              have b36005 := hb (x 0 8 && x 0 14)
              clear * - r35995 b35996 b35997 b35998 b35999 b36000 b36001 b36002 b36003 b36004 b36005 d35974 g19 g20 g21 g22 d34927 d34951 d35291 g2
              omega
            have d36006 : (x 7 1).toNat = 1 := by
              have r36007 := hand1 (x 7 1) (x 7 7)
              have b36008 := hb (x 7 1)
              have b36009 := hb (x 7 1 && x 7 7)
              clear * - r36007 b36008 b36009 d35994
              omega
            have d36010 : (x 7 2 && x 7 7).toNat = 1 := by
              have r36011 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36012 := hb (x (-1) 10)
              have b36013 := hb (x 9 5)
              have b36014 := hb (x 8 1 && x 8 6)
              have b36015 := hb (x 7 2 && x 7 7)
              have b36016 := hb (x 6 3 && x 6 8)
              have b36017 := hb (x 5 4 && x 5 9)
              have b36018 := hb (x 4 5 && x 4 10)
              have b36019 := hb (x 3 6 && x 3 11)
              have b36020 := hb (x 2 7 && x 2 12)
              have b36021 := hb (x 1 8 && x 1 13)
              have b36022 := hb (x 0 9 && x 0 14)
              clear * - r36011 b36012 b36013 b36014 b36015 b36016 b36017 b36018 b36019 b36020 b36021 b36022 d35958 d35990 g15 g16 g17 g18 d34931 d34955 d35680 d35028
              omega
            have d36023 : (x 7 2).toNat = 1 := by
              have r36024 := hand1 (x 7 2) (x 7 7)
              have b36025 := hb (x 7 2)
              have b36026 := hb (x 7 2 && x 7 7)
              clear * - r36024 b36025 b36026 d36010
              omega
            have d36027 : (x 7 14).toNat = 1 := by
              have r36028 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b36029 := hb (x 7 2)
              have b36030 := hb (x 7 14)
              clear * - r36028 b36029 b36030 d36023
              omega
            have d36031 : (x 6 1).toNat = 0 := by
              have r36032 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36033 := hb (x 6 1)
              have b36034 := hb (x 7 14)
              clear * - r36032 b36033 b36034 d36027
              omega
            have d36035 : (x 6 1 && x 6 14).toNat = 0 := by
              have r36036 := hand1 (x 6 1) (x 6 14)
              have b36037 := hb (x 6 1)
              have b36038 := hb (x 6 1 && x 6 14)
              clear * - r36036 b36037 b36038 d36031
              omega
            have d36039 : (x 6 1 && x 6 11).toNat = 0 := by
              have r36040 := hand1 (x 6 1) (x 6 11)
              have b36041 := hb (x 6 1)
              have b36042 := hb (x 6 1 && x 6 11)
              clear * - r36040 b36041 b36042 d36031
              omega
            have d36043 : (x 6 1 && x 6 10).toNat = 0 := by
              have r36044 := hand1 (x 6 1) (x 6 10)
              have b36045 := hb (x 6 1)
              have b36046 := hb (x 6 1 && x 6 10)
              clear * - r36044 b36045 b36046 d36031
              omega
            have d36047 : (x 6 13).toNat = 0 := by
              have r36048 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
              have b36049 := hb (x 6 1)
              have b36050 := hb (x 6 13)
              clear * - r36048 b36049 b36050 d36031
              omega
            have d36051 : (x 6 5).toNat = 0 := by
              have r36052 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
              have b36053 := hb (x 6 5)
              have b36054 := hb (x 6 13)
              clear * - r36052 b36053 b36054 d36047
              omega
            have d36055 : (x 9 12).toNat = 0 := by
              have r36056 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36057 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e36058 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b36059 := hb (x 6 3)
              have b36060 := hb (x 7 2)
              have b36061 := hb (x 8 13)
              have b36062 := hb (x 9 12)
              clear * - r36056 e36057 e36058 b36059 b36060 b36061 b36062 d36023
              omega
            have d36063 : (x 9 2 && x 9 12).toNat = 0 := by
              have r36064 := hand2 (x 9 2) (x 9 12)
              have b36065 := hb (x 9 12)
              have b36066 := hb (x 9 2 && x 9 12)
              clear * - r36064 b36065 b36066 d36055
              omega
            have d36067 : (x 9 4).toNat = 0 := by
              have r36068 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
              have b36069 := hb (x 9 4)
              have b36070 := hb (x 9 12)
              clear * - r36068 b36069 b36070 d36055
              omega
            have d36071 : (x 8 13).toNat = 0 := by
              have r36072 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36073 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e36074 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b36075 := hb (x 6 3)
              have b36076 := hb (x 7 2)
              have b36077 := hb (x 8 13)
              have b36078 := hb (x 9 12)
              clear * - r36072 e36073 e36074 b36075 b36076 b36077 b36078 d36055 d36023
              omega
            have d36079 : (x 8 3 && x 8 13).toNat = 0 := by
              have r36080 := hand2 (x 8 3) (x 8 13)
              have b36081 := hb (x 8 13)
              have b36082 := hb (x 8 3 && x 8 13)
              clear * - r36080 b36081 b36082 d36071
              omega
            have d36083 : (x 8 5).toNat = 0 := by
              have r36084 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
              have b36085 := hb (x 8 5)
              have b36086 := hb (x 8 13)
              clear * - r36084 b36085 b36086 d36071
              omega
            have d36087 : (x 6 3).toNat = 0 := by
              have r36088 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36089 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e36090 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b36091 := hb (x 6 3)
              have b36092 := hb (x 7 2)
              have b36093 := hb (x 8 13)
              have b36094 := hb (x 9 12)
              clear * - r36088 e36089 e36090 b36091 b36092 b36093 b36094 d36055 d36071 d36023
              omega
            have d36095 : (x 6 3 && x 6 7).toNat = 0 := by
              have r36096 := hand1 (x 6 3) (x 6 7)
              have b36097 := hb (x 6 3)
              have b36098 := hb (x 6 3 && x 6 7)
              clear * - r36096 b36097 b36098 d36087
              omega
            have d36099 : (x 6 11).toNat = 0 := by
              have r36100 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
              have b36101 := hb (x 6 3)
              have b36102 := hb (x 6 11)
              clear * - r36100 b36101 b36102 d36087
              omega
            have d36103 : (x 7 2 && x 7 6).toNat = 1 := by
              have r36104 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36105 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
              have e36106 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
              have b36107 := hb (x (-2) 11)
              have b36108 := hb (x (-1) 10)
              have b36109 := hb (x 8 5)
              have b36110 := hb (x 9 4)
              have b36111 := hb (x 7 2 && x 7 6)
              have b36112 := hb (x 6 3 && x 6 7)
              have b36113 := hb (x 5 4 && x 5 8)
              have b36114 := hb (x 4 5 && x 4 9)
              have b36115 := hb (x 3 6 && x 3 10)
              have b36116 := hb (x 2 7 && x 2 11)
              have b36117 := hb (x 1 8 && x 1 12)
              have b36118 := hb (x 0 9 && x 0 13)
              clear * - r36104 e36105 e36106 b36107 b36108 b36109 b36110 b36111 b36112 b36113 b36114 b36115 b36116 b36117 b36118 d36067 d36083 d36095 d35582 d35602 d35622 d35642 d35008 d35688 d35028 d35044
              omega
            have d36119 : (x 7 6).toNat = 1 := by
              have r36120 := hand2 (x 7 2) (x 7 6)
              have b36121 := hb (x 7 6)
              have b36122 := hb (x 7 2 && x 7 6)
              clear * - r36120 b36121 b36122 d36103
              omega
            have d36123 : (x 13 8).toNat = 0 := by
              have r36124 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36125 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
              have e36126 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
              have e36127 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
              have e36128 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
              have e36129 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
              have e36130 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
              have b36131 := hb (x 6 7)
              have b36132 := hb (x 7 6)
              have b36133 := hb (x 8 5)
              have b36134 := hb (x 9 4)
              have b36135 := hb (x 10 11)
              have b36136 := hb (x 11 10)
              have b36137 := hb (x 12 9)
              have b36138 := hb (x 13 8)
              clear * - r36124 e36125 e36126 e36127 e36128 e36129 e36130 b36131 b36132 b36133 b36134 b36135 b36136 b36137 b36138 d36067 d36083 d36119
              omega
            have d36139 : (x 12 9).toNat = 0 := by
              have r36140 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36141 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
              have e36142 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
              have e36143 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
              have e36144 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
              have e36145 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
              have e36146 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
              have b36147 := hb (x 6 7)
              have b36148 := hb (x 7 6)
              have b36149 := hb (x 8 5)
              have b36150 := hb (x 9 4)
              have b36151 := hb (x 10 11)
              have b36152 := hb (x 11 10)
              have b36153 := hb (x 12 9)
              have b36154 := hb (x 13 8)
              clear * - r36140 e36141 e36142 e36143 e36144 e36145 e36146 b36147 b36148 b36149 b36150 b36151 b36152 b36153 b36154 d36123 d36067 d36083 d36119
              omega
            have d36155 : (x 11 10).toNat = 0 := by
              have r36156 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36157 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
              have e36158 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
              have e36159 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
              have e36160 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
              have e36161 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
              have e36162 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
              have b36163 := hb (x 6 7)
              have b36164 := hb (x 7 6)
              have b36165 := hb (x 8 5)
              have b36166 := hb (x 9 4)
              have b36167 := hb (x 10 11)
              have b36168 := hb (x 11 10)
              have b36169 := hb (x 12 9)
              have b36170 := hb (x 13 8)
              clear * - r36156 e36157 e36158 e36159 e36160 e36161 e36162 b36163 b36164 b36165 b36166 b36167 b36168 b36169 b36170 d36123 d36139 d36067 d36083 d36119
              omega
            have d36171 : (x 10 11).toNat = 0 := by
              have r36172 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36173 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
              have e36174 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
              have e36175 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
              have e36176 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
              have e36177 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
              have e36178 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
              have b36179 := hb (x 6 7)
              have b36180 := hb (x 7 6)
              have b36181 := hb (x 8 5)
              have b36182 := hb (x 9 4)
              have b36183 := hb (x 10 11)
              have b36184 := hb (x 11 10)
              have b36185 := hb (x 12 9)
              have b36186 := hb (x 13 8)
              clear * - r36172 e36173 e36174 e36175 e36176 e36177 e36178 b36179 b36180 b36181 b36182 b36183 b36184 b36185 b36186 d36123 d36139 d36155 d36067 d36083 d36119
              omega
            have d36187 : (x 10 1 && x 10 11).toNat = 0 := by
              have r36188 := hand2 (x 10 1) (x 10 11)
              have b36189 := hb (x 10 11)
              have b36190 := hb (x 10 1 && x 10 11)
              clear * - r36188 b36189 b36190 d36171
              omega
            have d36191 : (x 7 4 && x 7 14).toNat = 1 := by
              have r36192 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36193 := hb (x 6 5)
              have b36194 := hb (x 11 10)
              have b36195 := hb (x 10 1 && x 10 11)
              have b36196 := hb (x 9 2 && x 9 12)
              have b36197 := hb (x 8 3 && x 8 13)
              have b36198 := hb (x 7 4 && x 7 14)
              clear * - r36192 b36193 b36194 b36195 b36196 b36197 b36198 d36155 d36187 d36063 d36079 d36051
              omega
            have d36199 : (x 7 4).toNat = 1 := by
              have r36200 := hand1 (x 7 4) (x 7 14)
              have b36201 := hb (x 7 4)
              have b36202 := hb (x 7 4 && x 7 14)
              clear * - r36200 b36201 b36202 d36191
              omega
            have d36203 : (x 7 12).toNat = 1 := by
              have r36204 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
              have b36205 := hb (x 7 4)
              have b36206 := hb (x 7 12)
              clear * - r36204 b36205 b36206 d36199
              omega
            have d36207 : (x 5 2).toNat = 0 := by
              have r36208 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36209 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e36210 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b36211 := hb (x 4 3)
              have b36212 := hb (x 5 2)
              have b36213 := hb (x 6 13)
              have b36214 := hb (x 7 12)
              clear * - r36208 e36209 e36210 b36211 b36212 b36213 b36214 d36203 d36047
              omega
            have d36215 : (x 5 2 && x 5 12).toNat = 0 := by
              have r36216 := hand1 (x 5 2) (x 5 12)
              have b36217 := hb (x 5 2)
              have b36218 := hb (x 5 2 && x 5 12)
              clear * - r36216 b36217 b36218 d36207
              omega
            have d36219 : (x 5 2 && x 5 11).toNat = 0 := by
              have r36220 := hand1 (x 5 2) (x 5 11)
              have b36221 := hb (x 5 2)
              have b36222 := hb (x 5 2 && x 5 11)
              clear * - r36220 b36221 b36222 d36207
              omega
            have d36223 : (x 7 13).toNat = 1 := by
              have r36224 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36225 := hb (x 5 2)
              have b36226 := hb (x 7 13)
              have b36227 := hb (x 6 1 && x 6 14)
              clear * - r36224 b36225 b36226 b36227 d36035 d36207
              omega
            have d36228 : (x 8 12).toNat = 0 := by
              have r36229 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36230 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e36231 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b36232 := hb (x 5 3)
              have b36233 := hb (x 6 2)
              have b36234 := hb (x 7 13)
              have b36235 := hb (x 8 12)
              clear * - r36229 e36230 e36231 b36232 b36233 b36234 b36235 d36223
              omega
            have d36236 : (x 6 2).toNat = 0 := by
              have r36237 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36238 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e36239 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b36240 := hb (x 5 3)
              have b36241 := hb (x 6 2)
              have b36242 := hb (x 7 13)
              have b36243 := hb (x 8 12)
              clear * - r36237 e36238 e36239 b36240 b36241 b36242 b36243 d36228 d36223
              omega
            have d36244 : (x 6 10).toNat = 0 := by
              have r36245 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
              have b36246 := hb (x 6 2)
              have b36247 := hb (x 6 10)
              clear * - r36245 b36246 b36247 d36236
              omega
            have d36248 : (x 5 3).toNat = 0 := by
              have r36249 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36250 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e36251 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b36252 := hb (x 5 3)
              have b36253 := hb (x 6 2)
              have b36254 := hb (x 7 13)
              have b36255 := hb (x 8 12)
              clear * - r36249 e36250 e36251 b36252 b36253 b36254 b36255 d36228 d36223 d36236
              omega
            have d36256 : (x 5 11).toNat = 0 := by
              have r36257 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have b36258 := hb (x 5 3)
              have b36259 := hb (x 5 11)
              clear * - r36257 b36258 b36259 d36248
              omega
            have d36260 : (x 5 1 && x 5 11).toNat = 0 := by
              have r36261 := hand2 (x 5 1) (x 5 11)
              have b36262 := hb (x 5 11)
              have b36263 := hb (x 5 1 && x 5 11)
              clear * - r36261 b36262 b36263 d36256
              omega
            have d36264 : (x 4 3).toNat = 0 := by
              have r36265 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36266 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e36267 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b36268 := hb (x 4 3)
              have b36269 := hb (x 5 2)
              have b36270 := hb (x 6 13)
              have b36271 := hb (x 7 12)
              clear * - r36265 e36266 e36267 b36268 b36269 b36270 b36271 d36203 d36047 d36207
              omega
            have d36272 : (x 4 3 && x 4 13).toNat = 0 := by
              have r36273 := hand1 (x 4 3) (x 4 13)
              have b36274 := hb (x 4 3)
              have b36275 := hb (x 4 3 && x 4 13)
              clear * - r36273 b36274 b36275 d36264
              omega
            have d36276 : (x 7 10).toNat = 1 := by
              have r36277 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36278 := hb (x 2 5)
              have b36279 := hb (x 7 10)
              have b36280 := hb (x 6 1 && x 6 11)
              have b36281 := hb (x 5 2 && x 5 12)
              have b36282 := hb (x 4 3 && x 4 13)
              have b36283 := hb (x 3 4 && x 3 14)
              clear * - r36277 b36278 b36279 b36280 b36281 b36282 b36283 d36039 d36215 d36272 g38 g10
              omega
            have d36284 : (x 9 8).toNat = 0 := by
              have r36285 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36286 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e36287 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e36288 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e36289 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e36290 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e36291 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b36292 := hb (x 2 7)
              have b36293 := hb (x 3 6)
              have b36294 := hb (x 4 5)
              have b36295 := hb (x 5 4)
              have b36296 := hb (x 6 11)
              have b36297 := hb (x 7 10)
              have b36298 := hb (x 8 9)
              have b36299 := hb (x 9 8)
              clear * - r36285 e36286 e36287 e36288 e36289 e36290 e36291 b36292 b36293 b36294 b36295 b36296 b36297 b36298 b36299 d36276 d36099
              omega
            have d36300 : (x 8 9).toNat = 0 := by
              have r36301 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36302 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e36303 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e36304 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e36305 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e36306 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e36307 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b36308 := hb (x 2 7)
              have b36309 := hb (x 3 6)
              have b36310 := hb (x 4 5)
              have b36311 := hb (x 5 4)
              have b36312 := hb (x 6 11)
              have b36313 := hb (x 7 10)
              have b36314 := hb (x 8 9)
              have b36315 := hb (x 9 8)
              clear * - r36301 e36302 e36303 e36304 e36305 e36306 e36307 b36308 b36309 b36310 b36311 b36312 b36313 b36314 b36315 d36284 d36276 d36099
              omega
            have d36316 : (x 5 4).toNat = 0 := by
              have r36317 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36318 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e36319 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e36320 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e36321 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e36322 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e36323 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b36324 := hb (x 2 7)
              have b36325 := hb (x 3 6)
              have b36326 := hb (x 4 5)
              have b36327 := hb (x 5 4)
              have b36328 := hb (x 6 11)
              have b36329 := hb (x 7 10)
              have b36330 := hb (x 8 9)
              have b36331 := hb (x 9 8)
              clear * - r36317 e36318 e36319 e36320 e36321 e36322 e36323 b36324 b36325 b36326 b36327 b36328 b36329 b36330 b36331 d36284 d36300 d36276 d36099
              omega
            have d36332 : (x 4 5).toNat = 0 := by
              have r36333 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36334 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e36335 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e36336 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e36337 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e36338 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e36339 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b36340 := hb (x 2 7)
              have b36341 := hb (x 3 6)
              have b36342 := hb (x 4 5)
              have b36343 := hb (x 5 4)
              have b36344 := hb (x 6 11)
              have b36345 := hb (x 7 10)
              have b36346 := hb (x 8 9)
              have b36347 := hb (x 9 8)
              clear * - r36333 e36334 e36335 e36336 e36337 e36338 e36339 b36340 b36341 b36342 b36343 b36344 b36345 b36346 b36347 d36284 d36300 d36276 d36099 d36316
              omega
            have d36348 : (x 3 6).toNat = 0 := by
              have r36349 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36350 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e36351 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e36352 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e36353 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e36354 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e36355 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b36356 := hb (x 2 7)
              have b36357 := hb (x 3 6)
              have b36358 := hb (x 4 5)
              have b36359 := hb (x 5 4)
              have b36360 := hb (x 6 11)
              have b36361 := hb (x 7 10)
              have b36362 := hb (x 8 9)
              have b36363 := hb (x 9 8)
              clear * - r36349 e36350 e36351 e36352 e36353 e36354 e36355 b36356 b36357 b36358 b36359 b36360 b36361 b36362 b36363 d36284 d36300 d36276 d36099 d36316 d36332
              omega
            have d36364 : (x 3 1 && x 3 6).toNat = 0 := by
              have r36365 := hand2 (x 3 1) (x 3 6)
              have b36366 := hb (x 3 6)
              have b36367 := hb (x 3 1 && x 3 6)
              clear * - r36365 b36366 b36367 d36348
              omega
            have d36368 : (x 2 7).toNat = 0 := by
              have r36369 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36370 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e36371 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e36372 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e36373 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e36374 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e36375 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b36376 := hb (x 2 7)
              have b36377 := hb (x 3 6)
              have b36378 := hb (x 4 5)
              have b36379 := hb (x 5 4)
              have b36380 := hb (x 6 11)
              have b36381 := hb (x 7 10)
              have b36382 := hb (x 8 9)
              have b36383 := hb (x 9 8)
              clear * - r36369 e36370 e36371 e36372 e36373 e36374 e36375 b36376 b36377 b36378 b36379 b36380 b36381 b36382 b36383 d36284 d36300 d36276 d36099 d36316 d36332 d36348
              omega
            have d36384 : (x 2 2 && x 2 7).toNat = 0 := by
              have r36385 := hand2 (x 2 2) (x 2 7)
              have b36386 := hb (x 2 7)
              have b36387 := hb (x 2 2 && x 2 7)
              clear * - r36385 b36386 b36387 d36368
              omega
            have d36388 : (x (-4) 8 && x (-4) 13).toNat = 1 := by
              have r36389 : 1 ≤ (x 4 5).toNat + (x 3 1 && x 3 6).toNat + (x 2 2 && x 2 7).toNat + (x 1 3 && x 1 8).toNat + (x 0 4 && x 0 9).toNat + (x (-1) 5 && x (-1) 10).toNat + (x (-2) 6 && x (-2) 11).toNat + (x (-3) 7 && x (-3) 12).toNat + (x (-4) 8 && x (-4) 13).toNat + (x (-5) 9 && x (-5) 14).toNat + (x (-6) 10).toNat := by have q := hcov5 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36390 := hb (x (-6) 10)
              have b36391 := hb (x 4 5)
              have b36392 := hb (x 3 1 && x 3 6)
              have b36393 := hb (x 2 2 && x 2 7)
              have b36394 := hb (x 1 3 && x 1 8)
              have b36395 := hb (x 0 4 && x 0 9)
              have b36396 := hb (x (-1) 5 && x (-1) 10)
              have b36397 := hb (x (-2) 6 && x (-2) 11)
              have b36398 := hb (x (-3) 7 && x (-3) 12)
              have b36399 := hb (x (-4) 8 && x (-4) 13)
              have b36400 := hb (x (-5) 9 && x (-5) 14)
              clear * - r36389 b36390 b36391 b36392 b36393 b36394 b36395 b36396 b36397 b36398 b36399 b36400 d36332 d36364 d36384 d35859 d35684 g14 d35052 d35267 d35823 d35115
              omega
            have d36401 : (x (-4) 8).toNat = 1 := by
              have r36402 := hand1 (x (-4) 8) (x (-4) 13)
              have b36403 := hb (x (-4) 8)
              have b36404 := hb (x (-4) 8 && x (-4) 13)
              clear * - r36402 b36403 b36404 d36388
              omega
            have d36405 : (x (-8) 4).toNat = 0 := by
              have r36406 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36407 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
              have e36408 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
              have e36409 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
              have e36410 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
              have e36411 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
              have e36412 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
              have b36413 := hb (x (-11) 7)
              have b36414 := hb (x (-10) 6)
              have b36415 := hb (x (-9) 5)
              have b36416 := hb (x (-8) 4)
              have b36417 := hb (x (-7) 11)
              have b36418 := hb (x (-6) 10)
              have b36419 := hb (x (-5) 9)
              have b36420 := hb (x (-4) 8)
              clear * - r36406 e36407 e36408 e36409 e36410 e36411 e36412 b36413 b36414 b36415 b36416 b36417 b36418 b36419 b36420 d36401 d35819 d35115 d35143
              omega
            have d36421 : (x (-8) 4 && x (-8) 14).toNat = 0 := by
              have r36422 := hand1 (x (-8) 4) (x (-8) 14)
              have b36423 := hb (x (-8) 4)
              have b36424 := hb (x (-8) 4 && x (-8) 14)
              clear * - r36422 b36423 b36424 d36405
              omega
            have d36425 : (x (-8) 4 && x (-8) 13).toNat = 0 := by
              have r36426 := hand1 (x (-8) 4) (x (-8) 13)
              have b36427 := hb (x (-8) 4)
              have b36428 := hb (x (-8) 4 && x (-8) 13)
              clear * - r36426 b36427 b36428 d36405
              omega
            have d36429 : (x (-4) 11).toNat = 1 := by
              have r36430 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36431 := hb (x (-8) 4)
              have b36432 := hb (x (-4) 11)
              have b36433 := hb (x (-5) 1 && x (-5) 12)
              have b36434 := hb (x (-6) 2 && x (-6) 13)
              have b36435 := hb (x (-7) 3 && x (-7) 14)
              clear * - r36430 b36431 b36432 b36433 b36434 b36435 d35811 d35103 d35131 d36405
              omega
            have d36436 : (x (-4) 3).toNat = 1 := by
              have r36437 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
              have b36438 := hb (x (-4) 3)
              have b36439 := hb (x (-4) 11)
              clear * - r36437 b36438 b36439 d36429
              omega
            have d36440 : (x (-1) 12).toNat = 0 := by
              have r36441 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36442 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e36443 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b36444 := hb (x (-4) 3)
              have b36445 := hb (x (-3) 2)
              have b36446 := hb (x (-2) 13)
              have b36447 := hb (x (-1) 12)
              clear * - r36441 e36442 e36443 b36444 b36445 b36446 b36447 d35729 d36436
              omega
            have d36448 : (x (-2) 13).toNat = 0 := by
              have r36449 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36450 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e36451 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b36452 := hb (x (-4) 3)
              have b36453 := hb (x (-3) 2)
              have b36454 := hb (x (-2) 13)
              have b36455 := hb (x (-1) 12)
              clear * - r36449 e36450 e36451 b36452 b36453 b36454 b36455 d36440 d35729 d36436
              omega
            have d36456 : (x (-4) 2).toNat = 1 := by
              have r36457 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36458 := hb (x (-4) 2)
              have b36459 := hb (x (-2) 13)
              have b36460 := hb (x (-3) 1 && x (-3) 14)
              clear * - r36457 b36458 b36459 b36460 d36448 d35713
              omega
            have d36461 : (x (-2) 12).toNat = 0 := by
              have r36462 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36463 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e36464 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b36465 := hb (x (-5) 3)
              have b36466 := hb (x (-4) 2)
              have b36467 := hb (x (-3) 13)
              have b36468 := hb (x (-2) 12)
              clear * - r36462 e36463 e36464 b36465 b36466 b36467 b36468 d35762 d36456
              omega
            have d36469 : (x (-5) 3).toNat = 0 := by
              have r36470 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36471 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e36472 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b36473 := hb (x (-5) 3)
              have b36474 := hb (x (-4) 2)
              have b36475 := hb (x (-3) 13)
              have b36476 := hb (x (-2) 12)
              clear * - r36470 e36471 e36472 b36473 b36474 b36475 b36476 d36461 d35762 d36456
              omega
            have d36477 : (x (-5) 11).toNat = 0 := by
              have r36478 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
              have b36479 := hb (x (-5) 3)
              have b36480 := hb (x (-5) 11)
              clear * - r36478 b36479 b36480 d36469
              omega
            have d36481 : (x (-9) 5).toNat = 0 := by
              have r36482 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36483 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
              have e36484 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
              have e36485 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
              have e36486 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
              have e36487 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
              have e36488 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
              have b36489 := hb (x (-11) 7)
              have b36490 := hb (x (-10) 6)
              have b36491 := hb (x (-9) 5)
              have b36492 := hb (x (-8) 4)
              have b36493 := hb (x (-7) 11)
              have b36494 := hb (x (-6) 10)
              have b36495 := hb (x (-5) 9)
              have b36496 := hb (x (-4) 8)
              clear * - r36482 e36483 e36484 e36485 e36486 e36487 e36488 b36489 b36490 b36491 b36492 b36493 b36494 b36495 b36496 d36401 d35819 d35115 d35143 d36405
              omega
            have d36497 : (x (-9) 5 && x (-9) 14).toNat = 0 := by
              have r36498 := hand1 (x (-9) 5) (x (-9) 14)
              have b36499 := hb (x (-9) 5)
              have b36500 := hb (x (-9) 5 && x (-9) 14)
              clear * - r36498 b36499 b36500 d36481
              omega
            have d36501 : (x (-4) 10).toNat = 1 := by
              have r36502 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36503 := hb (x (-9) 5)
              have b36504 := hb (x (-4) 10)
              have b36505 := hb (x (-5) 1 && x (-5) 11)
              have b36506 := hb (x (-6) 2 && x (-6) 12)
              have b36507 := hb (x (-7) 3 && x (-7) 13)
              have b36508 := hb (x (-8) 4 && x (-8) 14)
              clear * - r36502 b36503 b36504 b36505 b36506 b36507 b36508 d35815 d35107 d35135 d36421 d36481
              omega
            have d36509 : (x (-2) 8).toNat = 0 := by
              have r36510 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36511 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e36512 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e36513 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e36514 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e36515 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e36516 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have b36517 := hb (x (-9) 7)
              have b36518 := hb (x (-8) 6)
              have b36519 := hb (x (-7) 5)
              have b36520 := hb (x (-6) 4)
              have b36521 := hb (x (-5) 11)
              have b36522 := hb (x (-4) 10)
              have b36523 := hb (x (-3) 9)
              have b36524 := hb (x (-2) 8)
              clear * - r36510 e36511 e36512 e36513 e36514 e36515 e36516 b36517 b36518 b36519 b36520 b36521 b36522 b36523 b36524 d35766 d36501 d36477
              omega
            have d36525 : (x (-10) 6).toNat = 0 := by
              have r36526 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36527 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
              have e36528 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
              have e36529 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
              have e36530 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
              have e36531 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
              have e36532 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
              have b36533 := hb (x (-11) 7)
              have b36534 := hb (x (-10) 6)
              have b36535 := hb (x (-9) 5)
              have b36536 := hb (x (-8) 4)
              have b36537 := hb (x (-7) 11)
              have b36538 := hb (x (-6) 10)
              have b36539 := hb (x (-5) 9)
              have b36540 := hb (x (-4) 8)
              clear * - r36526 e36527 e36528 e36529 e36530 e36531 e36532 b36533 b36534 b36535 b36536 b36537 b36538 b36539 b36540 d36401 d35819 d35115 d35143 d36405 d36481
              omega
            have d36541 : (x (-4) 9).toNat = 1 := by
              have r36542 : 1 ≤ (x (-4) 9).toNat + (x (-5) 1 && x (-5) 10).toNat + (x (-6) 2 && x (-6) 11).toNat + (x (-7) 3 && x (-7) 12).toNat + (x (-8) 4 && x (-8) 13).toNat + (x (-9) 5 && x (-9) 14).toNat + (x (-10) 6).toNat := by have q := hcov9 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36543 := hb (x (-10) 6)
              have b36544 := hb (x (-4) 9)
              have b36545 := hb (x (-5) 1 && x (-5) 10)
              have b36546 := hb (x (-6) 2 && x (-6) 11)
              have b36547 := hb (x (-7) 3 && x (-7) 12)
              have b36548 := hb (x (-8) 4 && x (-8) 13)
              have b36549 := hb (x (-9) 5 && x (-9) 14)
              clear * - r36542 b36543 b36544 b36545 b36546 b36547 b36548 b36549 d35794 d35111 d35139 d36425 d36497 d36525
              omega
            have d36550 : (x (-3) 8).toNat = 0 := by
              have r36551 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36552 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
              have e36553 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
              have e36554 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
              have e36555 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
              have e36556 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
              have e36557 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
              have b36558 := hb (x (-10) 7)
              have b36559 := hb (x (-9) 6)
              have b36560 := hb (x (-8) 5)
              have b36561 := hb (x (-7) 4)
              have b36562 := hb (x (-6) 11)
              have b36563 := hb (x (-5) 10)
              have b36564 := hb (x (-4) 9)
              have b36565 := hb (x (-3) 8)
              clear * - r36551 e36552 e36553 e36554 e36555 e36556 e36557 b36558 b36559 b36560 b36561 b36562 b36563 b36564 b36565 d36541 d35790 d35839
              omega
            have d36566 : (x 4 3 && x 4 12).toNat = 0 := by
              have r36567 := hand1 (x 4 3) (x 4 12)
              have b36568 := hb (x 4 3)
              have b36569 := hb (x 4 3 && x 4 12)
              clear * - r36567 b36568 b36569 d36264
              omega
            have d36570 : (x 7 9).toNat = 1 := by
              have r36571 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36572 := hb (x 1 6)
              have b36573 := hb (x 7 9)
              have b36574 := hb (x 6 1 && x 6 10)
              have b36575 := hb (x 5 2 && x 5 11)
              have b36576 := hb (x 4 3 && x 4 12)
              have b36577 := hb (x 3 4 && x 3 13)
              have b36578 := hb (x 2 5 && x 2 14)
              clear * - r36571 b36572 b36573 b36574 b36575 b36576 b36577 b36578 d36043 d36219 d36566 g34 g35 d34898
              omega
            have d36579 : (x 8 8).toNat = 0 := by
              have r36580 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36581 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e36582 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e36583 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e36584 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e36585 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e36586 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b36587 := hb (x 1 7)
              have b36588 := hb (x 2 6)
              have b36589 := hb (x 3 5)
              have b36590 := hb (x 4 4)
              have b36591 := hb (x 5 11)
              have b36592 := hb (x 6 10)
              have b36593 := hb (x 7 9)
              have b36594 := hb (x 8 8)
              clear * - r36580 e36581 e36582 e36583 e36584 e36585 e36586 b36587 b36588 b36589 b36590 b36591 b36592 b36593 b36594 d36570 d36244 d36256 f35864
              omega
            have d36595 : (x 4 4).toNat = 0 := by
              have r36596 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36597 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e36598 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e36599 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e36600 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e36601 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e36602 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b36603 := hb (x 1 7)
              have b36604 := hb (x 2 6)
              have b36605 := hb (x 3 5)
              have b36606 := hb (x 4 4)
              have b36607 := hb (x 5 11)
              have b36608 := hb (x 6 10)
              have b36609 := hb (x 7 9)
              have b36610 := hb (x 8 8)
              clear * - r36596 e36597 e36598 e36599 e36600 e36601 e36602 b36603 b36604 b36605 b36606 b36607 b36608 b36609 b36610 d36579 d36570 d36244 d36256 f35864
              omega
            have d36611 : (x 3 5).toNat = 0 := by
              have r36612 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36613 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e36614 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e36615 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e36616 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e36617 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e36618 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b36619 := hb (x 1 7)
              have b36620 := hb (x 2 6)
              have b36621 := hb (x 3 5)
              have b36622 := hb (x 4 4)
              have b36623 := hb (x 5 11)
              have b36624 := hb (x 6 10)
              have b36625 := hb (x 7 9)
              have b36626 := hb (x 8 8)
              clear * - r36612 e36613 e36614 e36615 e36616 e36617 e36618 b36619 b36620 b36621 b36622 b36623 b36624 b36625 b36626 d36579 d36570 d36244 d36256 d36595 f35864
              omega
            have d36627 : (x 2 6).toNat = 0 := by
              have r36628 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36629 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e36630 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e36631 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e36632 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e36633 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e36634 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b36635 := hb (x 1 7)
              have b36636 := hb (x 2 6)
              have b36637 := hb (x 3 5)
              have b36638 := hb (x 4 4)
              have b36639 := hb (x 5 11)
              have b36640 := hb (x 6 10)
              have b36641 := hb (x 7 9)
              have b36642 := hb (x 8 8)
              clear * - r36628 e36629 e36630 e36631 e36632 e36633 e36634 b36635 b36636 b36637 b36638 b36639 b36640 b36641 b36642 d36579 d36570 d36244 d36256 d36595 d36611 f35864
              omega
            have d36643 : (x (-6) 14).toNat = 1 := by
              have r36644 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36645 := hb (x (-6) 14)
              have b36646 := hb (x (-5) 13)
              have b36647 := hb (x (-4) 12)
              have b36648 := hb (x (-3) 11)
              have b36649 := hb (x (-2) 10)
              have b36650 := hb (x (-1) 9)
              have b36651 := hb (x 0 8)
              have b36652 := hb (x 1 7)
              have b36653 := hb (x 2 6)
              have b36654 := hb (x 3 5)
              have b36655 := hb (x 4 4)
              have b36656 := hb (x 5 3)
              have b36657 := hb (x 6 2)
              have b36658 := hb (x 7 1)
              clear * - r36644 b36645 b36646 b36647 b36648 b36649 b36650 b36651 b36652 b36653 b36654 b36655 b36656 b36657 b36658 d36006 d36236 d36248 d36595 d36611 d36627 f35864 d35275 g2 d34991 d35155 d35075 d35079
              omega
            have d36659 : (x (-7) 1).toNat = 0 := by
              have r36660 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36661 := hb (x (-7) 1)
              have b36662 := hb (x (-6) 14)
              clear * - r36660 b36661 b36662 d36643
              omega
            have d36663 : (x (-7) 13).toNat = 0 := by
              have r36664 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
              have b36665 := hb (x (-7) 1)
              have b36666 := hb (x (-7) 13)
              clear * - r36664 b36665 b36666 d36659
              omega
            have r36667 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r36668 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r36669 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r36670 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r36671 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r36672 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
            have r36673 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
            have r36674 := hand1 (x 4 2) (x 4 12)
            have r36675 := hand1 (x 3 3) (x 3 13)
            have r36676 := hand2 (x (-8) 1) (x (-8) 14)
            have r36677 := hand1 (x 4 1) (x 4 14)
            linarith only [r36667, r36668, r36669, r36670, r36671, r36672, r36673, r36674, r36675, r36676, r36677, d36663, d35839, d35790, d36477, d36541, d36501, d36550, d35766, d35662, d36509, d35646, g1, f35561, g4, d35012, g7, g9, d36244, d36260, g37]
          · have f36715 : (x (-1) 8).toNat = 1 := by rw [h35865]; rfl
            have d36716 : (x (-2) 9).toNat = 0 := by
              have r36717 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36718 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e36719 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e36720 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e36721 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e36722 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e36723 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b36724 := hb (x (-8) 7)
              have b36725 := hb (x (-7) 6)
              have b36726 := hb (x (-6) 5)
              have b36727 := hb (x (-5) 4)
              have b36728 := hb (x (-4) 11)
              have b36729 := hb (x (-3) 10)
              have b36730 := hb (x (-2) 9)
              have b36731 := hb (x (-1) 8)
              clear * - r36717 e36718 e36719 e36720 e36721 e36722 e36723 b36724 b36725 b36726 b36727 b36728 b36729 b36730 b36731 f36715 d35741
              omega
            have d36732 : (x (-4) 11).toNat = 0 := by
              have r36733 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36734 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e36735 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e36736 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e36737 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e36738 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e36739 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b36740 := hb (x (-8) 7)
              have b36741 := hb (x (-7) 6)
              have b36742 := hb (x (-6) 5)
              have b36743 := hb (x (-5) 4)
              have b36744 := hb (x (-4) 11)
              have b36745 := hb (x (-3) 10)
              have b36746 := hb (x (-2) 9)
              have b36747 := hb (x (-1) 8)
              clear * - r36733 e36734 e36735 e36736 e36737 e36738 e36739 b36740 b36741 b36742 b36743 b36744 b36745 b36746 b36747 f36715 d36716 d35741
              omega
            have d36748 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
              have r36749 := hand2 (x (-4) 2) (x (-4) 11)
              have b36750 := hb (x (-4) 11)
              have b36751 := hb (x (-4) 2 && x (-4) 11)
              clear * - r36749 b36750 b36751 d36732
              omega
            have d36752 : (x (-8) 4).toNat = 1 := by
              have r36753 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36754 := hb (x (-8) 4)
              have b36755 := hb (x (-4) 11)
              have b36756 := hb (x (-5) 1 && x (-5) 12)
              have b36757 := hb (x (-6) 2 && x (-6) 13)
              have b36758 := hb (x (-7) 3 && x (-7) 14)
              clear * - r36753 b36754 b36755 b36756 b36757 b36758 d36732 d35811 d35103 d35131
              omega
            have d36759 : (x (-8) 12).toNat = 1 := by
              have r36760 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
              have b36761 := hb (x (-8) 4)
              have b36762 := hb (x (-8) 12)
              clear * - r36760 b36761 b36762 d36752
              omega
            have d36763 : (x (-9) 13).toNat = 0 := by
              have r36764 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36765 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e36766 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b36767 := hb (x (-11) 3)
              have b36768 := hb (x (-10) 2)
              have b36769 := hb (x (-9) 13)
              have b36770 := hb (x (-8) 12)
              clear * - r36764 e36765 e36766 b36767 b36768 b36769 b36770 d36759
              omega
            have d36771 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
              have r36772 := hand2 (x (-9) 8) (x (-9) 13)
              have b36773 := hb (x (-9) 13)
              have b36774 := hb (x (-9) 8 && x (-9) 13)
              clear * - r36772 b36773 b36774 d36763
              omega
            have d36775 : (x (-9) 5).toNat = 0 := by
              have r36776 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
              have b36777 := hb (x (-9) 5)
              have b36778 := hb (x (-9) 13)
              clear * - r36776 b36777 b36778 d36763
              omega
            have d36779 : (x (-5) 4).toNat = 0 := by
              have r36780 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36781 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e36782 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e36783 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e36784 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e36785 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e36786 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b36787 := hb (x (-8) 7)
              have b36788 := hb (x (-7) 6)
              have b36789 := hb (x (-6) 5)
              have b36790 := hb (x (-5) 4)
              have b36791 := hb (x (-4) 11)
              have b36792 := hb (x (-3) 10)
              have b36793 := hb (x (-2) 9)
              have b36794 := hb (x (-1) 8)
              clear * - r36780 e36781 e36782 e36783 e36784 e36785 e36786 b36787 b36788 b36789 b36790 b36791 b36792 b36793 b36794 f36715 d36716 d35741 d36732
              omega
            have d36795 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
              have r36796 := hand1 (x (-5) 4) (x (-5) 14)
              have b36797 := hb (x (-5) 4)
              have b36798 := hb (x (-5) 4 && x (-5) 14)
              clear * - r36796 b36797 b36798 d36779
              omega
            have d36799 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
              have r36800 := hand1 (x (-5) 4) (x (-5) 11)
              have b36801 := hb (x (-5) 4)
              have b36802 := hb (x (-5) 4 && x (-5) 11)
              clear * - r36800 b36801 b36802 d36779
              omega
            have d36803 : (x (-6) 5).toNat = 0 := by
              have r36804 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36805 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e36806 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e36807 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e36808 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e36809 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e36810 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b36811 := hb (x (-8) 7)
              have b36812 := hb (x (-7) 6)
              have b36813 := hb (x (-6) 5)
              have b36814 := hb (x (-5) 4)
              have b36815 := hb (x (-4) 11)
              have b36816 := hb (x (-3) 10)
              have b36817 := hb (x (-2) 9)
              have b36818 := hb (x (-1) 8)
              clear * - r36804 e36805 e36806 e36807 e36808 e36809 e36810 b36811 b36812 b36813 b36814 b36815 b36816 b36817 b36818 f36715 d36716 d35741 d36732 d36779
              omega
            have d36819 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
              have r36820 := hand1 (x (-6) 5) (x (-6) 12)
              have b36821 := hb (x (-6) 5)
              have b36822 := hb (x (-6) 5 && x (-6) 12)
              clear * - r36820 b36821 b36822 d36803
              omega
            have d36823 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
              have r36824 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36825 := hb (x (-6) 5)
              have b36826 := hb (x (-1) 10)
              have b36827 := hb (x (-2) 1 && x (-2) 11)
              have b36828 := hb (x (-3) 2 && x (-3) 12)
              have b36829 := hb (x (-4) 3 && x (-4) 13)
              have b36830 := hb (x (-5) 4 && x (-5) 14)
              clear * - r36824 b36825 b36826 b36827 b36828 b36829 b36830 d35028 d35048 d35733 d36795 d36803
              omega
            have d36831 : (x (-4) 3).toNat = 1 := by
              have r36832 := hand1 (x (-4) 3) (x (-4) 13)
              have b36833 := hb (x (-4) 3)
              have b36834 := hb (x (-4) 3 && x (-4) 13)
              clear * - r36832 b36833 b36834 d36823
              omega
            have d36835 : (x (-1) 12).toNat = 0 := by
              have r36836 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36837 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e36838 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b36839 := hb (x (-4) 3)
              have b36840 := hb (x (-3) 2)
              have b36841 := hb (x (-2) 13)
              have b36842 := hb (x (-1) 12)
              clear * - r36836 e36837 e36838 b36839 b36840 b36841 b36842 d35729 d36831
              omega
            have d36843 : (x (-2) 13).toNat = 0 := by
              have r36844 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36845 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e36846 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b36847 := hb (x (-4) 3)
              have b36848 := hb (x (-3) 2)
              have b36849 := hb (x (-2) 13)
              have b36850 := hb (x (-1) 12)
              clear * - r36844 e36845 e36846 b36847 b36848 b36849 b36850 d36835 d35729 d36831
              omega
            have d36851 : (x (-4) 2).toNat = 1 := by
              have r36852 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b36853 := hb (x (-4) 2)
              have b36854 := hb (x (-2) 13)
              have b36855 := hb (x (-3) 1 && x (-3) 14)
              clear * - r36852 b36853 b36854 b36855 d36843 d35713
              omega
            have d36856 : (x (-2) 12).toNat = 0 := by
              have r36857 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36858 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e36859 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b36860 := hb (x (-5) 3)
              have b36861 := hb (x (-4) 2)
              have b36862 := hb (x (-3) 13)
              have b36863 := hb (x (-2) 12)
              clear * - r36857 e36858 e36859 b36860 b36861 b36862 b36863 d35762 d36851
              omega
            have d36864 : (x (-5) 3).toNat = 0 := by
              have r36865 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36866 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e36867 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b36868 := hb (x (-5) 3)
              have b36869 := hb (x (-4) 2)
              have b36870 := hb (x (-3) 13)
              have b36871 := hb (x (-2) 12)
              clear * - r36865 e36866 e36867 b36868 b36869 b36870 b36871 d36856 d35762 d36851
              omega
            have d36872 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
              have r36873 := hand1 (x (-5) 3) (x (-5) 12)
              have b36874 := hb (x (-5) 3)
              have b36875 := hb (x (-5) 3 && x (-5) 12)
              clear * - r36873 b36874 b36875 d36864
              omega
            have d36876 : (x (-5) 11).toNat = 0 := by
              have r36877 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
              have b36878 := hb (x (-5) 3)
              have b36879 := hb (x (-5) 11)
              clear * - r36877 b36878 b36879 d36864
              omega
            have d36880 : (x (-7) 6).toNat = 0 := by
              have r36881 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36882 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e36883 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e36884 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e36885 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e36886 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e36887 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b36888 := hb (x (-8) 7)
              have b36889 := hb (x (-7) 6)
              have b36890 := hb (x (-6) 5)
              have b36891 := hb (x (-5) 4)
              have b36892 := hb (x (-4) 11)
              have b36893 := hb (x (-3) 10)
              have b36894 := hb (x (-2) 9)
              have b36895 := hb (x (-1) 8)
              clear * - r36881 e36882 e36883 e36884 e36885 e36886 e36887 b36888 b36889 b36890 b36891 b36892 b36893 b36894 b36895 f36715 d36716 d35741 d36732 d36779 d36803
              omega
            have d36896 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
              have r36897 := hand1 (x (-7) 6) (x (-7) 13)
              have b36898 := hb (x (-7) 6)
              have b36899 := hb (x (-7) 6 && x (-7) 13)
              clear * - r36897 b36898 b36899 d36880
              omega
            have d36900 : (x (-8) 7).toNat = 0 := by
              have r36901 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36902 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e36903 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e36904 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e36905 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e36906 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e36907 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b36908 := hb (x (-8) 7)
              have b36909 := hb (x (-7) 6)
              have b36910 := hb (x (-6) 5)
              have b36911 := hb (x (-5) 4)
              have b36912 := hb (x (-4) 11)
              have b36913 := hb (x (-3) 10)
              have b36914 := hb (x (-2) 9)
              have b36915 := hb (x (-1) 8)
              clear * - r36901 e36902 e36903 e36904 e36905 e36906 e36907 b36908 b36909 b36910 b36911 b36912 b36913 b36914 b36915 f36715 d36716 d35741 d36732 d36779 d36803 d36880
              omega
            have d36916 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
              have r36917 := hand1 (x (-8) 7) (x (-8) 14)
              have b36918 := hb (x (-8) 7)
              have b36919 := hb (x (-8) 7 && x (-8) 14)
              clear * - r36917 b36918 b36919 d36900
              omega
            have d36920 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
              have r36921 := hand1 (x (-8) 7) (x (-8) 12)
              have b36922 := hb (x (-8) 7)
              have b36923 := hb (x (-8) 7 && x (-8) 12)
              clear * - r36921 b36922 b36923 d36900
              omega
            have d36924 : (x (-4) 8).toNat = 0 := by
              have r36925 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e36926 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
              have e36927 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
              have e36928 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
              have e36929 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
              have e36930 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
              have e36931 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
              have b36932 := hb (x (-11) 7)
              have b36933 := hb (x (-10) 6)
              have b36934 := hb (x (-9) 5)
              have b36935 := hb (x (-8) 4)
              have b36936 := hb (x (-7) 11)
              have b36937 := hb (x (-6) 10)
              have b36938 := hb (x (-5) 9)
              have b36939 := hb (x (-4) 8)
              clear * - r36925 e36926 e36927 e36928 e36929 e36930 e36931 b36932 b36933 b36934 b36935 b36936 b36937 b36938 b36939 d35819 d35115 d35143 d36752 d36775
              omega
            have d36940 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
              have r36941 := hand2 (x (-4) 3) (x (-4) 8)
              have b36942 := hb (x (-4) 8)
              have b36943 := hb (x (-4) 3 && x (-4) 8)
              clear * - r36941 b36942 b36943 d36924
              omega
            have r36944 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e36945 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
            have e36946 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
            have e36947 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
            have e36948 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
            have e36949 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
            have e36950 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
            have r36951 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e36952 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e36953 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e36954 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e36955 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e36956 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e36957 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have r36958 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r36959 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r36960 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r36961 := hand1 (x (-10) 9) (x (-10) 14)
            have r36962 := hand2 (x (-2) 1) (x (-2) 8)
            have r36963 := hand2 (x (-4) 3) (x (-4) 10)
            have r36964 := hand1 (x (-6) 4) (x (-6) 13)
            have r36965 := hand1 (x (-7) 5) (x (-7) 14)
            linarith only [r36944, e36945, e36946, e36947, e36948, e36949, e36950, r36951, e36952, e36953, e36954, e36955, e36956, e36957, r36958, r36959, r36960, r36961, r36962, r36963, r36964, r36965, d36876, d35766, d36716, g0, g1, d35243, d35271, d36940, d35827, d35119, d35147, d36920, d36771, d35737, d36799, d36819, d36896, d36916, d35745, d36748, d36872]
        · have f37006 : (x 1 7).toNat = 1 := by rw [h35863]; rfl
          have d37007 : (x 8 8).toNat = 0 := by
            have r37008 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37009 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e37010 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e37011 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e37012 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e37013 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e37014 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b37015 := hb (x 1 7)
            have b37016 := hb (x 2 6)
            have b37017 := hb (x 3 5)
            have b37018 := hb (x 4 4)
            have b37019 := hb (x 5 11)
            have b37020 := hb (x 6 10)
            have b37021 := hb (x 7 9)
            have b37022 := hb (x 8 8)
            clear * - r37008 e37009 e37010 e37011 e37012 e37013 e37014 b37015 b37016 b37017 b37018 b37019 b37020 b37021 b37022 f37006
            omega
          have d37023 : (x 7 9).toNat = 0 := by
            have r37024 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37025 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e37026 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e37027 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e37028 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e37029 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e37030 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b37031 := hb (x 1 7)
            have b37032 := hb (x 2 6)
            have b37033 := hb (x 3 5)
            have b37034 := hb (x 4 4)
            have b37035 := hb (x 5 11)
            have b37036 := hb (x 6 10)
            have b37037 := hb (x 7 9)
            have b37038 := hb (x 8 8)
            clear * - r37024 e37025 e37026 e37027 e37028 e37029 e37030 b37031 b37032 b37033 b37034 b37035 b37036 b37037 b37038 d37007 f37006
            omega
          have d37039 : (x 6 10).toNat = 0 := by
            have r37040 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37041 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e37042 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e37043 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e37044 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e37045 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e37046 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b37047 := hb (x 1 7)
            have b37048 := hb (x 2 6)
            have b37049 := hb (x 3 5)
            have b37050 := hb (x 4 4)
            have b37051 := hb (x 5 11)
            have b37052 := hb (x 6 10)
            have b37053 := hb (x 7 9)
            have b37054 := hb (x 8 8)
            clear * - r37040 e37041 e37042 e37043 e37044 e37045 e37046 b37047 b37048 b37049 b37050 b37051 b37052 b37053 b37054 d37007 d37023 f37006
            omega
          have d37055 : (x 6 1 && x 6 10).toNat = 0 := by
            have r37056 := hand2 (x 6 1) (x 6 10)
            have b37057 := hb (x 6 10)
            have b37058 := hb (x 6 1 && x 6 10)
            clear * - r37056 b37057 b37058 d37039
            omega
          have d37059 : (x 5 11).toNat = 0 := by
            have r37060 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37061 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e37062 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e37063 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e37064 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e37065 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e37066 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b37067 := hb (x 1 7)
            have b37068 := hb (x 2 6)
            have b37069 := hb (x 3 5)
            have b37070 := hb (x 4 4)
            have b37071 := hb (x 5 11)
            have b37072 := hb (x 6 10)
            have b37073 := hb (x 7 9)
            have b37074 := hb (x 8 8)
            clear * - r37060 e37061 e37062 e37063 e37064 e37065 e37066 b37067 b37068 b37069 b37070 b37071 b37072 b37073 b37074 d37007 d37023 d37039 f37006
            omega
          have d37075 : (x 5 1 && x 5 11).toNat = 0 := by
            have r37076 := hand2 (x 5 1) (x 5 11)
            have b37077 := hb (x 5 11)
            have b37078 := hb (x 5 1 && x 5 11)
            clear * - r37076 b37077 b37078 d37059
            omega
          have d37079 : (x 5 2 && x 5 11).toNat = 0 := by
            have r37080 := hand2 (x 5 2) (x 5 11)
            have b37081 := hb (x 5 11)
            have b37082 := hb (x 5 2 && x 5 11)
            clear * - r37080 b37081 b37082 d37059
            omega
          have d37083 : (x 4 3 && x 4 12).toNat = 1 := by
            have r37084 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37085 := hb (x 1 6)
            have b37086 := hb (x 7 9)
            have b37087 := hb (x 6 1 && x 6 10)
            have b37088 := hb (x 5 2 && x 5 11)
            have b37089 := hb (x 4 3 && x 4 12)
            have b37090 := hb (x 3 4 && x 3 13)
            have b37091 := hb (x 2 5 && x 2 14)
            clear * - r37084 b37085 b37086 b37087 b37088 b37089 b37090 b37091 d37023 d37055 d37079 g34 g35 d34898
            omega
          have d37092 : (x 4 12).toNat = 1 := by
            have r37093 := hand2 (x 4 3) (x 4 12)
            have b37094 := hb (x 4 12)
            have b37095 := hb (x 4 3 && x 4 12)
            clear * - r37093 b37094 b37095 d37083
            omega
          have d37096 : (x 3 13).toNat = 0 := by
            have r37097 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37098 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e37099 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b37100 := hb (x 1 3)
            have b37101 := hb (x 2 2)
            have b37102 := hb (x 3 13)
            have b37103 := hb (x 4 12)
            clear * - r37097 e37098 e37099 b37100 b37101 b37102 b37103 d37092
            omega
          have d37104 : (x 3 3 && x 3 13).toNat = 0 := by
            have r37105 := hand2 (x 3 3) (x 3 13)
            have b37106 := hb (x 3 13)
            have b37107 := hb (x 3 3 && x 3 13)
            clear * - r37105 b37106 b37107 d37096
            omega
          have d37108 : (x 4 2 && x 4 12).toNat = 1 := by
            have r37109 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37110 := hb (x 1 5)
            have b37111 := hb (x 6 10)
            have b37112 := hb (x 5 1 && x 5 11)
            have b37113 := hb (x 4 2 && x 4 12)
            have b37114 := hb (x 3 3 && x 3 13)
            have b37115 := hb (x 2 4 && x 2 14)
            clear * - r37109 b37110 b37111 b37112 b37113 b37114 b37115 d37039 d37075 d37104 g37 g7
            omega
          have d37116 : (x 4 2).toNat = 1 := by
            have r37117 := hand1 (x 4 2) (x 4 12)
            have b37118 := hb (x 4 2)
            have b37119 := hb (x 4 2 && x 4 12)
            clear * - r37117 b37118 b37119 d37108
            omega
          have d37120 : (x 4 14).toNat = 1 := by
            have r37121 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
            have b37122 := hb (x 4 2)
            have b37123 := hb (x 4 14)
            clear * - r37121 b37122 b37123 d37116
            omega
          have d37124 : (x 3 1).toNat = 0 := by
            have r37125 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37126 := hb (x 3 1)
            have b37127 := hb (x 4 14)
            clear * - r37125 b37126 b37127 d37120
            omega
          have d37128 : (x 3 1 && x 3 8).toNat = 0 := by
            have r37129 := hand1 (x 3 1) (x 3 8)
            have b37130 := hb (x 3 1)
            have b37131 := hb (x 3 1 && x 3 8)
            clear * - r37129 b37130 b37131 d37124
            omega
          have d37132 : (x 6 12).toNat = 0 := by
            have r37133 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37134 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e37135 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b37136 := hb (x 3 3)
            have b37137 := hb (x 4 2)
            have b37138 := hb (x 5 13)
            have b37139 := hb (x 6 12)
            clear * - r37133 e37134 e37135 b37136 b37137 b37138 b37139 d37116
            omega
          have d37140 : (x 5 13).toNat = 0 := by
            have r37141 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37142 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e37143 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b37144 := hb (x 3 3)
            have b37145 := hb (x 4 2)
            have b37146 := hb (x 5 13)
            have b37147 := hb (x 6 12)
            clear * - r37141 e37142 e37143 b37144 b37145 b37146 b37147 d37132 d37116
            omega
          have d37148 : (x 3 5).toNat = 0 := by
            have r37149 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
            have b37150 := hb (x 3 5)
            have b37151 := hb (x 3 13)
            clear * - r37149 b37150 b37151 d37096
            omega
          have d37152 : (x 2 1 && x 2 14).toNat = 1 := by
            have r37153 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37154 := hb (x 1 2)
            have b37155 := hb (x 3 13)
            have b37156 := hb (x 2 1 && x 2 14)
            clear * - r37153 b37154 b37155 b37156 d37096 g6
            omega
          have d37157 : (x 2 1).toNat = 1 := by
            have r37158 := hand1 (x 2 1) (x 2 14)
            have b37159 := hb (x 2 1)
            have b37160 := hb (x 2 1 && x 2 14)
            clear * - r37158 b37159 b37160 d37152
            omega
          have d37161 : (x 3 14).toNat = 0 := by
            have r37162 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37163 := hb (x 2 1)
            have b37164 := hb (x 3 14)
            clear * - r37162 b37163 b37164 d37157
            omega
          have d37165 : (x 3 2).toNat = 0 := by
            have r37166 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b37167 := hb (x 3 2)
            have b37168 := hb (x 3 14)
            clear * - r37166 b37167 b37168 d37161
            omega
          have d37169 : (x 4 1 && x 4 14).toNat = 1 := by
            have r37170 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37171 := hb (x 3 2)
            have b37172 := hb (x 5 13)
            have b37173 := hb (x 4 1 && x 4 14)
            clear * - r37170 b37171 b37172 b37173 d37140 d37165
            omega
          have d37174 : (x 4 1).toNat = 1 := by
            have r37175 := hand1 (x 4 1) (x 4 14)
            have b37176 := hb (x 4 1)
            have b37177 := hb (x 4 1 && x 4 14)
            clear * - r37175 b37176 b37177 d37169
            omega
          have d37178 : (x 5 14).toNat = 0 := by
            have r37179 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37180 := hb (x 4 1)
            have b37181 := hb (x 5 14)
            clear * - r37179 b37180 b37181 d37174
            omega
          have d37182 : (x 5 3 && x 5 14).toNat = 0 := by
            have r37183 := hand2 (x 5 3) (x 5 14)
            have b37184 := hb (x 5 14)
            have b37185 := hb (x 5 3 && x 5 14)
            clear * - r37183 b37184 b37185 d37178
            omega
          have d37186 : (x 5 7 && x 5 14).toNat = 0 := by
            have r37187 := hand2 (x 5 7) (x 5 14)
            have b37188 := hb (x 5 14)
            have b37189 := hb (x 5 7 && x 5 14)
            clear * - r37187 b37188 b37189 d37178
            omega
          have d37190 : (x 5 6).toNat = 0 := by
            have r37191 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
            have b37192 := hb (x 5 6)
            have b37193 := hb (x 5 14)
            clear * - r37191 b37192 b37193 d37178
            omega
          have d37194 : (x 5 2).toNat = 0 := by
            have r37195 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b37196 := hb (x 5 2)
            have b37197 := hb (x 5 14)
            clear * - r37195 b37196 b37197 d37178
            omega
          have d37198 : (x 2 2).toNat = 0 := by
            have r37199 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37200 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e37201 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b37202 := hb (x 1 3)
            have b37203 := hb (x 2 2)
            have b37204 := hb (x 3 13)
            have b37205 := hb (x 4 12)
            clear * - r37199 e37200 e37201 b37202 b37203 b37204 b37205 d37092 d37096
            omega
          have d37206 : (x 2 2 && x 2 9).toNat = 0 := by
            have r37207 := hand1 (x 2 2) (x 2 9)
            have b37208 := hb (x 2 2)
            have b37209 := hb (x 2 2 && x 2 9)
            clear * - r37207 b37208 b37209 d37198
            omega
          have d37210 : (x 4 3).toNat = 1 := by
            have r37211 := hand1 (x 4 3) (x 4 12)
            have b37212 := hb (x 4 3)
            have b37213 := hb (x 4 3 && x 4 12)
            clear * - r37211 b37212 b37213 d37083
            omega
          have d37214 : (x 7 12).toNat = 0 := by
            have r37215 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37216 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e37217 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b37218 := hb (x 4 3)
            have b37219 := hb (x 5 2)
            have b37220 := hb (x 6 13)
            have b37221 := hb (x 7 12)
            clear * - r37215 e37216 e37217 b37218 b37219 b37220 b37221 d37194 d37210
            omega
          have d37222 : (x 7 1 && x 7 12).toNat = 0 := by
            have r37223 := hand2 (x 7 1) (x 7 12)
            have b37224 := hb (x 7 12)
            have b37225 := hb (x 7 1 && x 7 12)
            clear * - r37223 b37224 b37225 d37214
            omega
          have d37226 : (x 7 5 && x 7 12).toNat = 0 := by
            have r37227 := hand2 (x 7 5) (x 7 12)
            have b37228 := hb (x 7 12)
            have b37229 := hb (x 7 5 && x 7 12)
            clear * - r37227 b37228 b37229 d37214
            omega
          have d37230 : (x 7 6 && x 7 12).toNat = 0 := by
            have r37231 := hand2 (x 7 6) (x 7 12)
            have b37232 := hb (x 7 12)
            have b37233 := hb (x 7 6 && x 7 12)
            clear * - r37231 b37232 b37233 d37214
            omega
          have d37234 : (x 7 4).toNat = 0 := by
            have r37235 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
            have b37236 := hb (x 7 4)
            have b37237 := hb (x 7 12)
            clear * - r37235 b37236 b37237 d37214
            omega
          have d37238 : (x 7 4 && x 7 14).toNat = 0 := by
            have r37239 := hand1 (x 7 4) (x 7 14)
            have b37240 := hb (x 7 4)
            have b37241 := hb (x 7 4 && x 7 14)
            clear * - r37239 b37240 b37241 d37234
            omega
          have d37242 : (x 7 4 && x 7 13).toNat = 0 := by
            have r37243 := hand1 (x 7 4) (x 7 13)
            have b37244 := hb (x 7 4)
            have b37245 := hb (x 7 4 && x 7 13)
            clear * - r37243 b37244 b37245 d37234
            omega
          have d37246 : (x 6 13).toNat = 0 := by
            have r37247 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37248 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e37249 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b37250 := hb (x 4 3)
            have b37251 := hb (x 5 2)
            have b37252 := hb (x 6 13)
            have b37253 := hb (x 7 12)
            clear * - r37247 e37248 e37249 b37250 b37251 b37252 b37253 d37214 d37194 d37210
            omega
          have d37254 : (x 6 2 && x 6 13).toNat = 0 := by
            have r37255 := hand2 (x 6 2) (x 6 13)
            have b37256 := hb (x 6 13)
            have b37257 := hb (x 6 2 && x 6 13)
            clear * - r37255 b37256 b37257 d37246
            omega
          have d37258 : (x 6 6 && x 6 13).toNat = 0 := by
            have r37259 := hand2 (x 6 6) (x 6 13)
            have b37260 := hb (x 6 13)
            have b37261 := hb (x 6 6 && x 6 13)
            clear * - r37259 b37260 b37261 d37246
            omega
          have d37262 : (x 6 7 && x 6 13).toNat = 0 := by
            have r37263 := hand2 (x 6 7) (x 6 13)
            have b37264 := hb (x 6 13)
            have b37265 := hb (x 6 7 && x 6 13)
            clear * - r37263 b37264 b37265 d37246
            omega
          have d37266 : (x 6 5).toNat = 0 := by
            have r37267 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
            have b37268 := hb (x 6 5)
            have b37269 := hb (x 6 13)
            clear * - r37267 b37268 b37269 d37246
            omega
          have d37270 : (x 6 5 && x 6 14).toNat = 0 := by
            have r37271 := hand1 (x 6 5) (x 6 14)
            have b37272 := hb (x 6 5)
            have b37273 := hb (x 6 5 && x 6 14)
            clear * - r37271 b37272 b37273 d37266
            omega
          have d37274 : (x 4 4).toNat = 0 := by
            have r37275 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37276 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e37277 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e37278 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e37279 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e37280 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e37281 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b37282 := hb (x 1 7)
            have b37283 := hb (x 2 6)
            have b37284 := hb (x 3 5)
            have b37285 := hb (x 4 4)
            have b37286 := hb (x 5 11)
            have b37287 := hb (x 6 10)
            have b37288 := hb (x 7 9)
            have b37289 := hb (x 8 8)
            clear * - r37275 e37276 e37277 e37278 e37279 e37280 e37281 b37282 b37283 b37284 b37285 b37286 b37287 b37288 b37289 d37007 d37023 d37039 d37059 d37148 f37006
            omega
          have d37290 : (x 8 11).toNat = 1 := by
            have r37291 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37292 := hb (x 4 4)
            have b37293 := hb (x 8 11)
            have b37294 := hb (x 7 1 && x 7 12)
            have b37295 := hb (x 6 2 && x 6 13)
            have b37296 := hb (x 5 3 && x 5 14)
            clear * - r37291 b37292 b37293 b37294 b37295 b37296 d37222 d37254 d37182 d37274
            omega
          have d37297 : (x 8 3).toNat = 1 := by
            have r37298 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
            have b37299 := hb (x 8 3)
            have b37300 := hb (x 8 11)
            clear * - r37298 b37299 b37300 d37290
            omega
          have d37301 : (x 11 12).toNat = 0 := by
            have r37302 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37303 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e37304 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b37305 := hb (x 8 3)
            have b37306 := hb (x 9 2)
            have b37307 := hb (x 10 13)
            have b37308 := hb (x 11 12)
            clear * - r37302 e37303 e37304 b37305 b37306 b37307 b37308 d37297
            omega
          have d37309 : (x 11 2 && x 11 12).toNat = 0 := by
            have r37310 := hand2 (x 11 2) (x 11 12)
            have b37311 := hb (x 11 12)
            have b37312 := hb (x 11 2 && x 11 12)
            clear * - r37310 b37311 b37312 d37301
            omega
          have d37313 : (x 11 4).toNat = 0 := by
            have r37314 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
            have b37315 := hb (x 11 4)
            have b37316 := hb (x 11 12)
            clear * - r37314 b37315 b37316 d37301
            omega
          have d37317 : (x 11 4 && x 11 14).toNat = 0 := by
            have r37318 := hand1 (x 11 4) (x 11 14)
            have b37319 := hb (x 11 4)
            have b37320 := hb (x 11 4 && x 11 14)
            clear * - r37318 b37319 b37320 d37313
            omega
          have d37321 : (x 10 13).toNat = 0 := by
            have r37322 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37323 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e37324 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b37325 := hb (x 8 3)
            have b37326 := hb (x 9 2)
            have b37327 := hb (x 10 13)
            have b37328 := hb (x 11 12)
            clear * - r37322 e37323 e37324 b37325 b37326 b37327 b37328 d37301 d37297
            omega
          have d37329 : (x 10 3 && x 10 13).toNat = 0 := by
            have r37330 := hand2 (x 10 3) (x 10 13)
            have b37331 := hb (x 10 13)
            have b37332 := hb (x 10 3 && x 10 13)
            clear * - r37330 b37331 b37332 d37321
            omega
          have d37333 : (x 10 5).toNat = 0 := by
            have r37334 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
            have b37335 := hb (x 10 5)
            have b37336 := hb (x 10 13)
            clear * - r37334 b37335 b37336 d37321
            omega
          have d37337 : (x 9 2).toNat = 0 := by
            have r37338 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37339 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e37340 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b37341 := hb (x 8 3)
            have b37342 := hb (x 9 2)
            have b37343 := hb (x 10 13)
            have b37344 := hb (x 11 12)
            clear * - r37338 e37339 e37340 b37341 b37342 b37343 b37344 d37301 d37321 d37297
            omega
          have d37345 : (x 9 2 && x 9 13).toNat = 0 := by
            have r37346 := hand1 (x 9 2) (x 9 13)
            have b37347 := hb (x 9 2)
            have b37348 := hb (x 9 2 && x 9 13)
            clear * - r37346 b37347 b37348 d37337
            omega
          have d37349 : (x 9 2 && x 9 12).toNat = 0 := by
            have r37350 := hand1 (x 9 2) (x 9 12)
            have b37351 := hb (x 9 2)
            have b37352 := hb (x 9 2 && x 9 12)
            clear * - r37350 b37351 b37352 d37337
            omega
          have d37353 : (x 9 2 && x 9 11).toNat = 0 := by
            have r37354 := hand1 (x 9 2) (x 9 11)
            have b37355 := hb (x 9 2)
            have b37356 := hb (x 9 2 && x 9 11)
            clear * - r37354 b37355 b37356 d37337
            omega
          have d37357 : (x 9 10).toNat = 0 := by
            have r37358 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
            have b37359 := hb (x 9 2)
            have b37360 := hb (x 9 10)
            clear * - r37358 b37359 b37360 d37337
            omega
          have d37361 : (x 9 3 && x 9 10).toNat = 0 := by
            have r37362 := hand2 (x 9 3) (x 9 10)
            have b37363 := hb (x 9 10)
            have b37364 := hb (x 9 3 && x 9 10)
            clear * - r37362 b37363 b37364 d37357
            omega
          have d37365 : (x 9 4 && x 9 10).toNat = 0 := by
            have r37366 := hand2 (x 9 4) (x 9 10)
            have b37367 := hb (x 9 10)
            have b37368 := hb (x 9 4 && x 9 10)
            clear * - r37366 b37367 b37368 d37357
            omega
          have d37369 : (x 11 8).toNat = 0 := by
            have r37370 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37371 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e37372 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e37373 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e37374 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e37375 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e37376 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b37377 := hb (x 4 7)
            have b37378 := hb (x 5 6)
            have b37379 := hb (x 6 5)
            have b37380 := hb (x 7 4)
            have b37381 := hb (x 8 11)
            have b37382 := hb (x 9 10)
            have b37383 := hb (x 10 9)
            have b37384 := hb (x 11 8)
            clear * - r37370 e37371 e37372 e37373 e37374 e37375 e37376 b37377 b37378 b37379 b37380 b37381 b37382 b37383 b37384 d37357 d37290 d37234 d37266 d37190
            omega
          have d37385 : (x 11 1 && x 11 8).toNat = 0 := by
            have r37386 := hand2 (x 11 1) (x 11 8)
            have b37387 := hb (x 11 8)
            have b37388 := hb (x 11 1 && x 11 8)
            clear * - r37386 b37387 b37388 d37369
            omega
          have d37389 : (x 11 2 && x 11 8).toNat = 0 := by
            have r37390 := hand2 (x 11 2) (x 11 8)
            have b37391 := hb (x 11 8)
            have b37392 := hb (x 11 2 && x 11 8)
            clear * - r37390 b37391 b37392 d37369
            omega
          have d37393 : (x 10 9).toNat = 0 := by
            have r37394 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37395 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e37396 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e37397 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e37398 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e37399 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e37400 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b37401 := hb (x 4 7)
            have b37402 := hb (x 5 6)
            have b37403 := hb (x 6 5)
            have b37404 := hb (x 7 4)
            have b37405 := hb (x 8 11)
            have b37406 := hb (x 9 10)
            have b37407 := hb (x 10 9)
            have b37408 := hb (x 11 8)
            clear * - r37394 e37395 e37396 e37397 e37398 e37399 e37400 b37401 b37402 b37403 b37404 b37405 b37406 b37407 b37408 d37369 d37357 d37290 d37234 d37266 d37190
            omega
          have d37409 : (x 10 2 && x 10 9).toNat = 0 := by
            have r37410 := hand2 (x 10 2) (x 10 9)
            have b37411 := hb (x 10 9)
            have b37412 := hb (x 10 2 && x 10 9)
            clear * - r37410 b37411 b37412 d37393
            omega
          have d37413 : (x 10 3 && x 10 9).toNat = 0 := by
            have r37414 := hand2 (x 10 3) (x 10 9)
            have b37415 := hb (x 10 9)
            have b37416 := hb (x 10 3 && x 10 9)
            clear * - r37414 b37415 b37416 d37393
            omega
          have d37417 : (x 4 7).toNat = 0 := by
            have r37418 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37419 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e37420 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e37421 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e37422 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e37423 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e37424 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b37425 := hb (x 4 7)
            have b37426 := hb (x 5 6)
            have b37427 := hb (x 6 5)
            have b37428 := hb (x 7 4)
            have b37429 := hb (x 8 11)
            have b37430 := hb (x 9 10)
            have b37431 := hb (x 10 9)
            have b37432 := hb (x 11 8)
            clear * - r37418 e37419 e37420 e37421 e37422 e37423 e37424 b37425 b37426 b37427 b37428 b37429 b37430 b37431 b37432 d37369 d37393 d37357 d37290 d37234 d37266 d37190
            omega
          have d37433 : (x (-4) 8).toNat = 1 := by
            have r37434 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37435 := hb (x (-4) 8)
            have b37436 := hb (x 4 7)
            have b37437 := hb (x 3 1 && x 3 8)
            have b37438 := hb (x 2 2 && x 2 9)
            have b37439 := hb (x 1 3 && x 1 10)
            have b37440 := hb (x 0 4 && x 0 11)
            have b37441 := hb (x (-1) 5 && x (-1) 12)
            have b37442 := hb (x (-2) 6 && x (-2) 13)
            have b37443 := hb (x (-3) 7 && x (-3) 14)
            clear * - r37434 b37435 b37436 b37437 b37438 b37439 b37440 b37441 b37442 b37443 d37417 d37128 d37206 g23 d34822 g24 d35239 d35263
            omega
          have d37444 : (x (-8) 4).toNat = 0 := by
            have r37445 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37446 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
            have e37447 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
            have e37448 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
            have e37449 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
            have e37450 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
            have e37451 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
            have b37452 := hb (x (-11) 7)
            have b37453 := hb (x (-10) 6)
            have b37454 := hb (x (-9) 5)
            have b37455 := hb (x (-8) 4)
            have b37456 := hb (x (-7) 11)
            have b37457 := hb (x (-6) 10)
            have b37458 := hb (x (-5) 9)
            have b37459 := hb (x (-4) 8)
            clear * - r37445 e37446 e37447 e37448 e37449 e37450 e37451 b37452 b37453 b37454 b37455 b37456 b37457 b37458 b37459 d37433 d35819 d35115 d35143
            omega
          have d37460 : (x (-4) 11).toNat = 1 := by
            have r37461 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37462 := hb (x (-8) 4)
            have b37463 := hb (x (-4) 11)
            have b37464 := hb (x (-5) 1 && x (-5) 12)
            have b37465 := hb (x (-6) 2 && x (-6) 13)
            have b37466 := hb (x (-7) 3 && x (-7) 14)
            clear * - r37461 b37462 b37463 b37464 b37465 b37466 d35811 d35103 d35131 d37444
            omega
          have d37467 : (x (-1) 8).toNat = 0 := by
            have r37468 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37469 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e37470 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e37471 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e37472 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e37473 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e37474 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b37475 := hb (x (-8) 7)
            have b37476 := hb (x (-7) 6)
            have b37477 := hb (x (-6) 5)
            have b37478 := hb (x (-5) 4)
            have b37479 := hb (x (-4) 11)
            have b37480 := hb (x (-3) 10)
            have b37481 := hb (x (-2) 9)
            have b37482 := hb (x (-1) 8)
            clear * - r37468 e37469 e37470 e37471 e37472 e37473 e37474 b37475 b37476 b37477 b37478 b37479 b37480 b37481 b37482 d35741 d37460
            omega
          have d37483 : (x 7 7).toNat = 1 := by
            have r37484 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37485 := hb (x (-1) 8)
            have b37486 := hb (x 7 7)
            have b37487 := hb (x 6 1 && x 6 8)
            have b37488 := hb (x 5 2 && x 5 9)
            have b37489 := hb (x 4 3 && x 4 10)
            have b37490 := hb (x 3 4 && x 3 11)
            have b37491 := hb (x 2 5 && x 2 12)
            have b37492 := hb (x 1 6 && x 1 13)
            have b37493 := hb (x 0 7 && x 0 14)
            clear * - r37484 b37485 b37486 b37487 b37488 b37489 b37490 b37491 b37492 b37493 g25 g26 g27 g28 g29 d34902 g30 d37467
            omega
          have d37494 : (x 14 8).toNat = 0 := by
            have r37495 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37496 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e37497 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e37498 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e37499 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e37500 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e37501 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b37502 := hb (x 7 7)
            have b37503 := hb (x 8 6)
            have b37504 := hb (x 9 5)
            have b37505 := hb (x 10 4)
            have b37506 := hb (x 11 11)
            have b37507 := hb (x 12 10)
            have b37508 := hb (x 13 9)
            have b37509 := hb (x 14 8)
            clear * - r37495 e37496 e37497 e37498 e37499 e37500 e37501 b37502 b37503 b37504 b37505 b37506 b37507 b37508 b37509 d37483
            omega
          have d37510 : (x 13 9).toNat = 0 := by
            have r37511 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37512 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e37513 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e37514 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e37515 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e37516 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e37517 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b37518 := hb (x 7 7)
            have b37519 := hb (x 8 6)
            have b37520 := hb (x 9 5)
            have b37521 := hb (x 10 4)
            have b37522 := hb (x 11 11)
            have b37523 := hb (x 12 10)
            have b37524 := hb (x 13 9)
            have b37525 := hb (x 14 8)
            clear * - r37511 e37512 e37513 e37514 e37515 e37516 e37517 b37518 b37519 b37520 b37521 b37522 b37523 b37524 b37525 d37494 d37483
            omega
          have d37526 : (x 12 10).toNat = 0 := by
            have r37527 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37528 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e37529 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e37530 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e37531 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e37532 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e37533 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b37534 := hb (x 7 7)
            have b37535 := hb (x 8 6)
            have b37536 := hb (x 9 5)
            have b37537 := hb (x 10 4)
            have b37538 := hb (x 11 11)
            have b37539 := hb (x 12 10)
            have b37540 := hb (x 13 9)
            have b37541 := hb (x 14 8)
            clear * - r37527 e37528 e37529 e37530 e37531 e37532 e37533 b37534 b37535 b37536 b37537 b37538 b37539 b37540 b37541 d37494 d37510 d37483
            omega
          have d37542 : (x 11 11).toNat = 0 := by
            have r37543 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37544 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e37545 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e37546 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e37547 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e37548 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e37549 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b37550 := hb (x 7 7)
            have b37551 := hb (x 8 6)
            have b37552 := hb (x 9 5)
            have b37553 := hb (x 10 4)
            have b37554 := hb (x 11 11)
            have b37555 := hb (x 12 10)
            have b37556 := hb (x 13 9)
            have b37557 := hb (x 14 8)
            clear * - r37543 e37544 e37545 e37546 e37547 e37548 e37549 b37550 b37551 b37552 b37553 b37554 b37555 b37556 b37557 d37494 d37510 d37526 d37483
            omega
          have d37558 : (x 10 4).toNat = 0 := by
            have r37559 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37560 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e37561 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e37562 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e37563 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e37564 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e37565 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b37566 := hb (x 7 7)
            have b37567 := hb (x 8 6)
            have b37568 := hb (x 9 5)
            have b37569 := hb (x 10 4)
            have b37570 := hb (x 11 11)
            have b37571 := hb (x 12 10)
            have b37572 := hb (x 13 9)
            have b37573 := hb (x 14 8)
            clear * - r37559 e37560 e37561 e37562 e37563 e37564 e37565 b37566 b37567 b37568 b37569 b37570 b37571 b37572 b37573 d37494 d37510 d37526 d37542 d37483
            omega
          have d37574 : (x 9 5).toNat = 0 := by
            have r37575 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37576 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e37577 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e37578 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e37579 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e37580 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e37581 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b37582 := hb (x 7 7)
            have b37583 := hb (x 8 6)
            have b37584 := hb (x 9 5)
            have b37585 := hb (x 10 4)
            have b37586 := hb (x 11 11)
            have b37587 := hb (x 12 10)
            have b37588 := hb (x 13 9)
            have b37589 := hb (x 14 8)
            clear * - r37575 e37576 e37577 e37578 e37579 e37580 e37581 b37582 b37583 b37584 b37585 b37586 b37587 b37588 b37589 d37494 d37510 d37526 d37542 d37558 d37483
            omega
          have d37590 : (x 8 6).toNat = 0 := by
            have r37591 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37592 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
            have e37593 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
            have e37594 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
            have e37595 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
            have e37596 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
            have e37597 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
            have b37598 := hb (x 7 7)
            have b37599 := hb (x 8 6)
            have b37600 := hb (x 9 5)
            have b37601 := hb (x 10 4)
            have b37602 := hb (x 11 11)
            have b37603 := hb (x 12 10)
            have b37604 := hb (x 13 9)
            have b37605 := hb (x 14 8)
            clear * - r37591 e37592 e37593 e37594 e37595 e37596 e37597 b37598 b37599 b37600 b37601 b37602 b37603 b37604 b37605 d37494 d37510 d37526 d37542 d37558 d37574 d37483
            omega
          have d37606 : (x 7 1 && x 7 7).toNat = 1 := by
            have r37607 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37608 := hb (x (-1) 9)
            have b37609 := hb (x 8 6)
            have b37610 := hb (x 7 1 && x 7 7)
            have b37611 := hb (x 6 2 && x 6 8)
            have b37612 := hb (x 5 3 && x 5 9)
            have b37613 := hb (x 4 4 && x 4 10)
            have b37614 := hb (x 3 5 && x 3 11)
            have b37615 := hb (x 2 6 && x 2 12)
            have b37616 := hb (x 1 7 && x 1 13)
            have b37617 := hb (x 0 8 && x 0 14)
            clear * - r37607 b37608 b37609 b37610 b37611 b37612 b37613 b37614 b37615 b37616 b37617 d37590 g19 g20 g21 g22 d34927 d34951 d35291 g2
            omega
          have d37618 : (x 7 1).toNat = 1 := by
            have r37619 := hand1 (x 7 1) (x 7 7)
            have b37620 := hb (x 7 1)
            have b37621 := hb (x 7 1 && x 7 7)
            clear * - r37619 b37620 b37621 d37606
            omega
          have d37622 : (x 8 14).toNat = 0 := by
            have r37623 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37624 := hb (x 7 1)
            have b37625 := hb (x 8 14)
            clear * - r37623 b37624 b37625 d37618
            omega
          have d37626 : (x 8 1 && x 8 14).toNat = 0 := by
            have r37627 := hand2 (x 8 1) (x 8 14)
            have b37628 := hb (x 8 14)
            have b37629 := hb (x 8 1 && x 8 14)
            clear * - r37627 b37628 b37629 d37622
            omega
          have d37630 : (x 8 3 && x 8 14).toNat = 0 := by
            have r37631 := hand2 (x 8 3) (x 8 14)
            have b37632 := hb (x 8 14)
            have b37633 := hb (x 8 3 && x 8 14)
            clear * - r37631 b37632 b37633 d37622
            omega
          have d37634 : (x 10 1 && x 10 12).toNat = 1 := by
            have r37635 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37636 := hb (x 7 4)
            have b37637 := hb (x 11 11)
            have b37638 := hb (x 10 1 && x 10 12)
            have b37639 := hb (x 9 2 && x 9 13)
            have b37640 := hb (x 8 3 && x 8 14)
            clear * - r37635 b37636 b37637 b37638 b37639 b37640 d37542 d37345 d37630 d37234
            omega
          have d37641 : (x 10 12).toNat = 1 := by
            have r37642 := hand2 (x 10 1) (x 10 12)
            have b37643 := hb (x 10 12)
            have b37644 := hb (x 10 1 && x 10 12)
            clear * - r37642 b37643 b37644 d37634
            omega
          have d37645 : (x 9 13).toNat = 0 := by
            have r37646 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37647 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e37648 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b37649 := hb (x 7 3)
            have b37650 := hb (x 8 2)
            have b37651 := hb (x 9 13)
            have b37652 := hb (x 10 12)
            clear * - r37646 e37647 e37648 b37649 b37650 b37651 b37652 d37641
            omega
          have d37653 : (x 7 2).toNat = 1 := by
            have r37654 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37655 := hb (x 7 2)
            have b37656 := hb (x 9 13)
            have b37657 := hb (x 8 1 && x 8 14)
            clear * - r37654 b37655 b37656 b37657 d37645 d37626
            omega
          have d37658 : (x 7 14).toNat = 1 := by
            have r37659 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
            have b37660 := hb (x 7 2)
            have b37661 := hb (x 7 14)
            clear * - r37659 b37660 b37661 d37653
            omega
          have d37662 : (x 6 1).toNat = 0 := by
            have r37663 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37664 := hb (x 6 1)
            have b37665 := hb (x 7 14)
            clear * - r37663 b37664 b37665 d37658
            omega
          have d37666 : (x 6 1 && x 6 14).toNat = 0 := by
            have r37667 := hand1 (x 6 1) (x 6 14)
            have b37668 := hb (x 6 1)
            have b37669 := hb (x 6 1 && x 6 14)
            clear * - r37667 b37668 b37669 d37662
            omega
          have d37670 : (x 7 13).toNat = 1 := by
            have r37671 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37672 := hb (x 5 2)
            have b37673 := hb (x 7 13)
            have b37674 := hb (x 6 1 && x 6 14)
            clear * - r37671 b37672 b37673 b37674 d37666 d37194
            omega
          have d37675 : (x 8 12).toNat = 0 := by
            have r37676 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37677 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e37678 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b37679 := hb (x 5 3)
            have b37680 := hb (x 6 2)
            have b37681 := hb (x 7 13)
            have b37682 := hb (x 8 12)
            clear * - r37676 e37677 e37678 b37679 b37680 b37681 b37682 d37670
            omega
          have d37683 : (x 8 3 && x 8 12).toNat = 0 := by
            have r37684 := hand2 (x 8 3) (x 8 12)
            have b37685 := hb (x 8 12)
            have b37686 := hb (x 8 3 && x 8 12)
            clear * - r37684 b37685 b37686 d37675
            omega
          have d37687 : (x 8 4).toNat = 0 := by
            have r37688 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
            have b37689 := hb (x 8 4)
            have b37690 := hb (x 8 12)
            clear * - r37688 b37689 b37690 d37675
            omega
          have d37691 : (x 8 4 && x 8 11).toNat = 0 := by
            have r37692 := hand1 (x 8 4) (x 8 11)
            have b37693 := hb (x 8 4)
            have b37694 := hb (x 8 4 && x 8 11)
            clear * - r37692 b37693 b37694 d37687
            omega
          have d37695 : (x 12 7).toNat = 1 := by
            have r37696 : 1 ≤ (x 12 7).toNat + (x 11 1 && x 11 8).toNat + (x 10 2 && x 10 9).toNat + (x 9 3 && x 9 10).toNat + (x 8 4 && x 8 11).toNat + (x 7 5 && x 7 12).toNat + (x 6 6 && x 6 13).toNat + (x 5 7 && x 5 14).toNat + (x 4 8).toNat := by have q := hcov7 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37697 := hb (x 4 8)
            have b37698 := hb (x 12 7)
            have b37699 := hb (x 11 1 && x 11 8)
            have b37700 := hb (x 10 2 && x 10 9)
            have b37701 := hb (x 9 3 && x 9 10)
            have b37702 := hb (x 8 4 && x 8 11)
            have b37703 := hb (x 7 5 && x 7 12)
            have b37704 := hb (x 6 6 && x 6 13)
            have b37705 := hb (x 5 7 && x 5 14)
            clear * - r37696 b37697 b37698 b37699 b37700 b37701 b37702 b37703 b37704 b37705 d37385 d37409 d37361 d37691 d37226 d37258 d37186 d35159
            omega
          have d37706 : (x 19 8).toNat = 0 := by
            have r37707 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37708 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
            have e37709 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
            have e37710 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
            have e37711 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
            have e37712 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
            have e37713 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
            have b37714 := hb (x 12 7)
            have b37715 := hb (x 13 6)
            have b37716 := hb (x 14 5)
            have b37717 := hb (x 15 4)
            have b37718 := hb (x 16 11)
            have b37719 := hb (x 17 10)
            have b37720 := hb (x 18 9)
            have b37721 := hb (x 19 8)
            clear * - r37707 e37708 e37709 e37710 e37711 e37712 e37713 b37714 b37715 b37716 b37717 b37718 b37719 b37720 b37721 d37695
            omega
          have d37722 : (x 18 9).toNat = 0 := by
            have r37723 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37724 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
            have e37725 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
            have e37726 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
            have e37727 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
            have e37728 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
            have e37729 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
            have b37730 := hb (x 12 7)
            have b37731 := hb (x 13 6)
            have b37732 := hb (x 14 5)
            have b37733 := hb (x 15 4)
            have b37734 := hb (x 16 11)
            have b37735 := hb (x 17 10)
            have b37736 := hb (x 18 9)
            have b37737 := hb (x 19 8)
            clear * - r37723 e37724 e37725 e37726 e37727 e37728 e37729 b37730 b37731 b37732 b37733 b37734 b37735 b37736 b37737 d37706 d37695
            omega
          have d37738 : (x 17 10).toNat = 0 := by
            have r37739 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37740 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
            have e37741 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
            have e37742 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
            have e37743 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
            have e37744 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
            have e37745 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
            have b37746 := hb (x 12 7)
            have b37747 := hb (x 13 6)
            have b37748 := hb (x 14 5)
            have b37749 := hb (x 15 4)
            have b37750 := hb (x 16 11)
            have b37751 := hb (x 17 10)
            have b37752 := hb (x 18 9)
            have b37753 := hb (x 19 8)
            clear * - r37739 e37740 e37741 e37742 e37743 e37744 e37745 b37746 b37747 b37748 b37749 b37750 b37751 b37752 b37753 d37706 d37722 d37695
            omega
          have d37754 : (x 16 11).toNat = 0 := by
            have r37755 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37756 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
            have e37757 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
            have e37758 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
            have e37759 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
            have e37760 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
            have e37761 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
            have b37762 := hb (x 12 7)
            have b37763 := hb (x 13 6)
            have b37764 := hb (x 14 5)
            have b37765 := hb (x 15 4)
            have b37766 := hb (x 16 11)
            have b37767 := hb (x 17 10)
            have b37768 := hb (x 18 9)
            have b37769 := hb (x 19 8)
            clear * - r37755 e37756 e37757 e37758 e37759 e37760 e37761 b37762 b37763 b37764 b37765 b37766 b37767 b37768 b37769 d37706 d37722 d37738 d37695
            omega
          have d37770 : (x 15 4).toNat = 0 := by
            have r37771 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37772 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
            have e37773 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
            have e37774 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
            have e37775 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
            have e37776 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
            have e37777 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
            have b37778 := hb (x 12 7)
            have b37779 := hb (x 13 6)
            have b37780 := hb (x 14 5)
            have b37781 := hb (x 15 4)
            have b37782 := hb (x 16 11)
            have b37783 := hb (x 17 10)
            have b37784 := hb (x 18 9)
            have b37785 := hb (x 19 8)
            clear * - r37771 e37772 e37773 e37774 e37775 e37776 e37777 b37778 b37779 b37780 b37781 b37782 b37783 b37784 b37785 d37706 d37722 d37738 d37754 d37695
            omega
          have d37786 : (x 14 5).toNat = 0 := by
            have r37787 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37788 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
            have e37789 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
            have e37790 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
            have e37791 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
            have e37792 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
            have e37793 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
            have b37794 := hb (x 12 7)
            have b37795 := hb (x 13 6)
            have b37796 := hb (x 14 5)
            have b37797 := hb (x 15 4)
            have b37798 := hb (x 16 11)
            have b37799 := hb (x 17 10)
            have b37800 := hb (x 18 9)
            have b37801 := hb (x 19 8)
            clear * - r37787 e37788 e37789 e37790 e37791 e37792 e37793 b37794 b37795 b37796 b37797 b37798 b37799 b37800 b37801 d37706 d37722 d37738 d37754 d37770 d37695
            omega
          have d37802 : (x 13 6).toNat = 0 := by
            have r37803 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37804 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
            have e37805 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
            have e37806 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
            have e37807 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
            have e37808 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
            have e37809 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
            have b37810 := hb (x 12 7)
            have b37811 := hb (x 13 6)
            have b37812 := hb (x 14 5)
            have b37813 := hb (x 15 4)
            have b37814 := hb (x 16 11)
            have b37815 := hb (x 17 10)
            have b37816 := hb (x 18 9)
            have b37817 := hb (x 19 8)
            clear * - r37803 e37804 e37805 e37806 e37807 e37808 e37809 b37810 b37811 b37812 b37813 b37814 b37815 b37816 b37817 d37706 d37722 d37738 d37754 d37770 d37786 d37695
            omega
          have d37818 : (x 9 12).toNat = 0 := by
            have r37819 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37820 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e37821 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b37822 := hb (x 6 3)
            have b37823 := hb (x 7 2)
            have b37824 := hb (x 8 13)
            have b37825 := hb (x 9 12)
            clear * - r37819 e37820 e37821 b37822 b37823 b37824 b37825 d37653
            omega
          have d37826 : (x 9 4).toNat = 0 := by
            have r37827 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
            have b37828 := hb (x 9 4)
            have b37829 := hb (x 9 12)
            clear * - r37827 b37828 b37829 d37818
            omega
          have d37830 : (x 9 4 && x 9 14).toNat = 0 := by
            have r37831 := hand1 (x 9 4) (x 9 14)
            have b37832 := hb (x 9 4)
            have b37833 := hb (x 9 4 && x 9 14)
            clear * - r37831 b37832 b37833 d37826
            omega
          have d37834 : (x 8 13).toNat = 0 := by
            have r37835 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37836 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e37837 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b37838 := hb (x 6 3)
            have b37839 := hb (x 7 2)
            have b37840 := hb (x 8 13)
            have b37841 := hb (x 9 12)
            clear * - r37835 e37836 e37837 b37838 b37839 b37840 b37841 d37818 d37653
            omega
          have d37842 : (x 8 3 && x 8 13).toNat = 0 := by
            have r37843 := hand2 (x 8 3) (x 8 13)
            have b37844 := hb (x 8 13)
            have b37845 := hb (x 8 3 && x 8 13)
            clear * - r37843 b37844 b37845 d37834
            omega
          have d37846 : (x 8 5).toNat = 0 := by
            have r37847 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
            have b37848 := hb (x 8 5)
            have b37849 := hb (x 8 13)
            clear * - r37847 b37848 b37849 d37834
            omega
          have d37850 : (x 8 5 && x 8 11).toNat = 0 := by
            have r37851 := hand1 (x 8 5) (x 8 11)
            have b37852 := hb (x 8 5)
            have b37853 := hb (x 8 5 && x 8 11)
            clear * - r37851 b37852 b37853 d37846
            omega
          have d37854 : (x 12 1 && x 12 7).toNat = 1 := by
            have r37855 : 1 ≤ (x 13 6).toNat + (x 12 1 && x 12 7).toNat + (x 11 2 && x 11 8).toNat + (x 10 3 && x 10 9).toNat + (x 9 4 && x 9 10).toNat + (x 8 5 && x 8 11).toNat + (x 7 6 && x 7 12).toNat + (x 6 7 && x 6 13).toNat + (x 5 8 && x 5 14).toNat + (x 4 9).toNat := by have q := hcov6 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37856 := hb (x 4 9)
            have b37857 := hb (x 13 6)
            have b37858 := hb (x 12 1 && x 12 7)
            have b37859 := hb (x 11 2 && x 11 8)
            have b37860 := hb (x 10 3 && x 10 9)
            have b37861 := hb (x 9 4 && x 9 10)
            have b37862 := hb (x 8 5 && x 8 11)
            have b37863 := hb (x 7 6 && x 7 12)
            have b37864 := hb (x 6 7 && x 6 13)
            have b37865 := hb (x 5 8 && x 5 14)
            clear * - r37855 b37856 b37857 b37858 b37859 b37860 b37861 b37862 b37863 b37864 b37865 d37802 d37389 d37413 d37365 d37850 d37230 d37262 d35578 d35586
            omega
          have d37866 : (x 12 1).toNat = 1 := by
            have r37867 := hand1 (x 12 1) (x 12 7)
            have b37868 := hb (x 12 1)
            have b37869 := hb (x 12 1 && x 12 7)
            clear * - r37867 b37868 b37869 d37854
            omega
          have d37870 : (x 13 14).toNat = 0 := by
            have r37871 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37872 := hb (x 12 1)
            have b37873 := hb (x 13 14)
            clear * - r37871 b37872 b37873 d37866
            omega
          have d37874 : (x 13 3 && x 13 14).toNat = 0 := by
            have r37875 := hand2 (x 13 3) (x 13 14)
            have b37876 := hb (x 13 14)
            have b37877 := hb (x 13 3 && x 13 14)
            clear * - r37875 b37876 b37877 d37870
            omega
          have d37878 : (x 13 2).toNat = 0 := by
            have r37879 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
            have b37880 := hb (x 13 2)
            have b37881 := hb (x 13 14)
            clear * - r37879 b37880 b37881 d37870
            omega
          have d37882 : (x 13 2 && x 13 12).toNat = 0 := by
            have r37883 := hand1 (x 13 2) (x 13 12)
            have b37884 := hb (x 13 2)
            have b37885 := hb (x 13 2 && x 13 12)
            clear * - r37883 b37884 b37885 d37878
            omega
          have d37886 : (x 13 10).toNat = 0 := by
            have r37887 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
            have b37888 := hb (x 13 2)
            have b37889 := hb (x 13 10)
            clear * - r37887 b37888 b37889 d37878
            omega
          have d37890 : (x 12 1 && x 12 11).toNat = 1 := by
            have r37891 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37892 := hb (x 8 5)
            have b37893 := hb (x 13 10)
            have b37894 := hb (x 12 1 && x 12 11)
            have b37895 := hb (x 11 2 && x 11 12)
            have b37896 := hb (x 10 3 && x 10 13)
            have b37897 := hb (x 9 4 && x 9 14)
            clear * - r37891 b37892 b37893 b37894 b37895 b37896 b37897 d37886 d37309 d37329 d37830 d37846
            omega
          have d37898 : (x 12 11).toNat = 1 := by
            have r37899 := hand2 (x 12 1) (x 12 11)
            have b37900 := hb (x 12 11)
            have b37901 := hb (x 12 1 && x 12 11)
            clear * - r37899 b37900 b37901 d37890
            omega
          have d37902 : (x 12 3).toNat = 1 := by
            have r37903 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
            have b37904 := hb (x 12 3)
            have b37905 := hb (x 12 11)
            clear * - r37903 b37904 b37905 d37898
            omega
          have d37906 : (x 15 12).toNat = 0 := by
            have r37907 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37908 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e37909 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b37910 := hb (x 12 3)
            have b37911 := hb (x 13 2)
            have b37912 := hb (x 14 13)
            have b37913 := hb (x 15 12)
            clear * - r37907 e37908 e37909 b37910 b37911 b37912 b37913 d37878 d37902
            omega
          have d37914 : (x 15 1 && x 15 12).toNat = 0 := by
            have r37915 := hand2 (x 15 1) (x 15 12)
            have b37916 := hb (x 15 12)
            have b37917 := hb (x 15 1 && x 15 12)
            clear * - r37915 b37916 b37917 d37906
            omega
          have d37918 : (x 14 13).toNat = 0 := by
            have r37919 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37920 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
            have e37921 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
            have b37922 := hb (x 12 3)
            have b37923 := hb (x 13 2)
            have b37924 := hb (x 14 13)
            have b37925 := hb (x 15 12)
            clear * - r37919 e37920 e37921 b37922 b37923 b37924 b37925 d37906 d37878 d37902
            omega
          have d37926 : (x 14 2 && x 14 13).toNat = 0 := by
            have r37927 := hand2 (x 14 2) (x 14 13)
            have b37928 := hb (x 14 13)
            have b37929 := hb (x 14 2 && x 14 13)
            clear * - r37927 b37928 b37929 d37918
            omega
          have d37930 : (x 12 4).toNat = 1 := by
            have r37931 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37932 := hb (x 12 4)
            have b37933 := hb (x 16 11)
            have b37934 := hb (x 15 1 && x 15 12)
            have b37935 := hb (x 14 2 && x 14 13)
            have b37936 := hb (x 13 3 && x 13 14)
            clear * - r37931 b37932 b37933 b37934 b37935 b37936 d37754 d37914 d37926 d37874
            omega
          have d37937 : (x 12 12).toNat = 1 := by
            have r37938 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
            have b37939 := hb (x 12 4)
            have b37940 := hb (x 12 12)
            clear * - r37938 b37939 b37940 d37930
            omega
          have d37941 : (x 11 13).toNat = 0 := by
            have r37942 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37943 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
            have e37944 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
            have b37945 := hb (x 9 3)
            have b37946 := hb (x 10 2)
            have b37947 := hb (x 11 13)
            have b37948 := hb (x 12 12)
            clear * - r37942 e37943 e37944 b37945 b37946 b37947 b37948 d37937
            omega
          have d37949 : (x 10 1 && x 10 14).toNat = 1 := by
            have r37950 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37951 := hb (x 9 2)
            have b37952 := hb (x 11 13)
            have b37953 := hb (x 10 1 && x 10 14)
            clear * - r37950 b37951 b37952 b37953 d37941 d37337
            omega
          have d37954 : (x 10 1).toNat = 1 := by
            have r37955 := hand1 (x 10 1) (x 10 14)
            have b37956 := hb (x 10 1)
            have b37957 := hb (x 10 1 && x 10 14)
            clear * - r37955 b37956 b37957 d37949
            omega
          have d37958 : (x 11 14).toNat = 0 := by
            have r37959 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37960 := hb (x 10 1)
            have b37961 := hb (x 11 14)
            clear * - r37959 b37960 b37961 d37954
            omega
          have d37962 : (x 11 3 && x 11 14).toNat = 0 := by
            have r37963 := hand2 (x 11 3) (x 11 14)
            have b37964 := hb (x 11 14)
            have b37965 := hb (x 11 3 && x 11 14)
            clear * - r37963 b37964 b37965 d37958
            omega
          have d37966 : (x 11 2).toNat = 0 := by
            have r37967 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
            have b37968 := hb (x 11 2)
            have b37969 := hb (x 11 14)
            clear * - r37967 b37968 b37969 d37958
            omega
          have d37970 : (x 11 10).toNat = 0 := by
            have r37971 : (x 11 10).toNat ≤ (x 11 2).toNat := himp _ _ (hp10 11)
            have b37972 := hb (x 11 2)
            have b37973 := hb (x 11 10)
            clear * - r37971 b37972 b37973 d37966
            omega
          have d37974 : (x 10 1 && x 10 11).toNat = 1 := by
            have r37975 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b37976 := hb (x 6 5)
            have b37977 := hb (x 11 10)
            have b37978 := hb (x 10 1 && x 10 11)
            have b37979 := hb (x 9 2 && x 9 12)
            have b37980 := hb (x 8 3 && x 8 13)
            have b37981 := hb (x 7 4 && x 7 14)
            clear * - r37975 b37976 b37977 b37978 b37979 b37980 b37981 d37970 d37349 d37842 d37238 d37266
            omega
          have d37982 : (x 10 11).toNat = 1 := by
            have r37983 := hand2 (x 10 1) (x 10 11)
            have b37984 := hb (x 10 11)
            have b37985 := hb (x 10 1 && x 10 11)
            clear * - r37983 b37984 b37985 d37974
            omega
          have d37986 : (x 10 3).toNat = 1 := by
            have r37987 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
            have b37988 := hb (x 10 3)
            have b37989 := hb (x 10 11)
            clear * - r37987 b37988 b37989 d37982
            omega
          have d37990 : (x 13 12).toNat = 0 := by
            have r37991 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e37992 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e37993 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b37994 := hb (x 10 3)
            have b37995 := hb (x 11 2)
            have b37996 := hb (x 12 13)
            have b37997 := hb (x 13 12)
            clear * - r37991 e37992 e37993 b37994 b37995 b37996 b37997 d37966 d37986
            omega
          have d37998 : (x 13 1 && x 13 12).toNat = 0 := by
            have r37999 := hand2 (x 13 1) (x 13 12)
            have b38000 := hb (x 13 12)
            have b38001 := hb (x 13 1 && x 13 12)
            clear * - r37999 b38000 b38001 d37990
            omega
          have d38002 : (x 12 13).toNat = 0 := by
            have r38003 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38004 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
            have e38005 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
            have b38006 := hb (x 10 3)
            have b38007 := hb (x 11 2)
            have b38008 := hb (x 12 13)
            have b38009 := hb (x 13 12)
            clear * - r38003 e38004 e38005 b38006 b38007 b38008 b38009 d37990 d37966 d37986
            omega
          have d38010 : (x 12 2 && x 12 13).toNat = 0 := by
            have r38011 := hand2 (x 12 2) (x 12 13)
            have b38012 := hb (x 12 13)
            have b38013 := hb (x 12 2 && x 12 13)
            clear * - r38011 b38012 b38013 d38002
            omega
          have d38014 : (x 14 11).toNat = 1 := by
            have r38015 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38016 := hb (x 10 4)
            have b38017 := hb (x 14 11)
            have b38018 := hb (x 13 1 && x 13 12)
            have b38019 := hb (x 12 2 && x 12 13)
            have b38020 := hb (x 11 3 && x 11 14)
            clear * - r38015 b38016 b38017 b38018 b38019 b38020 d37998 d38010 d37962 d37558
            omega
          have d38021 : (x 14 3).toNat = 1 := by
            have r38022 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
            have b38023 := hb (x 14 3)
            have b38024 := hb (x 14 11)
            clear * - r38022 b38023 b38024 d38014
            omega
          have d38025 : (x 17 12).toNat = 0 := by
            have r38026 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38027 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e38028 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b38029 := hb (x 14 3)
            have b38030 := hb (x 15 2)
            have b38031 := hb (x 16 13)
            have b38032 := hb (x 17 12)
            clear * - r38026 e38027 e38028 b38029 b38030 b38031 b38032 d38021
            omega
          have d38033 : (x 16 13).toNat = 0 := by
            have r38034 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38035 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e38036 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b38037 := hb (x 14 3)
            have b38038 := hb (x 15 2)
            have b38039 := hb (x 16 13)
            have b38040 := hb (x 17 12)
            clear * - r38034 e38035 e38036 b38037 b38038 b38039 b38040 d38025 d38021
            omega
          have d38041 : (x 15 2).toNat = 0 := by
            have r38042 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e38043 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
            have e38044 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
            have b38045 := hb (x 14 3)
            have b38046 := hb (x 15 2)
            have b38047 := hb (x 16 13)
            have b38048 := hb (x 17 12)
            clear * - r38042 e38043 e38044 b38045 b38046 b38047 b38048 d38025 d38033 d38021
            omega
          have d38049 : (x 15 10).toNat = 0 := by
            have r38050 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
            have b38051 := hb (x 15 2)
            have b38052 := hb (x 15 10)
            clear * - r38050 b38051 b38052 d38041
            omega
          have d38053 : (x 12 3 && x 12 13).toNat = 0 := by
            have r38054 := hand2 (x 12 3) (x 12 13)
            have b38055 := hb (x 12 13)
            have b38056 := hb (x 12 3 && x 12 13)
            clear * - r38054 b38055 b38056 d38002
            omega
          have d38057 : (x 14 1 && x 14 11).toNat = 1 := by
            have r38058 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38059 := hb (x 10 5)
            have b38060 := hb (x 15 10)
            have b38061 := hb (x 14 1 && x 14 11)
            have b38062 := hb (x 13 2 && x 13 12)
            have b38063 := hb (x 12 3 && x 12 13)
            have b38064 := hb (x 11 4 && x 11 14)
            clear * - r38058 b38059 b38060 b38061 b38062 b38063 b38064 d38049 d37882 d38053 d37317 d37333
            omega
          have d38065 : (x 14 1).toNat = 1 := by
            have r38066 := hand1 (x 14 1) (x 14 11)
            have b38067 := hb (x 14 1)
            have b38068 := hb (x 14 1 && x 14 11)
            clear * - r38066 b38067 b38068 d38057
            omega
          have d38069 : (x 15 14).toNat = 0 := by
            have r38070 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38071 := hb (x 14 1)
            have b38072 := hb (x 15 14)
            clear * - r38070 b38071 b38072 d38065
            omega
          have d38073 : (x 15 1 && x 15 14).toNat = 0 := by
            have r38074 := hand2 (x 15 1) (x 15 14)
            have b38075 := hb (x 15 14)
            have b38076 := hb (x 15 1 && x 15 14)
            clear * - r38074 b38075 b38076 d38069
            omega
          have d38077 : (x 14 2).toNat = 1 := by
            have r38078 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38079 := hb (x 14 2)
            have b38080 := hb (x 16 13)
            have b38081 := hb (x 15 1 && x 15 14)
            clear * - r38078 b38079 b38080 b38081 d38033 d38073
            omega
          have d38082 : (x 14 14).toNat = 1 := by
            have r38083 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
            have b38084 := hb (x 14 2)
            have b38085 := hb (x 14 14)
            clear * - r38083 b38084 b38085 d38077
            omega
          have d38086 : (x 13 1).toNat = 0 := by
            have r38087 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38088 := hb (x 13 1)
            have b38089 := hb (x 14 14)
            clear * - r38087 b38088 b38089 d38082
            omega
          have d38090 : (x 13 13).toNat = 0 := by
            have r38091 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
            have b38092 := hb (x 13 1)
            have b38093 := hb (x 13 13)
            clear * - r38091 b38092 b38093 d38086
            omega
          have d38094 : (x 12 1 && x 12 14).toNat = 1 := by
            have r38095 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38096 := hb (x 11 2)
            have b38097 := hb (x 13 13)
            have b38098 := hb (x 12 1 && x 12 14)
            clear * - r38095 b38096 b38097 b38098 d38090 d37966
            omega
          have d38099 : (x 12 14).toNat = 1 := by
            have r38100 := hand2 (x 12 1) (x 12 14)
            have b38101 := hb (x 12 14)
            have b38102 := hb (x 12 1 && x 12 14)
            clear * - r38100 b38101 b38102 d38094
            omega
          have d38103 : (x 11 1).toNat = 0 := by
            have r38104 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38105 := hb (x 11 1)
            have b38106 := hb (x 12 14)
            clear * - r38104 b38105 b38106 d38099
            omega
          have d38107 : (x 11 9).toNat = 0 := by
            have r38108 : (x 11 9).toNat ≤ (x 11 1).toNat := himp _ _ (hp9 11)
            have b38109 := hb (x 11 1)
            have b38110 := hb (x 11 9)
            clear * - r38108 b38109 b38110 d38103
            omega
          have d38111 : (x 10 1 && x 10 10).toNat = 1 := by
            have r38112 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b38113 := hb (x 5 6)
            have b38114 := hb (x 11 9)
            have b38115 := hb (x 10 1 && x 10 10)
            have b38116 := hb (x 9 2 && x 9 11)
            have b38117 := hb (x 8 3 && x 8 12)
            have b38118 := hb (x 7 4 && x 7 13)
            have b38119 := hb (x 6 5 && x 6 14)
            clear * - r38112 b38113 b38114 b38115 b38116 b38117 b38118 b38119 d38107 d37353 d37683 d37242 d37270 d37190
            omega
          have d38120 : (x 10 10).toNat = 1 := by
            have r38121 := hand2 (x 10 1) (x 10 10)
            have b38122 := hb (x 10 10)
            have b38123 := hb (x 10 1 && x 10 10)
            clear * - r38121 b38122 b38123 d38111
            omega
          have d38124 : (x 10 2).toNat = 1 := by
            have r38125 : (x 10 10).toNat ≤ (x 10 2).toNat := himp _ _ (hp10 10)
            have b38126 := hb (x 10 2)
            have b38127 := hb (x 10 10)
            clear * - r38125 b38126 b38127 d38120
            omega
          have r38128 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e38129 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e38130 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b38131 := hb (x 9 3)
          have b38132 := hb (x 10 2)
          have b38133 := hb (x 11 13)
          have b38134 := hb (x 12 12)
          linarith only [r38128, e38129, e38130, b38131, b38132, b38133, b38134, d37937, d37941, d38124]
      · have f38135 : (x 0 9).toNat = 1 := by rw [h35678]; rfl
        have d38136 : (x 1 8).toNat = 0 := by
          have r38137 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e38138 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e38139 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e38140 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e38141 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e38142 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e38143 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b38144 := hb (x (-6) 7)
          have b38145 := hb (x (-5) 6)
          have b38146 := hb (x (-4) 5)
          have b38147 := hb (x (-3) 4)
          have b38148 := hb (x (-2) 11)
          have b38149 := hb (x (-1) 10)
          have b38150 := hb (x 0 9)
          have b38151 := hb (x 1 8)
          clear * - r38137 e38138 e38139 e38140 e38141 e38142 e38143 b38144 b38145 b38146 b38147 b38148 b38149 b38150 b38151 f38135 d35028 d35044
          omega
        have d38152 : (x (-3) 4).toNat = 0 := by
          have r38153 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e38154 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e38155 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e38156 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e38157 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e38158 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e38159 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have b38160 := hb (x (-6) 7)
          have b38161 := hb (x (-5) 6)
          have b38162 := hb (x (-4) 5)
          have b38163 := hb (x (-3) 4)
          have b38164 := hb (x (-2) 11)
          have b38165 := hb (x (-1) 10)
          have b38166 := hb (x 0 9)
          have b38167 := hb (x 1 8)
          clear * - r38153 e38154 e38155 e38156 e38157 e38158 e38159 b38160 b38161 b38162 b38163 b38164 b38165 b38166 b38167 d38136 f38135 d35028 d35044
          omega
        have d38168 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
          have r38169 := hand1 (x (-3) 4) (x (-3) 14)
          have b38170 := hb (x (-3) 4)
          have b38171 := hb (x (-3) 4 && x (-3) 14)
          clear * - r38169 b38170 b38171 d38152
          omega
        have d38172 : (x (-4) 5).toNat = 1 := by
          have r38173 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b38174 := hb (x (-4) 5)
          have b38175 := hb (x 1 10)
          have b38176 := hb (x 0 1 && x 0 11)
          have b38177 := hb (x (-1) 2 && x (-1) 12)
          have b38178 := hb (x (-2) 3 && x (-2) 13)
          have b38179 := hb (x (-3) 4 && x (-3) 14)
          clear * - r38173 b38174 b38175 b38176 b38177 b38178 b38179 g8 d34818 d35024 d35040 d38168
          omega
        have r38180 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38181 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e38182 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e38183 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e38184 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e38185 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e38186 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b38187 := hb (x (-6) 7)
        have b38188 := hb (x (-5) 6)
        have b38189 := hb (x (-4) 5)
        have b38190 := hb (x (-3) 4)
        have b38191 := hb (x (-2) 11)
        have b38192 := hb (x (-1) 10)
        have b38193 := hb (x 0 9)
        have b38194 := hb (x 1 8)
        linarith only [r38180, e38181, e38182, e38183, e38184, e38185, e38186, b38187, b38188, b38189, b38190, b38191, b38192, b38193, b38194, d38136, f38135, d35028, d35044, d38152, d38172]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a110 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 1).toNat = 0)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 2 13).toNat = 0)
    (g5 : (x 4 10).toNat = 0)
    (g6 : (x 3 1 && x 3 11).toNat = 0)
    (g7 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d38334 : (x 0 13).toNat = 0 := by
    have r38335 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b38336 := hb (x 0 1)
    have b38337 := hb (x 0 13)
    clear * - r38335 b38336 b38337 g2
    omega
  have d38338 : (x (-2) 2).toNat = 1 := by
    have r38339 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b38340 := hb (x (-2) 2)
    have b38341 := hb (x 0 13)
    have b38342 := hb (x (-1) 1 && x (-1) 14)
    clear * - r38339 b38340 b38341 b38342 d38334 g7
    omega
  have d38343 : (x 0 12).toNat = 0 := by
    have r38344 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e38345 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e38346 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b38347 := hb (x (-3) 3)
    have b38348 := hb (x (-2) 2)
    have b38349 := hb (x (-1) 13)
    have b38350 := hb (x 0 12)
    clear * - r38344 e38345 e38346 b38347 b38348 b38349 b38350 g1 d38338
    omega
  have d38351 : (x 0 4).toNat = 0 := by
    have r38352 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b38353 := hb (x 0 4)
    have b38354 := hb (x 0 12)
    clear * - r38352 b38353 b38354 d38343
    omega
  have d38355 : (x 0 4 && x 0 14).toNat = 0 := by
    have r38356 := hand1 (x 0 4) (x 0 14)
    have b38357 := hb (x 0 4)
    have b38358 := hb (x 0 4 && x 0 14)
    clear * - r38356 b38357 b38358 d38351
    omega
  have r38359 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e38360 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
  have e38361 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
  have r38362 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e38363 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
  have e38364 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
  have r38365 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38366 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38367 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38368 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38369 := hand1 (x 2 2) (x 2 12)
  have r38370 := hand2 (x 2 2) (x 2 12)
  have r38371 := hand1 (x 1 3) (x 1 13)
  have r38372 := hand2 (x 1 3) (x 1 13)
  have r38373 := hand1 (x 1 1) (x 1 14)
  have r38374 := hand2 (x 2 1) (x 2 14)
  linarith only [r38359, e38360, e38361, r38362, e38363, e38364, r38365, r38366, r38367, r38368, r38369, r38370, r38371, r38372, r38373, r38374, g0, g3, g4, g5, g6, d38355]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a1110_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 9).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 5).toNat = 0)
    (g3 : (x 0 11).toNat = 1)
    (g4 : (x 1 10).toNat = 0)
    (g5 : (x 2 9).toNat = 0)
    (g6 : (x 3 8).toNat = 0)
    (g7 : (x 5 9).toNat = 0)
    (g8 : (x 3 4 && x 3 8).toNat = 0)
    (g9 : (x 2 5 && x 2 9).toNat = 0)
    (g10 : (x 1 6 && x 1 10).toNat = 0)
    (g11 : (x 0 7 && x 0 11).toNat = 0)
    (g12 : (x 6 1 && x 6 8).toNat = 0)
    (g13 : (x 5 2 && x 5 9).toNat = 0)
    (g14 : (x 4 3 && x 4 10).toNat = 0)
    (g15 : (x 3 4 && x 3 11).toNat = 0)
    (g16 : (x 2 5 && x 2 12).toNat = 0)
    (g17 : (x 1 6 && x 1 13).toNat = 0)
    (g18 : (x 0 7 && x 0 14).toNat = 0)
    (g19 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g20 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g21 : (x 4 1 && x 4 10).toNat = 0)
    (g22 : (x 3 2 && x 3 11).toNat = 0)
    (g23 : (x 2 3 && x 2 12).toNat = 0)
    (g24 : (x 1 4 && x 1 13).toNat = 0)
    (g25 : (x 3 2 && x 3 12).toNat = 0)
    (g26 : (x 2 3 && x 2 13).toNat = 0)
    (g27 : (x 1 4 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d38816 : (x 0 5 && x 0 14).toNat = 0 := by
    have r38817 := hand1 (x 0 5) (x 0 14)
    have b38818 := hb (x 0 5)
    have b38819 := hb (x 0 5 && x 0 14)
    clear * - r38817 b38818 b38819 g2
    omega
  have d38820 : (x (-1) 6).toNat = 1 := by
    have r38821 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b38822 := hb (x (-1) 6)
    have b38823 := hb (x 5 9)
    have b38824 := hb (x 4 1 && x 4 10)
    have b38825 := hb (x 3 2 && x 3 11)
    have b38826 := hb (x 2 3 && x 2 12)
    have b38827 := hb (x 1 4 && x 1 13)
    have b38828 := hb (x 0 5 && x 0 14)
    clear * - r38821 b38822 b38823 b38824 b38825 b38826 b38827 b38828 g7 g21 g22 g23 g24 d38816
    omega
  have d38829 : (x (-1) 14).toNat = 1 := by
    have r38830 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b38831 := hb (x (-1) 6)
    have b38832 := hb (x (-1) 14)
    clear * - r38830 b38831 b38832 d38820
    omega
  have d38833 : (x (-2) 1).toNat = 0 := by
    have r38834 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b38835 := hb (x (-2) 1)
    have b38836 := hb (x (-1) 14)
    clear * - r38834 b38835 b38836 d38829
    omega
  have d38837 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r38838 := hand1 (x (-2) 1) (x (-2) 14)
    have b38839 := hb (x (-2) 1)
    have b38840 := hb (x (-2) 1 && x (-2) 14)
    clear * - r38838 b38839 b38840 d38833
    omega
  have d38841 : (x (-3) 2).toNat = 1 := by
    have r38842 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b38843 := hb (x (-3) 2)
    have b38844 := hb (x (-1) 13)
    have b38845 := hb (x (-2) 1 && x (-2) 14)
    clear * - r38842 b38843 b38844 b38845 g1 d38837
    omega
  have d38846 : (x (-3) 14).toNat = 1 := by
    have r38847 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b38848 := hb (x (-3) 2)
    have b38849 := hb (x (-3) 14)
    clear * - r38847 b38848 b38849 d38841
    omega
  have d38850 : (x (-1) 12).toNat = 0 := by
    have r38851 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e38852 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e38853 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b38854 := hb (x (-4) 3)
    have b38855 := hb (x (-3) 2)
    have b38856 := hb (x (-2) 13)
    have b38857 := hb (x (-1) 12)
    clear * - r38851 e38852 e38853 b38854 b38855 b38856 b38857 d38841
    omega
  have d38858 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
    have r38859 := hand2 (x (-1) 8) (x (-1) 12)
    have b38860 := hb (x (-1) 12)
    have b38861 := hb (x (-1) 8 && x (-1) 12)
    clear * - r38859 b38860 b38861 d38850
    omega
  have d38862 : (x (-2) 13).toNat = 0 := by
    have r38863 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e38864 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e38865 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b38866 := hb (x (-4) 3)
    have b38867 := hb (x (-3) 2)
    have b38868 := hb (x (-2) 13)
    have b38869 := hb (x (-1) 12)
    clear * - r38863 e38864 e38865 b38866 b38867 b38868 b38869 d38850 d38841
    omega
  have d38870 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
    have r38871 := hand2 (x (-2) 9) (x (-2) 13)
    have b38872 := hb (x (-2) 13)
    have b38873 := hb (x (-2) 9 && x (-2) 13)
    clear * - r38871 b38872 b38873 d38862
    omega
  have d38874 : (x (-4) 3).toNat = 0 := by
    have r38875 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e38876 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e38877 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b38878 := hb (x (-4) 3)
    have b38879 := hb (x (-3) 2)
    have b38880 := hb (x (-2) 13)
    have b38881 := hb (x (-1) 12)
    clear * - r38875 e38876 e38877 b38878 b38879 b38880 b38881 d38850 d38862 d38841
    omega
  have d38882 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
    have r38883 := hand1 (x (-4) 3) (x (-4) 12)
    have b38884 := hb (x (-4) 3)
    have b38885 := hb (x (-4) 3 && x (-4) 12)
    clear * - r38883 b38884 b38885 d38874
    omega
  have d38886 : (x (-4) 11).toNat = 0 := by
    have r38887 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b38888 := hb (x (-4) 3)
    have b38889 := hb (x (-4) 11)
    clear * - r38887 b38888 b38889 d38874
    omega
  have d38890 : (x (-2) 9).toNat = 0 := by
    have r38891 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
    have b38892 := hb (x (-2) 1)
    have b38893 := hb (x (-2) 9)
    clear * - r38891 b38892 b38893 d38833
    omega
  have r38894 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38895 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e38896 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
  have e38897 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
  have e38898 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
  have e38899 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
  have e38900 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
  have e38901 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
  have r38902 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e38903 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
  have e38904 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
  have e38905 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
  have e38906 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
  have e38907 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
  have e38908 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
  have r38909 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e38910 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
  have e38911 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
  have r38912 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e38913 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
  have e38914 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
  have r38915 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38916 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38917 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38918 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r38919 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
  have r38920 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
  have r38921 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
  have r38922 := hand2 (x 5 2) (x 5 6)
  have r38923 := hand2 (x 4 3) (x 4 7)
  have r38924 := hand1 (x (-5) 4) (x (-5) 13)
  have r38925 := hand1 (x (-6) 5) (x (-6) 14)
  have r38926 := hand2 (x 4 1) (x 4 11)
  have r38927 := hand1 (x 10 1) (x 10 12)
  have r38928 := hand1 (x 9 2) (x 9 13)
  have r38929 := hand1 (x 8 3) (x 8 14)
  linarith only [r38894, r38895, e38896, e38897, e38898, e38899, e38900, e38901, r38902, e38903, e38904, e38905, e38906, e38907, e38908, r38909, e38910, e38911, r38912, e38913, e38914, r38915, r38916, r38917, r38918, r38919, r38920, r38921, r38922, r38923, r38924, r38925, r38926, r38927, r38928, r38929, d38886, d38846, d38890, d38862, g0, d38850, g2, g3, g4, g5, g6, g8, g9, g10, g11, d38858, d38870, g12, g13, g14, g15, g16, g17, g18, g19, g20, d38882, g25, g26, g27]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a1110 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 9).toNat = 0)
    (g1 : (x (-1) 13).toNat = 0)
    (g2 : (x 0 5).toNat = 0)
    (g3 : (x 0 11).toNat = 1)
    (g4 : (x 1 10).toNat = 0)
    (g5 : (x 2 9).toNat = 0)
    (g6 : (x 3 8).toNat = 0)
    (g7 : (x 5 9).toNat = 0)
    (g8 : (x 3 4 && x 3 8).toNat = 0)
    (g9 : (x 2 5 && x 2 9).toNat = 0)
    (g10 : (x 1 6 && x 1 10).toNat = 0)
    (g11 : (x 0 7 && x 0 11).toNat = 0)
    (g12 : (x 6 1 && x 6 8).toNat = 0)
    (g13 : (x 5 2 && x 5 9).toNat = 0)
    (g14 : (x 4 3 && x 4 10).toNat = 0)
    (g15 : (x 3 4 && x 3 11).toNat = 0)
    (g16 : (x 2 5 && x 2 12).toNat = 0)
    (g17 : (x 1 6 && x 1 13).toNat = 0)
    (g18 : (x 0 7 && x 0 14).toNat = 0)
    (g19 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g20 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g21 : (x 4 1 && x 4 10).toNat = 0)
    (g22 : (x 3 2 && x 3 11).toNat = 0)
    (g23 : (x 2 3 && x 2 12).toNat = 0)
    (g24 : (x 1 4 && x 1 13).toNat = 0)
    (g25 : (x 3 2 && x 3 12).toNat = 0)
    (g26 : (x 2 3 && x 2 13).toNat = 0)
    (g27 : (x 1 4 && x 1 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a1110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27
