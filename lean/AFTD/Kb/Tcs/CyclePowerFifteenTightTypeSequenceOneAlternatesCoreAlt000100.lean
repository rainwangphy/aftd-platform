import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt000100

Topic: combinatorics   Node: 06935e2214b7

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 109 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt000100_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-7) 7).toNat = 0)
    (g1 : (x (-6) 6).toNat = 0)
    (g2 : (x (-5) 5).toNat = 0)
    (g3 : (x (-4) 4).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 3).toNat = 0)
    (g6 : (x (-2) 5).toNat = 0)
    (g7 : (x (-2) 9).toNat = 0)
    (g8 : (x (-2) 10).toNat = 0)
    (g9 : (x (-2) 11).toNat = 0)
    (g10 : (x (-2) 13).toNat = 0)
    (g11 : (x (-1) 2).toNat = 1)
    (g12 : (x (-1) 9).toNat = 0)
    (g13 : (x 0 1).toNat = 0)
    (g14 : (x 0 2).toNat = 0)
    (g15 : (x 0 3).toNat = 0)
    (g16 : (x 0 4).toNat = 0)
    (g17 : (x 0 5).toNat = 0)
    (g18 : (x 0 6).toNat = 0)
    (g19 : (x 0 8).toNat = 1)
    (g20 : (x 0 9).toNat = 0)
    (g21 : (x 0 10).toNat = 0)
    (g22 : (x 0 11).toNat = 0)
    (g23 : (x 0 13).toNat = 0)
    (g24 : (x 1 2).toNat = 0)
    (g25 : (x 1 4).toNat = 0)
    (g26 : (x 1 5).toNat = 0)
    (g27 : (x 1 9).toNat = 0)
    (g28 : (x 1 10).toNat = 0)
    (g29 : (x 1 13).toNat = 0)
    (g30 : (x 1 14).toNat = 1)
    (g31 : (x 2 1).toNat = 1)
    (g32 : (x 2 13).toNat = 1)
    (g33 : (x 3 2).toNat = 0)
    (g34 : (x 3 4).toNat = 0)
    (g35 : (x 3 6).toNat = 0)
    (g36 : (x 3 10).toNat = 0)
    (g37 : (x 3 12).toNat = 0)
    (g38 : (x 3 9 && x 3 12).toNat = 0)
    (g39 : (x (-4) 4 && x (-4) 8).toNat = 0)
    (g40 : (x (-5) 5 && x (-5) 9).toNat = 0)
    (g41 : (x (-6) 6 && x (-6) 10).toNat = 0)
    (g42 : (x (-7) 7 && x (-7) 11).toNat = 0)
    (g43 : (x 3 2 && x 3 6).toNat = 0)
    (g44 : (x 1 4 && x 1 8).toNat = 0)
    (g45 : (x 0 5 && x 0 9).toNat = 0)
    (g46 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g47 : (x 3 4 && x 3 8).toNat = 0)
    (g48 : (x 1 6 && x 1 10).toNat = 0)
    (g49 : (x 0 7 && x 0 11).toNat = 0)
    (g50 : (x (-2) 9 && x (-2) 13).toNat = 0)
    (g51 : (x 0 1 && x 0 6).toNat = 0)
    (g52 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g53 : (x 1 2 && x 1 7).toNat = 0)
    (g54 : (x 0 3 && x 0 8).toNat = 0)
    (g55 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g56 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g57 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g58 : (x 3 6 && x 3 11).toNat = 0)
    (g59 : (x 1 8 && x 1 13).toNat = 0)
    (g60 : (x 0 9 && x 0 14).toNat = 0)
    (g61 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g62 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g63 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g64 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g65 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g66 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g67 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g68 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g69 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g70 : (x 0 1 && x 0 8).toNat = 0)
    (g71 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g72 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g73 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g74 : (x 3 4 && x 3 11).toNat = 0)
    (g75 : (x 1 6 && x 1 13).toNat = 0)
    (g76 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g77 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g78 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g79 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g80 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g81 : (x 0 1 && x 0 10).toNat = 0)
    (g82 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g83 : (x 3 2 && x 3 11).toNat = 0)
    (g84 : (x 1 4 && x 1 13).toNat = 0)
    (g85 : (x 0 5 && x 0 14).toNat = 0)
    (g86 : (x 3 3 && x 3 12).toNat = 0)
    (g87 : (x 1 5 && x 1 14).toNat = 0)
    (g88 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g89 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g90 : (x 1 2 && x 1 12).toNat = 0)
    (g91 : (x 0 3 && x 0 13).toNat = 0)
    (g92 : (x 1 3 && x 1 13).toNat = 0)
    (g93 : (x 0 4 && x 0 14).toNat = 0)
    (g94 : (x 3 2 && x 3 12).toNat = 0)
    (g95 : (x 1 4 && x 1 14).toNat = 0)
    (g96 : (x 3 4 && x 3 14).toNat = 0)
    (g97 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g98 : (x 0 1 && x 0 12).toNat = 0)
    (g99 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g100 : (x 1 1 && x 1 12).toNat = 0)
    (g101 : (x 0 2 && x 0 13).toNat = 0)
    (g102 : (x 1 2 && x 1 13).toNat = 0)
    (g103 : (x 0 3 && x 0 14).toNat = 0)
    (g104 : (x 3 1 && x 3 12).toNat = 0)
    (g105 : (x 3 2 && x 3 13).toNat = 0)
    (g106 : (x 3 3 && x 3 14).toNat = 0)
    (g107 : (x (-2) 1 && x (-2) 14).toNat = 0)
    (g108 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h22828 : x 0 7
  · have f22829 : (x 0 7).toNat = 0 := by rw [h22828]; rfl
    have d22830 : (x 0 7 && x 0 14).toNat = 0 := by
      have r22831 := hand1 (x 0 7) (x 0 14)
      have b22832 := hb (x 0 7)
      have b22833 := hb (x 0 7 && x 0 14)
      clear * - r22831 b22832 b22833 f22829
      omega
    cases h22834 : x 0 12
    · have f22835 : (x 0 12).toNat = 0 := by rw [h22834]; rfl
      cases h22836 : x (-1) 1
      · have f22837 : (x (-1) 1).toNat = 0 := by rw [h22836]; rfl
        have d22838 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
          have r22839 := hand1 (x (-1) 1) (x (-1) 14)
          have b22840 := hb (x (-1) 1)
          have b22841 := hb (x (-1) 1 && x (-1) 14)
          clear * - r22839 b22840 b22841 f22837
          omega
        have d22842 : (x (-1) 13).toNat = 0 := by
          have r22843 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
          have b22844 := hb (x (-1) 1)
          have b22845 := hb (x (-1) 13)
          clear * - r22843 b22844 b22845 f22837
          omega
        have d22846 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
          have r22847 := hand2 (x (-1) 2) (x (-1) 13)
          have b22848 := hb (x (-1) 13)
          have b22849 := hb (x (-1) 2 && x (-1) 13)
          clear * - r22847 b22848 b22849 d22842
          omega
        have d22850 : (x (-2) 2).toNat = 1 := by
          have r22851 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22852 := hb (x (-2) 2)
          have b22853 := hb (x 0 13)
          have b22854 := hb (x (-1) 1 && x (-1) 14)
          clear * - r22851 b22852 b22853 b22854 g23 d22838
          omega
        have d22855 : (x (-2) 14).toNat = 1 := by
          have r22856 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
          have b22857 := hb (x (-2) 2)
          have b22858 := hb (x (-2) 14)
          clear * - r22856 b22857 b22858 d22850
          omega
        have d22859 : (x (-3) 1).toNat = 0 := by
          have r22860 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22861 := hb (x (-3) 1)
          have b22862 := hb (x (-2) 14)
          clear * - r22860 b22861 b22862 d22855
          omega
        have d22863 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
          have r22864 := hand1 (x (-3) 1) (x (-3) 14)
          have b22865 := hb (x (-3) 1)
          have b22866 := hb (x (-3) 1 && x (-3) 14)
          clear * - r22864 b22865 b22866 d22859
          omega
        have d22867 : (x (-3) 13).toNat = 0 := by
          have r22868 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b22869 := hb (x (-3) 1)
          have b22870 := hb (x (-3) 13)
          clear * - r22868 b22869 b22870 d22859
          omega
        have d22871 : (x (-3) 2).toNat = 1 := by
          have r22872 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22873 := hb (x (-3) 2)
          have b22874 := hb (x (-1) 13)
          have b22875 := hb (x (-2) 1 && x (-2) 14)
          clear * - r22872 b22873 b22874 b22875 d22842 g107
          omega
        have d22876 : (x (-3) 14).toNat = 1 := by
          have r22877 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b22878 := hb (x (-3) 2)
          have b22879 := hb (x (-3) 14)
          clear * - r22877 b22878 b22879 d22871
          omega
        have d22880 : (x (-4) 1).toNat = 0 := by
          have r22881 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22882 := hb (x (-4) 1)
          have b22883 := hb (x (-3) 14)
          clear * - r22881 b22882 b22883 d22876
          omega
        have d22884 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
          have r22885 := hand1 (x (-4) 1) (x (-4) 14)
          have b22886 := hb (x (-4) 1)
          have b22887 := hb (x (-4) 1 && x (-4) 14)
          clear * - r22885 b22886 b22887 d22880
          omega
        have d22888 : (x (-4) 13).toNat = 0 := by
          have r22889 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b22890 := hb (x (-4) 1)
          have b22891 := hb (x (-4) 13)
          clear * - r22889 b22890 b22891 d22880
          omega
        have d22892 : (x (-4) 2).toNat = 1 := by
          have r22893 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22894 := hb (x (-4) 2)
          have b22895 := hb (x (-2) 13)
          have b22896 := hb (x (-3) 1 && x (-3) 14)
          clear * - r22893 b22894 b22895 b22896 g10 d22863
          omega
        have d22897 : (x (-5) 2).toNat = 1 := by
          have r22898 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22899 := hb (x (-5) 2)
          have b22900 := hb (x (-3) 13)
          have b22901 := hb (x (-4) 1 && x (-4) 14)
          clear * - r22898 b22899 b22900 b22901 d22867 d22884
          omega
        have d22902 : (x (-1) 12).toNat = 0 := by
          have r22903 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22904 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e22905 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b22906 := hb (x (-4) 3)
          have b22907 := hb (x (-3) 2)
          have b22908 := hb (x (-2) 13)
          have b22909 := hb (x (-1) 12)
          clear * - r22903 e22904 e22905 b22906 b22907 b22908 b22909 g10 d22871
          omega
        have d22910 : (x (-1) 4).toNat = 0 := by
          have r22911 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b22912 := hb (x (-1) 4)
          have b22913 := hb (x (-1) 12)
          clear * - r22911 b22912 b22913 d22902
          omega
        have d22914 : (x (-2) 12).toNat = 0 := by
          have r22915 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22916 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e22917 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b22918 := hb (x (-5) 3)
          have b22919 := hb (x (-4) 2)
          have b22920 := hb (x (-3) 13)
          have b22921 := hb (x (-2) 12)
          clear * - r22915 e22916 e22917 b22918 b22919 b22920 b22921 d22867 d22892
          omega
        have d22922 : (x (-2) 4).toNat = 0 := by
          have r22923 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
          have b22924 := hb (x (-2) 4)
          have b22925 := hb (x (-2) 12)
          clear * - r22923 b22924 b22925 d22914
          omega
        have d22926 : (x (-3) 12).toNat = 0 := by
          have r22927 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22928 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e22929 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b22930 := hb (x (-6) 3)
          have b22931 := hb (x (-5) 2)
          have b22932 := hb (x (-4) 13)
          have b22933 := hb (x (-3) 12)
          clear * - r22927 e22928 e22929 b22930 b22931 b22932 b22933 d22888 d22897
          omega
        have d22934 : (x (-3) 4).toNat = 0 := by
          have r22935 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b22936 := hb (x (-3) 4)
          have b22937 := hb (x (-3) 12)
          clear * - r22935 b22936 b22937 d22926
          omega
        have d22938 : (x 1 11).toNat = 1 := by
          have r22939 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22940 := hb (x (-3) 4)
          have b22941 := hb (x 1 11)
          have b22942 := hb (x 0 1 && x 0 12)
          have b22943 := hb (x (-1) 2 && x (-1) 13)
          have b22944 := hb (x (-2) 3 && x (-2) 14)
          clear * - r22939 b22940 b22941 b22942 b22943 b22944 g98 d22846 g99 d22934
          omega
        have d22945 : (x 1 3).toNat = 1 := by
          have r22946 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b22947 := hb (x 1 3)
          have b22948 := hb (x 1 11)
          clear * - r22946 b22947 b22948 d22938
          omega
        have d22949 : (x 4 12).toNat = 0 := by
          have r22950 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22951 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e22952 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b22953 := hb (x 1 3)
          have b22954 := hb (x 2 2)
          have b22955 := hb (x 3 13)
          have b22956 := hb (x 4 12)
          clear * - r22950 e22951 e22952 b22953 b22954 b22955 b22956 d22945
          omega
        have d22957 : (x 4 1 && x 4 12).toNat = 0 := by
          have r22958 := hand2 (x 4 1) (x 4 12)
          have b22959 := hb (x 4 12)
          have b22960 := hb (x 4 1 && x 4 12)
          clear * - r22958 b22959 b22960 d22949
          omega
        have d22961 : (x 4 4).toNat = 0 := by
          have r22962 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b22963 := hb (x 4 4)
          have b22964 := hb (x 4 12)
          clear * - r22962 b22963 b22964 d22949
          omega
        have d22965 : (x 3 13).toNat = 0 := by
          have r22966 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22967 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e22968 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b22969 := hb (x 1 3)
          have b22970 := hb (x 2 2)
          have b22971 := hb (x 3 13)
          have b22972 := hb (x 4 12)
          clear * - r22966 e22967 e22968 b22969 b22970 b22971 b22972 d22949 d22945
          omega
        have d22973 : (x 2 2).toNat = 0 := by
          have r22974 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22975 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e22976 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b22977 := hb (x 1 3)
          have b22978 := hb (x 2 2)
          have b22979 := hb (x 3 13)
          have b22980 := hb (x 4 12)
          clear * - r22974 e22975 e22976 b22977 b22978 b22979 b22980 d22949 d22965 d22945
          omega
        have d22981 : (x 4 13).toNat = 1 := by
          have r22982 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22983 := hb (x 2 2)
          have b22984 := hb (x 4 13)
          have b22985 := hb (x 3 1 && x 3 14)
          clear * - r22982 b22983 b22984 b22985 g108 d22973
          omega
        have d22986 : (x 4 1).toNat = 1 := by
          have r22987 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b22988 := hb (x 4 1)
          have b22989 := hb (x 4 13)
          clear * - r22987 b22988 b22989 d22981
          omega
        have d22990 : (x 5 14).toNat = 0 := by
          have r22991 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22992 := hb (x 4 1)
          have b22993 := hb (x 5 14)
          clear * - r22991 b22992 b22993 d22986
          omega
        have d22994 : (x 5 1 && x 5 14).toNat = 0 := by
          have r22995 := hand2 (x 5 1) (x 5 14)
          have b22996 := hb (x 5 14)
          have b22997 := hb (x 5 1 && x 5 14)
          clear * - r22995 b22996 b22997 d22990
          omega
        have d22998 : (x 5 3 && x 5 14).toNat = 0 := by
          have r22999 := hand2 (x 5 3) (x 5 14)
          have b23000 := hb (x 5 14)
          have b23001 := hb (x 5 3 && x 5 14)
          clear * - r22999 b23000 b23001 d22990
          omega
        have d23002 : (x 5 2).toNat = 0 := by
          have r23003 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b23004 := hb (x 5 2)
          have b23005 := hb (x 5 14)
          clear * - r23003 b23004 b23005 d22990
          omega
        have d23006 : (x 5 2 && x 5 13).toNat = 0 := by
          have r23007 := hand1 (x 5 2) (x 5 13)
          have b23008 := hb (x 5 2)
          have b23009 := hb (x 5 2 && x 5 13)
          clear * - r23007 b23008 b23009 d23002
          omega
        have d23010 : (x 5 12).toNat = 0 := by
          have r23011 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23012 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e23013 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b23014 := hb (x 2 3)
          have b23015 := hb (x 3 2)
          have b23016 := hb (x 4 13)
          have b23017 := hb (x 5 12)
          clear * - r23011 e23012 e23013 b23014 b23015 b23016 b23017 d22981 g33
          omega
        have d23018 : (x 5 4).toNat = 0 := by
          have r23019 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b23020 := hb (x 5 4)
          have b23021 := hb (x 5 12)
          clear * - r23019 b23020 b23021 d23010
          omega
        have d23022 : (x 2 3).toNat = 0 := by
          have r23023 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23024 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e23025 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b23026 := hb (x 2 3)
          have b23027 := hb (x 3 2)
          have b23028 := hb (x 4 13)
          have b23029 := hb (x 5 12)
          clear * - r23023 e23024 e23025 b23026 b23027 b23028 b23029 d23010 d22981 g33
          omega
        have d23030 : (x 2 3 && x 2 14).toNat = 0 := by
          have r23031 := hand1 (x 2 3) (x 2 14)
          have b23032 := hb (x 2 3)
          have b23033 := hb (x 2 3 && x 2 14)
          clear * - r23031 b23032 b23033 d23022
          omega
        have d23034 : (x 5 11).toNat = 1 := by
          have r23035 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23036 := hb (x 1 4)
          have b23037 := hb (x 5 11)
          have b23038 := hb (x 4 1 && x 4 12)
          have b23039 := hb (x 3 2 && x 3 13)
          have b23040 := hb (x 2 3 && x 2 14)
          clear * - r23035 b23036 b23037 b23038 b23039 b23040 d22957 g105 d23030 g25
          omega
        have d23041 : (x 5 3).toNat = 1 := by
          have r23042 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b23043 := hb (x 5 3)
          have b23044 := hb (x 5 11)
          clear * - r23042 b23043 b23044 d23034
          omega
        have d23045 : (x 8 12).toNat = 0 := by
          have r23046 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23047 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e23048 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b23049 := hb (x 5 3)
          have b23050 := hb (x 6 2)
          have b23051 := hb (x 7 13)
          have b23052 := hb (x 8 12)
          clear * - r23046 e23047 e23048 b23049 b23050 b23051 b23052 d23041
          omega
        have d23053 : (x 8 1 && x 8 12).toNat = 0 := by
          have r23054 := hand2 (x 8 1) (x 8 12)
          have b23055 := hb (x 8 12)
          have b23056 := hb (x 8 1 && x 8 12)
          clear * - r23054 b23055 b23056 d23045
          omega
        have d23057 : (x 7 13).toNat = 0 := by
          have r23058 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23059 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e23060 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b23061 := hb (x 5 3)
          have b23062 := hb (x 6 2)
          have b23063 := hb (x 7 13)
          have b23064 := hb (x 8 12)
          clear * - r23058 e23059 e23060 b23061 b23062 b23063 b23064 d23045 d23041
          omega
        have d23065 : (x 7 2 && x 7 13).toNat = 0 := by
          have r23066 := hand2 (x 7 2) (x 7 13)
          have b23067 := hb (x 7 13)
          have b23068 := hb (x 7 2 && x 7 13)
          clear * - r23066 b23067 b23068 d23057
          omega
        have d23069 : (x 6 1 && x 6 14).toNat = 1 := by
          have r23070 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23071 := hb (x 5 2)
          have b23072 := hb (x 7 13)
          have b23073 := hb (x 6 1 && x 6 14)
          clear * - r23070 b23071 b23072 b23073 d23057 d23002
          omega
        have d23074 : (x 6 14).toNat = 1 := by
          have r23075 := hand2 (x 6 1) (x 6 14)
          have b23076 := hb (x 6 14)
          have b23077 := hb (x 6 1 && x 6 14)
          clear * - r23075 b23076 b23077 d23069
          omega
        have d23078 : (x 5 1).toNat = 0 := by
          have r23079 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23080 := hb (x 5 1)
          have b23081 := hb (x 6 14)
          clear * - r23079 b23080 b23081 d23074
          omega
        have d23082 : (x 5 13).toNat = 0 := by
          have r23083 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
          have b23084 := hb (x 5 1)
          have b23085 := hb (x 5 13)
          clear * - r23083 b23084 b23085 d23078
          omega
        have d23086 : (x 6 1).toNat = 1 := by
          have r23087 := hand1 (x 6 1) (x 6 14)
          have b23088 := hb (x 6 1)
          have b23089 := hb (x 6 1 && x 6 14)
          clear * - r23087 b23088 b23089 d23069
          omega
        have d23090 : (x 7 14).toNat = 0 := by
          have r23091 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23092 := hb (x 6 1)
          have b23093 := hb (x 7 14)
          clear * - r23091 b23092 b23093 d23086
          omega
        have d23094 : (x 7 1 && x 7 14).toNat = 0 := by
          have r23095 := hand2 (x 7 1) (x 7 14)
          have b23096 := hb (x 7 14)
          have b23097 := hb (x 7 1 && x 7 14)
          clear * - r23095 b23096 b23097 d23090
          omega
        have d23098 : (x 7 2).toNat = 0 := by
          have r23099 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b23100 := hb (x 7 2)
          have b23101 := hb (x 7 14)
          clear * - r23099 b23100 b23101 d23090
          omega
        have d23102 : (x 6 2).toNat = 0 := by
          have r23103 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23104 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e23105 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b23106 := hb (x 5 3)
          have b23107 := hb (x 6 2)
          have b23108 := hb (x 7 13)
          have b23109 := hb (x 8 12)
          clear * - r23103 e23104 e23105 b23106 b23107 b23108 b23109 d23045 d23057 d23041
          omega
        have d23110 : (x 6 2 && x 6 13).toNat = 0 := by
          have r23111 := hand1 (x 6 2) (x 6 13)
          have b23112 := hb (x 6 2)
          have b23113 := hb (x 6 2 && x 6 13)
          clear * - r23111 b23112 b23113 d23102
          omega
        have d23114 : (x 8 13).toNat = 1 := by
          have r23115 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23116 := hb (x 6 2)
          have b23117 := hb (x 8 13)
          have b23118 := hb (x 7 1 && x 7 14)
          clear * - r23115 b23116 b23117 b23118 d23094 d23102
          omega
        have d23119 : (x 8 1).toNat = 1 := by
          have r23120 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b23121 := hb (x 8 1)
          have b23122 := hb (x 8 13)
          clear * - r23120 b23121 b23122 d23114
          omega
        have d23123 : (x 9 14).toNat = 0 := by
          have r23124 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23125 := hb (x 8 1)
          have b23126 := hb (x 9 14)
          clear * - r23124 b23125 b23126 d23119
          omega
        have d23127 : (x 9 1 && x 9 14).toNat = 0 := by
          have r23128 := hand2 (x 9 1) (x 9 14)
          have b23129 := hb (x 9 14)
          have b23130 := hb (x 9 1 && x 9 14)
          clear * - r23128 b23129 b23130 d23123
          omega
        have d23131 : (x 9 2).toNat = 0 := by
          have r23132 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b23133 := hb (x 9 2)
          have b23134 := hb (x 9 14)
          clear * - r23132 b23133 b23134 d23123
          omega
        have d23135 : (x 9 12).toNat = 0 := by
          have r23136 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23137 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e23138 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b23139 := hb (x 6 3)
          have b23140 := hb (x 7 2)
          have b23141 := hb (x 8 13)
          have b23142 := hb (x 9 12)
          clear * - r23136 e23137 e23138 b23139 b23140 b23141 b23142 d23114 d23098
          omega
        have d23143 : (x 6 3).toNat = 0 := by
          have r23144 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23145 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e23146 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b23147 := hb (x 6 3)
          have b23148 := hb (x 7 2)
          have b23149 := hb (x 8 13)
          have b23150 := hb (x 9 12)
          clear * - r23144 e23145 e23146 b23147 b23148 b23149 b23150 d23135 d23114 d23098
          omega
        have d23151 : (x 6 3 && x 6 14).toNat = 0 := by
          have r23152 := hand1 (x 6 3) (x 6 14)
          have b23153 := hb (x 6 3)
          have b23154 := hb (x 6 3 && x 6 14)
          clear * - r23152 b23153 b23154 d23143
          omega
        have d23155 : (x 9 11).toNat = 1 := by
          have r23156 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23157 := hb (x 5 4)
          have b23158 := hb (x 9 11)
          have b23159 := hb (x 8 1 && x 8 12)
          have b23160 := hb (x 7 2 && x 7 13)
          have b23161 := hb (x 6 3 && x 6 14)
          clear * - r23156 b23157 b23158 b23159 b23160 b23161 d23053 d23065 d23151 d23018
          omega
        have d23162 : (x 9 3).toNat = 1 := by
          have r23163 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
          have b23164 := hb (x 9 3)
          have b23165 := hb (x 9 11)
          clear * - r23163 b23164 b23165 d23155
          omega
        have d23166 : (x 12 12).toNat = 0 := by
          have r23167 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23168 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e23169 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b23170 := hb (x 9 3)
          have b23171 := hb (x 10 2)
          have b23172 := hb (x 11 13)
          have b23173 := hb (x 12 12)
          clear * - r23167 e23168 e23169 b23170 b23171 b23172 b23173 d23162
          omega
        have d23174 : (x 11 13).toNat = 0 := by
          have r23175 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23176 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e23177 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b23178 := hb (x 9 3)
          have b23179 := hb (x 10 2)
          have b23180 := hb (x 11 13)
          have b23181 := hb (x 12 12)
          clear * - r23175 e23176 e23177 b23178 b23179 b23180 b23181 d23166 d23162
          omega
        have d23182 : (x 10 1 && x 10 14).toNat = 1 := by
          have r23183 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23184 := hb (x 9 2)
          have b23185 := hb (x 11 13)
          have b23186 := hb (x 10 1 && x 10 14)
          clear * - r23183 b23184 b23185 b23186 d23174 d23131
          omega
        have d23187 : (x 10 14).toNat = 1 := by
          have r23188 := hand2 (x 10 1) (x 10 14)
          have b23189 := hb (x 10 14)
          have b23190 := hb (x 10 1 && x 10 14)
          clear * - r23188 b23189 b23190 d23182
          omega
        have d23191 : (x 9 1).toNat = 0 := by
          have r23192 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23193 := hb (x 9 1)
          have b23194 := hb (x 10 14)
          clear * - r23192 b23193 b23194 d23187
          omega
        have d23195 : (x 9 13).toNat = 0 := by
          have r23196 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b23197 := hb (x 9 1)
          have b23198 := hb (x 9 13)
          clear * - r23196 b23197 b23198 d23191
          omega
        have d23199 : (x 8 1 && x 8 14).toNat = 1 := by
          have r23200 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23201 := hb (x 7 2)
          have b23202 := hb (x 9 13)
          have b23203 := hb (x 8 1 && x 8 14)
          clear * - r23200 b23201 b23202 b23203 d23195 d23098
          omega
        have d23204 : (x 8 14).toNat = 1 := by
          have r23205 := hand2 (x 8 1) (x 8 14)
          have b23206 := hb (x 8 14)
          have b23207 := hb (x 8 1 && x 8 14)
          clear * - r23205 b23206 b23207 d23199
          omega
        have d23208 : (x 7 1).toNat = 0 := by
          have r23209 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23210 := hb (x 7 1)
          have b23211 := hb (x 8 14)
          clear * - r23209 b23210 b23211 d23204
          omega
        have d23212 : (x 7 1 && x 7 12).toNat = 0 := by
          have r23213 := hand1 (x 7 1) (x 7 12)
          have b23214 := hb (x 7 1)
          have b23215 := hb (x 7 1 && x 7 12)
          clear * - r23213 b23214 b23215 d23208
          omega
        have d23216 : (x 8 11).toNat = 1 := by
          have r23217 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23218 := hb (x 4 4)
          have b23219 := hb (x 8 11)
          have b23220 := hb (x 7 1 && x 7 12)
          have b23221 := hb (x 6 2 && x 6 13)
          have b23222 := hb (x 5 3 && x 5 14)
          clear * - r23217 b23218 b23219 b23220 b23221 b23222 d23212 d23110 d22998 d22961
          omega
        have d23223 : (x 8 3).toNat = 1 := by
          have r23224 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b23225 := hb (x 8 3)
          have b23226 := hb (x 8 11)
          clear * - r23224 b23225 b23226 d23216
          omega
        have d23227 : (x 11 12).toNat = 0 := by
          have r23228 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23229 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e23230 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b23231 := hb (x 8 3)
          have b23232 := hb (x 9 2)
          have b23233 := hb (x 10 13)
          have b23234 := hb (x 11 12)
          clear * - r23228 e23229 e23230 b23231 b23232 b23233 b23234 d23131 d23223
          omega
        have d23235 : (x 10 13).toNat = 0 := by
          have r23236 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23237 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e23238 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b23239 := hb (x 8 3)
          have b23240 := hb (x 9 2)
          have b23241 := hb (x 10 13)
          have b23242 := hb (x 11 12)
          clear * - r23236 e23237 e23238 b23239 b23240 b23241 b23242 d23227 d23131 d23223
          omega
        have d23243 : (x 8 2).toNat = 1 := by
          have r23244 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23245 := hb (x 8 2)
          have b23246 := hb (x 10 13)
          have b23247 := hb (x 9 1 && x 9 14)
          clear * - r23244 b23245 b23246 b23247 d23235 d23127
          omega
        have d23248 : (x 10 12).toNat = 0 := by
          have r23249 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23250 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e23251 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b23252 := hb (x 7 3)
          have b23253 := hb (x 8 2)
          have b23254 := hb (x 9 13)
          have b23255 := hb (x 10 12)
          clear * - r23249 e23250 e23251 b23252 b23253 b23254 b23255 d23195 d23243
          omega
        have d23256 : (x 7 3).toNat = 0 := by
          have r23257 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23258 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e23259 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b23260 := hb (x 7 3)
          have b23261 := hb (x 8 2)
          have b23262 := hb (x 9 13)
          have b23263 := hb (x 10 12)
          clear * - r23257 e23258 e23259 b23260 b23261 b23262 b23263 d23248 d23195 d23243
          omega
        have d23264 : (x 7 11).toNat = 0 := by
          have r23265 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
          have b23266 := hb (x 7 3)
          have b23267 := hb (x 7 11)
          clear * - r23265 b23266 b23267 d23256
          omega
        have d23268 : (x 2 11).toNat = 0 := by
          have r23269 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
          have b23270 := hb (x 2 3)
          have b23271 := hb (x 2 11)
          clear * - r23269 b23270 b23271 d23022
          omega
        have d23272 : (x (-1) 3 && x (-1) 14).toNat = 1 := by
          have r23273 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23274 := hb (x (-2) 4)
          have b23275 := hb (x 2 11)
          have b23276 := hb (x 1 1 && x 1 12)
          have b23277 := hb (x 0 2 && x 0 13)
          have b23278 := hb (x (-1) 3 && x (-1) 14)
          clear * - r23273 b23274 b23275 b23276 b23277 b23278 d23268 g100 g101 d22922
          omega
        have d23279 : (x (-1) 3).toNat = 1 := by
          have r23280 := hand1 (x (-1) 3) (x (-1) 14)
          have b23281 := hb (x (-1) 3)
          have b23282 := hb (x (-1) 3 && x (-1) 14)
          clear * - r23280 b23281 b23282 d23272
          omega
        have d23283 : (x 2 12).toNat = 0 := by
          have r23284 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23285 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e23286 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b23287 := hb (x (-1) 3)
          have b23288 := hb (x 0 2)
          have b23289 := hb (x 1 13)
          have b23290 := hb (x 2 12)
          clear * - r23284 e23285 e23286 b23287 b23288 b23289 b23290 g29 g14 d23279
          omega
        have d23291 : (x 2 1 && x 2 12).toNat = 0 := by
          have r23292 := hand2 (x 2 1) (x 2 12)
          have b23293 := hb (x 2 12)
          have b23294 := hb (x 2 1 && x 2 12)
          clear * - r23292 b23293 b23294 d23283
          omega
        have d23295 : (x 3 11).toNat = 1 := by
          have r23296 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23297 := hb (x (-1) 4)
          have b23298 := hb (x 3 11)
          have b23299 := hb (x 2 1 && x 2 12)
          have b23300 := hb (x 1 2 && x 1 13)
          have b23301 := hb (x 0 3 && x 0 14)
          clear * - r23296 b23297 b23298 b23299 b23300 b23301 d23291 g102 g103 d22910
          omega
        have d23302 : (x 3 3).toNat = 1 := by
          have r23303 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b23304 := hb (x 3 3)
          have b23305 := hb (x 3 11)
          clear * - r23303 b23304 b23305 d23295
          omega
        have d23306 : (x 6 12).toNat = 0 := by
          have r23307 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23308 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e23309 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b23310 := hb (x 3 3)
          have b23311 := hb (x 4 2)
          have b23312 := hb (x 5 13)
          have b23313 := hb (x 6 12)
          clear * - r23307 e23308 e23309 b23310 b23311 b23312 b23313 d23082 d23302
          omega
        have d23314 : (x 6 1 && x 6 12).toNat = 0 := by
          have r23315 := hand2 (x 6 1) (x 6 12)
          have b23316 := hb (x 6 12)
          have b23317 := hb (x 6 1 && x 6 12)
          clear * - r23315 b23316 b23317 d23306
          omega
        have d23318 : (x 4 3 && x 4 14).toNat = 1 := by
          have r23319 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23320 := hb (x 3 4)
          have b23321 := hb (x 7 11)
          have b23322 := hb (x 6 1 && x 6 12)
          have b23323 := hb (x 5 2 && x 5 13)
          have b23324 := hb (x 4 3 && x 4 14)
          clear * - r23319 b23320 b23321 b23322 b23323 b23324 d23264 d23314 d23006 g34
          omega
        have d23325 : (x 4 3).toNat = 1 := by
          have r23326 := hand1 (x 4 3) (x 4 14)
          have b23327 := hb (x 4 3)
          have b23328 := hb (x 4 3 && x 4 14)
          clear * - r23326 b23327 b23328 d23318
          omega
        have d23329 : (x 7 12).toNat = 0 := by
          have r23330 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23331 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e23332 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b23333 := hb (x 4 3)
          have b23334 := hb (x 5 2)
          have b23335 := hb (x 6 13)
          have b23336 := hb (x 7 12)
          clear * - r23330 e23331 e23332 b23333 b23334 b23335 b23336 d23002 d23325
          omega
        have d23337 : (x 6 13).toNat = 0 := by
          have r23338 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23339 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e23340 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b23341 := hb (x 4 3)
          have b23342 := hb (x 5 2)
          have b23343 := hb (x 6 13)
          have b23344 := hb (x 7 12)
          clear * - r23338 e23339 e23340 b23341 b23342 b23343 b23344 d23329 d23002 d23325
          omega
        have d23345 : (x 4 2).toNat = 1 := by
          have r23346 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23347 := hb (x 4 2)
          have b23348 := hb (x 6 13)
          have b23349 := hb (x 5 1 && x 5 14)
          clear * - r23346 b23347 b23348 b23349 d23337 d22994
          omega
        have r23350 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23351 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e23352 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b23353 := hb (x 3 3)
        have b23354 := hb (x 4 2)
        have b23355 := hb (x 5 13)
        have b23356 := hb (x 6 12)
        linarith only [r23350, e23351, e23352, b23353, b23354, b23355, b23356, d23306, d23082, d23345, d23302]
      · have f23357 : (x (-1) 1).toNat = 1 := by rw [h22836]; rfl
        cases h23358 : x (-1) 3
        · have f23359 : (x (-1) 3).toNat = 0 := by rw [h23358]; rfl
          have d23360 : (x (-1) 11).toNat = 0 := by
            have r23361 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
            have b23362 := hb (x (-1) 3)
            have b23363 := hb (x (-1) 11)
            clear * - r23361 b23362 b23363 f23359
            omega
          have d23364 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
            have r23365 := hand2 (x (-1) 1) (x (-1) 11)
            have b23366 := hb (x (-1) 11)
            have b23367 := hb (x (-1) 1 && x (-1) 11)
            clear * - r23365 b23366 b23367 d23360
            omega
          have d23368 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
            have r23369 := hand2 (x (-1) 2) (x (-1) 11)
            have b23370 := hb (x (-1) 11)
            have b23371 := hb (x (-1) 2 && x (-1) 11)
            clear * - r23369 b23370 b23371 d23360
            omega
          cases h23372 : x (-1) 6
          · have f23373 : (x (-1) 6).toNat = 0 := by rw [h23372]; rfl
            cases h23374 : x 1 3
            · have f23375 : (x 1 3).toNat = 0 := by rw [h23374]; rfl
              have d23376 : (x 1 11).toNat = 0 := by
                have r23377 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                have b23378 := hb (x 1 3)
                have b23379 := hb (x 1 11)
                clear * - r23377 b23378 b23379 f23375
                omega
              cases h23380 : x (-1) 7
              · have f23381 : (x (-1) 7).toNat = 0 := by rw [h23380]; rfl
                have d23382 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
                  have r23383 := hand2 (x (-1) 1) (x (-1) 7)
                  have b23384 := hb (x (-1) 7)
                  have b23385 := hb (x (-1) 1 && x (-1) 7)
                  clear * - r23383 b23384 b23385 f23381
                  omega
                have d23386 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
                  have r23387 := hand2 (x (-1) 2) (x (-1) 7)
                  have b23388 := hb (x (-1) 7)
                  have b23389 := hb (x (-1) 2 && x (-1) 7)
                  clear * - r23387 b23388 b23389 f23381
                  omega
                have r23390 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23391 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23392 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23393 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                have e23394 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                have e23395 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                have e23396 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                have e23397 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                have e23398 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                have r23399 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23400 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e23401 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have r23402 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23403 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23404 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23405 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23406 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23407 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23408 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
                have r23409 := hand2 (x (-3) 4) (x (-3) 9)
                have r23410 := hand2 (x (-4) 5) (x (-4) 10)
                have r23411 := hand2 (x (-5) 6) (x (-5) 11)
                have r23412 := hand1 (x (-6) 7) (x (-6) 12)
                have r23413 := hand1 (x (-7) 8) (x (-7) 13)
                have r23414 := hand1 (x (-8) 9) (x (-8) 14)
                have r23415 := hand2 (x (-2) 2) (x (-2) 8)
                have r23416 := hand2 (x (-3) 3) (x (-3) 9)
                have r23417 := hand1 (x (-8) 8) (x (-8) 14)
                have r23418 := hand1 (x (-3) 4) (x (-3) 13)
                have r23419 := hand1 (x (-4) 5) (x (-4) 14)
                have r23420 := hand1 (x (-4) 2) (x (-4) 12)
                have r23421 := hand1 (x (-5) 3) (x (-5) 13)
                have r23422 := hand1 (x (-6) 4) (x (-6) 14)
                have r23423 := hand1 (x (-2) 2) (x (-2) 12)
                have r23424 := hand2 (x (-2) 2) (x (-2) 12)
                have r23425 := hand1 (x (-3) 3) (x (-3) 13)
                have r23426 := hand2 (x (-3) 3) (x (-3) 13)
                have r23427 := hand2 (x (-13) 1) (x (-13) 14)
                linarith only [r23390, r23391, r23392, e23393, e23394, e23395, e23396, e23397, e23398, r23399, e23400, e23401, r23402, r23403, r23404, r23405, r23406, r23407, r23408, r23409, r23410, r23411, r23412, r23413, r23414, r23415, r23416, r23417, r23418, r23419, r23420, r23421, r23422, r23423, r23424, r23425, r23426, r23427, g0, g1, g2, g3, g5, g8, f23357, g11, g13, g18, g21, g26, g27, g51, d23386, g52, d23382, g61, g62, g63, g64, g81, d23368, g82, g88, d23364, g89]
              · have f23505 : (x (-1) 7).toNat = 1 := by rw [h23380]; rfl
                have d23506 : (x 6 8).toNat = 0 := by
                  have r23507 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23508 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e23509 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e23510 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e23511 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e23512 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e23513 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b23514 := hb (x (-1) 7)
                  have b23515 := hb (x 0 6)
                  have b23516 := hb (x 1 5)
                  have b23517 := hb (x 2 4)
                  have b23518 := hb (x 3 11)
                  have b23519 := hb (x 4 10)
                  have b23520 := hb (x 5 9)
                  have b23521 := hb (x 6 8)
                  clear * - r23507 e23508 e23509 e23510 e23511 e23512 e23513 b23514 b23515 b23516 b23517 b23518 b23519 b23520 b23521 g26 g18 f23505
                  omega
                have d23522 : (x 6 1 && x 6 8).toNat = 0 := by
                  have r23523 := hand2 (x 6 1) (x 6 8)
                  have b23524 := hb (x 6 8)
                  have b23525 := hb (x 6 1 && x 6 8)
                  clear * - r23523 b23524 b23525 d23506
                  omega
                have d23526 : (x 6 3 && x 6 8).toNat = 0 := by
                  have r23527 := hand2 (x 6 3) (x 6 8)
                  have b23528 := hb (x 6 8)
                  have b23529 := hb (x 6 3 && x 6 8)
                  clear * - r23527 b23528 b23529 d23506
                  omega
                have d23530 : (x 5 9).toNat = 0 := by
                  have r23531 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23532 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e23533 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e23534 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e23535 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e23536 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e23537 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b23538 := hb (x (-1) 7)
                  have b23539 := hb (x 0 6)
                  have b23540 := hb (x 1 5)
                  have b23541 := hb (x 2 4)
                  have b23542 := hb (x 3 11)
                  have b23543 := hb (x 4 10)
                  have b23544 := hb (x 5 9)
                  have b23545 := hb (x 6 8)
                  clear * - r23531 e23532 e23533 e23534 e23535 e23536 e23537 b23538 b23539 b23540 b23541 b23542 b23543 b23544 b23545 d23506 g26 g18 f23505
                  omega
                have d23546 : (x 5 2 && x 5 9).toNat = 0 := by
                  have r23547 := hand2 (x 5 2) (x 5 9)
                  have b23548 := hb (x 5 9)
                  have b23549 := hb (x 5 2 && x 5 9)
                  clear * - r23547 b23548 b23549 d23530
                  omega
                have d23550 : (x 5 4 && x 5 9).toNat = 0 := by
                  have r23551 := hand2 (x 5 4) (x 5 9)
                  have b23552 := hb (x 5 9)
                  have b23553 := hb (x 5 4 && x 5 9)
                  clear * - r23551 b23552 b23553 d23530
                  omega
                have d23554 : (x 4 10).toNat = 0 := by
                  have r23555 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23556 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e23557 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e23558 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e23559 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e23560 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e23561 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b23562 := hb (x (-1) 7)
                  have b23563 := hb (x 0 6)
                  have b23564 := hb (x 1 5)
                  have b23565 := hb (x 2 4)
                  have b23566 := hb (x 3 11)
                  have b23567 := hb (x 4 10)
                  have b23568 := hb (x 5 9)
                  have b23569 := hb (x 6 8)
                  clear * - r23555 e23556 e23557 e23558 e23559 e23560 e23561 b23562 b23563 b23564 b23565 b23566 b23567 b23568 b23569 d23506 d23530 g26 g18 f23505
                  omega
                have d23570 : (x 4 1 && x 4 10).toNat = 0 := by
                  have r23571 := hand2 (x 4 1) (x 4 10)
                  have b23572 := hb (x 4 10)
                  have b23573 := hb (x 4 1 && x 4 10)
                  clear * - r23571 b23572 b23573 d23554
                  omega
                have d23574 : (x 2 3 && x 2 12).toNat = 1 := by
                  have r23575 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b23576 := hb (x (-1) 6)
                  have b23577 := hb (x 5 9)
                  have b23578 := hb (x 4 1 && x 4 10)
                  have b23579 := hb (x 3 2 && x 3 11)
                  have b23580 := hb (x 2 3 && x 2 12)
                  have b23581 := hb (x 1 4 && x 1 13)
                  have b23582 := hb (x 0 5 && x 0 14)
                  clear * - r23575 b23576 b23577 b23578 b23579 b23580 b23581 b23582 d23530 d23570 g83 g84 g85 f23373
                  omega
                have d23583 : (x 2 3).toNat = 1 := by
                  have r23584 := hand1 (x 2 3) (x 2 12)
                  have b23585 := hb (x 2 3)
                  have b23586 := hb (x 2 3 && x 2 12)
                  clear * - r23584 b23585 b23586 d23574
                  omega
                have d23587 : (x 5 12).toNat = 0 := by
                  have r23588 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23589 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e23590 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b23591 := hb (x 2 3)
                  have b23592 := hb (x 3 2)
                  have b23593 := hb (x 4 13)
                  have b23594 := hb (x 5 12)
                  clear * - r23588 e23589 e23590 b23591 b23592 b23593 b23594 g33 d23583
                  omega
                have d23595 : (x 5 1 && x 5 12).toNat = 0 := by
                  have r23596 := hand2 (x 5 1) (x 5 12)
                  have b23597 := hb (x 5 12)
                  have b23598 := hb (x 5 1 && x 5 12)
                  clear * - r23596 b23597 b23598 d23587
                  omega
                have d23599 : (x 5 4).toNat = 0 := by
                  have r23600 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                  have b23601 := hb (x 5 4)
                  have b23602 := hb (x 5 12)
                  clear * - r23600 b23601 b23602 d23587
                  omega
                have d23603 : (x 4 13).toNat = 0 := by
                  have r23604 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23605 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e23606 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b23607 := hb (x 2 3)
                  have b23608 := hb (x 3 2)
                  have b23609 := hb (x 4 13)
                  have b23610 := hb (x 5 12)
                  clear * - r23604 e23605 e23606 b23607 b23608 b23609 b23610 d23587 g33 d23583
                  omega
                have d23611 : (x 4 2 && x 4 13).toNat = 0 := by
                  have r23612 := hand2 (x 4 2) (x 4 13)
                  have b23613 := hb (x 4 13)
                  have b23614 := hb (x 4 2 && x 4 13)
                  clear * - r23612 b23613 b23614 d23603
                  omega
                have d23615 : (x 4 5).toNat = 0 := by
                  have r23616 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
                  have b23617 := hb (x 4 5)
                  have b23618 := hb (x 4 13)
                  clear * - r23616 b23617 b23618 d23603
                  omega
                have d23619 : (x 4 5 && x 4 10).toNat = 0 := by
                  have r23620 := hand1 (x 4 5) (x 4 10)
                  have b23621 := hb (x 4 5)
                  have b23622 := hb (x 4 5 && x 4 10)
                  clear * - r23620 b23621 b23622 d23615
                  omega
                have d23623 : (x 4 3 && x 4 10).toNat = 0 := by
                  have r23624 := hand2 (x 4 3) (x 4 10)
                  have b23625 := hb (x 4 10)
                  have b23626 := hb (x 4 3 && x 4 10)
                  clear * - r23624 b23625 b23626 d23554
                  omega
                have d23627 : (x 3 11).toNat = 0 := by
                  have r23628 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23629 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e23630 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e23631 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e23632 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e23633 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e23634 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b23635 := hb (x (-1) 7)
                  have b23636 := hb (x 0 6)
                  have b23637 := hb (x 1 5)
                  have b23638 := hb (x 2 4)
                  have b23639 := hb (x 3 11)
                  have b23640 := hb (x 4 10)
                  have b23641 := hb (x 5 9)
                  have b23642 := hb (x 6 8)
                  clear * - r23628 e23629 e23630 e23631 e23632 e23633 e23634 b23635 b23636 b23637 b23638 b23639 b23640 b23641 b23642 d23506 d23530 d23554 g26 g18 f23505
                  omega
                have d23643 : (x 2 4).toNat = 0 := by
                  have r23644 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23645 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e23646 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e23647 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e23648 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e23649 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e23650 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b23651 := hb (x (-1) 7)
                  have b23652 := hb (x 0 6)
                  have b23653 := hb (x 1 5)
                  have b23654 := hb (x 2 4)
                  have b23655 := hb (x 3 11)
                  have b23656 := hb (x 4 10)
                  have b23657 := hb (x 5 9)
                  have b23658 := hb (x 6 8)
                  clear * - r23644 e23645 e23646 e23647 e23648 e23649 e23650 b23651 b23652 b23653 b23654 b23655 b23656 b23657 b23658 d23506 d23530 d23554 d23627 g26 g18 f23505
                  omega
                have d23659 : (x 2 4 && x 2 13).toNat = 0 := by
                  have r23660 := hand1 (x 2 4) (x 2 13)
                  have b23661 := hb (x 2 4)
                  have b23662 := hb (x 2 4 && x 2 13)
                  clear * - r23660 b23661 b23662 d23643
                  omega
                have d23663 : (x 6 11).toNat = 1 := by
                  have r23664 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b23665 := hb (x 2 4)
                  have b23666 := hb (x 6 11)
                  have b23667 := hb (x 5 1 && x 5 12)
                  have b23668 := hb (x 4 2 && x 4 13)
                  have b23669 := hb (x 3 3 && x 3 14)
                  clear * - r23664 b23665 b23666 b23667 b23668 b23669 d23595 d23611 g106 d23643
                  omega
                have d23670 : (x 6 3).toNat = 1 := by
                  have r23671 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                  have b23672 := hb (x 6 3)
                  have b23673 := hb (x 6 11)
                  clear * - r23671 b23672 b23673 d23663
                  omega
                have d23674 : (x 9 12).toNat = 0 := by
                  have r23675 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23676 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                  have e23677 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                  have b23678 := hb (x 6 3)
                  have b23679 := hb (x 7 2)
                  have b23680 := hb (x 8 13)
                  have b23681 := hb (x 9 12)
                  clear * - r23675 e23676 e23677 b23678 b23679 b23680 b23681 d23670
                  omega
                have d23682 : (x 8 13).toNat = 0 := by
                  have r23683 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23684 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                  have e23685 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                  have b23686 := hb (x 6 3)
                  have b23687 := hb (x 7 2)
                  have b23688 := hb (x 8 13)
                  have b23689 := hb (x 9 12)
                  clear * - r23683 e23684 e23685 b23686 b23687 b23688 b23689 d23674 d23670
                  omega
                have d23690 : (x 7 2).toNat = 0 := by
                  have r23691 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23692 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                  have e23693 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                  have b23694 := hb (x 6 3)
                  have b23695 := hb (x 7 2)
                  have b23696 := hb (x 8 13)
                  have b23697 := hb (x 9 12)
                  clear * - r23691 e23692 e23693 b23694 b23695 b23696 b23697 d23674 d23682 d23670
                  omega
                have d23698 : (x 7 2 && x 7 7).toNat = 0 := by
                  have r23699 := hand1 (x 7 2) (x 7 7)
                  have b23700 := hb (x 7 2)
                  have b23701 := hb (x 7 2 && x 7 7)
                  clear * - r23699 b23700 b23701 d23690
                  omega
                have d23702 : (x 7 10).toNat = 0 := by
                  have r23703 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
                  have b23704 := hb (x 7 2)
                  have b23705 := hb (x 7 10)
                  clear * - r23703 b23704 b23705 d23690
                  omega
                have d23706 : (x 9 8).toNat = 0 := by
                  have r23707 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23708 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                  have e23709 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                  have e23710 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                  have e23711 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                  have e23712 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                  have e23713 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                  have b23714 := hb (x 2 7)
                  have b23715 := hb (x 3 6)
                  have b23716 := hb (x 4 5)
                  have b23717 := hb (x 5 4)
                  have b23718 := hb (x 6 11)
                  have b23719 := hb (x 7 10)
                  have b23720 := hb (x 8 9)
                  have b23721 := hb (x 9 8)
                  clear * - r23707 e23708 e23709 e23710 e23711 e23712 e23713 b23714 b23715 b23716 b23717 b23718 b23719 b23720 b23721 d23702 d23663 d23599 d23615 g35
                  omega
                have d23722 : (x 8 9).toNat = 0 := by
                  have r23723 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23724 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                  have e23725 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                  have e23726 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                  have e23727 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                  have e23728 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                  have e23729 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                  have b23730 := hb (x 2 7)
                  have b23731 := hb (x 3 6)
                  have b23732 := hb (x 4 5)
                  have b23733 := hb (x 5 4)
                  have b23734 := hb (x 6 11)
                  have b23735 := hb (x 7 10)
                  have b23736 := hb (x 8 9)
                  have b23737 := hb (x 9 8)
                  clear * - r23723 e23724 e23725 e23726 e23727 e23728 e23729 b23730 b23731 b23732 b23733 b23734 b23735 b23736 b23737 d23706 d23702 d23663 d23599 d23615 g35
                  omega
                have d23738 : (x 2 7).toNat = 0 := by
                  have r23739 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e23740 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                  have e23741 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                  have e23742 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                  have e23743 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                  have e23744 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                  have e23745 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                  have b23746 := hb (x 2 7)
                  have b23747 := hb (x 3 6)
                  have b23748 := hb (x 4 5)
                  have b23749 := hb (x 5 4)
                  have b23750 := hb (x 6 11)
                  have b23751 := hb (x 7 10)
                  have b23752 := hb (x 8 9)
                  have b23753 := hb (x 9 8)
                  clear * - r23739 e23740 e23741 e23742 e23743 e23744 e23745 b23746 b23747 b23748 b23749 b23750 b23751 b23752 b23753 d23706 d23722 d23702 d23663 d23599 d23615 g35
                  omega
                have d23754 : (x 2 7 && x 2 12).toNat = 0 := by
                  have r23755 := hand1 (x 2 7) (x 2 12)
                  have b23756 := hb (x 2 7)
                  have b23757 := hb (x 2 7 && x 2 12)
                  clear * - r23755 b23756 b23757 d23738
                  omega
                have r23758 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23759 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e23760 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e23761 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e23762 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e23763 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e23764 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have r23765 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23766 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e23767 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e23768 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e23769 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e23770 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e23771 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have r23772 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23773 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                have e23774 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                have e23775 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                have e23776 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                have e23777 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                have e23778 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                have r23779 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23780 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e23781 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e23782 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e23783 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e23784 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e23785 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have r23786 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23787 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e23788 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have r23789 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23790 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                have e23791 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                have r23792 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23793 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23794 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23795 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23796 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23797 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23798 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r23799 := hand2 (x 8 1) (x 8 6)
                have r23800 := hand1 (x 2 5) (x 2 12)
                have r23801 := hand1 (x (-4) 3) (x (-4) 12)
                have r23802 := hand1 (x (-5) 4) (x (-5) 13)
                have r23803 := hand1 (x (-6) 5) (x (-6) 14)
                have r23804 := hand2 (x 5 1) (x 5 10)
                have r23805 := hand2 (x 4 2) (x 4 11)
                have r23806 := hand1 (x (-2) 2) (x (-2) 12)
                have r23807 := hand1 (x (-3) 3) (x (-3) 13)
                have r23808 := hand2 (x (-1) 2) (x (-1) 13)
                linarith only [r23758, e23759, e23760, e23761, e23762, e23763, e23764, r23765, e23766, e23767, e23768, e23769, e23770, e23771, r23772, e23773, e23774, e23775, e23776, e23777, e23778, r23779, e23780, e23781, e23782, e23783, e23784, e23785, r23786, e23787, e23788, r23789, e23790, e23791, r23792, r23793, r23794, r23795, r23796, r23797, r23798, r23799, r23800, r23801, r23802, r23803, r23804, r23805, r23806, r23807, r23808, g2, g7, g9, g10, g12, g18, f22829, g20, g21, f22835, d23376, g34, d23698, d23526, d23550, d23619, g58, d23754, g59, g60, d23522, d23546, d23623, g74, g75, d22830, g76, g77, g86, d23659, g87, d23364, g89, g98, g99, g107]
            · have f23888 : (x 1 3).toNat = 1 := by rw [h23374]; rfl
              have d23889 : (x 4 12).toNat = 0 := by
                have r23890 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23891 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e23892 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b23893 := hb (x 1 3)
                have b23894 := hb (x 2 2)
                have b23895 := hb (x 3 13)
                have b23896 := hb (x 4 12)
                clear * - r23890 e23891 e23892 b23893 b23894 b23895 b23896 f23888
                omega
              have d23897 : (x 4 1 && x 4 12).toNat = 0 := by
                have r23898 := hand2 (x 4 1) (x 4 12)
                have b23899 := hb (x 4 12)
                have b23900 := hb (x 4 1 && x 4 12)
                clear * - r23898 b23899 b23900 d23889
                omega
              have d23901 : (x 4 4).toNat = 0 := by
                have r23902 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                have b23903 := hb (x 4 4)
                have b23904 := hb (x 4 12)
                clear * - r23902 b23903 b23904 d23889
                omega
              have d23905 : (x 3 13).toNat = 0 := by
                have r23906 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23907 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e23908 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b23909 := hb (x 1 3)
                have b23910 := hb (x 2 2)
                have b23911 := hb (x 3 13)
                have b23912 := hb (x 4 12)
                clear * - r23906 e23907 e23908 b23909 b23910 b23911 b23912 d23889 f23888
                omega
              have d23913 : (x 2 2).toNat = 0 := by
                have r23914 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23915 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e23916 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b23917 := hb (x 1 3)
                have b23918 := hb (x 2 2)
                have b23919 := hb (x 3 13)
                have b23920 := hb (x 4 12)
                clear * - r23914 e23915 e23916 b23917 b23918 b23919 b23920 d23889 d23905 f23888
                omega
              have d23921 : (x 4 13).toNat = 1 := by
                have r23922 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23923 := hb (x 2 2)
                have b23924 := hb (x 4 13)
                have b23925 := hb (x 3 1 && x 3 14)
                clear * - r23922 b23923 b23924 b23925 g108 d23913
                omega
              have d23926 : (x 4 1).toNat = 1 := by
                have r23927 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                have b23928 := hb (x 4 1)
                have b23929 := hb (x 4 13)
                clear * - r23927 b23928 b23929 d23921
                omega
              have d23930 : (x 5 14).toNat = 0 := by
                have r23931 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23932 := hb (x 4 1)
                have b23933 := hb (x 5 14)
                clear * - r23931 b23932 b23933 d23926
                omega
              have d23934 : (x 5 3 && x 5 14).toNat = 0 := by
                have r23935 := hand2 (x 5 3) (x 5 14)
                have b23936 := hb (x 5 14)
                have b23937 := hb (x 5 3 && x 5 14)
                clear * - r23935 b23936 b23937 d23930
                omega
              have d23938 : (x 5 2).toNat = 0 := by
                have r23939 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b23940 := hb (x 5 2)
                have b23941 := hb (x 5 14)
                clear * - r23939 b23940 b23941 d23930
                omega
              have d23942 : (x 5 12).toNat = 0 := by
                have r23943 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23944 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e23945 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b23946 := hb (x 2 3)
                have b23947 := hb (x 3 2)
                have b23948 := hb (x 4 13)
                have b23949 := hb (x 5 12)
                clear * - r23943 e23944 e23945 b23946 b23947 b23948 b23949 d23921 g33
                omega
              have d23950 : (x 5 4).toNat = 0 := by
                have r23951 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                have b23952 := hb (x 5 4)
                have b23953 := hb (x 5 12)
                clear * - r23951 b23952 b23953 d23942
                omega
              have d23954 : (x 2 3).toNat = 0 := by
                have r23955 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23956 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                have e23957 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                have b23958 := hb (x 2 3)
                have b23959 := hb (x 3 2)
                have b23960 := hb (x 4 13)
                have b23961 := hb (x 5 12)
                clear * - r23955 e23956 e23957 b23958 b23959 b23960 b23961 d23942 d23921 g33
                omega
              have d23962 : (x 2 3 && x 2 14).toNat = 0 := by
                have r23963 := hand1 (x 2 3) (x 2 14)
                have b23964 := hb (x 2 3)
                have b23965 := hb (x 2 3 && x 2 14)
                clear * - r23963 b23964 b23965 d23954
                omega
              have d23966 : (x 5 11).toNat = 1 := by
                have r23967 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b23968 := hb (x 1 4)
                have b23969 := hb (x 5 11)
                have b23970 := hb (x 4 1 && x 4 12)
                have b23971 := hb (x 3 2 && x 3 13)
                have b23972 := hb (x 2 3 && x 2 14)
                clear * - r23967 b23968 b23969 b23970 b23971 b23972 d23897 g105 d23962 g25
                omega
              have d23973 : (x 5 3).toNat = 1 := by
                have r23974 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                have b23975 := hb (x 5 3)
                have b23976 := hb (x 5 11)
                clear * - r23974 b23975 b23976 d23966
                omega
              have d23977 : (x 8 12).toNat = 0 := by
                have r23978 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23979 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e23980 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b23981 := hb (x 5 3)
                have b23982 := hb (x 6 2)
                have b23983 := hb (x 7 13)
                have b23984 := hb (x 8 12)
                clear * - r23978 e23979 e23980 b23981 b23982 b23983 b23984 d23973
                omega
              have d23985 : (x 8 1 && x 8 12).toNat = 0 := by
                have r23986 := hand2 (x 8 1) (x 8 12)
                have b23987 := hb (x 8 12)
                have b23988 := hb (x 8 1 && x 8 12)
                clear * - r23986 b23987 b23988 d23977
                omega
              have d23989 : (x 8 4).toNat = 0 := by
                have r23990 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have b23991 := hb (x 8 4)
                have b23992 := hb (x 8 12)
                clear * - r23990 b23991 b23992 d23977
                omega
              have d23993 : (x 7 13).toNat = 0 := by
                have r23994 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e23995 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e23996 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b23997 := hb (x 5 3)
                have b23998 := hb (x 6 2)
                have b23999 := hb (x 7 13)
                have b24000 := hb (x 8 12)
                clear * - r23994 e23995 e23996 b23997 b23998 b23999 b24000 d23977 d23973
                omega
              have d24001 : (x 7 2 && x 7 13).toNat = 0 := by
                have r24002 := hand2 (x 7 2) (x 7 13)
                have b24003 := hb (x 7 13)
                have b24004 := hb (x 7 2 && x 7 13)
                clear * - r24002 b24003 b24004 d23993
                omega
              have d24005 : (x 6 1 && x 6 14).toNat = 1 := by
                have r24006 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24007 := hb (x 5 2)
                have b24008 := hb (x 7 13)
                have b24009 := hb (x 6 1 && x 6 14)
                clear * - r24006 b24007 b24008 b24009 d23993 d23938
                omega
              have d24010 : (x 6 1).toNat = 1 := by
                have r24011 := hand1 (x 6 1) (x 6 14)
                have b24012 := hb (x 6 1)
                have b24013 := hb (x 6 1 && x 6 14)
                clear * - r24011 b24012 b24013 d24005
                omega
              have d24014 : (x 7 14).toNat = 0 := by
                have r24015 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24016 := hb (x 6 1)
                have b24017 := hb (x 7 14)
                clear * - r24015 b24016 b24017 d24010
                omega
              have d24018 : (x 7 1 && x 7 14).toNat = 0 := by
                have r24019 := hand2 (x 7 1) (x 7 14)
                have b24020 := hb (x 7 14)
                have b24021 := hb (x 7 1 && x 7 14)
                clear * - r24019 b24020 b24021 d24014
                omega
              have d24022 : (x 7 2).toNat = 0 := by
                have r24023 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b24024 := hb (x 7 2)
                have b24025 := hb (x 7 14)
                clear * - r24023 b24024 b24025 d24014
                omega
              have d24026 : (x 6 2).toNat = 0 := by
                have r24027 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24028 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e24029 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b24030 := hb (x 5 3)
                have b24031 := hb (x 6 2)
                have b24032 := hb (x 7 13)
                have b24033 := hb (x 8 12)
                clear * - r24027 e24028 e24029 b24030 b24031 b24032 b24033 d23977 d23993 d23973
                omega
              have d24034 : (x 6 2 && x 6 13).toNat = 0 := by
                have r24035 := hand1 (x 6 2) (x 6 13)
                have b24036 := hb (x 6 2)
                have b24037 := hb (x 6 2 && x 6 13)
                clear * - r24035 b24036 b24037 d24026
                omega
              have d24038 : (x 8 13).toNat = 1 := by
                have r24039 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24040 := hb (x 6 2)
                have b24041 := hb (x 8 13)
                have b24042 := hb (x 7 1 && x 7 14)
                clear * - r24039 b24040 b24041 b24042 d24018 d24026
                omega
              have d24043 : (x 8 1).toNat = 1 := by
                have r24044 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                have b24045 := hb (x 8 1)
                have b24046 := hb (x 8 13)
                clear * - r24044 b24045 b24046 d24038
                omega
              have d24047 : (x 9 14).toNat = 0 := by
                have r24048 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24049 := hb (x 8 1)
                have b24050 := hb (x 9 14)
                clear * - r24048 b24049 b24050 d24043
                omega
              have d24051 : (x 9 3 && x 9 14).toNat = 0 := by
                have r24052 := hand2 (x 9 3) (x 9 14)
                have b24053 := hb (x 9 14)
                have b24054 := hb (x 9 3 && x 9 14)
                clear * - r24052 b24053 b24054 d24047
                omega
              have d24055 : (x 9 2).toNat = 0 := by
                have r24056 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b24057 := hb (x 9 2)
                have b24058 := hb (x 9 14)
                clear * - r24056 b24057 b24058 d24047
                omega
              have d24059 : (x 9 12).toNat = 0 := by
                have r24060 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24061 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e24062 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b24063 := hb (x 6 3)
                have b24064 := hb (x 7 2)
                have b24065 := hb (x 8 13)
                have b24066 := hb (x 9 12)
                clear * - r24060 e24061 e24062 b24063 b24064 b24065 b24066 d24038 d24022
                omega
              have d24067 : (x 9 4).toNat = 0 := by
                have r24068 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have b24069 := hb (x 9 4)
                have b24070 := hb (x 9 12)
                clear * - r24068 b24069 b24070 d24059
                omega
              have d24071 : (x 6 3).toNat = 0 := by
                have r24072 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24073 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e24074 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b24075 := hb (x 6 3)
                have b24076 := hb (x 7 2)
                have b24077 := hb (x 8 13)
                have b24078 := hb (x 9 12)
                clear * - r24072 e24073 e24074 b24075 b24076 b24077 b24078 d24059 d24038 d24022
                omega
              have d24079 : (x 6 3 && x 6 14).toNat = 0 := by
                have r24080 := hand1 (x 6 3) (x 6 14)
                have b24081 := hb (x 6 3)
                have b24082 := hb (x 6 3 && x 6 14)
                clear * - r24080 b24081 b24082 d24071
                omega
              have d24083 : (x 9 11).toNat = 1 := by
                have r24084 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24085 := hb (x 5 4)
                have b24086 := hb (x 9 11)
                have b24087 := hb (x 8 1 && x 8 12)
                have b24088 := hb (x 7 2 && x 7 13)
                have b24089 := hb (x 6 3 && x 6 14)
                clear * - r24084 b24085 b24086 b24087 b24088 b24089 d23985 d24001 d24079 d23950
                omega
              have d24090 : (x 9 3).toNat = 1 := by
                have r24091 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
                have b24092 := hb (x 9 3)
                have b24093 := hb (x 9 11)
                clear * - r24091 b24092 b24093 d24083
                omega
              have d24094 : (x 12 12).toNat = 0 := by
                have r24095 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24096 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e24097 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b24098 := hb (x 9 3)
                have b24099 := hb (x 10 2)
                have b24100 := hb (x 11 13)
                have b24101 := hb (x 12 12)
                clear * - r24095 e24096 e24097 b24098 b24099 b24100 b24101 d24090
                omega
              have d24102 : (x 12 1 && x 12 12).toNat = 0 := by
                have r24103 := hand2 (x 12 1) (x 12 12)
                have b24104 := hb (x 12 12)
                have b24105 := hb (x 12 1 && x 12 12)
                clear * - r24103 b24104 b24105 d24094
                omega
              have d24106 : (x 12 4).toNat = 0 := by
                have r24107 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
                have b24108 := hb (x 12 4)
                have b24109 := hb (x 12 12)
                clear * - r24107 b24108 b24109 d24094
                omega
              have d24110 : (x 11 13).toNat = 0 := by
                have r24111 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24112 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e24113 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b24114 := hb (x 9 3)
                have b24115 := hb (x 10 2)
                have b24116 := hb (x 11 13)
                have b24117 := hb (x 12 12)
                clear * - r24111 e24112 e24113 b24114 b24115 b24116 b24117 d24094 d24090
                omega
              have d24118 : (x 11 2 && x 11 13).toNat = 0 := by
                have r24119 := hand2 (x 11 2) (x 11 13)
                have b24120 := hb (x 11 13)
                have b24121 := hb (x 11 2 && x 11 13)
                clear * - r24119 b24120 b24121 d24110
                omega
              have d24122 : (x 10 1 && x 10 14).toNat = 1 := by
                have r24123 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24124 := hb (x 9 2)
                have b24125 := hb (x 11 13)
                have b24126 := hb (x 10 1 && x 10 14)
                clear * - r24123 b24124 b24125 b24126 d24110 d24055
                omega
              have d24127 : (x 10 14).toNat = 1 := by
                have r24128 := hand2 (x 10 1) (x 10 14)
                have b24129 := hb (x 10 14)
                have b24130 := hb (x 10 1 && x 10 14)
                clear * - r24128 b24129 b24130 d24122
                omega
              have d24131 : (x 9 1).toNat = 0 := by
                have r24132 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24133 := hb (x 9 1)
                have b24134 := hb (x 10 14)
                clear * - r24132 b24133 b24134 d24127
                omega
              have d24135 : (x 9 13).toNat = 0 := by
                have r24136 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                have b24137 := hb (x 9 1)
                have b24138 := hb (x 9 13)
                clear * - r24136 b24137 b24138 d24131
                omega
              have d24139 : (x 8 1 && x 8 14).toNat = 1 := by
                have r24140 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24141 := hb (x 7 2)
                have b24142 := hb (x 9 13)
                have b24143 := hb (x 8 1 && x 8 14)
                clear * - r24140 b24141 b24142 b24143 d24135 d24022
                omega
              have d24144 : (x 8 14).toNat = 1 := by
                have r24145 := hand2 (x 8 1) (x 8 14)
                have b24146 := hb (x 8 14)
                have b24147 := hb (x 8 1 && x 8 14)
                clear * - r24145 b24146 b24147 d24139
                omega
              have d24148 : (x 7 1).toNat = 0 := by
                have r24149 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24150 := hb (x 7 1)
                have b24151 := hb (x 8 14)
                clear * - r24149 b24150 b24151 d24144
                omega
              have d24152 : (x 7 1 && x 7 12).toNat = 0 := by
                have r24153 := hand1 (x 7 1) (x 7 12)
                have b24154 := hb (x 7 1)
                have b24155 := hb (x 7 1 && x 7 12)
                clear * - r24153 b24154 b24155 d24148
                omega
              have d24156 : (x 8 11).toNat = 1 := by
                have r24157 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24158 := hb (x 4 4)
                have b24159 := hb (x 8 11)
                have b24160 := hb (x 7 1 && x 7 12)
                have b24161 := hb (x 6 2 && x 6 13)
                have b24162 := hb (x 5 3 && x 5 14)
                clear * - r24157 b24158 b24159 b24160 b24161 b24162 d24152 d24034 d23934 d23901
                omega
              have d24163 : (x 8 3).toNat = 1 := by
                have r24164 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                have b24165 := hb (x 8 3)
                have b24166 := hb (x 8 11)
                clear * - r24164 b24165 b24166 d24156
                omega
              have d24167 : (x 11 12).toNat = 0 := by
                have r24168 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24169 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e24170 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b24171 := hb (x 8 3)
                have b24172 := hb (x 9 2)
                have b24173 := hb (x 10 13)
                have b24174 := hb (x 11 12)
                clear * - r24168 e24169 e24170 b24171 b24172 b24173 b24174 d24055 d24163
                omega
              have d24175 : (x 11 1 && x 11 12).toNat = 0 := by
                have r24176 := hand2 (x 11 1) (x 11 12)
                have b24177 := hb (x 11 12)
                have b24178 := hb (x 11 1 && x 11 12)
                clear * - r24176 b24177 b24178 d24167
                omega
              have d24179 : (x 10 13).toNat = 0 := by
                have r24180 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24181 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e24182 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b24183 := hb (x 8 3)
                have b24184 := hb (x 9 2)
                have b24185 := hb (x 10 13)
                have b24186 := hb (x 11 12)
                clear * - r24180 e24181 e24182 b24183 b24184 b24185 b24186 d24167 d24055 d24163
                omega
              have d24187 : (x 10 2 && x 10 13).toNat = 0 := by
                have r24188 := hand2 (x 10 2) (x 10 13)
                have b24189 := hb (x 10 13)
                have b24190 := hb (x 10 2 && x 10 13)
                clear * - r24188 b24189 b24190 d24179
                omega
              have d24191 : (x 12 11).toNat = 1 := by
                have r24192 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24193 := hb (x 8 4)
                have b24194 := hb (x 12 11)
                have b24195 := hb (x 11 1 && x 11 12)
                have b24196 := hb (x 10 2 && x 10 13)
                have b24197 := hb (x 9 3 && x 9 14)
                clear * - r24192 b24193 b24194 b24195 b24196 b24197 d24175 d24187 d24051 d23989
                omega
              have d24198 : (x 12 3).toNat = 1 := by
                have r24199 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
                have b24200 := hb (x 12 3)
                have b24201 := hb (x 12 11)
                clear * - r24199 b24200 b24201 d24191
                omega
              have d24202 : (x 15 12).toNat = 0 := by
                have r24203 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24204 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e24205 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b24206 := hb (x 12 3)
                have b24207 := hb (x 13 2)
                have b24208 := hb (x 14 13)
                have b24209 := hb (x 15 12)
                clear * - r24203 e24204 e24205 b24206 b24207 b24208 b24209 d24198
                omega
              have d24210 : (x 15 1 && x 15 12).toNat = 0 := by
                have r24211 := hand2 (x 15 1) (x 15 12)
                have b24212 := hb (x 15 12)
                have b24213 := hb (x 15 1 && x 15 12)
                clear * - r24211 b24212 b24213 d24202
                omega
              have d24214 : (x 14 13).toNat = 0 := by
                have r24215 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24216 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e24217 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b24218 := hb (x 12 3)
                have b24219 := hb (x 13 2)
                have b24220 := hb (x 14 13)
                have b24221 := hb (x 15 12)
                clear * - r24215 e24216 e24217 b24218 b24219 b24220 b24221 d24202 d24198
                omega
              have d24222 : (x 14 2 && x 14 13).toNat = 0 := by
                have r24223 := hand2 (x 14 2) (x 14 13)
                have b24224 := hb (x 14 13)
                have b24225 := hb (x 14 2 && x 14 13)
                clear * - r24223 b24224 b24225 d24214
                omega
              have d24226 : (x 13 2).toNat = 0 := by
                have r24227 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24228 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e24229 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b24230 := hb (x 12 3)
                have b24231 := hb (x 13 2)
                have b24232 := hb (x 14 13)
                have b24233 := hb (x 15 12)
                clear * - r24227 e24228 e24229 b24230 b24231 b24232 b24233 d24202 d24214 d24198
                omega
              have d24234 : (x 10 1).toNat = 1 := by
                have r24235 := hand1 (x 10 1) (x 10 14)
                have b24236 := hb (x 10 1)
                have b24237 := hb (x 10 1 && x 10 14)
                clear * - r24235 b24236 b24237 d24122
                omega
              have d24238 : (x 11 14).toNat = 0 := by
                have r24239 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24240 := hb (x 10 1)
                have b24241 := hb (x 11 14)
                clear * - r24239 b24240 b24241 d24234
                omega
              have d24242 : (x 11 1 && x 11 14).toNat = 0 := by
                have r24243 := hand2 (x 11 1) (x 11 14)
                have b24244 := hb (x 11 14)
                have b24245 := hb (x 11 1 && x 11 14)
                clear * - r24243 b24244 b24245 d24238
                omega
              have d24246 : (x 11 2).toNat = 0 := by
                have r24247 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
                have b24248 := hb (x 11 2)
                have b24249 := hb (x 11 14)
                clear * - r24247 b24248 b24249 d24238
                omega
              have d24250 : (x 10 2).toNat = 0 := by
                have r24251 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24252 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e24253 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b24254 := hb (x 9 3)
                have b24255 := hb (x 10 2)
                have b24256 := hb (x 11 13)
                have b24257 := hb (x 12 12)
                clear * - r24251 e24252 e24253 b24254 b24255 b24256 b24257 d24094 d24110 d24090
                omega
              have d24258 : (x 12 13).toNat = 1 := by
                have r24259 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24260 := hb (x 10 2)
                have b24261 := hb (x 12 13)
                have b24262 := hb (x 11 1 && x 11 14)
                clear * - r24259 b24260 b24261 b24262 d24242 d24250
                omega
              have d24263 : (x 12 1).toNat = 1 := by
                have r24264 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
                have b24265 := hb (x 12 1)
                have b24266 := hb (x 12 13)
                clear * - r24264 b24265 b24266 d24258
                omega
              have d24267 : (x 13 14).toNat = 0 := by
                have r24268 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24269 := hb (x 12 1)
                have b24270 := hb (x 13 14)
                clear * - r24268 b24269 b24270 d24263
                omega
              have d24271 : (x 13 1 && x 13 14).toNat = 0 := by
                have r24272 := hand2 (x 13 1) (x 13 14)
                have b24273 := hb (x 13 14)
                have b24274 := hb (x 13 1 && x 13 14)
                clear * - r24272 b24273 b24274 d24267
                omega
              have d24275 : (x 12 2).toNat = 1 := by
                have r24276 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24277 := hb (x 12 2)
                have b24278 := hb (x 14 13)
                have b24279 := hb (x 13 1 && x 13 14)
                clear * - r24276 b24277 b24278 b24279 d24214 d24271
                omega
              have d24280 : (x 14 12).toNat = 0 := by
                have r24281 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24282 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e24283 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b24284 := hb (x 11 3)
                have b24285 := hb (x 12 2)
                have b24286 := hb (x 13 13)
                have b24287 := hb (x 14 12)
                clear * - r24281 e24282 e24283 b24284 b24285 b24286 b24287 d24275
                omega
              have d24288 : (x 14 4).toNat = 0 := by
                have r24289 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
                have b24290 := hb (x 14 4)
                have b24291 := hb (x 14 12)
                clear * - r24289 b24290 b24291 d24280
                omega
              have d24292 : (x 14 4 && x 14 14).toNat = 0 := by
                have r24293 := hand1 (x 14 4) (x 14 14)
                have b24294 := hb (x 14 4)
                have b24295 := hb (x 14 4 && x 14 14)
                clear * - r24293 b24294 b24295 d24288
                omega
              have d24296 : (x 13 13).toNat = 0 := by
                have r24297 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24298 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e24299 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b24300 := hb (x 11 3)
                have b24301 := hb (x 12 2)
                have b24302 := hb (x 13 13)
                have b24303 := hb (x 14 12)
                clear * - r24297 e24298 e24299 b24300 b24301 b24302 b24303 d24280 d24275
                omega
              have d24304 : (x 13 5).toNat = 0 := by
                have r24305 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
                have b24306 := hb (x 13 5)
                have b24307 := hb (x 13 13)
                clear * - r24305 b24306 b24307 d24296
                omega
              have d24308 : (x 13 3 && x 13 14).toNat = 0 := by
                have r24309 := hand2 (x 13 3) (x 13 14)
                have b24310 := hb (x 13 14)
                have b24311 := hb (x 13 3 && x 13 14)
                clear * - r24309 b24310 b24311 d24267
                omega
              have d24312 : (x 16 11).toNat = 1 := by
                have r24313 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24314 := hb (x 12 4)
                have b24315 := hb (x 16 11)
                have b24316 := hb (x 15 1 && x 15 12)
                have b24317 := hb (x 14 2 && x 14 13)
                have b24318 := hb (x 13 3 && x 13 14)
                clear * - r24313 b24314 b24315 b24316 b24317 b24318 d24210 d24222 d24308 d24106
                omega
              have d24319 : (x 16 3).toNat = 1 := by
                have r24320 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
                have b24321 := hb (x 16 3)
                have b24322 := hb (x 16 11)
                clear * - r24320 b24321 b24322 d24312
                omega
              have d24323 : (x 19 12).toNat = 0 := by
                have r24324 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24325 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e24326 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b24327 := hb (x 16 3)
                have b24328 := hb (x 17 2)
                have b24329 := hb (x 18 13)
                have b24330 := hb (x 19 12)
                clear * - r24324 e24325 e24326 b24327 b24328 b24329 b24330 d24319
                omega
              have d24331 : (x 18 13).toNat = 0 := by
                have r24332 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24333 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e24334 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b24335 := hb (x 16 3)
                have b24336 := hb (x 17 2)
                have b24337 := hb (x 18 13)
                have b24338 := hb (x 19 12)
                clear * - r24332 e24333 e24334 b24335 b24336 b24337 b24338 d24323 d24319
                omega
              have d24339 : (x 17 2).toNat = 0 := by
                have r24340 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24341 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                have e24342 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                have b24343 := hb (x 16 3)
                have b24344 := hb (x 17 2)
                have b24345 := hb (x 18 13)
                have b24346 := hb (x 19 12)
                clear * - r24340 e24341 e24342 b24343 b24344 b24345 b24346 d24323 d24331 d24319
                omega
              have d24347 : (x 13 12).toNat = 0 := by
                have r24348 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24349 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e24350 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b24351 := hb (x 10 3)
                have b24352 := hb (x 11 2)
                have b24353 := hb (x 12 13)
                have b24354 := hb (x 13 12)
                clear * - r24348 e24349 e24350 b24351 b24352 b24353 b24354 d24258 d24246
                omega
              have d24355 : (x 13 4).toNat = 0 := by
                have r24356 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
                have b24357 := hb (x 13 4)
                have b24358 := hb (x 13 12)
                clear * - r24356 b24357 b24358 d24347
                omega
              have d24359 : (x 10 3).toNat = 0 := by
                have r24360 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24361 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e24362 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b24363 := hb (x 10 3)
                have b24364 := hb (x 11 2)
                have b24365 := hb (x 12 13)
                have b24366 := hb (x 13 12)
                clear * - r24360 e24361 e24362 b24363 b24364 b24365 b24366 d24347 d24258 d24246
                omega
              have d24367 : (x 10 3 && x 10 14).toNat = 0 := by
                have r24368 := hand1 (x 10 3) (x 10 14)
                have b24369 := hb (x 10 3)
                have b24370 := hb (x 10 3 && x 10 14)
                clear * - r24368 b24369 b24370 d24359
                omega
              have d24371 : (x 13 11).toNat = 1 := by
                have r24372 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24373 := hb (x 9 4)
                have b24374 := hb (x 13 11)
                have b24375 := hb (x 12 1 && x 12 12)
                have b24376 := hb (x 11 2 && x 11 13)
                have b24377 := hb (x 10 3 && x 10 14)
                clear * - r24372 b24373 b24374 b24375 b24376 b24377 d24102 d24118 d24367 d24067
                omega
              have d24378 : (x 13 3).toNat = 1 := by
                have r24379 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have b24380 := hb (x 13 3)
                have b24381 := hb (x 13 11)
                clear * - r24379 b24380 b24381 d24371
                omega
              have d24382 : (x 16 12).toNat = 0 := by
                have r24383 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24384 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e24385 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b24386 := hb (x 13 3)
                have b24387 := hb (x 14 2)
                have b24388 := hb (x 15 13)
                have b24389 := hb (x 16 12)
                clear * - r24383 e24384 e24385 b24386 b24387 b24388 b24389 d24378
                omega
              have d24390 : (x 16 1 && x 16 12).toNat = 0 := by
                have r24391 := hand2 (x 16 1) (x 16 12)
                have b24392 := hb (x 16 12)
                have b24393 := hb (x 16 1 && x 16 12)
                clear * - r24391 b24392 b24393 d24382
                omega
              have d24394 : (x 16 2 && x 16 12).toNat = 0 := by
                have r24395 := hand2 (x 16 2) (x 16 12)
                have b24396 := hb (x 16 12)
                have b24397 := hb (x 16 2 && x 16 12)
                clear * - r24395 b24396 b24397 d24382
                omega
              have d24398 : (x 15 13).toNat = 0 := by
                have r24399 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24400 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e24401 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b24402 := hb (x 13 3)
                have b24403 := hb (x 14 2)
                have b24404 := hb (x 15 13)
                have b24405 := hb (x 16 12)
                clear * - r24399 e24400 e24401 b24402 b24403 b24404 b24405 d24382 d24378
                omega
              have d24406 : (x 15 2 && x 15 13).toNat = 0 := by
                have r24407 := hand2 (x 15 2) (x 15 13)
                have b24408 := hb (x 15 13)
                have b24409 := hb (x 15 2 && x 15 13)
                clear * - r24407 b24408 b24409 d24398
                omega
              have d24410 : (x 15 3 && x 15 13).toNat = 0 := by
                have r24411 := hand2 (x 15 3) (x 15 13)
                have b24412 := hb (x 15 13)
                have b24413 := hb (x 15 3 && x 15 13)
                clear * - r24411 b24412 b24413 d24398
                omega
              have d24414 : (x 14 1 && x 14 14).toNat = 1 := by
                have r24415 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24416 := hb (x 13 2)
                have b24417 := hb (x 15 13)
                have b24418 := hb (x 14 1 && x 14 14)
                clear * - r24415 b24416 b24417 b24418 d24398 d24226
                omega
              have d24419 : (x 14 1).toNat = 1 := by
                have r24420 := hand1 (x 14 1) (x 14 14)
                have b24421 := hb (x 14 1)
                have b24422 := hb (x 14 1 && x 14 14)
                clear * - r24420 b24421 b24422 d24414
                omega
              have d24423 : (x 15 14).toNat = 0 := by
                have r24424 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24425 := hb (x 14 1)
                have b24426 := hb (x 15 14)
                clear * - r24424 b24425 b24426 d24419
                omega
              have d24427 : (x 15 1 && x 15 14).toNat = 0 := by
                have r24428 := hand2 (x 15 1) (x 15 14)
                have b24429 := hb (x 15 14)
                have b24430 := hb (x 15 1 && x 15 14)
                clear * - r24428 b24429 b24430 d24423
                omega
              have d24431 : (x 15 2).toNat = 0 := by
                have r24432 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
                have b24433 := hb (x 15 2)
                have b24434 := hb (x 15 14)
                clear * - r24432 b24433 b24434 d24423
                omega
              have d24435 : (x 14 2).toNat = 0 := by
                have r24436 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24437 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e24438 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b24439 := hb (x 13 3)
                have b24440 := hb (x 14 2)
                have b24441 := hb (x 15 13)
                have b24442 := hb (x 16 12)
                clear * - r24436 e24437 e24438 b24439 b24440 b24441 b24442 d24382 d24398 d24378
                omega
              have d24443 : (x 16 13).toNat = 1 := by
                have r24444 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24445 := hb (x 14 2)
                have b24446 := hb (x 16 13)
                have b24447 := hb (x 15 1 && x 15 14)
                clear * - r24444 b24445 b24446 b24447 d24427 d24435
                omega
              have d24448 : (x 17 12).toNat = 0 := by
                have r24449 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24450 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e24451 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b24452 := hb (x 14 3)
                have b24453 := hb (x 15 2)
                have b24454 := hb (x 16 13)
                have b24455 := hb (x 17 12)
                clear * - r24449 e24450 e24451 b24452 b24453 b24454 b24455 d24443 d24431
                omega
              have d24456 : (x 14 3).toNat = 0 := by
                have r24457 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24458 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e24459 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b24460 := hb (x 14 3)
                have b24461 := hb (x 15 2)
                have b24462 := hb (x 16 13)
                have b24463 := hb (x 17 12)
                clear * - r24457 e24458 e24459 b24460 b24461 b24462 b24463 d24448 d24443 d24431
                omega
              have d24464 : (x 14 3 && x 14 14).toNat = 0 := by
                have r24465 := hand1 (x 14 3) (x 14 14)
                have b24466 := hb (x 14 3)
                have b24467 := hb (x 14 3 && x 14 14)
                clear * - r24465 b24466 b24467 d24456
                omega
              have d24468 : (x 17 11).toNat = 1 := by
                have r24469 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24470 := hb (x 13 4)
                have b24471 := hb (x 17 11)
                have b24472 := hb (x 16 1 && x 16 12)
                have b24473 := hb (x 15 2 && x 15 13)
                have b24474 := hb (x 14 3 && x 14 14)
                clear * - r24469 b24470 b24471 b24472 b24473 b24474 d24390 d24406 d24464 d24355
                omega
              have d24475 : (x 17 3).toNat = 1 := by
                have r24476 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
                have b24477 := hb (x 17 3)
                have b24478 := hb (x 17 11)
                clear * - r24476 b24477 b24478 d24468
                omega
              have d24479 : (x 20 12).toNat = 0 := by
                have r24480 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24481 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e24482 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b24483 := hb (x 17 3)
                have b24484 := hb (x 18 2)
                have b24485 := hb (x 19 13)
                have b24486 := hb (x 20 12)
                clear * - r24480 e24481 e24482 b24483 b24484 b24485 b24486 d24475
                omega
              have d24487 : (x 19 13).toNat = 0 := by
                have r24488 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24489 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e24490 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b24491 := hb (x 17 3)
                have b24492 := hb (x 18 2)
                have b24493 := hb (x 19 13)
                have b24494 := hb (x 20 12)
                clear * - r24488 e24489 e24490 b24491 b24492 b24493 b24494 d24479 d24475
                omega
              have d24495 : (x 18 1 && x 18 14).toNat = 1 := by
                have r24496 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24497 := hb (x 17 2)
                have b24498 := hb (x 19 13)
                have b24499 := hb (x 18 1 && x 18 14)
                clear * - r24496 b24497 b24498 b24499 d24487 d24339
                omega
              have d24500 : (x 18 14).toNat = 1 := by
                have r24501 := hand2 (x 18 1) (x 18 14)
                have b24502 := hb (x 18 14)
                have b24503 := hb (x 18 1 && x 18 14)
                clear * - r24501 b24502 b24503 d24495
                omega
              have d24504 : (x 17 1).toNat = 0 := by
                have r24505 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24506 := hb (x 17 1)
                have b24507 := hb (x 18 14)
                clear * - r24505 b24506 b24507 d24500
                omega
              have d24508 : (x 17 1 && x 17 11).toNat = 0 := by
                have r24509 := hand1 (x 17 1) (x 17 11)
                have b24510 := hb (x 17 1)
                have b24511 := hb (x 17 1 && x 17 11)
                clear * - r24509 b24510 b24511 d24504
                omega
              have d24512 : (x 18 2).toNat = 0 := by
                have r24513 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24514 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
                have e24515 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
                have b24516 := hb (x 17 3)
                have b24517 := hb (x 18 2)
                have b24518 := hb (x 19 13)
                have b24519 := hb (x 20 12)
                clear * - r24513 e24514 e24515 b24516 b24517 b24518 b24519 d24479 d24487 d24475
                omega
              have d24520 : (x 18 10).toNat = 0 := by
                have r24521 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
                have b24522 := hb (x 18 2)
                have b24523 := hb (x 18 10)
                clear * - r24521 b24522 b24523 d24512
                omega
              have r24524 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b24525 := hb (x 13 5)
              have b24526 := hb (x 18 10)
              have b24527 := hb (x 17 1 && x 17 11)
              have b24528 := hb (x 16 2 && x 16 12)
              have b24529 := hb (x 15 3 && x 15 13)
              have b24530 := hb (x 14 4 && x 14 14)
              linarith only [r24524, b24525, b24526, b24527, b24528, b24529, b24530, d24520, d24508, d24394, d24410, d24292, d24304]
          · have f24531 : (x (-1) 6).toNat = 1 := by rw [h23372]; rfl
            have d24532 : (x 5 8).toNat = 0 := by
              have r24533 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24534 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e24535 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e24536 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e24537 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e24538 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e24539 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b24540 := hb (x (-2) 7)
              have b24541 := hb (x (-1) 6)
              have b24542 := hb (x 0 5)
              have b24543 := hb (x 1 4)
              have b24544 := hb (x 2 11)
              have b24545 := hb (x 3 10)
              have b24546 := hb (x 4 9)
              have b24547 := hb (x 5 8)
              clear * - r24533 e24534 e24535 e24536 e24537 e24538 e24539 b24540 b24541 b24542 b24543 b24544 b24545 b24546 b24547 g36 g25 g17 f24531
              omega
            have d24548 : (x 4 9).toNat = 0 := by
              have r24549 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24550 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e24551 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e24552 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e24553 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e24554 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e24555 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b24556 := hb (x (-2) 7)
              have b24557 := hb (x (-1) 6)
              have b24558 := hb (x 0 5)
              have b24559 := hb (x 1 4)
              have b24560 := hb (x 2 11)
              have b24561 := hb (x 3 10)
              have b24562 := hb (x 4 9)
              have b24563 := hb (x 5 8)
              clear * - r24549 e24550 e24551 e24552 e24553 e24554 e24555 b24556 b24557 b24558 b24559 b24560 b24561 b24562 b24563 d24532 g36 g25 g17 f24531
              omega
            have d24564 : (x 2 11).toNat = 0 := by
              have r24565 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24566 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e24567 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e24568 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e24569 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e24570 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e24571 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b24572 := hb (x (-2) 7)
              have b24573 := hb (x (-1) 6)
              have b24574 := hb (x 0 5)
              have b24575 := hb (x 1 4)
              have b24576 := hb (x 2 11)
              have b24577 := hb (x 3 10)
              have b24578 := hb (x 4 9)
              have b24579 := hb (x 5 8)
              clear * - r24565 e24566 e24567 e24568 e24569 e24570 e24571 b24572 b24573 b24574 b24575 b24576 b24577 b24578 b24579 d24532 d24548 g36 g25 g17 f24531
              omega
            have d24580 : (x 2 1 && x 2 11).toNat = 0 := by
              have r24581 := hand2 (x 2 1) (x 2 11)
              have b24582 := hb (x 2 11)
              have b24583 := hb (x 2 1 && x 2 11)
              clear * - r24581 b24582 b24583 d24564
              omega
            have d24584 : (x (-1) 4 && x (-1) 14).toNat = 1 := by
              have r24585 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b24586 := hb (x (-2) 5)
              have b24587 := hb (x 3 10)
              have b24588 := hb (x 2 1 && x 2 11)
              have b24589 := hb (x 1 2 && x 1 12)
              have b24590 := hb (x 0 3 && x 0 13)
              have b24591 := hb (x (-1) 4 && x (-1) 14)
              clear * - r24585 b24586 b24587 b24588 b24589 b24590 b24591 g36 d24580 g90 g91 g6
              omega
            have d24592 : (x (-1) 4).toNat = 1 := by
              have r24593 := hand1 (x (-1) 4) (x (-1) 14)
              have b24594 := hb (x (-1) 4)
              have b24595 := hb (x (-1) 4 && x (-1) 14)
              clear * - r24593 b24594 b24595 d24584
              omega
            have d24596 : (x (-1) 12).toNat = 1 := by
              have r24597 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
              have b24598 := hb (x (-1) 4)
              have b24599 := hb (x (-1) 12)
              clear * - r24597 b24598 b24599 d24592
              omega
            have d24600 : (x (-3) 2).toNat = 0 := by
              have r24601 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24602 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e24603 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b24604 := hb (x (-4) 3)
              have b24605 := hb (x (-3) 2)
              have b24606 := hb (x (-2) 13)
              have b24607 := hb (x (-1) 12)
              clear * - r24601 e24602 e24603 b24604 b24605 b24606 b24607 d24596 g10
              omega
            have d24608 : (x (-1) 13).toNat = 1 := by
              have r24609 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b24610 := hb (x (-3) 2)
              have b24611 := hb (x (-1) 13)
              have b24612 := hb (x (-2) 1 && x (-2) 14)
              clear * - r24609 b24610 b24611 b24612 g107 d24600
              omega
            have d24613 : (x (-2) 2).toNat = 0 := by
              have r24614 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e24615 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e24616 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have b24617 := hb (x (-3) 3)
              have b24618 := hb (x (-2) 2)
              have b24619 := hb (x (-1) 13)
              have b24620 := hb (x 0 12)
              clear * - r24614 e24615 e24616 b24617 b24618 b24619 b24620 f22835 d24608
              omega
            have d24621 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
              have r24622 := hand1 (x (-2) 2) (x (-2) 12)
              have b24623 := hb (x (-2) 2)
              have b24624 := hb (x (-2) 2 && x (-2) 12)
              clear * - r24622 b24623 b24624 d24613
              omega
            have d24625 : (x (-3) 3 && x (-3) 13).toNat = 1 := by
              have r24626 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b24627 := hb (x (-5) 5)
              have b24628 := hb (x 0 10)
              have b24629 := hb (x (-1) 1 && x (-1) 11)
              have b24630 := hb (x (-2) 2 && x (-2) 12)
              have b24631 := hb (x (-3) 3 && x (-3) 13)
              have b24632 := hb (x (-4) 4 && x (-4) 14)
              clear * - r24626 b24627 b24628 b24629 b24630 b24631 b24632 g21 d23364 d24621 g89 g2
              omega
            have d24633 : (x (-3) 3).toNat = 1 := by
              have r24634 := hand1 (x (-3) 3) (x (-3) 13)
              have b24635 := hb (x (-3) 3)
              have b24636 := hb (x (-3) 3 && x (-3) 13)
              clear * - r24634 b24635 b24636 d24625
              omega
            have r24637 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24638 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e24639 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b24640 := hb (x (-3) 3)
            have b24641 := hb (x (-2) 2)
            have b24642 := hb (x (-1) 13)
            have b24643 := hb (x 0 12)
            linarith only [r24637, e24638, e24639, b24640, b24641, b24642, b24643, f22835, d24608, d24613, d24633]
        · have f24644 : (x (-1) 3).toNat = 1 := by rw [h23358]; rfl
          have d24645 : (x 2 12).toNat = 0 := by
            have r24646 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24647 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
            have e24648 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
            have b24649 := hb (x (-1) 3)
            have b24650 := hb (x 0 2)
            have b24651 := hb (x 1 13)
            have b24652 := hb (x 2 12)
            clear * - r24646 e24647 e24648 b24649 b24650 b24651 b24652 g29 g14 f24644
            omega
          have d24653 : (x 2 1 && x 2 12).toNat = 0 := by
            have r24654 := hand2 (x 2 1) (x 2 12)
            have b24655 := hb (x 2 12)
            have b24656 := hb (x 2 1 && x 2 12)
            clear * - r24654 b24655 b24656 d24645
            omega
          have d24657 : (x 2 2 && x 2 12).toNat = 0 := by
            have r24658 := hand2 (x 2 2) (x 2 12)
            have b24659 := hb (x 2 12)
            have b24660 := hb (x 2 2 && x 2 12)
            clear * - r24658 b24659 b24660 d24645
            omega
          have d24661 : (x 2 4).toNat = 0 := by
            have r24662 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
            have b24663 := hb (x 2 4)
            have b24664 := hb (x 2 12)
            clear * - r24662 b24663 b24664 d24645
            omega
          have d24665 : (x 2 4 && x 2 14).toNat = 0 := by
            have r24666 := hand1 (x 2 4) (x 2 14)
            have b24667 := hb (x 2 4)
            have b24668 := hb (x 2 4 && x 2 14)
            clear * - r24666 b24667 b24668 d24661
            omega
          cases h24669 : x 1 3
          · have f24670 : (x 1 3).toNat = 0 := by rw [h24669]; rfl
            have d24671 : (x 1 3 && x 1 14).toNat = 0 := by
              have r24672 := hand1 (x 1 3) (x 1 14)
              have b24673 := hb (x 1 3)
              have b24674 := hb (x 1 3 && x 1 14)
              clear * - r24672 b24673 b24674 f24670
              omega
            have d24675 : (x 1 11).toNat = 0 := by
              have r24676 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
              have b24677 := hb (x 1 3)
              have b24678 := hb (x 1 11)
              clear * - r24676 b24677 b24678 f24670
              omega
            have d24679 : (x 1 11 && x 1 14).toNat = 0 := by
              have r24680 := hand1 (x 1 11) (x 1 14)
              have b24681 := hb (x 1 11)
              have b24682 := hb (x 1 11 && x 1 14)
              clear * - r24680 b24681 b24682 d24675
              omega
            cases h24683 : x (-1) 4
            · have f24684 : (x (-1) 4).toNat = 0 := by rw [h24683]; rfl
              have d24685 : (x 3 11).toNat = 1 := by
                have r24686 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24687 := hb (x (-1) 4)
                have b24688 := hb (x 3 11)
                have b24689 := hb (x 2 1 && x 2 12)
                have b24690 := hb (x 1 2 && x 1 13)
                have b24691 := hb (x 0 3 && x 0 14)
                clear * - r24686 b24687 b24688 b24689 b24690 b24691 d24653 g102 g103 f24684
                omega
              have d24692 : (x 3 3).toNat = 1 := by
                have r24693 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                have b24694 := hb (x 3 3)
                have b24695 := hb (x 3 11)
                clear * - r24693 b24694 b24695 d24685
                omega
              have d24696 : (x 6 12).toNat = 0 := by
                have r24697 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24698 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e24699 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b24700 := hb (x 3 3)
                have b24701 := hb (x 4 2)
                have b24702 := hb (x 5 13)
                have b24703 := hb (x 6 12)
                clear * - r24697 e24698 e24699 b24700 b24701 b24702 b24703 d24692
                omega
              have d24704 : (x 6 1 && x 6 12).toNat = 0 := by
                have r24705 := hand2 (x 6 1) (x 6 12)
                have b24706 := hb (x 6 12)
                have b24707 := hb (x 6 1 && x 6 12)
                clear * - r24705 b24706 b24707 d24696
                omega
              have d24708 : (x 6 4).toNat = 0 := by
                have r24709 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                have b24710 := hb (x 6 4)
                have b24711 := hb (x 6 12)
                clear * - r24709 b24710 b24711 d24696
                omega
              have d24712 : (x 5 13).toNat = 0 := by
                have r24713 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24714 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e24715 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b24716 := hb (x 3 3)
                have b24717 := hb (x 4 2)
                have b24718 := hb (x 5 13)
                have b24719 := hb (x 6 12)
                clear * - r24713 e24714 e24715 b24716 b24717 b24718 b24719 d24696 d24692
                omega
              have d24720 : (x 5 2 && x 5 13).toNat = 0 := by
                have r24721 := hand2 (x 5 2) (x 5 13)
                have b24722 := hb (x 5 13)
                have b24723 := hb (x 5 2 && x 5 13)
                clear * - r24721 b24722 b24723 d24712
                omega
              have d24724 : (x 4 1 && x 4 14).toNat = 1 := by
                have r24725 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24726 := hb (x 3 2)
                have b24727 := hb (x 5 13)
                have b24728 := hb (x 4 1 && x 4 14)
                clear * - r24725 b24726 b24727 b24728 d24712 g33
                omega
              have d24729 : (x 4 1).toNat = 1 := by
                have r24730 := hand1 (x 4 1) (x 4 14)
                have b24731 := hb (x 4 1)
                have b24732 := hb (x 4 1 && x 4 14)
                clear * - r24730 b24731 b24732 d24724
                omega
              have d24733 : (x 5 14).toNat = 0 := by
                have r24734 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24735 := hb (x 4 1)
                have b24736 := hb (x 5 14)
                clear * - r24734 b24735 b24736 d24729
                omega
              have d24737 : (x 5 1 && x 5 14).toNat = 0 := by
                have r24738 := hand2 (x 5 1) (x 5 14)
                have b24739 := hb (x 5 14)
                have b24740 := hb (x 5 1 && x 5 14)
                clear * - r24738 b24739 b24740 d24733
                omega
              have d24741 : (x 5 2).toNat = 0 := by
                have r24742 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b24743 := hb (x 5 2)
                have b24744 := hb (x 5 14)
                clear * - r24742 b24743 b24744 d24733
                omega
              have d24745 : (x 4 2).toNat = 0 := by
                have r24746 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24747 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e24748 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b24749 := hb (x 3 3)
                have b24750 := hb (x 4 2)
                have b24751 := hb (x 5 13)
                have b24752 := hb (x 6 12)
                clear * - r24746 e24747 e24748 b24749 b24750 b24751 b24752 d24696 d24712 d24692
                omega
              have d24753 : (x 4 2 && x 4 13).toNat = 0 := by
                have r24754 := hand1 (x 4 2) (x 4 13)
                have b24755 := hb (x 4 2)
                have b24756 := hb (x 4 2 && x 4 13)
                clear * - r24754 b24755 b24756 d24745
                omega
              have d24757 : (x 6 13).toNat = 1 := by
                have r24758 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24759 := hb (x 4 2)
                have b24760 := hb (x 6 13)
                have b24761 := hb (x 5 1 && x 5 14)
                clear * - r24758 b24759 b24760 b24761 d24737 d24745
                omega
              have d24762 : (x 6 1).toNat = 1 := by
                have r24763 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
                have b24764 := hb (x 6 1)
                have b24765 := hb (x 6 13)
                clear * - r24763 b24764 b24765 d24757
                omega
              have d24766 : (x 7 14).toNat = 0 := by
                have r24767 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24768 := hb (x 6 1)
                have b24769 := hb (x 7 14)
                clear * - r24767 b24768 b24769 d24762
                omega
              have d24770 : (x 7 3 && x 7 14).toNat = 0 := by
                have r24771 := hand2 (x 7 3) (x 7 14)
                have b24772 := hb (x 7 14)
                have b24773 := hb (x 7 3 && x 7 14)
                clear * - r24771 b24772 b24773 d24766
                omega
              have d24774 : (x 7 2).toNat = 0 := by
                have r24775 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
                have b24776 := hb (x 7 2)
                have b24777 := hb (x 7 14)
                clear * - r24775 b24776 b24777 d24766
                omega
              have d24778 : (x 7 12).toNat = 0 := by
                have r24779 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24780 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e24781 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b24782 := hb (x 4 3)
                have b24783 := hb (x 5 2)
                have b24784 := hb (x 6 13)
                have b24785 := hb (x 7 12)
                clear * - r24779 e24780 e24781 b24782 b24783 b24784 b24785 d24757 d24741
                omega
              have d24786 : (x 7 4).toNat = 0 := by
                have r24787 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have b24788 := hb (x 7 4)
                have b24789 := hb (x 7 12)
                clear * - r24787 b24788 b24789 d24778
                omega
              have d24790 : (x 4 3).toNat = 0 := by
                have r24791 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24792 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e24793 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b24794 := hb (x 4 3)
                have b24795 := hb (x 5 2)
                have b24796 := hb (x 6 13)
                have b24797 := hb (x 7 12)
                clear * - r24791 e24792 e24793 b24794 b24795 b24796 b24797 d24778 d24757 d24741
                omega
              have d24798 : (x 4 3 && x 4 14).toNat = 0 := by
                have r24799 := hand1 (x 4 3) (x 4 14)
                have b24800 := hb (x 4 3)
                have b24801 := hb (x 4 3 && x 4 14)
                clear * - r24799 b24800 b24801 d24790
                omega
              have d24802 : (x 7 11).toNat = 1 := by
                have r24803 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24804 := hb (x 3 4)
                have b24805 := hb (x 7 11)
                have b24806 := hb (x 6 1 && x 6 12)
                have b24807 := hb (x 5 2 && x 5 13)
                have b24808 := hb (x 4 3 && x 4 14)
                clear * - r24803 b24804 b24805 b24806 b24807 b24808 d24704 d24720 d24798 g34
                omega
              have d24809 : (x 7 3).toNat = 1 := by
                have r24810 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                have b24811 := hb (x 7 3)
                have b24812 := hb (x 7 11)
                clear * - r24810 b24811 b24812 d24802
                omega
              have d24813 : (x 10 12).toNat = 0 := by
                have r24814 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24815 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e24816 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b24817 := hb (x 7 3)
                have b24818 := hb (x 8 2)
                have b24819 := hb (x 9 13)
                have b24820 := hb (x 10 12)
                clear * - r24814 e24815 e24816 b24817 b24818 b24819 b24820 d24809
                omega
              have d24821 : (x 10 1 && x 10 12).toNat = 0 := by
                have r24822 := hand2 (x 10 1) (x 10 12)
                have b24823 := hb (x 10 12)
                have b24824 := hb (x 10 1 && x 10 12)
                clear * - r24822 b24823 b24824 d24813
                omega
              have d24825 : (x 10 4).toNat = 0 := by
                have r24826 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                have b24827 := hb (x 10 4)
                have b24828 := hb (x 10 12)
                clear * - r24826 b24827 b24828 d24813
                omega
              have d24829 : (x 9 13).toNat = 0 := by
                have r24830 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24831 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e24832 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b24833 := hb (x 7 3)
                have b24834 := hb (x 8 2)
                have b24835 := hb (x 9 13)
                have b24836 := hb (x 10 12)
                clear * - r24830 e24831 e24832 b24833 b24834 b24835 b24836 d24813 d24809
                omega
              have d24837 : (x 9 2 && x 9 13).toNat = 0 := by
                have r24838 := hand2 (x 9 2) (x 9 13)
                have b24839 := hb (x 9 13)
                have b24840 := hb (x 9 2 && x 9 13)
                clear * - r24838 b24839 b24840 d24829
                omega
              have d24841 : (x 8 1 && x 8 14).toNat = 1 := by
                have r24842 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24843 := hb (x 7 2)
                have b24844 := hb (x 9 13)
                have b24845 := hb (x 8 1 && x 8 14)
                clear * - r24842 b24843 b24844 b24845 d24829 d24774
                omega
              have d24846 : (x 8 14).toNat = 1 := by
                have r24847 := hand2 (x 8 1) (x 8 14)
                have b24848 := hb (x 8 14)
                have b24849 := hb (x 8 1 && x 8 14)
                clear * - r24847 b24848 b24849 d24841
                omega
              have d24850 : (x 7 1).toNat = 0 := by
                have r24851 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24852 := hb (x 7 1)
                have b24853 := hb (x 8 14)
                clear * - r24851 b24852 b24853 d24846
                omega
              have d24854 : (x 7 13).toNat = 0 := by
                have r24855 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                have b24856 := hb (x 7 1)
                have b24857 := hb (x 7 13)
                clear * - r24855 b24856 b24857 d24850
                omega
              have d24858 : (x 6 1 && x 6 14).toNat = 1 := by
                have r24859 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24860 := hb (x 5 2)
                have b24861 := hb (x 7 13)
                have b24862 := hb (x 6 1 && x 6 14)
                clear * - r24859 b24860 b24861 b24862 d24854 d24741
                omega
              have d24863 : (x 6 14).toNat = 1 := by
                have r24864 := hand2 (x 6 1) (x 6 14)
                have b24865 := hb (x 6 14)
                have b24866 := hb (x 6 1 && x 6 14)
                clear * - r24864 b24865 b24866 d24858
                omega
              have d24867 : (x 5 1).toNat = 0 := by
                have r24868 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24869 := hb (x 5 1)
                have b24870 := hb (x 6 14)
                clear * - r24868 b24869 b24870 d24863
                omega
              have d24871 : (x 5 1 && x 5 12).toNat = 0 := by
                have r24872 := hand1 (x 5 1) (x 5 12)
                have b24873 := hb (x 5 1)
                have b24874 := hb (x 5 1 && x 5 12)
                clear * - r24872 b24873 b24874 d24867
                omega
              have d24875 : (x 6 11).toNat = 1 := by
                have r24876 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24877 := hb (x 2 4)
                have b24878 := hb (x 6 11)
                have b24879 := hb (x 5 1 && x 5 12)
                have b24880 := hb (x 4 2 && x 4 13)
                have b24881 := hb (x 3 3 && x 3 14)
                clear * - r24876 b24877 b24878 b24879 b24880 b24881 d24871 d24753 g106 d24661
                omega
              have d24882 : (x 6 3).toNat = 1 := by
                have r24883 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                have b24884 := hb (x 6 3)
                have b24885 := hb (x 6 11)
                clear * - r24883 b24884 b24885 d24875
                omega
              have d24886 : (x 9 12).toNat = 0 := by
                have r24887 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24888 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e24889 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b24890 := hb (x 6 3)
                have b24891 := hb (x 7 2)
                have b24892 := hb (x 8 13)
                have b24893 := hb (x 9 12)
                clear * - r24887 e24888 e24889 b24890 b24891 b24892 b24893 d24774 d24882
                omega
              have d24894 : (x 9 1 && x 9 12).toNat = 0 := by
                have r24895 := hand2 (x 9 1) (x 9 12)
                have b24896 := hb (x 9 12)
                have b24897 := hb (x 9 1 && x 9 12)
                clear * - r24895 b24896 b24897 d24886
                omega
              have d24898 : (x 8 13).toNat = 0 := by
                have r24899 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24900 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e24901 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b24902 := hb (x 6 3)
                have b24903 := hb (x 7 2)
                have b24904 := hb (x 8 13)
                have b24905 := hb (x 9 12)
                clear * - r24899 e24900 e24901 b24902 b24903 b24904 b24905 d24886 d24774 d24882
                omega
              have d24906 : (x 8 2 && x 8 13).toNat = 0 := by
                have r24907 := hand2 (x 8 2) (x 8 13)
                have b24908 := hb (x 8 13)
                have b24909 := hb (x 8 2 && x 8 13)
                clear * - r24907 b24908 b24909 d24898
                omega
              have d24910 : (x 10 11).toNat = 1 := by
                have r24911 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24912 := hb (x 6 4)
                have b24913 := hb (x 10 11)
                have b24914 := hb (x 9 1 && x 9 12)
                have b24915 := hb (x 8 2 && x 8 13)
                have b24916 := hb (x 7 3 && x 7 14)
                clear * - r24911 b24912 b24913 b24914 b24915 b24916 d24894 d24906 d24770 d24708
                omega
              have d24917 : (x 10 3).toNat = 1 := by
                have r24918 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
                have b24919 := hb (x 10 3)
                have b24920 := hb (x 10 11)
                clear * - r24918 b24919 b24920 d24910
                omega
              have d24921 : (x 13 12).toNat = 0 := by
                have r24922 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24923 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e24924 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b24925 := hb (x 10 3)
                have b24926 := hb (x 11 2)
                have b24927 := hb (x 12 13)
                have b24928 := hb (x 13 12)
                clear * - r24922 e24923 e24924 b24925 b24926 b24927 b24928 d24917
                omega
              have d24929 : (x 13 1 && x 13 12).toNat = 0 := by
                have r24930 := hand2 (x 13 1) (x 13 12)
                have b24931 := hb (x 13 12)
                have b24932 := hb (x 13 1 && x 13 12)
                clear * - r24930 b24931 b24932 d24921
                omega
              have d24933 : (x 12 13).toNat = 0 := by
                have r24934 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24935 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e24936 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b24937 := hb (x 10 3)
                have b24938 := hb (x 11 2)
                have b24939 := hb (x 12 13)
                have b24940 := hb (x 13 12)
                clear * - r24934 e24935 e24936 b24937 b24938 b24939 b24940 d24921 d24917
                omega
              have d24941 : (x 12 2 && x 12 13).toNat = 0 := by
                have r24942 := hand2 (x 12 2) (x 12 13)
                have b24943 := hb (x 12 13)
                have b24944 := hb (x 12 2 && x 12 13)
                clear * - r24942 b24943 b24944 d24933
                omega
              have d24945 : (x 11 2).toNat = 0 := by
                have r24946 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24947 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                have e24948 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                have b24949 := hb (x 10 3)
                have b24950 := hb (x 11 2)
                have b24951 := hb (x 12 13)
                have b24952 := hb (x 13 12)
                clear * - r24946 e24947 e24948 b24949 b24950 b24951 b24952 d24921 d24933 d24917
                omega
              have d24953 : (x 8 1).toNat = 1 := by
                have r24954 := hand1 (x 8 1) (x 8 14)
                have b24955 := hb (x 8 1)
                have b24956 := hb (x 8 1 && x 8 14)
                clear * - r24954 b24955 b24956 d24841
                omega
              have d24957 : (x 9 14).toNat = 0 := by
                have r24958 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24959 := hb (x 8 1)
                have b24960 := hb (x 9 14)
                clear * - r24958 b24959 b24960 d24953
                omega
              have d24961 : (x 9 1 && x 9 14).toNat = 0 := by
                have r24962 := hand2 (x 9 1) (x 9 14)
                have b24963 := hb (x 9 14)
                have b24964 := hb (x 9 1 && x 9 14)
                clear * - r24962 b24963 b24964 d24957
                omega
              have d24965 : (x 9 2).toNat = 0 := by
                have r24966 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                have b24967 := hb (x 9 2)
                have b24968 := hb (x 9 14)
                clear * - r24966 b24967 b24968 d24957
                omega
              have d24969 : (x 8 2).toNat = 0 := by
                have r24970 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e24971 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e24972 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have b24973 := hb (x 7 3)
                have b24974 := hb (x 8 2)
                have b24975 := hb (x 9 13)
                have b24976 := hb (x 10 12)
                clear * - r24970 e24971 e24972 b24973 b24974 b24975 b24976 d24813 d24829 d24809
                omega
              have d24977 : (x 10 13).toNat = 1 := by
                have r24978 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24979 := hb (x 8 2)
                have b24980 := hb (x 10 13)
                have b24981 := hb (x 9 1 && x 9 14)
                clear * - r24978 b24979 b24980 b24981 d24961 d24969
                omega
              have d24982 : (x 10 1).toNat = 1 := by
                have r24983 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                have b24984 := hb (x 10 1)
                have b24985 := hb (x 10 13)
                clear * - r24983 b24984 b24985 d24977
                omega
              have d24986 : (x 11 14).toNat = 0 := by
                have r24987 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24988 := hb (x 10 1)
                have b24989 := hb (x 11 14)
                clear * - r24987 b24988 b24989 d24982
                omega
              have d24990 : (x 11 1 && x 11 14).toNat = 0 := by
                have r24991 := hand2 (x 11 1) (x 11 14)
                have b24992 := hb (x 11 14)
                have b24993 := hb (x 11 1 && x 11 14)
                clear * - r24991 b24992 b24993 d24986
                omega
              have d24994 : (x 10 2).toNat = 1 := by
                have r24995 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b24996 := hb (x 10 2)
                have b24997 := hb (x 12 13)
                have b24998 := hb (x 11 1 && x 11 14)
                clear * - r24995 b24996 b24997 b24998 d24933 d24990
                omega
              have d24999 : (x 12 12).toNat = 0 := by
                have r25000 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25001 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e25002 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b25003 := hb (x 9 3)
                have b25004 := hb (x 10 2)
                have b25005 := hb (x 11 13)
                have b25006 := hb (x 12 12)
                clear * - r25000 e25001 e25002 b25003 b25004 b25005 b25006 d24994
                omega
              have d25007 : (x 12 4).toNat = 0 := by
                have r25008 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
                have b25009 := hb (x 12 4)
                have b25010 := hb (x 12 12)
                clear * - r25008 b25009 b25010 d24999
                omega
              have d25011 : (x 12 4 && x 12 14).toNat = 0 := by
                have r25012 := hand1 (x 12 4) (x 12 14)
                have b25013 := hb (x 12 4)
                have b25014 := hb (x 12 4 && x 12 14)
                clear * - r25012 b25013 b25014 d25007
                omega
              have d25015 : (x 11 13).toNat = 0 := by
                have r25016 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25017 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e25018 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have b25019 := hb (x 9 3)
                have b25020 := hb (x 10 2)
                have b25021 := hb (x 11 13)
                have b25022 := hb (x 12 12)
                clear * - r25016 e25017 e25018 b25019 b25020 b25021 b25022 d24999 d24994
                omega
              have d25023 : (x 11 5).toNat = 0 := by
                have r25024 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
                have b25025 := hb (x 11 5)
                have b25026 := hb (x 11 13)
                clear * - r25024 b25025 b25026 d25015
                omega
              have d25027 : (x 11 3 && x 11 14).toNat = 0 := by
                have r25028 := hand2 (x 11 3) (x 11 14)
                have b25029 := hb (x 11 14)
                have b25030 := hb (x 11 3 && x 11 14)
                clear * - r25028 b25029 b25030 d24986
                omega
              have d25031 : (x 14 11).toNat = 1 := by
                have r25032 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25033 := hb (x 10 4)
                have b25034 := hb (x 14 11)
                have b25035 := hb (x 13 1 && x 13 12)
                have b25036 := hb (x 12 2 && x 12 13)
                have b25037 := hb (x 11 3 && x 11 14)
                clear * - r25032 b25033 b25034 b25035 b25036 b25037 d24929 d24941 d25027 d24825
                omega
              have d25038 : (x 14 3).toNat = 1 := by
                have r25039 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                have b25040 := hb (x 14 3)
                have b25041 := hb (x 14 11)
                clear * - r25039 b25040 b25041 d25031
                omega
              have d25042 : (x 17 12).toNat = 0 := by
                have r25043 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25044 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e25045 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b25046 := hb (x 14 3)
                have b25047 := hb (x 15 2)
                have b25048 := hb (x 16 13)
                have b25049 := hb (x 17 12)
                clear * - r25043 e25044 e25045 b25046 b25047 b25048 b25049 d25038
                omega
              have d25050 : (x 16 13).toNat = 0 := by
                have r25051 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25052 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e25053 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b25054 := hb (x 14 3)
                have b25055 := hb (x 15 2)
                have b25056 := hb (x 16 13)
                have b25057 := hb (x 17 12)
                clear * - r25051 e25052 e25053 b25054 b25055 b25056 b25057 d25042 d25038
                omega
              have d25058 : (x 15 2).toNat = 0 := by
                have r25059 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25060 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                have e25061 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                have b25062 := hb (x 14 3)
                have b25063 := hb (x 15 2)
                have b25064 := hb (x 16 13)
                have b25065 := hb (x 17 12)
                clear * - r25059 e25060 e25061 b25062 b25063 b25064 b25065 d25042 d25050 d25038
                omega
              have d25066 : (x 11 12).toNat = 0 := by
                have r25067 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25068 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e25069 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b25070 := hb (x 8 3)
                have b25071 := hb (x 9 2)
                have b25072 := hb (x 10 13)
                have b25073 := hb (x 11 12)
                clear * - r25067 e25068 e25069 b25070 b25071 b25072 b25073 d24977 d24965
                omega
              have d25074 : (x 11 4).toNat = 0 := by
                have r25075 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                have b25076 := hb (x 11 4)
                have b25077 := hb (x 11 12)
                clear * - r25075 b25076 b25077 d25066
                omega
              have d25078 : (x 8 3).toNat = 0 := by
                have r25079 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25080 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                have e25081 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                have b25082 := hb (x 8 3)
                have b25083 := hb (x 9 2)
                have b25084 := hb (x 10 13)
                have b25085 := hb (x 11 12)
                clear * - r25079 e25080 e25081 b25082 b25083 b25084 b25085 d25066 d24977 d24965
                omega
              have d25086 : (x 8 3 && x 8 14).toNat = 0 := by
                have r25087 := hand1 (x 8 3) (x 8 14)
                have b25088 := hb (x 8 3)
                have b25089 := hb (x 8 3 && x 8 14)
                clear * - r25087 b25088 b25089 d25078
                omega
              have d25090 : (x 11 11).toNat = 1 := by
                have r25091 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25092 := hb (x 7 4)
                have b25093 := hb (x 11 11)
                have b25094 := hb (x 10 1 && x 10 12)
                have b25095 := hb (x 9 2 && x 9 13)
                have b25096 := hb (x 8 3 && x 8 14)
                clear * - r25091 b25092 b25093 b25094 b25095 b25096 d24821 d24837 d25086 d24786
                omega
              have d25097 : (x 11 3).toNat = 1 := by
                have r25098 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
                have b25099 := hb (x 11 3)
                have b25100 := hb (x 11 11)
                clear * - r25098 b25099 b25100 d25090
                omega
              have d25101 : (x 14 12).toNat = 0 := by
                have r25102 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25103 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e25104 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b25105 := hb (x 11 3)
                have b25106 := hb (x 12 2)
                have b25107 := hb (x 13 13)
                have b25108 := hb (x 14 12)
                clear * - r25102 e25103 e25104 b25105 b25106 b25107 b25108 d25097
                omega
              have d25109 : (x 14 1 && x 14 12).toNat = 0 := by
                have r25110 := hand2 (x 14 1) (x 14 12)
                have b25111 := hb (x 14 12)
                have b25112 := hb (x 14 1 && x 14 12)
                clear * - r25110 b25111 b25112 d25101
                omega
              have d25113 : (x 14 2 && x 14 12).toNat = 0 := by
                have r25114 := hand2 (x 14 2) (x 14 12)
                have b25115 := hb (x 14 12)
                have b25116 := hb (x 14 2 && x 14 12)
                clear * - r25114 b25115 b25116 d25101
                omega
              have d25117 : (x 13 13).toNat = 0 := by
                have r25118 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25119 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e25120 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b25121 := hb (x 11 3)
                have b25122 := hb (x 12 2)
                have b25123 := hb (x 13 13)
                have b25124 := hb (x 14 12)
                clear * - r25118 e25119 e25120 b25121 b25122 b25123 b25124 d25101 d25097
                omega
              have d25125 : (x 13 2 && x 13 13).toNat = 0 := by
                have r25126 := hand2 (x 13 2) (x 13 13)
                have b25127 := hb (x 13 13)
                have b25128 := hb (x 13 2 && x 13 13)
                clear * - r25126 b25127 b25128 d25117
                omega
              have d25129 : (x 13 3 && x 13 13).toNat = 0 := by
                have r25130 := hand2 (x 13 3) (x 13 13)
                have b25131 := hb (x 13 13)
                have b25132 := hb (x 13 3 && x 13 13)
                clear * - r25130 b25131 b25132 d25117
                omega
              have d25133 : (x 12 1 && x 12 14).toNat = 1 := by
                have r25134 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25135 := hb (x 11 2)
                have b25136 := hb (x 13 13)
                have b25137 := hb (x 12 1 && x 12 14)
                clear * - r25134 b25135 b25136 b25137 d25117 d24945
                omega
              have d25138 : (x 12 1).toNat = 1 := by
                have r25139 := hand1 (x 12 1) (x 12 14)
                have b25140 := hb (x 12 1)
                have b25141 := hb (x 12 1 && x 12 14)
                clear * - r25139 b25140 b25141 d25133
                omega
              have d25142 : (x 13 14).toNat = 0 := by
                have r25143 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25144 := hb (x 12 1)
                have b25145 := hb (x 13 14)
                clear * - r25143 b25144 b25145 d25138
                omega
              have d25146 : (x 13 1 && x 13 14).toNat = 0 := by
                have r25147 := hand2 (x 13 1) (x 13 14)
                have b25148 := hb (x 13 14)
                have b25149 := hb (x 13 1 && x 13 14)
                clear * - r25147 b25148 b25149 d25142
                omega
              have d25150 : (x 13 2).toNat = 0 := by
                have r25151 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
                have b25152 := hb (x 13 2)
                have b25153 := hb (x 13 14)
                clear * - r25151 b25152 b25153 d25142
                omega
              have d25154 : (x 12 2).toNat = 0 := by
                have r25155 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25156 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                have e25157 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                have b25158 := hb (x 11 3)
                have b25159 := hb (x 12 2)
                have b25160 := hb (x 13 13)
                have b25161 := hb (x 14 12)
                clear * - r25155 e25156 e25157 b25158 b25159 b25160 b25161 d25101 d25117 d25097
                omega
              have d25162 : (x 14 13).toNat = 1 := by
                have r25163 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25164 := hb (x 12 2)
                have b25165 := hb (x 14 13)
                have b25166 := hb (x 13 1 && x 13 14)
                clear * - r25163 b25164 b25165 b25166 d25146 d25154
                omega
              have d25167 : (x 15 12).toNat = 0 := by
                have r25168 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25169 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e25170 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b25171 := hb (x 12 3)
                have b25172 := hb (x 13 2)
                have b25173 := hb (x 14 13)
                have b25174 := hb (x 15 12)
                clear * - r25168 e25169 e25170 b25171 b25172 b25173 b25174 d25162 d25150
                omega
              have d25175 : (x 12 3).toNat = 0 := by
                have r25176 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25177 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e25178 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b25179 := hb (x 12 3)
                have b25180 := hb (x 13 2)
                have b25181 := hb (x 14 13)
                have b25182 := hb (x 15 12)
                clear * - r25176 e25177 e25178 b25179 b25180 b25181 b25182 d25167 d25162 d25150
                omega
              have d25183 : (x 12 3 && x 12 14).toNat = 0 := by
                have r25184 := hand1 (x 12 3) (x 12 14)
                have b25185 := hb (x 12 3)
                have b25186 := hb (x 12 3 && x 12 14)
                clear * - r25184 b25185 b25186 d25175
                omega
              have d25187 : (x 15 11).toNat = 1 := by
                have r25188 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25189 := hb (x 11 4)
                have b25190 := hb (x 15 11)
                have b25191 := hb (x 14 1 && x 14 12)
                have b25192 := hb (x 13 2 && x 13 13)
                have b25193 := hb (x 12 3 && x 12 14)
                clear * - r25188 b25189 b25190 b25191 b25192 b25193 d25109 d25125 d25183 d25074
                omega
              have d25194 : (x 15 3).toNat = 1 := by
                have r25195 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
                have b25196 := hb (x 15 3)
                have b25197 := hb (x 15 11)
                clear * - r25195 b25196 b25197 d25187
                omega
              have d25198 : (x 18 12).toNat = 0 := by
                have r25199 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25200 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e25201 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b25202 := hb (x 15 3)
                have b25203 := hb (x 16 2)
                have b25204 := hb (x 17 13)
                have b25205 := hb (x 18 12)
                clear * - r25199 e25200 e25201 b25202 b25203 b25204 b25205 d25194
                omega
              have d25206 : (x 17 13).toNat = 0 := by
                have r25207 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25208 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e25209 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b25210 := hb (x 15 3)
                have b25211 := hb (x 16 2)
                have b25212 := hb (x 17 13)
                have b25213 := hb (x 18 12)
                clear * - r25207 e25208 e25209 b25210 b25211 b25212 b25213 d25198 d25194
                omega
              have d25214 : (x 16 1 && x 16 14).toNat = 1 := by
                have r25215 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25216 := hb (x 15 2)
                have b25217 := hb (x 17 13)
                have b25218 := hb (x 16 1 && x 16 14)
                clear * - r25215 b25216 b25217 b25218 d25206 d25058
                omega
              have d25219 : (x 16 14).toNat = 1 := by
                have r25220 := hand2 (x 16 1) (x 16 14)
                have b25221 := hb (x 16 14)
                have b25222 := hb (x 16 1 && x 16 14)
                clear * - r25220 b25221 b25222 d25214
                omega
              have d25223 : (x 15 1).toNat = 0 := by
                have r25224 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25225 := hb (x 15 1)
                have b25226 := hb (x 16 14)
                clear * - r25224 b25225 b25226 d25219
                omega
              have d25227 : (x 15 1 && x 15 11).toNat = 0 := by
                have r25228 := hand1 (x 15 1) (x 15 11)
                have b25229 := hb (x 15 1)
                have b25230 := hb (x 15 1 && x 15 11)
                clear * - r25228 b25229 b25230 d25223
                omega
              have d25231 : (x 16 2).toNat = 0 := by
                have r25232 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25233 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                have e25234 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                have b25235 := hb (x 15 3)
                have b25236 := hb (x 16 2)
                have b25237 := hb (x 17 13)
                have b25238 := hb (x 18 12)
                clear * - r25232 e25233 e25234 b25235 b25236 b25237 b25238 d25198 d25206 d25194
                omega
              have d25239 : (x 16 10).toNat = 0 := by
                have r25240 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
                have b25241 := hb (x 16 2)
                have b25242 := hb (x 16 10)
                clear * - r25240 b25241 b25242 d25231
                omega
              have r25243 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b25244 := hb (x 11 5)
              have b25245 := hb (x 16 10)
              have b25246 := hb (x 15 1 && x 15 11)
              have b25247 := hb (x 14 2 && x 14 12)
              have b25248 := hb (x 13 3 && x 13 13)
              have b25249 := hb (x 12 4 && x 12 14)
              linarith only [r25243, b25244, b25245, b25246, b25247, b25248, b25249, d25239, d25227, d25113, d25129, d25011, d25023]
            · have f25250 : (x (-1) 4).toNat = 1 := by rw [h24683]; rfl
              have d25251 : (x (-1) 12).toNat = 1 := by
                have r25252 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                have b25253 := hb (x (-1) 4)
                have b25254 := hb (x (-1) 12)
                clear * - r25252 b25253 b25254 f25250
                omega
              have d25255 : (x (-3) 2).toNat = 0 := by
                have r25256 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25257 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e25258 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b25259 := hb (x (-4) 3)
                have b25260 := hb (x (-3) 2)
                have b25261 := hb (x (-2) 13)
                have b25262 := hb (x (-1) 12)
                clear * - r25256 e25257 e25258 b25259 b25260 b25261 b25262 d25251 g10
                omega
              have d25263 : (x (-3) 10).toNat = 0 := by
                have r25264 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
                have b25265 := hb (x (-3) 2)
                have b25266 := hb (x (-3) 10)
                clear * - r25264 b25265 b25266 d25255
                omega
              have d25267 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
                have r25268 := hand2 (x (-3) 3) (x (-3) 10)
                have b25269 := hb (x (-3) 10)
                have b25270 := hb (x (-3) 3 && x (-3) 10)
                clear * - r25268 b25269 b25270 d25263
                omega
              have d25271 : (x (-1) 13).toNat = 1 := by
                have r25272 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25273 := hb (x (-3) 2)
                have b25274 := hb (x (-1) 13)
                have b25275 := hb (x (-2) 1 && x (-2) 14)
                clear * - r25272 b25273 b25274 b25275 g107 d25255
                omega
              have d25276 : (x (-2) 2).toNat = 0 := by
                have r25277 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25278 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                have e25279 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                have b25280 := hb (x (-3) 3)
                have b25281 := hb (x (-2) 2)
                have b25282 := hb (x (-1) 13)
                have b25283 := hb (x 0 12)
                clear * - r25277 e25278 e25279 b25280 b25281 b25282 b25283 f22835 d25271
                omega
              have d25284 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
                have r25285 := hand1 (x (-2) 2) (x (-2) 8)
                have b25286 := hb (x (-2) 2)
                have b25287 := hb (x (-2) 2 && x (-2) 8)
                clear * - r25285 b25286 b25287 d25276
                omega
              have d25288 : (x (-2) 2 && x (-2) 6).toNat = 0 := by
                have r25289 := hand1 (x (-2) 2) (x (-2) 6)
                have b25290 := hb (x (-2) 2)
                have b25291 := hb (x (-2) 2 && x (-2) 6)
                clear * - r25289 b25290 b25291 d25276
                omega
              have d25292 : (x (-3) 3).toNat = 0 := by
                have r25293 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25294 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                have e25295 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                have b25296 := hb (x (-3) 3)
                have b25297 := hb (x (-2) 2)
                have b25298 := hb (x (-1) 13)
                have b25299 := hb (x 0 12)
                clear * - r25293 e25294 e25295 b25296 b25297 b25298 b25299 f22835 d25271 d25276
                omega
              have d25300 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
                have r25301 := hand1 (x (-3) 3) (x (-3) 12)
                have b25302 := hb (x (-3) 3)
                have b25303 := hb (x (-3) 3 && x (-3) 12)
                clear * - r25301 b25302 b25303 d25292
                omega
              have d25304 : (x (-3) 3 && x (-3) 9).toNat = 0 := by
                have r25305 := hand1 (x (-3) 3) (x (-3) 9)
                have b25306 := hb (x (-3) 3)
                have b25307 := hb (x (-3) 3 && x (-3) 9)
                clear * - r25305 b25306 b25307 d25292
                omega
              have d25308 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
                have r25309 := hand1 (x (-3) 3) (x (-3) 7)
                have b25310 := hb (x (-3) 3)
                have b25311 := hb (x (-3) 3 && x (-3) 7)
                clear * - r25309 b25310 b25311 d25292
                omega
              have d25312 : (x (-4) 3).toNat = 0 := by
                have r25313 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25314 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e25315 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b25316 := hb (x (-4) 3)
                have b25317 := hb (x (-3) 2)
                have b25318 := hb (x (-2) 13)
                have b25319 := hb (x (-1) 12)
                clear * - r25313 e25314 e25315 b25316 b25317 b25318 b25319 d25251 g10 d25255
                omega
              have d25320 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                have r25321 := hand1 (x (-4) 3) (x (-4) 12)
                have b25322 := hb (x (-4) 3)
                have b25323 := hb (x (-4) 3 && x (-4) 12)
                clear * - r25321 b25322 b25323 d25312
                omega
              have d25324 : (x (-4) 11).toNat = 0 := by
                have r25325 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                have b25326 := hb (x (-4) 3)
                have b25327 := hb (x (-4) 11)
                clear * - r25325 b25326 b25327 d25312
                omega
              have d25328 : (x (-1) 1 && x (-1) 10).toNat = 1 := by
                have r25329 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b25330 := hb (x (-6) 6)
                have b25331 := hb (x 0 9)
                have b25332 := hb (x (-1) 1 && x (-1) 10)
                have b25333 := hb (x (-2) 2 && x (-2) 11)
                have b25334 := hb (x (-3) 3 && x (-3) 12)
                have b25335 := hb (x (-4) 4 && x (-4) 13)
                have b25336 := hb (x (-5) 5 && x (-5) 14)
                clear * - r25329 b25330 b25331 b25332 b25333 b25334 b25335 b25336 g20 g78 d25300 g79 g80 g1
                omega
              have d25337 : (x (-1) 10).toNat = 1 := by
                have r25338 := hand2 (x (-1) 1) (x (-1) 10)
                have b25339 := hb (x (-1) 10)
                have b25340 := hb (x (-1) 1 && x (-1) 10)
                clear * - r25338 b25339 b25340 d25328
                omega
              have d25341 : (x 3 8).toNat = 0 := by
                have r25342 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25343 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e25344 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e25345 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e25346 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e25347 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e25348 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b25349 := hb (x (-4) 7)
                have b25350 := hb (x (-3) 6)
                have b25351 := hb (x (-2) 5)
                have b25352 := hb (x (-1) 4)
                have b25353 := hb (x 0 11)
                have b25354 := hb (x 1 10)
                have b25355 := hb (x 2 9)
                have b25356 := hb (x 3 8)
                clear * - r25342 e25343 e25344 e25345 e25346 e25347 e25348 b25349 b25350 b25351 b25352 b25353 b25354 b25355 b25356 g28 g22 f25250 g6
                omega
              have d25357 : (x 2 9).toNat = 0 := by
                have r25358 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25359 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e25360 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e25361 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e25362 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e25363 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e25364 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b25365 := hb (x (-4) 7)
                have b25366 := hb (x (-3) 6)
                have b25367 := hb (x (-2) 5)
                have b25368 := hb (x (-1) 4)
                have b25369 := hb (x 0 11)
                have b25370 := hb (x 1 10)
                have b25371 := hb (x 2 9)
                have b25372 := hb (x 3 8)
                clear * - r25358 e25359 e25360 e25361 e25362 e25363 e25364 b25365 b25366 b25367 b25368 b25369 b25370 b25371 b25372 d25341 g28 g22 f25250 g6
                omega
              have d25373 : (x 2 5 && x 2 9).toNat = 0 := by
                have r25374 := hand2 (x 2 5) (x 2 9)
                have b25375 := hb (x 2 9)
                have b25376 := hb (x 2 5 && x 2 9)
                clear * - r25374 b25375 b25376 d25357
                omega
              have d25377 : (x (-3) 6).toNat = 0 := by
                have r25378 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25379 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e25380 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e25381 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e25382 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e25383 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e25384 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b25385 := hb (x (-4) 7)
                have b25386 := hb (x (-3) 6)
                have b25387 := hb (x (-2) 5)
                have b25388 := hb (x (-1) 4)
                have b25389 := hb (x 0 11)
                have b25390 := hb (x 1 10)
                have b25391 := hb (x 2 9)
                have b25392 := hb (x 3 8)
                clear * - r25378 e25379 e25380 e25381 e25382 e25383 e25384 b25385 b25386 b25387 b25388 b25389 b25390 b25391 b25392 d25341 d25357 g28 g22 f25250 g6
                omega
              have d25393 : (x (-4) 7).toNat = 0 := by
                have r25394 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25395 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                have e25396 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                have e25397 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                have e25398 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                have e25399 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                have e25400 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                have b25401 := hb (x (-4) 7)
                have b25402 := hb (x (-3) 6)
                have b25403 := hb (x (-2) 5)
                have b25404 := hb (x (-1) 4)
                have b25405 := hb (x 0 11)
                have b25406 := hb (x 1 10)
                have b25407 := hb (x 2 9)
                have b25408 := hb (x 3 8)
                clear * - r25394 e25395 e25396 e25397 e25398 e25399 e25400 b25401 b25402 b25403 b25404 b25405 b25406 b25407 b25408 d25341 d25357 g28 g22 f25250 g6 d25377
                omega
              have d25409 : (x (-4) 7 && x (-4) 12).toNat = 0 := by
                have r25410 := hand1 (x (-4) 7) (x (-4) 12)
                have b25411 := hb (x (-4) 7)
                have b25412 := hb (x (-4) 7 && x (-4) 12)
                clear * - r25410 b25411 b25412 d25393
                omega
              have d25413 : (x 1 8).toNat = 0 := by
                have r25414 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25415 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e25416 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e25417 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e25418 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e25419 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e25420 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have b25421 := hb (x (-6) 7)
                have b25422 := hb (x (-5) 6)
                have b25423 := hb (x (-4) 5)
                have b25424 := hb (x (-3) 4)
                have b25425 := hb (x (-2) 11)
                have b25426 := hb (x (-1) 10)
                have b25427 := hb (x 0 9)
                have b25428 := hb (x 1 8)
                clear * - r25414 e25415 e25416 e25417 e25418 e25419 e25420 b25421 b25422 b25423 b25424 b25425 b25426 b25427 b25428 g20 d25337 g9
                omega
              have d25429 : (x (-3) 4).toNat = 0 := by
                have r25430 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25431 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e25432 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e25433 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e25434 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e25435 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e25436 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have b25437 := hb (x (-6) 7)
                have b25438 := hb (x (-5) 6)
                have b25439 := hb (x (-4) 5)
                have b25440 := hb (x (-3) 4)
                have b25441 := hb (x (-2) 11)
                have b25442 := hb (x (-1) 10)
                have b25443 := hb (x 0 9)
                have b25444 := hb (x 1 8)
                clear * - r25430 e25431 e25432 e25433 e25434 e25435 e25436 b25437 b25438 b25439 b25440 b25441 b25442 b25443 b25444 d25413 g20 d25337 g9
                omega
              have d25445 : (x (-4) 5).toNat = 0 := by
                have r25446 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25447 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e25448 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e25449 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e25450 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e25451 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e25452 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have b25453 := hb (x (-6) 7)
                have b25454 := hb (x (-5) 6)
                have b25455 := hb (x (-4) 5)
                have b25456 := hb (x (-3) 4)
                have b25457 := hb (x (-2) 11)
                have b25458 := hb (x (-1) 10)
                have b25459 := hb (x 0 9)
                have b25460 := hb (x 1 8)
                clear * - r25446 e25447 e25448 e25449 e25450 e25451 e25452 b25453 b25454 b25455 b25456 b25457 b25458 b25459 b25460 d25413 g20 d25337 g9 d25429
                omega
              have d25461 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
                have r25462 := hand1 (x (-4) 5) (x (-4) 12)
                have b25463 := hb (x (-4) 5)
                have b25464 := hb (x (-4) 5 && x (-4) 12)
                clear * - r25462 b25463 b25464 d25445
                omega
              have d25465 : (x (-5) 6).toNat = 0 := by
                have r25466 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25467 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e25468 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e25469 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e25470 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e25471 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e25472 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have b25473 := hb (x (-6) 7)
                have b25474 := hb (x (-5) 6)
                have b25475 := hb (x (-4) 5)
                have b25476 := hb (x (-3) 4)
                have b25477 := hb (x (-2) 11)
                have b25478 := hb (x (-1) 10)
                have b25479 := hb (x 0 9)
                have b25480 := hb (x 1 8)
                clear * - r25466 e25467 e25468 e25469 e25470 e25471 e25472 b25473 b25474 b25475 b25476 b25477 b25478 b25479 b25480 d25413 g20 d25337 g9 d25429 d25445
                omega
              have d25481 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
                have r25482 := hand1 (x (-5) 6) (x (-5) 13)
                have b25483 := hb (x (-5) 6)
                have b25484 := hb (x (-5) 6 && x (-5) 13)
                clear * - r25482 b25483 b25484 d25465
                omega
              have d25485 : (x (-6) 7).toNat = 0 := by
                have r25486 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25487 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                have e25488 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                have e25489 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                have e25490 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                have e25491 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                have e25492 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                have b25493 := hb (x (-6) 7)
                have b25494 := hb (x (-5) 6)
                have b25495 := hb (x (-4) 5)
                have b25496 := hb (x (-3) 4)
                have b25497 := hb (x (-2) 11)
                have b25498 := hb (x (-1) 10)
                have b25499 := hb (x 0 9)
                have b25500 := hb (x 1 8)
                clear * - r25486 e25487 e25488 e25489 e25490 e25491 e25492 b25493 b25494 b25495 b25496 b25497 b25498 b25499 b25500 d25413 g20 d25337 g9 d25429 d25445 d25465
                omega
              have d25501 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
                have r25502 := hand1 (x (-6) 7) (x (-6) 14)
                have b25503 := hb (x (-6) 7)
                have b25504 := hb (x (-6) 7 && x (-6) 14)
                clear * - r25502 b25503 b25504 d25485
                omega
              cases h25505 : x (-1) 5
              · have f25506 : (x (-1) 5).toNat = 0 := by rw [h25505]; rfl
                have r25507 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25508 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25509 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                have e25510 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                have e25511 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                have e25512 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                have e25513 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                have e25514 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                have r25515 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25516 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                have e25517 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                have e25518 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                have e25519 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                have e25520 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                have e25521 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                have r25522 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25523 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e25524 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e25525 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e25526 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e25527 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e25528 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have r25529 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25530 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e25531 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e25532 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e25533 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e25534 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e25535 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have r25536 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25537 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                have e25538 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                have e25539 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                have e25540 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                have e25541 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                have e25542 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                have r25543 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25544 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                have e25545 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                have r25546 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25547 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e25548 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have r25549 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25550 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25551 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25552 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
                have e25553 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
                have r25554 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25555 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
                have e25556 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
                have r25557 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25558 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25559 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25560 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25561 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25562 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25563 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25564 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25565 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25566 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
                have r25567 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
                have r25568 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                have r25569 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                have r25570 := hand2 (x (-8) 8) (x (-8) 12)
                have r25571 := hand2 (x (-9) 9) (x (-9) 13)
                have r25572 := hand2 (x 5 2) (x 5 6)
                have r25573 := hand2 (x 4 3) (x 4 7)
                have r25574 := hand1 (x (-1) 8) (x (-1) 12)
                have r25575 := hand2 (x (-1) 1) (x (-1) 7)
                have r25576 := hand2 (x (-8) 8) (x (-8) 14)
                have r25577 := hand2 (x (-1) 1) (x (-1) 8)
                have r25578 := hand2 (x (-9) 1) (x (-9) 10)
                have r25579 := hand2 (x (-10) 2) (x (-10) 11)
                have r25580 := hand1 (x (-11) 3) (x (-11) 12)
                have r25581 := hand1 (x (-12) 4) (x (-12) 13)
                have r25582 := hand1 (x (-13) 5) (x (-13) 14)
                have r25583 := hand1 (x (-5) 4) (x (-5) 13)
                have r25584 := hand1 (x (-6) 5) (x (-6) 14)
                have r25585 := hand2 (x 3 1) (x 3 11)
                have r25586 := hand1 (x 7 1) (x 7 12)
                have r25587 := hand1 (x 6 2) (x 6 13)
                have r25588 := hand1 (x 5 3) (x 5 14)
                have r25589 := hand1 (x (-9) 1) (x (-9) 14)
                have r25590 := hand2 (x (-6) 1) (x (-6) 14)
                linarith only [r25507, r25508, e25509, e25510, e25511, e25512, e25513, e25514, r25515, e25516, e25517, e25518, e25519, e25520, e25521, r25522, e25523, e25524, e25525, e25526, e25527, e25528, r25529, e25530, e25531, e25532, e25533, e25534, e25535, r25536, e25537, e25538, e25539, e25540, e25541, e25542, r25543, e25544, e25545, r25546, e25547, e25548, r25549, r25550, r25551, e25552, e25553, r25554, e25555, e25556, r25557, r25558, r25559, r25560, r25561, r25562, r25563, r25564, r25565, r25566, r25567, r25568, r25569, r25570, r25571, r25572, r25573, r25574, r25575, r25576, r25577, r25578, r25579, r25580, r25581, r25582, r25583, r25584, r25585, r25586, r25587, r25588, r25589, r25590, d25324, d25263, g4, g7, g8, f25506, g12, g16, g18, f22829, g19, g26, d24661, d25288, d25308, g39, g40, g41, g42, g47, d25373, g48, g49, g50, d25284, d25304, g61, g62, g63, g64, g65, d25267, g66, g67, g68, g69, g70, g71, g72, g73, d25461, d25481, d25501, g76, g77, d25320, d24657, g92, g93]
              · have f25718 : (x (-1) 5).toNat = 1 := by rw [h25505]; rfl
                have d25719 : (x 4 8).toNat = 0 := by
                  have r25720 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e25721 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e25722 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e25723 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e25724 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e25725 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e25726 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b25727 := hb (x (-3) 7)
                  have b25728 := hb (x (-2) 6)
                  have b25729 := hb (x (-1) 5)
                  have b25730 := hb (x 0 4)
                  have b25731 := hb (x 1 11)
                  have b25732 := hb (x 2 10)
                  have b25733 := hb (x 3 9)
                  have b25734 := hb (x 4 8)
                  clear * - r25720 e25721 e25722 e25723 e25724 e25725 e25726 b25727 b25728 b25729 b25730 b25731 b25732 b25733 b25734 d24675 g16 f25718
                  omega
                have d25735 : (x 4 8 && x 4 11).toNat = 0 := by
                  have r25736 := hand1 (x 4 8) (x 4 11)
                  have b25737 := hb (x 4 8)
                  have b25738 := hb (x 4 8 && x 4 11)
                  clear * - r25736 b25737 b25738 d25719
                  omega
                have d25739 : (x 3 9).toNat = 0 := by
                  have r25740 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e25741 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e25742 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e25743 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e25744 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e25745 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e25746 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b25747 := hb (x (-3) 7)
                  have b25748 := hb (x (-2) 6)
                  have b25749 := hb (x (-1) 5)
                  have b25750 := hb (x 0 4)
                  have b25751 := hb (x 1 11)
                  have b25752 := hb (x 2 10)
                  have b25753 := hb (x 3 9)
                  have b25754 := hb (x 4 8)
                  clear * - r25740 e25741 e25742 e25743 e25744 e25745 e25746 b25747 b25748 b25749 b25750 b25751 b25752 b25753 b25754 d25719 d24675 g16 f25718
                  omega
                have d25755 : (x 2 10).toNat = 0 := by
                  have r25756 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e25757 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e25758 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e25759 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e25760 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e25761 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e25762 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b25763 := hb (x (-3) 7)
                  have b25764 := hb (x (-2) 6)
                  have b25765 := hb (x (-1) 5)
                  have b25766 := hb (x 0 4)
                  have b25767 := hb (x 1 11)
                  have b25768 := hb (x 2 10)
                  have b25769 := hb (x 3 9)
                  have b25770 := hb (x 4 8)
                  clear * - r25756 e25757 e25758 e25759 e25760 e25761 e25762 b25763 b25764 b25765 b25766 b25767 b25768 b25769 b25770 d25719 d25739 d24675 g16 f25718
                  omega
                have d25771 : (x 2 10 && x 2 13).toNat = 0 := by
                  have r25772 := hand1 (x 2 10) (x 2 13)
                  have b25773 := hb (x 2 10)
                  have b25774 := hb (x 2 10 && x 2 13)
                  clear * - r25772 b25773 b25774 d25755
                  omega
                have r25775 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25776 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25777 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25778 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                have e25779 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                have e25780 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                have e25781 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                have e25782 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                have e25783 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                have r25784 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25785 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e25786 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e25787 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e25788 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e25789 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e25790 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have r25791 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25792 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e25793 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e25794 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e25795 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e25796 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e25797 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have r25798 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25799 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e25800 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have r25801 : 1 ≤ (x 12 3).toNat + (x 11 1 && x 11 4).toNat + (x 10 2 && x 10 5).toNat + (x 9 3 && x 9 6).toNat + (x 8 4 && x 8 7).toNat + (x 7 5 && x 7 8).toNat + (x 6 6 && x 6 9).toNat + (x 5 7 && x 5 10).toNat + (x 4 8 && x 4 11).toNat + (x 3 9 && x 3 12).toNat + (x 2 10 && x 2 13).toNat + (x 1 11 && x 1 14).toNat + (x 0 12).toNat := by have q := hcov3 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25802 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25803 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25804 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25805 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25806 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25807 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25808 := hand2 (x 11 1) (x 11 4)
                have r25809 := hand2 (x 10 2) (x 10 5)
                have r25810 := hand2 (x 9 3) (x 9 6)
                have r25811 := hand2 (x 8 4) (x 8 7)
                have r25812 := hand2 (x 7 5) (x 7 8)
                have r25813 := hand2 (x 6 6) (x 6 9)
                have r25814 := hand2 (x 5 7) (x 5 10)
                have r25815 := hand2 (x 2 1) (x 2 6)
                have r25816 := hand1 (x (-5) 8) (x (-5) 13)
                have r25817 := hand1 (x (-6) 9) (x (-6) 14)
                have r25818 := hand2 (x (-1) 1) (x (-1) 8)
                have r25819 := hand1 (x (-5) 4) (x (-5) 13)
                have r25820 := hand1 (x (-6) 5) (x (-6) 14)
                have r25821 := hand2 (x 5 1) (x 5 11)
                have r25822 := hand2 (x 4 2) (x 4 12)
                have r25823 := hand2 (x 3 3) (x 3 13)
                have r25824 := hand2 (x (-9) 1) (x (-9) 12)
                have r25825 := hand2 (x (-10) 2) (x (-10) 13)
                have r25826 := hand2 (x (-11) 3) (x (-11) 14)
                have r25827 := hand1 (x 2 2) (x 2 13)
                linarith only [r25775, r25776, r25777, e25778, e25779, e25780, e25781, e25782, e25783, r25784, e25785, e25786, e25787, e25788, e25789, e25790, r25791, e25792, e25793, e25794, e25795, e25796, e25797, r25798, e25799, e25800, r25801, r25802, r25803, r25804, r25805, r25806, r25807, r25808, r25809, r25810, r25811, r25812, r25813, r25814, r25815, r25816, r25817, r25818, r25819, r25820, r25821, r25822, r25823, r25824, r25825, r25826, r25827, d25393, d25324, d25377, d25263, g6, g7, f25250, g12, g15, g16, f22829, f22835, g24, f24670, g26, g30, g31, g32, g37, d25735, g38, d25771, d24679, g53, g54, g55, g56, g57, d25409, g65, d25267, g66, g67, g68, g69, g76, g77, d25320, d24665, g104, d24671]
          · have f25931 : (x 1 3).toNat = 1 := by rw [h24669]; rfl
            have d25932 : (x 4 12).toNat = 0 := by
              have r25933 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e25934 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e25935 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b25936 := hb (x 1 3)
              have b25937 := hb (x 2 2)
              have b25938 := hb (x 3 13)
              have b25939 := hb (x 4 12)
              clear * - r25933 e25934 e25935 b25936 b25937 b25938 b25939 f25931
              omega
            have d25940 : (x 4 1 && x 4 12).toNat = 0 := by
              have r25941 := hand2 (x 4 1) (x 4 12)
              have b25942 := hb (x 4 12)
              have b25943 := hb (x 4 1 && x 4 12)
              clear * - r25941 b25942 b25943 d25932
              omega
            have d25944 : (x 4 4).toNat = 0 := by
              have r25945 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b25946 := hb (x 4 4)
              have b25947 := hb (x 4 12)
              clear * - r25945 b25946 b25947 d25932
              omega
            have d25948 : (x 3 13).toNat = 0 := by
              have r25949 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e25950 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e25951 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b25952 := hb (x 1 3)
              have b25953 := hb (x 2 2)
              have b25954 := hb (x 3 13)
              have b25955 := hb (x 4 12)
              clear * - r25949 e25950 e25951 b25952 b25953 b25954 b25955 d25932 f25931
              omega
            have d25956 : (x 2 2).toNat = 0 := by
              have r25957 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e25958 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e25959 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b25960 := hb (x 1 3)
              have b25961 := hb (x 2 2)
              have b25962 := hb (x 3 13)
              have b25963 := hb (x 4 12)
              clear * - r25957 e25958 e25959 b25960 b25961 b25962 b25963 d25932 d25948 f25931
              omega
            have d25964 : (x 4 13).toNat = 1 := by
              have r25965 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b25966 := hb (x 2 2)
              have b25967 := hb (x 4 13)
              have b25968 := hb (x 3 1 && x 3 14)
              clear * - r25965 b25966 b25967 b25968 g108 d25956
              omega
            have d25969 : (x 4 1).toNat = 1 := by
              have r25970 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
              have b25971 := hb (x 4 1)
              have b25972 := hb (x 4 13)
              clear * - r25970 b25971 b25972 d25964
              omega
            have d25973 : (x 5 14).toNat = 0 := by
              have r25974 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b25975 := hb (x 4 1)
              have b25976 := hb (x 5 14)
              clear * - r25974 b25975 b25976 d25969
              omega
            have d25977 : (x 5 3 && x 5 14).toNat = 0 := by
              have r25978 := hand2 (x 5 3) (x 5 14)
              have b25979 := hb (x 5 14)
              have b25980 := hb (x 5 3 && x 5 14)
              clear * - r25978 b25979 b25980 d25973
              omega
            have d25981 : (x 5 2).toNat = 0 := by
              have r25982 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b25983 := hb (x 5 2)
              have b25984 := hb (x 5 14)
              clear * - r25982 b25983 b25984 d25973
              omega
            have d25985 : (x 5 12).toNat = 0 := by
              have r25986 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e25987 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e25988 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b25989 := hb (x 2 3)
              have b25990 := hb (x 3 2)
              have b25991 := hb (x 4 13)
              have b25992 := hb (x 5 12)
              clear * - r25986 e25987 e25988 b25989 b25990 b25991 b25992 d25964 g33
              omega
            have d25993 : (x 5 4).toNat = 0 := by
              have r25994 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b25995 := hb (x 5 4)
              have b25996 := hb (x 5 12)
              clear * - r25994 b25995 b25996 d25985
              omega
            have d25997 : (x 2 3).toNat = 0 := by
              have r25998 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e25999 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e26000 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b26001 := hb (x 2 3)
              have b26002 := hb (x 3 2)
              have b26003 := hb (x 4 13)
              have b26004 := hb (x 5 12)
              clear * - r25998 e25999 e26000 b26001 b26002 b26003 b26004 d25985 d25964 g33
              omega
            have d26005 : (x 2 3 && x 2 14).toNat = 0 := by
              have r26006 := hand1 (x 2 3) (x 2 14)
              have b26007 := hb (x 2 3)
              have b26008 := hb (x 2 3 && x 2 14)
              clear * - r26006 b26007 b26008 d25997
              omega
            have d26009 : (x 5 11).toNat = 1 := by
              have r26010 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26011 := hb (x 1 4)
              have b26012 := hb (x 5 11)
              have b26013 := hb (x 4 1 && x 4 12)
              have b26014 := hb (x 3 2 && x 3 13)
              have b26015 := hb (x 2 3 && x 2 14)
              clear * - r26010 b26011 b26012 b26013 b26014 b26015 d25940 g105 d26005 g25
              omega
            have d26016 : (x 5 3).toNat = 1 := by
              have r26017 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
              have b26018 := hb (x 5 3)
              have b26019 := hb (x 5 11)
              clear * - r26017 b26018 b26019 d26009
              omega
            have d26020 : (x 8 12).toNat = 0 := by
              have r26021 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26022 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e26023 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b26024 := hb (x 5 3)
              have b26025 := hb (x 6 2)
              have b26026 := hb (x 7 13)
              have b26027 := hb (x 8 12)
              clear * - r26021 e26022 e26023 b26024 b26025 b26026 b26027 d26016
              omega
            have d26028 : (x 8 1 && x 8 12).toNat = 0 := by
              have r26029 := hand2 (x 8 1) (x 8 12)
              have b26030 := hb (x 8 12)
              have b26031 := hb (x 8 1 && x 8 12)
              clear * - r26029 b26030 b26031 d26020
              omega
            have d26032 : (x 8 4).toNat = 0 := by
              have r26033 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
              have b26034 := hb (x 8 4)
              have b26035 := hb (x 8 12)
              clear * - r26033 b26034 b26035 d26020
              omega
            have d26036 : (x 7 13).toNat = 0 := by
              have r26037 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26038 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e26039 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b26040 := hb (x 5 3)
              have b26041 := hb (x 6 2)
              have b26042 := hb (x 7 13)
              have b26043 := hb (x 8 12)
              clear * - r26037 e26038 e26039 b26040 b26041 b26042 b26043 d26020 d26016
              omega
            have d26044 : (x 7 2 && x 7 13).toNat = 0 := by
              have r26045 := hand2 (x 7 2) (x 7 13)
              have b26046 := hb (x 7 13)
              have b26047 := hb (x 7 2 && x 7 13)
              clear * - r26045 b26046 b26047 d26036
              omega
            have d26048 : (x 6 1 && x 6 14).toNat = 1 := by
              have r26049 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26050 := hb (x 5 2)
              have b26051 := hb (x 7 13)
              have b26052 := hb (x 6 1 && x 6 14)
              clear * - r26049 b26050 b26051 b26052 d26036 d25981
              omega
            have d26053 : (x 6 1).toNat = 1 := by
              have r26054 := hand1 (x 6 1) (x 6 14)
              have b26055 := hb (x 6 1)
              have b26056 := hb (x 6 1 && x 6 14)
              clear * - r26054 b26055 b26056 d26048
              omega
            have d26057 : (x 7 14).toNat = 0 := by
              have r26058 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26059 := hb (x 6 1)
              have b26060 := hb (x 7 14)
              clear * - r26058 b26059 b26060 d26053
              omega
            have d26061 : (x 7 1 && x 7 14).toNat = 0 := by
              have r26062 := hand2 (x 7 1) (x 7 14)
              have b26063 := hb (x 7 14)
              have b26064 := hb (x 7 1 && x 7 14)
              clear * - r26062 b26063 b26064 d26057
              omega
            have d26065 : (x 7 2).toNat = 0 := by
              have r26066 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b26067 := hb (x 7 2)
              have b26068 := hb (x 7 14)
              clear * - r26066 b26067 b26068 d26057
              omega
            have d26069 : (x 6 2).toNat = 0 := by
              have r26070 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26071 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
              have e26072 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
              have b26073 := hb (x 5 3)
              have b26074 := hb (x 6 2)
              have b26075 := hb (x 7 13)
              have b26076 := hb (x 8 12)
              clear * - r26070 e26071 e26072 b26073 b26074 b26075 b26076 d26020 d26036 d26016
              omega
            have d26077 : (x 6 2 && x 6 13).toNat = 0 := by
              have r26078 := hand1 (x 6 2) (x 6 13)
              have b26079 := hb (x 6 2)
              have b26080 := hb (x 6 2 && x 6 13)
              clear * - r26078 b26079 b26080 d26069
              omega
            have d26081 : (x 8 13).toNat = 1 := by
              have r26082 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26083 := hb (x 6 2)
              have b26084 := hb (x 8 13)
              have b26085 := hb (x 7 1 && x 7 14)
              clear * - r26082 b26083 b26084 b26085 d26061 d26069
              omega
            have d26086 : (x 8 1).toNat = 1 := by
              have r26087 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
              have b26088 := hb (x 8 1)
              have b26089 := hb (x 8 13)
              clear * - r26087 b26088 b26089 d26081
              omega
            have d26090 : (x 9 14).toNat = 0 := by
              have r26091 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26092 := hb (x 8 1)
              have b26093 := hb (x 9 14)
              clear * - r26091 b26092 b26093 d26086
              omega
            have d26094 : (x 9 3 && x 9 14).toNat = 0 := by
              have r26095 := hand2 (x 9 3) (x 9 14)
              have b26096 := hb (x 9 14)
              have b26097 := hb (x 9 3 && x 9 14)
              clear * - r26095 b26096 b26097 d26090
              omega
            have d26098 : (x 9 2).toNat = 0 := by
              have r26099 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
              have b26100 := hb (x 9 2)
              have b26101 := hb (x 9 14)
              clear * - r26099 b26100 b26101 d26090
              omega
            have d26102 : (x 9 12).toNat = 0 := by
              have r26103 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26104 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e26105 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b26106 := hb (x 6 3)
              have b26107 := hb (x 7 2)
              have b26108 := hb (x 8 13)
              have b26109 := hb (x 9 12)
              clear * - r26103 e26104 e26105 b26106 b26107 b26108 b26109 d26081 d26065
              omega
            have d26110 : (x 9 4).toNat = 0 := by
              have r26111 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
              have b26112 := hb (x 9 4)
              have b26113 := hb (x 9 12)
              clear * - r26111 b26112 b26113 d26102
              omega
            have d26114 : (x 6 3).toNat = 0 := by
              have r26115 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26116 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e26117 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b26118 := hb (x 6 3)
              have b26119 := hb (x 7 2)
              have b26120 := hb (x 8 13)
              have b26121 := hb (x 9 12)
              clear * - r26115 e26116 e26117 b26118 b26119 b26120 b26121 d26102 d26081 d26065
              omega
            have d26122 : (x 6 3 && x 6 14).toNat = 0 := by
              have r26123 := hand1 (x 6 3) (x 6 14)
              have b26124 := hb (x 6 3)
              have b26125 := hb (x 6 3 && x 6 14)
              clear * - r26123 b26124 b26125 d26114
              omega
            have d26126 : (x 9 11).toNat = 1 := by
              have r26127 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26128 := hb (x 5 4)
              have b26129 := hb (x 9 11)
              have b26130 := hb (x 8 1 && x 8 12)
              have b26131 := hb (x 7 2 && x 7 13)
              have b26132 := hb (x 6 3 && x 6 14)
              clear * - r26127 b26128 b26129 b26130 b26131 b26132 d26028 d26044 d26122 d25993
              omega
            have d26133 : (x 9 3).toNat = 1 := by
              have r26134 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
              have b26135 := hb (x 9 3)
              have b26136 := hb (x 9 11)
              clear * - r26134 b26135 b26136 d26126
              omega
            have d26137 : (x 12 12).toNat = 0 := by
              have r26138 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26139 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e26140 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b26141 := hb (x 9 3)
              have b26142 := hb (x 10 2)
              have b26143 := hb (x 11 13)
              have b26144 := hb (x 12 12)
              clear * - r26138 e26139 e26140 b26141 b26142 b26143 b26144 d26133
              omega
            have d26145 : (x 12 1 && x 12 12).toNat = 0 := by
              have r26146 := hand2 (x 12 1) (x 12 12)
              have b26147 := hb (x 12 12)
              have b26148 := hb (x 12 1 && x 12 12)
              clear * - r26146 b26147 b26148 d26137
              omega
            have d26149 : (x 12 4).toNat = 0 := by
              have r26150 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
              have b26151 := hb (x 12 4)
              have b26152 := hb (x 12 12)
              clear * - r26150 b26151 b26152 d26137
              omega
            have d26153 : (x 11 13).toNat = 0 := by
              have r26154 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26155 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e26156 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b26157 := hb (x 9 3)
              have b26158 := hb (x 10 2)
              have b26159 := hb (x 11 13)
              have b26160 := hb (x 12 12)
              clear * - r26154 e26155 e26156 b26157 b26158 b26159 b26160 d26137 d26133
              omega
            have d26161 : (x 11 2 && x 11 13).toNat = 0 := by
              have r26162 := hand2 (x 11 2) (x 11 13)
              have b26163 := hb (x 11 13)
              have b26164 := hb (x 11 2 && x 11 13)
              clear * - r26162 b26163 b26164 d26153
              omega
            have d26165 : (x 10 1 && x 10 14).toNat = 1 := by
              have r26166 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26167 := hb (x 9 2)
              have b26168 := hb (x 11 13)
              have b26169 := hb (x 10 1 && x 10 14)
              clear * - r26166 b26167 b26168 b26169 d26153 d26098
              omega
            have d26170 : (x 10 14).toNat = 1 := by
              have r26171 := hand2 (x 10 1) (x 10 14)
              have b26172 := hb (x 10 14)
              have b26173 := hb (x 10 1 && x 10 14)
              clear * - r26171 b26172 b26173 d26165
              omega
            have d26174 : (x 9 1).toNat = 0 := by
              have r26175 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26176 := hb (x 9 1)
              have b26177 := hb (x 10 14)
              clear * - r26175 b26176 b26177 d26170
              omega
            have d26178 : (x 9 13).toNat = 0 := by
              have r26179 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
              have b26180 := hb (x 9 1)
              have b26181 := hb (x 9 13)
              clear * - r26179 b26180 b26181 d26174
              omega
            have d26182 : (x 8 1 && x 8 14).toNat = 1 := by
              have r26183 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26184 := hb (x 7 2)
              have b26185 := hb (x 9 13)
              have b26186 := hb (x 8 1 && x 8 14)
              clear * - r26183 b26184 b26185 b26186 d26178 d26065
              omega
            have d26187 : (x 8 14).toNat = 1 := by
              have r26188 := hand2 (x 8 1) (x 8 14)
              have b26189 := hb (x 8 14)
              have b26190 := hb (x 8 1 && x 8 14)
              clear * - r26188 b26189 b26190 d26182
              omega
            have d26191 : (x 7 1).toNat = 0 := by
              have r26192 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26193 := hb (x 7 1)
              have b26194 := hb (x 8 14)
              clear * - r26192 b26193 b26194 d26187
              omega
            have d26195 : (x 7 1 && x 7 12).toNat = 0 := by
              have r26196 := hand1 (x 7 1) (x 7 12)
              have b26197 := hb (x 7 1)
              have b26198 := hb (x 7 1 && x 7 12)
              clear * - r26196 b26197 b26198 d26191
              omega
            have d26199 : (x 8 11).toNat = 1 := by
              have r26200 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26201 := hb (x 4 4)
              have b26202 := hb (x 8 11)
              have b26203 := hb (x 7 1 && x 7 12)
              have b26204 := hb (x 6 2 && x 6 13)
              have b26205 := hb (x 5 3 && x 5 14)
              clear * - r26200 b26201 b26202 b26203 b26204 b26205 d26195 d26077 d25977 d25944
              omega
            have d26206 : (x 8 3).toNat = 1 := by
              have r26207 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
              have b26208 := hb (x 8 3)
              have b26209 := hb (x 8 11)
              clear * - r26207 b26208 b26209 d26199
              omega
            have d26210 : (x 11 12).toNat = 0 := by
              have r26211 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26212 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e26213 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b26214 := hb (x 8 3)
              have b26215 := hb (x 9 2)
              have b26216 := hb (x 10 13)
              have b26217 := hb (x 11 12)
              clear * - r26211 e26212 e26213 b26214 b26215 b26216 b26217 d26098 d26206
              omega
            have d26218 : (x 11 1 && x 11 12).toNat = 0 := by
              have r26219 := hand2 (x 11 1) (x 11 12)
              have b26220 := hb (x 11 12)
              have b26221 := hb (x 11 1 && x 11 12)
              clear * - r26219 b26220 b26221 d26210
              omega
            have d26222 : (x 10 13).toNat = 0 := by
              have r26223 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26224 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
              have e26225 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
              have b26226 := hb (x 8 3)
              have b26227 := hb (x 9 2)
              have b26228 := hb (x 10 13)
              have b26229 := hb (x 11 12)
              clear * - r26223 e26224 e26225 b26226 b26227 b26228 b26229 d26210 d26098 d26206
              omega
            have d26230 : (x 10 2 && x 10 13).toNat = 0 := by
              have r26231 := hand2 (x 10 2) (x 10 13)
              have b26232 := hb (x 10 13)
              have b26233 := hb (x 10 2 && x 10 13)
              clear * - r26231 b26232 b26233 d26222
              omega
            have d26234 : (x 12 11).toNat = 1 := by
              have r26235 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26236 := hb (x 8 4)
              have b26237 := hb (x 12 11)
              have b26238 := hb (x 11 1 && x 11 12)
              have b26239 := hb (x 10 2 && x 10 13)
              have b26240 := hb (x 9 3 && x 9 14)
              clear * - r26235 b26236 b26237 b26238 b26239 b26240 d26218 d26230 d26094 d26032
              omega
            have d26241 : (x 12 3).toNat = 1 := by
              have r26242 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
              have b26243 := hb (x 12 3)
              have b26244 := hb (x 12 11)
              clear * - r26242 b26243 b26244 d26234
              omega
            have d26245 : (x 15 12).toNat = 0 := by
              have r26246 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26247 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e26248 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b26249 := hb (x 12 3)
              have b26250 := hb (x 13 2)
              have b26251 := hb (x 14 13)
              have b26252 := hb (x 15 12)
              clear * - r26246 e26247 e26248 b26249 b26250 b26251 b26252 d26241
              omega
            have d26253 : (x 15 1 && x 15 12).toNat = 0 := by
              have r26254 := hand2 (x 15 1) (x 15 12)
              have b26255 := hb (x 15 12)
              have b26256 := hb (x 15 1 && x 15 12)
              clear * - r26254 b26255 b26256 d26245
              omega
            have d26257 : (x 14 13).toNat = 0 := by
              have r26258 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26259 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e26260 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b26261 := hb (x 12 3)
              have b26262 := hb (x 13 2)
              have b26263 := hb (x 14 13)
              have b26264 := hb (x 15 12)
              clear * - r26258 e26259 e26260 b26261 b26262 b26263 b26264 d26245 d26241
              omega
            have d26265 : (x 14 2 && x 14 13).toNat = 0 := by
              have r26266 := hand2 (x 14 2) (x 14 13)
              have b26267 := hb (x 14 13)
              have b26268 := hb (x 14 2 && x 14 13)
              clear * - r26266 b26267 b26268 d26257
              omega
            have d26269 : (x 13 2).toNat = 0 := by
              have r26270 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26271 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e26272 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b26273 := hb (x 12 3)
              have b26274 := hb (x 13 2)
              have b26275 := hb (x 14 13)
              have b26276 := hb (x 15 12)
              clear * - r26270 e26271 e26272 b26273 b26274 b26275 b26276 d26245 d26257 d26241
              omega
            have d26277 : (x 10 1).toNat = 1 := by
              have r26278 := hand1 (x 10 1) (x 10 14)
              have b26279 := hb (x 10 1)
              have b26280 := hb (x 10 1 && x 10 14)
              clear * - r26278 b26279 b26280 d26165
              omega
            have d26281 : (x 11 14).toNat = 0 := by
              have r26282 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26283 := hb (x 10 1)
              have b26284 := hb (x 11 14)
              clear * - r26282 b26283 b26284 d26277
              omega
            have d26285 : (x 11 1 && x 11 14).toNat = 0 := by
              have r26286 := hand2 (x 11 1) (x 11 14)
              have b26287 := hb (x 11 14)
              have b26288 := hb (x 11 1 && x 11 14)
              clear * - r26286 b26287 b26288 d26281
              omega
            have d26289 : (x 11 2).toNat = 0 := by
              have r26290 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
              have b26291 := hb (x 11 2)
              have b26292 := hb (x 11 14)
              clear * - r26290 b26291 b26292 d26281
              omega
            have d26293 : (x 10 2).toNat = 0 := by
              have r26294 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26295 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e26296 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b26297 := hb (x 9 3)
              have b26298 := hb (x 10 2)
              have b26299 := hb (x 11 13)
              have b26300 := hb (x 12 12)
              clear * - r26294 e26295 e26296 b26297 b26298 b26299 b26300 d26137 d26153 d26133
              omega
            have d26301 : (x 12 13).toNat = 1 := by
              have r26302 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26303 := hb (x 10 2)
              have b26304 := hb (x 12 13)
              have b26305 := hb (x 11 1 && x 11 14)
              clear * - r26302 b26303 b26304 b26305 d26285 d26293
              omega
            have d26306 : (x 12 1).toNat = 1 := by
              have r26307 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
              have b26308 := hb (x 12 1)
              have b26309 := hb (x 12 13)
              clear * - r26307 b26308 b26309 d26301
              omega
            have d26310 : (x 13 14).toNat = 0 := by
              have r26311 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26312 := hb (x 12 1)
              have b26313 := hb (x 13 14)
              clear * - r26311 b26312 b26313 d26306
              omega
            have d26314 : (x 13 1 && x 13 14).toNat = 0 := by
              have r26315 := hand2 (x 13 1) (x 13 14)
              have b26316 := hb (x 13 14)
              have b26317 := hb (x 13 1 && x 13 14)
              clear * - r26315 b26316 b26317 d26310
              omega
            have d26318 : (x 12 2).toNat = 1 := by
              have r26319 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26320 := hb (x 12 2)
              have b26321 := hb (x 14 13)
              have b26322 := hb (x 13 1 && x 13 14)
              clear * - r26319 b26320 b26321 b26322 d26257 d26314
              omega
            have d26323 : (x 14 12).toNat = 0 := by
              have r26324 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26325 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e26326 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b26327 := hb (x 11 3)
              have b26328 := hb (x 12 2)
              have b26329 := hb (x 13 13)
              have b26330 := hb (x 14 12)
              clear * - r26324 e26325 e26326 b26327 b26328 b26329 b26330 d26318
              omega
            have d26331 : (x 14 4).toNat = 0 := by
              have r26332 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
              have b26333 := hb (x 14 4)
              have b26334 := hb (x 14 12)
              clear * - r26332 b26333 b26334 d26323
              omega
            have d26335 : (x 14 4 && x 14 14).toNat = 0 := by
              have r26336 := hand1 (x 14 4) (x 14 14)
              have b26337 := hb (x 14 4)
              have b26338 := hb (x 14 4 && x 14 14)
              clear * - r26336 b26337 b26338 d26331
              omega
            have d26339 : (x 13 13).toNat = 0 := by
              have r26340 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26341 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
              have e26342 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
              have b26343 := hb (x 11 3)
              have b26344 := hb (x 12 2)
              have b26345 := hb (x 13 13)
              have b26346 := hb (x 14 12)
              clear * - r26340 e26341 e26342 b26343 b26344 b26345 b26346 d26323 d26318
              omega
            have d26347 : (x 13 5).toNat = 0 := by
              have r26348 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
              have b26349 := hb (x 13 5)
              have b26350 := hb (x 13 13)
              clear * - r26348 b26349 b26350 d26339
              omega
            have d26351 : (x 13 3 && x 13 14).toNat = 0 := by
              have r26352 := hand2 (x 13 3) (x 13 14)
              have b26353 := hb (x 13 14)
              have b26354 := hb (x 13 3 && x 13 14)
              clear * - r26352 b26353 b26354 d26310
              omega
            have d26355 : (x 16 11).toNat = 1 := by
              have r26356 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26357 := hb (x 12 4)
              have b26358 := hb (x 16 11)
              have b26359 := hb (x 15 1 && x 15 12)
              have b26360 := hb (x 14 2 && x 14 13)
              have b26361 := hb (x 13 3 && x 13 14)
              clear * - r26356 b26357 b26358 b26359 b26360 b26361 d26253 d26265 d26351 d26149
              omega
            have d26362 : (x 16 3).toNat = 1 := by
              have r26363 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
              have b26364 := hb (x 16 3)
              have b26365 := hb (x 16 11)
              clear * - r26363 b26364 b26365 d26355
              omega
            have d26366 : (x 19 12).toNat = 0 := by
              have r26367 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26368 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e26369 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b26370 := hb (x 16 3)
              have b26371 := hb (x 17 2)
              have b26372 := hb (x 18 13)
              have b26373 := hb (x 19 12)
              clear * - r26367 e26368 e26369 b26370 b26371 b26372 b26373 d26362
              omega
            have d26374 : (x 18 13).toNat = 0 := by
              have r26375 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26376 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e26377 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b26378 := hb (x 16 3)
              have b26379 := hb (x 17 2)
              have b26380 := hb (x 18 13)
              have b26381 := hb (x 19 12)
              clear * - r26375 e26376 e26377 b26378 b26379 b26380 b26381 d26366 d26362
              omega
            have d26382 : (x 17 2).toNat = 0 := by
              have r26383 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26384 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e26385 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b26386 := hb (x 16 3)
              have b26387 := hb (x 17 2)
              have b26388 := hb (x 18 13)
              have b26389 := hb (x 19 12)
              clear * - r26383 e26384 e26385 b26386 b26387 b26388 b26389 d26366 d26374 d26362
              omega
            have d26390 : (x 13 12).toNat = 0 := by
              have r26391 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26392 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e26393 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b26394 := hb (x 10 3)
              have b26395 := hb (x 11 2)
              have b26396 := hb (x 12 13)
              have b26397 := hb (x 13 12)
              clear * - r26391 e26392 e26393 b26394 b26395 b26396 b26397 d26301 d26289
              omega
            have d26398 : (x 13 4).toNat = 0 := by
              have r26399 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
              have b26400 := hb (x 13 4)
              have b26401 := hb (x 13 12)
              clear * - r26399 b26400 b26401 d26390
              omega
            have d26402 : (x 10 3).toNat = 0 := by
              have r26403 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26404 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e26405 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b26406 := hb (x 10 3)
              have b26407 := hb (x 11 2)
              have b26408 := hb (x 12 13)
              have b26409 := hb (x 13 12)
              clear * - r26403 e26404 e26405 b26406 b26407 b26408 b26409 d26390 d26301 d26289
              omega
            have d26410 : (x 10 3 && x 10 14).toNat = 0 := by
              have r26411 := hand1 (x 10 3) (x 10 14)
              have b26412 := hb (x 10 3)
              have b26413 := hb (x 10 3 && x 10 14)
              clear * - r26411 b26412 b26413 d26402
              omega
            have d26414 : (x 13 11).toNat = 1 := by
              have r26415 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26416 := hb (x 9 4)
              have b26417 := hb (x 13 11)
              have b26418 := hb (x 12 1 && x 12 12)
              have b26419 := hb (x 11 2 && x 11 13)
              have b26420 := hb (x 10 3 && x 10 14)
              clear * - r26415 b26416 b26417 b26418 b26419 b26420 d26145 d26161 d26410 d26110
              omega
            have d26421 : (x 13 3).toNat = 1 := by
              have r26422 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
              have b26423 := hb (x 13 3)
              have b26424 := hb (x 13 11)
              clear * - r26422 b26423 b26424 d26414
              omega
            have d26425 : (x 16 12).toNat = 0 := by
              have r26426 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26427 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e26428 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b26429 := hb (x 13 3)
              have b26430 := hb (x 14 2)
              have b26431 := hb (x 15 13)
              have b26432 := hb (x 16 12)
              clear * - r26426 e26427 e26428 b26429 b26430 b26431 b26432 d26421
              omega
            have d26433 : (x 16 1 && x 16 12).toNat = 0 := by
              have r26434 := hand2 (x 16 1) (x 16 12)
              have b26435 := hb (x 16 12)
              have b26436 := hb (x 16 1 && x 16 12)
              clear * - r26434 b26435 b26436 d26425
              omega
            have d26437 : (x 16 2 && x 16 12).toNat = 0 := by
              have r26438 := hand2 (x 16 2) (x 16 12)
              have b26439 := hb (x 16 12)
              have b26440 := hb (x 16 2 && x 16 12)
              clear * - r26438 b26439 b26440 d26425
              omega
            have d26441 : (x 15 13).toNat = 0 := by
              have r26442 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26443 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e26444 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b26445 := hb (x 13 3)
              have b26446 := hb (x 14 2)
              have b26447 := hb (x 15 13)
              have b26448 := hb (x 16 12)
              clear * - r26442 e26443 e26444 b26445 b26446 b26447 b26448 d26425 d26421
              omega
            have d26449 : (x 15 2 && x 15 13).toNat = 0 := by
              have r26450 := hand2 (x 15 2) (x 15 13)
              have b26451 := hb (x 15 13)
              have b26452 := hb (x 15 2 && x 15 13)
              clear * - r26450 b26451 b26452 d26441
              omega
            have d26453 : (x 15 3 && x 15 13).toNat = 0 := by
              have r26454 := hand2 (x 15 3) (x 15 13)
              have b26455 := hb (x 15 13)
              have b26456 := hb (x 15 3 && x 15 13)
              clear * - r26454 b26455 b26456 d26441
              omega
            have d26457 : (x 14 1 && x 14 14).toNat = 1 := by
              have r26458 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26459 := hb (x 13 2)
              have b26460 := hb (x 15 13)
              have b26461 := hb (x 14 1 && x 14 14)
              clear * - r26458 b26459 b26460 b26461 d26441 d26269
              omega
            have d26462 : (x 14 1).toNat = 1 := by
              have r26463 := hand1 (x 14 1) (x 14 14)
              have b26464 := hb (x 14 1)
              have b26465 := hb (x 14 1 && x 14 14)
              clear * - r26463 b26464 b26465 d26457
              omega
            have d26466 : (x 15 14).toNat = 0 := by
              have r26467 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26468 := hb (x 14 1)
              have b26469 := hb (x 15 14)
              clear * - r26467 b26468 b26469 d26462
              omega
            have d26470 : (x 15 1 && x 15 14).toNat = 0 := by
              have r26471 := hand2 (x 15 1) (x 15 14)
              have b26472 := hb (x 15 14)
              have b26473 := hb (x 15 1 && x 15 14)
              clear * - r26471 b26472 b26473 d26466
              omega
            have d26474 : (x 15 2).toNat = 0 := by
              have r26475 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
              have b26476 := hb (x 15 2)
              have b26477 := hb (x 15 14)
              clear * - r26475 b26476 b26477 d26466
              omega
            have d26478 : (x 14 2).toNat = 0 := by
              have r26479 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26480 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e26481 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b26482 := hb (x 13 3)
              have b26483 := hb (x 14 2)
              have b26484 := hb (x 15 13)
              have b26485 := hb (x 16 12)
              clear * - r26479 e26480 e26481 b26482 b26483 b26484 b26485 d26425 d26441 d26421
              omega
            have d26486 : (x 16 13).toNat = 1 := by
              have r26487 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26488 := hb (x 14 2)
              have b26489 := hb (x 16 13)
              have b26490 := hb (x 15 1 && x 15 14)
              clear * - r26487 b26488 b26489 b26490 d26470 d26478
              omega
            have d26491 : (x 17 12).toNat = 0 := by
              have r26492 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26493 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e26494 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b26495 := hb (x 14 3)
              have b26496 := hb (x 15 2)
              have b26497 := hb (x 16 13)
              have b26498 := hb (x 17 12)
              clear * - r26492 e26493 e26494 b26495 b26496 b26497 b26498 d26486 d26474
              omega
            have d26499 : (x 14 3).toNat = 0 := by
              have r26500 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26501 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e26502 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b26503 := hb (x 14 3)
              have b26504 := hb (x 15 2)
              have b26505 := hb (x 16 13)
              have b26506 := hb (x 17 12)
              clear * - r26500 e26501 e26502 b26503 b26504 b26505 b26506 d26491 d26486 d26474
              omega
            have d26507 : (x 14 3 && x 14 14).toNat = 0 := by
              have r26508 := hand1 (x 14 3) (x 14 14)
              have b26509 := hb (x 14 3)
              have b26510 := hb (x 14 3 && x 14 14)
              clear * - r26508 b26509 b26510 d26499
              omega
            have d26511 : (x 17 11).toNat = 1 := by
              have r26512 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26513 := hb (x 13 4)
              have b26514 := hb (x 17 11)
              have b26515 := hb (x 16 1 && x 16 12)
              have b26516 := hb (x 15 2 && x 15 13)
              have b26517 := hb (x 14 3 && x 14 14)
              clear * - r26512 b26513 b26514 b26515 b26516 b26517 d26433 d26449 d26507 d26398
              omega
            have d26518 : (x 17 3).toNat = 1 := by
              have r26519 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
              have b26520 := hb (x 17 3)
              have b26521 := hb (x 17 11)
              clear * - r26519 b26520 b26521 d26511
              omega
            have d26522 : (x 20 12).toNat = 0 := by
              have r26523 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26524 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e26525 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b26526 := hb (x 17 3)
              have b26527 := hb (x 18 2)
              have b26528 := hb (x 19 13)
              have b26529 := hb (x 20 12)
              clear * - r26523 e26524 e26525 b26526 b26527 b26528 b26529 d26518
              omega
            have d26530 : (x 19 13).toNat = 0 := by
              have r26531 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26532 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e26533 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b26534 := hb (x 17 3)
              have b26535 := hb (x 18 2)
              have b26536 := hb (x 19 13)
              have b26537 := hb (x 20 12)
              clear * - r26531 e26532 e26533 b26534 b26535 b26536 b26537 d26522 d26518
              omega
            have d26538 : (x 18 1 && x 18 14).toNat = 1 := by
              have r26539 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26540 := hb (x 17 2)
              have b26541 := hb (x 19 13)
              have b26542 := hb (x 18 1 && x 18 14)
              clear * - r26539 b26540 b26541 b26542 d26530 d26382
              omega
            have d26543 : (x 18 14).toNat = 1 := by
              have r26544 := hand2 (x 18 1) (x 18 14)
              have b26545 := hb (x 18 14)
              have b26546 := hb (x 18 1 && x 18 14)
              clear * - r26544 b26545 b26546 d26538
              omega
            have d26547 : (x 17 1).toNat = 0 := by
              have r26548 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26549 := hb (x 17 1)
              have b26550 := hb (x 18 14)
              clear * - r26548 b26549 b26550 d26543
              omega
            have d26551 : (x 17 1 && x 17 11).toNat = 0 := by
              have r26552 := hand1 (x 17 1) (x 17 11)
              have b26553 := hb (x 17 1)
              have b26554 := hb (x 17 1 && x 17 11)
              clear * - r26552 b26553 b26554 d26547
              omega
            have d26555 : (x 18 2).toNat = 0 := by
              have r26556 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26557 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e26558 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b26559 := hb (x 17 3)
              have b26560 := hb (x 18 2)
              have b26561 := hb (x 19 13)
              have b26562 := hb (x 20 12)
              clear * - r26556 e26557 e26558 b26559 b26560 b26561 b26562 d26522 d26530 d26518
              omega
            have d26563 : (x 18 10).toNat = 0 := by
              have r26564 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
              have b26565 := hb (x 18 2)
              have b26566 := hb (x 18 10)
              clear * - r26564 b26565 b26566 d26555
              omega
            have r26567 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b26568 := hb (x 13 5)
            have b26569 := hb (x 18 10)
            have b26570 := hb (x 17 1 && x 17 11)
            have b26571 := hb (x 16 2 && x 16 12)
            have b26572 := hb (x 15 3 && x 15 13)
            have b26573 := hb (x 14 4 && x 14 14)
            linarith only [r26567, b26568, b26569, b26570, b26571, b26572, b26573, d26563, d26551, d26437, d26453, d26335, d26347]
    · have f26574 : (x 0 12).toNat = 1 := by rw [h22834]; rfl
      have d26575 : (x (-1) 13).toNat = 0 := by
        have r26576 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e26577 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e26578 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b26579 := hb (x (-3) 3)
        have b26580 := hb (x (-2) 2)
        have b26581 := hb (x (-1) 13)
        have b26582 := hb (x 0 12)
        clear * - r26576 e26577 e26578 b26579 b26580 b26581 b26582 f26574
        omega
      have d26583 : (x (-3) 2).toNat = 1 := by
        have r26584 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b26585 := hb (x (-3) 2)
        have b26586 := hb (x (-1) 13)
        have b26587 := hb (x (-2) 1 && x (-2) 14)
        clear * - r26584 b26585 b26586 b26587 d26575 g107
        omega
      have d26588 : (x (-2) 2).toNat = 0 := by
        have r26589 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e26590 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e26591 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b26592 := hb (x (-3) 3)
        have b26593 := hb (x (-2) 2)
        have b26594 := hb (x (-1) 13)
        have b26595 := hb (x 0 12)
        clear * - r26589 e26590 e26591 b26592 b26593 b26594 b26595 f26574 d26575
        omega
      have d26596 : (x (-3) 3).toNat = 0 := by
        have r26597 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e26598 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e26599 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b26600 := hb (x (-3) 3)
        have b26601 := hb (x (-2) 2)
        have b26602 := hb (x (-1) 13)
        have b26603 := hb (x 0 12)
        clear * - r26597 e26598 e26599 b26600 b26601 b26602 b26603 f26574 d26575 d26588
        omega
      have d26604 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
        have r26605 := hand1 (x (-3) 3) (x (-3) 14)
        have b26606 := hb (x (-3) 3)
        have b26607 := hb (x (-3) 3 && x (-3) 14)
        clear * - r26605 b26606 b26607 d26596
        omega
      have d26608 : (x (-1) 12).toNat = 0 := by
        have r26609 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e26610 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e26611 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b26612 := hb (x (-4) 3)
        have b26613 := hb (x (-3) 2)
        have b26614 := hb (x (-2) 13)
        have b26615 := hb (x (-1) 12)
        clear * - r26609 e26610 e26611 b26612 b26613 b26614 b26615 g10 d26583
        omega
      have d26616 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
        have r26617 := hand2 (x (-1) 1) (x (-1) 12)
        have b26618 := hb (x (-1) 12)
        have b26619 := hb (x (-1) 1 && x (-1) 12)
        clear * - r26617 b26618 b26619 d26608
        omega
      have r26620 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26621 := hb (x (-4) 4)
      have b26622 := hb (x 0 11)
      have b26623 := hb (x (-1) 1 && x (-1) 12)
      have b26624 := hb (x (-2) 2 && x (-2) 13)
      have b26625 := hb (x (-3) 3 && x (-3) 14)
      linarith only [r26620, b26621, b26622, b26623, b26624, b26625, g22, d26616, g97, d26604, g3]
  · have f26626 : (x 0 7).toNat = 1 := by rw [h22828]; rfl
    have d26627 : (x 7 8).toNat = 0 := by
      have r26628 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26629 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e26630 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e26631 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e26632 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e26633 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e26634 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b26635 := hb (x 0 7)
      have b26636 := hb (x 1 6)
      have b26637 := hb (x 2 5)
      have b26638 := hb (x 3 4)
      have b26639 := hb (x 4 11)
      have b26640 := hb (x 5 10)
      have b26641 := hb (x 6 9)
      have b26642 := hb (x 7 8)
      clear * - r26628 e26629 e26630 e26631 e26632 e26633 e26634 b26635 b26636 b26637 b26638 b26639 b26640 b26641 b26642 g34 f26626
      omega
    have d26643 : (x 6 9).toNat = 0 := by
      have r26644 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26645 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e26646 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e26647 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e26648 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e26649 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e26650 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b26651 := hb (x 0 7)
      have b26652 := hb (x 1 6)
      have b26653 := hb (x 2 5)
      have b26654 := hb (x 3 4)
      have b26655 := hb (x 4 11)
      have b26656 := hb (x 5 10)
      have b26657 := hb (x 6 9)
      have b26658 := hb (x 7 8)
      clear * - r26644 e26645 e26646 e26647 e26648 e26649 e26650 b26651 b26652 b26653 b26654 b26655 b26656 b26657 b26658 d26627 g34 f26626
      omega
    have d26659 : (x 5 10).toNat = 0 := by
      have r26660 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26661 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e26662 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e26663 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e26664 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e26665 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e26666 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b26667 := hb (x 0 7)
      have b26668 := hb (x 1 6)
      have b26669 := hb (x 2 5)
      have b26670 := hb (x 3 4)
      have b26671 := hb (x 4 11)
      have b26672 := hb (x 5 10)
      have b26673 := hb (x 6 9)
      have b26674 := hb (x 7 8)
      clear * - r26660 e26661 e26662 e26663 e26664 e26665 e26666 b26667 b26668 b26669 b26670 b26671 b26672 b26673 b26674 d26627 d26643 g34 f26626
      omega
    have d26675 : (x 5 1 && x 5 10).toNat = 0 := by
      have r26676 := hand2 (x 5 1) (x 5 10)
      have b26677 := hb (x 5 10)
      have b26678 := hb (x 5 1 && x 5 10)
      clear * - r26676 b26677 b26678 d26659
      omega
    have d26679 : (x 4 11).toNat = 0 := by
      have r26680 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26681 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e26682 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e26683 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e26684 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e26685 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e26686 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b26687 := hb (x 0 7)
      have b26688 := hb (x 1 6)
      have b26689 := hb (x 2 5)
      have b26690 := hb (x 3 4)
      have b26691 := hb (x 4 11)
      have b26692 := hb (x 5 10)
      have b26693 := hb (x 6 9)
      have b26694 := hb (x 7 8)
      clear * - r26680 e26681 e26682 e26683 e26684 e26685 e26686 b26687 b26688 b26689 b26690 b26691 b26692 b26693 b26694 d26627 d26643 d26659 g34 f26626
      omega
    have d26695 : (x 4 1 && x 4 11).toNat = 0 := by
      have r26696 := hand2 (x 4 1) (x 4 11)
      have b26697 := hb (x 4 11)
      have b26698 := hb (x 4 1 && x 4 11)
      clear * - r26696 b26697 b26698 d26679
      omega
    have d26699 : (x 2 3 && x 2 13).toNat = 1 := by
      have r26700 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26701 := hb (x 0 5)
      have b26702 := hb (x 5 10)
      have b26703 := hb (x 4 1 && x 4 11)
      have b26704 := hb (x 3 2 && x 3 12)
      have b26705 := hb (x 2 3 && x 2 13)
      have b26706 := hb (x 1 4 && x 1 14)
      clear * - r26700 b26701 b26702 b26703 b26704 b26705 b26706 d26659 d26695 g94 g95 g17
      omega
    have d26707 : (x 2 3).toNat = 1 := by
      have r26708 := hand1 (x 2 3) (x 2 13)
      have b26709 := hb (x 2 3)
      have b26710 := hb (x 2 3 && x 2 13)
      clear * - r26708 b26709 b26710 d26699
      omega
    have d26711 : (x 5 12).toNat = 0 := by
      have r26712 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26713 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e26714 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b26715 := hb (x 2 3)
      have b26716 := hb (x 3 2)
      have b26717 := hb (x 4 13)
      have b26718 := hb (x 5 12)
      clear * - r26712 e26713 e26714 b26715 b26716 b26717 b26718 g33 d26707
      omega
    have d26719 : (x 5 2 && x 5 12).toNat = 0 := by
      have r26720 := hand2 (x 5 2) (x 5 12)
      have b26721 := hb (x 5 12)
      have b26722 := hb (x 5 2 && x 5 12)
      clear * - r26720 b26721 b26722 d26711
      omega
    have d26723 : (x 5 4).toNat = 0 := by
      have r26724 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b26725 := hb (x 5 4)
      have b26726 := hb (x 5 12)
      clear * - r26724 b26725 b26726 d26711
      omega
    have d26727 : (x 4 13).toNat = 0 := by
      have r26728 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26729 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e26730 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b26731 := hb (x 2 3)
      have b26732 := hb (x 3 2)
      have b26733 := hb (x 4 13)
      have b26734 := hb (x 5 12)
      clear * - r26728 e26729 e26730 b26731 b26732 b26733 b26734 d26711 g33 d26707
      omega
    have d26735 : (x 4 3 && x 4 13).toNat = 0 := by
      have r26736 := hand2 (x 4 3) (x 4 13)
      have b26737 := hb (x 4 13)
      have b26738 := hb (x 4 3 && x 4 13)
      clear * - r26736 b26737 b26738 d26727
      omega
    have d26739 : (x 4 5).toNat = 0 := by
      have r26740 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
      have b26741 := hb (x 4 5)
      have b26742 := hb (x 4 13)
      clear * - r26740 b26741 b26742 d26727
      omega
    have d26743 : (x 2 2).toNat = 1 := by
      have r26744 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26745 := hb (x 2 2)
      have b26746 := hb (x 4 13)
      have b26747 := hb (x 3 1 && x 3 14)
      clear * - r26744 b26745 b26746 b26747 d26727 g108
      omega
    have d26748 : (x 4 12).toNat = 0 := by
      have r26749 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26750 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e26751 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b26752 := hb (x 1 3)
      have b26753 := hb (x 2 2)
      have b26754 := hb (x 3 13)
      have b26755 := hb (x 4 12)
      clear * - r26749 e26750 e26751 b26752 b26753 b26754 b26755 d26743
      omega
    have d26756 : (x 3 13).toNat = 0 := by
      have r26757 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26758 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e26759 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b26760 := hb (x 1 3)
      have b26761 := hb (x 2 2)
      have b26762 := hb (x 3 13)
      have b26763 := hb (x 4 12)
      clear * - r26757 e26758 e26759 b26760 b26761 b26762 b26763 d26748 d26743
      omega
    have d26764 : (x 1 3).toNat = 0 := by
      have r26765 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26766 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e26767 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b26768 := hb (x 1 3)
      have b26769 := hb (x 2 2)
      have b26770 := hb (x 3 13)
      have b26771 := hb (x 4 12)
      clear * - r26765 e26766 e26767 b26768 b26769 b26770 b26771 d26748 d26756 d26743
      omega
    have d26772 : (x 1 11).toNat = 0 := by
      have r26773 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b26774 := hb (x 1 3)
      have b26775 := hb (x 1 11)
      clear * - r26773 b26774 b26775 d26764
      omega
    have d26776 : (x 4 2 && x 4 11).toNat = 0 := by
      have r26777 := hand2 (x 4 2) (x 4 11)
      have b26778 := hb (x 4 11)
      have b26779 := hb (x 4 2 && x 4 11)
      clear * - r26777 b26778 b26779 d26679
      omega
    have d26780 : (x 2 4 && x 2 13).toNat = 1 := by
      have r26781 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26782 := hb (x 0 6)
      have b26783 := hb (x 6 9)
      have b26784 := hb (x 5 1 && x 5 10)
      have b26785 := hb (x 4 2 && x 4 11)
      have b26786 := hb (x 3 3 && x 3 12)
      have b26787 := hb (x 2 4 && x 2 13)
      have b26788 := hb (x 1 5 && x 1 14)
      clear * - r26781 b26782 b26783 b26784 b26785 b26786 b26787 b26788 d26643 d26675 d26776 g86 g87 g18
      omega
    have d26789 : (x 2 4).toNat = 1 := by
      have r26790 := hand1 (x 2 4) (x 2 13)
      have b26791 := hb (x 2 4)
      have b26792 := hb (x 2 4 && x 2 13)
      clear * - r26790 b26791 b26792 d26780
      omega
    have d26793 : (x 2 12).toNat = 1 := by
      have r26794 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b26795 := hb (x 2 4)
      have b26796 := hb (x 2 12)
      clear * - r26794 b26795 b26796 d26789
      omega
    have d26797 : (x (-1) 3).toNat = 0 := by
      have r26798 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26799 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e26800 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b26801 := hb (x (-1) 3)
      have b26802 := hb (x 0 2)
      have b26803 := hb (x 1 13)
      have b26804 := hb (x 2 12)
      clear * - r26798 e26799 e26800 b26801 b26802 b26803 b26804 d26793 g29 g14
      omega
    have d26805 : (x (-1) 11).toNat = 0 := by
      have r26806 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b26807 := hb (x (-1) 3)
      have b26808 := hb (x (-1) 11)
      clear * - r26806 b26807 b26808 d26797
      omega
    have d26809 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
      have r26810 := hand2 (x (-1) 1) (x (-1) 11)
      have b26811 := hb (x (-1) 11)
      have b26812 := hb (x (-1) 1 && x (-1) 11)
      clear * - r26810 b26811 b26812 d26805
      omega
    have d26813 : (x 2 5).toNat = 0 := by
      have r26814 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26815 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e26816 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e26817 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e26818 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e26819 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e26820 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b26821 := hb (x 0 7)
      have b26822 := hb (x 1 6)
      have b26823 := hb (x 2 5)
      have b26824 := hb (x 3 4)
      have b26825 := hb (x 4 11)
      have b26826 := hb (x 5 10)
      have b26827 := hb (x 6 9)
      have b26828 := hb (x 7 8)
      clear * - r26814 e26815 e26816 e26817 e26818 e26819 e26820 b26821 b26822 b26823 b26824 b26825 b26826 b26827 b26828 d26627 d26643 d26659 d26679 g34 f26626
      omega
    have r26829 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26830 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
    have e26831 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
    have e26832 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
    have e26833 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
    have e26834 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
    have e26835 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
    have r26836 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26837 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e26838 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e26839 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e26840 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e26841 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e26842 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have r26843 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26844 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e26845 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e26846 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e26847 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e26848 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e26849 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have r26850 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26851 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e26852 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e26853 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e26854 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e26855 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e26856 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have r26857 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26858 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e26859 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have r26860 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26861 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e26862 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have r26863 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26864 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e26865 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have r26866 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26867 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
    have e26868 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
    have r26869 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r26870 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r26871 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r26872 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r26873 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r26874 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r26875 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r26876 := hand2 (x 2 3) (x 2 7)
    have r26877 := hand2 (x (-1) 6) (x (-1) 10)
    have r26878 := hand1 (x (-3) 8) (x (-3) 12)
    have r26879 := hand2 (x (-4) 9) (x (-4) 13)
    have r26880 := hand1 (x (-4) 3) (x (-4) 12)
    have r26881 := hand1 (x (-5) 4) (x (-5) 13)
    have r26882 := hand1 (x (-6) 5) (x (-6) 14)
    have r26883 := hand2 (x (-1) 1) (x (-1) 10)
    have r26884 := hand2 (x (-3) 3) (x (-3) 12)
    have r26885 := hand2 (x (-4) 1) (x (-4) 11)
    have r26886 := hand1 (x (-5) 2) (x (-5) 12)
    have r26887 := hand1 (x (-6) 3) (x (-6) 13)
    have r26888 := hand1 (x (-7) 4) (x (-7) 14)
    have r26889 := hand1 (x (-2) 2) (x (-2) 12)
    have r26890 := hand1 (x (-3) 3) (x (-3) 13)
    have r26891 := hand2 (x 6 1) (x 6 11)
    have r26892 := hand2 (x (-1) 2) (x (-1) 13)
    linarith only [r26829, e26830, e26831, e26832, e26833, e26834, e26835, r26836, e26837, e26838, e26839, e26840, e26841, e26842, r26843, e26844, e26845, e26846, e26847, e26848, e26849, r26850, e26851, e26852, e26853, e26854, e26855, e26856, r26857, e26858, e26859, r26860, e26861, e26862, r26863, e26864, e26865, r26866, e26867, e26868, r26869, r26870, r26871, r26872, r26873, r26874, r26875, r26876, r26877, r26878, r26879, r26880, r26881, r26882, r26883, r26884, r26885, r26886, r26887, r26888, r26889, r26890, r26891, r26892, g1, g2, g7, g9, g10, g12, g20, g21, d26772, d26813, g35, d26739, d26723, g43, g44, g45, g46, g76, g77, g78, g79, g80, d26809, g89, d26719, d26735, g96, g98, g99, g107]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt000100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-7) 7).toNat = 0)
    (g1 : (x (-6) 6).toNat = 0)
    (g2 : (x (-5) 5).toNat = 0)
    (g3 : (x (-4) 4).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 3).toNat = 0)
    (g6 : (x (-2) 5).toNat = 0)
    (g7 : (x (-2) 9).toNat = 0)
    (g8 : (x (-2) 10).toNat = 0)
    (g9 : (x (-2) 11).toNat = 0)
    (g10 : (x (-2) 13).toNat = 0)
    (g11 : (x (-1) 2).toNat = 1)
    (g12 : (x (-1) 9).toNat = 0)
    (g13 : (x 0 1).toNat = 0)
    (g14 : (x 0 2).toNat = 0)
    (g15 : (x 0 3).toNat = 0)
    (g16 : (x 0 4).toNat = 0)
    (g17 : (x 0 5).toNat = 0)
    (g18 : (x 0 6).toNat = 0)
    (g19 : (x 0 8).toNat = 1)
    (g20 : (x 0 9).toNat = 0)
    (g21 : (x 0 10).toNat = 0)
    (g22 : (x 0 11).toNat = 0)
    (g23 : (x 0 13).toNat = 0)
    (g24 : (x 1 2).toNat = 0)
    (g25 : (x 1 4).toNat = 0)
    (g26 : (x 1 5).toNat = 0)
    (g27 : (x 1 9).toNat = 0)
    (g28 : (x 1 10).toNat = 0)
    (g29 : (x 1 13).toNat = 0)
    (g30 : (x 1 14).toNat = 1)
    (g31 : (x 2 1).toNat = 1)
    (g32 : (x 2 13).toNat = 1)
    (g33 : (x 3 2).toNat = 0)
    (g34 : (x 3 4).toNat = 0)
    (g35 : (x 3 6).toNat = 0)
    (g36 : (x 3 10).toNat = 0)
    (g37 : (x 3 12).toNat = 0)
    (g38 : (x 3 9 && x 3 12).toNat = 0)
    (g39 : (x (-4) 4 && x (-4) 8).toNat = 0)
    (g40 : (x (-5) 5 && x (-5) 9).toNat = 0)
    (g41 : (x (-6) 6 && x (-6) 10).toNat = 0)
    (g42 : (x (-7) 7 && x (-7) 11).toNat = 0)
    (g43 : (x 3 2 && x 3 6).toNat = 0)
    (g44 : (x 1 4 && x 1 8).toNat = 0)
    (g45 : (x 0 5 && x 0 9).toNat = 0)
    (g46 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g47 : (x 3 4 && x 3 8).toNat = 0)
    (g48 : (x 1 6 && x 1 10).toNat = 0)
    (g49 : (x 0 7 && x 0 11).toNat = 0)
    (g50 : (x (-2) 9 && x (-2) 13).toNat = 0)
    (g51 : (x 0 1 && x 0 6).toNat = 0)
    (g52 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g53 : (x 1 2 && x 1 7).toNat = 0)
    (g54 : (x 0 3 && x 0 8).toNat = 0)
    (g55 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g56 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g57 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g58 : (x 3 6 && x 3 11).toNat = 0)
    (g59 : (x 1 8 && x 1 13).toNat = 0)
    (g60 : (x 0 9 && x 0 14).toNat = 0)
    (g61 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g62 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g63 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g64 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g65 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g66 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g67 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g68 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g69 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g70 : (x 0 1 && x 0 8).toNat = 0)
    (g71 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g72 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g73 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g74 : (x 3 4 && x 3 11).toNat = 0)
    (g75 : (x 1 6 && x 1 13).toNat = 0)
    (g76 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g77 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g78 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g79 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g80 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g81 : (x 0 1 && x 0 10).toNat = 0)
    (g82 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g83 : (x 3 2 && x 3 11).toNat = 0)
    (g84 : (x 1 4 && x 1 13).toNat = 0)
    (g85 : (x 0 5 && x 0 14).toNat = 0)
    (g86 : (x 3 3 && x 3 12).toNat = 0)
    (g87 : (x 1 5 && x 1 14).toNat = 0)
    (g88 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g89 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g90 : (x 1 2 && x 1 12).toNat = 0)
    (g91 : (x 0 3 && x 0 13).toNat = 0)
    (g92 : (x 1 3 && x 1 13).toNat = 0)
    (g93 : (x 0 4 && x 0 14).toNat = 0)
    (g94 : (x 3 2 && x 3 12).toNat = 0)
    (g95 : (x 1 4 && x 1 14).toNat = 0)
    (g96 : (x 3 4 && x 3 14).toNat = 0)
    (g97 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g98 : (x 0 1 && x 0 12).toNat = 0)
    (g99 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g100 : (x 1 1 && x 1 12).toNat = 0)
    (g101 : (x 0 2 && x 0 13).toNat = 0)
    (g102 : (x 1 2 && x 1 13).toNat = 0)
    (g103 : (x 0 3 && x 0 14).toNat = 0)
    (g104 : (x 3 1 && x 3 12).toNat = 0)
    (g105 : (x 3 2 && x 3 13).toNat = 0)
    (g106 : (x 3 3 && x 3 14).toNat = 0)
    (g107 : (x (-2) 1 && x (-2) 14).toNat = 0)
    (g108 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt000100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108
