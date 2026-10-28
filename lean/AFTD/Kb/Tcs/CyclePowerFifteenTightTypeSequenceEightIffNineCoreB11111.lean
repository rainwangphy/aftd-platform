import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b11111

Topic: combinatorics   Node: 599a0f3d4664

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 112 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b11111_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 6).toNat = 0)
    (g1 : (x (-4) 7).toNat = 0)
    (g2 : (x (-3) 6).toNat = 0)
    (g3 : (x (-3) 7).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 5).toNat = 0)
    (g6 : (x (-2) 6).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-2) 11).toNat = 0)
    (g9 : (x (-1) 4).toNat = 0)
    (g10 : (x (-1) 5).toNat = 0)
    (g11 : (x (-1) 7).toNat = 0)
    (g12 : (x (-1) 9).toNat = 0)
    (g13 : (x (-1) 10).toNat = 0)
    (g14 : (x (-1) 11).toNat = 0)
    (g15 : (x (-1) 13).toNat = 0)
    (g16 : (x 0 3).toNat = 1)
    (g17 : (x 0 4).toNat = 1)
    (g18 : (x 0 7).toNat = 1)
    (g19 : (x 0 8).toNat = 0)
    (g20 : (x 0 9).toNat = 1)
    (g21 : (x 0 11).toNat = 1)
    (g22 : (x 0 13).toNat = 1)
    (g23 : (x 0 14).toNat = 1)
    (g24 : (x 1 2).toNat = 0)
    (g25 : (x 1 4).toNat = 0)
    (g26 : (x 1 5).toNat = 0)
    (g27 : (x 1 6).toNat = 0)
    (g28 : (x 1 8).toNat = 0)
    (g29 : (x 1 10).toNat = 0)
    (g30 : (x 1 12).toNat = 0)
    (g31 : (x 1 13).toNat = 0)
    (g32 : (x 1 14).toNat = 0)
    (g33 : (x 2 5).toNat = 0)
    (g34 : (x 2 9).toNat = 0)
    (g35 : (x 2 11).toNat = 0)
    (g36 : (x 2 12).toNat = 0)
    (g37 : (x 2 13).toNat = 0)
    (g38 : (x 3 4).toNat = 0)
    (g39 : (x 3 8).toNat = 0)
    (g40 : (x 3 10).toNat = 0)
    (g41 : (x 3 11).toNat = 0)
    (g42 : (x 3 12).toNat = 0)
    (g43 : (x 4 9).toNat = 0)
    (g44 : (x 4 10).toNat = 0)
    (g45 : (x 5 8).toNat = 0)
    (g46 : (x 5 9).toNat = 0)
    (g47 : (x 6 8).toNat = 0)
    (g48 : (x 3 12 && x 3 13).toNat = 0)
    (g49 : (x 2 13 && x 2 14).toNat = 0)
    (g50 : (x 0 4 && x 0 8).toNat = 0)
    (g51 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g52 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g53 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g54 : (x 4 4 && x 4 8).toNat = 0)
    (g55 : (x 3 5 && x 3 9).toNat = 0)
    (g56 : (x 2 6 && x 2 10).toNat = 0)
    (g57 : (x 1 7 && x 1 11).toNat = 0)
    (g58 : (x 0 8 && x 0 12).toNat = 0)
    (g59 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g60 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g61 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g62 : (x 1 2 && x 1 7).toNat = 0)
    (g63 : (x 0 3 && x 0 8).toNat = 0)
    (g64 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g65 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g66 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g67 : (x (-4) 7 && x (-4) 12).toNat = 0)
    (g68 : (x 5 3 && x 5 8).toNat = 0)
    (g69 : (x 4 4 && x 4 9).toNat = 0)
    (g70 : (x 3 5 && x 3 10).toNat = 0)
    (g71 : (x 2 6 && x 2 11).toNat = 0)
    (g72 : (x 1 7 && x 1 12).toNat = 0)
    (g73 : (x 0 8 && x 0 13).toNat = 0)
    (g74 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g75 : (x 3 7 && x 3 12).toNat = 0)
    (g76 : (x 2 8 && x 2 13).toNat = 0)
    (g77 : (x 1 9 && x 1 14).toNat = 0)
    (g78 : (x 3 8 && x 3 13).toNat = 0)
    (g79 : (x 2 9 && x 2 14).toNat = 0)
    (g80 : (x 0 2 && x 0 8).toNat = 0)
    (g81 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g82 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g83 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g84 : (x 6 2 && x 6 8).toNat = 0)
    (g85 : (x 5 3 && x 5 9).toNat = 0)
    (g86 : (x 4 4 && x 4 10).toNat = 0)
    (g87 : (x 3 5 && x 3 11).toNat = 0)
    (g88 : (x 2 6 && x 2 12).toNat = 0)
    (g89 : (x 1 7 && x 1 13).toNat = 0)
    (g90 : (x 0 8 && x 0 14).toNat = 0)
    (g91 : (x 0 1 && x 0 8).toNat = 0)
    (g92 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g93 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g94 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g95 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g96 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g97 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g98 : (x 3 5 && x 3 12).toNat = 0)
    (g99 : (x 2 6 && x 2 13).toNat = 0)
    (g100 : (x 1 7 && x 1 14).toNat = 0)
    (g101 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g102 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g103 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g104 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g105 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g106 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g107 : (x 3 4 && x 3 13).toNat = 0)
    (g108 : (x 2 5 && x 2 14).toNat = 0)
    (g109 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g110 : (x 2 4 && x 2 14).toNat = 0)
    (g111 : (x 3 4 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d23910 : (x 7 8).toNat = 0 := by
    have r23911 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23912 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e23913 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e23914 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e23915 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e23916 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e23917 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b23918 := hb (x 0 7)
    have b23919 := hb (x 1 6)
    have b23920 := hb (x 2 5)
    have b23921 := hb (x 3 4)
    have b23922 := hb (x 4 11)
    have b23923 := hb (x 5 10)
    have b23924 := hb (x 6 9)
    have b23925 := hb (x 7 8)
    clear * - r23911 e23912 e23913 e23914 e23915 e23916 e23917 b23918 b23919 b23920 b23921 b23922 b23923 b23924 b23925 g38 g33 g27 g18
    omega
  have d23926 : (x 7 1 && x 7 8).toNat = 0 := by
    have r23927 := hand2 (x 7 1) (x 7 8)
    have b23928 := hb (x 7 8)
    have b23929 := hb (x 7 1 && x 7 8)
    clear * - r23927 b23928 b23929 d23910
    omega
  have d23930 : (x 7 3 && x 7 8).toNat = 0 := by
    have r23931 := hand2 (x 7 3) (x 7 8)
    have b23932 := hb (x 7 8)
    have b23933 := hb (x 7 3 && x 7 8)
    clear * - r23931 b23932 b23933 d23910
    omega
  have d23934 : (x 7 8 && x 7 9).toNat = 0 := by
    have r23935 := hand1 (x 7 8) (x 7 9)
    have b23936 := hb (x 7 8)
    have b23937 := hb (x 7 8 && x 7 9)
    clear * - r23935 b23936 b23937 d23910
    omega
  have d23938 : (x 6 9).toNat = 0 := by
    have r23939 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23940 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e23941 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e23942 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e23943 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e23944 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e23945 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b23946 := hb (x 0 7)
    have b23947 := hb (x 1 6)
    have b23948 := hb (x 2 5)
    have b23949 := hb (x 3 4)
    have b23950 := hb (x 4 11)
    have b23951 := hb (x 5 10)
    have b23952 := hb (x 6 9)
    have b23953 := hb (x 7 8)
    clear * - r23939 e23940 e23941 e23942 e23943 e23944 e23945 b23946 b23947 b23948 b23949 b23950 b23951 b23952 b23953 d23910 g38 g33 g27 g18
    omega
  have d23954 : (x 6 2 && x 6 9).toNat = 0 := by
    have r23955 := hand2 (x 6 2) (x 6 9)
    have b23956 := hb (x 6 9)
    have b23957 := hb (x 6 2 && x 6 9)
    clear * - r23955 b23956 b23957 d23938
    omega
  have d23958 : (x 6 4 && x 6 9).toNat = 0 := by
    have r23959 := hand2 (x 6 4) (x 6 9)
    have b23960 := hb (x 6 9)
    have b23961 := hb (x 6 4 && x 6 9)
    clear * - r23959 b23960 b23961 d23938
    omega
  have d23962 : (x 6 9 && x 6 10).toNat = 0 := by
    have r23963 := hand1 (x 6 9) (x 6 10)
    have b23964 := hb (x 6 9)
    have b23965 := hb (x 6 9 && x 6 10)
    clear * - r23963 b23964 b23965 d23938
    omega
  have d23966 : (x 5 10).toNat = 0 := by
    have r23967 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23968 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e23969 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e23970 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e23971 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e23972 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e23973 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b23974 := hb (x 0 7)
    have b23975 := hb (x 1 6)
    have b23976 := hb (x 2 5)
    have b23977 := hb (x 3 4)
    have b23978 := hb (x 4 11)
    have b23979 := hb (x 5 10)
    have b23980 := hb (x 6 9)
    have b23981 := hb (x 7 8)
    clear * - r23967 e23968 e23969 e23970 e23971 e23972 e23973 b23974 b23975 b23976 b23977 b23978 b23979 b23980 b23981 d23910 d23938 g38 g33 g27 g18
    omega
  have d23982 : (x 5 3 && x 5 10).toNat = 0 := by
    have r23983 := hand2 (x 5 3) (x 5 10)
    have b23984 := hb (x 5 10)
    have b23985 := hb (x 5 3 && x 5 10)
    clear * - r23983 b23984 b23985 d23966
    omega
  have d23986 : (x 5 5 && x 5 10).toNat = 0 := by
    have r23987 := hand2 (x 5 5) (x 5 10)
    have b23988 := hb (x 5 10)
    have b23989 := hb (x 5 5 && x 5 10)
    clear * - r23987 b23988 b23989 d23966
    omega
  have d23990 : (x 5 10 && x 5 11).toNat = 0 := by
    have r23991 := hand1 (x 5 10) (x 5 11)
    have b23992 := hb (x 5 10)
    have b23993 := hb (x 5 10 && x 5 11)
    clear * - r23991 b23992 b23993 d23966
    omega
  have d23994 : (x 4 11).toNat = 0 := by
    have r23995 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23996 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e23997 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e23998 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e23999 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e24000 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e24001 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b24002 := hb (x 0 7)
    have b24003 := hb (x 1 6)
    have b24004 := hb (x 2 5)
    have b24005 := hb (x 3 4)
    have b24006 := hb (x 4 11)
    have b24007 := hb (x 5 10)
    have b24008 := hb (x 6 9)
    have b24009 := hb (x 7 8)
    clear * - r23995 e23996 e23997 e23998 e23999 e24000 e24001 b24002 b24003 b24004 b24005 b24006 b24007 b24008 b24009 d23910 d23938 d23966 g38 g33 g27 g18
    omega
  have d24010 : (x 4 4 && x 4 11).toNat = 0 := by
    have r24011 := hand2 (x 4 4) (x 4 11)
    have b24012 := hb (x 4 11)
    have b24013 := hb (x 4 4 && x 4 11)
    clear * - r24011 b24012 b24013 d23994
    omega
  have d24014 : (x 4 6 && x 4 11).toNat = 0 := by
    have r24015 := hand2 (x 4 6) (x 4 11)
    have b24016 := hb (x 4 11)
    have b24017 := hb (x 4 6 && x 4 11)
    clear * - r24015 b24016 b24017 d23994
    omega
  have d24018 : (x 4 11 && x 4 12).toNat = 0 := by
    have r24019 := hand1 (x 4 11) (x 4 12)
    have b24020 := hb (x 4 11)
    have b24021 := hb (x 4 11 && x 4 12)
    clear * - r24019 b24020 b24021 d23994
    omega
  have d24022 : (x 8 7).toNat = 1 := by
    have r24023 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24024 := hb (x 0 8)
    have b24025 := hb (x 8 7)
    have b24026 := hb (x 7 1 && x 7 8)
    have b24027 := hb (x 6 2 && x 6 9)
    have b24028 := hb (x 5 3 && x 5 10)
    have b24029 := hb (x 4 4 && x 4 11)
    have b24030 := hb (x 3 5 && x 3 12)
    have b24031 := hb (x 2 6 && x 2 13)
    have b24032 := hb (x 1 7 && x 1 14)
    clear * - r24023 b24024 b24025 b24026 b24027 b24028 b24029 b24030 b24031 b24032 d23926 d23954 d23982 d24010 g98 g99 g100 g19
    omega
  have d24033 : (x 15 8).toNat = 0 := by
    have r24034 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24035 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e24036 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e24037 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e24038 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e24039 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e24040 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b24041 := hb (x 8 7)
    have b24042 := hb (x 9 6)
    have b24043 := hb (x 10 5)
    have b24044 := hb (x 11 4)
    have b24045 := hb (x 12 11)
    have b24046 := hb (x 13 10)
    have b24047 := hb (x 14 9)
    have b24048 := hb (x 15 8)
    clear * - r24034 e24035 e24036 e24037 e24038 e24039 e24040 b24041 b24042 b24043 b24044 b24045 b24046 b24047 b24048 d24022
    omega
  have d24049 : (x 14 9).toNat = 0 := by
    have r24050 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24051 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e24052 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e24053 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e24054 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e24055 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e24056 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b24057 := hb (x 8 7)
    have b24058 := hb (x 9 6)
    have b24059 := hb (x 10 5)
    have b24060 := hb (x 11 4)
    have b24061 := hb (x 12 11)
    have b24062 := hb (x 13 10)
    have b24063 := hb (x 14 9)
    have b24064 := hb (x 15 8)
    clear * - r24050 e24051 e24052 e24053 e24054 e24055 e24056 b24057 b24058 b24059 b24060 b24061 b24062 b24063 b24064 d24033 d24022
    omega
  have d24065 : (x 13 10).toNat = 0 := by
    have r24066 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24067 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e24068 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e24069 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e24070 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e24071 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e24072 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b24073 := hb (x 8 7)
    have b24074 := hb (x 9 6)
    have b24075 := hb (x 10 5)
    have b24076 := hb (x 11 4)
    have b24077 := hb (x 12 11)
    have b24078 := hb (x 13 10)
    have b24079 := hb (x 14 9)
    have b24080 := hb (x 15 8)
    clear * - r24066 e24067 e24068 e24069 e24070 e24071 e24072 b24073 b24074 b24075 b24076 b24077 b24078 b24079 b24080 d24033 d24049 d24022
    omega
  have d24081 : (x 13 1 && x 13 10).toNat = 0 := by
    have r24082 := hand2 (x 13 1) (x 13 10)
    have b24083 := hb (x 13 10)
    have b24084 := hb (x 13 1 && x 13 10)
    clear * - r24082 b24083 b24084 d24065
    omega
  have d24085 : (x 12 11).toNat = 0 := by
    have r24086 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24087 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e24088 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e24089 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e24090 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e24091 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e24092 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b24093 := hb (x 8 7)
    have b24094 := hb (x 9 6)
    have b24095 := hb (x 10 5)
    have b24096 := hb (x 11 4)
    have b24097 := hb (x 12 11)
    have b24098 := hb (x 13 10)
    have b24099 := hb (x 14 9)
    have b24100 := hb (x 15 8)
    clear * - r24086 e24087 e24088 e24089 e24090 e24091 e24092 b24093 b24094 b24095 b24096 b24097 b24098 b24099 b24100 d24033 d24049 d24065 d24022
    omega
  have d24101 : (x 12 2 && x 12 11).toNat = 0 := by
    have r24102 := hand2 (x 12 2) (x 12 11)
    have b24103 := hb (x 12 11)
    have b24104 := hb (x 12 2 && x 12 11)
    clear * - r24102 b24103 b24104 d24085
    omega
  have d24105 : (x 11 4).toNat = 0 := by
    have r24106 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24107 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e24108 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e24109 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e24110 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e24111 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e24112 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b24113 := hb (x 8 7)
    have b24114 := hb (x 9 6)
    have b24115 := hb (x 10 5)
    have b24116 := hb (x 11 4)
    have b24117 := hb (x 12 11)
    have b24118 := hb (x 13 10)
    have b24119 := hb (x 14 9)
    have b24120 := hb (x 15 8)
    clear * - r24106 e24107 e24108 e24109 e24110 e24111 e24112 b24113 b24114 b24115 b24116 b24117 b24118 b24119 b24120 d24033 d24049 d24065 d24085 d24022
    omega
  have d24121 : (x 11 4 && x 11 5).toNat = 0 := by
    have r24122 := hand1 (x 11 4) (x 11 5)
    have b24123 := hb (x 11 4)
    have b24124 := hb (x 11 4 && x 11 5)
    clear * - r24122 b24123 b24124 d24105
    omega
  have d24125 : (x 10 5).toNat = 0 := by
    have r24126 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24127 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e24128 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e24129 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e24130 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e24131 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e24132 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b24133 := hb (x 8 7)
    have b24134 := hb (x 9 6)
    have b24135 := hb (x 10 5)
    have b24136 := hb (x 11 4)
    have b24137 := hb (x 12 11)
    have b24138 := hb (x 13 10)
    have b24139 := hb (x 14 9)
    have b24140 := hb (x 15 8)
    clear * - r24126 e24127 e24128 e24129 e24130 e24131 e24132 b24133 b24134 b24135 b24136 b24137 b24138 b24139 b24140 d24033 d24049 d24065 d24085 d24105 d24022
    omega
  have d24141 : (x 10 5 && x 10 6).toNat = 0 := by
    have r24142 := hand1 (x 10 5) (x 10 6)
    have b24143 := hb (x 10 5)
    have b24144 := hb (x 10 5 && x 10 6)
    clear * - r24142 b24143 b24144 d24125
    omega
  have d24145 : (x 9 6).toNat = 0 := by
    have r24146 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24147 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e24148 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e24149 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e24150 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e24151 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e24152 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b24153 := hb (x 8 7)
    have b24154 := hb (x 9 6)
    have b24155 := hb (x 10 5)
    have b24156 := hb (x 11 4)
    have b24157 := hb (x 12 11)
    have b24158 := hb (x 13 10)
    have b24159 := hb (x 14 9)
    have b24160 := hb (x 15 8)
    clear * - r24146 e24147 e24148 e24149 e24150 e24151 e24152 b24153 b24154 b24155 b24156 b24157 b24158 b24159 b24160 d24033 d24049 d24065 d24085 d24105 d24125 d24022
    omega
  have d24161 : (x 9 1 && x 9 6).toNat = 0 := by
    have r24162 := hand2 (x 9 1) (x 9 6)
    have b24163 := hb (x 9 6)
    have b24164 := hb (x 9 1 && x 9 6)
    clear * - r24162 b24163 b24164 d24145
    omega
  have d24165 : (x 9 6 && x 9 7).toNat = 0 := by
    have r24166 := hand1 (x 9 6) (x 9 7)
    have b24167 := hb (x 9 6)
    have b24168 := hb (x 9 6 && x 9 7)
    clear * - r24166 b24167 b24168 d24145
    omega
  cases h24169 : x 0 10
  · have f24170 : (x 0 10).toNat = 0 := by rw [h24169]; rfl
    have d24171 : (x 0 1 && x 0 10).toNat = 0 := by
      have r24172 := hand2 (x 0 1) (x 0 10)
      have b24173 := hb (x 0 10)
      have b24174 := hb (x 0 1 && x 0 10)
      clear * - r24172 b24173 b24174 f24170
      omega
    have d24175 : (x 1 9).toNat = 1 := by
      have r24176 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24177 := hb (x (-5) 6)
      have b24178 := hb (x 1 9)
      have b24179 := hb (x 0 1 && x 0 10)
      have b24180 := hb (x (-1) 2 && x (-1) 11)
      have b24181 := hb (x (-2) 3 && x (-2) 12)
      have b24182 := hb (x (-3) 4 && x (-3) 13)
      have b24183 := hb (x (-4) 5 && x (-4) 14)
      clear * - r24176 b24177 b24178 b24179 b24180 b24181 b24182 b24183 d24171 g103 g104 g105 g106 g0
      omega
    have d24184 : (x 1 1).toNat = 1 := by
      have r24185 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b24186 := hb (x 1 1)
      have b24187 := hb (x 1 9)
      clear * - r24185 b24186 b24187 d24175
      omega
    have d24188 : (x 2 14).toNat = 0 := by
      have r24189 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24190 := hb (x 1 1)
      have b24191 := hb (x 2 14)
      clear * - r24189 b24190 b24191 d24184
      omega
    have d24192 : (x 2 1 && x 2 14).toNat = 0 := by
      have r24193 := hand2 (x 2 1) (x 2 14)
      have b24194 := hb (x 2 14)
      have b24195 := hb (x 2 1 && x 2 14)
      clear * - r24193 b24194 b24195 d24188
      omega
    have d24196 : (x 3 13).toNat = 1 := by
      have r24197 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24198 := hb (x 1 2)
      have b24199 := hb (x 3 13)
      have b24200 := hb (x 2 1 && x 2 14)
      clear * - r24197 b24198 b24199 b24200 d24192 g24
      omega
    have d24201 : (x 4 12).toNat = 0 := by
      have r24202 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24203 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e24204 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b24205 := hb (x 1 3)
      have b24206 := hb (x 2 2)
      have b24207 := hb (x 3 13)
      have b24208 := hb (x 4 12)
      clear * - r24202 e24203 e24204 b24205 b24206 b24207 b24208 d24196
      omega
    have d24209 : (x 4 3 && x 4 12).toNat = 0 := by
      have r24210 := hand2 (x 4 3) (x 4 12)
      have b24211 := hb (x 4 12)
      have b24212 := hb (x 4 3 && x 4 12)
      clear * - r24210 b24211 b24212 d24201
      omega
    have d24213 : (x 8 2 && x 8 7).toNat = 1 := by
      have r24214 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24215 := hb (x 0 10)
      have b24216 := hb (x 10 5)
      have b24217 := hb (x 9 1 && x 9 6)
      have b24218 := hb (x 8 2 && x 8 7)
      have b24219 := hb (x 7 3 && x 7 8)
      have b24220 := hb (x 6 4 && x 6 9)
      have b24221 := hb (x 5 5 && x 5 10)
      have b24222 := hb (x 4 6 && x 4 11)
      have b24223 := hb (x 3 7 && x 3 12)
      have b24224 := hb (x 2 8 && x 2 13)
      have b24225 := hb (x 1 9 && x 1 14)
      clear * - r24214 b24215 b24216 b24217 b24218 b24219 b24220 b24221 b24222 b24223 b24224 b24225 d24125 d24161 d23930 d23958 d23986 d24014 g75 g76 g77 f24170
      omega
    have d24226 : (x 8 2).toNat = 1 := by
      have r24227 := hand1 (x 8 2) (x 8 7)
      have b24228 := hb (x 8 2)
      have b24229 := hb (x 8 2 && x 8 7)
      clear * - r24227 b24228 b24229 d24213
      omega
    have d24230 : (x 8 14).toNat = 1 := by
      have r24231 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
      have b24232 := hb (x 8 2)
      have b24233 := hb (x 8 14)
      clear * - r24231 b24232 b24233 d24226
      omega
    have d24234 : (x 7 1).toNat = 0 := by
      have r24235 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24236 := hb (x 7 1)
      have b24237 := hb (x 8 14)
      clear * - r24235 b24236 b24237 d24230
      omega
    have d24238 : (x 7 1 && x 7 7).toNat = 0 := by
      have r24239 := hand1 (x 7 1) (x 7 7)
      have b24240 := hb (x 7 1)
      have b24241 := hb (x 7 1 && x 7 7)
      clear * - r24239 b24240 b24241 d24234
      omega
    have d24242 : (x 8 6).toNat = 1 := by
      have r24243 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24244 := hb (x (-1) 9)
      have b24245 := hb (x 8 6)
      have b24246 := hb (x 7 1 && x 7 7)
      have b24247 := hb (x 6 2 && x 6 8)
      have b24248 := hb (x 5 3 && x 5 9)
      have b24249 := hb (x 4 4 && x 4 10)
      have b24250 := hb (x 3 5 && x 3 11)
      have b24251 := hb (x 2 6 && x 2 12)
      have b24252 := hb (x 1 7 && x 1 13)
      have b24253 := hb (x 0 8 && x 0 14)
      clear * - r24243 b24244 b24245 b24246 b24247 b24248 b24249 b24250 b24251 b24252 b24253 d24238 g84 g85 g86 g87 g88 g89 g90 g12
      omega
    have d24254 : (x 14 8).toNat = 0 := by
      have r24255 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24256 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e24257 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e24258 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e24259 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e24260 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e24261 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b24262 := hb (x 7 7)
      have b24263 := hb (x 8 6)
      have b24264 := hb (x 9 5)
      have b24265 := hb (x 10 4)
      have b24266 := hb (x 11 11)
      have b24267 := hb (x 12 10)
      have b24268 := hb (x 13 9)
      have b24269 := hb (x 14 8)
      clear * - r24255 e24256 e24257 e24258 e24259 e24260 e24261 b24262 b24263 b24264 b24265 b24266 b24267 b24268 b24269 d24242
      omega
    have d24270 : (x 13 9).toNat = 0 := by
      have r24271 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24272 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e24273 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e24274 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e24275 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e24276 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e24277 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b24278 := hb (x 7 7)
      have b24279 := hb (x 8 6)
      have b24280 := hb (x 9 5)
      have b24281 := hb (x 10 4)
      have b24282 := hb (x 11 11)
      have b24283 := hb (x 12 10)
      have b24284 := hb (x 13 9)
      have b24285 := hb (x 14 8)
      clear * - r24271 e24272 e24273 e24274 e24275 e24276 e24277 b24278 b24279 b24280 b24281 b24282 b24283 b24284 b24285 d24254 d24242
      omega
    have d24286 : (x 12 10).toNat = 0 := by
      have r24287 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24288 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e24289 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e24290 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e24291 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e24292 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e24293 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b24294 := hb (x 7 7)
      have b24295 := hb (x 8 6)
      have b24296 := hb (x 9 5)
      have b24297 := hb (x 10 4)
      have b24298 := hb (x 11 11)
      have b24299 := hb (x 12 10)
      have b24300 := hb (x 13 9)
      have b24301 := hb (x 14 8)
      clear * - r24287 e24288 e24289 e24290 e24291 e24292 e24293 b24294 b24295 b24296 b24297 b24298 b24299 b24300 b24301 d24254 d24270 d24242
      omega
    have d24302 : (x 11 11).toNat = 0 := by
      have r24303 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24304 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e24305 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e24306 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e24307 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e24308 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e24309 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b24310 := hb (x 7 7)
      have b24311 := hb (x 8 6)
      have b24312 := hb (x 9 5)
      have b24313 := hb (x 10 4)
      have b24314 := hb (x 11 11)
      have b24315 := hb (x 12 10)
      have b24316 := hb (x 13 9)
      have b24317 := hb (x 14 8)
      clear * - r24303 e24304 e24305 e24306 e24307 e24308 e24309 b24310 b24311 b24312 b24313 b24314 b24315 b24316 b24317 d24254 d24270 d24286 d24242
      omega
    have d24318 : (x 11 1 && x 11 11).toNat = 0 := by
      have r24319 := hand2 (x 11 1) (x 11 11)
      have b24320 := hb (x 11 11)
      have b24321 := hb (x 11 1 && x 11 11)
      clear * - r24319 b24320 b24321 d24302
      omega
    have d24322 : (x 7 13).toNat = 0 := by
      have r24323 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b24324 := hb (x 7 1)
      have b24325 := hb (x 7 13)
      clear * - r24323 b24324 b24325 d24234
      omega
    have d24326 : (x 7 5).toNat = 0 := by
      have r24327 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
      have b24328 := hb (x 7 5)
      have b24329 := hb (x 7 13)
      clear * - r24327 b24328 b24329 d24322
      omega
    have d24330 : (x 7 9).toNat = 0 := by
      have r24331 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
      have b24332 := hb (x 7 1)
      have b24333 := hb (x 7 9)
      clear * - r24331 b24332 b24333 d24234
      omega
    have d24334 : (x 10 12).toNat = 0 := by
      have r24335 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24336 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e24337 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b24338 := hb (x 7 3)
      have b24339 := hb (x 8 2)
      have b24340 := hb (x 9 13)
      have b24341 := hb (x 10 12)
      clear * - r24335 e24336 e24337 b24338 b24339 b24340 b24341 d24226
      omega
    have d24342 : (x 10 2 && x 10 12).toNat = 0 := by
      have r24343 := hand2 (x 10 2) (x 10 12)
      have b24344 := hb (x 10 12)
      have b24345 := hb (x 10 2 && x 10 12)
      clear * - r24343 b24344 b24345 d24334
      omega
    have d24346 : (x 9 13).toNat = 0 := by
      have r24347 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24348 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e24349 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b24350 := hb (x 7 3)
      have b24351 := hb (x 8 2)
      have b24352 := hb (x 9 13)
      have b24353 := hb (x 10 12)
      clear * - r24347 e24348 e24349 b24350 b24351 b24352 b24353 d24334 d24226
      omega
    have d24354 : (x 9 3 && x 9 13).toNat = 0 := by
      have r24355 := hand2 (x 9 3) (x 9 13)
      have b24356 := hb (x 9 13)
      have b24357 := hb (x 9 3 && x 9 13)
      clear * - r24355 b24356 b24357 d24346
      omega
    have d24358 : (x 8 4 && x 8 14).toNat = 1 := by
      have r24359 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24360 := hb (x 7 5)
      have b24361 := hb (x 12 10)
      have b24362 := hb (x 11 1 && x 11 11)
      have b24363 := hb (x 10 2 && x 10 12)
      have b24364 := hb (x 9 3 && x 9 13)
      have b24365 := hb (x 8 4 && x 8 14)
      clear * - r24359 b24360 b24361 b24362 b24363 b24364 b24365 d24286 d24318 d24342 d24354 d24326
      omega
    have d24366 : (x 8 4).toNat = 1 := by
      have r24367 := hand1 (x 8 4) (x 8 14)
      have b24368 := hb (x 8 4)
      have b24369 := hb (x 8 4 && x 8 14)
      clear * - r24367 b24368 b24369 d24358
      omega
    have d24370 : (x 8 12).toNat = 1 := by
      have r24371 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
      have b24372 := hb (x 8 4)
      have b24373 := hb (x 8 12)
      clear * - r24371 b24372 b24373 d24366
      omega
    have d24374 : (x 6 2).toNat = 0 := by
      have r24375 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24376 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e24377 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b24378 := hb (x 5 3)
      have b24379 := hb (x 6 2)
      have b24380 := hb (x 7 13)
      have b24381 := hb (x 8 12)
      clear * - r24375 e24376 e24377 b24378 b24379 b24380 b24381 d24370 d24322
      omega
    have d24382 : (x 6 10).toNat = 0 := by
      have r24383 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
      have b24384 := hb (x 6 2)
      have b24385 := hb (x 6 10)
      clear * - r24383 b24384 b24385 d24374
      omega
    have d24386 : (x 6 1 && x 6 10).toNat = 0 := by
      have r24387 := hand2 (x 6 1) (x 6 10)
      have b24388 := hb (x 6 10)
      have b24389 := hb (x 6 1 && x 6 10)
      clear * - r24387 b24388 b24389 d24382
      omega
    have d24390 : (x 5 2 && x 5 11).toNat = 1 := by
      have r24391 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24392 := hb (x 1 6)
      have b24393 := hb (x 7 9)
      have b24394 := hb (x 6 1 && x 6 10)
      have b24395 := hb (x 5 2 && x 5 11)
      have b24396 := hb (x 4 3 && x 4 12)
      have b24397 := hb (x 3 4 && x 3 13)
      have b24398 := hb (x 2 5 && x 2 14)
      clear * - r24391 b24392 b24393 b24394 b24395 b24396 b24397 b24398 d24330 d24386 d24209 g107 g108 g27
      omega
    have d24399 : (x 5 11).toNat = 1 := by
      have r24400 := hand2 (x 5 2) (x 5 11)
      have b24401 := hb (x 5 11)
      have b24402 := hb (x 5 2 && x 5 11)
      clear * - r24400 b24401 b24402 d24390
      omega
    have d24403 : (x 5 3).toNat = 1 := by
      have r24404 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
      have b24405 := hb (x 5 3)
      have b24406 := hb (x 5 11)
      clear * - r24404 b24405 b24406 d24399
      omega
    have r24407 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24408 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e24409 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b24410 := hb (x 5 3)
    have b24411 := hb (x 6 2)
    have b24412 := hb (x 7 13)
    have b24413 := hb (x 8 12)
    linarith only [r24407, e24408, e24409, b24410, b24411, b24412, b24413, d24370, d24322, d24374, d24403]
  · have f24414 : (x 0 10).toNat = 1 := by rw [h24169]; rfl
    have d24415 : (x 2 8).toNat = 0 := by
      have r24416 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24417 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e24418 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e24419 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e24420 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e24421 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e24422 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b24423 := hb (x (-5) 7)
      have b24424 := hb (x (-4) 6)
      have b24425 := hb (x (-3) 5)
      have b24426 := hb (x (-2) 4)
      have b24427 := hb (x (-1) 11)
      have b24428 := hb (x 0 10)
      have b24429 := hb (x 1 9)
      have b24430 := hb (x 2 8)
      clear * - r24416 e24417 e24418 e24419 e24420 e24421 e24422 b24423 b24424 b24425 b24426 b24427 b24428 b24429 b24430 f24414 g14
      omega
    have d24431 : (x 2 8 && x 2 14).toNat = 0 := by
      have r24432 := hand1 (x 2 8) (x 2 14)
      have b24433 := hb (x 2 8)
      have b24434 := hb (x 2 8 && x 2 14)
      clear * - r24432 b24433 b24434 d24415
      omega
    have d24435 : (x 1 9).toNat = 0 := by
      have r24436 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24437 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e24438 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e24439 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e24440 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e24441 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e24442 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b24443 := hb (x (-5) 7)
      have b24444 := hb (x (-4) 6)
      have b24445 := hb (x (-3) 5)
      have b24446 := hb (x (-2) 4)
      have b24447 := hb (x (-1) 11)
      have b24448 := hb (x 0 10)
      have b24449 := hb (x 1 9)
      have b24450 := hb (x 2 8)
      clear * - r24436 e24437 e24438 e24439 e24440 e24441 e24442 b24443 b24444 b24445 b24446 b24447 b24448 b24449 b24450 d24415 f24414 g14
      omega
    have d24451 : (x (-2) 4).toNat = 0 := by
      have r24452 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24453 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e24454 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e24455 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e24456 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e24457 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e24458 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b24459 := hb (x (-5) 7)
      have b24460 := hb (x (-4) 6)
      have b24461 := hb (x (-3) 5)
      have b24462 := hb (x (-2) 4)
      have b24463 := hb (x (-1) 11)
      have b24464 := hb (x 0 10)
      have b24465 := hb (x 1 9)
      have b24466 := hb (x 2 8)
      clear * - r24452 e24453 e24454 e24455 e24456 e24457 e24458 b24459 b24460 b24461 b24462 b24463 b24464 b24465 b24466 d24415 d24435 f24414 g14
      omega
    have d24467 : (x (-3) 5).toNat = 0 := by
      have r24468 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24469 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e24470 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e24471 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e24472 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e24473 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e24474 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b24475 := hb (x (-5) 7)
      have b24476 := hb (x (-4) 6)
      have b24477 := hb (x (-3) 5)
      have b24478 := hb (x (-2) 4)
      have b24479 := hb (x (-1) 11)
      have b24480 := hb (x 0 10)
      have b24481 := hb (x 1 9)
      have b24482 := hb (x 2 8)
      clear * - r24468 e24469 e24470 e24471 e24472 e24473 e24474 b24475 b24476 b24477 b24478 b24479 b24480 b24481 b24482 d24415 d24435 f24414 g14 d24451
      omega
    have d24483 : (x (-4) 6).toNat = 0 := by
      have r24484 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24485 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e24486 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e24487 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e24488 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e24489 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e24490 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b24491 := hb (x (-5) 7)
      have b24492 := hb (x (-4) 6)
      have b24493 := hb (x (-3) 5)
      have b24494 := hb (x (-2) 4)
      have b24495 := hb (x (-1) 11)
      have b24496 := hb (x 0 10)
      have b24497 := hb (x 1 9)
      have b24498 := hb (x 2 8)
      clear * - r24484 e24485 e24486 e24487 e24488 e24489 e24490 b24491 b24492 b24493 b24494 b24495 b24496 b24497 b24498 d24415 d24435 f24414 g14 d24451 d24467
      omega
    have d24499 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
      have r24500 := hand1 (x (-4) 6) (x (-4) 12)
      have b24501 := hb (x (-4) 6)
      have b24502 := hb (x (-4) 6 && x (-4) 12)
      clear * - r24500 b24501 b24502 d24483
      omega
    have d24503 : (x (-5) 7).toNat = 0 := by
      have r24504 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24505 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e24506 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e24507 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e24508 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e24509 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e24510 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b24511 := hb (x (-5) 7)
      have b24512 := hb (x (-4) 6)
      have b24513 := hb (x (-3) 5)
      have b24514 := hb (x (-2) 4)
      have b24515 := hb (x (-1) 11)
      have b24516 := hb (x 0 10)
      have b24517 := hb (x 1 9)
      have b24518 := hb (x 2 8)
      clear * - r24504 e24505 e24506 e24507 e24508 e24509 e24510 b24511 b24512 b24513 b24514 b24515 b24516 b24517 b24518 d24415 d24435 f24414 g14 d24451 d24467 d24483
      omega
    have d24519 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
      have r24520 := hand1 (x (-5) 7) (x (-5) 13)
      have b24521 := hb (x (-5) 7)
      have b24522 := hb (x (-5) 7 && x (-5) 13)
      clear * - r24520 b24521 b24522 d24503
      omega
    cases h24523 : x 1 1
    · have f24524 : (x 1 1).toNat = 0 := by rw [h24523]; rfl
      have d24525 : (x 1 1 && x 1 7).toNat = 0 := by
        have r24526 := hand1 (x 1 1) (x 1 7)
        have b24527 := hb (x 1 1)
        have b24528 := hb (x 1 1 && x 1 7)
        clear * - r24526 b24527 b24528 f24524
        omega
      have d24529 : (x 2 14).toNat = 1 := by
        have r24530 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b24531 := hb (x 1 1)
        have b24532 := hb (x 2 14)
        clear * - r24530 b24531 b24532 f24524
        omega
      cases h24533 : x 1 3
      · have f24534 : (x 1 3).toNat = 0 := by rw [h24533]; rfl
        have d24535 : (x 1 3 && x 1 7).toNat = 0 := by
          have r24536 := hand1 (x 1 3) (x 1 7)
          have b24537 := hb (x 1 3)
          have b24538 := hb (x 1 3 && x 1 7)
          clear * - r24536 b24537 b24538 f24534
          omega
        cases h24539 : x 1 7
        · have f24540 : (x 1 7).toNat = 0 := by rw [h24539]; rfl
          have d24541 : (x (-7) 8).toNat = 1 := by
            have r24542 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b24543 := hb (x (-7) 8)
            have b24544 := hb (x 1 7)
            have b24545 := hb (x 0 1 && x 0 8)
            have b24546 := hb (x (-1) 2 && x (-1) 9)
            have b24547 := hb (x (-2) 3 && x (-2) 10)
            have b24548 := hb (x (-3) 4 && x (-3) 11)
            have b24549 := hb (x (-4) 5 && x (-4) 12)
            have b24550 := hb (x (-5) 6 && x (-5) 13)
            have b24551 := hb (x (-6) 7 && x (-6) 14)
            clear * - r24542 b24543 b24544 b24545 b24546 b24547 b24548 b24549 b24550 b24551 f24540 g91 g92 g93 g94 g95 g96 g97
            omega
          have d24552 : (x (-8) 9).toNat = 0 := by
            have r24553 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24554 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e24555 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e24556 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e24557 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e24558 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e24559 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b24560 := hb (x (-14) 7)
            have b24561 := hb (x (-13) 6)
            have b24562 := hb (x (-12) 5)
            have b24563 := hb (x (-11) 4)
            have b24564 := hb (x (-10) 11)
            have b24565 := hb (x (-9) 10)
            have b24566 := hb (x (-8) 9)
            have b24567 := hb (x (-7) 8)
            clear * - r24553 e24554 e24555 e24556 e24557 e24558 e24559 b24560 b24561 b24562 b24563 b24564 b24565 b24566 b24567 d24541
            omega
          have d24568 : (x (-9) 10).toNat = 0 := by
            have r24569 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24570 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e24571 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e24572 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e24573 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e24574 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e24575 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b24576 := hb (x (-14) 7)
            have b24577 := hb (x (-13) 6)
            have b24578 := hb (x (-12) 5)
            have b24579 := hb (x (-11) 4)
            have b24580 := hb (x (-10) 11)
            have b24581 := hb (x (-9) 10)
            have b24582 := hb (x (-8) 9)
            have b24583 := hb (x (-7) 8)
            clear * - r24569 e24570 e24571 e24572 e24573 e24574 e24575 b24576 b24577 b24578 b24579 b24580 b24581 b24582 b24583 d24541 d24552
            omega
          have d24584 : (x (-10) 11).toNat = 0 := by
            have r24585 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24586 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e24587 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e24588 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e24589 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e24590 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e24591 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b24592 := hb (x (-14) 7)
            have b24593 := hb (x (-13) 6)
            have b24594 := hb (x (-12) 5)
            have b24595 := hb (x (-11) 4)
            have b24596 := hb (x (-10) 11)
            have b24597 := hb (x (-9) 10)
            have b24598 := hb (x (-8) 9)
            have b24599 := hb (x (-7) 8)
            clear * - r24585 e24586 e24587 e24588 e24589 e24590 e24591 b24592 b24593 b24594 b24595 b24596 b24597 b24598 b24599 d24541 d24552 d24568
            omega
          have d24600 : (x (-11) 4).toNat = 0 := by
            have r24601 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24602 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e24603 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e24604 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e24605 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e24606 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e24607 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b24608 := hb (x (-14) 7)
            have b24609 := hb (x (-13) 6)
            have b24610 := hb (x (-12) 5)
            have b24611 := hb (x (-11) 4)
            have b24612 := hb (x (-10) 11)
            have b24613 := hb (x (-9) 10)
            have b24614 := hb (x (-8) 9)
            have b24615 := hb (x (-7) 8)
            clear * - r24601 e24602 e24603 e24604 e24605 e24606 e24607 b24608 b24609 b24610 b24611 b24612 b24613 b24614 b24615 d24541 d24552 d24568 d24584
            omega
          have d24616 : (x (-11) 4 && x (-11) 14).toNat = 0 := by
            have r24617 := hand1 (x (-11) 4) (x (-11) 14)
            have b24618 := hb (x (-11) 4)
            have b24619 := hb (x (-11) 4 && x (-11) 14)
            clear * - r24617 b24618 b24619 d24600
            omega
          have d24620 : (x (-12) 5).toNat = 0 := by
            have r24621 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e24622 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e24623 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e24624 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e24625 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e24626 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e24627 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b24628 := hb (x (-14) 7)
            have b24629 := hb (x (-13) 6)
            have b24630 := hb (x (-12) 5)
            have b24631 := hb (x (-11) 4)
            have b24632 := hb (x (-10) 11)
            have b24633 := hb (x (-9) 10)
            have b24634 := hb (x (-8) 9)
            have b24635 := hb (x (-7) 8)
            clear * - r24621 e24622 e24623 e24624 e24625 e24626 e24627 b24628 b24629 b24630 b24631 b24632 b24633 b24634 b24635 d24541 d24552 d24568 d24584 d24600
            omega
          cases h24636 : x (-1) 8
          · have f24637 : (x (-1) 8).toNat = 0 := by rw [h24636]; rfl
            cases h24638 : x (-1) 12
            · have f24639 : (x (-1) 12).toNat = 0 := by rw [h24638]; rfl
              cases h24640 : x (-1) 14
              · have f24641 : (x (-1) 14).toNat = 0 := by rw [h24640]; rfl
                cases h24642 : x 2 1
                · have f24643 : (x 2 1).toNat = 0 := by rw [h24642]; rfl
                  have d24644 : (x 2 1 && x 2 14).toNat = 0 := by
                    have r24645 := hand1 (x 2 1) (x 2 14)
                    have b24646 := hb (x 2 1)
                    have b24647 := hb (x 2 1 && x 2 14)
                    clear * - r24645 b24646 b24647 f24643
                    omega
                  have d24648 : (x 3 13).toNat = 1 := by
                    have r24649 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b24650 := hb (x 1 2)
                    have b24651 := hb (x 3 13)
                    have b24652 := hb (x 2 1 && x 2 14)
                    clear * - r24649 b24650 b24651 b24652 d24644 g24
                    omega
                  have d24653 : (x 4 12).toNat = 0 := by
                    have r24654 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e24655 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e24656 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b24657 := hb (x 1 3)
                    have b24658 := hb (x 2 2)
                    have b24659 := hb (x 3 13)
                    have b24660 := hb (x 4 12)
                    clear * - r24654 e24655 e24656 b24657 b24658 b24659 b24660 d24648 f24534
                    omega
                  have d24661 : (x 4 3 && x 4 12).toNat = 0 := by
                    have r24662 := hand2 (x 4 3) (x 4 12)
                    have b24663 := hb (x 4 12)
                    have b24664 := hb (x 4 3 && x 4 12)
                    clear * - r24662 b24663 b24664 d24653
                    omega
                  have r24665 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r24666 : 1 ≤ (x 15 1).toNat + (x 14 1 && x 14 2).toNat + (x 13 2 && x 13 3).toNat + (x 12 3 && x 12 4).toNat + (x 11 4 && x 11 5).toNat + (x 10 5 && x 10 6).toNat + (x 9 6 && x 9 7).toNat + (x 8 7 && x 8 8).toNat + (x 7 8 && x 7 9).toNat + (x 6 9 && x 6 10).toNat + (x 5 10 && x 5 11).toNat + (x 4 11 && x 4 12).toNat + (x 3 12 && x 3 13).toNat + (x 2 13 && x 2 14).toNat + (x 1 14).toNat := by have q := hcov1 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r24667 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r24668 := hand2 (x 14 1) (x 14 2)
                  have r24669 := hand2 (x 13 2) (x 13 3)
                  have r24670 := hand2 (x 12 3) (x 12 4)
                  have r24671 := hand2 (x 8 7) (x 8 8)
                  have r24672 := hand2 (x 6 1) (x 6 10)
                  have r24673 := hand2 (x 5 2) (x 5 11)
                  linarith only [r24665, r24666, r24667, r24668, r24669, r24670, r24671, r24672, r24673, g27, g32, d24529, d24648, d24653, d24121, d24141, d24165, d23934, d23962, d23990, d24018, g48, g49, d24661, g107, g108]
                · have f24708 : (x 2 1).toNat = 1 := by rw [h24642]; rfl
                  have d24709 : (x 3 14).toNat = 0 := by
                    have r24710 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b24711 := hb (x 2 1)
                    have b24712 := hb (x 3 14)
                    clear * - r24710 b24711 b24712 f24708
                    omega
                  have d24713 : (x 3 1 && x 3 14).toNat = 0 := by
                    have r24714 := hand2 (x 3 1) (x 3 14)
                    have b24715 := hb (x 3 14)
                    have b24716 := hb (x 3 1 && x 3 14)
                    clear * - r24714 b24715 b24716 d24709
                    omega
                  have d24717 : (x 3 5 && x 3 14).toNat = 0 := by
                    have r24718 := hand2 (x 3 5) (x 3 14)
                    have b24719 := hb (x 3 14)
                    have b24720 := hb (x 3 5 && x 3 14)
                    clear * - r24718 b24719 b24720 d24709
                    omega
                  have d24721 : (x 3 6).toNat = 0 := by
                    have r24722 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
                    have b24723 := hb (x 3 6)
                    have b24724 := hb (x 3 14)
                    clear * - r24722 b24723 b24724 d24709
                    omega
                  have d24725 : (x 3 6 && x 3 13).toNat = 0 := by
                    have r24726 := hand1 (x 3 6) (x 3 13)
                    have b24727 := hb (x 3 6)
                    have b24728 := hb (x 3 6 && x 3 13)
                    clear * - r24726 b24727 b24728 d24721
                    omega
                  have d24729 : (x 3 2).toNat = 0 := by
                    have r24730 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                    have b24731 := hb (x 3 2)
                    have b24732 := hb (x 3 14)
                    clear * - r24730 b24731 b24732 d24709
                    omega
                  have d24733 : (x 3 2 && x 3 13).toNat = 0 := by
                    have r24734 := hand1 (x 3 2) (x 3 13)
                    have b24735 := hb (x 3 2)
                    have b24736 := hb (x 3 2 && x 3 13)
                    clear * - r24734 b24735 b24736 d24729
                    omega
                  cases h24737 : x 2 2
                  · have f24738 : (x 2 2).toNat = 0 := by rw [h24737]; rfl
                    have d24739 : (x 4 13).toNat = 1 := by
                      have r24740 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b24741 := hb (x 2 2)
                      have b24742 := hb (x 4 13)
                      have b24743 := hb (x 3 1 && x 3 14)
                      clear * - r24740 b24741 b24742 b24743 d24713 f24738
                      omega
                    have d24744 : (x 4 1).toNat = 1 := by
                      have r24745 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                      have b24746 := hb (x 4 1)
                      have b24747 := hb (x 4 13)
                      clear * - r24745 b24746 b24747 d24739
                      omega
                    have d24748 : (x 5 14).toNat = 0 := by
                      have r24749 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b24750 := hb (x 4 1)
                      have b24751 := hb (x 5 14)
                      clear * - r24749 b24750 b24751 d24744
                      omega
                    have d24752 : (x 5 1 && x 5 14).toNat = 0 := by
                      have r24753 := hand2 (x 5 1) (x 5 14)
                      have b24754 := hb (x 5 14)
                      have b24755 := hb (x 5 1 && x 5 14)
                      clear * - r24753 b24754 b24755 d24748
                      omega
                    have d24756 : (x 5 3 && x 5 14).toNat = 0 := by
                      have r24757 := hand2 (x 5 3) (x 5 14)
                      have b24758 := hb (x 5 14)
                      have b24759 := hb (x 5 3 && x 5 14)
                      clear * - r24757 b24758 b24759 d24748
                      omega
                    have d24760 : (x 5 6).toNat = 0 := by
                      have r24761 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                      have b24762 := hb (x 5 6)
                      have b24763 := hb (x 5 14)
                      clear * - r24761 b24762 b24763 d24748
                      omega
                    have d24764 : (x 5 6 && x 5 11).toNat = 0 := by
                      have r24765 := hand1 (x 5 6) (x 5 11)
                      have b24766 := hb (x 5 6)
                      have b24767 := hb (x 5 6 && x 5 11)
                      clear * - r24765 b24766 b24767 d24760
                      omega
                    have d24768 : (x 5 2).toNat = 0 := by
                      have r24769 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                      have b24770 := hb (x 5 2)
                      have b24771 := hb (x 5 14)
                      clear * - r24769 b24770 b24771 d24748
                      omega
                    have d24772 : (x 5 2 && x 5 12).toNat = 0 := by
                      have r24773 := hand1 (x 5 2) (x 5 12)
                      have b24774 := hb (x 5 2)
                      have b24775 := hb (x 5 2 && x 5 12)
                      clear * - r24773 b24774 b24775 d24768
                      omega
                    have d24776 : (x 5 2 && x 5 11).toNat = 0 := by
                      have r24777 := hand1 (x 5 2) (x 5 11)
                      have b24778 := hb (x 5 2)
                      have b24779 := hb (x 5 2 && x 5 11)
                      clear * - r24777 b24778 b24779 d24768
                      omega
                    have d24780 : (x 5 12).toNat = 0 := by
                      have r24781 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e24782 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                      have e24783 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                      have b24784 := hb (x 2 3)
                      have b24785 := hb (x 3 2)
                      have b24786 := hb (x 4 13)
                      have b24787 := hb (x 5 12)
                      clear * - r24781 e24782 e24783 b24784 b24785 b24786 b24787 d24739 d24729
                      omega
                    have d24788 : (x 5 3 && x 5 12).toNat = 0 := by
                      have r24789 := hand2 (x 5 3) (x 5 12)
                      have b24790 := hb (x 5 12)
                      have b24791 := hb (x 5 3 && x 5 12)
                      clear * - r24789 b24790 b24791 d24780
                      omega
                    have d24792 : (x 5 4).toNat = 0 := by
                      have r24793 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                      have b24794 := hb (x 5 4)
                      have b24795 := hb (x 5 12)
                      clear * - r24793 b24794 b24795 d24780
                      omega
                    have d24796 : (x 5 4 && x 5 13).toNat = 0 := by
                      have r24797 := hand1 (x 5 4) (x 5 13)
                      have b24798 := hb (x 5 4)
                      have b24799 := hb (x 5 4 && x 5 13)
                      clear * - r24797 b24798 b24799 d24792
                      omega
                    have d24800 : (x 5 4 && x 5 11).toNat = 0 := by
                      have r24801 := hand1 (x 5 4) (x 5 11)
                      have b24802 := hb (x 5 4)
                      have b24803 := hb (x 5 4 && x 5 11)
                      clear * - r24801 b24802 b24803 d24792
                      omega
                    have d24804 : (x 2 3).toNat = 0 := by
                      have r24805 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e24806 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                      have e24807 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                      have b24808 := hb (x 2 3)
                      have b24809 := hb (x 3 2)
                      have b24810 := hb (x 4 13)
                      have b24811 := hb (x 5 12)
                      clear * - r24805 e24806 e24807 b24808 b24809 b24810 b24811 d24780 d24739 d24729
                      omega
                    have d24812 : (x 2 3 && x 2 14).toNat = 0 := by
                      have r24813 := hand1 (x 2 3) (x 2 14)
                      have b24814 := hb (x 2 3)
                      have b24815 := hb (x 2 3 && x 2 14)
                      clear * - r24813 b24814 b24815 d24804
                      omega
                    cases h24816 : x 2 6
                    · have f24817 : (x 2 6).toNat = 0 := by rw [h24816]; rfl
                      have d24818 : (x 2 1 && x 2 6).toNat = 0 := by
                        have r24819 := hand2 (x 2 1) (x 2 6)
                        have b24820 := hb (x 2 6)
                        have b24821 := hb (x 2 1 && x 2 6)
                        clear * - r24819 b24820 b24821 f24817
                        omega
                      cases h24822 : x 2 7
                      · have f24823 : (x 2 7).toNat = 0 := by rw [h24822]; rfl
                        have d24824 : (x 2 7 && x 2 14).toNat = 0 := by
                          have r24825 := hand1 (x 2 7) (x 2 14)
                          have b24826 := hb (x 2 7)
                          have b24827 := hb (x 2 7 && x 2 14)
                          clear * - r24825 b24826 b24827 f24823
                          omega
                        have r24828 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24829 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24830 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24831 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24832 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24833 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24834 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e24835 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                        have e24836 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                        have e24837 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                        have e24838 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                        have e24839 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                        have e24840 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                        have r24841 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e24842 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e24843 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e24844 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e24845 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e24846 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e24847 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have r24848 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e24849 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                        have e24850 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                        have e24851 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                        have e24852 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                        have e24853 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                        have e24854 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                        have r24855 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e24856 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                        have e24857 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                        have r24858 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e24859 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                        have e24860 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                        have r24861 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e24862 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                        have e24863 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                        have r24864 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24865 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24866 : 1 ≤ (x 15 1).toNat + (x 14 1 && x 14 2).toNat + (x 13 2 && x 13 3).toNat + (x 12 3 && x 12 4).toNat + (x 11 4 && x 11 5).toNat + (x 10 5 && x 10 6).toNat + (x 9 6 && x 9 7).toNat + (x 8 7 && x 8 8).toNat + (x 7 8 && x 7 9).toNat + (x 6 9 && x 6 10).toNat + (x 5 10 && x 5 11).toNat + (x 4 11 && x 4 12).toNat + (x 3 12 && x 3 13).toNat + (x 2 13 && x 2 14).toNat + (x 1 14).toNat := by have q := hcov1 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24867 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e24868 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                        have e24869 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                        have r24870 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24871 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24872 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24873 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24874 : 1 ≤ (x (-6) 9).toNat + (x (-7) 1 && x (-7) 10).toNat + (x (-8) 2 && x (-8) 11).toNat + (x (-9) 3 && x (-9) 12).toNat + (x (-10) 4 && x (-10) 13).toNat + (x (-11) 5 && x (-11) 14).toNat + (x (-12) 6).toNat := by have q := hcov9 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24875 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24876 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24877 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24878 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24879 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24880 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r24881 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                        have r24882 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
                        have r24883 := hand2 (x 14 1) (x 14 2)
                        have r24884 := hand2 (x 13 2) (x 13 3)
                        have r24885 := hand2 (x 12 3) (x 12 4)
                        have r24886 := hand2 (x 8 7) (x 8 8)
                        have r24887 := hand2 (x 6 2) (x 6 6)
                        have r24888 := hand2 (x 5 3) (x 5 7)
                        have r24889 := hand1 (x (-5) 8) (x (-5) 13)
                        have r24890 := hand1 (x (-6) 9) (x (-6) 14)
                        have r24891 := hand1 (x (-6) 8) (x (-6) 14)
                        have r24892 := hand2 (x 7 1) (x 7 7)
                        have r24893 := hand2 (x 8 1) (x 8 8)
                        have r24894 := hand2 (x 7 2) (x 7 9)
                        have r24895 := hand2 (x 6 3) (x 6 10)
                        have r24896 := hand1 (x 4 5) (x 4 12)
                        have r24897 := hand1 (x (-7) 1) (x (-7) 10)
                        have r24898 := hand2 (x (-8) 2) (x (-8) 11)
                        have r24899 := hand2 (x (-9) 3) (x (-9) 12)
                        have r24900 := hand1 (x (-10) 4) (x (-10) 13)
                        have r24901 := hand1 (x (-11) 5) (x (-11) 14)
                        have r24902 := hand1 (x 11 3) (x 11 12)
                        have r24903 := hand1 (x 10 4) (x 10 13)
                        have r24904 := hand1 (x 9 5) (x 9 14)
                        have r24905 := hand2 (x (-8) 1) (x (-8) 11)
                        have r24906 := hand2 (x (-9) 2) (x (-9) 12)
                        have r24907 := hand2 (x (-10) 3) (x (-10) 13)
                        have r24908 := hand2 (x 4 1) (x 4 12)
                        have r24909 := hand1 (x 8 1) (x 8 12)
                        have r24910 := hand1 (x 7 2) (x 7 13)
                        have r24911 := hand1 (x 6 3) (x 6 14)
                        have r24912 := hand2 (x (-5) 1) (x (-5) 14)
                        have r24913 := hand1 (x 13 1) (x 13 14)
                        have b25019 := hb (x 14 1)
                        linarith only [r24828, r24829, r24830, r24831, r24832, r24833, r24834, e24835, e24836, e24837, e24838, e24839, e24840, r24841, e24842, e24843, e24844, e24845, e24846, e24847, r24848, e24849, e24850, e24851, e24852, e24853, e24854, r24855, e24856, e24857, r24858, e24859, e24860, r24861, e24862, e24863, r24864, r24865, r24866, r24867, e24868, e24869, r24870, r24871, r24872, r24873, r24874, r24875, r24876, r24877, r24878, r24879, r24880, r24881, r24882, r24883, r24884, r24885, r24886, r24887, r24888, r24889, r24890, r24891, r24892, r24893, r24894, r24895, r24896, r24897, r24898, r24899, r24900, r24901, r24902, r24903, r24904, r24905, r24906, r24907, r24908, r24909, r24910, r24911, r24912, r24913, b25019, d24620, g1, g2, g4, g5, g7, g8, g9, g12, g13, g16, g19, g20, g23, g24, g25, f24540, g28, g31, g32, f24708, f24817, f24823, g36, g37, d24529, d24721, g41, g42, g44, d23994, d24792, g46, d23966, g47, d23938, d23910, d24022, d24145, d24125, d24105, d24049, d24121, d24141, d24165, d23934, d23962, d23990, d24018, g48, g49, g54, g55, g56, g57, g58, g59, d24818, g62, g63, g64, g65, g66, g67, d24525, g80, g81, g82, g83, d24499, d24519, g84, g85, g86, g87, g88, g89, g90, d24800, d24725, d24824, d24081, d24101, d24616, d24733, d24812]
                      · have f25100 : (x 2 7).toNat = 1 := by rw [h24822]; rfl
                        have d25101 : (x 9 8).toNat = 0 := by
                          have r25102 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25103 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e25104 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e25105 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e25106 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e25107 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e25108 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b25109 := hb (x 2 7)
                          have b25110 := hb (x 3 6)
                          have b25111 := hb (x 4 5)
                          have b25112 := hb (x 5 4)
                          have b25113 := hb (x 6 11)
                          have b25114 := hb (x 7 10)
                          have b25115 := hb (x 8 9)
                          have b25116 := hb (x 9 8)
                          clear * - r25102 e25103 e25104 e25105 e25106 e25107 e25108 b25109 b25110 b25111 b25112 b25113 b25114 b25115 b25116 d24792 d24721 f25100
                          omega
                        have d25117 : (x 8 9).toNat = 0 := by
                          have r25118 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25119 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e25120 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e25121 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e25122 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e25123 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e25124 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b25125 := hb (x 2 7)
                          have b25126 := hb (x 3 6)
                          have b25127 := hb (x 4 5)
                          have b25128 := hb (x 5 4)
                          have b25129 := hb (x 6 11)
                          have b25130 := hb (x 7 10)
                          have b25131 := hb (x 8 9)
                          have b25132 := hb (x 9 8)
                          clear * - r25118 e25119 e25120 e25121 e25122 e25123 e25124 b25125 b25126 b25127 b25128 b25129 b25130 b25131 b25132 d25101 d24792 d24721 f25100
                          omega
                        have d25133 : (x 7 10).toNat = 0 := by
                          have r25134 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25135 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e25136 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e25137 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e25138 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e25139 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e25140 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b25141 := hb (x 2 7)
                          have b25142 := hb (x 3 6)
                          have b25143 := hb (x 4 5)
                          have b25144 := hb (x 5 4)
                          have b25145 := hb (x 6 11)
                          have b25146 := hb (x 7 10)
                          have b25147 := hb (x 8 9)
                          have b25148 := hb (x 9 8)
                          clear * - r25134 e25135 e25136 e25137 e25138 e25139 e25140 b25141 b25142 b25143 b25144 b25145 b25146 b25147 b25148 d25101 d25117 d24792 d24721 f25100
                          omega
                        have d25149 : (x 7 1 && x 7 10).toNat = 0 := by
                          have r25150 := hand2 (x 7 1) (x 7 10)
                          have b25151 := hb (x 7 10)
                          have b25152 := hb (x 7 1 && x 7 10)
                          clear * - r25150 b25151 b25152 d25133
                          omega
                        have d25153 : (x 6 11).toNat = 0 := by
                          have r25154 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25155 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e25156 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e25157 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e25158 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e25159 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e25160 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b25161 := hb (x 2 7)
                          have b25162 := hb (x 3 6)
                          have b25163 := hb (x 4 5)
                          have b25164 := hb (x 5 4)
                          have b25165 := hb (x 6 11)
                          have b25166 := hb (x 7 10)
                          have b25167 := hb (x 8 9)
                          have b25168 := hb (x 9 8)
                          clear * - r25154 e25155 e25156 e25157 e25158 e25159 e25160 b25161 b25162 b25163 b25164 b25165 b25166 b25167 b25168 d25101 d25117 d25133 d24792 d24721 f25100
                          omega
                        have d25169 : (x 6 1 && x 6 11).toNat = 0 := by
                          have r25170 := hand2 (x 6 1) (x 6 11)
                          have b25171 := hb (x 6 11)
                          have b25172 := hb (x 6 1 && x 6 11)
                          clear * - r25170 b25171 b25172 d25153
                          omega
                        have d25173 : (x 4 3 && x 4 13).toNat = 1 := by
                          have r25174 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b25175 := hb (x 2 5)
                          have b25176 := hb (x 7 10)
                          have b25177 := hb (x 6 1 && x 6 11)
                          have b25178 := hb (x 5 2 && x 5 12)
                          have b25179 := hb (x 4 3 && x 4 13)
                          have b25180 := hb (x 3 4 && x 3 14)
                          clear * - r25174 b25175 b25176 b25177 b25178 b25179 b25180 d25133 d25169 d24772 g111 g33
                          omega
                        have d25181 : (x 4 3).toNat = 1 := by
                          have r25182 := hand1 (x 4 3) (x 4 13)
                          have b25183 := hb (x 4 3)
                          have b25184 := hb (x 4 3 && x 4 13)
                          clear * - r25182 b25183 b25184 d25173
                          omega
                        have d25185 : (x 7 12).toNat = 0 := by
                          have r25186 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25187 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                          have e25188 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                          have b25189 := hb (x 4 3)
                          have b25190 := hb (x 5 2)
                          have b25191 := hb (x 6 13)
                          have b25192 := hb (x 7 12)
                          clear * - r25186 e25187 e25188 b25189 b25190 b25191 b25192 d24768 d25181
                          omega
                        have d25193 : (x 6 13).toNat = 0 := by
                          have r25194 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25195 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                          have e25196 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                          have b25197 := hb (x 4 3)
                          have b25198 := hb (x 5 2)
                          have b25199 := hb (x 6 13)
                          have b25200 := hb (x 7 12)
                          clear * - r25194 e25195 e25196 b25197 b25198 b25199 b25200 d25185 d24768 d25181
                          omega
                        have d25201 : (x 4 2).toNat = 1 := by
                          have r25202 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b25203 := hb (x 4 2)
                          have b25204 := hb (x 6 13)
                          have b25205 := hb (x 5 1 && x 5 14)
                          clear * - r25202 b25203 b25204 b25205 d25193 d24752
                          omega
                        have d25206 : (x 4 14).toNat = 1 := by
                          have r25207 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                          have b25208 := hb (x 4 2)
                          have b25209 := hb (x 4 14)
                          clear * - r25207 b25208 b25209 d25201
                          omega
                        have d25210 : (x 3 1).toNat = 0 := by
                          have r25211 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b25212 := hb (x 3 1)
                          have b25213 := hb (x 4 14)
                          clear * - r25211 b25212 b25213 d25206
                          omega
                        have d25214 : (x 3 13).toNat = 0 := by
                          have r25215 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                          have b25216 := hb (x 3 1)
                          have b25217 := hb (x 3 13)
                          clear * - r25215 b25216 b25217 d25210
                          omega
                        have d25218 : (x 3 7 && x 3 13).toNat = 0 := by
                          have r25219 := hand2 (x 3 7) (x 3 13)
                          have b25220 := hb (x 3 13)
                          have b25221 := hb (x 3 7 && x 3 13)
                          clear * - r25219 b25220 b25221 d25214
                          omega
                        have d25222 : (x 3 5).toNat = 0 := by
                          have r25223 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                          have b25224 := hb (x 3 5)
                          have b25225 := hb (x 3 13)
                          clear * - r25223 b25224 b25225 d25214
                          omega
                        have d25226 : (x 4 12).toNat = 1 := by
                          have r25227 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25228 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                          have e25229 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                          have b25230 := hb (x 1 3)
                          have b25231 := hb (x 2 2)
                          have b25232 := hb (x 3 13)
                          have b25233 := hb (x 4 12)
                          clear * - r25227 e25228 e25229 b25230 b25231 b25232 b25233 d25214 f24738 f24534
                          omega
                        have d25234 : (x 6 12).toNat = 0 := by
                          have r25235 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25236 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                          have e25237 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                          have b25238 := hb (x 3 3)
                          have b25239 := hb (x 4 2)
                          have b25240 := hb (x 5 13)
                          have b25241 := hb (x 6 12)
                          clear * - r25235 e25236 e25237 b25238 b25239 b25240 b25241 d25201
                          omega
                        have d25242 : (x 6 3 && x 6 12).toNat = 0 := by
                          have r25243 := hand2 (x 6 3) (x 6 12)
                          have b25244 := hb (x 6 12)
                          have b25245 := hb (x 6 3 && x 6 12)
                          clear * - r25243 b25244 b25245 d25234
                          omega
                        have d25246 : (x 6 4).toNat = 0 := by
                          have r25247 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                          have b25248 := hb (x 6 4)
                          have b25249 := hb (x 6 12)
                          clear * - r25247 b25248 b25249 d25234
                          omega
                        have d25250 : (x 6 4 && x 6 10).toNat = 0 := by
                          have r25251 := hand1 (x 6 4) (x 6 10)
                          have b25252 := hb (x 6 4)
                          have b25253 := hb (x 6 4 && x 6 10)
                          clear * - r25251 b25252 b25253 d25246
                          omega
                        have d25254 : (x 5 13).toNat = 0 := by
                          have r25255 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25256 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                          have e25257 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                          have b25258 := hb (x 3 3)
                          have b25259 := hb (x 4 2)
                          have b25260 := hb (x 5 13)
                          have b25261 := hb (x 6 12)
                          clear * - r25255 e25256 e25257 b25258 b25259 b25260 b25261 d25234 d25201
                          omega
                        have d25262 : (x 5 5).toNat = 0 := by
                          have r25263 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                          have b25264 := hb (x 5 5)
                          have b25265 := hb (x 5 13)
                          clear * - r25263 b25264 b25265 d25254
                          omega
                        have d25266 : (x 5 5 && x 5 11).toNat = 0 := by
                          have r25267 := hand1 (x 5 5) (x 5 11)
                          have b25268 := hb (x 5 5)
                          have b25269 := hb (x 5 5 && x 5 11)
                          clear * - r25267 b25268 b25269 d25262
                          omega
                        have d25270 : (x 6 2 && x 6 11).toNat = 0 := by
                          have r25271 := hand2 (x 6 2) (x 6 11)
                          have b25272 := hb (x 6 11)
                          have b25273 := hb (x 6 2 && x 6 11)
                          clear * - r25271 b25272 b25273 d25153
                          omega
                        have d25274 : (x 4 4 && x 4 13).toNat = 1 := by
                          have r25275 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b25276 := hb (x 2 6)
                          have b25277 := hb (x 8 9)
                          have b25278 := hb (x 7 1 && x 7 10)
                          have b25279 := hb (x 6 2 && x 6 11)
                          have b25280 := hb (x 5 3 && x 5 12)
                          have b25281 := hb (x 4 4 && x 4 13)
                          have b25282 := hb (x 3 5 && x 3 14)
                          clear * - r25275 b25276 b25277 b25278 b25279 b25280 b25281 b25282 d25117 d25149 d25270 d24788 d24717 f24817
                          omega
                        have d25283 : (x 4 4).toNat = 1 := by
                          have r25284 := hand1 (x 4 4) (x 4 13)
                          have b25285 := hb (x 4 4)
                          have b25286 := hb (x 4 4 && x 4 13)
                          clear * - r25284 b25285 b25286 d25274
                          omega
                        have d25287 : (x 4 5).toNat = 0 := by
                          have r25288 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25289 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e25290 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e25291 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e25292 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e25293 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e25294 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b25295 := hb (x 2 7)
                          have b25296 := hb (x 3 6)
                          have b25297 := hb (x 4 5)
                          have b25298 := hb (x 5 4)
                          have b25299 := hb (x 6 11)
                          have b25300 := hb (x 7 10)
                          have b25301 := hb (x 8 9)
                          have b25302 := hb (x 9 8)
                          clear * - r25288 e25289 e25290 e25291 e25292 e25293 e25294 b25295 b25296 b25297 b25298 b25299 b25300 b25301 b25302 d25101 d25117 d25133 d25153 d24792 d24721 f25100
                          omega
                        have d25303 : (x 4 5 && x 4 14).toNat = 0 := by
                          have r25304 := hand1 (x 4 5) (x 4 14)
                          have b25305 := hb (x 4 5)
                          have b25306 := hb (x 4 5 && x 4 14)
                          clear * - r25304 b25305 b25306 d25287
                          omega
                        have d25307 : (x 8 8).toNat = 0 := by
                          have r25308 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25309 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e25310 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e25311 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e25312 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e25313 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e25314 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have b25315 := hb (x 1 7)
                          have b25316 := hb (x 2 6)
                          have b25317 := hb (x 3 5)
                          have b25318 := hb (x 4 4)
                          have b25319 := hb (x 5 11)
                          have b25320 := hb (x 6 10)
                          have b25321 := hb (x 7 9)
                          have b25322 := hb (x 8 8)
                          clear * - r25308 e25309 e25310 e25311 e25312 e25313 e25314 b25315 b25316 b25317 b25318 b25319 b25320 b25321 b25322 d25283 d25222 f24817 f24540
                          omega
                        have d25323 : (x 8 2 && x 8 8).toNat = 0 := by
                          have r25324 := hand2 (x 8 2) (x 8 8)
                          have b25325 := hb (x 8 8)
                          have b25326 := hb (x 8 2 && x 8 8)
                          clear * - r25324 b25325 b25326 d25307
                          omega
                        have d25327 : (x 8 7 && x 8 8).toNat = 0 := by
                          have r25328 := hand2 (x 8 7) (x 8 8)
                          have b25329 := hb (x 8 8)
                          have b25330 := hb (x 8 7 && x 8 8)
                          clear * - r25328 b25329 b25330 d25307
                          omega
                        have d25331 : (x 7 9).toNat = 0 := by
                          have r25332 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25333 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e25334 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e25335 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e25336 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e25337 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e25338 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have b25339 := hb (x 1 7)
                          have b25340 := hb (x 2 6)
                          have b25341 := hb (x 3 5)
                          have b25342 := hb (x 4 4)
                          have b25343 := hb (x 5 11)
                          have b25344 := hb (x 6 10)
                          have b25345 := hb (x 7 9)
                          have b25346 := hb (x 8 8)
                          clear * - r25332 e25333 e25334 e25335 e25336 e25337 e25338 b25339 b25340 b25341 b25342 b25343 b25344 b25345 b25346 d25307 d25283 d25222 f24817 f24540
                          omega
                        have d25347 : (x 7 3 && x 7 9).toNat = 0 := by
                          have r25348 := hand2 (x 7 3) (x 7 9)
                          have b25349 := hb (x 7 9)
                          have b25350 := hb (x 7 3 && x 7 9)
                          clear * - r25348 b25349 b25350 d25331
                          omega
                        have d25351 : (x 6 10).toNat = 0 := by
                          have r25352 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25353 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e25354 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e25355 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e25356 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e25357 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e25358 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have b25359 := hb (x 1 7)
                          have b25360 := hb (x 2 6)
                          have b25361 := hb (x 3 5)
                          have b25362 := hb (x 4 4)
                          have b25363 := hb (x 5 11)
                          have b25364 := hb (x 6 10)
                          have b25365 := hb (x 7 9)
                          have b25366 := hb (x 8 8)
                          clear * - r25352 e25353 e25354 e25355 e25356 e25357 e25358 b25359 b25360 b25361 b25362 b25363 b25364 b25365 b25366 d25307 d25331 d25283 d25222 f24817 f24540
                          omega
                        have d25367 : (x 5 11).toNat = 0 := by
                          have r25368 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e25369 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e25370 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e25371 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e25372 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e25373 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e25374 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have b25375 := hb (x 1 7)
                          have b25376 := hb (x 2 6)
                          have b25377 := hb (x 3 5)
                          have b25378 := hb (x 4 4)
                          have b25379 := hb (x 5 11)
                          have b25380 := hb (x 6 10)
                          have b25381 := hb (x 7 9)
                          have b25382 := hb (x 8 8)
                          clear * - r25368 e25369 e25370 e25371 e25372 e25373 e25374 b25375 b25376 b25377 b25378 b25379 b25380 b25381 b25382 d25307 d25331 d25351 d25283 d25222 f24817 f24540
                          omega
                        have r25383 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r25384 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25385 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                        have e25386 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                        have e25387 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                        have e25388 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                        have e25389 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                        have e25390 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                        have r25391 : 1 ≤ (x 15 1).toNat + (x 14 1 && x 14 2).toNat + (x 13 2 && x 13 3).toNat + (x 12 3 && x 12 4).toNat + (x 11 4 && x 11 5).toNat + (x 10 5 && x 10 6).toNat + (x 9 6 && x 9 7).toNat + (x 8 7 && x 8 8).toNat + (x 7 8 && x 7 9).toNat + (x 6 9 && x 6 10).toNat + (x 5 10 && x 5 11).toNat + (x 4 11 && x 4 12).toNat + (x 3 12 && x 3 13).toNat + (x 2 13 && x 2 14).toNat + (x 1 14).toNat := by have q := hcov1 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r25392 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r25393 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r25394 := hand2 (x 14 1) (x 14 2)
                        have r25395 := hand2 (x 13 2) (x 13 3)
                        have r25396 := hand2 (x 12 3) (x 12 4)
                        have r25397 := hand2 (x 9 1) (x 9 7)
                        have r25398 := hand1 (x 4 6) (x 4 12)
                        have r25399 := hand2 (x 8 1) (x 8 10)
                        have r25400 := hand2 (x 7 2) (x 7 11)
                        linarith only [r25383, r25384, e25385, e25386, e25387, e25388, e25389, e25390, r25391, r25392, r25393, r25394, r25395, r25396, r25397, r25398, r25399, r25400, d24435, g32, d24529, d24721, d25214, d25226, d25262, d25367, d25246, d25351, d25331, d25307, d24121, d24141, d24165, d25327, d23934, d23962, d23990, d24018, g48, g49, d25323, d25347, d25250, d25266, d25218, d24431, d25242, d24796, d25303]
                    · have f25452 : (x 2 6).toNat = 1 := by rw [h24816]; rfl
                      have d25453 : (x 8 8).toNat = 0 := by
                        have r25454 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25455 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e25456 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e25457 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e25458 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e25459 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e25460 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b25461 := hb (x 1 7)
                        have b25462 := hb (x 2 6)
                        have b25463 := hb (x 3 5)
                        have b25464 := hb (x 4 4)
                        have b25465 := hb (x 5 11)
                        have b25466 := hb (x 6 10)
                        have b25467 := hb (x 7 9)
                        have b25468 := hb (x 8 8)
                        clear * - r25454 e25455 e25456 e25457 e25458 e25459 e25460 b25461 b25462 b25463 b25464 b25465 b25466 b25467 b25468 f25452 f24540
                        omega
                      have d25469 : (x 8 3 && x 8 8).toNat = 0 := by
                        have r25470 := hand2 (x 8 3) (x 8 8)
                        have b25471 := hb (x 8 8)
                        have b25472 := hb (x 8 3 && x 8 8)
                        clear * - r25470 b25471 b25472 d25453
                        omega
                      have d25473 : (x 8 7 && x 8 8).toNat = 0 := by
                        have r25474 := hand2 (x 8 7) (x 8 8)
                        have b25475 := hb (x 8 8)
                        have b25476 := hb (x 8 7 && x 8 8)
                        clear * - r25474 b25475 b25476 d25453
                        omega
                      have d25477 : (x 7 9).toNat = 0 := by
                        have r25478 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25479 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e25480 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e25481 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e25482 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e25483 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e25484 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b25485 := hb (x 1 7)
                        have b25486 := hb (x 2 6)
                        have b25487 := hb (x 3 5)
                        have b25488 := hb (x 4 4)
                        have b25489 := hb (x 5 11)
                        have b25490 := hb (x 6 10)
                        have b25491 := hb (x 7 9)
                        have b25492 := hb (x 8 8)
                        clear * - r25478 e25479 e25480 e25481 e25482 e25483 e25484 b25485 b25486 b25487 b25488 b25489 b25490 b25491 b25492 d25453 f25452 f24540
                        omega
                      have d25493 : (x 7 4 && x 7 9).toNat = 0 := by
                        have r25494 := hand2 (x 7 4) (x 7 9)
                        have b25495 := hb (x 7 9)
                        have b25496 := hb (x 7 4 && x 7 9)
                        clear * - r25494 b25495 b25496 d25477
                        omega
                      have d25497 : (x 6 10).toNat = 0 := by
                        have r25498 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25499 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e25500 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e25501 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e25502 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e25503 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e25504 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b25505 := hb (x 1 7)
                        have b25506 := hb (x 2 6)
                        have b25507 := hb (x 3 5)
                        have b25508 := hb (x 4 4)
                        have b25509 := hb (x 5 11)
                        have b25510 := hb (x 6 10)
                        have b25511 := hb (x 7 9)
                        have b25512 := hb (x 8 8)
                        clear * - r25498 e25499 e25500 e25501 e25502 e25503 e25504 b25505 b25506 b25507 b25508 b25509 b25510 b25511 b25512 d25453 d25477 f25452 f24540
                        omega
                      have d25513 : (x 6 1 && x 6 10).toNat = 0 := by
                        have r25514 := hand2 (x 6 1) (x 6 10)
                        have b25515 := hb (x 6 10)
                        have b25516 := hb (x 6 1 && x 6 10)
                        clear * - r25514 b25515 b25516 d25497
                        omega
                      have d25517 : (x 4 3 && x 4 12).toNat = 1 := by
                        have r25518 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b25519 := hb (x 1 6)
                        have b25520 := hb (x 7 9)
                        have b25521 := hb (x 6 1 && x 6 10)
                        have b25522 := hb (x 5 2 && x 5 11)
                        have b25523 := hb (x 4 3 && x 4 12)
                        have b25524 := hb (x 3 4 && x 3 13)
                        have b25525 := hb (x 2 5 && x 2 14)
                        clear * - r25518 b25519 b25520 b25521 b25522 b25523 b25524 b25525 d25477 d25513 d24776 g107 g108 g27
                        omega
                      have d25526 : (x 4 12).toNat = 1 := by
                        have r25527 := hand2 (x 4 3) (x 4 12)
                        have b25528 := hb (x 4 12)
                        have b25529 := hb (x 4 3 && x 4 12)
                        clear * - r25527 b25528 b25529 d25517
                        omega
                      have d25530 : (x 3 13).toNat = 0 := by
                        have r25531 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25532 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                        have e25533 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                        have b25534 := hb (x 1 3)
                        have b25535 := hb (x 2 2)
                        have b25536 := hb (x 3 13)
                        have b25537 := hb (x 4 12)
                        clear * - r25531 e25532 e25533 b25534 b25535 b25536 b25537 d25526 f24738 f24534
                        omega
                      have d25538 : (x 3 5).toNat = 0 := by
                        have r25539 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                        have b25540 := hb (x 3 5)
                        have b25541 := hb (x 3 13)
                        clear * - r25539 b25540 b25541 d25530
                        omega
                      have d25542 : (x 4 3).toNat = 1 := by
                        have r25543 := hand1 (x 4 3) (x 4 12)
                        have b25544 := hb (x 4 3)
                        have b25545 := hb (x 4 3 && x 4 12)
                        clear * - r25543 b25544 b25545 d25517
                        omega
                      have d25546 : (x 7 12).toNat = 0 := by
                        have r25547 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25548 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                        have e25549 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                        have b25550 := hb (x 4 3)
                        have b25551 := hb (x 5 2)
                        have b25552 := hb (x 6 13)
                        have b25553 := hb (x 7 12)
                        clear * - r25547 e25548 e25549 b25550 b25551 b25552 b25553 d24768 d25542
                        omega
                      have d25554 : (x 7 1 && x 7 12).toNat = 0 := by
                        have r25555 := hand2 (x 7 1) (x 7 12)
                        have b25556 := hb (x 7 12)
                        have b25557 := hb (x 7 1 && x 7 12)
                        clear * - r25555 b25556 b25557 d25546
                        omega
                      have d25558 : (x 7 4).toNat = 0 := by
                        have r25559 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                        have b25560 := hb (x 7 4)
                        have b25561 := hb (x 7 12)
                        clear * - r25559 b25560 b25561 d25546
                        omega
                      have d25562 : (x 6 13).toNat = 0 := by
                        have r25563 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25564 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                        have e25565 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                        have b25566 := hb (x 4 3)
                        have b25567 := hb (x 5 2)
                        have b25568 := hb (x 6 13)
                        have b25569 := hb (x 7 12)
                        clear * - r25563 e25564 e25565 b25566 b25567 b25568 b25569 d25546 d24768 d25542
                        omega
                      have d25570 : (x 6 2 && x 6 13).toNat = 0 := by
                        have r25571 := hand2 (x 6 2) (x 6 13)
                        have b25572 := hb (x 6 13)
                        have b25573 := hb (x 6 2 && x 6 13)
                        clear * - r25571 b25572 b25573 d25562
                        omega
                      have d25574 : (x 6 5).toNat = 0 := by
                        have r25575 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                        have b25576 := hb (x 6 5)
                        have b25577 := hb (x 6 13)
                        clear * - r25575 b25576 b25577 d25562
                        omega
                      have d25578 : (x 6 5 && x 6 10).toNat = 0 := by
                        have r25579 := hand1 (x 6 5) (x 6 10)
                        have b25580 := hb (x 6 5)
                        have b25581 := hb (x 6 5 && x 6 10)
                        clear * - r25579 b25580 b25581 d25574
                        omega
                      have d25582 : (x 5 11).toNat = 0 := by
                        have r25583 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25584 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e25585 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e25586 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e25587 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e25588 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e25589 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b25590 := hb (x 1 7)
                        have b25591 := hb (x 2 6)
                        have b25592 := hb (x 3 5)
                        have b25593 := hb (x 4 4)
                        have b25594 := hb (x 5 11)
                        have b25595 := hb (x 6 10)
                        have b25596 := hb (x 7 9)
                        have b25597 := hb (x 8 8)
                        clear * - r25583 e25584 e25585 e25586 e25587 e25588 e25589 b25590 b25591 b25592 b25593 b25594 b25595 b25596 b25597 d25453 d25477 d25497 d25538 f25452 f24540
                        omega
                      have d25598 : (x 4 4).toNat = 0 := by
                        have r25599 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25600 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e25601 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e25602 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e25603 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e25604 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e25605 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b25606 := hb (x 1 7)
                        have b25607 := hb (x 2 6)
                        have b25608 := hb (x 3 5)
                        have b25609 := hb (x 4 4)
                        have b25610 := hb (x 5 11)
                        have b25611 := hb (x 6 10)
                        have b25612 := hb (x 7 9)
                        have b25613 := hb (x 8 8)
                        clear * - r25599 e25600 e25601 e25602 e25603 e25604 e25605 b25606 b25607 b25608 b25609 b25610 b25611 b25612 b25613 d25453 d25477 d25497 d25582 d25538 f25452 f24540
                        omega
                      have d25614 : (x 8 11).toNat = 1 := by
                        have r25615 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b25616 := hb (x 4 4)
                        have b25617 := hb (x 8 11)
                        have b25618 := hb (x 7 1 && x 7 12)
                        have b25619 := hb (x 6 2 && x 6 13)
                        have b25620 := hb (x 5 3 && x 5 14)
                        clear * - r25615 b25616 b25617 b25618 b25619 b25620 d25554 d25570 d24756 d25598
                        omega
                      have d25621 : (x 8 3).toNat = 1 := by
                        have r25622 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                        have b25623 := hb (x 8 3)
                        have b25624 := hb (x 8 11)
                        clear * - r25622 b25623 b25624 d25614
                        omega
                      have d25625 : (x 11 12).toNat = 0 := by
                        have r25626 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25627 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                        have e25628 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                        have b25629 := hb (x 8 3)
                        have b25630 := hb (x 9 2)
                        have b25631 := hb (x 10 13)
                        have b25632 := hb (x 11 12)
                        clear * - r25626 e25627 e25628 b25629 b25630 b25631 b25632 d25621
                        omega
                      have d25633 : (x 10 13).toNat = 0 := by
                        have r25634 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25635 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                        have e25636 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                        have b25637 := hb (x 8 3)
                        have b25638 := hb (x 9 2)
                        have b25639 := hb (x 10 13)
                        have b25640 := hb (x 11 12)
                        clear * - r25634 e25635 e25636 b25637 b25638 b25639 b25640 d25625 d25621
                        omega
                      have d25641 : (x 9 2).toNat = 0 := by
                        have r25642 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25643 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                        have e25644 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                        have b25645 := hb (x 8 3)
                        have b25646 := hb (x 9 2)
                        have b25647 := hb (x 10 13)
                        have b25648 := hb (x 11 12)
                        clear * - r25642 e25643 e25644 b25645 b25646 b25647 b25648 d25625 d25633 d25621
                        omega
                      have d25649 : (x 9 2 && x 9 7).toNat = 0 := by
                        have r25650 := hand1 (x 9 2) (x 9 7)
                        have b25651 := hb (x 9 2)
                        have b25652 := hb (x 9 2 && x 9 7)
                        clear * - r25650 b25651 b25652 d25641
                        omega
                      have d25653 : (x 9 10).toNat = 0 := by
                        have r25654 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                        have b25655 := hb (x 9 2)
                        have b25656 := hb (x 9 10)
                        clear * - r25654 b25655 b25656 d25641
                        omega
                      have d25657 : (x 11 8).toNat = 0 := by
                        have r25658 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25659 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                        have e25660 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                        have e25661 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                        have e25662 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                        have e25663 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                        have e25664 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                        have b25665 := hb (x 4 7)
                        have b25666 := hb (x 5 6)
                        have b25667 := hb (x 6 5)
                        have b25668 := hb (x 7 4)
                        have b25669 := hb (x 8 11)
                        have b25670 := hb (x 9 10)
                        have b25671 := hb (x 10 9)
                        have b25672 := hb (x 11 8)
                        clear * - r25658 e25659 e25660 e25661 e25662 e25663 e25664 b25665 b25666 b25667 b25668 b25669 b25670 b25671 b25672 d25653 d25614 d25558 d25574 d24760
                        omega
                      have d25673 : (x 10 9).toNat = 0 := by
                        have r25674 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25675 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                        have e25676 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                        have e25677 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                        have e25678 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                        have e25679 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                        have e25680 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                        have b25681 := hb (x 4 7)
                        have b25682 := hb (x 5 6)
                        have b25683 := hb (x 6 5)
                        have b25684 := hb (x 7 4)
                        have b25685 := hb (x 8 11)
                        have b25686 := hb (x 9 10)
                        have b25687 := hb (x 10 9)
                        have b25688 := hb (x 11 8)
                        clear * - r25674 e25675 e25676 e25677 e25678 e25679 e25680 b25681 b25682 b25683 b25684 b25685 b25686 b25687 b25688 d25657 d25653 d25614 d25558 d25574 d24760
                        omega
                      have d25689 : (x 4 7).toNat = 0 := by
                        have r25690 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e25691 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                        have e25692 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                        have e25693 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                        have e25694 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                        have e25695 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                        have e25696 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                        have b25697 := hb (x 4 7)
                        have b25698 := hb (x 5 6)
                        have b25699 := hb (x 6 5)
                        have b25700 := hb (x 7 4)
                        have b25701 := hb (x 8 11)
                        have b25702 := hb (x 9 10)
                        have b25703 := hb (x 10 9)
                        have b25704 := hb (x 11 8)
                        clear * - r25690 e25691 e25692 e25693 e25694 e25695 e25696 b25697 b25698 b25699 b25700 b25701 b25702 b25703 b25704 d25657 d25673 d25653 d25614 d25558 d25574 d24760
                        omega
                      have d25705 : (x 4 7 && x 4 12).toNat = 0 := by
                        have r25706 := hand1 (x 4 7) (x 4 12)
                        have b25707 := hb (x 4 7)
                        have b25708 := hb (x 4 7 && x 4 12)
                        clear * - r25706 b25707 b25708 d25689
                        omega
                      have r25709 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r25710 : 1 ≤ (x 15 1).toNat + (x 14 1 && x 14 2).toNat + (x 13 2 && x 13 3).toNat + (x 12 3 && x 12 4).toNat + (x 11 4 && x 11 5).toNat + (x 10 5 && x 10 6).toNat + (x 9 6 && x 9 7).toNat + (x 8 7 && x 8 8).toNat + (x 7 8 && x 7 9).toNat + (x 6 9 && x 6 10).toNat + (x 5 10 && x 5 11).toNat + (x 4 11 && x 4 12).toNat + (x 3 12 && x 3 13).toNat + (x 2 13 && x 2 14).toNat + (x 1 14).toNat := by have q := hcov1 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r25711 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r25712 := hand2 (x 14 1) (x 14 2)
                      have r25713 := hand2 (x 13 2) (x 13 3)
                      have r25714 := hand2 (x 12 3) (x 12 4)
                      have r25715 := hand2 (x 10 1) (x 10 6)
                      linarith only [r25709, r25710, r25711, r25712, r25713, r25714, r25715, g29, g32, d24529, d25530, d25526, d25582, d25497, d25477, d25453, d24121, d24141, d24165, d25473, d23934, d23962, d23990, d24018, g48, g49, d25649, d25469, d25493, d25578, d24764, d25705, g78, g79]
                  · have f25754 : (x 2 2).toNat = 1 := by rw [h24737]; rfl
                    have d25755 : (x 4 12).toNat = 0 := by
                      have r25756 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e25757 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                      have e25758 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                      have b25759 := hb (x 1 3)
                      have b25760 := hb (x 2 2)
                      have b25761 := hb (x 3 13)
                      have b25762 := hb (x 4 12)
                      clear * - r25756 e25757 e25758 b25759 b25760 b25761 b25762 f25754 f24534
                      omega
                    have d25763 : (x 4 2 && x 4 12).toNat = 0 := by
                      have r25764 := hand2 (x 4 2) (x 4 12)
                      have b25765 := hb (x 4 12)
                      have b25766 := hb (x 4 2 && x 4 12)
                      clear * - r25764 b25765 b25766 d25755
                      omega
                    have d25767 : (x 4 4).toNat = 0 := by
                      have r25768 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                      have b25769 := hb (x 4 4)
                      have b25770 := hb (x 4 12)
                      clear * - r25768 b25769 b25770 d25755
                      omega
                    have d25771 : (x 3 13).toNat = 0 := by
                      have r25772 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e25773 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                      have e25774 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                      have b25775 := hb (x 1 3)
                      have b25776 := hb (x 2 2)
                      have b25777 := hb (x 3 13)
                      have b25778 := hb (x 4 12)
                      clear * - r25772 e25773 e25774 b25775 b25776 b25777 b25778 d25755 f25754 f24534
                      omega
                    have d25779 : (x 3 3 && x 3 13).toNat = 0 := by
                      have r25780 := hand2 (x 3 3) (x 3 13)
                      have b25781 := hb (x 3 13)
                      have b25782 := hb (x 3 3 && x 3 13)
                      clear * - r25780 b25781 b25782 d25771
                      omega
                    have d25783 : (x 3 5).toNat = 0 := by
                      have r25784 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                      have b25785 := hb (x 3 5)
                      have b25786 := hb (x 3 13)
                      clear * - r25784 b25785 b25786 d25771
                      omega
                    have r25787 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r25788 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r25789 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e25790 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e25791 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e25792 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e25793 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e25794 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e25795 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have r25796 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e25797 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                    have e25798 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                    have r25799 : 1 ≤ (x (-7) 10).toNat + (x (-8) 1 && x (-8) 11).toNat + (x (-9) 2 && x (-9) 12).toNat + (x (-10) 3 && x (-10) 13).toNat + (x (-11) 4 && x (-11) 14).toNat + (x (-12) 5).toNat := by have q := hcov10 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r25800 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r25801 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r25802 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
                    have r25803 := hand2 (x 2 2) (x 2 6)
                    have r25804 := hand1 (x (-4) 8) (x (-4) 12)
                    have r25805 := hand1 (x (-5) 9) (x (-5) 13)
                    have r25806 := hand2 (x (-8) 1) (x (-8) 11)
                    have r25807 := hand2 (x (-9) 2) (x (-9) 12)
                    have r25808 := hand2 (x (-10) 3) (x (-10) 13)
                    have r25809 := hand2 (x 5 1) (x 5 11)
                    have r25810 := hand2 (x (-10) 1) (x (-10) 14)
                    linarith only [r25787, r25788, r25789, e25790, e25791, e25792, e25793, e25794, e25795, r25796, e25797, e25798, r25799, r25800, r25801, r25802, r25803, r25804, r25805, r25806, r25807, r25808, r25809, r25810, d24620, g1, g2, g3, g5, g6, g9, g10, g16, g17, g24, f24534, g26, f24540, f24708, f25754, d25783, d25767, d24535, g50, g51, g52, g53, d24616, d25763, d25779, g110]
              · have f25867 : (x (-1) 14).toNat = 1 := by rw [h24640]; rfl
                have d25868 : (x (-2) 1).toNat = 0 := by
                  have r25869 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b25870 := hb (x (-2) 1)
                  have b25871 := hb (x (-1) 14)
                  clear * - r25869 b25870 b25871 f25867
                  omega
                have d25872 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                  have r25873 := hand1 (x (-2) 1) (x (-2) 14)
                  have b25874 := hb (x (-2) 1)
                  have b25875 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r25873 b25874 b25875 d25868
                  omega
                have d25876 : (x (-2) 13).toNat = 0 := by
                  have r25877 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                  have b25878 := hb (x (-2) 1)
                  have b25879 := hb (x (-2) 13)
                  clear * - r25877 b25878 b25879 d25868
                  omega
                have d25880 : (x (-3) 2).toNat = 1 := by
                  have r25881 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b25882 := hb (x (-3) 2)
                  have b25883 := hb (x (-1) 13)
                  have b25884 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r25881 b25882 b25883 b25884 g15 d25872
                  omega
                have d25885 : (x (-3) 14).toNat = 1 := by
                  have r25886 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                  have b25887 := hb (x (-3) 2)
                  have b25888 := hb (x (-3) 14)
                  clear * - r25886 b25887 b25888 d25880
                  omega
                have r25889 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25890 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25891 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25892 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e25893 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                have e25894 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                have e25895 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                have e25896 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                have e25897 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                have e25898 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                have r25899 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25900 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25901 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25902 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25903 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25904 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r25905 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have r25906 := hand2 (x 7 1) (x 7 6)
                have r25907 := hand2 (x 6 2) (x 6 7)
                have r25908 := hand2 (x 10 1) (x 10 6)
                have r25909 := hand2 (x 9 2) (x 9 7)
                have r25910 := hand2 (x 8 3) (x 8 8)
                have r25911 := hand2 (x 7 4) (x 7 9)
                have r25912 := hand1 (x 6 5) (x 6 10)
                have r25913 := hand1 (x 5 6) (x 5 11)
                have r25914 := hand1 (x 4 7) (x 4 12)
                have r25915 := hand2 (x 7 1) (x 7 7)
                have r25916 := hand2 (x 5 1) (x 5 11)
                have r25917 := hand2 (x 4 2) (x 4 12)
                have r25918 := hand2 (x 3 3) (x 3 13)
                have r25919 := hand1 (x 10 1) (x 10 12)
                have r25920 := hand1 (x 9 2) (x 9 13)
                have r25921 := hand1 (x 8 3) (x 8 14)
                have r25922 := hand1 (x 12 1) (x 12 12)
                have r25923 := hand1 (x 11 2) (x 11 13)
                have r25924 := hand1 (x 10 3) (x 10 14)
                linarith only [r25889, r25890, r25891, r25892, e25893, e25894, e25895, e25896, e25897, e25898, r25899, r25900, r25901, r25902, r25903, r25904, r25905, r25906, r25907, r25908, r25909, r25910, r25911, r25912, r25913, r25914, r25915, r25916, r25917, r25918, r25919, r25920, r25921, r25922, r25923, r25924, d25885, g7, d25876, g12, f24639, f25867, g21, g22, g26, g29, g30, g34, g35, d24529, g39, g40, g43, g45, g68, g69, g70, g71, g72, g73, g74, g78, g79, g84, g85, g86, g87, g88, g89, g90, g110]
            · have f26015 : (x (-1) 12).toNat = 1 := by rw [h24638]; rfl
              have d26016 : (x (-2) 13).toNat = 0 := by
                have r26017 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e26018 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e26019 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b26020 := hb (x (-4) 3)
                have b26021 := hb (x (-3) 2)
                have b26022 := hb (x (-2) 13)
                have b26023 := hb (x (-1) 12)
                clear * - r26017 e26018 e26019 b26020 b26021 b26022 b26023 f26015
                omega
              have d26024 : (x (-3) 2).toNat = 0 := by
                have r26025 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e26026 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e26027 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b26028 := hb (x (-4) 3)
                have b26029 := hb (x (-3) 2)
                have b26030 := hb (x (-2) 13)
                have b26031 := hb (x (-1) 12)
                clear * - r26025 e26026 e26027 b26028 b26029 b26030 b26031 f26015 d26016
                omega
              have d26032 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
                have r26033 := hand1 (x (-3) 2) (x (-3) 13)
                have b26034 := hb (x (-3) 2)
                have b26035 := hb (x (-3) 2 && x (-3) 13)
                clear * - r26033 b26034 b26035 d26024
                omega
              have d26036 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                have r26037 := hand1 (x (-3) 2) (x (-3) 12)
                have b26038 := hb (x (-3) 2)
                have b26039 := hb (x (-3) 2 && x (-3) 12)
                clear * - r26037 b26038 b26039 d26024
                omega
              have d26040 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                have r26041 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b26042 := hb (x (-3) 2)
                have b26043 := hb (x (-1) 13)
                have b26044 := hb (x (-2) 1 && x (-2) 14)
                clear * - r26041 b26042 b26043 b26044 g15 d26024
                omega
              have d26045 : (x (-2) 14).toNat = 1 := by
                have r26046 := hand2 (x (-2) 1) (x (-2) 14)
                have b26047 := hb (x (-2) 14)
                have b26048 := hb (x (-2) 1 && x (-2) 14)
                clear * - r26046 b26047 b26048 d26040
                omega
              have d26049 : (x (-3) 1).toNat = 0 := by
                have r26050 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b26051 := hb (x (-3) 1)
                have b26052 := hb (x (-2) 14)
                clear * - r26050 b26051 b26052 d26045
                omega
              have d26053 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                have r26054 := hand1 (x (-3) 1) (x (-3) 14)
                have b26055 := hb (x (-3) 1)
                have b26056 := hb (x (-3) 1 && x (-3) 14)
                clear * - r26054 b26055 b26056 d26049
                omega
              have d26057 : (x (-4) 2).toNat = 1 := by
                have r26058 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b26059 := hb (x (-4) 2)
                have b26060 := hb (x (-2) 13)
                have b26061 := hb (x (-3) 1 && x (-3) 14)
                clear * - r26058 b26059 b26060 b26061 d26016 d26053
                omega
              have d26062 : (x (-4) 14).toNat = 1 := by
                have r26063 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                have b26064 := hb (x (-4) 2)
                have b26065 := hb (x (-4) 14)
                clear * - r26063 b26064 b26065 d26057
                omega
              have d26066 : (x (-5) 1).toNat = 0 := by
                have r26067 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b26068 := hb (x (-5) 1)
                have b26069 := hb (x (-4) 14)
                clear * - r26067 b26068 b26069 d26062
                omega
              have d26070 : (x (-5) 13).toNat = 0 := by
                have r26071 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                have b26072 := hb (x (-5) 1)
                have b26073 := hb (x (-5) 13)
                clear * - r26071 b26072 b26073 d26066
                omega
              have d26074 : (x (-3) 13).toNat = 0 := by
                have r26075 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                have b26076 := hb (x (-3) 1)
                have b26077 := hb (x (-3) 13)
                clear * - r26075 b26076 b26077 d26049
                omega
              have d26078 : (x (-4) 3).toNat = 0 := by
                have r26079 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e26080 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e26081 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b26082 := hb (x (-4) 3)
                have b26083 := hb (x (-3) 2)
                have b26084 := hb (x (-2) 13)
                have b26085 := hb (x (-1) 12)
                clear * - r26079 e26080 e26081 b26082 b26083 b26084 b26085 f26015 d26016 d26024
                omega
              have d26086 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                have r26087 := hand1 (x (-4) 3) (x (-4) 14)
                have b26088 := hb (x (-4) 3)
                have b26089 := hb (x (-4) 3 && x (-4) 14)
                clear * - r26087 b26088 b26089 d26078
                omega
              have d26090 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                have r26091 := hand1 (x (-4) 3) (x (-4) 13)
                have b26092 := hb (x (-4) 3)
                have b26093 := hb (x (-4) 3 && x (-4) 13)
                clear * - r26091 b26092 b26093 d26078
                omega
              have d26094 : (x (-2) 12).toNat = 0 := by
                have r26095 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e26096 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e26097 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b26098 := hb (x (-5) 3)
                have b26099 := hb (x (-4) 2)
                have b26100 := hb (x (-3) 13)
                have b26101 := hb (x (-2) 12)
                clear * - r26095 e26096 e26097 b26098 b26099 b26100 b26101 d26074 d26057
                omega
              have d26102 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                have r26103 := hand2 (x (-2) 1) (x (-2) 12)
                have b26104 := hb (x (-2) 12)
                have b26105 := hb (x (-2) 1 && x (-2) 12)
                clear * - r26103 b26104 b26105 d26094
                omega
              have d26106 : (x (-5) 4).toNat = 1 := by
                have r26107 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b26108 := hb (x (-5) 4)
                have b26109 := hb (x (-1) 11)
                have b26110 := hb (x (-2) 1 && x (-2) 12)
                have b26111 := hb (x (-3) 2 && x (-3) 13)
                have b26112 := hb (x (-4) 3 && x (-4) 14)
                clear * - r26107 b26108 b26109 b26110 b26111 b26112 g14 d26102 d26032 d26086
                omega
              have d26113 : (x (-5) 12).toNat = 1 := by
                have r26114 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                have b26115 := hb (x (-5) 4)
                have b26116 := hb (x (-5) 12)
                clear * - r26114 b26115 b26116 d26106
                omega
              have d26117 : (x (-6) 13).toNat = 0 := by
                have r26118 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e26119 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e26120 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b26121 := hb (x (-8) 3)
                have b26122 := hb (x (-7) 2)
                have b26123 := hb (x (-6) 13)
                have b26124 := hb (x (-5) 12)
                clear * - r26118 e26119 e26120 b26121 b26122 b26123 b26124 d26113
                omega
              have d26125 : (x (-6) 5).toNat = 0 := by
                have r26126 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
                have b26127 := hb (x (-6) 5)
                have b26128 := hb (x (-6) 13)
                clear * - r26126 b26127 b26128 d26117
                omega
              have d26129 : (x (-7) 2).toNat = 0 := by
                have r26130 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e26131 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e26132 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b26133 := hb (x (-8) 3)
                have b26134 := hb (x (-7) 2)
                have b26135 := hb (x (-6) 13)
                have b26136 := hb (x (-5) 12)
                clear * - r26130 e26131 e26132 b26133 b26134 b26135 b26136 d26113 d26117
                omega
              have d26137 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                have r26138 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b26139 := hb (x (-7) 2)
                have b26140 := hb (x (-5) 13)
                have b26141 := hb (x (-6) 1 && x (-6) 14)
                clear * - r26138 b26139 b26140 b26141 d26070 d26129
                omega
              have d26142 : (x (-6) 1).toNat = 1 := by
                have r26143 := hand1 (x (-6) 1) (x (-6) 14)
                have b26144 := hb (x (-6) 1)
                have b26145 := hb (x (-6) 1 && x (-6) 14)
                clear * - r26143 b26144 b26145 d26137
                omega
              have d26146 : (x (-5) 14).toNat = 0 := by
                have r26147 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b26148 := hb (x (-6) 1)
                have b26149 := hb (x (-5) 14)
                clear * - r26147 b26148 b26149 d26142
                omega
              have d26150 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                have r26151 := hand2 (x (-5) 4) (x (-5) 14)
                have b26152 := hb (x (-5) 14)
                have b26153 := hb (x (-5) 4 && x (-5) 14)
                clear * - r26151 b26152 b26153 d26146
                omega
              have r26154 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26155 := hb (x (-6) 5)
              have b26156 := hb (x (-1) 10)
              have b26157 := hb (x (-2) 1 && x (-2) 11)
              have b26158 := hb (x (-3) 2 && x (-3) 12)
              have b26159 := hb (x (-4) 3 && x (-4) 13)
              have b26160 := hb (x (-5) 4 && x (-5) 14)
              linarith only [r26154, b26155, b26156, b26157, b26158, b26159, b26160, g13, g109, d26036, d26090, d26150, d26125]
          · have f26161 : (x (-1) 8).toNat = 1 := by rw [h24636]; rfl
            have d26162 : (x (-2) 9).toNat = 0 := by
              have r26163 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26164 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e26165 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e26166 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e26167 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e26168 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e26169 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b26170 := hb (x (-8) 7)
              have b26171 := hb (x (-7) 6)
              have b26172 := hb (x (-6) 5)
              have b26173 := hb (x (-5) 4)
              have b26174 := hb (x (-4) 11)
              have b26175 := hb (x (-3) 10)
              have b26176 := hb (x (-2) 9)
              have b26177 := hb (x (-1) 8)
              clear * - r26163 e26164 e26165 e26166 e26167 e26168 e26169 b26170 b26171 b26172 b26173 b26174 b26175 b26176 b26177 f26161
              omega
            have d26178 : (x (-3) 10).toNat = 0 := by
              have r26179 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26180 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e26181 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e26182 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e26183 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e26184 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e26185 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b26186 := hb (x (-8) 7)
              have b26187 := hb (x (-7) 6)
              have b26188 := hb (x (-6) 5)
              have b26189 := hb (x (-5) 4)
              have b26190 := hb (x (-4) 11)
              have b26191 := hb (x (-3) 10)
              have b26192 := hb (x (-2) 9)
              have b26193 := hb (x (-1) 8)
              clear * - r26179 e26180 e26181 e26182 e26183 e26184 e26185 b26186 b26187 b26188 b26189 b26190 b26191 b26192 b26193 f26161 d26162
              omega
            have d26194 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
              have r26195 := hand2 (x (-3) 1) (x (-3) 10)
              have b26196 := hb (x (-3) 10)
              have b26197 := hb (x (-3) 1 && x (-3) 10)
              clear * - r26195 b26196 b26197 d26178
              omega
            have d26198 : (x (-4) 11).toNat = 0 := by
              have r26199 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26200 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e26201 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e26202 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e26203 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e26204 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e26205 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b26206 := hb (x (-8) 7)
              have b26207 := hb (x (-7) 6)
              have b26208 := hb (x (-6) 5)
              have b26209 := hb (x (-5) 4)
              have b26210 := hb (x (-4) 11)
              have b26211 := hb (x (-3) 10)
              have b26212 := hb (x (-2) 9)
              have b26213 := hb (x (-1) 8)
              clear * - r26199 e26200 e26201 e26202 e26203 e26204 e26205 b26206 b26207 b26208 b26209 b26210 b26211 b26212 b26213 f26161 d26162 d26178
              omega
            have d26214 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
              have r26215 := hand2 (x (-4) 2) (x (-4) 11)
              have b26216 := hb (x (-4) 11)
              have b26217 := hb (x (-4) 2 && x (-4) 11)
              clear * - r26215 b26216 b26217 d26198
              omega
            have d26218 : (x (-5) 4).toNat = 0 := by
              have r26219 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26220 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e26221 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e26222 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e26223 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e26224 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e26225 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b26226 := hb (x (-8) 7)
              have b26227 := hb (x (-7) 6)
              have b26228 := hb (x (-6) 5)
              have b26229 := hb (x (-5) 4)
              have b26230 := hb (x (-4) 11)
              have b26231 := hb (x (-3) 10)
              have b26232 := hb (x (-2) 9)
              have b26233 := hb (x (-1) 8)
              clear * - r26219 e26220 e26221 e26222 e26223 e26224 e26225 b26226 b26227 b26228 b26229 b26230 b26231 b26232 b26233 f26161 d26162 d26178 d26198
              omega
            have d26234 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
              have r26235 := hand1 (x (-5) 4) (x (-5) 14)
              have b26236 := hb (x (-5) 4)
              have b26237 := hb (x (-5) 4 && x (-5) 14)
              clear * - r26235 b26236 b26237 d26218
              omega
            have d26238 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
              have r26239 := hand1 (x (-5) 4) (x (-5) 13)
              have b26240 := hb (x (-5) 4)
              have b26241 := hb (x (-5) 4 && x (-5) 13)
              clear * - r26239 b26240 b26241 d26218
              omega
            have d26242 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
              have r26243 := hand1 (x (-5) 4) (x (-5) 11)
              have b26244 := hb (x (-5) 4)
              have b26245 := hb (x (-5) 4 && x (-5) 11)
              clear * - r26243 b26244 b26245 d26218
              omega
            have d26246 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
              have r26247 := hand1 (x (-5) 4) (x (-5) 9)
              have b26248 := hb (x (-5) 4)
              have b26249 := hb (x (-5) 4 && x (-5) 9)
              clear * - r26247 b26248 b26249 d26218
              omega
            have d26250 : (x (-6) 5).toNat = 0 := by
              have r26251 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26252 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e26253 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e26254 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e26255 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e26256 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e26257 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b26258 := hb (x (-8) 7)
              have b26259 := hb (x (-7) 6)
              have b26260 := hb (x (-6) 5)
              have b26261 := hb (x (-5) 4)
              have b26262 := hb (x (-4) 11)
              have b26263 := hb (x (-3) 10)
              have b26264 := hb (x (-2) 9)
              have b26265 := hb (x (-1) 8)
              clear * - r26251 e26252 e26253 e26254 e26255 e26256 e26257 b26258 b26259 b26260 b26261 b26262 b26263 b26264 b26265 f26161 d26162 d26178 d26198 d26218
              omega
            have d26266 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
              have r26267 := hand1 (x (-6) 5) (x (-6) 14)
              have b26268 := hb (x (-6) 5)
              have b26269 := hb (x (-6) 5 && x (-6) 14)
              clear * - r26267 b26268 b26269 d26250
              omega
            have d26270 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
              have r26271 := hand1 (x (-6) 5) (x (-6) 12)
              have b26272 := hb (x (-6) 5)
              have b26273 := hb (x (-6) 5 && x (-6) 12)
              clear * - r26271 b26272 b26273 d26250
              omega
            have d26274 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
              have r26275 := hand1 (x (-6) 5) (x (-6) 10)
              have b26276 := hb (x (-6) 5)
              have b26277 := hb (x (-6) 5 && x (-6) 10)
              clear * - r26275 b26276 b26277 d26250
              omega
            have d26278 : (x (-7) 6).toNat = 0 := by
              have r26279 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26280 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e26281 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e26282 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e26283 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e26284 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e26285 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b26286 := hb (x (-8) 7)
              have b26287 := hb (x (-7) 6)
              have b26288 := hb (x (-6) 5)
              have b26289 := hb (x (-5) 4)
              have b26290 := hb (x (-4) 11)
              have b26291 := hb (x (-3) 10)
              have b26292 := hb (x (-2) 9)
              have b26293 := hb (x (-1) 8)
              clear * - r26279 e26280 e26281 e26282 e26283 e26284 e26285 b26286 b26287 b26288 b26289 b26290 b26291 b26292 b26293 f26161 d26162 d26178 d26198 d26218 d26250
              omega
            have d26294 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
              have r26295 := hand1 (x (-7) 6) (x (-7) 13)
              have b26296 := hb (x (-7) 6)
              have b26297 := hb (x (-7) 6 && x (-7) 13)
              clear * - r26295 b26296 b26297 d26278
              omega
            have d26298 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
              have r26299 := hand1 (x (-7) 6) (x (-7) 11)
              have b26300 := hb (x (-7) 6)
              have b26301 := hb (x (-7) 6 && x (-7) 11)
              clear * - r26299 b26300 b26301 d26278
              omega
            have d26302 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
              have r26303 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26304 := hb (x (-7) 6)
              have b26305 := hb (x (-1) 9)
              have b26306 := hb (x (-2) 1 && x (-2) 10)
              have b26307 := hb (x (-3) 2 && x (-3) 11)
              have b26308 := hb (x (-4) 3 && x (-4) 12)
              have b26309 := hb (x (-5) 4 && x (-5) 13)
              have b26310 := hb (x (-6) 5 && x (-6) 14)
              clear * - r26303 b26304 b26305 b26306 b26307 b26308 b26309 b26310 g12 g101 g102 d26238 d26266 d26278
              omega
            have d26311 : (x (-4) 12).toNat = 1 := by
              have r26312 := hand2 (x (-4) 3) (x (-4) 12)
              have b26313 := hb (x (-4) 12)
              have b26314 := hb (x (-4) 3 && x (-4) 12)
              clear * - r26312 b26313 b26314 d26302
              omega
            have d26315 : (x (-5) 13).toNat = 0 := by
              have r26316 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26317 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e26318 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b26319 := hb (x (-7) 3)
              have b26320 := hb (x (-6) 2)
              have b26321 := hb (x (-5) 13)
              have b26322 := hb (x (-4) 12)
              clear * - r26316 e26317 e26318 b26319 b26320 b26321 b26322 d26311
              omega
            have d26323 : (x (-6) 2).toNat = 0 := by
              have r26324 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26325 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e26326 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b26327 := hb (x (-7) 3)
              have b26328 := hb (x (-6) 2)
              have b26329 := hb (x (-5) 13)
              have b26330 := hb (x (-4) 12)
              clear * - r26324 e26325 e26326 b26327 b26328 b26329 b26330 d26311 d26315
              omega
            have d26331 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
              have r26332 := hand1 (x (-6) 2) (x (-6) 13)
              have b26333 := hb (x (-6) 2)
              have b26334 := hb (x (-6) 2 && x (-6) 13)
              clear * - r26332 b26333 b26334 d26323
              omega
            have d26335 : (x (-6) 10).toNat = 0 := by
              have r26336 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
              have b26337 := hb (x (-6) 2)
              have b26338 := hb (x (-6) 10)
              clear * - r26336 b26337 b26338 d26323
              omega
            have d26339 : (x (-7) 3).toNat = 0 := by
              have r26340 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26341 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e26342 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b26343 := hb (x (-7) 3)
              have b26344 := hb (x (-6) 2)
              have b26345 := hb (x (-5) 13)
              have b26346 := hb (x (-4) 12)
              clear * - r26340 e26341 e26342 b26343 b26344 b26345 b26346 d26311 d26315 d26323
              omega
            have d26347 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
              have r26348 := hand1 (x (-7) 3) (x (-7) 14)
              have b26349 := hb (x (-7) 3)
              have b26350 := hb (x (-7) 3 && x (-7) 14)
              clear * - r26348 b26349 b26350 d26339
              omega
            have d26351 : (x (-7) 11).toNat = 0 := by
              have r26352 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
              have b26353 := hb (x (-7) 3)
              have b26354 := hb (x (-7) 11)
              clear * - r26352 b26353 b26354 d26339
              omega
            have d26355 : (x (-4) 3).toNat = 1 := by
              have r26356 := hand1 (x (-4) 3) (x (-4) 12)
              have b26357 := hb (x (-4) 3)
              have b26358 := hb (x (-4) 3 && x (-4) 12)
              clear * - r26356 b26357 b26358 d26302
              omega
            have d26359 : (x (-1) 12).toNat = 0 := by
              have r26360 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26361 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e26362 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b26363 := hb (x (-4) 3)
              have b26364 := hb (x (-3) 2)
              have b26365 := hb (x (-2) 13)
              have b26366 := hb (x (-1) 12)
              clear * - r26360 e26361 e26362 b26363 b26364 b26365 b26366 d26355
              omega
            have d26367 : (x (-2) 13).toNat = 0 := by
              have r26368 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26369 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e26370 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b26371 := hb (x (-4) 3)
              have b26372 := hb (x (-3) 2)
              have b26373 := hb (x (-2) 13)
              have b26374 := hb (x (-1) 12)
              clear * - r26368 e26369 e26370 b26371 b26372 b26373 b26374 d26359 d26355
              omega
            have d26375 : (x (-3) 2).toNat = 0 := by
              have r26376 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26377 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e26378 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b26379 := hb (x (-4) 3)
              have b26380 := hb (x (-3) 2)
              have b26381 := hb (x (-2) 13)
              have b26382 := hb (x (-1) 12)
              clear * - r26376 e26377 e26378 b26379 b26380 b26381 b26382 d26359 d26367 d26355
              omega
            have d26383 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
              have r26384 := hand1 (x (-3) 2) (x (-3) 12)
              have b26385 := hb (x (-3) 2)
              have b26386 := hb (x (-3) 2 && x (-3) 12)
              clear * - r26384 b26385 b26386 d26375
              omega
            have d26387 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
              have r26388 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26389 := hb (x (-6) 5)
              have b26390 := hb (x (-1) 10)
              have b26391 := hb (x (-2) 1 && x (-2) 11)
              have b26392 := hb (x (-3) 2 && x (-3) 12)
              have b26393 := hb (x (-4) 3 && x (-4) 13)
              have b26394 := hb (x (-5) 4 && x (-5) 14)
              clear * - r26388 b26389 b26390 b26391 b26392 b26393 b26394 g13 g109 d26383 d26234 d26250
              omega
            have d26395 : (x (-4) 13).toNat = 1 := by
              have r26396 := hand2 (x (-4) 3) (x (-4) 13)
              have b26397 := hb (x (-4) 13)
              have b26398 := hb (x (-4) 3 && x (-4) 13)
              clear * - r26396 b26397 b26398 d26387
              omega
            have d26399 : (x (-4) 1).toNat = 1 := by
              have r26400 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
              have b26401 := hb (x (-4) 1)
              have b26402 := hb (x (-4) 13)
              clear * - r26400 b26401 b26402 d26395
              omega
            have d26403 : (x (-3) 14).toNat = 0 := by
              have r26404 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26405 := hb (x (-4) 1)
              have b26406 := hb (x (-3) 14)
              clear * - r26404 b26405 b26406 d26399
              omega
            have d26407 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
              have r26408 := hand2 (x (-3) 1) (x (-3) 14)
              have b26409 := hb (x (-3) 14)
              have b26410 := hb (x (-3) 1 && x (-3) 14)
              clear * - r26408 b26409 b26410 d26403
              omega
            have d26411 : (x (-4) 2).toNat = 1 := by
              have r26412 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26413 := hb (x (-4) 2)
              have b26414 := hb (x (-2) 13)
              have b26415 := hb (x (-3) 1 && x (-3) 14)
              clear * - r26412 b26413 b26414 b26415 d26367 d26407
              omega
            have d26416 : (x (-4) 14).toNat = 1 := by
              have r26417 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
              have b26418 := hb (x (-4) 2)
              have b26419 := hb (x (-4) 14)
              clear * - r26417 b26418 b26419 d26411
              omega
            have d26420 : (x (-5) 1).toNat = 0 := by
              have r26421 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26422 := hb (x (-5) 1)
              have b26423 := hb (x (-4) 14)
              clear * - r26421 b26422 b26423 d26416
              omega
            have d26424 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
              have r26425 := hand1 (x (-5) 1) (x (-5) 12)
              have b26426 := hb (x (-5) 1)
              have b26427 := hb (x (-5) 1 && x (-5) 12)
              clear * - r26425 b26426 b26427 d26420
              omega
            have d26428 : (x (-8) 4).toNat = 1 := by
              have r26429 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26430 := hb (x (-8) 4)
              have b26431 := hb (x (-4) 11)
              have b26432 := hb (x (-5) 1 && x (-5) 12)
              have b26433 := hb (x (-6) 2 && x (-6) 13)
              have b26434 := hb (x (-7) 3 && x (-7) 14)
              clear * - r26429 b26430 b26431 b26432 b26433 b26434 d26198 d26424 d26331 d26347
              omega
            have d26435 : (x (-8) 12).toNat = 1 := by
              have r26436 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
              have b26437 := hb (x (-8) 4)
              have b26438 := hb (x (-8) 12)
              clear * - r26436 b26437 b26438 d26428
              omega
            have d26439 : (x (-9) 13).toNat = 0 := by
              have r26440 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26441 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e26442 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b26443 := hb (x (-11) 3)
              have b26444 := hb (x (-10) 2)
              have b26445 := hb (x (-9) 13)
              have b26446 := hb (x (-8) 12)
              clear * - r26440 e26441 e26442 b26443 b26444 b26445 b26446 d26435
              omega
            have d26447 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
              have r26448 := hand2 (x (-9) 8) (x (-9) 13)
              have b26449 := hb (x (-9) 13)
              have b26450 := hb (x (-9) 8 && x (-9) 13)
              clear * - r26448 b26449 b26450 d26439
              omega
            have d26451 : (x (-9) 5).toNat = 0 := by
              have r26452 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
              have b26453 := hb (x (-9) 5)
              have b26454 := hb (x (-9) 13)
              clear * - r26452 b26453 b26454 d26439
              omega
            have d26455 : (x (-5) 9).toNat = 0 := by
              have r26456 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
              have b26457 := hb (x (-5) 1)
              have b26458 := hb (x (-5) 9)
              clear * - r26456 b26457 b26458 d26420
              omega
            have d26459 : (x (-2) 12).toNat = 0 := by
              have r26460 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26461 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e26462 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b26463 := hb (x (-5) 3)
              have b26464 := hb (x (-4) 2)
              have b26465 := hb (x (-3) 13)
              have b26466 := hb (x (-2) 12)
              clear * - r26460 e26461 e26462 b26463 b26464 b26465 b26466 d26411
              omega
            have d26467 : (x (-3) 13).toNat = 0 := by
              have r26468 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26469 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e26470 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b26471 := hb (x (-5) 3)
              have b26472 := hb (x (-4) 2)
              have b26473 := hb (x (-3) 13)
              have b26474 := hb (x (-2) 12)
              clear * - r26468 e26469 e26470 b26471 b26472 b26473 b26474 d26459 d26411
              omega
            have d26475 : (x (-5) 3).toNat = 0 := by
              have r26476 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26477 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e26478 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have b26479 := hb (x (-5) 3)
              have b26480 := hb (x (-4) 2)
              have b26481 := hb (x (-3) 13)
              have b26482 := hb (x (-2) 12)
              clear * - r26476 e26477 e26478 b26479 b26480 b26481 b26482 d26459 d26467 d26411
              omega
            have d26483 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
              have r26484 := hand1 (x (-5) 3) (x (-5) 12)
              have b26485 := hb (x (-5) 3)
              have b26486 := hb (x (-5) 3 && x (-5) 12)
              clear * - r26484 b26485 b26486 d26475
              omega
            have d26487 : (x (-5) 11).toNat = 0 := by
              have r26488 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
              have b26489 := hb (x (-5) 3)
              have b26490 := hb (x (-5) 11)
              clear * - r26488 b26489 b26490 d26475
              omega
            have d26491 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
              have r26492 := hand1 (x (-3) 2) (x (-3) 9)
              have b26493 := hb (x (-3) 2)
              have b26494 := hb (x (-3) 2 && x (-3) 9)
              clear * - r26492 b26493 b26494 d26375
              omega
            have d26495 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
              have r26496 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26497 := hb (x (-3) 2)
              have b26498 := hb (x (-1) 13)
              have b26499 := hb (x (-2) 1 && x (-2) 14)
              clear * - r26496 b26497 b26498 b26499 g15 d26375
              omega
            have d26500 : (x (-2) 14).toNat = 1 := by
              have r26501 := hand2 (x (-2) 1) (x (-2) 14)
              have b26502 := hb (x (-2) 14)
              have b26503 := hb (x (-2) 1 && x (-2) 14)
              clear * - r26501 b26502 b26503 d26495
              omega
            have d26504 : (x (-3) 1).toNat = 0 := by
              have r26505 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b26506 := hb (x (-3) 1)
              have b26507 := hb (x (-2) 14)
              clear * - r26505 b26506 b26507 d26500
              omega
            have d26508 : (x (-3) 9).toNat = 0 := by
              have r26509 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
              have b26510 := hb (x (-3) 1)
              have b26511 := hb (x (-3) 9)
              clear * - r26509 b26510 b26511 d26504
              omega
            have d26512 : (x (-2) 1).toNat = 1 := by
              have r26513 := hand1 (x (-2) 1) (x (-2) 14)
              have b26514 := hb (x (-2) 1)
              have b26515 := hb (x (-2) 1 && x (-2) 14)
              clear * - r26513 b26514 b26515 d26495
              omega
            have d26516 : (x (-8) 7).toNat = 0 := by
              have r26517 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26518 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e26519 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e26520 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e26521 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e26522 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e26523 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b26524 := hb (x (-8) 7)
              have b26525 := hb (x (-7) 6)
              have b26526 := hb (x (-6) 5)
              have b26527 := hb (x (-5) 4)
              have b26528 := hb (x (-4) 11)
              have b26529 := hb (x (-3) 10)
              have b26530 := hb (x (-2) 9)
              have b26531 := hb (x (-1) 8)
              clear * - r26517 e26518 e26519 e26520 e26521 e26522 e26523 b26524 b26525 b26526 b26527 b26528 b26529 b26530 b26531 f26161 d26162 d26178 d26198 d26218 d26250 d26278
              omega
            have d26532 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
              have r26533 := hand1 (x (-8) 7) (x (-8) 14)
              have b26534 := hb (x (-8) 7)
              have b26535 := hb (x (-8) 7 && x (-8) 14)
              clear * - r26533 b26534 b26535 d26516
              omega
            have d26536 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
              have r26537 := hand1 (x (-8) 7) (x (-8) 12)
              have b26538 := hb (x (-8) 7)
              have b26539 := hb (x (-8) 7 && x (-8) 12)
              clear * - r26537 b26538 b26539 d26516
              omega
            have d26540 : (x (-4) 8).toNat = 0 := by
              have r26541 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e26542 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
              have e26543 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
              have e26544 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
              have e26545 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
              have e26546 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
              have e26547 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
              have b26548 := hb (x (-11) 7)
              have b26549 := hb (x (-10) 6)
              have b26550 := hb (x (-9) 5)
              have b26551 := hb (x (-8) 4)
              have b26552 := hb (x (-7) 11)
              have b26553 := hb (x (-6) 10)
              have b26554 := hb (x (-5) 9)
              have b26555 := hb (x (-4) 8)
              clear * - r26541 e26542 e26543 e26544 e26545 e26546 e26547 b26548 b26549 b26550 b26551 b26552 b26553 b26554 b26555 d26455 d26335 d26351 d26428 d26451
              omega
            have d26556 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
              have r26557 := hand2 (x (-4) 3) (x (-4) 8)
              have b26558 := hb (x (-4) 8)
              have b26559 := hb (x (-4) 3 && x (-4) 8)
              clear * - r26557 b26558 b26559 d26540
              omega
            have r26560 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r26561 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26562 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e26563 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e26564 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e26565 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e26566 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e26567 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have r26568 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r26569 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r26570 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r26571 := hand1 (x (-10) 9) (x (-10) 14)
            have r26572 := hand2 (x (-2) 1) (x (-2) 8)
            have r26573 := hand2 (x (-4) 3) (x (-4) 10)
            have r26574 := hand1 (x (-6) 4) (x (-6) 13)
            have r26575 := hand1 (x (-7) 5) (x (-7) 14)
            linarith only [r26560, r26561, e26562, e26563, e26564, e26565, e26566, e26567, r26568, r26569, r26570, r26571, r26572, r26573, r26574, r26575, d26516, d26278, d26250, d26218, d26487, d26355, d26375, d26508, d26512, d26162, g10, g11, g60, g61, d26556, d26246, d26274, d26298, d26536, d26447, d26491, d26242, d26270, d26294, d26532, d26194, d26214, d26483]
        · have f26622 : (x 1 7).toNat = 1 := by rw [h24539]; rfl
          have d26623 : (x 8 8).toNat = 0 := by
            have r26624 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26625 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e26626 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e26627 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e26628 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e26629 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e26630 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b26631 := hb (x 1 7)
            have b26632 := hb (x 2 6)
            have b26633 := hb (x 3 5)
            have b26634 := hb (x 4 4)
            have b26635 := hb (x 5 11)
            have b26636 := hb (x 6 10)
            have b26637 := hb (x 7 9)
            have b26638 := hb (x 8 8)
            clear * - r26624 e26625 e26626 e26627 e26628 e26629 e26630 b26631 b26632 b26633 b26634 b26635 b26636 b26637 b26638 f26622
            omega
          have d26639 : (x 8 3 && x 8 8).toNat = 0 := by
            have r26640 := hand2 (x 8 3) (x 8 8)
            have b26641 := hb (x 8 8)
            have b26642 := hb (x 8 3 && x 8 8)
            clear * - r26640 b26641 b26642 d26623
            omega
          have d26643 : (x 8 7 && x 8 8).toNat = 0 := by
            have r26644 := hand2 (x 8 7) (x 8 8)
            have b26645 := hb (x 8 8)
            have b26646 := hb (x 8 7 && x 8 8)
            clear * - r26644 b26645 b26646 d26623
            omega
          have d26647 : (x 7 9).toNat = 0 := by
            have r26648 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26649 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e26650 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e26651 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e26652 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e26653 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e26654 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b26655 := hb (x 1 7)
            have b26656 := hb (x 2 6)
            have b26657 := hb (x 3 5)
            have b26658 := hb (x 4 4)
            have b26659 := hb (x 5 11)
            have b26660 := hb (x 6 10)
            have b26661 := hb (x 7 9)
            have b26662 := hb (x 8 8)
            clear * - r26648 e26649 e26650 e26651 e26652 e26653 e26654 b26655 b26656 b26657 b26658 b26659 b26660 b26661 b26662 d26623 f26622
            omega
          have d26663 : (x 7 4 && x 7 9).toNat = 0 := by
            have r26664 := hand2 (x 7 4) (x 7 9)
            have b26665 := hb (x 7 9)
            have b26666 := hb (x 7 4 && x 7 9)
            clear * - r26664 b26665 b26666 d26647
            omega
          have d26667 : (x 6 10).toNat = 0 := by
            have r26668 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26669 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e26670 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e26671 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e26672 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e26673 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e26674 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b26675 := hb (x 1 7)
            have b26676 := hb (x 2 6)
            have b26677 := hb (x 3 5)
            have b26678 := hb (x 4 4)
            have b26679 := hb (x 5 11)
            have b26680 := hb (x 6 10)
            have b26681 := hb (x 7 9)
            have b26682 := hb (x 8 8)
            clear * - r26668 e26669 e26670 e26671 e26672 e26673 e26674 b26675 b26676 b26677 b26678 b26679 b26680 b26681 b26682 d26623 d26647 f26622
            omega
          have d26683 : (x 6 1 && x 6 10).toNat = 0 := by
            have r26684 := hand2 (x 6 1) (x 6 10)
            have b26685 := hb (x 6 10)
            have b26686 := hb (x 6 1 && x 6 10)
            clear * - r26684 b26685 b26686 d26667
            omega
          have d26687 : (x 6 5 && x 6 10).toNat = 0 := by
            have r26688 := hand2 (x 6 5) (x 6 10)
            have b26689 := hb (x 6 10)
            have b26690 := hb (x 6 5 && x 6 10)
            clear * - r26688 b26689 b26690 d26667
            omega
          have d26691 : (x 5 11).toNat = 0 := by
            have r26692 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26693 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e26694 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e26695 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e26696 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e26697 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e26698 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b26699 := hb (x 1 7)
            have b26700 := hb (x 2 6)
            have b26701 := hb (x 3 5)
            have b26702 := hb (x 4 4)
            have b26703 := hb (x 5 11)
            have b26704 := hb (x 6 10)
            have b26705 := hb (x 7 9)
            have b26706 := hb (x 8 8)
            clear * - r26692 e26693 e26694 e26695 e26696 e26697 e26698 b26699 b26700 b26701 b26702 b26703 b26704 b26705 b26706 d26623 d26647 d26667 f26622
            omega
          have d26707 : (x 5 1 && x 5 11).toNat = 0 := by
            have r26708 := hand2 (x 5 1) (x 5 11)
            have b26709 := hb (x 5 11)
            have b26710 := hb (x 5 1 && x 5 11)
            clear * - r26708 b26709 b26710 d26691
            omega
          have d26711 : (x 5 2 && x 5 11).toNat = 0 := by
            have r26712 := hand2 (x 5 2) (x 5 11)
            have b26713 := hb (x 5 11)
            have b26714 := hb (x 5 2 && x 5 11)
            clear * - r26712 b26713 b26714 d26691
            omega
          have d26715 : (x 4 3 && x 4 12).toNat = 1 := by
            have r26716 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b26717 := hb (x 1 6)
            have b26718 := hb (x 7 9)
            have b26719 := hb (x 6 1 && x 6 10)
            have b26720 := hb (x 5 2 && x 5 11)
            have b26721 := hb (x 4 3 && x 4 12)
            have b26722 := hb (x 3 4 && x 3 13)
            have b26723 := hb (x 2 5 && x 2 14)
            clear * - r26716 b26717 b26718 b26719 b26720 b26721 b26722 b26723 d26647 d26683 d26711 g107 g108 g27
            omega
          have d26724 : (x 4 12).toNat = 1 := by
            have r26725 := hand2 (x 4 3) (x 4 12)
            have b26726 := hb (x 4 12)
            have b26727 := hb (x 4 3 && x 4 12)
            clear * - r26725 b26726 b26727 d26715
            omega
          have d26728 : (x 3 13).toNat = 0 := by
            have r26729 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26730 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e26731 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b26732 := hb (x 1 3)
            have b26733 := hb (x 2 2)
            have b26734 := hb (x 3 13)
            have b26735 := hb (x 4 12)
            clear * - r26729 e26730 e26731 b26732 b26733 b26734 b26735 d26724 f24534
            omega
          have d26736 : (x 3 3 && x 3 13).toNat = 0 := by
            have r26737 := hand2 (x 3 3) (x 3 13)
            have b26738 := hb (x 3 13)
            have b26739 := hb (x 3 3 && x 3 13)
            clear * - r26737 b26738 b26739 d26728
            omega
          have d26740 : (x 4 2 && x 4 12).toNat = 1 := by
            have r26741 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b26742 := hb (x 1 5)
            have b26743 := hb (x 6 10)
            have b26744 := hb (x 5 1 && x 5 11)
            have b26745 := hb (x 4 2 && x 4 12)
            have b26746 := hb (x 3 3 && x 3 13)
            have b26747 := hb (x 2 4 && x 2 14)
            clear * - r26741 b26742 b26743 b26744 b26745 b26746 b26747 d26667 d26707 d26736 g110 g26
            omega
          have d26748 : (x 4 2).toNat = 1 := by
            have r26749 := hand1 (x 4 2) (x 4 12)
            have b26750 := hb (x 4 2)
            have b26751 := hb (x 4 2 && x 4 12)
            clear * - r26749 b26750 b26751 d26740
            omega
          have d26752 : (x 6 12).toNat = 0 := by
            have r26753 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26754 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e26755 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b26756 := hb (x 3 3)
            have b26757 := hb (x 4 2)
            have b26758 := hb (x 5 13)
            have b26759 := hb (x 6 12)
            clear * - r26753 e26754 e26755 b26756 b26757 b26758 b26759 d26748
            omega
          have d26760 : (x 5 13).toNat = 0 := by
            have r26761 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26762 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e26763 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b26764 := hb (x 3 3)
            have b26765 := hb (x 4 2)
            have b26766 := hb (x 5 13)
            have b26767 := hb (x 6 12)
            clear * - r26761 e26762 e26763 b26764 b26765 b26766 b26767 d26752 d26748
            omega
          have d26768 : (x 3 5).toNat = 0 := by
            have r26769 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
            have b26770 := hb (x 3 5)
            have b26771 := hb (x 3 13)
            clear * - r26769 b26770 b26771 d26728
            omega
          have d26772 : (x 2 1 && x 2 14).toNat = 1 := by
            have r26773 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b26774 := hb (x 1 2)
            have b26775 := hb (x 3 13)
            have b26776 := hb (x 2 1 && x 2 14)
            clear * - r26773 b26774 b26775 b26776 d26728 g24
            omega
          have d26777 : (x 2 1).toNat = 1 := by
            have r26778 := hand1 (x 2 1) (x 2 14)
            have b26779 := hb (x 2 1)
            have b26780 := hb (x 2 1 && x 2 14)
            clear * - r26778 b26779 b26780 d26772
            omega
          have d26781 : (x 3 14).toNat = 0 := by
            have r26782 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b26783 := hb (x 2 1)
            have b26784 := hb (x 3 14)
            clear * - r26782 b26783 b26784 d26777
            omega
          have d26785 : (x 3 2).toNat = 0 := by
            have r26786 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b26787 := hb (x 3 2)
            have b26788 := hb (x 3 14)
            clear * - r26786 b26787 b26788 d26781
            omega
          have d26789 : (x 4 1 && x 4 14).toNat = 1 := by
            have r26790 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b26791 := hb (x 3 2)
            have b26792 := hb (x 5 13)
            have b26793 := hb (x 4 1 && x 4 14)
            clear * - r26790 b26791 b26792 b26793 d26760 d26785
            omega
          have d26794 : (x 4 1).toNat = 1 := by
            have r26795 := hand1 (x 4 1) (x 4 14)
            have b26796 := hb (x 4 1)
            have b26797 := hb (x 4 1 && x 4 14)
            clear * - r26795 b26796 b26797 d26789
            omega
          have d26798 : (x 5 14).toNat = 0 := by
            have r26799 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b26800 := hb (x 4 1)
            have b26801 := hb (x 5 14)
            clear * - r26799 b26800 b26801 d26794
            omega
          have d26802 : (x 5 3 && x 5 14).toNat = 0 := by
            have r26803 := hand2 (x 5 3) (x 5 14)
            have b26804 := hb (x 5 14)
            have b26805 := hb (x 5 3 && x 5 14)
            clear * - r26803 b26804 b26805 d26798
            omega
          have d26806 : (x 5 6).toNat = 0 := by
            have r26807 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
            have b26808 := hb (x 5 6)
            have b26809 := hb (x 5 14)
            clear * - r26807 b26808 b26809 d26798
            omega
          have d26810 : (x 5 6 && x 5 11).toNat = 0 := by
            have r26811 := hand1 (x 5 6) (x 5 11)
            have b26812 := hb (x 5 6)
            have b26813 := hb (x 5 6 && x 5 11)
            clear * - r26811 b26812 b26813 d26806
            omega
          have d26814 : (x 5 2).toNat = 0 := by
            have r26815 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b26816 := hb (x 5 2)
            have b26817 := hb (x 5 14)
            clear * - r26815 b26816 b26817 d26798
            omega
          have d26818 : (x 4 3).toNat = 1 := by
            have r26819 := hand1 (x 4 3) (x 4 12)
            have b26820 := hb (x 4 3)
            have b26821 := hb (x 4 3 && x 4 12)
            clear * - r26819 b26820 b26821 d26715
            omega
          have d26822 : (x 7 12).toNat = 0 := by
            have r26823 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26824 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e26825 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b26826 := hb (x 4 3)
            have b26827 := hb (x 5 2)
            have b26828 := hb (x 6 13)
            have b26829 := hb (x 7 12)
            clear * - r26823 e26824 e26825 b26826 b26827 b26828 b26829 d26814 d26818
            omega
          have d26830 : (x 7 1 && x 7 12).toNat = 0 := by
            have r26831 := hand2 (x 7 1) (x 7 12)
            have b26832 := hb (x 7 12)
            have b26833 := hb (x 7 1 && x 7 12)
            clear * - r26831 b26832 b26833 d26822
            omega
          have d26834 : (x 7 4).toNat = 0 := by
            have r26835 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
            have b26836 := hb (x 7 4)
            have b26837 := hb (x 7 12)
            clear * - r26835 b26836 b26837 d26822
            omega
          have d26838 : (x 6 13).toNat = 0 := by
            have r26839 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26840 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e26841 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b26842 := hb (x 4 3)
            have b26843 := hb (x 5 2)
            have b26844 := hb (x 6 13)
            have b26845 := hb (x 7 12)
            clear * - r26839 e26840 e26841 b26842 b26843 b26844 b26845 d26822 d26814 d26818
            omega
          have d26846 : (x 6 2 && x 6 13).toNat = 0 := by
            have r26847 := hand2 (x 6 2) (x 6 13)
            have b26848 := hb (x 6 13)
            have b26849 := hb (x 6 2 && x 6 13)
            clear * - r26847 b26848 b26849 d26838
            omega
          have d26850 : (x 6 5).toNat = 0 := by
            have r26851 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
            have b26852 := hb (x 6 5)
            have b26853 := hb (x 6 13)
            clear * - r26851 b26852 b26853 d26838
            omega
          have d26854 : (x 4 4).toNat = 0 := by
            have r26855 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26856 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e26857 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e26858 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e26859 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e26860 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e26861 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b26862 := hb (x 1 7)
            have b26863 := hb (x 2 6)
            have b26864 := hb (x 3 5)
            have b26865 := hb (x 4 4)
            have b26866 := hb (x 5 11)
            have b26867 := hb (x 6 10)
            have b26868 := hb (x 7 9)
            have b26869 := hb (x 8 8)
            clear * - r26855 e26856 e26857 e26858 e26859 e26860 e26861 b26862 b26863 b26864 b26865 b26866 b26867 b26868 b26869 d26623 d26647 d26667 d26691 d26768 f26622
            omega
          have d26870 : (x 8 11).toNat = 1 := by
            have r26871 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b26872 := hb (x 4 4)
            have b26873 := hb (x 8 11)
            have b26874 := hb (x 7 1 && x 7 12)
            have b26875 := hb (x 6 2 && x 6 13)
            have b26876 := hb (x 5 3 && x 5 14)
            clear * - r26871 b26872 b26873 b26874 b26875 b26876 d26830 d26846 d26802 d26854
            omega
          have d26877 : (x 8 3).toNat = 1 := by
            have r26878 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
            have b26879 := hb (x 8 3)
            have b26880 := hb (x 8 11)
            clear * - r26878 b26879 b26880 d26870
            omega
          have d26881 : (x 11 12).toNat = 0 := by
            have r26882 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26883 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e26884 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b26885 := hb (x 8 3)
            have b26886 := hb (x 9 2)
            have b26887 := hb (x 10 13)
            have b26888 := hb (x 11 12)
            clear * - r26882 e26883 e26884 b26885 b26886 b26887 b26888 d26877
            omega
          have d26889 : (x 10 13).toNat = 0 := by
            have r26890 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26891 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e26892 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b26893 := hb (x 8 3)
            have b26894 := hb (x 9 2)
            have b26895 := hb (x 10 13)
            have b26896 := hb (x 11 12)
            clear * - r26890 e26891 e26892 b26893 b26894 b26895 b26896 d26881 d26877
            omega
          have d26897 : (x 9 2).toNat = 0 := by
            have r26898 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26899 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e26900 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b26901 := hb (x 8 3)
            have b26902 := hb (x 9 2)
            have b26903 := hb (x 10 13)
            have b26904 := hb (x 11 12)
            clear * - r26898 e26899 e26900 b26901 b26902 b26903 b26904 d26881 d26889 d26877
            omega
          have d26905 : (x 9 2 && x 9 7).toNat = 0 := by
            have r26906 := hand1 (x 9 2) (x 9 7)
            have b26907 := hb (x 9 2)
            have b26908 := hb (x 9 2 && x 9 7)
            clear * - r26906 b26907 b26908 d26897
            omega
          have d26909 : (x 9 10).toNat = 0 := by
            have r26910 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
            have b26911 := hb (x 9 2)
            have b26912 := hb (x 9 10)
            clear * - r26910 b26911 b26912 d26897
            omega
          have d26913 : (x 11 8).toNat = 0 := by
            have r26914 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26915 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e26916 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e26917 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e26918 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e26919 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e26920 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b26921 := hb (x 4 7)
            have b26922 := hb (x 5 6)
            have b26923 := hb (x 6 5)
            have b26924 := hb (x 7 4)
            have b26925 := hb (x 8 11)
            have b26926 := hb (x 9 10)
            have b26927 := hb (x 10 9)
            have b26928 := hb (x 11 8)
            clear * - r26914 e26915 e26916 e26917 e26918 e26919 e26920 b26921 b26922 b26923 b26924 b26925 b26926 b26927 b26928 d26909 d26870 d26834 d26850 d26806
            omega
          have d26929 : (x 10 9).toNat = 0 := by
            have r26930 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26931 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e26932 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e26933 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e26934 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e26935 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e26936 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b26937 := hb (x 4 7)
            have b26938 := hb (x 5 6)
            have b26939 := hb (x 6 5)
            have b26940 := hb (x 7 4)
            have b26941 := hb (x 8 11)
            have b26942 := hb (x 9 10)
            have b26943 := hb (x 10 9)
            have b26944 := hb (x 11 8)
            clear * - r26930 e26931 e26932 e26933 e26934 e26935 e26936 b26937 b26938 b26939 b26940 b26941 b26942 b26943 b26944 d26913 d26909 d26870 d26834 d26850 d26806
            omega
          have d26945 : (x 4 7).toNat = 0 := by
            have r26946 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e26947 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e26948 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e26949 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e26950 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e26951 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e26952 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b26953 := hb (x 4 7)
            have b26954 := hb (x 5 6)
            have b26955 := hb (x 6 5)
            have b26956 := hb (x 7 4)
            have b26957 := hb (x 8 11)
            have b26958 := hb (x 9 10)
            have b26959 := hb (x 10 9)
            have b26960 := hb (x 11 8)
            clear * - r26946 e26947 e26948 e26949 e26950 e26951 e26952 b26953 b26954 b26955 b26956 b26957 b26958 b26959 b26960 d26913 d26929 d26909 d26870 d26834 d26850 d26806
            omega
          have d26961 : (x 4 7 && x 4 12).toNat = 0 := by
            have r26962 := hand1 (x 4 7) (x 4 12)
            have b26963 := hb (x 4 7)
            have b26964 := hb (x 4 7 && x 4 12)
            clear * - r26962 b26963 b26964 d26945
            omega
          have r26965 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r26966 : 1 ≤ (x 15 1).toNat + (x 14 1 && x 14 2).toNat + (x 13 2 && x 13 3).toNat + (x 12 3 && x 12 4).toNat + (x 11 4 && x 11 5).toNat + (x 10 5 && x 10 6).toNat + (x 9 6 && x 9 7).toNat + (x 8 7 && x 8 8).toNat + (x 7 8 && x 7 9).toNat + (x 6 9 && x 6 10).toNat + (x 5 10 && x 5 11).toNat + (x 4 11 && x 4 12).toNat + (x 3 12 && x 3 13).toNat + (x 2 13 && x 2 14).toNat + (x 1 14).toNat := by have q := hcov1 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r26967 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r26968 := hand2 (x 14 1) (x 14 2)
          have r26969 := hand2 (x 13 2) (x 13 3)
          have r26970 := hand2 (x 12 3) (x 12 4)
          have r26971 := hand2 (x 10 1) (x 10 6)
          linarith only [r26965, r26966, r26967, r26968, r26969, r26970, r26971, g29, g32, d24529, d26728, d26724, d26691, d26667, d26647, d26623, d24121, d24141, d24165, d26643, d23934, d23962, d23990, d24018, g48, g49, d26905, d26639, d26663, d26687, d26810, d26961, g78, g79]
      · have f27010 : (x 1 3).toNat = 1 := by rw [h24533]; rfl
        have d27011 : (x 4 12).toNat = 0 := by
          have r27012 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27013 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e27014 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b27015 := hb (x 1 3)
          have b27016 := hb (x 2 2)
          have b27017 := hb (x 3 13)
          have b27018 := hb (x 4 12)
          clear * - r27012 e27013 e27014 b27015 b27016 b27017 b27018 f27010
          omega
        have d27019 : (x 4 1 && x 4 12).toNat = 0 := by
          have r27020 := hand2 (x 4 1) (x 4 12)
          have b27021 := hb (x 4 12)
          have b27022 := hb (x 4 1 && x 4 12)
          clear * - r27020 b27021 b27022 d27011
          omega
        have d27023 : (x 4 4).toNat = 0 := by
          have r27024 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b27025 := hb (x 4 4)
          have b27026 := hb (x 4 12)
          clear * - r27024 b27025 b27026 d27011
          omega
        have d27027 : (x 3 13).toNat = 0 := by
          have r27028 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27029 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e27030 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b27031 := hb (x 1 3)
          have b27032 := hb (x 2 2)
          have b27033 := hb (x 3 13)
          have b27034 := hb (x 4 12)
          clear * - r27028 e27029 e27030 b27031 b27032 b27033 b27034 d27011 f27010
          omega
        have d27035 : (x 3 2 && x 3 13).toNat = 0 := by
          have r27036 := hand2 (x 3 2) (x 3 13)
          have b27037 := hb (x 3 13)
          have b27038 := hb (x 3 2 && x 3 13)
          clear * - r27036 b27037 b27038 d27027
          omega
        have d27039 : (x 2 1 && x 2 14).toNat = 1 := by
          have r27040 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27041 := hb (x 1 2)
          have b27042 := hb (x 3 13)
          have b27043 := hb (x 2 1 && x 2 14)
          clear * - r27040 b27041 b27042 b27043 d27027 g24
          omega
        have d27044 : (x 2 1).toNat = 1 := by
          have r27045 := hand1 (x 2 1) (x 2 14)
          have b27046 := hb (x 2 1)
          have b27047 := hb (x 2 1 && x 2 14)
          clear * - r27045 b27046 b27047 d27039
          omega
        have d27048 : (x 3 14).toNat = 0 := by
          have r27049 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27050 := hb (x 2 1)
          have b27051 := hb (x 3 14)
          clear * - r27049 b27050 b27051 d27044
          omega
        have d27052 : (x 3 1 && x 3 14).toNat = 0 := by
          have r27053 := hand2 (x 3 1) (x 3 14)
          have b27054 := hb (x 3 14)
          have b27055 := hb (x 3 1 && x 3 14)
          clear * - r27053 b27054 b27055 d27048
          omega
        have d27056 : (x 3 2).toNat = 0 := by
          have r27057 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
          have b27058 := hb (x 3 2)
          have b27059 := hb (x 3 14)
          clear * - r27057 b27058 b27059 d27048
          omega
        have d27060 : (x 2 2).toNat = 0 := by
          have r27061 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27062 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e27063 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b27064 := hb (x 1 3)
          have b27065 := hb (x 2 2)
          have b27066 := hb (x 3 13)
          have b27067 := hb (x 4 12)
          clear * - r27061 e27062 e27063 b27064 b27065 b27066 b27067 d27011 d27027 f27010
          omega
        have d27068 : (x 4 13).toNat = 1 := by
          have r27069 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27070 := hb (x 2 2)
          have b27071 := hb (x 4 13)
          have b27072 := hb (x 3 1 && x 3 14)
          clear * - r27069 b27070 b27071 b27072 d27052 d27060
          omega
        have d27073 : (x 4 1).toNat = 1 := by
          have r27074 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b27075 := hb (x 4 1)
          have b27076 := hb (x 4 13)
          clear * - r27074 b27075 b27076 d27068
          omega
        have d27077 : (x 5 14).toNat = 0 := by
          have r27078 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27079 := hb (x 4 1)
          have b27080 := hb (x 5 14)
          clear * - r27078 b27079 b27080 d27073
          omega
        have d27081 : (x 5 3 && x 5 14).toNat = 0 := by
          have r27082 := hand2 (x 5 3) (x 5 14)
          have b27083 := hb (x 5 14)
          have b27084 := hb (x 5 3 && x 5 14)
          clear * - r27082 b27083 b27084 d27077
          omega
        have d27085 : (x 5 2).toNat = 0 := by
          have r27086 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b27087 := hb (x 5 2)
          have b27088 := hb (x 5 14)
          clear * - r27086 b27087 b27088 d27077
          omega
        have d27089 : (x 5 12).toNat = 0 := by
          have r27090 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27091 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e27092 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b27093 := hb (x 2 3)
          have b27094 := hb (x 3 2)
          have b27095 := hb (x 4 13)
          have b27096 := hb (x 5 12)
          clear * - r27090 e27091 e27092 b27093 b27094 b27095 b27096 d27068 d27056
          omega
        have d27097 : (x 5 4).toNat = 0 := by
          have r27098 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b27099 := hb (x 5 4)
          have b27100 := hb (x 5 12)
          clear * - r27098 b27099 b27100 d27089
          omega
        have d27101 : (x 2 3).toNat = 0 := by
          have r27102 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27103 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e27104 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b27105 := hb (x 2 3)
          have b27106 := hb (x 3 2)
          have b27107 := hb (x 4 13)
          have b27108 := hb (x 5 12)
          clear * - r27102 e27103 e27104 b27105 b27106 b27107 b27108 d27089 d27068 d27056
          omega
        have d27109 : (x 2 3 && x 2 14).toNat = 0 := by
          have r27110 := hand1 (x 2 3) (x 2 14)
          have b27111 := hb (x 2 3)
          have b27112 := hb (x 2 3 && x 2 14)
          clear * - r27110 b27111 b27112 d27101
          omega
        have d27113 : (x 5 11).toNat = 1 := by
          have r27114 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27115 := hb (x 1 4)
          have b27116 := hb (x 5 11)
          have b27117 := hb (x 4 1 && x 4 12)
          have b27118 := hb (x 3 2 && x 3 13)
          have b27119 := hb (x 2 3 && x 2 14)
          clear * - r27114 b27115 b27116 b27117 b27118 b27119 d27019 d27035 d27109 g25
          omega
        have d27120 : (x 5 3).toNat = 1 := by
          have r27121 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b27122 := hb (x 5 3)
          have b27123 := hb (x 5 11)
          clear * - r27121 b27122 b27123 d27113
          omega
        have d27124 : (x 8 12).toNat = 0 := by
          have r27125 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27126 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e27127 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b27128 := hb (x 5 3)
          have b27129 := hb (x 6 2)
          have b27130 := hb (x 7 13)
          have b27131 := hb (x 8 12)
          clear * - r27125 e27126 e27127 b27128 b27129 b27130 b27131 d27120
          omega
        have d27132 : (x 8 1 && x 8 12).toNat = 0 := by
          have r27133 := hand2 (x 8 1) (x 8 12)
          have b27134 := hb (x 8 12)
          have b27135 := hb (x 8 1 && x 8 12)
          clear * - r27133 b27134 b27135 d27124
          omega
        have d27136 : (x 8 4).toNat = 0 := by
          have r27137 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
          have b27138 := hb (x 8 4)
          have b27139 := hb (x 8 12)
          clear * - r27137 b27138 b27139 d27124
          omega
        have d27140 : (x 7 13).toNat = 0 := by
          have r27141 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27142 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e27143 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b27144 := hb (x 5 3)
          have b27145 := hb (x 6 2)
          have b27146 := hb (x 7 13)
          have b27147 := hb (x 8 12)
          clear * - r27141 e27142 e27143 b27144 b27145 b27146 b27147 d27124 d27120
          omega
        have d27148 : (x 7 2 && x 7 13).toNat = 0 := by
          have r27149 := hand2 (x 7 2) (x 7 13)
          have b27150 := hb (x 7 13)
          have b27151 := hb (x 7 2 && x 7 13)
          clear * - r27149 b27150 b27151 d27140
          omega
        have d27152 : (x 6 1 && x 6 14).toNat = 1 := by
          have r27153 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27154 := hb (x 5 2)
          have b27155 := hb (x 7 13)
          have b27156 := hb (x 6 1 && x 6 14)
          clear * - r27153 b27154 b27155 b27156 d27140 d27085
          omega
        have d27157 : (x 6 1).toNat = 1 := by
          have r27158 := hand1 (x 6 1) (x 6 14)
          have b27159 := hb (x 6 1)
          have b27160 := hb (x 6 1 && x 6 14)
          clear * - r27158 b27159 b27160 d27152
          omega
        have d27161 : (x 7 14).toNat = 0 := by
          have r27162 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27163 := hb (x 6 1)
          have b27164 := hb (x 7 14)
          clear * - r27162 b27163 b27164 d27157
          omega
        have d27165 : (x 7 1 && x 7 14).toNat = 0 := by
          have r27166 := hand2 (x 7 1) (x 7 14)
          have b27167 := hb (x 7 14)
          have b27168 := hb (x 7 1 && x 7 14)
          clear * - r27166 b27167 b27168 d27161
          omega
        have d27169 : (x 7 2).toNat = 0 := by
          have r27170 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b27171 := hb (x 7 2)
          have b27172 := hb (x 7 14)
          clear * - r27170 b27171 b27172 d27161
          omega
        have d27173 : (x 6 2).toNat = 0 := by
          have r27174 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27175 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e27176 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b27177 := hb (x 5 3)
          have b27178 := hb (x 6 2)
          have b27179 := hb (x 7 13)
          have b27180 := hb (x 8 12)
          clear * - r27174 e27175 e27176 b27177 b27178 b27179 b27180 d27124 d27140 d27120
          omega
        have d27181 : (x 6 2 && x 6 13).toNat = 0 := by
          have r27182 := hand1 (x 6 2) (x 6 13)
          have b27183 := hb (x 6 2)
          have b27184 := hb (x 6 2 && x 6 13)
          clear * - r27182 b27183 b27184 d27173
          omega
        have d27185 : (x 8 13).toNat = 1 := by
          have r27186 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27187 := hb (x 6 2)
          have b27188 := hb (x 8 13)
          have b27189 := hb (x 7 1 && x 7 14)
          clear * - r27186 b27187 b27188 b27189 d27165 d27173
          omega
        have d27190 : (x 8 1).toNat = 1 := by
          have r27191 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b27192 := hb (x 8 1)
          have b27193 := hb (x 8 13)
          clear * - r27191 b27192 b27193 d27185
          omega
        have d27194 : (x 9 14).toNat = 0 := by
          have r27195 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27196 := hb (x 8 1)
          have b27197 := hb (x 9 14)
          clear * - r27195 b27196 b27197 d27190
          omega
        have d27198 : (x 9 3 && x 9 14).toNat = 0 := by
          have r27199 := hand2 (x 9 3) (x 9 14)
          have b27200 := hb (x 9 14)
          have b27201 := hb (x 9 3 && x 9 14)
          clear * - r27199 b27200 b27201 d27194
          omega
        have d27202 : (x 9 2).toNat = 0 := by
          have r27203 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b27204 := hb (x 9 2)
          have b27205 := hb (x 9 14)
          clear * - r27203 b27204 b27205 d27194
          omega
        have d27206 : (x 9 12).toNat = 0 := by
          have r27207 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27208 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e27209 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b27210 := hb (x 6 3)
          have b27211 := hb (x 7 2)
          have b27212 := hb (x 8 13)
          have b27213 := hb (x 9 12)
          clear * - r27207 e27208 e27209 b27210 b27211 b27212 b27213 d27185 d27169
          omega
        have d27214 : (x 6 3).toNat = 0 := by
          have r27215 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27216 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e27217 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b27218 := hb (x 6 3)
          have b27219 := hb (x 7 2)
          have b27220 := hb (x 8 13)
          have b27221 := hb (x 9 12)
          clear * - r27215 e27216 e27217 b27218 b27219 b27220 b27221 d27206 d27185 d27169
          omega
        have d27222 : (x 6 3 && x 6 14).toNat = 0 := by
          have r27223 := hand1 (x 6 3) (x 6 14)
          have b27224 := hb (x 6 3)
          have b27225 := hb (x 6 3 && x 6 14)
          clear * - r27223 b27224 b27225 d27214
          omega
        have d27226 : (x 9 11).toNat = 1 := by
          have r27227 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27228 := hb (x 5 4)
          have b27229 := hb (x 9 11)
          have b27230 := hb (x 8 1 && x 8 12)
          have b27231 := hb (x 7 2 && x 7 13)
          have b27232 := hb (x 6 3 && x 6 14)
          clear * - r27227 b27228 b27229 b27230 b27231 b27232 d27132 d27148 d27222 d27097
          omega
        have d27233 : (x 9 3).toNat = 1 := by
          have r27234 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
          have b27235 := hb (x 9 3)
          have b27236 := hb (x 9 11)
          clear * - r27234 b27235 b27236 d27226
          omega
        have d27237 : (x 12 12).toNat = 0 := by
          have r27238 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27239 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e27240 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b27241 := hb (x 9 3)
          have b27242 := hb (x 10 2)
          have b27243 := hb (x 11 13)
          have b27244 := hb (x 12 12)
          clear * - r27238 e27239 e27240 b27241 b27242 b27243 b27244 d27233
          omega
        have d27245 : (x 11 13).toNat = 0 := by
          have r27246 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27247 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e27248 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b27249 := hb (x 9 3)
          have b27250 := hb (x 10 2)
          have b27251 := hb (x 11 13)
          have b27252 := hb (x 12 12)
          clear * - r27246 e27247 e27248 b27249 b27250 b27251 b27252 d27237 d27233
          omega
        have d27253 : (x 10 1 && x 10 14).toNat = 1 := by
          have r27254 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27255 := hb (x 9 2)
          have b27256 := hb (x 11 13)
          have b27257 := hb (x 10 1 && x 10 14)
          clear * - r27254 b27255 b27256 b27257 d27245 d27202
          omega
        have d27258 : (x 10 14).toNat = 1 := by
          have r27259 := hand2 (x 10 1) (x 10 14)
          have b27260 := hb (x 10 14)
          have b27261 := hb (x 10 1 && x 10 14)
          clear * - r27259 b27260 b27261 d27253
          omega
        have d27262 : (x 9 1).toNat = 0 := by
          have r27263 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27264 := hb (x 9 1)
          have b27265 := hb (x 10 14)
          clear * - r27263 b27264 b27265 d27258
          omega
        have d27266 : (x 9 13).toNat = 0 := by
          have r27267 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b27268 := hb (x 9 1)
          have b27269 := hb (x 9 13)
          clear * - r27267 b27268 b27269 d27262
          omega
        have d27270 : (x 8 1 && x 8 14).toNat = 1 := by
          have r27271 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27272 := hb (x 7 2)
          have b27273 := hb (x 9 13)
          have b27274 := hb (x 8 1 && x 8 14)
          clear * - r27271 b27272 b27273 b27274 d27266 d27169
          omega
        have d27275 : (x 8 14).toNat = 1 := by
          have r27276 := hand2 (x 8 1) (x 8 14)
          have b27277 := hb (x 8 14)
          have b27278 := hb (x 8 1 && x 8 14)
          clear * - r27276 b27277 b27278 d27270
          omega
        have d27279 : (x 7 1).toNat = 0 := by
          have r27280 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27281 := hb (x 7 1)
          have b27282 := hb (x 8 14)
          clear * - r27280 b27281 b27282 d27275
          omega
        have d27283 : (x 7 1 && x 7 12).toNat = 0 := by
          have r27284 := hand1 (x 7 1) (x 7 12)
          have b27285 := hb (x 7 1)
          have b27286 := hb (x 7 1 && x 7 12)
          clear * - r27284 b27285 b27286 d27279
          omega
        have d27287 : (x 8 11).toNat = 1 := by
          have r27288 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27289 := hb (x 4 4)
          have b27290 := hb (x 8 11)
          have b27291 := hb (x 7 1 && x 7 12)
          have b27292 := hb (x 6 2 && x 6 13)
          have b27293 := hb (x 5 3 && x 5 14)
          clear * - r27288 b27289 b27290 b27291 b27292 b27293 d27283 d27181 d27081 d27023
          omega
        have d27294 : (x 8 3).toNat = 1 := by
          have r27295 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b27296 := hb (x 8 3)
          have b27297 := hb (x 8 11)
          clear * - r27295 b27296 b27297 d27287
          omega
        have d27298 : (x 11 12).toNat = 0 := by
          have r27299 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e27300 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e27301 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b27302 := hb (x 8 3)
          have b27303 := hb (x 9 2)
          have b27304 := hb (x 10 13)
          have b27305 := hb (x 11 12)
          clear * - r27299 e27300 e27301 b27302 b27303 b27304 b27305 d27202 d27294
          omega
        have d27306 : (x 11 1 && x 11 12).toNat = 0 := by
          have r27307 := hand2 (x 11 1) (x 11 12)
          have b27308 := hb (x 11 12)
          have b27309 := hb (x 11 1 && x 11 12)
          clear * - r27307 b27308 b27309 d27298
          omega
        have d27310 : (x 10 2 && x 10 13).toNat = 1 := by
          have r27311 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b27312 := hb (x 8 4)
          have b27313 := hb (x 12 11)
          have b27314 := hb (x 11 1 && x 11 12)
          have b27315 := hb (x 10 2 && x 10 13)
          have b27316 := hb (x 9 3 && x 9 14)
          clear * - r27311 b27312 b27313 b27314 b27315 b27316 d24085 d27306 d27198 d27136
          omega
        have d27317 : (x 10 13).toNat = 1 := by
          have r27318 := hand2 (x 10 2) (x 10 13)
          have b27319 := hb (x 10 13)
          have b27320 := hb (x 10 2 && x 10 13)
          clear * - r27318 b27319 b27320 d27310
          omega
        have r27321 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27322 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e27323 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b27324 := hb (x 8 3)
        have b27325 := hb (x 9 2)
        have b27326 := hb (x 10 13)
        have b27327 := hb (x 11 12)
        linarith only [r27321, e27322, e27323, b27324, b27325, b27326, b27327, d27298, d27317, d27202, d27294]
    · have f27328 : (x 1 1).toNat = 1 := by rw [h24523]; rfl
      have d27329 : (x 2 14).toNat = 0 := by
        have r27330 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27331 := hb (x 1 1)
        have b27332 := hb (x 2 14)
        clear * - r27330 b27331 b27332 f27328
        omega
      have d27333 : (x 2 1 && x 2 14).toNat = 0 := by
        have r27334 := hand2 (x 2 1) (x 2 14)
        have b27335 := hb (x 2 14)
        have b27336 := hb (x 2 1 && x 2 14)
        clear * - r27334 b27335 b27336 d27329
        omega
      have d27337 : (x 2 6).toNat = 0 := by
        have r27338 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
        have b27339 := hb (x 2 6)
        have b27340 := hb (x 2 14)
        clear * - r27338 b27339 b27340 d27329
        omega
      have d27341 : (x 2 2 && x 2 6).toNat = 0 := by
        have r27342 := hand2 (x 2 2) (x 2 6)
        have b27343 := hb (x 2 6)
        have b27344 := hb (x 2 2 && x 2 6)
        clear * - r27342 b27343 b27344 d27337
        omega
      have d27345 : (x 2 2).toNat = 0 := by
        have r27346 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b27347 := hb (x 2 2)
        have b27348 := hb (x 2 14)
        clear * - r27346 b27347 b27348 d27329
        omega
      have d27349 : (x 3 13).toNat = 1 := by
        have r27350 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27351 := hb (x 1 2)
        have b27352 := hb (x 3 13)
        have b27353 := hb (x 2 1 && x 2 14)
        clear * - r27350 b27351 b27352 b27353 d27333 g24
        omega
      have d27354 : (x 3 1).toNat = 1 := by
        have r27355 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b27356 := hb (x 3 1)
        have b27357 := hb (x 3 13)
        clear * - r27355 b27356 b27357 d27349
        omega
      have d27358 : (x 4 12).toNat = 0 := by
        have r27359 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27360 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e27361 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b27362 := hb (x 1 3)
        have b27363 := hb (x 2 2)
        have b27364 := hb (x 3 13)
        have b27365 := hb (x 4 12)
        clear * - r27359 e27360 e27361 b27362 b27363 b27364 b27365 d27349 d27345
        omega
      have d27366 : (x 4 3 && x 4 12).toNat = 0 := by
        have r27367 := hand2 (x 4 3) (x 4 12)
        have b27368 := hb (x 4 12)
        have b27369 := hb (x 4 3 && x 4 12)
        clear * - r27367 b27368 b27369 d27358
        omega
      have d27370 : (x 4 4).toNat = 0 := by
        have r27371 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b27372 := hb (x 4 4)
        have b27373 := hb (x 4 12)
        clear * - r27371 b27372 b27373 d27358
        omega
      have d27374 : (x 1 3).toNat = 0 := by
        have r27375 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27376 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e27377 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b27378 := hb (x 1 3)
        have b27379 := hb (x 2 2)
        have b27380 := hb (x 3 13)
        have b27381 := hb (x 4 12)
        clear * - r27375 e27376 e27377 b27378 b27379 b27380 b27381 d27358 d27349 d27345
        omega
      have d27382 : (x 1 3 && x 1 7).toNat = 0 := by
        have r27383 := hand1 (x 1 3) (x 1 7)
        have b27384 := hb (x 1 3)
        have b27385 := hb (x 1 3 && x 1 7)
        clear * - r27383 b27384 b27385 d27374
        omega
      have r27386 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27387 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27388 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27389 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27390 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27391 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e27392 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e27393 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e27394 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e27395 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e27396 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have r27397 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27398 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e27399 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e27400 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e27401 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e27402 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e27403 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r27404 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27405 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e27406 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have r27407 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27408 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e27409 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have r27410 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27411 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e27412 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have r27413 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27414 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27415 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
      have e27416 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
      have r27417 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27418 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27419 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27420 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27421 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27422 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r27423 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have r27424 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
      have r27425 := hand1 (x (-4) 8) (x (-4) 12)
      have r27426 := hand1 (x (-5) 9) (x (-5) 13)
      have r27427 := hand2 (x 7 1) (x 7 7)
      have r27428 := hand2 (x 6 1) (x 6 10)
      have r27429 := hand2 (x 5 2) (x 5 11)
      have r27430 := hand1 (x 11 3) (x 11 12)
      have r27431 := hand1 (x 10 4) (x 10 13)
      have r27432 := hand1 (x 9 5) (x 9 14)
      have r27433 := hand2 (x (-8) 1) (x (-8) 12)
      have r27434 := hand2 (x (-9) 2) (x (-9) 13)
      have r27435 := hand2 (x (-10) 3) (x (-10) 14)
      have r27436 := hand1 (x 13 1) (x 13 14)
      have b27452 := hb (x (-6) 14)
      have b27510 := hb (x 14 1)
      linarith only [r27386, r27387, r27388, r27389, r27390, e27391, e27392, e27393, e27394, e27395, e27396, r27397, e27398, e27399, e27400, e27401, e27402, e27403, r27404, e27405, e27406, r27407, e27408, e27409, r27410, e27411, e27412, r27413, r27414, e27415, e27416, r27417, r27418, r27419, r27420, r27421, r27422, r27423, r27424, r27425, r27426, r27427, r27428, r27429, r27430, r27431, r27432, r27433, r27434, r27435, r27436, b27452, b27510, g3, g4, g6, g7, g10, g12, g17, g19, g23, d27374, g27, g31, g32, d27345, d27337, g36, g37, d27354, g41, g42, d27370, g44, d23994, g46, d23966, g47, d23938, d23910, d24022, d24145, d24125, d24105, d24049, d27341, d27382, g50, g51, g52, g53, g84, g85, g86, g87, g88, g89, g90, g91, g92, g93, g94, g95, g96, g97, d27366, g107, g108, d24081, d24101]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b11111 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 6).toNat = 0)
    (g1 : (x (-4) 7).toNat = 0)
    (g2 : (x (-3) 6).toNat = 0)
    (g3 : (x (-3) 7).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 5).toNat = 0)
    (g6 : (x (-2) 6).toNat = 0)
    (g7 : (x (-2) 10).toNat = 0)
    (g8 : (x (-2) 11).toNat = 0)
    (g9 : (x (-1) 4).toNat = 0)
    (g10 : (x (-1) 5).toNat = 0)
    (g11 : (x (-1) 7).toNat = 0)
    (g12 : (x (-1) 9).toNat = 0)
    (g13 : (x (-1) 10).toNat = 0)
    (g14 : (x (-1) 11).toNat = 0)
    (g15 : (x (-1) 13).toNat = 0)
    (g16 : (x 0 3).toNat = 1)
    (g17 : (x 0 4).toNat = 1)
    (g18 : (x 0 7).toNat = 1)
    (g19 : (x 0 8).toNat = 0)
    (g20 : (x 0 9).toNat = 1)
    (g21 : (x 0 11).toNat = 1)
    (g22 : (x 0 13).toNat = 1)
    (g23 : (x 0 14).toNat = 1)
    (g24 : (x 1 2).toNat = 0)
    (g25 : (x 1 4).toNat = 0)
    (g26 : (x 1 5).toNat = 0)
    (g27 : (x 1 6).toNat = 0)
    (g28 : (x 1 8).toNat = 0)
    (g29 : (x 1 10).toNat = 0)
    (g30 : (x 1 12).toNat = 0)
    (g31 : (x 1 13).toNat = 0)
    (g32 : (x 1 14).toNat = 0)
    (g33 : (x 2 5).toNat = 0)
    (g34 : (x 2 9).toNat = 0)
    (g35 : (x 2 11).toNat = 0)
    (g36 : (x 2 12).toNat = 0)
    (g37 : (x 2 13).toNat = 0)
    (g38 : (x 3 4).toNat = 0)
    (g39 : (x 3 8).toNat = 0)
    (g40 : (x 3 10).toNat = 0)
    (g41 : (x 3 11).toNat = 0)
    (g42 : (x 3 12).toNat = 0)
    (g43 : (x 4 9).toNat = 0)
    (g44 : (x 4 10).toNat = 0)
    (g45 : (x 5 8).toNat = 0)
    (g46 : (x 5 9).toNat = 0)
    (g47 : (x 6 8).toNat = 0)
    (g48 : (x 3 12 && x 3 13).toNat = 0)
    (g49 : (x 2 13 && x 2 14).toNat = 0)
    (g50 : (x 0 4 && x 0 8).toNat = 0)
    (g51 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g52 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g53 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g54 : (x 4 4 && x 4 8).toNat = 0)
    (g55 : (x 3 5 && x 3 9).toNat = 0)
    (g56 : (x 2 6 && x 2 10).toNat = 0)
    (g57 : (x 1 7 && x 1 11).toNat = 0)
    (g58 : (x 0 8 && x 0 12).toNat = 0)
    (g59 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g60 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g61 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g62 : (x 1 2 && x 1 7).toNat = 0)
    (g63 : (x 0 3 && x 0 8).toNat = 0)
    (g64 : (x (-1) 4 && x (-1) 9).toNat = 0)
    (g65 : (x (-2) 5 && x (-2) 10).toNat = 0)
    (g66 : (x (-3) 6 && x (-3) 11).toNat = 0)
    (g67 : (x (-4) 7 && x (-4) 12).toNat = 0)
    (g68 : (x 5 3 && x 5 8).toNat = 0)
    (g69 : (x 4 4 && x 4 9).toNat = 0)
    (g70 : (x 3 5 && x 3 10).toNat = 0)
    (g71 : (x 2 6 && x 2 11).toNat = 0)
    (g72 : (x 1 7 && x 1 12).toNat = 0)
    (g73 : (x 0 8 && x 0 13).toNat = 0)
    (g74 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g75 : (x 3 7 && x 3 12).toNat = 0)
    (g76 : (x 2 8 && x 2 13).toNat = 0)
    (g77 : (x 1 9 && x 1 14).toNat = 0)
    (g78 : (x 3 8 && x 3 13).toNat = 0)
    (g79 : (x 2 9 && x 2 14).toNat = 0)
    (g80 : (x 0 2 && x 0 8).toNat = 0)
    (g81 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g82 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g83 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g84 : (x 6 2 && x 6 8).toNat = 0)
    (g85 : (x 5 3 && x 5 9).toNat = 0)
    (g86 : (x 4 4 && x 4 10).toNat = 0)
    (g87 : (x 3 5 && x 3 11).toNat = 0)
    (g88 : (x 2 6 && x 2 12).toNat = 0)
    (g89 : (x 1 7 && x 1 13).toNat = 0)
    (g90 : (x 0 8 && x 0 14).toNat = 0)
    (g91 : (x 0 1 && x 0 8).toNat = 0)
    (g92 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g93 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g94 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g95 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g96 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g97 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g98 : (x 3 5 && x 3 12).toNat = 0)
    (g99 : (x 2 6 && x 2 13).toNat = 0)
    (g100 : (x 1 7 && x 1 14).toNat = 0)
    (g101 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g102 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g103 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g104 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g105 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g106 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g107 : (x 3 4 && x 3 13).toNat = 0)
    (g108 : (x 2 5 && x 2 14).toNat = 0)
    (g109 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g110 : (x 2 4 && x 2 14).toNat = 0)
    (g111 : (x 3 4 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b11111_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111
