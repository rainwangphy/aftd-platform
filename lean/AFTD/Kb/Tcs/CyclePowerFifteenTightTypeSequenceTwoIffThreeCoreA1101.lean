import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1101

Topic: combinatorics   Node: 1c67b4fec4f4

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 69 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1101_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-7) 11).toNat = 0)
    (g1 : (x (-6) 6).toNat = 0)
    (g2 : (x (-6) 10).toNat = 0)
    (g3 : (x (-5) 13).toNat = 0)
    (g4 : (x (-4) 12).toNat = 1)
    (g5 : (x (-3) 11).toNat = 0)
    (g6 : (x (-2) 10).toNat = 0)
    (g7 : (x (-2) 11).toNat = 0)
    (g8 : (x (-1) 5).toNat = 0)
    (g9 : (x (-1) 9).toNat = 0)
    (g10 : (x (-1) 10).toNat = 0)
    (g11 : (x (-1) 11).toNat = 0)
    (g12 : (x 0 4).toNat = 0)
    (g13 : (x 0 5).toNat = 1)
    (g14 : (x 0 8).toNat = 0)
    (g15 : (x 0 11).toNat = 0)
    (g16 : (x 0 14).toNat = 1)
    (g17 : (x 1 2).toNat = 0)
    (g18 : (x 1 4).toNat = 0)
    (g19 : (x 1 5).toNat = 0)
    (g20 : (x 1 6).toNat = 0)
    (g21 : (x 1 10).toNat = 0)
    (g22 : (x 1 13).toNat = 0)
    (g23 : (x 2 4).toNat = 0)
    (g24 : (x 2 12).toNat = 0)
    (g25 : (x 0 4 && x 0 8).toNat = 0)
    (g26 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g27 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g29 : (x (-5) 9 && x (-5) 13).toNat = 0)
    (g30 : (x 0 4 && x 0 9).toNat = 0)
    (g31 : (x (-1) 5 && x (-1) 10).toNat = 0)
    (g32 : (x (-2) 6 && x (-2) 11).toNat = 0)
    (g33 : (x 1 7 && x 1 12).toNat = 0)
    (g34 : (x 0 8 && x 0 13).toNat = 0)
    (g35 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g37 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g38 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g39 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g40 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g41 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g42 : (x (-6) 2 && x (-6) 11).toNat = 0)
    (g43 : (x (-7) 3 && x (-7) 12).toNat = 0)
    (g44 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g45 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g46 : (x (-5) 4 && x (-5) 13).toNat = 0)
    (g47 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g48 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g49 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g50 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g51 : (x 1 2 && x 1 11).toNat = 0)
    (g52 : (x 0 3 && x 0 12).toNat = 0)
    (g53 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g54 : (x 1 3 && x 1 12).toNat = 0)
    (g55 : (x 0 4 && x 0 13).toNat = 0)
    (g56 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g57 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g58 : (x 0 1 && x 0 11).toNat = 0)
    (g59 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g60 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g61 : (x 2 2 && x 2 12).toNat = 0)
    (g62 : (x 1 3 && x 1 13).toNat = 0)
    (g63 : (x 0 4 && x 0 14).toNat = 0)
    (g64 : (x (-6) 2 && x (-6) 13).toNat = 0)
    (g65 : (x (-7) 3 && x (-7) 14).toNat = 0)
    (g66 : (x 2 1 && x 2 12).toNat = 0)
    (g67 : (x 1 2 && x 1 13).toNat = 0)
    (g68 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d22095 : (x 5 8).toNat = 0 := by
    have r22096 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22097 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e22098 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e22099 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e22100 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e22101 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e22102 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b22103 := hb (x (-2) 7)
    have b22104 := hb (x (-1) 6)
    have b22105 := hb (x 0 5)
    have b22106 := hb (x 1 4)
    have b22107 := hb (x 2 11)
    have b22108 := hb (x 3 10)
    have b22109 := hb (x 4 9)
    have b22110 := hb (x 5 8)
    clear * - r22096 e22097 e22098 e22099 e22100 e22101 e22102 b22103 b22104 b22105 b22106 b22107 b22108 b22109 b22110 g18 g13
    omega
  have d22111 : (x 5 3 && x 5 8).toNat = 0 := by
    have r22112 := hand2 (x 5 3) (x 5 8)
    have b22113 := hb (x 5 8)
    have b22114 := hb (x 5 3 && x 5 8)
    clear * - r22112 b22113 b22114 d22095
    omega
  have d22115 : (x 4 9).toNat = 0 := by
    have r22116 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22117 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e22118 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e22119 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e22120 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e22121 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e22122 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b22123 := hb (x (-2) 7)
    have b22124 := hb (x (-1) 6)
    have b22125 := hb (x 0 5)
    have b22126 := hb (x 1 4)
    have b22127 := hb (x 2 11)
    have b22128 := hb (x 3 10)
    have b22129 := hb (x 4 9)
    have b22130 := hb (x 5 8)
    clear * - r22116 e22117 e22118 e22119 e22120 e22121 e22122 b22123 b22124 b22125 b22126 b22127 b22128 b22129 b22130 d22095 g18 g13
    omega
  have d22131 : (x 4 4 && x 4 9).toNat = 0 := by
    have r22132 := hand2 (x 4 4) (x 4 9)
    have b22133 := hb (x 4 9)
    have b22134 := hb (x 4 4 && x 4 9)
    clear * - r22132 b22133 b22134 d22115
    omega
  have d22135 : (x 3 10).toNat = 0 := by
    have r22136 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22137 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e22138 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e22139 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e22140 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e22141 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e22142 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b22143 := hb (x (-2) 7)
    have b22144 := hb (x (-1) 6)
    have b22145 := hb (x 0 5)
    have b22146 := hb (x 1 4)
    have b22147 := hb (x 2 11)
    have b22148 := hb (x 3 10)
    have b22149 := hb (x 4 9)
    have b22150 := hb (x 5 8)
    clear * - r22136 e22137 e22138 e22139 e22140 e22141 e22142 b22143 b22144 b22145 b22146 b22147 b22148 b22149 b22150 d22095 d22115 g18 g13
    omega
  have d22151 : (x 3 1 && x 3 10).toNat = 0 := by
    have r22152 := hand2 (x 3 1) (x 3 10)
    have b22153 := hb (x 3 10)
    have b22154 := hb (x 3 1 && x 3 10)
    clear * - r22152 b22153 b22154 d22135
    omega
  have d22155 : (x 3 5 && x 3 10).toNat = 0 := by
    have r22156 := hand2 (x 3 5) (x 3 10)
    have b22157 := hb (x 3 10)
    have b22158 := hb (x 3 5 && x 3 10)
    clear * - r22156 b22157 b22158 d22135
    omega
  have d22159 : (x 2 11).toNat = 0 := by
    have r22160 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22161 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e22162 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e22163 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e22164 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e22165 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e22166 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b22167 := hb (x (-2) 7)
    have b22168 := hb (x (-1) 6)
    have b22169 := hb (x 0 5)
    have b22170 := hb (x 1 4)
    have b22171 := hb (x 2 11)
    have b22172 := hb (x 3 10)
    have b22173 := hb (x 4 9)
    have b22174 := hb (x 5 8)
    clear * - r22160 e22161 e22162 e22163 e22164 e22165 e22166 b22167 b22168 b22169 b22170 b22171 b22172 b22173 b22174 d22095 d22115 d22135 g18 g13
    omega
  have d22175 : (x 2 2 && x 2 11).toNat = 0 := by
    have r22176 := hand2 (x 2 2) (x 2 11)
    have b22177 := hb (x 2 11)
    have b22178 := hb (x 2 2 && x 2 11)
    clear * - r22176 b22177 b22178 d22159
    omega
  have d22179 : (x (-2) 6).toNat = 1 := by
    have r22180 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b22181 := hb (x (-2) 6)
    have b22182 := hb (x 4 9)
    have b22183 := hb (x 3 1 && x 3 10)
    have b22184 := hb (x 2 2 && x 2 11)
    have b22185 := hb (x 1 3 && x 1 12)
    have b22186 := hb (x 0 4 && x 0 13)
    have b22187 := hb (x (-1) 5 && x (-1) 14)
    clear * - r22180 b22181 b22182 b22183 b22184 b22185 b22186 b22187 d22115 d22151 d22175 g54 g55 g56
    omega
  have d22188 : (x (-2) 14).toNat = 1 := by
    have r22189 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b22190 := hb (x (-2) 6)
    have b22191 := hb (x (-2) 14)
    clear * - r22189 b22190 b22191 d22179
    omega
  have d22192 : (x (-3) 1).toNat = 0 := by
    have r22193 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b22194 := hb (x (-3) 1)
    have b22195 := hb (x (-2) 14)
    clear * - r22193 b22194 b22195 d22188
    omega
  have d22196 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
    have r22197 := hand1 (x (-3) 1) (x (-3) 12)
    have b22198 := hb (x (-3) 1)
    have b22199 := hb (x (-3) 1 && x (-3) 12)
    clear * - r22197 b22198 b22199 d22192
    omega
  have d22200 : (x (-3) 13).toNat = 0 := by
    have r22201 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b22202 := hb (x (-3) 1)
    have b22203 := hb (x (-3) 13)
    clear * - r22201 b22202 b22203 d22192
    omega
  have d22204 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
    have r22205 := hand2 (x (-3) 2) (x (-3) 13)
    have b22206 := hb (x (-3) 13)
    have b22207 := hb (x (-3) 2 && x (-3) 13)
    clear * - r22205 b22206 b22207 d22200
    omega
  have d22208 : (x 2 6 && x 2 11).toNat = 0 := by
    have r22209 := hand2 (x 2 6) (x 2 11)
    have b22210 := hb (x 2 11)
    have b22211 := hb (x 2 6 && x 2 11)
    clear * - r22209 b22210 b22211 d22159
    omega
  have d22212 : (x (-1) 6).toNat = 0 := by
    have r22213 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22214 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e22215 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e22216 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e22217 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e22218 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e22219 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b22220 := hb (x (-2) 7)
    have b22221 := hb (x (-1) 6)
    have b22222 := hb (x 0 5)
    have b22223 := hb (x 1 4)
    have b22224 := hb (x 2 11)
    have b22225 := hb (x 3 10)
    have b22226 := hb (x 4 9)
    have b22227 := hb (x 5 8)
    clear * - r22213 e22214 e22215 e22216 e22217 e22218 e22219 b22220 b22221 b22222 b22223 b22224 b22225 b22226 b22227 d22095 d22115 d22135 d22159 g18 g13
    omega
  have d22228 : (x (-2) 7).toNat = 0 := by
    have r22229 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22230 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e22231 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e22232 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e22233 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e22234 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e22235 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b22236 := hb (x (-2) 7)
    have b22237 := hb (x (-1) 6)
    have b22238 := hb (x 0 5)
    have b22239 := hb (x 1 4)
    have b22240 := hb (x 2 11)
    have b22241 := hb (x 3 10)
    have b22242 := hb (x 4 9)
    have b22243 := hb (x 5 8)
    clear * - r22229 e22230 e22231 e22232 e22233 e22234 e22235 b22236 b22237 b22238 b22239 b22240 b22241 b22242 b22243 d22095 d22115 d22135 d22159 g18 g13 d22212
    omega
  have d22244 : (x 4 8).toNat = 0 := by
    have r22245 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22246 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e22247 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e22248 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e22249 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e22250 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e22251 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b22252 := hb (x (-3) 7)
    have b22253 := hb (x (-2) 6)
    have b22254 := hb (x (-1) 5)
    have b22255 := hb (x 0 4)
    have b22256 := hb (x 1 11)
    have b22257 := hb (x 2 10)
    have b22258 := hb (x 3 9)
    have b22259 := hb (x 4 8)
    clear * - r22245 e22246 e22247 e22248 e22249 e22250 e22251 b22252 b22253 b22254 b22255 b22256 b22257 b22258 b22259 g12 g8 d22179
    omega
  have d22260 : (x 3 9).toNat = 0 := by
    have r22261 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22262 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e22263 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e22264 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e22265 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e22266 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e22267 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b22268 := hb (x (-3) 7)
    have b22269 := hb (x (-2) 6)
    have b22270 := hb (x (-1) 5)
    have b22271 := hb (x 0 4)
    have b22272 := hb (x 1 11)
    have b22273 := hb (x 2 10)
    have b22274 := hb (x 3 9)
    have b22275 := hb (x 4 8)
    clear * - r22261 e22262 e22263 e22264 e22265 e22266 e22267 b22268 b22269 b22270 b22271 b22272 b22273 b22274 b22275 d22244 g12 g8 d22179
    omega
  have d22276 : (x 2 10).toNat = 0 := by
    have r22277 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22278 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e22279 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e22280 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e22281 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e22282 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e22283 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b22284 := hb (x (-3) 7)
    have b22285 := hb (x (-2) 6)
    have b22286 := hb (x (-1) 5)
    have b22287 := hb (x 0 4)
    have b22288 := hb (x 1 11)
    have b22289 := hb (x 2 10)
    have b22290 := hb (x 3 9)
    have b22291 := hb (x 4 8)
    clear * - r22277 e22278 e22279 e22280 e22281 e22282 e22283 b22284 b22285 b22286 b22287 b22288 b22289 b22290 b22291 d22244 d22260 g12 g8 d22179
    omega
  have d22292 : (x 2 1 && x 2 10).toNat = 0 := by
    have r22293 := hand2 (x 2 1) (x 2 10)
    have b22294 := hb (x 2 10)
    have b22295 := hb (x 2 1 && x 2 10)
    clear * - r22293 b22294 b22295 d22276
    omega
  have d22296 : (x 1 11).toNat = 0 := by
    have r22297 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22298 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e22299 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e22300 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e22301 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e22302 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e22303 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b22304 := hb (x (-3) 7)
    have b22305 := hb (x (-2) 6)
    have b22306 := hb (x (-1) 5)
    have b22307 := hb (x 0 4)
    have b22308 := hb (x 1 11)
    have b22309 := hb (x 2 10)
    have b22310 := hb (x 3 9)
    have b22311 := hb (x 4 8)
    clear * - r22297 e22298 e22299 e22300 e22301 e22302 e22303 b22304 b22305 b22306 b22307 b22308 b22309 b22310 b22311 d22244 d22260 d22276 g12 g8 d22179
    omega
  have d22312 : (x (-3) 7).toNat = 0 := by
    have r22313 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22314 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e22315 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e22316 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e22317 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e22318 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e22319 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b22320 := hb (x (-3) 7)
    have b22321 := hb (x (-2) 6)
    have b22322 := hb (x (-1) 5)
    have b22323 := hb (x 0 4)
    have b22324 := hb (x 1 11)
    have b22325 := hb (x 2 10)
    have b22326 := hb (x 3 9)
    have b22327 := hb (x 4 8)
    clear * - r22313 e22314 e22315 e22316 e22317 e22318 e22319 b22320 b22321 b22322 b22323 b22324 b22325 b22326 b22327 d22244 d22260 d22276 d22296 g12 g8 d22179
    omega
  have d22328 : (x (-3) 7 && x (-3) 12).toNat = 0 := by
    have r22329 := hand1 (x (-3) 7) (x (-3) 12)
    have b22330 := hb (x (-3) 7)
    have b22331 := hb (x (-3) 7 && x (-3) 12)
    clear * - r22329 b22330 b22331 d22312
    omega
  cases h22332 : x 0 6
  · have f22333 : (x 0 6).toNat = 0 := by rw [h22332]; rfl
    cases h22334 : x 0 9
    · have f22335 : (x 0 9).toNat = 0 := by rw [h22334]; rfl
      have d22336 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
        have r22337 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22338 := hb (x (-6) 6)
        have b22339 := hb (x 0 9)
        have b22340 := hb (x (-1) 1 && x (-1) 10)
        have b22341 := hb (x (-2) 2 && x (-2) 11)
        have b22342 := hb (x (-3) 3 && x (-3) 12)
        have b22343 := hb (x (-4) 4 && x (-4) 13)
        have b22344 := hb (x (-5) 5 && x (-5) 14)
        clear * - r22337 b22338 b22339 b22340 b22341 b22342 b22343 b22344 f22335 g47 g48 g49 g50 g1
        omega
      have d22345 : (x (-4) 13).toNat = 1 := by
        have r22346 := hand2 (x (-4) 4) (x (-4) 13)
        have b22347 := hb (x (-4) 13)
        have b22348 := hb (x (-4) 4 && x (-4) 13)
        clear * - r22346 b22347 b22348 d22336
        omega
      have d22349 : (x (-4) 1).toNat = 1 := by
        have r22350 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b22351 := hb (x (-4) 1)
        have b22352 := hb (x (-4) 13)
        clear * - r22350 b22351 b22352 d22345
        omega
      have d22353 : (x (-3) 14).toNat = 0 := by
        have r22354 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22355 := hb (x (-4) 1)
        have b22356 := hb (x (-3) 14)
        clear * - r22354 b22355 b22356 d22349
        omega
      have d22357 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
        have r22358 := hand2 (x (-3) 4) (x (-3) 14)
        have b22359 := hb (x (-3) 14)
        have b22360 := hb (x (-3) 4 && x (-3) 14)
        clear * - r22358 b22359 b22360 d22353
        omega
      have d22361 : (x (-4) 5).toNat = 1 := by
        have r22362 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22363 := hb (x (-4) 5)
        have b22364 := hb (x 1 10)
        have b22365 := hb (x 0 1 && x 0 11)
        have b22366 := hb (x (-1) 2 && x (-1) 12)
        have b22367 := hb (x (-2) 3 && x (-2) 13)
        have b22368 := hb (x (-3) 4 && x (-3) 14)
        clear * - r22362 b22363 b22364 b22365 b22366 b22367 b22368 g21 g58 g59 g60 d22357
        omega
      have d22369 : (x (-3) 6).toNat = 0 := by
        have r22370 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
        have b22371 := hb (x (-3) 6)
        have b22372 := hb (x (-3) 14)
        clear * - r22370 b22371 b22372 d22353
        omega
      have d22373 : (x (-2) 5 && x (-2) 14).toNat = 1 := by
        have r22374 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22375 := hb (x (-3) 6)
        have b22376 := hb (x 3 9)
        have b22377 := hb (x 2 1 && x 2 10)
        have b22378 := hb (x 1 2 && x 1 11)
        have b22379 := hb (x 0 3 && x 0 12)
        have b22380 := hb (x (-1) 4 && x (-1) 13)
        have b22381 := hb (x (-2) 5 && x (-2) 14)
        clear * - r22374 b22375 b22376 b22377 b22378 b22379 b22380 b22381 d22260 d22292 g51 g52 g53 d22369
        omega
      have d22382 : (x (-2) 5).toNat = 1 := by
        have r22383 := hand1 (x (-2) 5) (x (-2) 14)
        have b22384 := hb (x (-2) 5)
        have b22385 := hb (x (-2) 5 && x (-2) 14)
        clear * - r22383 b22384 b22385 d22373
        omega
      have d22386 : (x (-2) 13).toNat = 1 := by
        have r22387 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
        have b22388 := hb (x (-2) 5)
        have b22389 := hb (x (-2) 13)
        clear * - r22387 b22388 b22389 d22382
        omega
      have d22390 : (x (-1) 12).toNat = 0 := by
        have r22391 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22392 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e22393 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b22394 := hb (x (-4) 3)
        have b22395 := hb (x (-3) 2)
        have b22396 := hb (x (-2) 13)
        have b22397 := hb (x (-1) 12)
        clear * - r22391 e22392 e22393 b22394 b22395 b22396 b22397 d22386
        omega
      have d22398 : (x (-1) 4).toNat = 0 := by
        have r22399 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b22400 := hb (x (-1) 4)
        have b22401 := hb (x (-1) 12)
        clear * - r22399 b22400 b22401 d22390
        omega
      have d22402 : (x 3 11).toNat = 1 := by
        have r22403 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22404 := hb (x (-1) 4)
        have b22405 := hb (x 3 11)
        have b22406 := hb (x 2 1 && x 2 12)
        have b22407 := hb (x 1 2 && x 1 13)
        have b22408 := hb (x 0 3 && x 0 14)
        clear * - r22403 b22404 b22405 b22406 b22407 b22408 g66 g67 g68 d22398
        omega
      have d22409 : (x 3 3).toNat = 1 := by
        have r22410 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
        have b22411 := hb (x 3 3)
        have b22412 := hb (x 3 11)
        clear * - r22410 b22411 b22412 d22402
        omega
      have d22413 : (x 6 12).toNat = 0 := by
        have r22414 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22415 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e22416 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b22417 := hb (x 3 3)
        have b22418 := hb (x 4 2)
        have b22419 := hb (x 5 13)
        have b22420 := hb (x 6 12)
        clear * - r22414 e22415 e22416 b22417 b22418 b22419 b22420 d22409
        omega
      have d22421 : (x 5 13).toNat = 0 := by
        have r22422 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22423 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e22424 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b22425 := hb (x 3 3)
        have b22426 := hb (x 4 2)
        have b22427 := hb (x 5 13)
        have b22428 := hb (x 6 12)
        clear * - r22422 e22423 e22424 b22425 b22426 b22427 b22428 d22413 d22409
        omega
      have d22429 : (x 4 2).toNat = 0 := by
        have r22430 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22431 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e22432 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b22433 := hb (x 3 3)
        have b22434 := hb (x 4 2)
        have b22435 := hb (x 5 13)
        have b22436 := hb (x 6 12)
        clear * - r22430 e22431 e22432 b22433 b22434 b22435 b22436 d22413 d22421 d22409
        omega
      have d22437 : (x 4 10).toNat = 0 := by
        have r22438 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
        have b22439 := hb (x 4 2)
        have b22440 := hb (x 4 10)
        clear * - r22438 b22439 b22440 d22429
        omega
      have d22441 : (x 3 1 && x 3 11).toNat = 1 := by
        have r22442 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22443 := hb (x (-1) 5)
        have b22444 := hb (x 4 10)
        have b22445 := hb (x 3 1 && x 3 11)
        have b22446 := hb (x 2 2 && x 2 12)
        have b22447 := hb (x 1 3 && x 1 13)
        have b22448 := hb (x 0 4 && x 0 14)
        clear * - r22442 b22443 b22444 b22445 b22446 b22447 b22448 d22437 g61 g62 g63 g8
        omega
      have d22449 : (x 3 1).toNat = 1 := by
        have r22450 := hand1 (x 3 1) (x 3 11)
        have b22451 := hb (x 3 1)
        have b22452 := hb (x 3 1 && x 3 11)
        clear * - r22450 b22451 b22452 d22441
        omega
      have d22453 : (x 4 14).toNat = 0 := by
        have r22454 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22455 := hb (x 3 1)
        have b22456 := hb (x 4 14)
        clear * - r22454 b22455 b22456 d22449
        omega
      have d22457 : (x 4 1 && x 4 14).toNat = 0 := by
        have r22458 := hand2 (x 4 1) (x 4 14)
        have b22459 := hb (x 4 14)
        have b22460 := hb (x 4 1 && x 4 14)
        clear * - r22458 b22459 b22460 d22453
        omega
      have d22461 : (x 3 2).toNat = 1 := by
        have r22462 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22463 := hb (x 3 2)
        have b22464 := hb (x 5 13)
        have b22465 := hb (x 4 1 && x 4 14)
        clear * - r22462 b22463 b22464 b22465 d22421 d22457
        omega
      have d22466 : (x 3 14).toNat = 1 := by
        have r22467 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b22468 := hb (x 3 2)
        have b22469 := hb (x 3 14)
        clear * - r22467 b22468 b22469 d22461
        omega
      have d22470 : (x 2 1).toNat = 0 := by
        have r22471 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22472 := hb (x 2 1)
        have b22473 := hb (x 3 14)
        clear * - r22471 b22472 b22473 d22466
        omega
      have d22474 : (x 2 1 && x 2 14).toNat = 0 := by
        have r22475 := hand1 (x 2 1) (x 2 14)
        have b22476 := hb (x 2 1)
        have b22477 := hb (x 2 1 && x 2 14)
        clear * - r22475 b22476 b22477 d22470
        omega
      have d22478 : (x 3 13).toNat = 1 := by
        have r22479 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22480 := hb (x 1 2)
        have b22481 := hb (x 3 13)
        have b22482 := hb (x 2 1 && x 2 14)
        clear * - r22479 b22480 b22481 b22482 d22474 g17
        omega
      have d22483 : (x 4 12).toNat = 0 := by
        have r22484 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22485 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e22486 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b22487 := hb (x 1 3)
        have b22488 := hb (x 2 2)
        have b22489 := hb (x 3 13)
        have b22490 := hb (x 4 12)
        clear * - r22484 e22485 e22486 b22487 b22488 b22489 b22490 d22478
        omega
      have d22491 : (x 4 4).toNat = 0 := by
        have r22492 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b22493 := hb (x 4 4)
        have b22494 := hb (x 4 12)
        clear * - r22492 b22493 b22494 d22483
        omega
      have d22495 : (x 2 2).toNat = 0 := by
        have r22496 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22497 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e22498 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b22499 := hb (x 1 3)
        have b22500 := hb (x 2 2)
        have b22501 := hb (x 3 13)
        have b22502 := hb (x 4 12)
        clear * - r22496 e22497 e22498 b22499 b22500 b22501 b22502 d22483 d22478
        omega
      have d22503 : (x 2 2 && x 2 7).toNat = 0 := by
        have r22504 := hand1 (x 2 2) (x 2 7)
        have b22505 := hb (x 2 2)
        have b22506 := hb (x 2 2 && x 2 7)
        clear * - r22504 b22505 b22506 d22495
        omega
      have d22507 : (x 2 2 && x 2 6).toNat = 0 := by
        have r22508 := hand1 (x 2 2) (x 2 6)
        have b22509 := hb (x 2 2)
        have b22510 := hb (x 2 2 && x 2 6)
        clear * - r22508 b22509 b22510 d22495
        omega
      have d22511 : (x 1 3).toNat = 0 := by
        have r22512 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22513 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e22514 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b22515 := hb (x 1 3)
        have b22516 := hb (x 2 2)
        have b22517 := hb (x 3 13)
        have b22518 := hb (x 4 12)
        clear * - r22512 e22513 e22514 b22515 b22516 b22517 b22518 d22483 d22478 d22495
        omega
      have d22519 : (x 1 3 && x 1 8).toNat = 0 := by
        have r22520 := hand1 (x 1 3) (x 1 8)
        have b22521 := hb (x 1 3)
        have b22522 := hb (x 1 3 && x 1 8)
        clear * - r22520 b22521 b22522 d22511
        omega
      have d22523 : (x 1 3 && x 1 7).toNat = 0 := by
        have r22524 := hand1 (x 1 3) (x 1 7)
        have b22525 := hb (x 1 3)
        have b22526 := hb (x 1 3 && x 1 7)
        clear * - r22524 b22525 b22526 d22511
        omega
      have d22527 : (x 2 13).toNat = 0 := by
        have r22528 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
        have b22529 := hb (x 2 1)
        have b22530 := hb (x 2 13)
        clear * - r22528 b22529 b22530 d22470
        omega
      have d22531 : (x 2 9 && x 2 13).toNat = 0 := by
        have r22532 := hand2 (x 2 9) (x 2 13)
        have b22533 := hb (x 2 13)
        have b22534 := hb (x 2 9 && x 2 13)
        clear * - r22532 b22533 b22534 d22527
        omega
      have d22535 : (x 2 5).toNat = 0 := by
        have r22536 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
        have b22537 := hb (x 2 5)
        have b22538 := hb (x 2 13)
        clear * - r22536 b22537 b22538 d22527
        omega
      have d22539 : (x 2 9).toNat = 0 := by
        have r22540 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
        have b22541 := hb (x 2 1)
        have b22542 := hb (x 2 9)
        clear * - r22540 b22541 b22542 d22470
        omega
      have d22543 : (x 5 12).toNat = 0 := by
        have r22544 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22545 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e22546 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b22547 := hb (x 2 3)
        have b22548 := hb (x 3 2)
        have b22549 := hb (x 4 13)
        have b22550 := hb (x 5 12)
        clear * - r22544 e22545 e22546 b22547 b22548 b22549 b22550 d22461
        omega
      have d22551 : (x 5 2 && x 5 12).toNat = 0 := by
        have r22552 := hand2 (x 5 2) (x 5 12)
        have b22553 := hb (x 5 12)
        have b22554 := hb (x 5 2 && x 5 12)
        clear * - r22552 b22553 b22554 d22543
        omega
      have d22555 : (x 5 6 && x 5 12).toNat = 0 := by
        have r22556 := hand2 (x 5 6) (x 5 12)
        have b22557 := hb (x 5 12)
        have b22558 := hb (x 5 6 && x 5 12)
        clear * - r22556 b22557 b22558 d22543
        omega
      have d22559 : (x 5 4).toNat = 0 := by
        have r22560 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b22561 := hb (x 5 4)
        have b22562 := hb (x 5 12)
        clear * - r22560 b22561 b22562 d22543
        omega
      have d22563 : (x 5 4 && x 5 14).toNat = 0 := by
        have r22564 := hand1 (x 5 4) (x 5 14)
        have b22565 := hb (x 5 4)
        have b22566 := hb (x 5 4 && x 5 14)
        clear * - r22564 b22565 b22566 d22559
        omega
      have d22567 : (x 4 13).toNat = 0 := by
        have r22568 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22569 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e22570 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b22571 := hb (x 2 3)
        have b22572 := hb (x 3 2)
        have b22573 := hb (x 4 13)
        have b22574 := hb (x 5 12)
        clear * - r22568 e22569 e22570 b22571 b22572 b22573 b22574 d22543 d22461
        omega
      have d22575 : (x 4 3 && x 4 13).toNat = 0 := by
        have r22576 := hand2 (x 4 3) (x 4 13)
        have b22577 := hb (x 4 13)
        have b22578 := hb (x 4 3 && x 4 13)
        clear * - r22576 b22577 b22578 d22567
        omega
      have d22579 : (x 4 7 && x 4 13).toNat = 0 := by
        have r22580 := hand2 (x 4 7) (x 4 13)
        have b22581 := hb (x 4 13)
        have b22582 := hb (x 4 7 && x 4 13)
        clear * - r22580 b22581 b22582 d22567
        omega
      have d22583 : (x 4 5).toNat = 0 := by
        have r22584 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
        have b22585 := hb (x 4 5)
        have b22586 := hb (x 4 13)
        clear * - r22584 b22585 b22586 d22567
        omega
      have d22587 : (x 2 3).toNat = 0 := by
        have r22588 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22589 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e22590 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b22591 := hb (x 2 3)
        have b22592 := hb (x 3 2)
        have b22593 := hb (x 4 13)
        have b22594 := hb (x 5 12)
        clear * - r22588 e22589 e22590 b22591 b22592 b22593 b22594 d22543 d22567 d22461
        omega
      have d22595 : (x (-3) 2).toNat = 0 := by
        have r22596 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22597 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e22598 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b22599 := hb (x (-4) 3)
        have b22600 := hb (x (-3) 2)
        have b22601 := hb (x (-2) 13)
        have b22602 := hb (x (-1) 12)
        clear * - r22596 e22597 e22598 b22599 b22600 b22601 b22602 d22390 d22386
        omega
      have d22603 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
        have r22604 := hand1 (x (-3) 2) (x (-3) 12)
        have b22605 := hb (x (-3) 2)
        have b22606 := hb (x (-3) 2 && x (-3) 12)
        clear * - r22604 b22605 b22606 d22595
        omega
      have d22607 : (x (-4) 3).toNat = 0 := by
        have r22608 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22609 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e22610 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b22611 := hb (x (-4) 3)
        have b22612 := hb (x (-3) 2)
        have b22613 := hb (x (-2) 13)
        have b22614 := hb (x (-1) 12)
        clear * - r22608 e22609 e22610 b22611 b22612 b22613 b22614 d22390 d22386 d22595
        omega
      have d22615 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
        have r22616 := hand1 (x (-4) 3) (x (-4) 14)
        have b22617 := hb (x (-4) 3)
        have b22618 := hb (x (-4) 3 && x (-4) 14)
        clear * - r22616 b22617 b22618 d22607
        omega
      have d22619 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
        have r22620 := hand1 (x (-4) 3) (x (-4) 13)
        have b22621 := hb (x (-4) 3)
        have b22622 := hb (x (-4) 3 && x (-4) 13)
        clear * - r22620 b22621 b22622 d22607
        omega
      have d22623 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
        have r22624 := hand1 (x (-4) 3) (x (-4) 12)
        have b22625 := hb (x (-4) 3)
        have b22626 := hb (x (-4) 3 && x (-4) 12)
        clear * - r22624 b22625 b22626 d22607
        omega
      have d22627 : (x (-4) 11).toNat = 0 := by
        have r22628 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
        have b22629 := hb (x (-4) 3)
        have b22630 := hb (x (-4) 11)
        clear * - r22628 b22629 b22630 d22607
        omega
      have d22631 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
        have r22632 := hand2 (x (-4) 4) (x (-4) 11)
        have b22633 := hb (x (-4) 11)
        have b22634 := hb (x (-4) 4 && x (-4) 11)
        clear * - r22632 b22633 b22634 d22627
        omega
      have d22635 : (x (-3) 12).toNat = 0 := by
        have r22636 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22637 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e22638 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b22639 := hb (x (-6) 3)
        have b22640 := hb (x (-5) 2)
        have b22641 := hb (x (-4) 13)
        have b22642 := hb (x (-3) 12)
        clear * - r22636 e22637 e22638 b22639 b22640 b22641 b22642 d22345
        omega
      have d22643 : (x (-3) 4).toNat = 0 := by
        have r22644 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b22645 := hb (x (-3) 4)
        have b22646 := hb (x (-3) 12)
        clear * - r22644 b22645 b22646 d22635
        omega
      have d22647 : (x (-5) 2).toNat = 0 := by
        have r22648 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22649 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e22650 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b22651 := hb (x (-6) 3)
        have b22652 := hb (x (-5) 2)
        have b22653 := hb (x (-4) 13)
        have b22654 := hb (x (-3) 12)
        clear * - r22648 e22649 e22650 b22651 b22652 b22653 b22654 d22635 d22345
        omega
      have d22655 : (x (-5) 10).toNat = 0 := by
        have r22656 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
        have b22657 := hb (x (-5) 2)
        have b22658 := hb (x (-5) 10)
        clear * - r22656 b22657 b22658 d22647
        omega
      have d22659 : (x (-5) 1 && x (-5) 10).toNat = 0 := by
        have r22660 := hand2 (x (-5) 1) (x (-5) 10)
        have b22661 := hb (x (-5) 10)
        have b22662 := hb (x (-5) 1 && x (-5) 10)
        clear * - r22660 b22661 b22662 d22655
        omega
      have d22663 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
        have r22664 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22665 := hb (x (-5) 2)
        have b22666 := hb (x (-3) 13)
        have b22667 := hb (x (-4) 1 && x (-4) 14)
        clear * - r22664 b22665 b22666 b22667 d22200 d22647
        omega
      have d22668 : (x (-4) 14).toNat = 1 := by
        have r22669 := hand2 (x (-4) 1) (x (-4) 14)
        have b22670 := hb (x (-4) 14)
        have b22671 := hb (x (-4) 1 && x (-4) 14)
        clear * - r22669 b22670 b22671 d22663
        omega
      have d22672 : (x (-5) 1).toNat = 0 := by
        have r22673 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22674 := hb (x (-5) 1)
        have b22675 := hb (x (-4) 14)
        clear * - r22673 b22674 b22675 d22668
        omega
      have d22676 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
        have r22677 := hand1 (x (-5) 1) (x (-5) 12)
        have b22678 := hb (x (-5) 1)
        have b22679 := hb (x (-5) 1 && x (-5) 12)
        clear * - r22677 b22678 b22679 d22672
        omega
      have d22680 : (x (-8) 4).toNat = 1 := by
        have r22681 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22682 := hb (x (-8) 4)
        have b22683 := hb (x (-4) 11)
        have b22684 := hb (x (-5) 1 && x (-5) 12)
        have b22685 := hb (x (-6) 2 && x (-6) 13)
        have b22686 := hb (x (-7) 3 && x (-7) 14)
        clear * - r22681 b22682 b22683 b22684 b22685 b22686 d22627 d22676 g64 g65
        omega
      have d22687 : (x (-8) 12).toNat = 1 := by
        have r22688 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
        have b22689 := hb (x (-8) 4)
        have b22690 := hb (x (-8) 12)
        clear * - r22688 b22689 b22690 d22680
        omega
      have d22691 : (x (-9) 13).toNat = 0 := by
        have r22692 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22693 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e22694 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b22695 := hb (x (-11) 3)
        have b22696 := hb (x (-10) 2)
        have b22697 := hb (x (-9) 13)
        have b22698 := hb (x (-8) 12)
        clear * - r22692 e22693 e22694 b22695 b22696 b22697 b22698 d22687
        omega
      have d22699 : (x (-9) 5).toNat = 0 := by
        have r22700 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
        have b22701 := hb (x (-9) 5)
        have b22702 := hb (x (-9) 13)
        clear * - r22700 b22701 b22702 d22691
        omega
      have d22703 : (x (-9) 5 && x (-9) 14).toNat = 0 := by
        have r22704 := hand1 (x (-9) 5) (x (-9) 14)
        have b22705 := hb (x (-9) 5)
        have b22706 := hb (x (-9) 5 && x (-9) 14)
        clear * - r22704 b22705 b22706 d22699
        omega
      have d22707 : (x (-10) 2).toNat = 0 := by
        have r22708 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22709 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e22710 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b22711 := hb (x (-11) 3)
        have b22712 := hb (x (-10) 2)
        have b22713 := hb (x (-9) 13)
        have b22714 := hb (x (-8) 12)
        clear * - r22708 e22709 e22710 b22711 b22712 b22713 b22714 d22687 d22691
        omega
      have d22715 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
        have r22716 := hand1 (x (-10) 2) (x (-10) 13)
        have b22717 := hb (x (-10) 2)
        have b22718 := hb (x (-10) 2 && x (-10) 13)
        clear * - r22716 b22717 b22718 d22707
        omega
      have d22719 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
        have r22720 := hand1 (x (-10) 2) (x (-10) 12)
        have b22721 := hb (x (-10) 2)
        have b22722 := hb (x (-10) 2 && x (-10) 12)
        clear * - r22720 b22721 b22722 d22707
        omega
      have d22723 : (x (-10) 10).toNat = 0 := by
        have r22724 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
        have b22725 := hb (x (-10) 2)
        have b22726 := hb (x (-10) 10)
        clear * - r22724 b22725 b22726 d22707
        omega
      have d22727 : (x (-11) 3).toNat = 0 := by
        have r22728 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22729 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e22730 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b22731 := hb (x (-11) 3)
        have b22732 := hb (x (-10) 2)
        have b22733 := hb (x (-9) 13)
        have b22734 := hb (x (-8) 12)
        clear * - r22728 e22729 e22730 b22731 b22732 b22733 b22734 d22687 d22691 d22707
        omega
      have d22735 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
        have r22736 := hand1 (x (-11) 3) (x (-11) 14)
        have b22737 := hb (x (-11) 3)
        have b22738 := hb (x (-11) 3 && x (-11) 14)
        clear * - r22736 b22737 b22738 d22727
        omega
      have d22739 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
        have r22740 := hand1 (x (-11) 3) (x (-11) 13)
        have b22741 := hb (x (-11) 3)
        have b22742 := hb (x (-11) 3 && x (-11) 13)
        clear * - r22740 b22741 b22742 d22727
        omega
      have d22743 : (x (-11) 11).toNat = 0 := by
        have r22744 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
        have b22745 := hb (x (-11) 3)
        have b22746 := hb (x (-11) 11)
        clear * - r22744 b22745 b22746 d22727
        omega
      have d22747 : (x (-5) 9).toNat = 0 := by
        have r22748 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
        have b22749 := hb (x (-5) 1)
        have b22750 := hb (x (-5) 9)
        clear * - r22748 b22749 b22750 d22672
        omega
      have d22751 : (x (-5) 9 && x (-5) 14).toNat = 0 := by
        have r22752 := hand1 (x (-5) 9) (x (-5) 14)
        have b22753 := hb (x (-5) 9)
        have b22754 := hb (x (-5) 9 && x (-5) 14)
        clear * - r22752 b22753 b22754 d22747
        omega
      have d22755 : (x (-6) 3).toNat = 0 := by
        have r22756 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22757 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e22758 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b22759 := hb (x (-6) 3)
        have b22760 := hb (x (-5) 2)
        have b22761 := hb (x (-4) 13)
        have b22762 := hb (x (-3) 12)
        clear * - r22756 e22757 e22758 b22759 b22760 b22761 b22762 d22635 d22345 d22647
        omega
      have d22763 : (x (-6) 11).toNat = 0 := by
        have r22764 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
        have b22765 := hb (x (-6) 3)
        have b22766 := hb (x (-6) 11)
        clear * - r22764 b22765 b22766 d22755
        omega
      have d22767 : (x 6 8).toNat = 0 := by
        have r22768 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22769 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e22770 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e22771 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e22772 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e22773 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e22774 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b22775 := hb (x (-1) 7)
        have b22776 := hb (x 0 6)
        have b22777 := hb (x 1 5)
        have b22778 := hb (x 2 4)
        have b22779 := hb (x 3 11)
        have b22780 := hb (x 4 10)
        have b22781 := hb (x 5 9)
        have b22782 := hb (x 6 8)
        clear * - r22768 e22769 e22770 e22771 e22772 e22773 e22774 b22775 b22776 b22777 b22778 b22779 b22780 b22781 b22782 d22437 d22402 g23 g19 f22333
        omega
      have d22783 : (x 5 9).toNat = 0 := by
        have r22784 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22785 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e22786 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e22787 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e22788 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e22789 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e22790 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b22791 := hb (x (-1) 7)
        have b22792 := hb (x 0 6)
        have b22793 := hb (x 1 5)
        have b22794 := hb (x 2 4)
        have b22795 := hb (x 3 11)
        have b22796 := hb (x 4 10)
        have b22797 := hb (x 5 9)
        have b22798 := hb (x 6 8)
        clear * - r22784 e22785 e22786 e22787 e22788 e22789 e22790 b22791 b22792 b22793 b22794 b22795 b22796 b22797 b22798 d22767 d22437 d22402 g23 g19 f22333
        omega
      have d22799 : (x 3 8).toNat = 0 := by
        have r22800 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22801 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
        have e22802 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
        have e22803 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
        have e22804 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
        have e22805 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
        have e22806 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
        have b22807 := hb (x (-4) 7)
        have b22808 := hb (x (-3) 6)
        have b22809 := hb (x (-2) 5)
        have b22810 := hb (x (-1) 4)
        have b22811 := hb (x 0 11)
        have b22812 := hb (x 1 10)
        have b22813 := hb (x 2 9)
        have b22814 := hb (x 3 8)
        clear * - r22800 e22801 e22802 e22803 e22804 e22805 e22806 b22807 b22808 b22809 b22810 b22811 b22812 b22813 b22814 d22539 g21 g15 d22398 d22382 d22369
        omega
      have d22815 : (x 3 8 && x 3 14).toNat = 0 := by
        have r22816 := hand1 (x 3 8) (x 3 14)
        have b22817 := hb (x 3 8)
        have b22818 := hb (x 3 8 && x 3 14)
        clear * - r22816 b22817 b22818 d22799
        omega
      have d22819 : (x 3 8 && x 3 12).toNat = 0 := by
        have r22820 := hand1 (x 3 8) (x 3 12)
        have b22821 := hb (x 3 8)
        have b22822 := hb (x 3 8 && x 3 12)
        clear * - r22820 b22821 b22822 d22799
        omega
      have d22823 : (x 1 8).toNat = 0 := by
        have r22824 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22825 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e22826 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e22827 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e22828 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e22829 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e22830 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b22831 := hb (x (-6) 7)
        have b22832 := hb (x (-5) 6)
        have b22833 := hb (x (-4) 5)
        have b22834 := hb (x (-3) 4)
        have b22835 := hb (x (-2) 11)
        have b22836 := hb (x (-1) 10)
        have b22837 := hb (x 0 9)
        have b22838 := hb (x 1 8)
        clear * - r22824 e22825 e22826 e22827 e22828 e22829 e22830 b22831 b22832 b22833 b22834 b22835 b22836 b22837 b22838 f22335 g10 g7 d22643 d22361
        omega
      have d22839 : (x (-4) 8).toNat = 0 := by
        have r22840 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22841 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e22842 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e22843 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e22844 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e22845 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e22846 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b22847 := hb (x (-11) 7)
        have b22848 := hb (x (-10) 6)
        have b22849 := hb (x (-9) 5)
        have b22850 := hb (x (-8) 4)
        have b22851 := hb (x (-7) 11)
        have b22852 := hb (x (-6) 10)
        have b22853 := hb (x (-5) 9)
        have b22854 := hb (x (-4) 8)
        clear * - r22840 e22841 e22842 e22843 e22844 e22845 e22846 b22847 b22848 b22849 b22850 b22851 b22852 b22853 b22854 d22747 g2 g0 d22680 d22699
        omega
      have d22855 : (x (-4) 8 && x (-4) 13).toNat = 0 := by
        have r22856 := hand1 (x (-4) 8) (x (-4) 13)
        have b22857 := hb (x (-4) 8)
        have b22858 := hb (x (-4) 8 && x (-4) 13)
        clear * - r22856 b22857 b22858 d22839
        omega
      have d22859 : (x (-4) 8 && x (-4) 12).toNat = 0 := by
        have r22860 := hand1 (x (-4) 8) (x (-4) 12)
        have b22861 := hb (x (-4) 8)
        have b22862 := hb (x (-4) 8 && x (-4) 12)
        clear * - r22860 b22861 b22862 d22839
        omega
      have d22863 : (x (-10) 6).toNat = 0 := by
        have r22864 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22865 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e22866 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e22867 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e22868 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e22869 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e22870 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b22871 := hb (x (-11) 7)
        have b22872 := hb (x (-10) 6)
        have b22873 := hb (x (-9) 5)
        have b22874 := hb (x (-8) 4)
        have b22875 := hb (x (-7) 11)
        have b22876 := hb (x (-6) 10)
        have b22877 := hb (x (-5) 9)
        have b22878 := hb (x (-4) 8)
        clear * - r22864 e22865 e22866 e22867 e22868 e22869 e22870 b22871 b22872 b22873 b22874 b22875 b22876 b22877 b22878 d22839 d22747 g2 g0 d22680 d22699
        omega
      have d22879 : (x 3 1 && x 3 6).toNat = 1 := by
        have r22880 : 1 ≤ (x 4 5).toNat + (x 3 1 && x 3 6).toNat + (x 2 2 && x 2 7).toNat + (x 1 3 && x 1 8).toNat + (x 0 4 && x 0 9).toNat + (x (-1) 5 && x (-1) 10).toNat + (x (-2) 6 && x (-2) 11).toNat + (x (-3) 7 && x (-3) 12).toNat + (x (-4) 8 && x (-4) 13).toNat + (x (-5) 9 && x (-5) 14).toNat + (x (-6) 10).toNat := by have q := hcov5 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22881 := hb (x (-6) 10)
        have b22882 := hb (x 4 5)
        have b22883 := hb (x 3 1 && x 3 6)
        have b22884 := hb (x 2 2 && x 2 7)
        have b22885 := hb (x 1 3 && x 1 8)
        have b22886 := hb (x 0 4 && x 0 9)
        have b22887 := hb (x (-1) 5 && x (-1) 10)
        have b22888 := hb (x (-2) 6 && x (-2) 11)
        have b22889 := hb (x (-3) 7 && x (-3) 12)
        have b22890 := hb (x (-4) 8 && x (-4) 13)
        have b22891 := hb (x (-5) 9 && x (-5) 14)
        clear * - r22880 b22881 b22882 b22883 b22884 b22885 b22886 b22887 b22888 b22889 b22890 b22891 d22583 d22503 d22519 g30 g31 g32 d22328 d22855 d22751 g2
        omega
      have d22892 : (x 3 6).toNat = 1 := by
        have r22893 := hand2 (x 3 1) (x 3 6)
        have b22894 := hb (x 3 6)
        have b22895 := hb (x 3 1 && x 3 6)
        clear * - r22893 b22894 b22895 d22879
        omega
      have d22896 : (x 9 8).toNat = 0 := by
        have r22897 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22898 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e22899 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e22900 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e22901 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e22902 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e22903 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b22904 := hb (x 2 7)
        have b22905 := hb (x 3 6)
        have b22906 := hb (x 4 5)
        have b22907 := hb (x 5 4)
        have b22908 := hb (x 6 11)
        have b22909 := hb (x 7 10)
        have b22910 := hb (x 8 9)
        have b22911 := hb (x 9 8)
        clear * - r22897 e22898 e22899 e22900 e22901 e22902 e22903 b22904 b22905 b22906 b22907 b22908 b22909 b22910 b22911 d22559 d22583 d22892
        omega
      have d22912 : (x 9 2 && x 9 8).toNat = 0 := by
        have r22913 := hand2 (x 9 2) (x 9 8)
        have b22914 := hb (x 9 8)
        have b22915 := hb (x 9 2 && x 9 8)
        clear * - r22913 b22914 b22915 d22896
        omega
      have d22916 : (x 8 9).toNat = 0 := by
        have r22917 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22918 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e22919 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e22920 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e22921 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e22922 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e22923 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b22924 := hb (x 2 7)
        have b22925 := hb (x 3 6)
        have b22926 := hb (x 4 5)
        have b22927 := hb (x 5 4)
        have b22928 := hb (x 6 11)
        have b22929 := hb (x 7 10)
        have b22930 := hb (x 8 9)
        have b22931 := hb (x 9 8)
        clear * - r22917 e22918 e22919 e22920 e22921 e22922 e22923 b22924 b22925 b22926 b22927 b22928 b22929 b22930 b22931 d22896 d22559 d22583 d22892
        omega
      have d22932 : (x 8 3 && x 8 9).toNat = 0 := by
        have r22933 := hand2 (x 8 3) (x 8 9)
        have b22934 := hb (x 8 9)
        have b22935 := hb (x 8 3 && x 8 9)
        clear * - r22933 b22934 b22935 d22916
        omega
      have d22936 : (x 7 10).toNat = 0 := by
        have r22937 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22938 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e22939 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e22940 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e22941 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e22942 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e22943 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b22944 := hb (x 2 7)
        have b22945 := hb (x 3 6)
        have b22946 := hb (x 4 5)
        have b22947 := hb (x 5 4)
        have b22948 := hb (x 6 11)
        have b22949 := hb (x 7 10)
        have b22950 := hb (x 8 9)
        have b22951 := hb (x 9 8)
        clear * - r22937 e22938 e22939 e22940 e22941 e22942 e22943 b22944 b22945 b22946 b22947 b22948 b22949 b22950 b22951 d22896 d22916 d22559 d22583 d22892
        omega
      have d22952 : (x 7 4 && x 7 10).toNat = 0 := by
        have r22953 := hand2 (x 7 4) (x 7 10)
        have b22954 := hb (x 7 10)
        have b22955 := hb (x 7 4 && x 7 10)
        clear * - r22953 b22954 b22955 d22936
        omega
      have d22956 : (x 6 11).toNat = 0 := by
        have r22957 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22958 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e22959 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e22960 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e22961 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e22962 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e22963 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b22964 := hb (x 2 7)
        have b22965 := hb (x 3 6)
        have b22966 := hb (x 4 5)
        have b22967 := hb (x 5 4)
        have b22968 := hb (x 6 11)
        have b22969 := hb (x 7 10)
        have b22970 := hb (x 8 9)
        have b22971 := hb (x 9 8)
        clear * - r22957 e22958 e22959 e22960 e22961 e22962 e22963 b22964 b22965 b22966 b22967 b22968 b22969 b22970 b22971 d22896 d22916 d22936 d22559 d22583 d22892
        omega
      have d22972 : (x 6 1 && x 6 11).toNat = 0 := by
        have r22973 := hand2 (x 6 1) (x 6 11)
        have b22974 := hb (x 6 11)
        have b22975 := hb (x 6 1 && x 6 11)
        clear * - r22973 b22974 b22975 d22956
        omega
      have d22976 : (x 3 4 && x 3 14).toNat = 1 := by
        have r22977 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22978 := hb (x 2 5)
        have b22979 := hb (x 7 10)
        have b22980 := hb (x 6 1 && x 6 11)
        have b22981 := hb (x 5 2 && x 5 12)
        have b22982 := hb (x 4 3 && x 4 13)
        have b22983 := hb (x 3 4 && x 3 14)
        clear * - r22977 b22978 b22979 b22980 b22981 b22982 b22983 d22936 d22972 d22551 d22575 d22535
        omega
      have d22984 : (x 3 4).toNat = 1 := by
        have r22985 := hand1 (x 3 4) (x 3 14)
        have b22986 := hb (x 3 4)
        have b22987 := hb (x 3 4 && x 3 14)
        clear * - r22985 b22986 b22987 d22976
        omega
      have d22988 : (x 7 8).toNat = 0 := by
        have r22989 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22990 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e22991 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e22992 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e22993 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e22994 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e22995 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b22996 := hb (x 0 7)
        have b22997 := hb (x 1 6)
        have b22998 := hb (x 2 5)
        have b22999 := hb (x 3 4)
        have b23000 := hb (x 4 11)
        have b23001 := hb (x 5 10)
        have b23002 := hb (x 6 9)
        have b23003 := hb (x 7 8)
        clear * - r22989 e22990 e22991 e22992 e22993 e22994 e22995 b22996 b22997 b22998 b22999 b23000 b23001 b23002 b23003 d22984 d22535 g20
        omega
      have d23004 : (x 7 4 && x 7 8).toNat = 0 := by
        have r23005 := hand2 (x 7 4) (x 7 8)
        have b23006 := hb (x 7 8)
        have b23007 := hb (x 7 4 && x 7 8)
        clear * - r23005 b23006 b23007 d22988
        omega
      have d23008 : (x 6 9).toNat = 0 := by
        have r23009 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23010 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e23011 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e23012 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e23013 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e23014 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e23015 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b23016 := hb (x 0 7)
        have b23017 := hb (x 1 6)
        have b23018 := hb (x 2 5)
        have b23019 := hb (x 3 4)
        have b23020 := hb (x 4 11)
        have b23021 := hb (x 5 10)
        have b23022 := hb (x 6 9)
        have b23023 := hb (x 7 8)
        clear * - r23009 e23010 e23011 e23012 e23013 e23014 e23015 b23016 b23017 b23018 b23019 b23020 b23021 b23022 b23023 d22988 d22984 d22535 g20
        omega
      have d23024 : (x 6 5 && x 6 9).toNat = 0 := by
        have r23025 := hand2 (x 6 5) (x 6 9)
        have b23026 := hb (x 6 9)
        have b23027 := hb (x 6 5 && x 6 9)
        clear * - r23025 b23026 b23027 d23008
        omega
      have d23028 : (x 5 10).toNat = 0 := by
        have r23029 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23030 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e23031 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e23032 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e23033 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e23034 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e23035 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b23036 := hb (x 0 7)
        have b23037 := hb (x 1 6)
        have b23038 := hb (x 2 5)
        have b23039 := hb (x 3 4)
        have b23040 := hb (x 4 11)
        have b23041 := hb (x 5 10)
        have b23042 := hb (x 6 9)
        have b23043 := hb (x 7 8)
        clear * - r23029 e23030 e23031 e23032 e23033 e23034 e23035 b23036 b23037 b23038 b23039 b23040 b23041 b23042 b23043 d22988 d23008 d22984 d22535 g20
        omega
      have d23044 : (x 5 6 && x 5 10).toNat = 0 := by
        have r23045 := hand2 (x 5 6) (x 5 10)
        have b23046 := hb (x 5 10)
        have b23047 := hb (x 5 6 && x 5 10)
        clear * - r23045 b23046 b23047 d23028
        omega
      have d23048 : (x 4 11).toNat = 0 := by
        have r23049 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23050 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e23051 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e23052 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e23053 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e23054 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e23055 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b23056 := hb (x 0 7)
        have b23057 := hb (x 1 6)
        have b23058 := hb (x 2 5)
        have b23059 := hb (x 3 4)
        have b23060 := hb (x 4 11)
        have b23061 := hb (x 5 10)
        have b23062 := hb (x 6 9)
        have b23063 := hb (x 7 8)
        clear * - r23049 e23050 e23051 e23052 e23053 e23054 e23055 b23056 b23057 b23058 b23059 b23060 b23061 b23062 b23063 d22988 d23008 d23028 d22984 d22535 g20
        omega
      have d23064 : (x 4 7 && x 4 11).toNat = 0 := by
        have r23065 := hand2 (x 4 7) (x 4 11)
        have b23066 := hb (x 4 11)
        have b23067 := hb (x 4 7 && x 4 11)
        clear * - r23065 b23066 b23067 d23048
        omega
      have d23068 : (x 0 7).toNat = 0 := by
        have r23069 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23070 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e23071 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e23072 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e23073 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e23074 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e23075 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b23076 := hb (x 0 7)
        have b23077 := hb (x 1 6)
        have b23078 := hb (x 2 5)
        have b23079 := hb (x 3 4)
        have b23080 := hb (x 4 11)
        have b23081 := hb (x 5 10)
        have b23082 := hb (x 6 9)
        have b23083 := hb (x 7 8)
        clear * - r23069 e23070 e23071 e23072 e23073 e23074 e23075 b23076 b23077 b23078 b23079 b23080 b23081 b23082 b23083 d22988 d23008 d23028 d23048 d22984 d22535 g20
        omega
      have d23084 : (x (-8) 8).toNat = 1 := by
        have r23085 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23086 := hb (x (-8) 8)
        have b23087 := hb (x 0 7)
        have b23088 := hb (x (-1) 1 && x (-1) 8)
        have b23089 := hb (x (-2) 2 && x (-2) 9)
        have b23090 := hb (x (-3) 3 && x (-3) 10)
        have b23091 := hb (x (-4) 4 && x (-4) 11)
        have b23092 := hb (x (-5) 5 && x (-5) 12)
        have b23093 := hb (x (-6) 6 && x (-6) 13)
        have b23094 := hb (x (-7) 7 && x (-7) 14)
        clear * - r23085 b23086 b23087 b23088 b23089 b23090 b23091 b23092 b23093 b23094 d23068 g36 g37 g38 d22631 g39 g40 g41
        omega
      have d23095 : (x (-9) 9).toNat = 0 := by
        have r23096 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23097 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e23098 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e23099 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e23100 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e23101 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e23102 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b23103 := hb (x (-15) 7)
        have b23104 := hb (x (-14) 6)
        have b23105 := hb (x (-13) 5)
        have b23106 := hb (x (-12) 4)
        have b23107 := hb (x (-11) 11)
        have b23108 := hb (x (-10) 10)
        have b23109 := hb (x (-9) 9)
        have b23110 := hb (x (-8) 8)
        clear * - r23096 e23097 e23098 e23099 e23100 e23101 e23102 b23103 b23104 b23105 b23106 b23107 b23108 b23109 b23110 d23084 d22723 d22743
        omega
      have d23111 : (x (-12) 4).toNat = 0 := by
        have r23112 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23113 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e23114 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e23115 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e23116 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e23117 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e23118 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b23119 := hb (x (-15) 7)
        have b23120 := hb (x (-14) 6)
        have b23121 := hb (x (-13) 5)
        have b23122 := hb (x (-12) 4)
        have b23123 := hb (x (-11) 11)
        have b23124 := hb (x (-10) 10)
        have b23125 := hb (x (-9) 9)
        have b23126 := hb (x (-8) 8)
        clear * - r23112 e23113 e23114 e23115 e23116 e23117 e23118 b23119 b23120 b23121 b23122 b23123 b23124 b23125 b23126 d23084 d23095 d22723 d22743
        omega
      have d23127 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
        have r23128 := hand1 (x (-12) 4) (x (-12) 14)
        have b23129 := hb (x (-12) 4)
        have b23130 := hb (x (-12) 4 && x (-12) 14)
        clear * - r23128 b23129 b23130 d23111
        omega
      have d23131 : (x (-13) 5).toNat = 0 := by
        have r23132 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23133 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
        have e23134 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
        have e23135 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
        have e23136 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
        have e23137 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
        have e23138 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
        have b23139 := hb (x (-15) 7)
        have b23140 := hb (x (-14) 6)
        have b23141 := hb (x (-13) 5)
        have b23142 := hb (x (-12) 4)
        have b23143 := hb (x (-11) 11)
        have b23144 := hb (x (-10) 10)
        have b23145 := hb (x (-9) 9)
        have b23146 := hb (x (-8) 8)
        clear * - r23132 e23133 e23134 e23135 e23136 e23137 e23138 b23139 b23140 b23141 b23142 b23143 b23144 b23145 b23146 d23084 d23095 d22723 d22743 d23111
        omega
      have d23147 : (x 6 5 && x 6 11).toNat = 0 := by
        have r23148 := hand2 (x 6 5) (x 6 11)
        have b23149 := hb (x 6 11)
        have b23150 := hb (x 6 5 && x 6 11)
        clear * - r23148 b23149 b23150 d22956
        omega
      have d23151 : (x 2 7).toNat = 0 := by
        have r23152 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23153 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e23154 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e23155 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e23156 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e23157 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e23158 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b23159 := hb (x 2 7)
        have b23160 := hb (x 3 6)
        have b23161 := hb (x 4 5)
        have b23162 := hb (x 5 4)
        have b23163 := hb (x 6 11)
        have b23164 := hb (x 7 10)
        have b23165 := hb (x 8 9)
        have b23166 := hb (x 9 8)
        clear * - r23152 e23153 e23154 e23155 e23156 e23157 e23158 b23159 b23160 b23161 b23162 b23163 b23164 b23165 b23166 d22896 d22916 d22936 d22956 d22559 d22583 d22892
        omega
      have d23167 : (x 3 5).toNat = 1 := by
        have r23168 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23169 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
        have e23170 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
        have b23171 := hb (x (-7) 11)
        have b23172 := hb (x (-6) 10)
        have b23173 := hb (x 3 5)
        have b23174 := hb (x 4 4)
        have b23175 := hb (x 2 2 && x 2 6)
        have b23176 := hb (x 1 3 && x 1 7)
        have b23177 := hb (x 0 4 && x 0 8)
        have b23178 := hb (x (-1) 5 && x (-1) 9)
        have b23179 := hb (x (-2) 6 && x (-2) 10)
        have b23180 := hb (x (-3) 7 && x (-3) 11)
        have b23181 := hb (x (-4) 8 && x (-4) 12)
        have b23182 := hb (x (-5) 9 && x (-5) 13)
        clear * - r23168 e23169 e23170 b23171 b23172 b23173 b23174 b23175 b23176 b23177 b23178 b23179 b23180 b23181 b23182 d22491 d22507 d22523 g25 g26 g27 g28 d22859 g29 g2 g0
        omega
      have d23183 : (x 8 8).toNat = 0 := by
        have r23184 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23185 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e23186 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e23187 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e23188 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e23189 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e23190 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b23191 := hb (x 1 7)
        have b23192 := hb (x 2 6)
        have b23193 := hb (x 3 5)
        have b23194 := hb (x 4 4)
        have b23195 := hb (x 5 11)
        have b23196 := hb (x 6 10)
        have b23197 := hb (x 7 9)
        have b23198 := hb (x 8 8)
        clear * - r23184 e23185 e23186 e23187 e23188 e23189 e23190 b23191 b23192 b23193 b23194 b23195 b23196 b23197 b23198 d22491 d23167
        omega
      have d23199 : (x 7 9).toNat = 0 := by
        have r23200 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23201 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e23202 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e23203 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e23204 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e23205 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e23206 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b23207 := hb (x 1 7)
        have b23208 := hb (x 2 6)
        have b23209 := hb (x 3 5)
        have b23210 := hb (x 4 4)
        have b23211 := hb (x 5 11)
        have b23212 := hb (x 6 10)
        have b23213 := hb (x 7 9)
        have b23214 := hb (x 8 8)
        clear * - r23200 e23201 e23202 e23203 e23204 e23205 e23206 b23207 b23208 b23209 b23210 b23211 b23212 b23213 b23214 d23183 d22491 d23167
        omega
      have d23215 : (x 6 10).toNat = 0 := by
        have r23216 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23217 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e23218 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e23219 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e23220 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e23221 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e23222 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b23223 := hb (x 1 7)
        have b23224 := hb (x 2 6)
        have b23225 := hb (x 3 5)
        have b23226 := hb (x 4 4)
        have b23227 := hb (x 5 11)
        have b23228 := hb (x 6 10)
        have b23229 := hb (x 7 9)
        have b23230 := hb (x 8 8)
        clear * - r23216 e23217 e23218 e23219 e23220 e23221 e23222 b23223 b23224 b23225 b23226 b23227 b23228 b23229 b23230 d23183 d23199 d22491 d23167
        omega
      have d23231 : (x 5 11).toNat = 0 := by
        have r23232 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23233 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e23234 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e23235 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e23236 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e23237 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e23238 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b23239 := hb (x 1 7)
        have b23240 := hb (x 2 6)
        have b23241 := hb (x 3 5)
        have b23242 := hb (x 4 4)
        have b23243 := hb (x 5 11)
        have b23244 := hb (x 6 10)
        have b23245 := hb (x 7 9)
        have b23246 := hb (x 8 8)
        clear * - r23232 e23233 e23234 e23235 e23236 e23237 e23238 b23239 b23240 b23241 b23242 b23243 b23244 b23245 b23246 d23183 d23199 d23215 d22491 d23167
        omega
      have d23247 : (x 2 6).toNat = 0 := by
        have r23248 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23249 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e23250 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e23251 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e23252 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e23253 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e23254 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b23255 := hb (x 1 7)
        have b23256 := hb (x 2 6)
        have b23257 := hb (x 3 5)
        have b23258 := hb (x 4 4)
        have b23259 := hb (x 5 11)
        have b23260 := hb (x 6 10)
        have b23261 := hb (x 7 9)
        have b23262 := hb (x 8 8)
        clear * - r23248 e23249 e23250 e23251 e23252 e23253 e23254 b23255 b23256 b23257 b23258 b23259 b23260 b23261 b23262 d23183 d23199 d23215 d23231 d22491 d23167
        omega
      have d23263 : (x 1 7).toNat = 0 := by
        have r23264 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23265 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e23266 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e23267 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e23268 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e23269 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e23270 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b23271 := hb (x 1 7)
        have b23272 := hb (x 2 6)
        have b23273 := hb (x 3 5)
        have b23274 := hb (x 4 4)
        have b23275 := hb (x 5 11)
        have b23276 := hb (x 6 10)
        have b23277 := hb (x 7 9)
        have b23278 := hb (x 8 8)
        clear * - r23264 e23265 e23266 e23267 e23268 e23269 e23270 b23271 b23272 b23273 b23274 b23275 b23276 b23277 b23278 d23183 d23199 d23215 d23231 d22491 d23167 d23247
        omega
      have d23279 : (x (-10) 14).toNat = 0 := by
        have r23280 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23281 := hb (x (-10) 14)
        have b23282 := hb (x (-9) 13)
        have b23283 := hb (x (-8) 12)
        have b23284 := hb (x (-7) 11)
        have b23285 := hb (x (-6) 10)
        have b23286 := hb (x (-5) 9)
        have b23287 := hb (x (-4) 8)
        have b23288 := hb (x (-3) 7)
        have b23289 := hb (x (-2) 6)
        have b23290 := hb (x (-1) 5)
        have b23291 := hb (x 0 4)
        have b23292 := hb (x 1 3)
        have b23293 := hb (x 2 2)
        have b23294 := hb (x 3 1)
        clear * - r23280 b23281 b23282 b23283 b23284 b23285 b23286 b23287 b23288 b23289 b23290 b23291 b23292 b23293 b23294 d22449 d22495 d22511 g12 g8 d22179 d22312 d22839 d22747 g2 g0 d22687 d22691
        omega
      have d23295 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
        have r23296 := hand2 (x (-10) 1) (x (-10) 14)
        have b23297 := hb (x (-10) 14)
        have b23298 := hb (x (-10) 1 && x (-10) 14)
        clear * - r23296 b23297 b23298 d23279
        omega
      have d23299 : (x (-11) 2).toNat = 1 := by
        have r23300 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23301 := hb (x (-11) 2)
        have b23302 := hb (x (-9) 13)
        have b23303 := hb (x (-10) 1 && x (-10) 14)
        clear * - r23300 b23301 b23302 b23303 d22691 d23295
        omega
      have d23304 : (x (-9) 12).toNat = 0 := by
        have r23305 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23306 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
        have e23307 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
        have b23308 := hb (x (-12) 3)
        have b23309 := hb (x (-11) 2)
        have b23310 := hb (x (-10) 13)
        have b23311 := hb (x (-9) 12)
        clear * - r23305 e23306 e23307 b23308 b23309 b23310 b23311 d23299
        omega
      have d23312 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
        have r23313 := hand2 (x (-9) 1) (x (-9) 12)
        have b23314 := hb (x (-9) 12)
        have b23315 := hb (x (-9) 1 && x (-9) 12)
        clear * - r23313 b23314 b23315 d23304
        omega
      have d23316 : (x (-8) 11).toNat = 1 := by
        have r23317 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23318 := hb (x (-12) 4)
        have b23319 := hb (x (-8) 11)
        have b23320 := hb (x (-9) 1 && x (-9) 12)
        have b23321 := hb (x (-10) 2 && x (-10) 13)
        have b23322 := hb (x (-11) 3 && x (-11) 14)
        clear * - r23317 b23318 b23319 b23320 b23321 b23322 d23312 d22715 d22735 d23111
        omega
      have d23323 : (x (-8) 3).toNat = 1 := by
        have r23324 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
        have b23325 := hb (x (-8) 3)
        have b23326 := hb (x (-8) 11)
        clear * - r23324 b23325 b23326 d23316
        omega
      have d23327 : (x (-5) 12).toNat = 0 := by
        have r23328 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23329 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e23330 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b23331 := hb (x (-8) 3)
        have b23332 := hb (x (-7) 2)
        have b23333 := hb (x (-6) 13)
        have b23334 := hb (x (-5) 12)
        clear * - r23328 e23329 e23330 b23331 b23332 b23333 b23334 d23323
        omega
      have d23335 : (x (-5) 4).toNat = 0 := by
        have r23336 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have b23337 := hb (x (-5) 4)
        have b23338 := hb (x (-5) 12)
        clear * - r23336 b23337 b23338 d23327
        omega
      have d23339 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
        have r23340 := hand1 (x (-5) 4) (x (-5) 14)
        have b23341 := hb (x (-5) 4)
        have b23342 := hb (x (-5) 4 && x (-5) 14)
        clear * - r23340 b23341 b23342 d23335
        omega
      have d23343 : (x (-6) 5).toNat = 1 := by
        have r23344 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23345 := hb (x (-6) 5)
        have b23346 := hb (x (-1) 10)
        have b23347 := hb (x (-2) 1 && x (-2) 11)
        have b23348 := hb (x (-3) 2 && x (-3) 12)
        have b23349 := hb (x (-4) 3 && x (-4) 13)
        have b23350 := hb (x (-5) 4 && x (-5) 14)
        clear * - r23344 b23345 b23346 b23347 b23348 b23349 b23350 g10 g57 d22603 d22619 d23339
        omega
      have d23351 : (x (-6) 13).toNat = 1 := by
        have r23352 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
        have b23353 := hb (x (-6) 5)
        have b23354 := hb (x (-6) 13)
        clear * - r23352 b23353 b23354 d23343
        omega
      have d23355 : (x (-6) 1).toNat = 1 := by
        have r23356 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
        have b23357 := hb (x (-6) 1)
        have b23358 := hb (x (-6) 13)
        clear * - r23356 b23357 b23358 d23351
        omega
      have d23359 : (x (-5) 14).toNat = 0 := by
        have r23360 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23361 := hb (x (-6) 1)
        have b23362 := hb (x (-5) 14)
        clear * - r23360 b23361 b23362 d23355
        omega
      have d23363 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
        have r23364 := hand2 (x (-5) 3) (x (-5) 14)
        have b23365 := hb (x (-5) 14)
        have b23366 := hb (x (-5) 3 && x (-5) 14)
        clear * - r23364 b23365 b23366 d23359
        omega
      have d23367 : (x (-2) 1 && x (-2) 12).toNat = 1 := by
        have r23368 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23369 := hb (x (-5) 4)
        have b23370 := hb (x (-1) 11)
        have b23371 := hb (x (-2) 1 && x (-2) 12)
        have b23372 := hb (x (-3) 2 && x (-3) 13)
        have b23373 := hb (x (-4) 3 && x (-4) 14)
        clear * - r23368 b23369 b23370 b23371 b23372 b23373 g11 d22204 d22615 d23335
        omega
      have d23374 : (x (-2) 12).toNat = 1 := by
        have r23375 := hand2 (x (-2) 1) (x (-2) 12)
        have b23376 := hb (x (-2) 12)
        have b23377 := hb (x (-2) 1 && x (-2) 12)
        clear * - r23375 b23376 b23377 d23367
        omega
      have d23378 : (x (-4) 2).toNat = 0 := by
        have r23379 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23380 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e23381 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b23382 := hb (x (-5) 3)
        have b23383 := hb (x (-4) 2)
        have b23384 := hb (x (-3) 13)
        have b23385 := hb (x (-2) 12)
        clear * - r23379 e23380 e23381 b23382 b23383 b23384 b23385 d23374 d22200
        omega
      have d23386 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
        have r23387 := hand1 (x (-4) 2) (x (-4) 13)
        have b23388 := hb (x (-4) 2)
        have b23389 := hb (x (-4) 2 && x (-4) 13)
        clear * - r23387 b23388 b23389 d23378
        omega
      have d23390 : (x (-6) 4).toNat = 1 := by
        have r23391 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23392 := hb (x (-6) 4)
        have b23393 := hb (x (-2) 11)
        have b23394 := hb (x (-3) 1 && x (-3) 12)
        have b23395 := hb (x (-4) 2 && x (-4) 13)
        have b23396 := hb (x (-5) 3 && x (-5) 14)
        clear * - r23391 b23392 b23393 b23394 b23395 b23396 g7 d22196 d23386 d23363
        omega
      have d23397 : (x (-6) 12).toNat = 1 := by
        have r23398 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
        have b23399 := hb (x (-6) 4)
        have b23400 := hb (x (-6) 12)
        clear * - r23398 b23399 b23400 d23390
        omega
      have d23401 : (x (-7) 13).toNat = 0 := by
        have r23402 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23403 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e23404 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b23405 := hb (x (-9) 3)
        have b23406 := hb (x (-8) 2)
        have b23407 := hb (x (-7) 13)
        have b23408 := hb (x (-6) 12)
        clear * - r23402 e23403 e23404 b23405 b23406 b23407 b23408 d23397
        omega
      have d23409 : (x (-8) 2).toNat = 0 := by
        have r23410 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23411 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e23412 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b23413 := hb (x (-9) 3)
        have b23414 := hb (x (-8) 2)
        have b23415 := hb (x (-7) 13)
        have b23416 := hb (x (-6) 12)
        clear * - r23410 e23411 e23412 b23413 b23414 b23415 b23416 d23397 d23401
        omega
      have d23417 : (x (-8) 10).toNat = 0 := by
        have r23418 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
        have b23419 := hb (x (-8) 2)
        have b23420 := hb (x (-8) 10)
        clear * - r23418 b23419 b23420 d23409
        omega
      have d23421 : (x (-9) 1 && x (-9) 11).toNat = 1 := by
        have r23422 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23423 := hb (x (-13) 5)
        have b23424 := hb (x (-8) 10)
        have b23425 := hb (x (-9) 1 && x (-9) 11)
        have b23426 := hb (x (-10) 2 && x (-10) 12)
        have b23427 := hb (x (-11) 3 && x (-11) 13)
        have b23428 := hb (x (-12) 4 && x (-12) 14)
        clear * - r23422 b23423 b23424 b23425 b23426 b23427 b23428 d23417 d22719 d22739 d23127 d23131
        omega
      have d23429 : (x (-9) 1).toNat = 1 := by
        have r23430 := hand1 (x (-9) 1) (x (-9) 11)
        have b23431 := hb (x (-9) 1)
        have b23432 := hb (x (-9) 1 && x (-9) 11)
        clear * - r23430 b23431 b23432 d23421
        omega
      have d23433 : (x (-8) 14).toNat = 0 := by
        have r23434 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23435 := hb (x (-9) 1)
        have b23436 := hb (x (-8) 14)
        clear * - r23434 b23435 b23436 d23429
        omega
      have d23437 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
        have r23438 := hand2 (x (-8) 1) (x (-8) 14)
        have b23439 := hb (x (-8) 14)
        have b23440 := hb (x (-8) 1 && x (-8) 14)
        clear * - r23438 b23439 b23440 d23433
        omega
      have d23441 : (x (-9) 2).toNat = 1 := by
        have r23442 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23443 := hb (x (-9) 2)
        have b23444 := hb (x (-7) 13)
        have b23445 := hb (x (-8) 1 && x (-8) 14)
        clear * - r23442 b23443 b23444 b23445 d23401 d23437
        omega
      have d23446 : (x (-9) 14).toNat = 1 := by
        have r23447 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
        have b23448 := hb (x (-9) 2)
        have b23449 := hb (x (-9) 14)
        clear * - r23447 b23448 b23449 d23441
        omega
      have d23450 : (x 4 1).toNat = 0 := by
        have r23451 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23452 := hb (x (-9) 14)
        have b23453 := hb (x (-8) 13)
        have b23454 := hb (x (-7) 12)
        have b23455 := hb (x (-6) 11)
        have b23456 := hb (x (-5) 10)
        have b23457 := hb (x (-4) 9)
        have b23458 := hb (x (-3) 8)
        have b23459 := hb (x (-2) 7)
        have b23460 := hb (x (-1) 6)
        have b23461 := hb (x 0 5)
        have b23462 := hb (x 1 4)
        have b23463 := hb (x 2 3)
        have b23464 := hb (x 3 2)
        have b23465 := hb (x 4 1)
        clear * - r23451 b23452 b23453 b23454 b23455 b23456 b23457 b23458 b23459 b23460 b23461 b23462 b23463 b23464 b23465 d22461 d22587 g18 g13 d22212 d22228 d22655 d22763 d23446
        omega
      have d23466 : (x (-3) 8).toNat = 0 := by
        have r23467 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23468 := hb (x (-9) 14)
        have b23469 := hb (x (-8) 13)
        have b23470 := hb (x (-7) 12)
        have b23471 := hb (x (-6) 11)
        have b23472 := hb (x (-5) 10)
        have b23473 := hb (x (-4) 9)
        have b23474 := hb (x (-3) 8)
        have b23475 := hb (x (-2) 7)
        have b23476 := hb (x (-1) 6)
        have b23477 := hb (x 0 5)
        have b23478 := hb (x 1 4)
        have b23479 := hb (x 2 3)
        have b23480 := hb (x 3 2)
        have b23481 := hb (x 4 1)
        clear * - r23467 b23468 b23469 b23470 b23471 b23472 b23473 b23474 b23475 b23476 b23477 b23478 b23479 b23480 b23481 d23450 d22461 d22587 g18 g13 d22212 d22228 d22655 d22763 d23446
        omega
      have d23482 : (x (-4) 9).toNat = 0 := by
        have r23483 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23484 := hb (x (-9) 14)
        have b23485 := hb (x (-8) 13)
        have b23486 := hb (x (-7) 12)
        have b23487 := hb (x (-6) 11)
        have b23488 := hb (x (-5) 10)
        have b23489 := hb (x (-4) 9)
        have b23490 := hb (x (-3) 8)
        have b23491 := hb (x (-2) 7)
        have b23492 := hb (x (-1) 6)
        have b23493 := hb (x 0 5)
        have b23494 := hb (x 1 4)
        have b23495 := hb (x 2 3)
        have b23496 := hb (x 3 2)
        have b23497 := hb (x 4 1)
        clear * - r23483 b23484 b23485 b23486 b23487 b23488 b23489 b23490 b23491 b23492 b23493 b23494 b23495 b23496 b23497 d23450 d22461 d22587 g18 g13 d22212 d22228 d23466 d22655 d22763 d23446
        omega
      have d23498 : (x (-8) 4 && x (-8) 13).toNat = 1 := by
        have r23499 : 1 ≤ (x (-4) 9).toNat + (x (-5) 1 && x (-5) 10).toNat + (x (-6) 2 && x (-6) 11).toNat + (x (-7) 3 && x (-7) 12).toNat + (x (-8) 4 && x (-8) 13).toNat + (x (-9) 5 && x (-9) 14).toNat + (x (-10) 6).toNat := by have q := hcov9 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23500 := hb (x (-10) 6)
        have b23501 := hb (x (-4) 9)
        have b23502 := hb (x (-5) 1 && x (-5) 10)
        have b23503 := hb (x (-6) 2 && x (-6) 11)
        have b23504 := hb (x (-7) 3 && x (-7) 12)
        have b23505 := hb (x (-8) 4 && x (-8) 13)
        have b23506 := hb (x (-9) 5 && x (-9) 14)
        clear * - r23499 b23500 b23501 b23502 b23503 b23504 b23505 b23506 d23482 d22659 g42 g43 d22703 d22863
        omega
      have d23507 : (x (-8) 13).toNat = 1 := by
        have r23508 := hand2 (x (-8) 4) (x (-8) 13)
        have b23509 := hb (x (-8) 13)
        have b23510 := hb (x (-8) 4 && x (-8) 13)
        clear * - r23508 b23509 b23510 d23498
        omega
      have d23511 : (x (-8) 1).toNat = 1 := by
        have r23512 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b23513 := hb (x (-8) 1)
        have b23514 := hb (x (-8) 13)
        clear * - r23512 b23513 b23514 d23507
        omega
      have d23515 : (x (-7) 14).toNat = 0 := by
        have r23516 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23517 := hb (x (-8) 1)
        have b23518 := hb (x (-7) 14)
        clear * - r23516 b23517 b23518 d23511
        omega
      have d23519 : (x (-7) 6).toNat = 0 := by
        have r23520 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
        have b23521 := hb (x (-7) 6)
        have b23522 := hb (x (-7) 14)
        clear * - r23520 b23521 b23522 d23515
        omega
      have d23523 : (x (-6) 5 && x (-6) 14).toNat = 1 := by
        have r23524 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23525 := hb (x (-7) 6)
        have b23526 := hb (x (-1) 9)
        have b23527 := hb (x (-2) 1 && x (-2) 10)
        have b23528 := hb (x (-3) 2 && x (-3) 11)
        have b23529 := hb (x (-4) 3 && x (-4) 12)
        have b23530 := hb (x (-5) 4 && x (-5) 13)
        have b23531 := hb (x (-6) 5 && x (-6) 14)
        clear * - r23524 b23525 b23526 b23527 b23528 b23529 b23530 b23531 g9 g44 g45 d22623 g46 d23519
        omega
      have d23532 : (x (-6) 14).toNat = 1 := by
        have r23533 := hand2 (x (-6) 5) (x (-6) 14)
        have b23534 := hb (x (-6) 14)
        have b23535 := hb (x (-6) 5 && x (-6) 14)
        clear * - r23533 b23534 b23535 d23523
        omega
      have d23536 : (x 7 1).toNat = 0 := by
        have r23537 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23538 := hb (x (-6) 14)
        have b23539 := hb (x (-5) 13)
        have b23540 := hb (x (-4) 12)
        have b23541 := hb (x (-3) 11)
        have b23542 := hb (x (-2) 10)
        have b23543 := hb (x (-1) 9)
        have b23544 := hb (x 0 8)
        have b23545 := hb (x 1 7)
        have b23546 := hb (x 2 6)
        have b23547 := hb (x 3 5)
        have b23548 := hb (x 4 4)
        have b23549 := hb (x 5 3)
        have b23550 := hb (x 6 2)
        have b23551 := hb (x 7 1)
        clear * - r23537 b23538 b23539 b23540 b23541 b23542 b23543 b23544 b23545 b23546 b23547 b23548 b23549 b23550 b23551 d22491 d23167 d23247 d23263 g14 g9 g6 g5 g4 g3 d23532
        omega
      have d23552 : (x 7 1 && x 7 6).toNat = 0 := by
        have r23553 := hand1 (x 7 1) (x 7 6)
        have b23554 := hb (x 7 1)
        have b23555 := hb (x 7 1 && x 7 6)
        clear * - r23553 b23554 b23555 d23536
        omega
      have d23556 : (x 6 2).toNat = 0 := by
        have r23557 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23558 := hb (x (-6) 14)
        have b23559 := hb (x (-5) 13)
        have b23560 := hb (x (-4) 12)
        have b23561 := hb (x (-3) 11)
        have b23562 := hb (x (-2) 10)
        have b23563 := hb (x (-1) 9)
        have b23564 := hb (x 0 8)
        have b23565 := hb (x 1 7)
        have b23566 := hb (x 2 6)
        have b23567 := hb (x 3 5)
        have b23568 := hb (x 4 4)
        have b23569 := hb (x 5 3)
        have b23570 := hb (x 6 2)
        have b23571 := hb (x 7 1)
        clear * - r23557 b23558 b23559 b23560 b23561 b23562 b23563 b23564 b23565 b23566 b23567 b23568 b23569 b23570 b23571 d23536 d22491 d23167 d23247 d23263 g14 g9 g6 g5 g4 g3 d23532
        omega
      have d23572 : (x 6 2 && x 6 7).toNat = 0 := by
        have r23573 := hand1 (x 6 2) (x 6 7)
        have b23574 := hb (x 6 2)
        have b23575 := hb (x 6 2 && x 6 7)
        clear * - r23573 b23574 b23575 d23556
        omega
      have d23576 : (x 8 5).toNat = 1 := by
        have r23577 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23578 := hb (x (-2) 10)
        have b23579 := hb (x 8 5)
        have b23580 := hb (x 7 1 && x 7 6)
        have b23581 := hb (x 6 2 && x 6 7)
        have b23582 := hb (x 5 3 && x 5 8)
        have b23583 := hb (x 4 4 && x 4 9)
        have b23584 := hb (x 3 5 && x 3 10)
        have b23585 := hb (x 2 6 && x 2 11)
        have b23586 := hb (x 1 7 && x 1 12)
        have b23587 := hb (x 0 8 && x 0 13)
        have b23588 := hb (x (-1) 9 && x (-1) 14)
        clear * - r23577 b23578 b23579 b23580 b23581 b23582 b23583 b23584 b23585 b23586 b23587 b23588 d23552 d23572 d22111 d22131 d22155 d22208 g33 g34 g35 g6
        omega
      have d23589 : (x 8 13).toNat = 1 := by
        have r23590 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
        have b23591 := hb (x 8 5)
        have b23592 := hb (x 8 13)
        clear * - r23590 b23591 b23592 d23576
        omega
      have d23593 : (x 8 1).toNat = 1 := by
        have r23594 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b23595 := hb (x 8 1)
        have b23596 := hb (x 8 13)
        clear * - r23594 b23595 b23596 d23589
        omega
      have d23597 : (x 9 14).toNat = 0 := by
        have r23598 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23599 := hb (x 8 1)
        have b23600 := hb (x 9 14)
        clear * - r23598 b23599 b23600 d23593
        omega
      have d23601 : (x 9 5 && x 9 14).toNat = 0 := by
        have r23602 := hand2 (x 9 5) (x 9 14)
        have b23603 := hb (x 9 14)
        have b23604 := hb (x 9 5 && x 9 14)
        clear * - r23602 b23603 b23604 d23597
        omega
      have d23605 : (x 9 6).toNat = 0 := by
        have r23606 : (x 9 6).toNat ≤ (x 9 14).toNat := himp _ _ (hp6 9)
        have b23607 := hb (x 9 6)
        have b23608 := hb (x 9 14)
        clear * - r23606 b23607 b23608 d23597
        omega
      have d23609 : (x 9 2 && x 9 6).toNat = 0 := by
        have r23610 := hand2 (x 9 2) (x 9 6)
        have b23611 := hb (x 9 6)
        have b23612 := hb (x 9 2 && x 9 6)
        clear * - r23610 b23611 b23612 d23605
        omega
      have d23613 : (x 9 2).toNat = 0 := by
        have r23614 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b23615 := hb (x 9 2)
        have b23616 := hb (x 9 14)
        clear * - r23614 b23615 b23616 d23597
        omega
      have d23617 : (x 9 10).toNat = 0 := by
        have r23618 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
        have b23619 := hb (x 9 2)
        have b23620 := hb (x 9 10)
        clear * - r23618 b23619 b23620 d23613
        omega
      have d23621 : (x 7 2).toNat = 0 := by
        have r23622 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23623 := hb (x (-5) 14)
        have b23624 := hb (x (-4) 13)
        have b23625 := hb (x (-3) 12)
        have b23626 := hb (x (-2) 11)
        have b23627 := hb (x (-1) 10)
        have b23628 := hb (x 0 9)
        have b23629 := hb (x 1 8)
        have b23630 := hb (x 2 7)
        have b23631 := hb (x 3 6)
        have b23632 := hb (x 4 5)
        have b23633 := hb (x 5 4)
        have b23634 := hb (x 6 3)
        have b23635 := hb (x 7 2)
        have b23636 := hb (x 8 1)
        clear * - r23622 b23623 b23624 b23625 b23626 b23627 b23628 b23629 b23630 b23631 b23632 b23633 b23634 b23635 b23636 d23593 d22559 d22583 d22892 d23151 d22823 f22335 g10 g7 d22635 d22345 d23359
        omega
      have d23637 : (x 7 2 && x 7 12).toNat = 0 := by
        have r23638 := hand1 (x 7 2) (x 7 12)
        have b23639 := hb (x 7 2)
        have b23640 := hb (x 7 2 && x 7 12)
        clear * - r23638 b23639 b23640 d23621
        omega
      have d23641 : (x 6 3).toNat = 0 := by
        have r23642 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23643 := hb (x (-5) 14)
        have b23644 := hb (x (-4) 13)
        have b23645 := hb (x (-3) 12)
        have b23646 := hb (x (-2) 11)
        have b23647 := hb (x (-1) 10)
        have b23648 := hb (x 0 9)
        have b23649 := hb (x 1 8)
        have b23650 := hb (x 2 7)
        have b23651 := hb (x 3 6)
        have b23652 := hb (x 4 5)
        have b23653 := hb (x 5 4)
        have b23654 := hb (x 6 3)
        have b23655 := hb (x 7 2)
        have b23656 := hb (x 8 1)
        clear * - r23642 b23643 b23644 b23645 b23646 b23647 b23648 b23649 b23650 b23651 b23652 b23653 b23654 b23655 b23656 d23593 d23621 d22559 d22583 d22892 d23151 d22823 f22335 g10 g7 d22635 d22345 d23359
        omega
      have d23657 : (x 6 3 && x 6 13).toNat = 0 := by
        have r23658 := hand1 (x 6 3) (x 6 13)
        have b23659 := hb (x 6 3)
        have b23660 := hb (x 6 3 && x 6 13)
        clear * - r23658 b23659 b23660 d23641
        omega
      have d23661 : (x 8 1 && x 8 11).toNat = 1 := by
        have r23662 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23663 := hb (x 4 5)
        have b23664 := hb (x 9 10)
        have b23665 := hb (x 8 1 && x 8 11)
        have b23666 := hb (x 7 2 && x 7 12)
        have b23667 := hb (x 6 3 && x 6 13)
        have b23668 := hb (x 5 4 && x 5 14)
        clear * - r23662 b23663 b23664 b23665 b23666 b23667 b23668 d23617 d23637 d23657 d22563 d22583
        omega
      have d23669 : (x 8 11).toNat = 1 := by
        have r23670 := hand2 (x 8 1) (x 8 11)
        have b23671 := hb (x 8 11)
        have b23672 := hb (x 8 1 && x 8 11)
        clear * - r23670 b23671 b23672 d23661
        omega
      have d23673 : (x 8 3).toNat = 1 := by
        have r23674 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b23675 := hb (x 8 3)
        have b23676 := hb (x 8 11)
        clear * - r23674 b23675 b23676 d23669
        omega
      have d23677 : (x 11 12).toNat = 0 := by
        have r23678 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23679 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e23680 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b23681 := hb (x 8 3)
        have b23682 := hb (x 9 2)
        have b23683 := hb (x 10 13)
        have b23684 := hb (x 11 12)
        clear * - r23678 e23679 e23680 b23681 b23682 b23683 b23684 d23613 d23673
        omega
      have d23685 : (x 11 3 && x 11 12).toNat = 0 := by
        have r23686 := hand2 (x 11 3) (x 11 12)
        have b23687 := hb (x 11 12)
        have b23688 := hb (x 11 3 && x 11 12)
        clear * - r23686 b23687 b23688 d23677
        omega
      have d23689 : (x 11 4).toNat = 0 := by
        have r23690 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
        have b23691 := hb (x 11 4)
        have b23692 := hb (x 11 12)
        clear * - r23690 b23691 b23692 d23677
        omega
      have d23693 : (x 11 4 && x 11 14).toNat = 0 := by
        have r23694 := hand1 (x 11 4) (x 11 14)
        have b23695 := hb (x 11 4)
        have b23696 := hb (x 11 4 && x 11 14)
        clear * - r23694 b23695 b23696 d23689
        omega
      have d23697 : (x 10 13).toNat = 0 := by
        have r23698 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23699 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e23700 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b23701 := hb (x 8 3)
        have b23702 := hb (x 9 2)
        have b23703 := hb (x 10 13)
        have b23704 := hb (x 11 12)
        clear * - r23698 e23699 e23700 b23701 b23702 b23703 b23704 d23677 d23613 d23673
        omega
      have d23705 : (x 10 4 && x 10 13).toNat = 0 := by
        have r23706 := hand2 (x 10 4) (x 10 13)
        have b23707 := hb (x 10 13)
        have b23708 := hb (x 10 4 && x 10 13)
        clear * - r23706 b23707 b23708 d23697
        omega
      have d23709 : (x 10 5).toNat = 0 := by
        have r23710 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
        have b23711 := hb (x 10 5)
        have b23712 := hb (x 10 13)
        clear * - r23710 b23711 b23712 d23697
        omega
      have d23713 : (x 8 3 && x 8 7).toNat = 1 := by
        have r23714 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23715 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
        have e23716 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
        have b23717 := hb (x 0 11)
        have b23718 := hb (x 1 10)
        have b23719 := hb (x 10 5)
        have b23720 := hb (x 11 4)
        have b23721 := hb (x 9 2 && x 9 6)
        have b23722 := hb (x 8 3 && x 8 7)
        have b23723 := hb (x 7 4 && x 7 8)
        have b23724 := hb (x 6 5 && x 6 9)
        have b23725 := hb (x 5 6 && x 5 10)
        have b23726 := hb (x 4 7 && x 4 11)
        have b23727 := hb (x 3 8 && x 3 12)
        have b23728 := hb (x 2 9 && x 2 13)
        clear * - r23714 e23715 e23716 b23717 b23718 b23719 b23720 b23721 b23722 b23723 b23724 b23725 b23726 b23727 b23728 d23689 d23709 d23609 d23004 d23024 d23044 d23064 d22819 d22531 g21 g15
        omega
      have d23729 : (x 8 7).toNat = 1 := by
        have r23730 := hand2 (x 8 3) (x 8 7)
        have b23731 := hb (x 8 7)
        have b23732 := hb (x 8 3 && x 8 7)
        clear * - r23730 b23731 b23732 d23713
        omega
      have d23733 : (x 15 8).toNat = 0 := by
        have r23734 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23735 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e23736 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e23737 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e23738 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e23739 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e23740 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b23741 := hb (x 8 7)
        have b23742 := hb (x 9 6)
        have b23743 := hb (x 10 5)
        have b23744 := hb (x 11 4)
        have b23745 := hb (x 12 11)
        have b23746 := hb (x 13 10)
        have b23747 := hb (x 14 9)
        have b23748 := hb (x 15 8)
        clear * - r23734 e23735 e23736 e23737 e23738 e23739 e23740 b23741 b23742 b23743 b23744 b23745 b23746 b23747 b23748 d23689 d23709 d23605 d23729
        omega
      have d23749 : (x 14 9).toNat = 0 := by
        have r23750 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23751 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e23752 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e23753 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e23754 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e23755 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e23756 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b23757 := hb (x 8 7)
        have b23758 := hb (x 9 6)
        have b23759 := hb (x 10 5)
        have b23760 := hb (x 11 4)
        have b23761 := hb (x 12 11)
        have b23762 := hb (x 13 10)
        have b23763 := hb (x 14 9)
        have b23764 := hb (x 15 8)
        clear * - r23750 e23751 e23752 e23753 e23754 e23755 e23756 b23757 b23758 b23759 b23760 b23761 b23762 b23763 b23764 d23733 d23689 d23709 d23605 d23729
        omega
      have d23765 : (x 13 10).toNat = 0 := by
        have r23766 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23767 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e23768 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e23769 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e23770 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e23771 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e23772 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b23773 := hb (x 8 7)
        have b23774 := hb (x 9 6)
        have b23775 := hb (x 10 5)
        have b23776 := hb (x 11 4)
        have b23777 := hb (x 12 11)
        have b23778 := hb (x 13 10)
        have b23779 := hb (x 14 9)
        have b23780 := hb (x 15 8)
        clear * - r23766 e23767 e23768 e23769 e23770 e23771 e23772 b23773 b23774 b23775 b23776 b23777 b23778 b23779 b23780 d23733 d23749 d23689 d23709 d23605 d23729
        omega
      have d23781 : (x 13 1 && x 13 10).toNat = 0 := by
        have r23782 := hand2 (x 13 1) (x 13 10)
        have b23783 := hb (x 13 10)
        have b23784 := hb (x 13 1 && x 13 10)
        clear * - r23782 b23783 b23784 d23765
        omega
      have d23785 : (x 12 11).toNat = 0 := by
        have r23786 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23787 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e23788 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e23789 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e23790 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e23791 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e23792 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b23793 := hb (x 8 7)
        have b23794 := hb (x 9 6)
        have b23795 := hb (x 10 5)
        have b23796 := hb (x 11 4)
        have b23797 := hb (x 12 11)
        have b23798 := hb (x 13 10)
        have b23799 := hb (x 14 9)
        have b23800 := hb (x 15 8)
        clear * - r23786 e23787 e23788 e23789 e23790 e23791 e23792 b23793 b23794 b23795 b23796 b23797 b23798 b23799 b23800 d23733 d23749 d23765 d23689 d23709 d23605 d23729
        omega
      have d23801 : (x 12 2 && x 12 11).toNat = 0 := by
        have r23802 := hand2 (x 12 2) (x 12 11)
        have b23803 := hb (x 12 11)
        have b23804 := hb (x 12 2 && x 12 11)
        clear * - r23802 b23803 b23804 d23785
        omega
      have d23805 : (x 8 6).toNat = 1 := by
        have r23806 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23807 := hb (x 8 6)
        have b23808 := hb (x 14 9)
        have b23809 := hb (x 13 1 && x 13 10)
        have b23810 := hb (x 12 2 && x 12 11)
        have b23811 := hb (x 11 3 && x 11 12)
        have b23812 := hb (x 10 4 && x 10 13)
        have b23813 := hb (x 9 5 && x 9 14)
        clear * - r23806 b23807 b23808 b23809 b23810 b23811 b23812 b23813 d23749 d23781 d23801 d23685 d23705 d23601
        omega
      have d23814 : (x 14 8).toNat = 0 := by
        have r23815 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23816 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e23817 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e23818 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e23819 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e23820 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e23821 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b23822 := hb (x 7 7)
        have b23823 := hb (x 8 6)
        have b23824 := hb (x 9 5)
        have b23825 := hb (x 10 4)
        have b23826 := hb (x 11 11)
        have b23827 := hb (x 12 10)
        have b23828 := hb (x 13 9)
        have b23829 := hb (x 14 8)
        clear * - r23815 e23816 e23817 e23818 e23819 e23820 e23821 b23822 b23823 b23824 b23825 b23826 b23827 b23828 b23829 d23805
        omega
      have d23830 : (x 13 9).toNat = 0 := by
        have r23831 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23832 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e23833 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e23834 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e23835 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e23836 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e23837 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b23838 := hb (x 7 7)
        have b23839 := hb (x 8 6)
        have b23840 := hb (x 9 5)
        have b23841 := hb (x 10 4)
        have b23842 := hb (x 11 11)
        have b23843 := hb (x 12 10)
        have b23844 := hb (x 13 9)
        have b23845 := hb (x 14 8)
        clear * - r23831 e23832 e23833 e23834 e23835 e23836 e23837 b23838 b23839 b23840 b23841 b23842 b23843 b23844 b23845 d23814 d23805
        omega
      have d23846 : (x 12 10).toNat = 0 := by
        have r23847 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23848 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e23849 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e23850 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e23851 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e23852 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e23853 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b23854 := hb (x 7 7)
        have b23855 := hb (x 8 6)
        have b23856 := hb (x 9 5)
        have b23857 := hb (x 10 4)
        have b23858 := hb (x 11 11)
        have b23859 := hb (x 12 10)
        have b23860 := hb (x 13 9)
        have b23861 := hb (x 14 8)
        clear * - r23847 e23848 e23849 e23850 e23851 e23852 e23853 b23854 b23855 b23856 b23857 b23858 b23859 b23860 b23861 d23814 d23830 d23805
        omega
      have d23862 : (x 11 11).toNat = 0 := by
        have r23863 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23864 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e23865 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e23866 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e23867 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e23868 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e23869 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b23870 := hb (x 7 7)
        have b23871 := hb (x 8 6)
        have b23872 := hb (x 9 5)
        have b23873 := hb (x 10 4)
        have b23874 := hb (x 11 11)
        have b23875 := hb (x 12 10)
        have b23876 := hb (x 13 9)
        have b23877 := hb (x 14 8)
        clear * - r23863 e23864 e23865 e23866 e23867 e23868 e23869 b23870 b23871 b23872 b23873 b23874 b23875 b23876 b23877 d23814 d23830 d23846 d23805
        omega
      have d23878 : (x 10 4).toNat = 0 := by
        have r23879 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23880 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e23881 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e23882 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e23883 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e23884 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e23885 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b23886 := hb (x 7 7)
        have b23887 := hb (x 8 6)
        have b23888 := hb (x 9 5)
        have b23889 := hb (x 10 4)
        have b23890 := hb (x 11 11)
        have b23891 := hb (x 12 10)
        have b23892 := hb (x 13 9)
        have b23893 := hb (x 14 8)
        clear * - r23879 e23880 e23881 e23882 e23883 e23884 e23885 b23886 b23887 b23888 b23889 b23890 b23891 b23892 b23893 d23814 d23830 d23846 d23862 d23805
        omega
      have d23894 : (x 9 5).toNat = 0 := by
        have r23895 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23896 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e23897 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e23898 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e23899 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e23900 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e23901 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b23902 := hb (x 7 7)
        have b23903 := hb (x 8 6)
        have b23904 := hb (x 9 5)
        have b23905 := hb (x 10 4)
        have b23906 := hb (x 11 11)
        have b23907 := hb (x 12 10)
        have b23908 := hb (x 13 9)
        have b23909 := hb (x 14 8)
        clear * - r23895 e23896 e23897 e23898 e23899 e23900 e23901 b23902 b23903 b23904 b23905 b23906 b23907 b23908 b23909 d23814 d23830 d23846 d23862 d23878 d23805
        omega
      have d23910 : (x 7 7).toNat = 0 := by
        have r23911 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23912 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e23913 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e23914 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e23915 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e23916 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e23917 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b23918 := hb (x 7 7)
        have b23919 := hb (x 8 6)
        have b23920 := hb (x 9 5)
        have b23921 := hb (x 10 4)
        have b23922 := hb (x 11 11)
        have b23923 := hb (x 12 10)
        have b23924 := hb (x 13 9)
        have b23925 := hb (x 14 8)
        clear * - r23911 e23912 e23913 e23914 e23915 e23916 e23917 b23918 b23919 b23920 b23921 b23922 b23923 b23924 b23925 d23814 d23830 d23846 d23862 d23878 d23894 d23805
        omega
      have d23926 : (x 13 1).toNat = 0 := by
        have r23927 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23928 := hb (x 0 14)
        have b23929 := hb (x 1 13)
        have b23930 := hb (x 2 12)
        have b23931 := hb (x 3 11)
        have b23932 := hb (x 4 10)
        have b23933 := hb (x 5 9)
        have b23934 := hb (x 6 8)
        have b23935 := hb (x 7 7)
        have b23936 := hb (x 8 6)
        have b23937 := hb (x 9 5)
        have b23938 := hb (x 10 4)
        have b23939 := hb (x 11 3)
        have b23940 := hb (x 12 2)
        have b23941 := hb (x 13 1)
        clear * - r23927 b23928 b23929 b23930 b23931 b23932 b23933 b23934 b23935 b23936 b23937 b23938 b23939 b23940 b23941 d23878 d23894 d23805 d23910 d22767 d22783 d22437 d22402 g24 g22 g16
        omega
      have d23942 : (x 13 1 && x 13 14).toNat = 0 := by
        have r23943 := hand1 (x 13 1) (x 13 14)
        have b23944 := hb (x 13 1)
        have b23945 := hb (x 13 1 && x 13 14)
        clear * - r23943 b23944 b23945 d23926
        omega
      have d23946 : (x 12 2).toNat = 0 := by
        have r23947 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23948 := hb (x 0 14)
        have b23949 := hb (x 1 13)
        have b23950 := hb (x 2 12)
        have b23951 := hb (x 3 11)
        have b23952 := hb (x 4 10)
        have b23953 := hb (x 5 9)
        have b23954 := hb (x 6 8)
        have b23955 := hb (x 7 7)
        have b23956 := hb (x 8 6)
        have b23957 := hb (x 9 5)
        have b23958 := hb (x 10 4)
        have b23959 := hb (x 11 3)
        have b23960 := hb (x 12 2)
        have b23961 := hb (x 13 1)
        clear * - r23947 b23948 b23949 b23950 b23951 b23952 b23953 b23954 b23955 b23956 b23957 b23958 b23959 b23960 b23961 d23926 d23878 d23894 d23805 d23910 d22767 d22783 d22437 d22402 g24 g22 g16
        omega
      have d23962 : (x 14 13).toNat = 1 := by
        have r23963 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23964 := hb (x 12 2)
        have b23965 := hb (x 14 13)
        have b23966 := hb (x 13 1 && x 13 14)
        clear * - r23963 b23964 b23965 b23966 d23942 d23946
        omega
      have d23967 : (x 14 1).toNat = 1 := by
        have r23968 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
        have b23969 := hb (x 14 1)
        have b23970 := hb (x 14 13)
        clear * - r23968 b23969 b23970 d23962
        omega
      have d23971 : (x 15 14).toNat = 0 := by
        have r23972 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23973 := hb (x 14 1)
        have b23974 := hb (x 15 14)
        clear * - r23972 b23973 b23974 d23967
        omega
      have d23975 : (x 15 2).toNat = 0 := by
        have r23976 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b23977 := hb (x 15 2)
        have b23978 := hb (x 15 14)
        clear * - r23976 b23977 b23978 d23971
        omega
      have d23979 : (x 15 10).toNat = 0 := by
        have r23980 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
        have b23981 := hb (x 15 2)
        have b23982 := hb (x 15 10)
        clear * - r23980 b23981 b23982 d23975
        omega
      have d23983 : (x 15 12).toNat = 0 := by
        have r23984 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23985 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e23986 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b23987 := hb (x 12 3)
        have b23988 := hb (x 13 2)
        have b23989 := hb (x 14 13)
        have b23990 := hb (x 15 12)
        clear * - r23984 e23985 e23986 b23987 b23988 b23989 b23990 d23962
        omega
      have d23991 : (x 13 2).toNat = 0 := by
        have r23992 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23993 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e23994 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b23995 := hb (x 12 3)
        have b23996 := hb (x 13 2)
        have b23997 := hb (x 14 13)
        have b23998 := hb (x 15 12)
        clear * - r23992 e23993 e23994 b23995 b23996 b23997 b23998 d23983 d23962
        omega
      have d23999 : (x 13 2 && x 13 12).toNat = 0 := by
        have r24000 := hand1 (x 13 2) (x 13 12)
        have b24001 := hb (x 13 2)
        have b24002 := hb (x 13 2 && x 13 12)
        clear * - r24000 b24001 b24002 d23991
        omega
      have d24003 : (x 12 3).toNat = 0 := by
        have r24004 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24005 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e24006 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b24007 := hb (x 12 3)
        have b24008 := hb (x 13 2)
        have b24009 := hb (x 14 13)
        have b24010 := hb (x 15 12)
        clear * - r24004 e24005 e24006 b24007 b24008 b24009 b24010 d23983 d23962 d23991
        omega
      have d24011 : (x 12 3 && x 12 13).toNat = 0 := by
        have r24012 := hand1 (x 12 3) (x 12 13)
        have b24013 := hb (x 12 3)
        have b24014 := hb (x 12 3 && x 12 13)
        clear * - r24012 b24013 b24014 d24003
        omega
      have d24015 : (x 14 1 && x 14 11).toNat = 1 := by
        have r24016 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b24017 := hb (x 10 5)
        have b24018 := hb (x 15 10)
        have b24019 := hb (x 14 1 && x 14 11)
        have b24020 := hb (x 13 2 && x 13 12)
        have b24021 := hb (x 12 3 && x 12 13)
        have b24022 := hb (x 11 4 && x 11 14)
        clear * - r24016 b24017 b24018 b24019 b24020 b24021 b24022 d23979 d23999 d24011 d23693 d23709
        omega
      have d24023 : (x 14 11).toNat = 1 := by
        have r24024 := hand2 (x 14 1) (x 14 11)
        have b24025 := hb (x 14 11)
        have b24026 := hb (x 14 1 && x 14 11)
        clear * - r24024 b24025 b24026 d24015
        omega
      have d24027 : (x 17 8).toNat = 0 := by
        have r24028 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24029 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e24030 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e24031 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e24032 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e24033 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e24034 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b24035 := hb (x 10 7)
        have b24036 := hb (x 11 6)
        have b24037 := hb (x 12 5)
        have b24038 := hb (x 13 4)
        have b24039 := hb (x 14 11)
        have b24040 := hb (x 15 10)
        have b24041 := hb (x 16 9)
        have b24042 := hb (x 17 8)
        clear * - r24028 e24029 e24030 e24031 e24032 e24033 e24034 b24035 b24036 b24037 b24038 b24039 b24040 b24041 b24042 d23979 d24023
        omega
      have d24043 : (x 16 9).toNat = 0 := by
        have r24044 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24045 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e24046 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e24047 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e24048 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e24049 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e24050 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b24051 := hb (x 10 7)
        have b24052 := hb (x 11 6)
        have b24053 := hb (x 12 5)
        have b24054 := hb (x 13 4)
        have b24055 := hb (x 14 11)
        have b24056 := hb (x 15 10)
        have b24057 := hb (x 16 9)
        have b24058 := hb (x 17 8)
        clear * - r24044 e24045 e24046 e24047 e24048 e24049 e24050 b24051 b24052 b24053 b24054 b24055 b24056 b24057 b24058 d24027 d23979 d24023
        omega
      have d24059 : (x 13 4).toNat = 0 := by
        have r24060 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24061 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e24062 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e24063 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e24064 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e24065 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e24066 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b24067 := hb (x 10 7)
        have b24068 := hb (x 11 6)
        have b24069 := hb (x 12 5)
        have b24070 := hb (x 13 4)
        have b24071 := hb (x 14 11)
        have b24072 := hb (x 15 10)
        have b24073 := hb (x 16 9)
        have b24074 := hb (x 17 8)
        clear * - r24060 e24061 e24062 e24063 e24064 e24065 e24066 b24067 b24068 b24069 b24070 b24071 b24072 b24073 b24074 d24027 d24043 d23979 d24023
        omega
      have d24075 : (x 12 5).toNat = 0 := by
        have r24076 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24077 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e24078 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e24079 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e24080 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e24081 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e24082 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b24083 := hb (x 10 7)
        have b24084 := hb (x 11 6)
        have b24085 := hb (x 12 5)
        have b24086 := hb (x 13 4)
        have b24087 := hb (x 14 11)
        have b24088 := hb (x 15 10)
        have b24089 := hb (x 16 9)
        have b24090 := hb (x 17 8)
        clear * - r24076 e24077 e24078 e24079 e24080 e24081 e24082 b24083 b24084 b24085 b24086 b24087 b24088 b24089 b24090 d24027 d24043 d23979 d24023 d24059
        omega
      have d24091 : (x 11 6).toNat = 0 := by
        have r24092 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24093 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e24094 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e24095 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e24096 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e24097 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e24098 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b24099 := hb (x 10 7)
        have b24100 := hb (x 11 6)
        have b24101 := hb (x 12 5)
        have b24102 := hb (x 13 4)
        have b24103 := hb (x 14 11)
        have b24104 := hb (x 15 10)
        have b24105 := hb (x 16 9)
        have b24106 := hb (x 17 8)
        clear * - r24092 e24093 e24094 e24095 e24096 e24097 e24098 b24099 b24100 b24101 b24102 b24103 b24104 b24105 b24106 d24027 d24043 d23979 d24023 d24059 d24075
        omega
      have d24107 : (x 10 7).toNat = 0 := by
        have r24108 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24109 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e24110 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e24111 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e24112 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e24113 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e24114 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b24115 := hb (x 10 7)
        have b24116 := hb (x 11 6)
        have b24117 := hb (x 12 5)
        have b24118 := hb (x 13 4)
        have b24119 := hb (x 14 11)
        have b24120 := hb (x 15 10)
        have b24121 := hb (x 16 9)
        have b24122 := hb (x 17 8)
        clear * - r24108 e24109 e24110 e24111 e24112 e24113 e24114 b24115 b24116 b24117 b24118 b24119 b24120 b24121 b24122 d24027 d24043 d23979 d24023 d24059 d24075 d24091
        omega
      have d24123 : (x 10 1 && x 10 7).toNat = 0 := by
        have r24124 := hand2 (x 10 1) (x 10 7)
        have b24125 := hb (x 10 7)
        have b24126 := hb (x 10 1 && x 10 7)
        clear * - r24124 b24125 b24126 d24107
        omega
      have r24127 : 1 ≤ (x 11 6).toNat + (x 10 1 && x 10 7).toNat + (x 9 2 && x 9 8).toNat + (x 8 3 && x 8 9).toNat + (x 7 4 && x 7 10).toNat + (x 6 5 && x 6 11).toNat + (x 5 6 && x 5 12).toNat + (x 4 7 && x 4 13).toNat + (x 3 8 && x 3 14).toNat + (x 2 9).toNat := by have q := hcov6 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24128 := hb (x 2 9)
      have b24129 := hb (x 11 6)
      have b24130 := hb (x 10 1 && x 10 7)
      have b24131 := hb (x 9 2 && x 9 8)
      have b24132 := hb (x 8 3 && x 8 9)
      have b24133 := hb (x 7 4 && x 7 10)
      have b24134 := hb (x 6 5 && x 6 11)
      have b24135 := hb (x 5 6 && x 5 12)
      have b24136 := hb (x 4 7 && x 4 13)
      have b24137 := hb (x 3 8 && x 3 14)
      linarith only [r24127, b24128, b24129, b24130, b24131, b24132, b24133, b24134, b24135, b24136, b24137, d24091, d24123, d22912, d22932, d22952, d23147, d22555, d22579, d22815, d22539]
    · have f24138 : (x 0 9).toNat = 1 := by rw [h22334]; rfl
      have d24139 : (x 1 8).toNat = 0 := by
        have r24140 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24141 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e24142 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e24143 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e24144 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e24145 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e24146 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b24147 := hb (x (-6) 7)
        have b24148 := hb (x (-5) 6)
        have b24149 := hb (x (-4) 5)
        have b24150 := hb (x (-3) 4)
        have b24151 := hb (x (-2) 11)
        have b24152 := hb (x (-1) 10)
        have b24153 := hb (x 0 9)
        have b24154 := hb (x 1 8)
        clear * - r24140 e24141 e24142 e24143 e24144 e24145 e24146 b24147 b24148 b24149 b24150 b24151 b24152 b24153 b24154 f24138 g10 g7
        omega
      have d24155 : (x (-3) 4).toNat = 0 := by
        have r24156 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e24157 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
        have e24158 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
        have e24159 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
        have e24160 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
        have e24161 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
        have e24162 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
        have b24163 := hb (x (-6) 7)
        have b24164 := hb (x (-5) 6)
        have b24165 := hb (x (-4) 5)
        have b24166 := hb (x (-3) 4)
        have b24167 := hb (x (-2) 11)
        have b24168 := hb (x (-1) 10)
        have b24169 := hb (x 0 9)
        have b24170 := hb (x 1 8)
        clear * - r24156 e24157 e24158 e24159 e24160 e24161 e24162 b24163 b24164 b24165 b24166 b24167 b24168 b24169 b24170 d24139 f24138 g10 g7
        omega
      have d24171 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
        have r24172 := hand1 (x (-3) 4) (x (-3) 14)
        have b24173 := hb (x (-3) 4)
        have b24174 := hb (x (-3) 4 && x (-3) 14)
        clear * - r24172 b24173 b24174 d24155
        omega
      have d24175 : (x (-4) 5).toNat = 1 := by
        have r24176 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b24177 := hb (x (-4) 5)
        have b24178 := hb (x 1 10)
        have b24179 := hb (x 0 1 && x 0 11)
        have b24180 := hb (x (-1) 2 && x (-1) 12)
        have b24181 := hb (x (-2) 3 && x (-2) 13)
        have b24182 := hb (x (-3) 4 && x (-3) 14)
        clear * - r24176 b24177 b24178 b24179 b24180 b24181 b24182 g21 g58 g59 g60 d24171
        omega
      have r24183 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24184 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e24185 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e24186 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e24187 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e24188 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e24189 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b24190 := hb (x (-6) 7)
      have b24191 := hb (x (-5) 6)
      have b24192 := hb (x (-4) 5)
      have b24193 := hb (x (-3) 4)
      have b24194 := hb (x (-2) 11)
      have b24195 := hb (x (-1) 10)
      have b24196 := hb (x 0 9)
      have b24197 := hb (x 1 8)
      linarith only [r24183, e24184, e24185, e24186, e24187, e24188, e24189, b24190, b24191, b24192, b24193, b24194, b24195, b24196, b24197, d24139, f24138, g10, g7, d24155, d24175]
  · have f24198 : (x 0 6).toNat = 1 := by rw [h22332]; rfl
    have d24199 : (x 6 8).toNat = 0 := by
      have r24200 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24201 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e24202 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e24203 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e24204 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e24205 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e24206 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b24207 := hb (x (-1) 7)
      have b24208 := hb (x 0 6)
      have b24209 := hb (x 1 5)
      have b24210 := hb (x 2 4)
      have b24211 := hb (x 3 11)
      have b24212 := hb (x 4 10)
      have b24213 := hb (x 5 9)
      have b24214 := hb (x 6 8)
      clear * - r24200 e24201 e24202 e24203 e24204 e24205 e24206 b24207 b24208 b24209 b24210 b24211 b24212 b24213 b24214 g23 g19 f24198
      omega
    have d24215 : (x 5 9).toNat = 0 := by
      have r24216 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24217 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e24218 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e24219 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e24220 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e24221 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e24222 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b24223 := hb (x (-1) 7)
      have b24224 := hb (x 0 6)
      have b24225 := hb (x 1 5)
      have b24226 := hb (x 2 4)
      have b24227 := hb (x 3 11)
      have b24228 := hb (x 4 10)
      have b24229 := hb (x 5 9)
      have b24230 := hb (x 6 8)
      clear * - r24216 e24217 e24218 e24219 e24220 e24221 e24222 b24223 b24224 b24225 b24226 b24227 b24228 b24229 b24230 d24199 g23 g19 f24198
      omega
    have d24231 : (x 4 10).toNat = 0 := by
      have r24232 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24233 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e24234 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e24235 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e24236 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e24237 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e24238 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b24239 := hb (x (-1) 7)
      have b24240 := hb (x 0 6)
      have b24241 := hb (x 1 5)
      have b24242 := hb (x 2 4)
      have b24243 := hb (x 3 11)
      have b24244 := hb (x 4 10)
      have b24245 := hb (x 5 9)
      have b24246 := hb (x 6 8)
      clear * - r24232 e24233 e24234 e24235 e24236 e24237 e24238 b24239 b24240 b24241 b24242 b24243 b24244 b24245 b24246 d24199 d24215 g23 g19 f24198
      omega
    have d24247 : (x 3 1 && x 3 11).toNat = 1 := by
      have r24248 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24249 := hb (x (-1) 5)
      have b24250 := hb (x 4 10)
      have b24251 := hb (x 3 1 && x 3 11)
      have b24252 := hb (x 2 2 && x 2 12)
      have b24253 := hb (x 1 3 && x 1 13)
      have b24254 := hb (x 0 4 && x 0 14)
      clear * - r24248 b24249 b24250 b24251 b24252 b24253 b24254 d24231 g61 g62 g63 g8
      omega
    have d24255 : (x 3 11).toNat = 1 := by
      have r24256 := hand2 (x 3 1) (x 3 11)
      have b24257 := hb (x 3 11)
      have b24258 := hb (x 3 1 && x 3 11)
      clear * - r24256 b24257 b24258 d24247
      omega
    have r24259 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24260 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e24261 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e24262 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e24263 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e24264 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e24265 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b24266 := hb (x (-1) 7)
    have b24267 := hb (x 0 6)
    have b24268 := hb (x 1 5)
    have b24269 := hb (x 2 4)
    have b24270 := hb (x 3 11)
    have b24271 := hb (x 4 10)
    have b24272 := hb (x 5 9)
    have b24273 := hb (x 6 8)
    linarith only [r24259, e24260, e24261, e24262, e24263, e24264, e24265, b24266, b24267, b24268, b24269, b24270, b24271, b24272, b24273, d24199, d24215, d24231, d24255, g23, g19, f24198]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-7) 11).toNat = 0)
    (g1 : (x (-6) 6).toNat = 0)
    (g2 : (x (-6) 10).toNat = 0)
    (g3 : (x (-5) 13).toNat = 0)
    (g4 : (x (-4) 12).toNat = 1)
    (g5 : (x (-3) 11).toNat = 0)
    (g6 : (x (-2) 10).toNat = 0)
    (g7 : (x (-2) 11).toNat = 0)
    (g8 : (x (-1) 5).toNat = 0)
    (g9 : (x (-1) 9).toNat = 0)
    (g10 : (x (-1) 10).toNat = 0)
    (g11 : (x (-1) 11).toNat = 0)
    (g12 : (x 0 4).toNat = 0)
    (g13 : (x 0 5).toNat = 1)
    (g14 : (x 0 8).toNat = 0)
    (g15 : (x 0 11).toNat = 0)
    (g16 : (x 0 14).toNat = 1)
    (g17 : (x 1 2).toNat = 0)
    (g18 : (x 1 4).toNat = 0)
    (g19 : (x 1 5).toNat = 0)
    (g20 : (x 1 6).toNat = 0)
    (g21 : (x 1 10).toNat = 0)
    (g22 : (x 1 13).toNat = 0)
    (g23 : (x 2 4).toNat = 0)
    (g24 : (x 2 12).toNat = 0)
    (g25 : (x 0 4 && x 0 8).toNat = 0)
    (g26 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g27 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g29 : (x (-5) 9 && x (-5) 13).toNat = 0)
    (g30 : (x 0 4 && x 0 9).toNat = 0)
    (g31 : (x (-1) 5 && x (-1) 10).toNat = 0)
    (g32 : (x (-2) 6 && x (-2) 11).toNat = 0)
    (g33 : (x 1 7 && x 1 12).toNat = 0)
    (g34 : (x 0 8 && x 0 13).toNat = 0)
    (g35 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g37 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g38 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g39 : (x (-5) 5 && x (-5) 12).toNat = 0)
    (g40 : (x (-6) 6 && x (-6) 13).toNat = 0)
    (g41 : (x (-7) 7 && x (-7) 14).toNat = 0)
    (g42 : (x (-6) 2 && x (-6) 11).toNat = 0)
    (g43 : (x (-7) 3 && x (-7) 12).toNat = 0)
    (g44 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g45 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g46 : (x (-5) 4 && x (-5) 13).toNat = 0)
    (g47 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g48 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g49 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g50 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g51 : (x 1 2 && x 1 11).toNat = 0)
    (g52 : (x 0 3 && x 0 12).toNat = 0)
    (g53 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g54 : (x 1 3 && x 1 12).toNat = 0)
    (g55 : (x 0 4 && x 0 13).toNat = 0)
    (g56 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g57 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g58 : (x 0 1 && x 0 11).toNat = 0)
    (g59 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g60 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g61 : (x 2 2 && x 2 12).toNat = 0)
    (g62 : (x 1 3 && x 1 13).toNat = 0)
    (g63 : (x 0 4 && x 0 14).toNat = 0)
    (g64 : (x (-6) 2 && x (-6) 13).toNat = 0)
    (g65 : (x (-7) 3 && x (-7) 14).toNat = 0)
    (g66 : (x 2 1 && x 2 12).toNat = 0)
    (g67 : (x 1 2 && x 1 13).toNat = 0)
    (g68 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_a1101_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68
