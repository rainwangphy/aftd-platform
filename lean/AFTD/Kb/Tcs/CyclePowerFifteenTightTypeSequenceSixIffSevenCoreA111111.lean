import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111111

Topic: combinatorics   Node: 6bb2e25bab69

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 70 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111111_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-12) 4).toNat = 0)
    (g1 : (x (-5) 7).toNat = 0)
    (g2 : (x (-4) 6).toNat = 0)
    (g3 : (x (-3) 5).toNat = 0)
    (g4 : (x (-3) 7).toNat = 0)
    (g5 : (x (-2) 4).toNat = 0)
    (g6 : (x (-2) 6).toNat = 0)
    (g7 : (x (-1) 3).toNat = 0)
    (g8 : (x (-1) 5).toNat = 0)
    (g9 : (x (-1) 7).toNat = 0)
    (g10 : (x (-1) 9).toNat = 0)
    (g11 : (x (-1) 10).toNat = 0)
    (g12 : (x (-1) 11).toNat = 0)
    (g13 : (x (-1) 13).toNat = 0)
    (g14 : (x 0 2).toNat = 1)
    (g15 : (x 0 4).toNat = 1)
    (g16 : (x 0 7).toNat = 0)
    (g17 : (x 0 11).toNat = 1)
    (g18 : (x 0 13).toNat = 1)
    (g19 : (x 1 1).toNat = 1)
    (g20 : (x 1 2).toNat = 0)
    (g21 : (x 1 6).toNat = 0)
    (g22 : (x 1 10).toNat = 0)
    (g23 : (x 1 12).toNat = 0)
    (g24 : (x 2 5).toNat = 0)
    (g25 : (x 2 9).toNat = 0)
    (g26 : (x 2 11).toNat = 0)
    (g27 : (x 3 4).toNat = 0)
    (g28 : (x 3 8).toNat = 0)
    (g29 : (x 3 10).toNat = 0)
    (g30 : (x 4 9).toNat = 0)
    (g31 : (x 5 8).toNat = 0)
    (g32 : (x 3 4 && x 3 8).toNat = 0)
    (g33 : (x 2 5 && x 2 9).toNat = 0)
    (g34 : (x 1 6 && x 1 10).toNat = 0)
    (g35 : (x 0 7 && x 0 11).toNat = 0)
    (g36 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g37 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g38 : (x 1 1 && x 1 6).toNat = 0)
    (g39 : (x 0 2 && x 0 7).toNat = 0)
    (g40 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g41 : (x (-2) 4 && x (-2) 9).toNat = 0)
    (g42 : (x (-3) 5 && x (-3) 10).toNat = 0)
    (g43 : (x (-4) 6 && x (-4) 11).toNat = 0)
    (g44 : (x (-5) 7 && x (-5) 12).toNat = 0)
    (g45 : (x 0 1 && x 0 7).toNat = 0)
    (g46 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g47 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g48 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g49 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g50 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g51 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g52 : (x 5 2 && x 5 8).toNat = 0)
    (g53 : (x 4 3 && x 4 9).toNat = 0)
    (g54 : (x 3 4 && x 3 10).toNat = 0)
    (g55 : (x 2 5 && x 2 11).toNat = 0)
    (g56 : (x 1 6 && x 1 12).toNat = 0)
    (g57 : (x 0 7 && x 0 13).toNat = 0)
    (g58 : (x 6 1 && x 6 8).toNat = 0)
    (g59 : (x 5 2 && x 5 9).toNat = 0)
    (g60 : (x 4 3 && x 4 10).toNat = 0)
    (g61 : (x 3 4 && x 3 11).toNat = 0)
    (g62 : (x 2 5 && x 2 12).toNat = 0)
    (g63 : (x 1 6 && x 1 13).toNat = 0)
    (g64 : (x 0 7 && x 0 14).toNat = 0)
    (g65 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g66 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g67 : (x 3 4 && x 3 13).toNat = 0)
    (g68 : (x 2 5 && x 2 14).toNat = 0)
    (g69 : (x (-2) 1 && x (-2) 11).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d50103 : (x 2 14).toNat = 0 := by
    have r50104 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b50105 := hb (x 1 1)
    have b50106 := hb (x 2 14)
    clear * - r50104 b50105 b50106 g19
    omega
  have d50107 : (x 2 1 && x 2 14).toNat = 0 := by
    have r50108 := hand2 (x 2 1) (x 2 14)
    have b50109 := hb (x 2 14)
    have b50110 := hb (x 2 1 && x 2 14)
    clear * - r50108 b50109 b50110 d50103
    omega
  have d50111 : (x 2 6).toNat = 0 := by
    have r50112 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
    have b50113 := hb (x 2 6)
    have b50114 := hb (x 2 14)
    clear * - r50112 b50113 b50114 d50103
    omega
  have d50115 : (x 2 2).toNat = 0 := by
    have r50116 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b50117 := hb (x 2 2)
    have b50118 := hb (x 2 14)
    clear * - r50116 b50117 b50118 d50103
    omega
  have d50119 : (x 3 13).toNat = 1 := by
    have r50120 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b50121 := hb (x 1 2)
    have b50122 := hb (x 3 13)
    have b50123 := hb (x 2 1 && x 2 14)
    clear * - r50120 b50121 b50122 b50123 d50107 g20
    omega
  have d50124 : (x 3 1).toNat = 1 := by
    have r50125 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b50126 := hb (x 3 1)
    have b50127 := hb (x 3 13)
    clear * - r50125 b50126 b50127 d50119
    omega
  have d50128 : (x 4 12).toNat = 0 := by
    have r50129 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e50130 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e50131 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b50132 := hb (x 1 3)
    have b50133 := hb (x 2 2)
    have b50134 := hb (x 3 13)
    have b50135 := hb (x 4 12)
    clear * - r50129 e50130 e50131 b50132 b50133 b50134 b50135 d50119 d50115
    omega
  have d50136 : (x 4 3 && x 4 12).toNat = 0 := by
    have r50137 := hand2 (x 4 3) (x 4 12)
    have b50138 := hb (x 4 12)
    have b50139 := hb (x 4 3 && x 4 12)
    clear * - r50137 b50138 b50139 d50128
    omega
  have d50140 : (x 4 4).toNat = 0 := by
    have r50141 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b50142 := hb (x 4 4)
    have b50143 := hb (x 4 12)
    clear * - r50141 b50142 b50143 d50128
    omega
  have d50144 : (x 1 3).toNat = 0 := by
    have r50145 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e50146 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e50147 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b50148 := hb (x 1 3)
    have b50149 := hb (x 2 2)
    have b50150 := hb (x 3 13)
    have b50151 := hb (x 4 12)
    clear * - r50145 e50146 e50147 b50148 b50149 b50150 b50151 d50128 d50119 d50115
    omega
  cases h50152 : x 1 7
  · have f50153 : (x 1 7).toNat = 0 := by rw [h50152]; rfl
    cases h50154 : x (-1) 8
    · have f50155 : (x (-1) 8).toNat = 0 := by rw [h50154]; rfl
      have d50156 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
        have r50157 := hand1 (x (-1) 8) (x (-1) 14)
        have b50158 := hb (x (-1) 8)
        have b50159 := hb (x (-1) 8 && x (-1) 14)
        clear * - r50157 b50158 b50159 f50155
        omega
      have d50160 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
        have r50161 := hand1 (x (-1) 8) (x (-1) 12)
        have b50162 := hb (x (-1) 8)
        have b50163 := hb (x (-1) 8 && x (-1) 12)
        clear * - r50161 b50162 b50163 f50155
        omega
      have d50164 : (x 7 7).toNat = 1 := by
        have r50165 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b50166 := hb (x (-1) 8)
        have b50167 := hb (x 7 7)
        have b50168 := hb (x 6 1 && x 6 8)
        have b50169 := hb (x 5 2 && x 5 9)
        have b50170 := hb (x 4 3 && x 4 10)
        have b50171 := hb (x 3 4 && x 3 11)
        have b50172 := hb (x 2 5 && x 2 12)
        have b50173 := hb (x 1 6 && x 1 13)
        have b50174 := hb (x 0 7 && x 0 14)
        clear * - r50165 b50166 b50167 b50168 b50169 b50170 b50171 b50172 b50173 b50174 g58 g59 g60 g61 g62 g63 g64 f50155
        omega
      have d50175 : (x 14 8).toNat = 0 := by
        have r50176 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50177 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e50178 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e50179 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e50180 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e50181 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e50182 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b50183 := hb (x 7 7)
        have b50184 := hb (x 8 6)
        have b50185 := hb (x 9 5)
        have b50186 := hb (x 10 4)
        have b50187 := hb (x 11 11)
        have b50188 := hb (x 12 10)
        have b50189 := hb (x 13 9)
        have b50190 := hb (x 14 8)
        clear * - r50176 e50177 e50178 e50179 e50180 e50181 e50182 b50183 b50184 b50185 b50186 b50187 b50188 b50189 b50190 d50164
        omega
      have d50191 : (x 13 9).toNat = 0 := by
        have r50192 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50193 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e50194 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e50195 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e50196 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e50197 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e50198 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b50199 := hb (x 7 7)
        have b50200 := hb (x 8 6)
        have b50201 := hb (x 9 5)
        have b50202 := hb (x 10 4)
        have b50203 := hb (x 11 11)
        have b50204 := hb (x 12 10)
        have b50205 := hb (x 13 9)
        have b50206 := hb (x 14 8)
        clear * - r50192 e50193 e50194 e50195 e50196 e50197 e50198 b50199 b50200 b50201 b50202 b50203 b50204 b50205 b50206 d50175 d50164
        omega
      have d50207 : (x 12 10).toNat = 0 := by
        have r50208 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50209 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e50210 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e50211 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e50212 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e50213 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e50214 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b50215 := hb (x 7 7)
        have b50216 := hb (x 8 6)
        have b50217 := hb (x 9 5)
        have b50218 := hb (x 10 4)
        have b50219 := hb (x 11 11)
        have b50220 := hb (x 12 10)
        have b50221 := hb (x 13 9)
        have b50222 := hb (x 14 8)
        clear * - r50208 e50209 e50210 e50211 e50212 e50213 e50214 b50215 b50216 b50217 b50218 b50219 b50220 b50221 b50222 d50175 d50191 d50164
        omega
      have d50223 : (x 12 1 && x 12 10).toNat = 0 := by
        have r50224 := hand2 (x 12 1) (x 12 10)
        have b50225 := hb (x 12 10)
        have b50226 := hb (x 12 1 && x 12 10)
        clear * - r50224 b50225 b50226 d50207
        omega
      have d50227 : (x 11 11).toNat = 0 := by
        have r50228 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50229 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e50230 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e50231 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e50232 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e50233 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e50234 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b50235 := hb (x 7 7)
        have b50236 := hb (x 8 6)
        have b50237 := hb (x 9 5)
        have b50238 := hb (x 10 4)
        have b50239 := hb (x 11 11)
        have b50240 := hb (x 12 10)
        have b50241 := hb (x 13 9)
        have b50242 := hb (x 14 8)
        clear * - r50228 e50229 e50230 e50231 e50232 e50233 e50234 b50235 b50236 b50237 b50238 b50239 b50240 b50241 b50242 d50175 d50191 d50207 d50164
        omega
      have d50243 : (x 11 2 && x 11 11).toNat = 0 := by
        have r50244 := hand2 (x 11 2) (x 11 11)
        have b50245 := hb (x 11 11)
        have b50246 := hb (x 11 2 && x 11 11)
        clear * - r50244 b50245 b50246 d50227
        omega
      cases h50247 : x (-1) 12
      · have f50248 : (x (-1) 12).toNat = 0 := by rw [h50247]; rfl
        cases h50249 : x (-1) 14
        · have f50250 : (x (-1) 14).toNat = 0 := by rw [h50249]; rfl
          have d50251 : (x (-2) 1).toNat = 1 := by
            have r50252 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b50253 := hb (x (-2) 1)
            have b50254 := hb (x (-1) 14)
            clear * - r50252 b50253 b50254 f50250
            omega
          have r50255 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50256 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50257 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50258 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50259 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
          have e50260 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
          have e50261 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
          have e50262 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
          have e50263 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
          have e50264 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
          have r50265 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50266 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50267 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50268 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50269 : 1 ≤ (x (-9) 11).toNat + (x (-10) 1 && x (-10) 12).toNat + (x (-11) 2 && x (-11) 13).toNat + (x (-12) 3 && x (-12) 14).toNat + (x (-13) 4).toNat := by have q := hcov11 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50270 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50271 : (x (-13) 4).toNat ≤ (x (-13) 12).toNat := himp _ _ (hp4 (-13))
          have r50272 := hand2 (x (-4) 3) (x (-4) 8)
          have r50273 := hand2 (x (-5) 4) (x (-5) 9)
          have r50274 := hand2 (x (-6) 5) (x (-6) 10)
          have r50275 := hand1 (x (-7) 6) (x (-7) 11)
          have r50276 := hand1 (x (-8) 7) (x (-8) 12)
          have r50277 := hand1 (x (-9) 8) (x (-9) 13)
          have r50278 := hand1 (x (-10) 9) (x (-10) 14)
          have r50279 := hand1 (x (-6) 8) (x (-6) 13)
          have r50280 := hand1 (x (-7) 9) (x (-7) 14)
          have r50281 := hand1 (x (-7) 8) (x (-7) 14)
          have r50282 := hand1 (x (-3) 2) (x (-3) 12)
          have r50283 := hand1 (x (-4) 3) (x (-4) 13)
          have r50284 := hand1 (x (-5) 4) (x (-5) 14)
          have r50285 := hand2 (x (-10) 1) (x (-10) 12)
          have r50286 := hand2 (x (-11) 2) (x (-11) 13)
          have r50287 := hand2 (x (-12) 3) (x (-12) 14)
          have r50288 := hand2 (x (-8) 1) (x (-8) 12)
          have r50289 := hand2 (x (-9) 2) (x (-9) 13)
          have r50290 := hand2 (x (-10) 3) (x (-10) 14)
          linarith only [r50255, r50256, r50257, r50258, e50259, e50260, e50261, e50262, e50263, e50264, r50265, r50266, r50267, r50268, r50269, r50270, r50271, r50272, r50273, r50274, r50275, r50276, r50277, r50278, r50279, r50280, r50281, r50282, r50283, r50284, r50285, r50286, r50287, r50288, r50289, r50290, g1, g2, g3, g4, d50251, g5, g6, g7, g8, g11, g14, g15, g19, d50144, g21, d50115, g24, d50124, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g69]
        · have f50381 : (x (-1) 14).toNat = 1 := by rw [h50249]; rfl
          have d50382 : (x (-2) 1).toNat = 0 := by
            have r50383 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b50384 := hb (x (-2) 1)
            have b50385 := hb (x (-1) 14)
            clear * - r50383 b50384 b50385 f50381
            omega
          have d50386 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r50387 := hand1 (x (-2) 1) (x (-2) 14)
            have b50388 := hb (x (-2) 1)
            have b50389 := hb (x (-2) 1 && x (-2) 14)
            clear * - r50387 b50388 b50389 d50382
            omega
          have d50390 : (x (-2) 13).toNat = 0 := by
            have r50391 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
            have b50392 := hb (x (-2) 1)
            have b50393 := hb (x (-2) 13)
            clear * - r50391 b50392 b50393 d50382
            omega
          have d50394 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
            have r50395 := hand2 (x (-2) 9) (x (-2) 13)
            have b50396 := hb (x (-2) 13)
            have b50397 := hb (x (-2) 9 && x (-2) 13)
            clear * - r50395 b50396 b50397 d50390
            omega
          have d50398 : (x (-2) 9).toNat = 0 := by
            have r50399 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
            have b50400 := hb (x (-2) 1)
            have b50401 := hb (x (-2) 9)
            clear * - r50399 b50400 b50401 d50382
            omega
          have d50402 : (x (-3) 2).toNat = 1 := by
            have r50403 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b50404 := hb (x (-3) 2)
            have b50405 := hb (x (-1) 13)
            have b50406 := hb (x (-2) 1 && x (-2) 14)
            clear * - r50403 b50404 b50405 b50406 g13 d50386
            omega
          have d50407 : (x (-3) 14).toNat = 1 := by
            have r50408 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
            have b50409 := hb (x (-3) 2)
            have b50410 := hb (x (-3) 14)
            clear * - r50408 b50409 b50410 d50402
            omega
          have d50411 : (x (-4) 3).toNat = 0 := by
            have r50412 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e50413 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e50414 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b50415 := hb (x (-4) 3)
            have b50416 := hb (x (-3) 2)
            have b50417 := hb (x (-2) 13)
            have b50418 := hb (x (-1) 12)
            clear * - r50412 e50413 e50414 b50415 b50416 b50417 b50418 f50248 d50390 d50402
            omega
          have d50419 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
            have r50420 := hand1 (x (-4) 3) (x (-4) 12)
            have b50421 := hb (x (-4) 3)
            have b50422 := hb (x (-4) 3 && x (-4) 12)
            clear * - r50420 b50421 b50422 d50411
            omega
          have d50423 : (x (-4) 11).toNat = 0 := by
            have r50424 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
            have b50425 := hb (x (-4) 3)
            have b50426 := hb (x (-4) 11)
            clear * - r50424 b50425 b50426 d50411
            omega
          have r50427 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50428 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50429 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50430 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50431 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
          have e50432 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
          have e50433 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
          have e50434 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
          have e50435 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
          have e50436 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
          have r50437 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50438 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e50439 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have r50440 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50441 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e50442 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have r50443 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50444 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50445 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
          have e50446 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
          have r50447 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50448 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50449 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50450 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r50451 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
          have r50452 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
          have r50453 := hand2 (x 5 2) (x 5 6)
          have r50454 := hand2 (x 4 3) (x 4 7)
          have r50455 := hand2 (x 6 1) (x 6 7)
          have r50456 := hand1 (x (-5) 4) (x (-5) 13)
          have r50457 := hand1 (x (-6) 5) (x (-6) 14)
          have r50458 := hand1 (x 10 3) (x 10 12)
          have r50459 := hand1 (x 9 4) (x 9 13)
          have r50460 := hand1 (x 8 5) (x 8 14)
          have r50461 := hand1 (x 10 1) (x 10 12)
          have r50462 := hand1 (x 9 2) (x 9 13)
          have r50463 := hand1 (x 8 3) (x 8 14)
          have b50468 := hb (x (-7) 14)
          linarith only [r50427, r50428, r50429, r50430, e50431, e50432, e50433, e50434, e50435, e50436, r50437, e50438, e50439, r50440, e50441, e50442, r50443, r50444, e50445, e50446, r50447, r50448, r50449, r50450, r50451, r50452, r50453, r50454, r50455, r50456, r50457, r50458, r50459, r50460, r50461, r50462, r50463, b50468, d50423, d50407, d50398, d50390, f50155, g10, f50248, f50381, g16, g17, g18, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, d50227, d50191, g32, g33, g34, g35, d50160, d50394, g52, g53, g54, g55, g56, g57, d50156, g65, g66, d50419, d50223, d50243]
      · have f50547 : (x (-1) 12).toNat = 1 := by rw [h50247]; rfl
        have d50548 : (x (-2) 13).toNat = 0 := by
          have r50549 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50550 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e50551 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b50552 := hb (x (-4) 3)
          have b50553 := hb (x (-3) 2)
          have b50554 := hb (x (-2) 13)
          have b50555 := hb (x (-1) 12)
          clear * - r50549 e50550 e50551 b50552 b50553 b50554 b50555 f50547
          omega
        have d50556 : (x (-3) 2).toNat = 0 := by
          have r50557 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50558 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e50559 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b50560 := hb (x (-4) 3)
          have b50561 := hb (x (-3) 2)
          have b50562 := hb (x (-2) 13)
          have b50563 := hb (x (-1) 12)
          clear * - r50557 e50558 e50559 b50560 b50561 b50562 b50563 f50547 d50548
          omega
        have d50564 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
          have r50565 := hand1 (x (-3) 2) (x (-3) 13)
          have b50566 := hb (x (-3) 2)
          have b50567 := hb (x (-3) 2 && x (-3) 13)
          clear * - r50565 b50566 b50567 d50556
          omega
        have d50568 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
          have r50569 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50570 := hb (x (-3) 2)
          have b50571 := hb (x (-1) 13)
          have b50572 := hb (x (-2) 1 && x (-2) 14)
          clear * - r50569 b50570 b50571 b50572 g13 d50556
          omega
        have d50573 : (x (-2) 14).toNat = 1 := by
          have r50574 := hand2 (x (-2) 1) (x (-2) 14)
          have b50575 := hb (x (-2) 14)
          have b50576 := hb (x (-2) 1 && x (-2) 14)
          clear * - r50574 b50575 b50576 d50568
          omega
        have d50577 : (x (-3) 1).toNat = 0 := by
          have r50578 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50579 := hb (x (-3) 1)
          have b50580 := hb (x (-2) 14)
          clear * - r50578 b50579 b50580 d50573
          omega
        have d50581 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
          have r50582 := hand1 (x (-3) 1) (x (-3) 14)
          have b50583 := hb (x (-3) 1)
          have b50584 := hb (x (-3) 1 && x (-3) 14)
          clear * - r50582 b50583 b50584 d50577
          omega
        have d50585 : (x (-4) 2).toNat = 1 := by
          have r50586 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50587 := hb (x (-4) 2)
          have b50588 := hb (x (-2) 13)
          have b50589 := hb (x (-3) 1 && x (-3) 14)
          clear * - r50586 b50587 b50588 b50589 d50548 d50581
          omega
        have d50590 : (x (-4) 14).toNat = 1 := by
          have r50591 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
          have b50592 := hb (x (-4) 2)
          have b50593 := hb (x (-4) 14)
          clear * - r50591 b50592 b50593 d50585
          omega
        have d50594 : (x (-5) 1).toNat = 0 := by
          have r50595 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50596 := hb (x (-5) 1)
          have b50597 := hb (x (-4) 14)
          clear * - r50595 b50596 b50597 d50590
          omega
        have d50598 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
          have r50599 := hand1 (x (-5) 1) (x (-5) 12)
          have b50600 := hb (x (-5) 1)
          have b50601 := hb (x (-5) 1 && x (-5) 12)
          clear * - r50599 b50600 b50601 d50594
          omega
        have d50602 : (x (-5) 13).toNat = 0 := by
          have r50603 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
          have b50604 := hb (x (-5) 1)
          have b50605 := hb (x (-5) 13)
          clear * - r50603 b50604 b50605 d50594
          omega
        have d50606 : (x (-3) 13).toNat = 0 := by
          have r50607 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b50608 := hb (x (-3) 1)
          have b50609 := hb (x (-3) 13)
          clear * - r50607 b50608 b50609 d50577
          omega
        have d50610 : (x (-4) 3).toNat = 0 := by
          have r50611 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50612 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e50613 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b50614 := hb (x (-4) 3)
          have b50615 := hb (x (-3) 2)
          have b50616 := hb (x (-2) 13)
          have b50617 := hb (x (-1) 12)
          clear * - r50611 e50612 e50613 b50614 b50615 b50616 b50617 f50547 d50548 d50556
          omega
        have d50618 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
          have r50619 := hand1 (x (-4) 3) (x (-4) 14)
          have b50620 := hb (x (-4) 3)
          have b50621 := hb (x (-4) 3 && x (-4) 14)
          clear * - r50619 b50620 b50621 d50610
          omega
        have d50622 : (x (-4) 11).toNat = 0 := by
          have r50623 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b50624 := hb (x (-4) 3)
          have b50625 := hb (x (-4) 11)
          clear * - r50623 b50624 b50625 d50610
          omega
        have d50626 : (x (-2) 12).toNat = 0 := by
          have r50627 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50628 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e50629 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b50630 := hb (x (-5) 3)
          have b50631 := hb (x (-4) 2)
          have b50632 := hb (x (-3) 13)
          have b50633 := hb (x (-2) 12)
          clear * - r50627 e50628 e50629 b50630 b50631 b50632 b50633 d50606 d50585
          omega
        have d50634 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
          have r50635 := hand2 (x (-2) 1) (x (-2) 12)
          have b50636 := hb (x (-2) 12)
          have b50637 := hb (x (-2) 1 && x (-2) 12)
          clear * - r50635 b50636 b50637 d50626
          omega
        have d50638 : (x (-5) 3).toNat = 0 := by
          have r50639 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50640 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e50641 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b50642 := hb (x (-5) 3)
          have b50643 := hb (x (-4) 2)
          have b50644 := hb (x (-3) 13)
          have b50645 := hb (x (-2) 12)
          clear * - r50639 e50640 e50641 b50642 b50643 b50644 b50645 d50626 d50606 d50585
          omega
        have d50646 : (x (-5) 11).toNat = 0 := by
          have r50647 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
          have b50648 := hb (x (-5) 3)
          have b50649 := hb (x (-5) 11)
          clear * - r50647 b50648 b50649 d50638
          omega
        have d50650 : (x (-5) 4).toNat = 1 := by
          have r50651 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50652 := hb (x (-5) 4)
          have b50653 := hb (x (-1) 11)
          have b50654 := hb (x (-2) 1 && x (-2) 12)
          have b50655 := hb (x (-3) 2 && x (-3) 13)
          have b50656 := hb (x (-4) 3 && x (-4) 14)
          clear * - r50651 b50652 b50653 b50654 b50655 b50656 g12 d50634 d50564 d50618
          omega
        have d50657 : (x (-5) 12).toNat = 1 := by
          have r50658 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
          have b50659 := hb (x (-5) 4)
          have b50660 := hb (x (-5) 12)
          clear * - r50658 b50659 b50660 d50650
          omega
        have d50661 : (x (-6) 13).toNat = 0 := by
          have r50662 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50663 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e50664 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b50665 := hb (x (-8) 3)
          have b50666 := hb (x (-7) 2)
          have b50667 := hb (x (-6) 13)
          have b50668 := hb (x (-5) 12)
          clear * - r50662 e50663 e50664 b50665 b50666 b50667 b50668 d50657
          omega
        have d50669 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
          have r50670 := hand2 (x (-6) 2) (x (-6) 13)
          have b50671 := hb (x (-6) 13)
          have b50672 := hb (x (-6) 2 && x (-6) 13)
          clear * - r50670 b50671 b50672 d50661
          omega
        have d50673 : (x (-7) 2).toNat = 0 := by
          have r50674 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50675 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e50676 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b50677 := hb (x (-8) 3)
          have b50678 := hb (x (-7) 2)
          have b50679 := hb (x (-6) 13)
          have b50680 := hb (x (-5) 12)
          clear * - r50674 e50675 e50676 b50677 b50678 b50679 b50680 d50657 d50661
          omega
        have d50681 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
          have r50682 := hand1 (x (-7) 2) (x (-7) 13)
          have b50683 := hb (x (-7) 2)
          have b50684 := hb (x (-7) 2 && x (-7) 13)
          clear * - r50682 b50683 b50684 d50673
          omega
        have d50685 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
          have r50686 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50687 := hb (x (-7) 2)
          have b50688 := hb (x (-5) 13)
          have b50689 := hb (x (-6) 1 && x (-6) 14)
          clear * - r50686 b50687 b50688 b50689 d50602 d50673
          omega
        have d50690 : (x (-6) 14).toNat = 1 := by
          have r50691 := hand2 (x (-6) 1) (x (-6) 14)
          have b50692 := hb (x (-6) 14)
          have b50693 := hb (x (-6) 1 && x (-6) 14)
          clear * - r50691 b50692 b50693 d50685
          omega
        have d50694 : (x (-7) 1).toNat = 0 := by
          have r50695 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50696 := hb (x (-7) 1)
          have b50697 := hb (x (-6) 14)
          clear * - r50695 b50696 b50697 d50690
          omega
        have d50698 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
          have r50699 := hand1 (x (-7) 1) (x (-7) 14)
          have b50700 := hb (x (-7) 1)
          have b50701 := hb (x (-7) 1 && x (-7) 14)
          clear * - r50699 b50700 b50701 d50694
          omega
        have d50702 : (x (-8) 2).toNat = 1 := by
          have r50703 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50704 := hb (x (-8) 2)
          have b50705 := hb (x (-6) 13)
          have b50706 := hb (x (-7) 1 && x (-7) 14)
          clear * - r50703 b50704 b50705 b50706 d50661 d50698
          omega
        have d50707 : (x (-8) 14).toNat = 1 := by
          have r50708 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
          have b50709 := hb (x (-8) 2)
          have b50710 := hb (x (-8) 14)
          clear * - r50708 b50709 b50710 d50702
          omega
        have d50711 : (x (-9) 1).toNat = 0 := by
          have r50712 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50713 := hb (x (-9) 1)
          have b50714 := hb (x (-8) 14)
          clear * - r50712 b50713 b50714 d50707
          omega
        have d50715 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
          have r50716 := hand1 (x (-9) 1) (x (-9) 12)
          have b50717 := hb (x (-9) 1)
          have b50718 := hb (x (-9) 1 && x (-9) 12)
          clear * - r50716 b50717 b50718 d50711
          omega
        have d50719 : (x (-9) 13).toNat = 0 := by
          have r50720 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
          have b50721 := hb (x (-9) 1)
          have b50722 := hb (x (-9) 13)
          clear * - r50720 b50721 b50722 d50711
          omega
        have d50723 : (x (-6) 12).toNat = 0 := by
          have r50724 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50725 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e50726 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b50727 := hb (x (-9) 3)
          have b50728 := hb (x (-8) 2)
          have b50729 := hb (x (-7) 13)
          have b50730 := hb (x (-6) 12)
          clear * - r50724 e50725 e50726 b50727 b50728 b50729 b50730 d50702
          omega
        have d50731 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
          have r50732 := hand2 (x (-6) 1) (x (-6) 12)
          have b50733 := hb (x (-6) 12)
          have b50734 := hb (x (-6) 1 && x (-6) 12)
          clear * - r50732 b50733 b50734 d50723
          omega
        have d50735 : (x (-7) 13).toNat = 0 := by
          have r50736 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50737 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e50738 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b50739 := hb (x (-9) 3)
          have b50740 := hb (x (-8) 2)
          have b50741 := hb (x (-7) 13)
          have b50742 := hb (x (-6) 12)
          clear * - r50736 e50737 e50738 b50739 b50740 b50741 b50742 d50723 d50702
          omega
        have d50743 : (x (-8) 3).toNat = 0 := by
          have r50744 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50745 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e50746 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b50747 := hb (x (-8) 3)
          have b50748 := hb (x (-7) 2)
          have b50749 := hb (x (-6) 13)
          have b50750 := hb (x (-5) 12)
          clear * - r50744 e50745 e50746 b50747 b50748 b50749 b50750 d50657 d50661 d50673
          omega
        have d50751 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
          have r50752 := hand1 (x (-8) 3) (x (-8) 14)
          have b50753 := hb (x (-8) 3)
          have b50754 := hb (x (-8) 3 && x (-8) 14)
          clear * - r50752 b50753 b50754 d50743
          omega
        have d50755 : (x (-8) 11).toNat = 0 := by
          have r50756 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
          have b50757 := hb (x (-8) 3)
          have b50758 := hb (x (-8) 11)
          clear * - r50756 b50757 b50758 d50743
          omega
        have d50759 : (x (-9) 4).toNat = 1 := by
          have r50760 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50761 := hb (x (-9) 4)
          have b50762 := hb (x (-5) 11)
          have b50763 := hb (x (-6) 1 && x (-6) 12)
          have b50764 := hb (x (-7) 2 && x (-7) 13)
          have b50765 := hb (x (-8) 3 && x (-8) 14)
          clear * - r50760 b50761 b50762 b50763 b50764 b50765 d50646 d50731 d50681 d50751
          omega
        have d50766 : (x (-9) 12).toNat = 1 := by
          have r50767 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
          have b50768 := hb (x (-9) 4)
          have b50769 := hb (x (-9) 12)
          clear * - r50767 b50768 b50769 d50759
          omega
        have d50770 : (x (-10) 13).toNat = 0 := by
          have r50771 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50772 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
          have e50773 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
          have b50774 := hb (x (-12) 3)
          have b50775 := hb (x (-11) 2)
          have b50776 := hb (x (-10) 13)
          have b50777 := hb (x (-9) 12)
          clear * - r50771 e50772 e50773 b50774 b50775 b50776 b50777 d50766
          omega
        have d50778 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
          have r50779 := hand2 (x (-10) 2) (x (-10) 13)
          have b50780 := hb (x (-10) 13)
          have b50781 := hb (x (-10) 2 && x (-10) 13)
          clear * - r50779 b50780 b50781 d50770
          omega
        have d50782 : (x (-11) 2).toNat = 0 := by
          have r50783 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50784 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
          have e50785 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
          have b50786 := hb (x (-12) 3)
          have b50787 := hb (x (-11) 2)
          have b50788 := hb (x (-10) 13)
          have b50789 := hb (x (-9) 12)
          clear * - r50783 e50784 e50785 b50786 b50787 b50788 b50789 d50766 d50770
          omega
        have d50790 : (x (-10) 1 && x (-10) 14).toNat = 1 := by
          have r50791 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50792 := hb (x (-11) 2)
          have b50793 := hb (x (-9) 13)
          have b50794 := hb (x (-10) 1 && x (-10) 14)
          clear * - r50791 b50792 b50793 b50794 d50719 d50782
          omega
        have d50795 : (x (-10) 1).toNat = 1 := by
          have r50796 := hand1 (x (-10) 1) (x (-10) 14)
          have b50797 := hb (x (-10) 1)
          have b50798 := hb (x (-10) 1 && x (-10) 14)
          clear * - r50796 b50797 b50798 d50790
          omega
        have d50799 : (x (-9) 14).toNat = 0 := by
          have r50800 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50801 := hb (x (-10) 1)
          have b50802 := hb (x (-9) 14)
          clear * - r50800 b50801 b50802 d50795
          omega
        have d50803 : (x (-9) 2).toNat = 0 := by
          have r50804 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
          have b50805 := hb (x (-9) 2)
          have b50806 := hb (x (-9) 14)
          clear * - r50804 b50805 b50806 d50799
          omega
        have d50807 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
          have r50808 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50809 := hb (x (-9) 2)
          have b50810 := hb (x (-7) 13)
          have b50811 := hb (x (-8) 1 && x (-8) 14)
          clear * - r50808 b50809 b50810 b50811 d50735 d50803
          omega
        have d50812 : (x (-8) 1).toNat = 1 := by
          have r50813 := hand1 (x (-8) 1) (x (-8) 14)
          have b50814 := hb (x (-8) 1)
          have b50815 := hb (x (-8) 1 && x (-8) 14)
          clear * - r50813 b50814 b50815 d50807
          omega
        have d50816 : (x (-7) 14).toNat = 0 := by
          have r50817 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50818 := hb (x (-8) 1)
          have b50819 := hb (x (-7) 14)
          clear * - r50817 b50818 b50819 d50812
          omega
        have d50820 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
          have r50821 := hand2 (x (-7) 3) (x (-7) 14)
          have b50822 := hb (x (-7) 14)
          have b50823 := hb (x (-7) 3 && x (-7) 14)
          clear * - r50821 b50822 b50823 d50816
          omega
        have d50824 : (x (-8) 4).toNat = 1 := by
          have r50825 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b50826 := hb (x (-8) 4)
          have b50827 := hb (x (-4) 11)
          have b50828 := hb (x (-5) 1 && x (-5) 12)
          have b50829 := hb (x (-6) 2 && x (-6) 13)
          have b50830 := hb (x (-7) 3 && x (-7) 14)
          clear * - r50825 b50826 b50827 b50828 b50829 b50830 d50622 d50598 d50669 d50820
          omega
        have d50831 : (x (-8) 12).toNat = 1 := by
          have r50832 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
          have b50833 := hb (x (-8) 4)
          have b50834 := hb (x (-8) 12)
          clear * - r50832 b50833 b50834 d50824
          omega
        have d50835 : (x (-10) 2).toNat = 0 := by
          have r50836 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50837 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
          have e50838 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
          have b50839 := hb (x (-11) 3)
          have b50840 := hb (x (-10) 2)
          have b50841 := hb (x (-9) 13)
          have b50842 := hb (x (-8) 12)
          clear * - r50836 e50837 e50838 b50839 b50840 b50841 b50842 d50831 d50719
          omega
        have d50843 : (x (-11) 3).toNat = 0 := by
          have r50844 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e50845 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
          have e50846 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
          have b50847 := hb (x (-11) 3)
          have b50848 := hb (x (-10) 2)
          have b50849 := hb (x (-9) 13)
          have b50850 := hb (x (-8) 12)
          clear * - r50844 e50845 e50846 b50847 b50848 b50849 b50850 d50831 d50719 d50835
          omega
        have d50851 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
          have r50852 := hand1 (x (-11) 3) (x (-11) 14)
          have b50853 := hb (x (-11) 3)
          have b50854 := hb (x (-11) 3 && x (-11) 14)
          clear * - r50852 b50853 b50854 d50843
          omega
        have r50855 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b50856 := hb (x (-12) 4)
        have b50857 := hb (x (-8) 11)
        have b50858 := hb (x (-9) 1 && x (-9) 12)
        have b50859 := hb (x (-10) 2 && x (-10) 13)
        have b50860 := hb (x (-11) 3 && x (-11) 14)
        linarith only [r50855, b50856, b50857, b50858, b50859, b50860, d50755, d50715, d50778, d50851, g0]
    · have f50861 : (x (-1) 8).toNat = 1 := by rw [h50154]; rfl
      have d50862 : (x (-2) 9).toNat = 0 := by
        have r50863 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50864 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e50865 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e50866 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e50867 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e50868 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e50869 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b50870 := hb (x (-8) 7)
        have b50871 := hb (x (-7) 6)
        have b50872 := hb (x (-6) 5)
        have b50873 := hb (x (-5) 4)
        have b50874 := hb (x (-4) 11)
        have b50875 := hb (x (-3) 10)
        have b50876 := hb (x (-2) 9)
        have b50877 := hb (x (-1) 8)
        clear * - r50863 e50864 e50865 e50866 e50867 e50868 e50869 b50870 b50871 b50872 b50873 b50874 b50875 b50876 b50877 f50861
        omega
      have d50878 : (x (-3) 10).toNat = 0 := by
        have r50879 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50880 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e50881 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e50882 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e50883 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e50884 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e50885 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b50886 := hb (x (-8) 7)
        have b50887 := hb (x (-7) 6)
        have b50888 := hb (x (-6) 5)
        have b50889 := hb (x (-5) 4)
        have b50890 := hb (x (-4) 11)
        have b50891 := hb (x (-3) 10)
        have b50892 := hb (x (-2) 9)
        have b50893 := hb (x (-1) 8)
        clear * - r50879 e50880 e50881 e50882 e50883 e50884 e50885 b50886 b50887 b50888 b50889 b50890 b50891 b50892 b50893 f50861 d50862
        omega
      have d50894 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
        have r50895 := hand2 (x (-3) 1) (x (-3) 10)
        have b50896 := hb (x (-3) 10)
        have b50897 := hb (x (-3) 1 && x (-3) 10)
        clear * - r50895 b50896 b50897 d50878
        omega
      have d50898 : (x (-4) 11).toNat = 0 := by
        have r50899 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50900 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e50901 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e50902 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e50903 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e50904 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e50905 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b50906 := hb (x (-8) 7)
        have b50907 := hb (x (-7) 6)
        have b50908 := hb (x (-6) 5)
        have b50909 := hb (x (-5) 4)
        have b50910 := hb (x (-4) 11)
        have b50911 := hb (x (-3) 10)
        have b50912 := hb (x (-2) 9)
        have b50913 := hb (x (-1) 8)
        clear * - r50899 e50900 e50901 e50902 e50903 e50904 e50905 b50906 b50907 b50908 b50909 b50910 b50911 b50912 b50913 f50861 d50862 d50878
        omega
      have d50914 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
        have r50915 := hand2 (x (-4) 2) (x (-4) 11)
        have b50916 := hb (x (-4) 11)
        have b50917 := hb (x (-4) 2 && x (-4) 11)
        clear * - r50915 b50916 b50917 d50898
        omega
      have d50918 : (x (-5) 4).toNat = 0 := by
        have r50919 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50920 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e50921 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e50922 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e50923 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e50924 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e50925 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b50926 := hb (x (-8) 7)
        have b50927 := hb (x (-7) 6)
        have b50928 := hb (x (-6) 5)
        have b50929 := hb (x (-5) 4)
        have b50930 := hb (x (-4) 11)
        have b50931 := hb (x (-3) 10)
        have b50932 := hb (x (-2) 9)
        have b50933 := hb (x (-1) 8)
        clear * - r50919 e50920 e50921 e50922 e50923 e50924 e50925 b50926 b50927 b50928 b50929 b50930 b50931 b50932 b50933 f50861 d50862 d50878 d50898
        omega
      have d50934 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
        have r50935 := hand1 (x (-5) 4) (x (-5) 14)
        have b50936 := hb (x (-5) 4)
        have b50937 := hb (x (-5) 4 && x (-5) 14)
        clear * - r50935 b50936 b50937 d50918
        omega
      have d50938 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
        have r50939 := hand1 (x (-5) 4) (x (-5) 13)
        have b50940 := hb (x (-5) 4)
        have b50941 := hb (x (-5) 4 && x (-5) 13)
        clear * - r50939 b50940 b50941 d50918
        omega
      have d50942 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
        have r50943 := hand1 (x (-5) 4) (x (-5) 11)
        have b50944 := hb (x (-5) 4)
        have b50945 := hb (x (-5) 4 && x (-5) 11)
        clear * - r50943 b50944 b50945 d50918
        omega
      have d50946 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
        have r50947 := hand1 (x (-5) 4) (x (-5) 9)
        have b50948 := hb (x (-5) 4)
        have b50949 := hb (x (-5) 4 && x (-5) 9)
        clear * - r50947 b50948 b50949 d50918
        omega
      have d50950 : (x (-6) 5).toNat = 0 := by
        have r50951 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50952 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e50953 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e50954 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e50955 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e50956 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e50957 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b50958 := hb (x (-8) 7)
        have b50959 := hb (x (-7) 6)
        have b50960 := hb (x (-6) 5)
        have b50961 := hb (x (-5) 4)
        have b50962 := hb (x (-4) 11)
        have b50963 := hb (x (-3) 10)
        have b50964 := hb (x (-2) 9)
        have b50965 := hb (x (-1) 8)
        clear * - r50951 e50952 e50953 e50954 e50955 e50956 e50957 b50958 b50959 b50960 b50961 b50962 b50963 b50964 b50965 f50861 d50862 d50878 d50898 d50918
        omega
      have d50966 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
        have r50967 := hand1 (x (-6) 5) (x (-6) 14)
        have b50968 := hb (x (-6) 5)
        have b50969 := hb (x (-6) 5 && x (-6) 14)
        clear * - r50967 b50968 b50969 d50950
        omega
      have d50970 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
        have r50971 := hand1 (x (-6) 5) (x (-6) 12)
        have b50972 := hb (x (-6) 5)
        have b50973 := hb (x (-6) 5 && x (-6) 12)
        clear * - r50971 b50972 b50973 d50950
        omega
      have d50974 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
        have r50975 := hand1 (x (-6) 5) (x (-6) 10)
        have b50976 := hb (x (-6) 5)
        have b50977 := hb (x (-6) 5 && x (-6) 10)
        clear * - r50975 b50976 b50977 d50950
        omega
      have d50978 : (x (-7) 6).toNat = 0 := by
        have r50979 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e50980 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e50981 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e50982 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e50983 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e50984 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e50985 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b50986 := hb (x (-8) 7)
        have b50987 := hb (x (-7) 6)
        have b50988 := hb (x (-6) 5)
        have b50989 := hb (x (-5) 4)
        have b50990 := hb (x (-4) 11)
        have b50991 := hb (x (-3) 10)
        have b50992 := hb (x (-2) 9)
        have b50993 := hb (x (-1) 8)
        clear * - r50979 e50980 e50981 e50982 e50983 e50984 e50985 b50986 b50987 b50988 b50989 b50990 b50991 b50992 b50993 f50861 d50862 d50878 d50898 d50918 d50950
        omega
      have d50994 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
        have r50995 := hand1 (x (-7) 6) (x (-7) 13)
        have b50996 := hb (x (-7) 6)
        have b50997 := hb (x (-7) 6 && x (-7) 13)
        clear * - r50995 b50996 b50997 d50978
        omega
      have d50998 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
        have r50999 := hand1 (x (-7) 6) (x (-7) 11)
        have b51000 := hb (x (-7) 6)
        have b51001 := hb (x (-7) 6 && x (-7) 11)
        clear * - r50999 b51000 b51001 d50978
        omega
      have d51002 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
        have r51003 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51004 := hb (x (-7) 6)
        have b51005 := hb (x (-1) 9)
        have b51006 := hb (x (-2) 1 && x (-2) 10)
        have b51007 := hb (x (-3) 2 && x (-3) 11)
        have b51008 := hb (x (-4) 3 && x (-4) 12)
        have b51009 := hb (x (-5) 4 && x (-5) 13)
        have b51010 := hb (x (-6) 5 && x (-6) 14)
        clear * - r51003 b51004 b51005 b51006 b51007 b51008 b51009 b51010 g10 g65 g66 d50938 d50966 d50978
        omega
      have d51011 : (x (-4) 12).toNat = 1 := by
        have r51012 := hand2 (x (-4) 3) (x (-4) 12)
        have b51013 := hb (x (-4) 12)
        have b51014 := hb (x (-4) 3 && x (-4) 12)
        clear * - r51012 b51013 b51014 d51002
        omega
      have d51015 : (x (-5) 13).toNat = 0 := by
        have r51016 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51017 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e51018 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b51019 := hb (x (-7) 3)
        have b51020 := hb (x (-6) 2)
        have b51021 := hb (x (-5) 13)
        have b51022 := hb (x (-4) 12)
        clear * - r51016 e51017 e51018 b51019 b51020 b51021 b51022 d51011
        omega
      have d51023 : (x (-6) 2).toNat = 0 := by
        have r51024 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51025 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e51026 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b51027 := hb (x (-7) 3)
        have b51028 := hb (x (-6) 2)
        have b51029 := hb (x (-5) 13)
        have b51030 := hb (x (-4) 12)
        clear * - r51024 e51025 e51026 b51027 b51028 b51029 b51030 d51011 d51015
        omega
      have d51031 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
        have r51032 := hand1 (x (-6) 2) (x (-6) 13)
        have b51033 := hb (x (-6) 2)
        have b51034 := hb (x (-6) 2 && x (-6) 13)
        clear * - r51032 b51033 b51034 d51023
        omega
      have d51035 : (x (-6) 10).toNat = 0 := by
        have r51036 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have b51037 := hb (x (-6) 2)
        have b51038 := hb (x (-6) 10)
        clear * - r51036 b51037 b51038 d51023
        omega
      have d51039 : (x (-7) 3).toNat = 0 := by
        have r51040 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51041 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e51042 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b51043 := hb (x (-7) 3)
        have b51044 := hb (x (-6) 2)
        have b51045 := hb (x (-5) 13)
        have b51046 := hb (x (-4) 12)
        clear * - r51040 e51041 e51042 b51043 b51044 b51045 b51046 d51011 d51015 d51023
        omega
      have d51047 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
        have r51048 := hand1 (x (-7) 3) (x (-7) 14)
        have b51049 := hb (x (-7) 3)
        have b51050 := hb (x (-7) 3 && x (-7) 14)
        clear * - r51048 b51049 b51050 d51039
        omega
      have d51051 : (x (-7) 11).toNat = 0 := by
        have r51052 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have b51053 := hb (x (-7) 3)
        have b51054 := hb (x (-7) 11)
        clear * - r51052 b51053 b51054 d51039
        omega
      have d51055 : (x (-4) 3).toNat = 1 := by
        have r51056 := hand1 (x (-4) 3) (x (-4) 12)
        have b51057 := hb (x (-4) 3)
        have b51058 := hb (x (-4) 3 && x (-4) 12)
        clear * - r51056 b51057 b51058 d51002
        omega
      have d51059 : (x (-1) 12).toNat = 0 := by
        have r51060 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51061 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e51062 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b51063 := hb (x (-4) 3)
        have b51064 := hb (x (-3) 2)
        have b51065 := hb (x (-2) 13)
        have b51066 := hb (x (-1) 12)
        clear * - r51060 e51061 e51062 b51063 b51064 b51065 b51066 d51055
        omega
      have d51067 : (x (-2) 13).toNat = 0 := by
        have r51068 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51069 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e51070 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b51071 := hb (x (-4) 3)
        have b51072 := hb (x (-3) 2)
        have b51073 := hb (x (-2) 13)
        have b51074 := hb (x (-1) 12)
        clear * - r51068 e51069 e51070 b51071 b51072 b51073 b51074 d51059 d51055
        omega
      have d51075 : (x (-3) 2).toNat = 0 := by
        have r51076 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51077 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e51078 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b51079 := hb (x (-4) 3)
        have b51080 := hb (x (-3) 2)
        have b51081 := hb (x (-2) 13)
        have b51082 := hb (x (-1) 12)
        clear * - r51076 e51077 e51078 b51079 b51080 b51081 b51082 d51059 d51067 d51055
        omega
      have d51083 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
        have r51084 := hand1 (x (-3) 2) (x (-3) 12)
        have b51085 := hb (x (-3) 2)
        have b51086 := hb (x (-3) 2 && x (-3) 12)
        clear * - r51084 b51085 b51086 d51075
        omega
      have d51087 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
        have r51088 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51089 := hb (x (-6) 5)
        have b51090 := hb (x (-1) 10)
        have b51091 := hb (x (-2) 1 && x (-2) 11)
        have b51092 := hb (x (-3) 2 && x (-3) 12)
        have b51093 := hb (x (-4) 3 && x (-4) 13)
        have b51094 := hb (x (-5) 4 && x (-5) 14)
        clear * - r51088 b51089 b51090 b51091 b51092 b51093 b51094 g11 g69 d51083 d50934 d50950
        omega
      have d51095 : (x (-4) 13).toNat = 1 := by
        have r51096 := hand2 (x (-4) 3) (x (-4) 13)
        have b51097 := hb (x (-4) 13)
        have b51098 := hb (x (-4) 3 && x (-4) 13)
        clear * - r51096 b51097 b51098 d51087
        omega
      have d51099 : (x (-4) 1).toNat = 1 := by
        have r51100 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b51101 := hb (x (-4) 1)
        have b51102 := hb (x (-4) 13)
        clear * - r51100 b51101 b51102 d51095
        omega
      have d51103 : (x (-3) 14).toNat = 0 := by
        have r51104 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51105 := hb (x (-4) 1)
        have b51106 := hb (x (-3) 14)
        clear * - r51104 b51105 b51106 d51099
        omega
      have d51107 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
        have r51108 := hand2 (x (-3) 1) (x (-3) 14)
        have b51109 := hb (x (-3) 14)
        have b51110 := hb (x (-3) 1 && x (-3) 14)
        clear * - r51108 b51109 b51110 d51103
        omega
      have d51111 : (x (-4) 2).toNat = 1 := by
        have r51112 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51113 := hb (x (-4) 2)
        have b51114 := hb (x (-2) 13)
        have b51115 := hb (x (-3) 1 && x (-3) 14)
        clear * - r51112 b51113 b51114 b51115 d51067 d51107
        omega
      have d51116 : (x (-4) 14).toNat = 1 := by
        have r51117 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
        have b51118 := hb (x (-4) 2)
        have b51119 := hb (x (-4) 14)
        clear * - r51117 b51118 b51119 d51111
        omega
      have d51120 : (x (-5) 1).toNat = 0 := by
        have r51121 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51122 := hb (x (-5) 1)
        have b51123 := hb (x (-4) 14)
        clear * - r51121 b51122 b51123 d51116
        omega
      have d51124 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
        have r51125 := hand1 (x (-5) 1) (x (-5) 12)
        have b51126 := hb (x (-5) 1)
        have b51127 := hb (x (-5) 1 && x (-5) 12)
        clear * - r51125 b51126 b51127 d51120
        omega
      have d51128 : (x (-8) 4).toNat = 1 := by
        have r51129 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51130 := hb (x (-8) 4)
        have b51131 := hb (x (-4) 11)
        have b51132 := hb (x (-5) 1 && x (-5) 12)
        have b51133 := hb (x (-6) 2 && x (-6) 13)
        have b51134 := hb (x (-7) 3 && x (-7) 14)
        clear * - r51129 b51130 b51131 b51132 b51133 b51134 d50898 d51124 d51031 d51047
        omega
      have d51135 : (x (-8) 12).toNat = 1 := by
        have r51136 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
        have b51137 := hb (x (-8) 4)
        have b51138 := hb (x (-8) 12)
        clear * - r51136 b51137 b51138 d51128
        omega
      have d51139 : (x (-9) 13).toNat = 0 := by
        have r51140 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51141 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e51142 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b51143 := hb (x (-11) 3)
        have b51144 := hb (x (-10) 2)
        have b51145 := hb (x (-9) 13)
        have b51146 := hb (x (-8) 12)
        clear * - r51140 e51141 e51142 b51143 b51144 b51145 b51146 d51135
        omega
      have d51147 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
        have r51148 := hand2 (x (-9) 8) (x (-9) 13)
        have b51149 := hb (x (-9) 13)
        have b51150 := hb (x (-9) 8 && x (-9) 13)
        clear * - r51148 b51149 b51150 d51139
        omega
      have d51151 : (x (-9) 5).toNat = 0 := by
        have r51152 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
        have b51153 := hb (x (-9) 5)
        have b51154 := hb (x (-9) 13)
        clear * - r51152 b51153 b51154 d51139
        omega
      have d51155 : (x (-10) 2).toNat = 0 := by
        have r51156 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51157 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e51158 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b51159 := hb (x (-11) 3)
        have b51160 := hb (x (-10) 2)
        have b51161 := hb (x (-9) 13)
        have b51162 := hb (x (-8) 12)
        clear * - r51156 e51157 e51158 b51159 b51160 b51161 b51162 d51135 d51139
        omega
      have d51163 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
        have r51164 := hand1 (x (-10) 2) (x (-10) 13)
        have b51165 := hb (x (-10) 2)
        have b51166 := hb (x (-10) 2 && x (-10) 13)
        clear * - r51164 b51165 b51166 d51155
        omega
      have d51167 : (x (-11) 3).toNat = 0 := by
        have r51168 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51169 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e51170 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b51171 := hb (x (-11) 3)
        have b51172 := hb (x (-10) 2)
        have b51173 := hb (x (-9) 13)
        have b51174 := hb (x (-8) 12)
        clear * - r51168 e51169 e51170 b51171 b51172 b51173 b51174 d51135 d51139 d51155
        omega
      have d51175 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
        have r51176 := hand1 (x (-11) 3) (x (-11) 14)
        have b51177 := hb (x (-11) 3)
        have b51178 := hb (x (-11) 3 && x (-11) 14)
        clear * - r51176 b51177 b51178 d51167
        omega
      have d51179 : (x (-5) 9).toNat = 0 := by
        have r51180 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
        have b51181 := hb (x (-5) 1)
        have b51182 := hb (x (-5) 9)
        clear * - r51180 b51181 b51182 d51120
        omega
      have d51183 : (x (-2) 12).toNat = 0 := by
        have r51184 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51185 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e51186 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b51187 := hb (x (-5) 3)
        have b51188 := hb (x (-4) 2)
        have b51189 := hb (x (-3) 13)
        have b51190 := hb (x (-2) 12)
        clear * - r51184 e51185 e51186 b51187 b51188 b51189 b51190 d51111
        omega
      have d51191 : (x (-3) 13).toNat = 0 := by
        have r51192 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51193 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e51194 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b51195 := hb (x (-5) 3)
        have b51196 := hb (x (-4) 2)
        have b51197 := hb (x (-3) 13)
        have b51198 := hb (x (-2) 12)
        clear * - r51192 e51193 e51194 b51195 b51196 b51197 b51198 d51183 d51111
        omega
      have d51199 : (x (-5) 3).toNat = 0 := by
        have r51200 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51201 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e51202 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b51203 := hb (x (-5) 3)
        have b51204 := hb (x (-4) 2)
        have b51205 := hb (x (-3) 13)
        have b51206 := hb (x (-2) 12)
        clear * - r51200 e51201 e51202 b51203 b51204 b51205 b51206 d51183 d51191 d51111
        omega
      have d51207 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
        have r51208 := hand1 (x (-5) 3) (x (-5) 12)
        have b51209 := hb (x (-5) 3)
        have b51210 := hb (x (-5) 3 && x (-5) 12)
        clear * - r51208 b51209 b51210 d51199
        omega
      have d51211 : (x (-5) 11).toNat = 0 := by
        have r51212 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
        have b51213 := hb (x (-5) 3)
        have b51214 := hb (x (-5) 11)
        clear * - r51212 b51213 b51214 d51199
        omega
      have d51215 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
        have r51216 := hand1 (x (-3) 2) (x (-3) 9)
        have b51217 := hb (x (-3) 2)
        have b51218 := hb (x (-3) 2 && x (-3) 9)
        clear * - r51216 b51217 b51218 d51075
        omega
      have d51219 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
        have r51220 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51221 := hb (x (-3) 2)
        have b51222 := hb (x (-1) 13)
        have b51223 := hb (x (-2) 1 && x (-2) 14)
        clear * - r51220 b51221 b51222 b51223 g13 d51075
        omega
      have d51224 : (x (-2) 14).toNat = 1 := by
        have r51225 := hand2 (x (-2) 1) (x (-2) 14)
        have b51226 := hb (x (-2) 14)
        have b51227 := hb (x (-2) 1 && x (-2) 14)
        clear * - r51225 b51226 b51227 d51219
        omega
      have d51228 : (x (-3) 1).toNat = 0 := by
        have r51229 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51230 := hb (x (-3) 1)
        have b51231 := hb (x (-2) 14)
        clear * - r51229 b51230 b51231 d51224
        omega
      have d51232 : (x (-3) 9).toNat = 0 := by
        have r51233 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
        have b51234 := hb (x (-3) 1)
        have b51235 := hb (x (-3) 9)
        clear * - r51233 b51234 b51235 d51228
        omega
      have d51236 : (x (-8) 7).toNat = 0 := by
        have r51237 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51238 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e51239 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e51240 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e51241 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e51242 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e51243 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b51244 := hb (x (-8) 7)
        have b51245 := hb (x (-7) 6)
        have b51246 := hb (x (-6) 5)
        have b51247 := hb (x (-5) 4)
        have b51248 := hb (x (-4) 11)
        have b51249 := hb (x (-3) 10)
        have b51250 := hb (x (-2) 9)
        have b51251 := hb (x (-1) 8)
        clear * - r51237 e51238 e51239 e51240 e51241 e51242 e51243 b51244 b51245 b51246 b51247 b51248 b51249 b51250 b51251 f50861 d50862 d50878 d50898 d50918 d50950 d50978
        omega
      have d51252 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
        have r51253 := hand1 (x (-8) 7) (x (-8) 14)
        have b51254 := hb (x (-8) 7)
        have b51255 := hb (x (-8) 7 && x (-8) 14)
        clear * - r51253 b51254 b51255 d51236
        omega
      have d51256 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
        have r51257 := hand1 (x (-8) 7) (x (-8) 12)
        have b51258 := hb (x (-8) 7)
        have b51259 := hb (x (-8) 7 && x (-8) 12)
        clear * - r51257 b51258 b51259 d51236
        omega
      have d51260 : (x (-4) 8).toNat = 0 := by
        have r51261 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51262 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e51263 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e51264 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e51265 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e51266 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e51267 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b51268 := hb (x (-11) 7)
        have b51269 := hb (x (-10) 6)
        have b51270 := hb (x (-9) 5)
        have b51271 := hb (x (-8) 4)
        have b51272 := hb (x (-7) 11)
        have b51273 := hb (x (-6) 10)
        have b51274 := hb (x (-5) 9)
        have b51275 := hb (x (-4) 8)
        clear * - r51261 e51262 e51263 e51264 e51265 e51266 e51267 b51268 b51269 b51270 b51271 b51272 b51273 b51274 b51275 d51179 d51035 d51051 d51128 d51151
        omega
      have d51276 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
        have r51277 := hand2 (x (-4) 3) (x (-4) 8)
        have b51278 := hb (x (-4) 8)
        have b51279 := hb (x (-4) 3 && x (-4) 8)
        clear * - r51277 b51278 b51279 d51260
        omega
      have d51280 : (x (-10) 14).toNat = 0 := by
        have r51281 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51282 := hb (x (-10) 14)
        have b51283 := hb (x (-9) 13)
        have b51284 := hb (x (-8) 12)
        have b51285 := hb (x (-7) 11)
        have b51286 := hb (x (-6) 10)
        have b51287 := hb (x (-5) 9)
        have b51288 := hb (x (-4) 8)
        have b51289 := hb (x (-3) 7)
        have b51290 := hb (x (-2) 6)
        have b51291 := hb (x (-1) 5)
        have b51292 := hb (x 0 4)
        have b51293 := hb (x 1 3)
        have b51294 := hb (x 2 2)
        have b51295 := hb (x 3 1)
        clear * - r51281 b51282 b51283 b51284 b51285 b51286 b51287 b51288 b51289 b51290 b51291 b51292 b51293 b51294 b51295 d50124 d50115 d50144 g15 g8 g6 g4 d51260 d51179 d51035 d51051 d51135 d51139
        omega
      have d51296 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
        have r51297 := hand2 (x (-10) 1) (x (-10) 14)
        have b51298 := hb (x (-10) 14)
        have b51299 := hb (x (-10) 1 && x (-10) 14)
        clear * - r51297 b51298 b51299 d51280
        omega
      have d51300 : (x (-11) 2).toNat = 1 := by
        have r51301 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51302 := hb (x (-11) 2)
        have b51303 := hb (x (-9) 13)
        have b51304 := hb (x (-10) 1 && x (-10) 14)
        clear * - r51301 b51302 b51303 b51304 d51139 d51296
        omega
      have d51305 : (x (-9) 12).toNat = 0 := by
        have r51306 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51307 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
        have e51308 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
        have b51309 := hb (x (-12) 3)
        have b51310 := hb (x (-11) 2)
        have b51311 := hb (x (-10) 13)
        have b51312 := hb (x (-9) 12)
        clear * - r51306 e51307 e51308 b51309 b51310 b51311 b51312 d51300
        omega
      have d51313 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
        have r51314 := hand2 (x (-9) 1) (x (-9) 12)
        have b51315 := hb (x (-9) 12)
        have b51316 := hb (x (-9) 1 && x (-9) 12)
        clear * - r51314 b51315 b51316 d51305
        omega
      have d51317 : (x (-8) 11).toNat = 1 := by
        have r51318 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51319 := hb (x (-12) 4)
        have b51320 := hb (x (-8) 11)
        have b51321 := hb (x (-9) 1 && x (-9) 12)
        have b51322 := hb (x (-10) 2 && x (-10) 13)
        have b51323 := hb (x (-11) 3 && x (-11) 14)
        clear * - r51318 b51319 b51320 b51321 b51322 b51323 d51313 d51163 d51175 g0
        omega
      have d51324 : (x (-8) 3).toNat = 1 := by
        have r51325 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
        have b51326 := hb (x (-8) 3)
        have b51327 := hb (x (-8) 11)
        clear * - r51325 b51326 b51327 d51317
        omega
      have d51328 : (x (-5) 12).toNat = 0 := by
        have r51329 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51330 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e51331 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b51332 := hb (x (-8) 3)
        have b51333 := hb (x (-7) 2)
        have b51334 := hb (x (-6) 13)
        have b51335 := hb (x (-5) 12)
        clear * - r51329 e51330 e51331 b51332 b51333 b51334 b51335 d51324
        omega
      have d51336 : (x (-6) 13).toNat = 0 := by
        have r51337 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51338 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e51339 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b51340 := hb (x (-8) 3)
        have b51341 := hb (x (-7) 2)
        have b51342 := hb (x (-6) 13)
        have b51343 := hb (x (-5) 12)
        clear * - r51337 e51338 e51339 b51340 b51341 b51342 b51343 d51328 d51324
        omega
      have d51344 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
        have r51345 := hand2 (x (-6) 4) (x (-6) 13)
        have b51346 := hb (x (-6) 13)
        have b51347 := hb (x (-6) 4 && x (-6) 13)
        clear * - r51345 b51346 b51347 d51336
        omega
      have d51348 : (x (-7) 2).toNat = 0 := by
        have r51349 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51350 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e51351 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b51352 := hb (x (-8) 3)
        have b51353 := hb (x (-7) 2)
        have b51354 := hb (x (-6) 13)
        have b51355 := hb (x (-5) 12)
        clear * - r51349 e51350 e51351 b51352 b51353 b51354 b51355 d51328 d51336 d51324
        omega
      have d51356 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
        have r51357 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51358 := hb (x (-7) 2)
        have b51359 := hb (x (-5) 13)
        have b51360 := hb (x (-6) 1 && x (-6) 14)
        clear * - r51357 b51358 b51359 b51360 d51015 d51348
        omega
      have d51361 : (x (-6) 14).toNat = 1 := by
        have r51362 := hand2 (x (-6) 1) (x (-6) 14)
        have b51363 := hb (x (-6) 14)
        have b51364 := hb (x (-6) 1 && x (-6) 14)
        clear * - r51362 b51363 b51364 d51356
        omega
      have d51365 : (x (-7) 1).toNat = 0 := by
        have r51366 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51367 := hb (x (-7) 1)
        have b51368 := hb (x (-6) 14)
        clear * - r51366 b51367 b51368 d51361
        omega
      have d51369 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
        have r51370 := hand1 (x (-7) 1) (x (-7) 14)
        have b51371 := hb (x (-7) 1)
        have b51372 := hb (x (-7) 1 && x (-7) 14)
        clear * - r51370 b51371 b51372 d51365
        omega
      have d51373 : (x (-8) 2).toNat = 1 := by
        have r51374 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51375 := hb (x (-8) 2)
        have b51376 := hb (x (-6) 13)
        have b51377 := hb (x (-7) 1 && x (-7) 14)
        clear * - r51374 b51375 b51376 b51377 d51336 d51369
        omega
      have d51378 : (x (-8) 14).toNat = 1 := by
        have r51379 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
        have b51380 := hb (x (-8) 2)
        have b51381 := hb (x (-8) 14)
        clear * - r51379 b51380 b51381 d51373
        omega
      have d51382 : (x (-9) 1).toNat = 0 := by
        have r51383 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51384 := hb (x (-9) 1)
        have b51385 := hb (x (-8) 14)
        clear * - r51383 b51384 b51385 d51378
        omega
      have d51386 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
        have r51387 := hand1 (x (-9) 1) (x (-9) 14)
        have b51388 := hb (x (-9) 1)
        have b51389 := hb (x (-9) 1 && x (-9) 14)
        clear * - r51387 b51388 b51389 d51382
        omega
      have d51390 : (x (-8) 13).toNat = 1 := by
        have r51391 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51392 := hb (x (-10) 2)
        have b51393 := hb (x (-8) 13)
        have b51394 := hb (x (-9) 1 && x (-9) 14)
        clear * - r51391 b51392 b51393 b51394 d51386 d51155
        omega
      have d51395 : (x (-8) 1).toNat = 1 := by
        have r51396 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b51397 := hb (x (-8) 1)
        have b51398 := hb (x (-8) 13)
        clear * - r51396 b51397 b51398 d51390
        omega
      have d51399 : (x (-7) 14).toNat = 0 := by
        have r51400 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51401 := hb (x (-8) 1)
        have b51402 := hb (x (-7) 14)
        clear * - r51400 b51401 b51402 d51395
        omega
      have d51403 : (x (-7) 5 && x (-7) 14).toNat = 0 := by
        have r51404 := hand2 (x (-7) 5) (x (-7) 14)
        have b51405 := hb (x (-7) 14)
        have b51406 := hb (x (-7) 5 && x (-7) 14)
        clear * - r51404 b51405 b51406 d51399
        omega
      have d51407 : (x (-8) 6).toNat = 1 := by
        have r51408 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51409 := hb (x (-8) 6)
        have b51410 := hb (x (-2) 9)
        have b51411 := hb (x (-3) 1 && x (-3) 10)
        have b51412 := hb (x (-4) 2 && x (-4) 11)
        have b51413 := hb (x (-5) 3 && x (-5) 12)
        have b51414 := hb (x (-6) 4 && x (-6) 13)
        have b51415 := hb (x (-7) 5 && x (-7) 14)
        clear * - r51408 b51409 b51410 b51411 b51412 b51413 b51414 b51415 d50862 d50894 d50914 d51207 d51344 d51403
        omega
      have d51416 : (x (-2) 8).toNat = 0 := by
        have r51417 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51418 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e51419 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e51420 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e51421 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e51422 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e51423 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b51424 := hb (x (-9) 7)
        have b51425 := hb (x (-8) 6)
        have b51426 := hb (x (-7) 5)
        have b51427 := hb (x (-6) 4)
        have b51428 := hb (x (-5) 11)
        have b51429 := hb (x (-4) 10)
        have b51430 := hb (x (-3) 9)
        have b51431 := hb (x (-2) 8)
        clear * - r51417 e51418 e51419 e51420 e51421 e51422 e51423 b51424 b51425 b51426 b51427 b51428 b51429 b51430 b51431 d51232 d51211 d51407
        omega
      have d51432 : (x (-2) 1 && x (-2) 8).toNat = 0 := by
        have r51433 := hand2 (x (-2) 1) (x (-2) 8)
        have b51434 := hb (x (-2) 8)
        have b51435 := hb (x (-2) 1 && x (-2) 8)
        clear * - r51433 b51434 b51435 d51416
        omega
      have d51436 : (x (-4) 10).toNat = 0 := by
        have r51437 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51438 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e51439 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e51440 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e51441 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e51442 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e51443 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b51444 := hb (x (-9) 7)
        have b51445 := hb (x (-8) 6)
        have b51446 := hb (x (-7) 5)
        have b51447 := hb (x (-6) 4)
        have b51448 := hb (x (-5) 11)
        have b51449 := hb (x (-4) 10)
        have b51450 := hb (x (-3) 9)
        have b51451 := hb (x (-2) 8)
        clear * - r51437 e51438 e51439 e51440 e51441 e51442 e51443 b51444 b51445 b51446 b51447 b51448 b51449 b51450 b51451 d51416 d51232 d51211 d51407
        omega
      have d51452 : (x (-4) 3 && x (-4) 10).toNat = 0 := by
        have r51453 := hand2 (x (-4) 3) (x (-4) 10)
        have b51454 := hb (x (-4) 10)
        have b51455 := hb (x (-4) 3 && x (-4) 10)
        clear * - r51453 b51454 b51455 d51436
        omega
      have d51456 : (x (-9) 8).toNat = 1 := by
        have r51457 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51458 := hb (x (-9) 8)
        have b51459 := hb (x (-1) 7)
        have b51460 := hb (x (-2) 1 && x (-2) 8)
        have b51461 := hb (x (-3) 2 && x (-3) 9)
        have b51462 := hb (x (-4) 3 && x (-4) 10)
        have b51463 := hb (x (-5) 4 && x (-5) 11)
        have b51464 := hb (x (-6) 5 && x (-6) 12)
        have b51465 := hb (x (-7) 6 && x (-7) 13)
        have b51466 := hb (x (-8) 7 && x (-8) 14)
        clear * - r51457 b51458 b51459 b51460 b51461 b51462 b51463 b51464 b51465 b51466 g9 d51432 d51215 d51452 d50942 d50970 d50994 d51252
        omega
      have d51467 : (x (-10) 9).toNat = 0 := by
        have r51468 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e51469 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
        have e51470 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
        have e51471 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
        have e51472 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
        have e51473 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
        have e51474 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
        have b51475 := hb (x (-16) 7)
        have b51476 := hb (x (-15) 6)
        have b51477 := hb (x (-14) 5)
        have b51478 := hb (x (-13) 4)
        have b51479 := hb (x (-12) 11)
        have b51480 := hb (x (-11) 10)
        have b51481 := hb (x (-10) 9)
        have b51482 := hb (x (-9) 8)
        clear * - r51468 e51469 e51470 e51471 e51472 e51473 e51474 b51475 b51476 b51477 b51478 b51479 b51480 b51481 b51482 d51456
        omega
      have d51483 : (x (-10) 9 && x (-10) 14).toNat = 0 := by
        have r51484 := hand1 (x (-10) 9) (x (-10) 14)
        have b51485 := hb (x (-10) 9)
        have b51486 := hb (x (-10) 9 && x (-10) 14)
        clear * - r51484 b51485 b51486 d51467
        omega
      have d51487 : (x (-11) 10).toNat = 1 := by
        have r51488 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b51489 := hb (x (-11) 10)
        have b51490 := hb (x (-1) 5)
        have b51491 := hb (x (-2) 1 && x (-2) 6)
        have b51492 := hb (x (-3) 2 && x (-3) 7)
        have b51493 := hb (x (-4) 3 && x (-4) 8)
        have b51494 := hb (x (-5) 4 && x (-5) 9)
        have b51495 := hb (x (-6) 5 && x (-6) 10)
        have b51496 := hb (x (-7) 6 && x (-7) 11)
        have b51497 := hb (x (-8) 7 && x (-8) 12)
        have b51498 := hb (x (-9) 8 && x (-9) 13)
        have b51499 := hb (x (-10) 9 && x (-10) 14)
        clear * - r51488 b51489 b51490 b51491 b51492 b51493 b51494 b51495 b51496 b51497 b51498 b51499 g8 g36 g37 d51276 d50946 d50974 d50998 d51256 d51147 d51483
        omega
      have r51500 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e51501 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e51502 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e51503 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e51504 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e51505 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e51506 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b51507 := hb (x (-16) 7)
      have b51508 := hb (x (-15) 6)
      have b51509 := hb (x (-14) 5)
      have b51510 := hb (x (-13) 4)
      have b51511 := hb (x (-12) 11)
      have b51512 := hb (x (-11) 10)
      have b51513 := hb (x (-10) 9)
      have b51514 := hb (x (-9) 8)
      linarith only [r51500, e51501, e51502, e51503, e51504, e51505, e51506, b51507, b51508, b51509, b51510, b51511, b51512, b51513, b51514, d51456, d51467, d51487]
  · have f51515 : (x 1 7).toNat = 1 := by rw [h50152]; rfl
    have d51516 : (x 8 8).toNat = 0 := by
      have r51517 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e51518 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e51519 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e51520 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e51521 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e51522 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e51523 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b51524 := hb (x 1 7)
      have b51525 := hb (x 2 6)
      have b51526 := hb (x 3 5)
      have b51527 := hb (x 4 4)
      have b51528 := hb (x 5 11)
      have b51529 := hb (x 6 10)
      have b51530 := hb (x 7 9)
      have b51531 := hb (x 8 8)
      clear * - r51517 e51518 e51519 e51520 e51521 e51522 e51523 b51524 b51525 b51526 b51527 b51528 b51529 b51530 b51531 d50140 d50111 f51515
      omega
    have d51532 : (x 7 9).toNat = 0 := by
      have r51533 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e51534 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e51535 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e51536 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e51537 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e51538 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e51539 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b51540 := hb (x 1 7)
      have b51541 := hb (x 2 6)
      have b51542 := hb (x 3 5)
      have b51543 := hb (x 4 4)
      have b51544 := hb (x 5 11)
      have b51545 := hb (x 6 10)
      have b51546 := hb (x 7 9)
      have b51547 := hb (x 8 8)
      clear * - r51533 e51534 e51535 e51536 e51537 e51538 e51539 b51540 b51541 b51542 b51543 b51544 b51545 b51546 b51547 d51516 d50140 d50111 f51515
      omega
    have d51548 : (x 6 10).toNat = 0 := by
      have r51549 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e51550 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e51551 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e51552 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e51553 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e51554 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e51555 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b51556 := hb (x 1 7)
      have b51557 := hb (x 2 6)
      have b51558 := hb (x 3 5)
      have b51559 := hb (x 4 4)
      have b51560 := hb (x 5 11)
      have b51561 := hb (x 6 10)
      have b51562 := hb (x 7 9)
      have b51563 := hb (x 8 8)
      clear * - r51549 e51550 e51551 e51552 e51553 e51554 e51555 b51556 b51557 b51558 b51559 b51560 b51561 b51562 b51563 d51516 d51532 d50140 d50111 f51515
      omega
    have d51564 : (x 6 1 && x 6 10).toNat = 0 := by
      have r51565 := hand2 (x 6 1) (x 6 10)
      have b51566 := hb (x 6 10)
      have b51567 := hb (x 6 1 && x 6 10)
      clear * - r51565 b51566 b51567 d51548
      omega
    have d51568 : (x 5 2 && x 5 11).toNat = 1 := by
      have r51569 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b51570 := hb (x 1 6)
      have b51571 := hb (x 7 9)
      have b51572 := hb (x 6 1 && x 6 10)
      have b51573 := hb (x 5 2 && x 5 11)
      have b51574 := hb (x 4 3 && x 4 12)
      have b51575 := hb (x 3 4 && x 3 13)
      have b51576 := hb (x 2 5 && x 2 14)
      clear * - r51569 b51570 b51571 b51572 b51573 b51574 b51575 b51576 d51532 d51564 d50136 g67 g68 g21
      omega
    have d51577 : (x 5 11).toNat = 1 := by
      have r51578 := hand2 (x 5 2) (x 5 11)
      have b51579 := hb (x 5 11)
      have b51580 := hb (x 5 2 && x 5 11)
      clear * - r51578 b51579 b51580 d51568
      omega
    have r51581 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e51582 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e51583 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e51584 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e51585 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e51586 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e51587 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b51588 := hb (x 1 7)
    have b51589 := hb (x 2 6)
    have b51590 := hb (x 3 5)
    have b51591 := hb (x 4 4)
    have b51592 := hb (x 5 11)
    have b51593 := hb (x 6 10)
    have b51594 := hb (x 7 9)
    have b51595 := hb (x 8 8)
    linarith only [r51581, e51582, e51583, e51584, e51585, e51586, e51587, b51588, b51589, b51590, b51591, b51592, b51593, b51594, b51595, d51516, d51532, d51548, d51577, d50140, d50111, f51515]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111111 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-12) 4).toNat = 0)
    (g1 : (x (-5) 7).toNat = 0)
    (g2 : (x (-4) 6).toNat = 0)
    (g3 : (x (-3) 5).toNat = 0)
    (g4 : (x (-3) 7).toNat = 0)
    (g5 : (x (-2) 4).toNat = 0)
    (g6 : (x (-2) 6).toNat = 0)
    (g7 : (x (-1) 3).toNat = 0)
    (g8 : (x (-1) 5).toNat = 0)
    (g9 : (x (-1) 7).toNat = 0)
    (g10 : (x (-1) 9).toNat = 0)
    (g11 : (x (-1) 10).toNat = 0)
    (g12 : (x (-1) 11).toNat = 0)
    (g13 : (x (-1) 13).toNat = 0)
    (g14 : (x 0 2).toNat = 1)
    (g15 : (x 0 4).toNat = 1)
    (g16 : (x 0 7).toNat = 0)
    (g17 : (x 0 11).toNat = 1)
    (g18 : (x 0 13).toNat = 1)
    (g19 : (x 1 1).toNat = 1)
    (g20 : (x 1 2).toNat = 0)
    (g21 : (x 1 6).toNat = 0)
    (g22 : (x 1 10).toNat = 0)
    (g23 : (x 1 12).toNat = 0)
    (g24 : (x 2 5).toNat = 0)
    (g25 : (x 2 9).toNat = 0)
    (g26 : (x 2 11).toNat = 0)
    (g27 : (x 3 4).toNat = 0)
    (g28 : (x 3 8).toNat = 0)
    (g29 : (x 3 10).toNat = 0)
    (g30 : (x 4 9).toNat = 0)
    (g31 : (x 5 8).toNat = 0)
    (g32 : (x 3 4 && x 3 8).toNat = 0)
    (g33 : (x 2 5 && x 2 9).toNat = 0)
    (g34 : (x 1 6 && x 1 10).toNat = 0)
    (g35 : (x 0 7 && x 0 11).toNat = 0)
    (g36 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g37 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g38 : (x 1 1 && x 1 6).toNat = 0)
    (g39 : (x 0 2 && x 0 7).toNat = 0)
    (g40 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g41 : (x (-2) 4 && x (-2) 9).toNat = 0)
    (g42 : (x (-3) 5 && x (-3) 10).toNat = 0)
    (g43 : (x (-4) 6 && x (-4) 11).toNat = 0)
    (g44 : (x (-5) 7 && x (-5) 12).toNat = 0)
    (g45 : (x 0 1 && x 0 7).toNat = 0)
    (g46 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g47 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g48 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g49 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g50 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g51 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g52 : (x 5 2 && x 5 8).toNat = 0)
    (g53 : (x 4 3 && x 4 9).toNat = 0)
    (g54 : (x 3 4 && x 3 10).toNat = 0)
    (g55 : (x 2 5 && x 2 11).toNat = 0)
    (g56 : (x 1 6 && x 1 12).toNat = 0)
    (g57 : (x 0 7 && x 0 13).toNat = 0)
    (g58 : (x 6 1 && x 6 8).toNat = 0)
    (g59 : (x 5 2 && x 5 9).toNat = 0)
    (g60 : (x 4 3 && x 4 10).toNat = 0)
    (g61 : (x 3 4 && x 3 11).toNat = 0)
    (g62 : (x 2 5 && x 2 12).toNat = 0)
    (g63 : (x 1 6 && x 1 13).toNat = 0)
    (g64 : (x 0 7 && x 0 14).toNat = 0)
    (g65 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g66 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g67 : (x 3 4 && x 3 13).toNat = 0)
    (g68 : (x 2 5 && x 2 14).toNat = 0)
    (g69 : (x (-2) 1 && x (-2) 11).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_a111111_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69
