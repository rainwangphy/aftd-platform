import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b001

Topic: combinatorics   Node: cc3ff164d7e3

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core: under the layer-free tight-cover constraints for k = 15 and 17 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00001000001, cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b0000100001, cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b000010001, cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00001001, cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b0000101, cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b000011, cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b0001.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00001000001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 7).toNat = 1)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x 0 6).toNat = 0)
    (g4 : (x 0 13).toNat = 1)
    (g5 : (x 0 14).toNat = 1)
    (g6 : (x 1 5).toNat = 0)
    (g7 : (x 1 12).toNat = 0)
    (g8 : (x 1 13).toNat = 0)
    (g9 : (x 2 11).toNat = 1)
    (g10 : (x 2 12).toNat = 1)
    (g11 : (x 2 14).toNat = 1)
    (g12 : (x 3 5).toNat = 0)
    (g13 : (x 3 6).toNat = 0)
    (g14 : (x 3 10).toNat = 0)
    (g15 : (x 3 13).toNat = 0)
    (g16 : (x 4 4).toNat = 0)
    (g17 : (x 4 5).toNat = 0)
    (g18 : (x 4 9).toNat = 0)
    (g19 : (x 4 12).toNat = 0)
    (g20 : (x 5 4).toNat = 0)
    (g21 : (x 5 8).toNat = 0)
    (g22 : (x 5 4 && x 5 8).toNat = 0)
    (g23 : (x 4 5 && x 4 9).toNat = 0)
    (g24 : (x 3 6 && x 3 10).toNat = 0)
    (g25 : (x 1 8 && x 1 12).toNat = 0)
    (g26 : (x 0 9 && x 0 13).toNat = 0)
    (g27 : (x 5 4 && x 5 9).toNat = 0)
    (g28 : (x 4 5 && x 4 10).toNat = 0)
    (g29 : (x 3 6 && x 3 11).toNat = 0)
    (g30 : (x 1 8 && x 1 13).toNat = 0)
    (g31 : (x 0 9 && x 0 14).toNat = 0)
    (g32 : (x 3 3 && x 3 12).toNat = 0)
    (g33 : (x 1 5 && x 1 14).toNat = 0)
    (g34 : (x 4 2 && x 4 12).toNat = 0)
    (g35 : (x 3 3 && x 3 13).toNat = 0)
    (g36 : (x 5 1 && x 5 12).toNat = 0)
    (g37 : (x 4 2 && x 4 13).toNat = 0)
    (g38 : (x 3 3 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6085 : (x 6 8).toNat = 0 := by
    have r6086 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6087 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e6088 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e6089 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e6090 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e6091 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e6092 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b6093 := hb (x (-1) 7)
    have b6094 := hb (x 0 6)
    have b6095 := hb (x 1 5)
    have b6096 := hb (x 2 4)
    have b6097 := hb (x 3 11)
    have b6098 := hb (x 4 10)
    have b6099 := hb (x 5 9)
    have b6100 := hb (x 6 8)
    clear * - r6086 e6087 e6088 e6089 e6090 e6091 e6092 b6093 b6094 b6095 b6096 b6097 b6098 b6099 b6100 g6 g3 g1
    omega
  have d6101 : (x 6 3 && x 6 8).toNat = 0 := by
    have r6102 := hand2 (x 6 3) (x 6 8)
    have b6103 := hb (x 6 8)
    have b6104 := hb (x 6 3 && x 6 8)
    clear * - r6102 b6103 b6104 d6085
    omega
  have d6105 : (x 5 9).toNat = 0 := by
    have r6106 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6107 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e6108 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e6109 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e6110 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e6111 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e6112 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b6113 := hb (x (-1) 7)
    have b6114 := hb (x 0 6)
    have b6115 := hb (x 1 5)
    have b6116 := hb (x 2 4)
    have b6117 := hb (x 3 11)
    have b6118 := hb (x 4 10)
    have b6119 := hb (x 5 9)
    have b6120 := hb (x 6 8)
    clear * - r6106 e6107 e6108 e6109 e6110 e6111 e6112 b6113 b6114 b6115 b6116 b6117 b6118 b6119 b6120 d6085 g6 g3 g1
    omega
  have d6121 : (x 4 10).toNat = 0 := by
    have r6122 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6123 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e6124 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e6125 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e6126 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e6127 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e6128 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b6129 := hb (x (-1) 7)
    have b6130 := hb (x 0 6)
    have b6131 := hb (x 1 5)
    have b6132 := hb (x 2 4)
    have b6133 := hb (x 3 11)
    have b6134 := hb (x 4 10)
    have b6135 := hb (x 5 9)
    have b6136 := hb (x 6 8)
    clear * - r6122 e6123 e6124 e6125 e6126 e6127 e6128 b6129 b6130 b6131 b6132 b6133 b6134 b6135 b6136 d6085 d6105 g6 g3 g1
    omega
  have d6137 : (x 3 11).toNat = 0 := by
    have r6138 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6139 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e6140 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e6141 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e6142 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e6143 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e6144 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b6145 := hb (x (-1) 7)
    have b6146 := hb (x 0 6)
    have b6147 := hb (x 1 5)
    have b6148 := hb (x 2 4)
    have b6149 := hb (x 3 11)
    have b6150 := hb (x 4 10)
    have b6151 := hb (x 5 9)
    have b6152 := hb (x 6 8)
    clear * - r6138 e6139 e6140 e6141 e6142 e6143 e6144 b6145 b6146 b6147 b6148 b6149 b6150 b6151 b6152 d6085 d6105 d6121 g6 g3 g1
    omega
  have d6153 : (x 2 4).toNat = 0 := by
    have r6154 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6155 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e6156 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e6157 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e6158 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e6159 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e6160 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b6161 := hb (x (-1) 7)
    have b6162 := hb (x 0 6)
    have b6163 := hb (x 1 5)
    have b6164 := hb (x 2 4)
    have b6165 := hb (x 3 11)
    have b6166 := hb (x 4 10)
    have b6167 := hb (x 5 9)
    have b6168 := hb (x 6 8)
    clear * - r6154 e6155 e6156 e6157 e6158 e6159 e6160 b6161 b6162 b6163 b6164 b6165 b6166 b6167 b6168 d6085 d6105 d6121 d6137 g6 g3 g1
    omega
  have d6169 : (x 2 4 && x 2 14).toNat = 0 := by
    have r6170 := hand1 (x 2 4) (x 2 14)
    have b6171 := hb (x 2 4)
    have b6172 := hb (x 2 4 && x 2 14)
    clear * - r6170 b6171 b6172 d6153
    omega
  have d6173 : (x 2 4 && x 2 13).toNat = 0 := by
    have r6174 := hand1 (x 2 4) (x 2 13)
    have b6175 := hb (x 2 4)
    have b6176 := hb (x 2 4 && x 2 13)
    clear * - r6174 b6175 b6176 d6153
    omega
  have d6177 : (x 6 11).toNat = 1 := by
    have r6178 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6179 := hb (x 2 4)
    have b6180 := hb (x 6 11)
    have b6181 := hb (x 5 1 && x 5 12)
    have b6182 := hb (x 4 2 && x 4 13)
    have b6183 := hb (x 3 3 && x 3 14)
    clear * - r6178 b6179 b6180 b6181 b6182 b6183 g36 g37 g38 d6153
    omega
  have d6184 : (x 6 3).toNat = 1 := by
    have r6185 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
    have b6186 := hb (x 6 3)
    have b6187 := hb (x 6 11)
    clear * - r6185 b6186 b6187 d6177
    omega
  have d6188 : (x 9 12).toNat = 0 := by
    have r6189 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6190 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e6191 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b6192 := hb (x 6 3)
    have b6193 := hb (x 7 2)
    have b6194 := hb (x 8 13)
    have b6195 := hb (x 9 12)
    clear * - r6189 e6190 e6191 b6192 b6193 b6194 b6195 d6184
    omega
  have d6196 : (x 9 3 && x 9 12).toNat = 0 := by
    have r6197 := hand2 (x 9 3) (x 9 12)
    have b6198 := hb (x 9 12)
    have b6199 := hb (x 9 3 && x 9 12)
    clear * - r6197 b6198 b6199 d6188
    omega
  have d6200 : (x 9 5 && x 9 12).toNat = 0 := by
    have r6201 := hand2 (x 9 5) (x 9 12)
    have b6202 := hb (x 9 12)
    have b6203 := hb (x 9 5 && x 9 12)
    clear * - r6201 b6202 b6203 d6188
    omega
  have d6204 : (x 9 4).toNat = 0 := by
    have r6205 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b6206 := hb (x 9 4)
    have b6207 := hb (x 9 12)
    clear * - r6205 b6206 b6207 d6188
    omega
  have d6208 : (x 8 13).toNat = 0 := by
    have r6209 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6210 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e6211 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b6212 := hb (x 6 3)
    have b6213 := hb (x 7 2)
    have b6214 := hb (x 8 13)
    have b6215 := hb (x 9 12)
    clear * - r6209 e6210 e6211 b6212 b6213 b6214 b6215 d6188 d6184
    omega
  have d6216 : (x 8 4 && x 8 13).toNat = 0 := by
    have r6217 := hand2 (x 8 4) (x 8 13)
    have b6218 := hb (x 8 13)
    have b6219 := hb (x 8 4 && x 8 13)
    clear * - r6217 b6218 b6219 d6208
    omega
  have d6220 : (x 8 6 && x 8 13).toNat = 0 := by
    have r6221 := hand2 (x 8 6) (x 8 13)
    have b6222 := hb (x 8 13)
    have b6223 := hb (x 8 6 && x 8 13)
    clear * - r6221 b6222 b6223 d6208
    omega
  have d6224 : (x 8 5).toNat = 0 := by
    have r6225 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
    have b6226 := hb (x 8 5)
    have b6227 := hb (x 8 13)
    clear * - r6225 b6226 b6227 d6208
    omega
  have d6228 : (x 7 2).toNat = 0 := by
    have r6229 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6230 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e6231 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b6232 := hb (x 6 3)
    have b6233 := hb (x 7 2)
    have b6234 := hb (x 8 13)
    have b6235 := hb (x 9 12)
    clear * - r6229 e6230 e6231 b6232 b6233 b6234 b6235 d6188 d6208 d6184
    omega
  have d6236 : (x 7 2 && x 7 7).toNat = 0 := by
    have r6237 := hand1 (x 7 2) (x 7 7)
    have b6238 := hb (x 7 2)
    have b6239 := hb (x 7 2 && x 7 7)
    clear * - r6237 b6238 b6239 d6228
    omega
  have d6240 : (x 7 2 && x 7 6).toNat = 0 := by
    have r6241 := hand1 (x 7 2) (x 7 6)
    have b6242 := hb (x 7 2)
    have b6243 := hb (x 7 2 && x 7 6)
    clear * - r6241 b6242 b6243 d6228
    omega
  have d6244 : (x 7 10).toNat = 0 := by
    have r6245 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
    have b6246 := hb (x 7 2)
    have b6247 := hb (x 7 10)
    clear * - r6245 b6246 b6247 d6228
    omega
  have d6248 : (x 9 8).toNat = 0 := by
    have r6249 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6250 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e6251 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e6252 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e6253 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e6254 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e6255 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b6256 := hb (x 2 7)
    have b6257 := hb (x 3 6)
    have b6258 := hb (x 4 5)
    have b6259 := hb (x 5 4)
    have b6260 := hb (x 6 11)
    have b6261 := hb (x 7 10)
    have b6262 := hb (x 8 9)
    have b6263 := hb (x 9 8)
    clear * - r6249 e6250 e6251 e6252 e6253 e6254 e6255 b6256 b6257 b6258 b6259 b6260 b6261 b6262 b6263 d6244 d6177 g20 g17 g13
    omega
  have d6264 : (x 8 9).toNat = 0 := by
    have r6265 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6266 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e6267 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e6268 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e6269 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e6270 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e6271 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b6272 := hb (x 2 7)
    have b6273 := hb (x 3 6)
    have b6274 := hb (x 4 5)
    have b6275 := hb (x 5 4)
    have b6276 := hb (x 6 11)
    have b6277 := hb (x 7 10)
    have b6278 := hb (x 8 9)
    have b6279 := hb (x 9 8)
    clear * - r6265 e6266 e6267 e6268 e6269 e6270 e6271 b6272 b6273 b6274 b6275 b6276 b6277 b6278 b6279 d6248 d6244 d6177 g20 g17 g13
    omega
  have d6280 : (x 2 7).toNat = 0 := by
    have r6281 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6282 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e6283 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e6284 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e6285 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e6286 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e6287 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b6288 := hb (x 2 7)
    have b6289 := hb (x 3 6)
    have b6290 := hb (x 4 5)
    have b6291 := hb (x 5 4)
    have b6292 := hb (x 6 11)
    have b6293 := hb (x 7 10)
    have b6294 := hb (x 8 9)
    have b6295 := hb (x 9 8)
    clear * - r6281 e6282 e6283 e6284 e6285 e6286 e6287 b6288 b6289 b6290 b6291 b6292 b6293 b6294 b6295 d6248 d6264 d6244 d6177 g20 g17 g13
    omega
  have d6296 : (x 2 7 && x 2 12).toNat = 0 := by
    have r6297 := hand1 (x 2 7) (x 2 12)
    have b6298 := hb (x 2 7)
    have b6299 := hb (x 2 7 && x 2 12)
    clear * - r6297 b6298 b6299 d6280
    omega
  have d6300 : (x 2 7 && x 2 11).toNat = 0 := by
    have r6301 := hand1 (x 2 7) (x 2 11)
    have b6302 := hb (x 2 7)
    have b6303 := hb (x 2 7 && x 2 11)
    clear * - r6301 b6302 b6303 d6280
    omega
  have d6304 : (x 6 3 && x 6 7).toNat = 1 := by
    have r6305 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6306 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
    have e6307 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
    have b6308 := hb (x (-2) 11)
    have b6309 := hb (x (-1) 10)
    have b6310 := hb (x 8 5)
    have b6311 := hb (x 9 4)
    have b6312 := hb (x 7 2 && x 7 6)
    have b6313 := hb (x 6 3 && x 6 7)
    have b6314 := hb (x 5 4 && x 5 8)
    have b6315 := hb (x 4 5 && x 4 9)
    have b6316 := hb (x 3 6 && x 3 10)
    have b6317 := hb (x 2 7 && x 2 11)
    have b6318 := hb (x 1 8 && x 1 12)
    have b6319 := hb (x 0 9 && x 0 13)
    clear * - r6305 e6306 e6307 b6308 b6309 b6310 b6311 b6312 b6313 b6314 b6315 b6316 b6317 b6318 b6319 d6204 d6224 d6240 g22 g23 g24 d6300 g25 g26 g2 g0
    omega
  have d6320 : (x 6 7).toNat = 1 := by
    have r6321 := hand2 (x 6 3) (x 6 7)
    have b6322 := hb (x 6 7)
    have b6323 := hb (x 6 3 && x 6 7)
    clear * - r6321 b6322 b6323 d6304
    omega
  have d6324 : (x 13 8).toNat = 0 := by
    have r6325 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6326 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e6327 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e6328 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e6329 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e6330 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e6331 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b6332 := hb (x 6 7)
    have b6333 := hb (x 7 6)
    have b6334 := hb (x 8 5)
    have b6335 := hb (x 9 4)
    have b6336 := hb (x 10 11)
    have b6337 := hb (x 11 10)
    have b6338 := hb (x 12 9)
    have b6339 := hb (x 13 8)
    clear * - r6325 e6326 e6327 e6328 e6329 e6330 e6331 b6332 b6333 b6334 b6335 b6336 b6337 b6338 b6339 d6204 d6224 d6320
    omega
  have d6340 : (x 13 1 && x 13 8).toNat = 0 := by
    have r6341 := hand2 (x 13 1) (x 13 8)
    have b6342 := hb (x 13 8)
    have b6343 := hb (x 13 1 && x 13 8)
    clear * - r6341 b6342 b6343 d6324
    omega
  have d6344 : (x 12 9).toNat = 0 := by
    have r6345 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6346 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e6347 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e6348 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e6349 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e6350 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e6351 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b6352 := hb (x 6 7)
    have b6353 := hb (x 7 6)
    have b6354 := hb (x 8 5)
    have b6355 := hb (x 9 4)
    have b6356 := hb (x 10 11)
    have b6357 := hb (x 11 10)
    have b6358 := hb (x 12 9)
    have b6359 := hb (x 13 8)
    clear * - r6345 e6346 e6347 e6348 e6349 e6350 e6351 b6352 b6353 b6354 b6355 b6356 b6357 b6358 b6359 d6324 d6204 d6224 d6320
    omega
  have d6360 : (x 12 2 && x 12 9).toNat = 0 := by
    have r6361 := hand2 (x 12 2) (x 12 9)
    have b6362 := hb (x 12 9)
    have b6363 := hb (x 12 2 && x 12 9)
    clear * - r6361 b6362 b6363 d6344
    omega
  have d6364 : (x 11 10).toNat = 0 := by
    have r6365 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6366 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e6367 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e6368 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e6369 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e6370 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e6371 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b6372 := hb (x 6 7)
    have b6373 := hb (x 7 6)
    have b6374 := hb (x 8 5)
    have b6375 := hb (x 9 4)
    have b6376 := hb (x 10 11)
    have b6377 := hb (x 11 10)
    have b6378 := hb (x 12 9)
    have b6379 := hb (x 13 8)
    clear * - r6365 e6366 e6367 e6368 e6369 e6370 e6371 b6372 b6373 b6374 b6375 b6376 b6377 b6378 b6379 d6324 d6344 d6204 d6224 d6320
    omega
  have d6380 : (x 11 1 && x 11 10).toNat = 0 := by
    have r6381 := hand2 (x 11 1) (x 11 10)
    have b6382 := hb (x 11 10)
    have b6383 := hb (x 11 1 && x 11 10)
    clear * - r6381 b6382 b6383 d6364
    omega
  have d6384 : (x 11 3 && x 11 10).toNat = 0 := by
    have r6385 := hand2 (x 11 3) (x 11 10)
    have b6386 := hb (x 11 10)
    have b6387 := hb (x 11 3 && x 11 10)
    clear * - r6385 b6386 b6387 d6364
    omega
  have d6388 : (x 10 11).toNat = 0 := by
    have r6389 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6390 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e6391 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e6392 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e6393 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e6394 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e6395 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b6396 := hb (x 6 7)
    have b6397 := hb (x 7 6)
    have b6398 := hb (x 8 5)
    have b6399 := hb (x 9 4)
    have b6400 := hb (x 10 11)
    have b6401 := hb (x 11 10)
    have b6402 := hb (x 12 9)
    have b6403 := hb (x 13 8)
    clear * - r6389 e6390 e6391 e6392 e6393 e6394 e6395 b6396 b6397 b6398 b6399 b6400 b6401 b6402 b6403 d6324 d6344 d6364 d6204 d6224 d6320
    omega
  have d6404 : (x 10 2 && x 10 11).toNat = 0 := by
    have r6405 := hand2 (x 10 2) (x 10 11)
    have b6406 := hb (x 10 11)
    have b6407 := hb (x 10 2 && x 10 11)
    clear * - r6405 b6406 b6407 d6388
    omega
  have d6408 : (x 10 4 && x 10 11).toNat = 0 := by
    have r6409 := hand2 (x 10 4) (x 10 11)
    have b6410 := hb (x 10 11)
    have b6411 := hb (x 10 4 && x 10 11)
    clear * - r6409 b6410 b6411 d6388
    omega
  have d6412 : (x 7 6).toNat = 0 := by
    have r6413 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6414 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e6415 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e6416 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e6417 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e6418 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e6419 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b6420 := hb (x 6 7)
    have b6421 := hb (x 7 6)
    have b6422 := hb (x 8 5)
    have b6423 := hb (x 9 4)
    have b6424 := hb (x 10 11)
    have b6425 := hb (x 11 10)
    have b6426 := hb (x 12 9)
    have b6427 := hb (x 13 8)
    clear * - r6413 e6414 e6415 e6416 e6417 e6418 e6419 b6420 b6421 b6422 b6423 b6424 b6425 b6426 b6427 d6324 d6344 d6364 d6388 d6204 d6224 d6320
    omega
  have d6428 : (x 12 1).toNat = 0 := by
    have r6429 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6430 := hb (x (-1) 14)
    have b6431 := hb (x 0 13)
    have b6432 := hb (x 1 12)
    have b6433 := hb (x 2 11)
    have b6434 := hb (x 3 10)
    have b6435 := hb (x 4 9)
    have b6436 := hb (x 5 8)
    have b6437 := hb (x 6 7)
    have b6438 := hb (x 7 6)
    have b6439 := hb (x 8 5)
    have b6440 := hb (x 9 4)
    have b6441 := hb (x 10 3)
    have b6442 := hb (x 11 2)
    have b6443 := hb (x 12 1)
    clear * - r6429 b6430 b6431 b6432 b6433 b6434 b6435 b6436 b6437 b6438 b6439 b6440 b6441 b6442 b6443 d6204 d6224 d6412 d6320 g21 g18 g14 g9 g7 g4
    omega
  have d6444 : (x 12 1 && x 12 14).toNat = 0 := by
    have r6445 := hand1 (x 12 1) (x 12 14)
    have b6446 := hb (x 12 1)
    have b6447 := hb (x 12 1 && x 12 14)
    clear * - r6445 b6446 b6447 d6428
    omega
  have d6448 : (x 11 2).toNat = 0 := by
    have r6449 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6450 := hb (x (-1) 14)
    have b6451 := hb (x 0 13)
    have b6452 := hb (x 1 12)
    have b6453 := hb (x 2 11)
    have b6454 := hb (x 3 10)
    have b6455 := hb (x 4 9)
    have b6456 := hb (x 5 8)
    have b6457 := hb (x 6 7)
    have b6458 := hb (x 7 6)
    have b6459 := hb (x 8 5)
    have b6460 := hb (x 9 4)
    have b6461 := hb (x 10 3)
    have b6462 := hb (x 11 2)
    have b6463 := hb (x 12 1)
    clear * - r6449 b6450 b6451 b6452 b6453 b6454 b6455 b6456 b6457 b6458 b6459 b6460 b6461 b6462 b6463 d6428 d6204 d6224 d6412 d6320 g21 g18 g14 g9 g7 g4
    omega
  have d6464 : (x 13 13).toNat = 1 := by
    have r6465 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6466 := hb (x 11 2)
    have b6467 := hb (x 13 13)
    have b6468 := hb (x 12 1 && x 12 14)
    clear * - r6465 b6466 b6467 b6468 d6444 d6448
    omega
  have d6469 : (x 13 1).toNat = 1 := by
    have r6470 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
    have b6471 := hb (x 13 1)
    have b6472 := hb (x 13 13)
    clear * - r6470 b6471 b6472 d6464
    omega
  have d6473 : (x 14 14).toNat = 0 := by
    have r6474 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6475 := hb (x 13 1)
    have b6476 := hb (x 14 14)
    clear * - r6474 b6475 b6476 d6469
    omega
  have d6477 : (x 14 6).toNat = 0 := by
    have r6478 : (x 14 6).toNat ≤ (x 14 14).toNat := himp _ _ (hp6 14)
    have b6479 := hb (x 14 6)
    have b6480 := hb (x 14 14)
    clear * - r6478 b6479 b6480 d6473
    omega
  have d6481 : (x 14 2).toNat = 0 := by
    have r6482 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
    have b6483 := hb (x 14 2)
    have b6484 := hb (x 14 14)
    clear * - r6482 b6483 b6484 d6473
    omega
  have d6485 : (x 14 10).toNat = 0 := by
    have r6486 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
    have b6487 := hb (x 14 2)
    have b6488 := hb (x 14 10)
    clear * - r6486 b6487 b6488 d6481
    omega
  have d6489 : (x 12 2).toNat = 0 := by
    have r6490 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6491 := hb (x 0 14)
    have b6492 := hb (x 1 13)
    have b6493 := hb (x 2 12)
    have b6494 := hb (x 3 11)
    have b6495 := hb (x 4 10)
    have b6496 := hb (x 5 9)
    have b6497 := hb (x 6 8)
    have b6498 := hb (x 7 7)
    have b6499 := hb (x 8 6)
    have b6500 := hb (x 9 5)
    have b6501 := hb (x 10 4)
    have b6502 := hb (x 11 3)
    have b6503 := hb (x 12 2)
    have b6504 := hb (x 13 1)
    clear * - r6490 b6491 b6492 b6493 b6494 b6495 b6496 b6497 b6498 b6499 b6500 b6501 b6502 b6503 b6504 d6469 d6085 d6105 d6121 d6137 g10 g8 g5
    omega
  have d6505 : (x 12 2 && x 12 12).toNat = 0 := by
    have r6506 := hand1 (x 12 2) (x 12 12)
    have b6507 := hb (x 12 2)
    have b6508 := hb (x 12 2 && x 12 12)
    clear * - r6506 b6507 b6508 d6489
    omega
  have d6509 : (x 11 3).toNat = 0 := by
    have r6510 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6511 := hb (x 0 14)
    have b6512 := hb (x 1 13)
    have b6513 := hb (x 2 12)
    have b6514 := hb (x 3 11)
    have b6515 := hb (x 4 10)
    have b6516 := hb (x 5 9)
    have b6517 := hb (x 6 8)
    have b6518 := hb (x 7 7)
    have b6519 := hb (x 8 6)
    have b6520 := hb (x 9 5)
    have b6521 := hb (x 10 4)
    have b6522 := hb (x 11 3)
    have b6523 := hb (x 12 2)
    have b6524 := hb (x 13 1)
    clear * - r6510 b6511 b6512 b6513 b6514 b6515 b6516 b6517 b6518 b6519 b6520 b6521 b6522 b6523 b6524 d6469 d6489 d6085 d6105 d6121 d6137 g10 g8 g5
    omega
  have d6525 : (x 11 3 && x 11 13).toNat = 0 := by
    have r6526 := hand1 (x 11 3) (x 11 13)
    have b6527 := hb (x 11 3)
    have b6528 := hb (x 11 3 && x 11 13)
    clear * - r6526 b6527 b6528 d6509
    omega
  have d6529 : (x 10 4).toNat = 0 := by
    have r6530 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6531 := hb (x 0 14)
    have b6532 := hb (x 1 13)
    have b6533 := hb (x 2 12)
    have b6534 := hb (x 3 11)
    have b6535 := hb (x 4 10)
    have b6536 := hb (x 5 9)
    have b6537 := hb (x 6 8)
    have b6538 := hb (x 7 7)
    have b6539 := hb (x 8 6)
    have b6540 := hb (x 9 5)
    have b6541 := hb (x 10 4)
    have b6542 := hb (x 11 3)
    have b6543 := hb (x 12 2)
    have b6544 := hb (x 13 1)
    clear * - r6530 b6531 b6532 b6533 b6534 b6535 b6536 b6537 b6538 b6539 b6540 b6541 b6542 b6543 b6544 d6469 d6489 d6509 d6085 d6105 d6121 d6137 g10 g8 g5
    omega
  have d6545 : (x 10 4 && x 10 14).toNat = 0 := by
    have r6546 := hand1 (x 10 4) (x 10 14)
    have b6547 := hb (x 10 4)
    have b6548 := hb (x 10 4 && x 10 14)
    clear * - r6546 b6547 b6548 d6529
    omega
  have d6549 : (x 9 5).toNat = 0 := by
    have r6550 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6551 := hb (x 0 14)
    have b6552 := hb (x 1 13)
    have b6553 := hb (x 2 12)
    have b6554 := hb (x 3 11)
    have b6555 := hb (x 4 10)
    have b6556 := hb (x 5 9)
    have b6557 := hb (x 6 8)
    have b6558 := hb (x 7 7)
    have b6559 := hb (x 8 6)
    have b6560 := hb (x 9 5)
    have b6561 := hb (x 10 4)
    have b6562 := hb (x 11 3)
    have b6563 := hb (x 12 2)
    have b6564 := hb (x 13 1)
    clear * - r6550 b6551 b6552 b6553 b6554 b6555 b6556 b6557 b6558 b6559 b6560 b6561 b6562 b6563 b6564 d6469 d6489 d6509 d6529 d6085 d6105 d6121 d6137 g10 g8 g5
    omega
  have d6565 : (x 13 1 && x 13 11).toNat = 1 := by
    have r6566 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6567 := hb (x 9 5)
    have b6568 := hb (x 14 10)
    have b6569 := hb (x 13 1 && x 13 11)
    have b6570 := hb (x 12 2 && x 12 12)
    have b6571 := hb (x 11 3 && x 11 13)
    have b6572 := hb (x 10 4 && x 10 14)
    clear * - r6566 b6567 b6568 b6569 b6570 b6571 b6572 d6485 d6505 d6525 d6545 d6549
    omega
  have d6573 : (x 13 11).toNat = 1 := by
    have r6574 := hand2 (x 13 1) (x 13 11)
    have b6575 := hb (x 13 11)
    have b6576 := hb (x 13 1 && x 13 11)
    clear * - r6574 b6575 b6576 d6565
    omega
  have d6577 : (x 13 3).toNat = 1 := by
    have r6578 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
    have b6579 := hb (x 13 3)
    have b6580 := hb (x 13 11)
    clear * - r6578 b6579 b6580 d6573
    omega
  have d6581 : (x 16 12).toNat = 0 := by
    have r6582 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6583 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e6584 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b6585 := hb (x 13 3)
    have b6586 := hb (x 14 2)
    have b6587 := hb (x 15 13)
    have b6588 := hb (x 16 12)
    clear * - r6582 e6583 e6584 b6585 b6586 b6587 b6588 d6481 d6577
    omega
  have d6589 : (x 16 4).toNat = 0 := by
    have r6590 : (x 16 4).toNat ≤ (x 16 12).toNat := himp _ _ (hp4 16)
    have b6591 := hb (x 16 4)
    have b6592 := hb (x 16 12)
    clear * - r6590 b6591 b6592 d6581
    omega
  have d6593 : (x 16 4 && x 16 13).toNat = 0 := by
    have r6594 := hand1 (x 16 4) (x 16 13)
    have b6595 := hb (x 16 4)
    have b6596 := hb (x 16 4 && x 16 13)
    clear * - r6594 b6595 b6596 d6589
    omega
  have d6597 : (x 15 13).toNat = 0 := by
    have r6598 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6599 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e6600 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b6601 := hb (x 13 3)
    have b6602 := hb (x 14 2)
    have b6603 := hb (x 15 13)
    have b6604 := hb (x 16 12)
    clear * - r6598 e6599 e6600 b6601 b6602 b6603 b6604 d6581 d6481 d6577
    omega
  have d6605 : (x 15 5).toNat = 0 := by
    have r6606 : (x 15 5).toNat ≤ (x 15 13).toNat := himp _ _ (hp5 15)
    have b6607 := hb (x 15 5)
    have b6608 := hb (x 15 13)
    clear * - r6606 b6607 b6608 d6597
    omega
  have d6609 : (x 15 5 && x 15 14).toNat = 0 := by
    have r6610 := hand1 (x 15 5) (x 15 14)
    have b6611 := hb (x 15 5)
    have b6612 := hb (x 15 5 && x 15 14)
    clear * - r6610 b6611 b6612 d6605
    omega
  have d6613 : (x 16 8).toNat = 0 := by
    have r6614 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6615 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e6616 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e6617 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e6618 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e6619 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e6620 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b6621 := hb (x 9 7)
    have b6622 := hb (x 10 6)
    have b6623 := hb (x 11 5)
    have b6624 := hb (x 12 4)
    have b6625 := hb (x 13 11)
    have b6626 := hb (x 14 10)
    have b6627 := hb (x 15 9)
    have b6628 := hb (x 16 8)
    clear * - r6614 e6615 e6616 e6617 e6618 e6619 e6620 b6621 b6622 b6623 b6624 b6625 b6626 b6627 b6628 d6485 d6573
    omega
  have d6629 : (x 15 9).toNat = 0 := by
    have r6630 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6631 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e6632 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e6633 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e6634 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e6635 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e6636 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b6637 := hb (x 9 7)
    have b6638 := hb (x 10 6)
    have b6639 := hb (x 11 5)
    have b6640 := hb (x 12 4)
    have b6641 := hb (x 13 11)
    have b6642 := hb (x 14 10)
    have b6643 := hb (x 15 9)
    have b6644 := hb (x 16 8)
    clear * - r6630 e6631 e6632 e6633 e6634 e6635 e6636 b6637 b6638 b6639 b6640 b6641 b6642 b6643 b6644 d6613 d6485 d6573
    omega
  have d6645 : (x 12 4).toNat = 0 := by
    have r6646 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6647 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e6648 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e6649 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e6650 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e6651 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e6652 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b6653 := hb (x 9 7)
    have b6654 := hb (x 10 6)
    have b6655 := hb (x 11 5)
    have b6656 := hb (x 12 4)
    have b6657 := hb (x 13 11)
    have b6658 := hb (x 14 10)
    have b6659 := hb (x 15 9)
    have b6660 := hb (x 16 8)
    clear * - r6646 e6647 e6648 e6649 e6650 e6651 e6652 b6653 b6654 b6655 b6656 b6657 b6658 b6659 b6660 d6613 d6629 d6485 d6573
    omega
  have d6661 : (x 11 5).toNat = 0 := by
    have r6662 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6663 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e6664 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e6665 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e6666 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e6667 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e6668 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b6669 := hb (x 9 7)
    have b6670 := hb (x 10 6)
    have b6671 := hb (x 11 5)
    have b6672 := hb (x 12 4)
    have b6673 := hb (x 13 11)
    have b6674 := hb (x 14 10)
    have b6675 := hb (x 15 9)
    have b6676 := hb (x 16 8)
    clear * - r6662 e6663 e6664 e6665 e6666 e6667 e6668 b6669 b6670 b6671 b6672 b6673 b6674 b6675 b6676 d6613 d6629 d6485 d6573 d6645
    omega
  have d6677 : (x 10 6).toNat = 0 := by
    have r6678 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6679 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e6680 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e6681 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e6682 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e6683 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e6684 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b6685 := hb (x 9 7)
    have b6686 := hb (x 10 6)
    have b6687 := hb (x 11 5)
    have b6688 := hb (x 12 4)
    have b6689 := hb (x 13 11)
    have b6690 := hb (x 14 10)
    have b6691 := hb (x 15 9)
    have b6692 := hb (x 16 8)
    clear * - r6678 e6679 e6680 e6681 e6682 e6683 e6684 b6685 b6686 b6687 b6688 b6689 b6690 b6691 b6692 d6613 d6629 d6485 d6573 d6645 d6661
    omega
  have d6693 : (x 9 7).toNat = 0 := by
    have r6694 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6695 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e6696 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e6697 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e6698 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e6699 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e6700 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b6701 := hb (x 9 7)
    have b6702 := hb (x 10 6)
    have b6703 := hb (x 11 5)
    have b6704 := hb (x 12 4)
    have b6705 := hb (x 13 11)
    have b6706 := hb (x 14 10)
    have b6707 := hb (x 15 9)
    have b6708 := hb (x 16 8)
    clear * - r6694 e6695 e6696 e6697 e6698 e6699 e6700 b6701 b6702 b6703 b6704 b6705 b6706 b6707 b6708 d6613 d6629 d6485 d6573 d6645 d6661 d6677
    omega
  have d6709 : (x 8 1 && x 8 6).toNat = 1 := by
    have r6710 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6711 := hb (x (-1) 10)
    have b6712 := hb (x 9 5)
    have b6713 := hb (x 8 1 && x 8 6)
    have b6714 := hb (x 7 2 && x 7 7)
    have b6715 := hb (x 6 3 && x 6 8)
    have b6716 := hb (x 5 4 && x 5 9)
    have b6717 := hb (x 4 5 && x 4 10)
    have b6718 := hb (x 3 6 && x 3 11)
    have b6719 := hb (x 2 7 && x 2 12)
    have b6720 := hb (x 1 8 && x 1 13)
    have b6721 := hb (x 0 9 && x 0 14)
    clear * - r6710 b6711 b6712 b6713 b6714 b6715 b6716 b6717 b6718 b6719 b6720 b6721 d6549 d6236 d6101 g27 g28 g29 d6296 g30 g31 g2
    omega
  have d6722 : (x 8 6).toNat = 1 := by
    have r6723 := hand2 (x 8 1) (x 8 6)
    have b6724 := hb (x 8 6)
    have b6725 := hb (x 8 1 && x 8 6)
    clear * - r6723 b6724 b6725 d6709
    omega
  have d6726 : (x 8 14).toNat = 1 := by
    have r6727 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
    have b6728 := hb (x 8 6)
    have b6729 := hb (x 8 14)
    clear * - r6727 b6728 b6729 d6722
    omega
  have d6730 : (x 7 1).toNat = 0 := by
    have r6731 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6732 := hb (x 7 1)
    have b6733 := hb (x 8 14)
    clear * - r6731 b6732 b6733 d6726
    omega
  have d6734 : (x 7 1 && x 7 14).toNat = 0 := by
    have r6735 := hand1 (x 7 1) (x 7 14)
    have b6736 := hb (x 7 1)
    have b6737 := hb (x 7 1 && x 7 14)
    clear * - r6735 b6736 b6737 d6730
    omega
  have d6738 : (x 6 2).toNat = 1 := by
    have r6739 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6740 := hb (x 6 2)
    have b6741 := hb (x 8 13)
    have b6742 := hb (x 7 1 && x 7 14)
    clear * - r6739 b6740 b6741 b6742 d6208 d6734
    omega
  have d6743 : (x 6 14).toNat = 1 := by
    have r6744 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b6745 := hb (x 6 2)
    have b6746 := hb (x 6 14)
    clear * - r6744 b6745 b6746 d6738
    omega
  have d6747 : (x 5 1).toNat = 0 := by
    have r6748 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6749 := hb (x 5 1)
    have b6750 := hb (x 6 14)
    clear * - r6748 b6749 b6750 d6743
    omega
  have d6751 : (x 5 1 && x 5 11).toNat = 0 := by
    have r6752 := hand1 (x 5 1) (x 5 11)
    have b6753 := hb (x 5 1)
    have b6754 := hb (x 5 1 && x 5 11)
    clear * - r6752 b6753 b6754 d6747
    omega
  have d6755 : (x 6 10).toNat = 1 := by
    have r6756 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6757 := hb (x 1 5)
    have b6758 := hb (x 6 10)
    have b6759 := hb (x 5 1 && x 5 11)
    have b6760 := hb (x 4 2 && x 4 12)
    have b6761 := hb (x 3 3 && x 3 13)
    have b6762 := hb (x 2 4 && x 2 14)
    clear * - r6756 b6757 b6758 b6759 b6760 b6761 b6762 d6751 g34 g35 d6169 g6
    omega
  have d6763 : (x 8 8).toNat = 0 := by
    have r6764 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6765 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e6766 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e6767 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e6768 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e6769 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e6770 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b6771 := hb (x 1 7)
    have b6772 := hb (x 2 6)
    have b6773 := hb (x 3 5)
    have b6774 := hb (x 4 4)
    have b6775 := hb (x 5 11)
    have b6776 := hb (x 6 10)
    have b6777 := hb (x 7 9)
    have b6778 := hb (x 8 8)
    clear * - r6764 e6765 e6766 e6767 e6768 e6769 e6770 b6771 b6772 b6773 b6774 b6775 b6776 b6777 b6778 d6755 g16 g12
    omega
  have d6779 : (x 7 9).toNat = 0 := by
    have r6780 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6781 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e6782 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e6783 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e6784 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e6785 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e6786 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b6787 := hb (x 1 7)
    have b6788 := hb (x 2 6)
    have b6789 := hb (x 3 5)
    have b6790 := hb (x 4 4)
    have b6791 := hb (x 5 11)
    have b6792 := hb (x 6 10)
    have b6793 := hb (x 7 9)
    have b6794 := hb (x 8 8)
    clear * - r6780 e6781 e6782 e6783 e6784 e6785 e6786 b6787 b6788 b6789 b6790 b6791 b6792 b6793 b6794 d6763 d6755 g16 g12
    omega
  have d6795 : (x 5 11).toNat = 0 := by
    have r6796 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6797 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e6798 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e6799 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e6800 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e6801 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e6802 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b6803 := hb (x 1 7)
    have b6804 := hb (x 2 6)
    have b6805 := hb (x 3 5)
    have b6806 := hb (x 4 4)
    have b6807 := hb (x 5 11)
    have b6808 := hb (x 6 10)
    have b6809 := hb (x 7 9)
    have b6810 := hb (x 8 8)
    clear * - r6796 e6797 e6798 e6799 e6800 e6801 e6802 b6803 b6804 b6805 b6806 b6807 b6808 b6809 b6810 d6763 d6779 d6755 g16 g12
    omega
  have d6811 : (x 15 1).toNat = 0 := by
    have r6812 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6813 := hb (x 2 14)
    have b6814 := hb (x 3 13)
    have b6815 := hb (x 4 12)
    have b6816 := hb (x 5 11)
    have b6817 := hb (x 6 10)
    have b6818 := hb (x 7 9)
    have b6819 := hb (x 8 8)
    have b6820 := hb (x 9 7)
    have b6821 := hb (x 10 6)
    have b6822 := hb (x 11 5)
    have b6823 := hb (x 12 4)
    have b6824 := hb (x 13 3)
    have b6825 := hb (x 14 2)
    have b6826 := hb (x 15 1)
    clear * - r6812 b6813 b6814 b6815 b6816 b6817 b6818 b6819 b6820 b6821 b6822 b6823 b6824 b6825 b6826 d6481 d6577 d6645 d6661 d6677 d6693 d6763 d6779 d6755 d6795 g19 g15 g11
    omega
  have d6827 : (x 15 1 && x 15 14).toNat = 0 := by
    have r6828 := hand1 (x 15 1) (x 15 14)
    have b6829 := hb (x 15 1)
    have b6830 := hb (x 15 1 && x 15 14)
    clear * - r6828 b6829 b6830 d6811
    omega
  have d6831 : (x 16 13).toNat = 1 := by
    have r6832 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6833 := hb (x 14 2)
    have b6834 := hb (x 16 13)
    have b6835 := hb (x 15 1 && x 15 14)
    clear * - r6832 b6833 b6834 b6835 d6827 d6481
    omega
  have d6836 : (x 17 12).toNat = 0 := by
    have r6837 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6838 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e6839 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b6840 := hb (x 14 3)
    have b6841 := hb (x 15 2)
    have b6842 := hb (x 16 13)
    have b6843 := hb (x 17 12)
    clear * - r6837 e6838 e6839 b6840 b6841 b6842 b6843 d6831
    omega
  have d6844 : (x 17 3 && x 17 12).toNat = 0 := by
    have r6845 := hand2 (x 17 3) (x 17 12)
    have b6846 := hb (x 17 12)
    have b6847 := hb (x 17 3 && x 17 12)
    clear * - r6845 b6846 b6847 d6836
    omega
  have d6848 : (x 17 4).toNat = 0 := by
    have r6849 : (x 17 4).toNat ≤ (x 17 12).toNat := himp _ _ (hp4 17)
    have b6850 := hb (x 17 4)
    have b6851 := hb (x 17 12)
    clear * - r6849 b6850 b6851 d6836
    omega
  have d6852 : (x 5 1 && x 5 10).toNat = 0 := by
    have r6853 := hand1 (x 5 1) (x 5 10)
    have b6854 := hb (x 5 1)
    have b6855 := hb (x 5 1 && x 5 10)
    clear * - r6853 b6854 b6855 d6747
    omega
  have d6856 : (x 5 13).toNat = 0 := by
    have r6857 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b6858 := hb (x 5 1)
    have b6859 := hb (x 5 13)
    clear * - r6857 b6858 b6859 d6747
    omega
  have d6860 : (x 5 5).toNat = 0 := by
    have r6861 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b6862 := hb (x 5 5)
    have b6863 := hb (x 5 13)
    clear * - r6861 b6862 b6863 d6856
    omega
  have d6864 : (x 8 12).toNat = 0 := by
    have r6865 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6866 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e6867 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b6868 := hb (x 5 3)
    have b6869 := hb (x 6 2)
    have b6870 := hb (x 7 13)
    have b6871 := hb (x 8 12)
    clear * - r6865 e6866 e6867 b6868 b6869 b6870 b6871 d6738
    omega
  have d6872 : (x 8 2 && x 8 12).toNat = 0 := by
    have r6873 := hand2 (x 8 2) (x 8 12)
    have b6874 := hb (x 8 12)
    have b6875 := hb (x 8 2 && x 8 12)
    clear * - r6873 b6874 b6875 d6864
    omega
  have d6876 : (x 8 4).toNat = 0 := by
    have r6877 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b6878 := hb (x 8 4)
    have b6879 := hb (x 8 12)
    clear * - r6877 b6878 b6879 d6864
    omega
  have d6880 : (x 7 13).toNat = 0 := by
    have r6881 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6882 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e6883 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b6884 := hb (x 5 3)
    have b6885 := hb (x 6 2)
    have b6886 := hb (x 7 13)
    have b6887 := hb (x 8 12)
    clear * - r6881 e6882 e6883 b6884 b6885 b6886 b6887 d6864 d6738
    omega
  have d6888 : (x 7 3 && x 7 13).toNat = 0 := by
    have r6889 := hand2 (x 7 3) (x 7 13)
    have b6890 := hb (x 7 13)
    have b6891 := hb (x 7 3 && x 7 13)
    clear * - r6889 b6890 b6891 d6880
    omega
  have d6892 : (x 7 5).toNat = 0 := by
    have r6893 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
    have b6894 := hb (x 7 5)
    have b6895 := hb (x 7 13)
    clear * - r6893 b6894 b6895 d6880
    omega
  have d6896 : (x 7 5 && x 7 14).toNat = 0 := by
    have r6897 := hand1 (x 7 5) (x 7 14)
    have b6898 := hb (x 7 5)
    have b6899 := hb (x 7 5 && x 7 14)
    clear * - r6897 b6898 b6899 d6892
    omega
  have d6900 : (x 6 6).toNat = 1 := by
    have r6901 : 1 ≤ (x 12 9).toNat + (x 11 1 && x 11 10).toNat + (x 10 2 && x 10 11).toNat + (x 9 3 && x 9 12).toNat + (x 8 4 && x 8 13).toNat + (x 7 5 && x 7 14).toNat + (x 6 6).toNat := by have q := hcov9 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6902 := hb (x 6 6)
    have b6903 := hb (x 12 9)
    have b6904 := hb (x 11 1 && x 11 10)
    have b6905 := hb (x 10 2 && x 10 11)
    have b6906 := hb (x 9 3 && x 9 12)
    have b6907 := hb (x 8 4 && x 8 13)
    have b6908 := hb (x 7 5 && x 7 14)
    clear * - r6901 b6902 b6903 b6904 b6905 b6906 b6907 b6908 d6344 d6380 d6404 d6196 d6216 d6896
    omega
  have d6909 : (x 12 8).toNat = 0 := by
    have r6910 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6911 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e6912 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e6913 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e6914 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e6915 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e6916 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b6917 := hb (x 5 7)
    have b6918 := hb (x 6 6)
    have b6919 := hb (x 7 5)
    have b6920 := hb (x 8 4)
    have b6921 := hb (x 9 11)
    have b6922 := hb (x 10 10)
    have b6923 := hb (x 11 9)
    have b6924 := hb (x 12 8)
    clear * - r6910 e6911 e6912 e6913 e6914 e6915 e6916 b6917 b6918 b6919 b6920 b6921 b6922 b6923 b6924 d6876 d6892 d6900
    omega
  have d6925 : (x 11 9).toNat = 0 := by
    have r6926 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6927 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e6928 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e6929 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e6930 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e6931 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e6932 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b6933 := hb (x 5 7)
    have b6934 := hb (x 6 6)
    have b6935 := hb (x 7 5)
    have b6936 := hb (x 8 4)
    have b6937 := hb (x 9 11)
    have b6938 := hb (x 10 10)
    have b6939 := hb (x 11 9)
    have b6940 := hb (x 12 8)
    clear * - r6926 e6927 e6928 e6929 e6930 e6931 e6932 b6933 b6934 b6935 b6936 b6937 b6938 b6939 b6940 d6909 d6876 d6892 d6900
    omega
  have d6941 : (x 10 10).toNat = 0 := by
    have r6942 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6943 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e6944 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e6945 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e6946 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e6947 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e6948 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b6949 := hb (x 5 7)
    have b6950 := hb (x 6 6)
    have b6951 := hb (x 7 5)
    have b6952 := hb (x 8 4)
    have b6953 := hb (x 9 11)
    have b6954 := hb (x 10 10)
    have b6955 := hb (x 11 9)
    have b6956 := hb (x 12 8)
    clear * - r6942 e6943 e6944 e6945 e6946 e6947 e6948 b6949 b6950 b6951 b6952 b6953 b6954 b6955 b6956 d6909 d6925 d6876 d6892 d6900
    omega
  have d6957 : (x 9 11).toNat = 0 := by
    have r6958 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6959 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e6960 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e6961 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e6962 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e6963 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e6964 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b6965 := hb (x 5 7)
    have b6966 := hb (x 6 6)
    have b6967 := hb (x 7 5)
    have b6968 := hb (x 8 4)
    have b6969 := hb (x 9 11)
    have b6970 := hb (x 10 10)
    have b6971 := hb (x 11 9)
    have b6972 := hb (x 12 8)
    clear * - r6958 e6959 e6960 e6961 e6962 e6963 e6964 b6965 b6966 b6967 b6968 b6969 b6970 b6971 b6972 d6909 d6925 d6941 d6876 d6892 d6900
    omega
  have d6973 : (x 9 1 && x 9 11).toNat = 0 := by
    have r6974 := hand2 (x 9 1) (x 9 11)
    have b6975 := hb (x 9 11)
    have b6976 := hb (x 9 1 && x 9 11)
    clear * - r6974 b6975 b6976 d6957
    omega
  have d6977 : (x 6 4 && x 6 14).toNat = 1 := by
    have r6978 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b6979 := hb (x 5 5)
    have b6980 := hb (x 10 10)
    have b6981 := hb (x 9 1 && x 9 11)
    have b6982 := hb (x 8 2 && x 8 12)
    have b6983 := hb (x 7 3 && x 7 13)
    have b6984 := hb (x 6 4 && x 6 14)
    clear * - r6978 b6979 b6980 b6981 b6982 b6983 b6984 d6941 d6973 d6872 d6888 d6860
    omega
  have d6985 : (x 6 4).toNat = 1 := by
    have r6986 := hand1 (x 6 4) (x 6 14)
    have b6987 := hb (x 6 4)
    have b6988 := hb (x 6 4 && x 6 14)
    clear * - r6986 b6987 b6988 d6977
    omega
  have d6989 : (x 6 12).toNat = 1 := by
    have r6990 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b6991 := hb (x 6 4)
    have b6992 := hb (x 6 12)
    clear * - r6990 b6991 b6992 d6985
    omega
  have d6993 : (x 4 2).toNat = 0 := by
    have r6994 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6995 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e6996 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b6997 := hb (x 3 3)
    have b6998 := hb (x 4 2)
    have b6999 := hb (x 5 13)
    have b7000 := hb (x 6 12)
    clear * - r6994 e6995 e6996 b6997 b6998 b6999 b7000 d6989 d6856
    omega
  have d7001 : (x 4 2 && x 4 11).toNat = 0 := by
    have r7002 := hand1 (x 4 2) (x 4 11)
    have b7003 := hb (x 4 2)
    have b7004 := hb (x 4 2 && x 4 11)
    clear * - r7002 b7003 b7004 d6993
    omega
  have d7005 : (x 6 9).toNat = 1 := by
    have r7006 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7007 := hb (x 0 6)
    have b7008 := hb (x 6 9)
    have b7009 := hb (x 5 1 && x 5 10)
    have b7010 := hb (x 4 2 && x 4 11)
    have b7011 := hb (x 3 3 && x 3 12)
    have b7012 := hb (x 2 4 && x 2 13)
    have b7013 := hb (x 1 5 && x 1 14)
    clear * - r7006 b7007 b7008 b7009 b7010 b7011 b7012 b7013 d6852 d7001 g32 d6173 g33 g3
    omega
  have d7014 : (x 6 1).toNat = 1 := by
    have r7015 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
    have b7016 := hb (x 6 1)
    have b7017 := hb (x 6 9)
    clear * - r7015 b7016 b7017 d7005
    omega
  have d7018 : (x 7 14).toNat = 0 := by
    have r7019 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7020 := hb (x 6 1)
    have b7021 := hb (x 7 14)
    clear * - r7019 b7020 b7021 d7014
    omega
  have d7022 : (x 7 7 && x 7 14).toNat = 0 := by
    have r7023 := hand2 (x 7 7) (x 7 14)
    have b7024 := hb (x 7 14)
    have b7025 := hb (x 7 7 && x 7 14)
    clear * - r7023 b7024 b7025 d7018
    omega
  have d7026 : (x 14 7).toNat = 1 := by
    have r7027 : 1 ≤ (x 14 7).toNat + (x 13 1 && x 13 8).toNat + (x 12 2 && x 12 9).toNat + (x 11 3 && x 11 10).toNat + (x 10 4 && x 10 11).toNat + (x 9 5 && x 9 12).toNat + (x 8 6 && x 8 13).toNat + (x 7 7 && x 7 14).toNat + (x 6 8).toNat := by have q := hcov7 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7028 := hb (x 6 8)
    have b7029 := hb (x 14 7)
    have b7030 := hb (x 13 1 && x 13 8)
    have b7031 := hb (x 12 2 && x 12 9)
    have b7032 := hb (x 11 3 && x 11 10)
    have b7033 := hb (x 10 4 && x 10 11)
    have b7034 := hb (x 9 5 && x 9 12)
    have b7035 := hb (x 8 6 && x 8 13)
    have b7036 := hb (x 7 7 && x 7 14)
    clear * - r7027 b7028 b7029 b7030 b7031 b7032 b7033 b7034 b7035 b7036 d6340 d6360 d6384 d6408 d6200 d6220 d7022 d6085
    omega
  have d7037 : (x 21 8).toNat = 0 := by
    have r7038 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7039 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
    have e7040 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
    have e7041 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
    have e7042 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
    have e7043 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
    have e7044 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
    have b7045 := hb (x 14 7)
    have b7046 := hb (x 15 6)
    have b7047 := hb (x 16 5)
    have b7048 := hb (x 17 4)
    have b7049 := hb (x 18 11)
    have b7050 := hb (x 19 10)
    have b7051 := hb (x 20 9)
    have b7052 := hb (x 21 8)
    clear * - r7038 e7039 e7040 e7041 e7042 e7043 e7044 b7045 b7046 b7047 b7048 b7049 b7050 b7051 b7052 d6848 d7026
    omega
  have d7053 : (x 20 9).toNat = 0 := by
    have r7054 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7055 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
    have e7056 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
    have e7057 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
    have e7058 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
    have e7059 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
    have e7060 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
    have b7061 := hb (x 14 7)
    have b7062 := hb (x 15 6)
    have b7063 := hb (x 16 5)
    have b7064 := hb (x 17 4)
    have b7065 := hb (x 18 11)
    have b7066 := hb (x 19 10)
    have b7067 := hb (x 20 9)
    have b7068 := hb (x 21 8)
    clear * - r7054 e7055 e7056 e7057 e7058 e7059 e7060 b7061 b7062 b7063 b7064 b7065 b7066 b7067 b7068 d7037 d6848 d7026
    omega
  have d7069 : (x 19 10).toNat = 0 := by
    have r7070 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7071 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
    have e7072 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
    have e7073 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
    have e7074 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
    have e7075 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
    have e7076 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
    have b7077 := hb (x 14 7)
    have b7078 := hb (x 15 6)
    have b7079 := hb (x 16 5)
    have b7080 := hb (x 17 4)
    have b7081 := hb (x 18 11)
    have b7082 := hb (x 19 10)
    have b7083 := hb (x 20 9)
    have b7084 := hb (x 21 8)
    clear * - r7070 e7071 e7072 e7073 e7074 e7075 e7076 b7077 b7078 b7079 b7080 b7081 b7082 b7083 b7084 d7037 d7053 d6848 d7026
    omega
  have d7085 : (x 19 1 && x 19 10).toNat = 0 := by
    have r7086 := hand2 (x 19 1) (x 19 10)
    have b7087 := hb (x 19 10)
    have b7088 := hb (x 19 1 && x 19 10)
    clear * - r7086 b7087 b7088 d7069
    omega
  have d7089 : (x 18 2 && x 18 11).toNat = 1 := by
    have r7090 : 1 ≤ (x 20 9).toNat + (x 19 1 && x 19 10).toNat + (x 18 2 && x 18 11).toNat + (x 17 3 && x 17 12).toNat + (x 16 4 && x 16 13).toNat + (x 15 5 && x 15 14).toNat + (x 14 6).toNat := by have q := hcov9 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7091 := hb (x 14 6)
    have b7092 := hb (x 20 9)
    have b7093 := hb (x 19 1 && x 19 10)
    have b7094 := hb (x 18 2 && x 18 11)
    have b7095 := hb (x 17 3 && x 17 12)
    have b7096 := hb (x 16 4 && x 16 13)
    have b7097 := hb (x 15 5 && x 15 14)
    clear * - r7090 b7091 b7092 b7093 b7094 b7095 b7096 b7097 d7053 d7085 d6844 d6593 d6609 d6477
    omega
  have d7098 : (x 18 11).toNat = 1 := by
    have r7099 := hand2 (x 18 2) (x 18 11)
    have b7100 := hb (x 18 11)
    have b7101 := hb (x 18 2 && x 18 11)
    clear * - r7099 b7100 b7101 d7089
    omega
  have r7102 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7103 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
  have e7104 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
  have e7105 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
  have e7106 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
  have e7107 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
  have e7108 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
  have b7109 := hb (x 14 7)
  have b7110 := hb (x 15 6)
  have b7111 := hb (x 16 5)
  have b7112 := hb (x 17 4)
  have b7113 := hb (x 18 11)
  have b7114 := hb (x 19 10)
  have b7115 := hb (x 20 9)
  have b7116 := hb (x 21 8)
  linarith only [r7102, e7103, e7104, e7105, e7106, e7107, e7108, b7109, b7110, b7111, b7112, b7113, b7114, b7115, b7116, d7037, d7053, d7069, d7098, d6848, d7026]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b0000100001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 1 3).toNat = 1)
    (g1 : (x 1 4).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 2 && x 3 13).toNat = 0)
    (g4 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d7118 : (x 4 12).toNat = 0 := by
    have r7119 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7120 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e7121 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b7122 := hb (x 1 3)
    have b7123 := hb (x 2 2)
    have b7124 := hb (x 3 13)
    have b7125 := hb (x 4 12)
    clear * - r7119 e7120 e7121 b7122 b7123 b7124 b7125 g0
    omega
  have d7126 : (x 4 1 && x 4 12).toNat = 0 := by
    have r7127 := hand2 (x 4 1) (x 4 12)
    have b7128 := hb (x 4 12)
    have b7129 := hb (x 4 1 && x 4 12)
    clear * - r7127 b7128 b7129 d7118
    omega
  have d7130 : (x 4 4).toNat = 0 := by
    have r7131 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b7132 := hb (x 4 4)
    have b7133 := hb (x 4 12)
    clear * - r7131 b7132 b7133 d7118
    omega
  have d7134 : (x 3 13).toNat = 0 := by
    have r7135 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7136 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e7137 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b7138 := hb (x 1 3)
    have b7139 := hb (x 2 2)
    have b7140 := hb (x 3 13)
    have b7141 := hb (x 4 12)
    clear * - r7135 e7136 e7137 b7138 b7139 b7140 b7141 d7118 g0
    omega
  have d7142 : (x 2 2).toNat = 0 := by
    have r7143 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7144 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e7145 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b7146 := hb (x 1 3)
    have b7147 := hb (x 2 2)
    have b7148 := hb (x 3 13)
    have b7149 := hb (x 4 12)
    clear * - r7143 e7144 e7145 b7146 b7147 b7148 b7149 d7118 d7134 g0
    omega
  have d7150 : (x 4 13).toNat = 1 := by
    have r7151 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7152 := hb (x 2 2)
    have b7153 := hb (x 4 13)
    have b7154 := hb (x 3 1 && x 3 14)
    clear * - r7151 b7152 b7153 b7154 g4 d7142
    omega
  have d7155 : (x 4 1).toNat = 1 := by
    have r7156 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b7157 := hb (x 4 1)
    have b7158 := hb (x 4 13)
    clear * - r7156 b7157 b7158 d7150
    omega
  have d7159 : (x 5 14).toNat = 0 := by
    have r7160 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7161 := hb (x 4 1)
    have b7162 := hb (x 5 14)
    clear * - r7160 b7161 b7162 d7155
    omega
  have d7163 : (x 5 3 && x 5 14).toNat = 0 := by
    have r7164 := hand2 (x 5 3) (x 5 14)
    have b7165 := hb (x 5 14)
    have b7166 := hb (x 5 3 && x 5 14)
    clear * - r7164 b7165 b7166 d7159
    omega
  have d7167 : (x 5 2).toNat = 0 := by
    have r7168 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b7169 := hb (x 5 2)
    have b7170 := hb (x 5 14)
    clear * - r7168 b7169 b7170 d7159
    omega
  have d7171 : (x 5 12).toNat = 0 := by
    have r7172 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7173 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e7174 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b7175 := hb (x 2 3)
    have b7176 := hb (x 3 2)
    have b7177 := hb (x 4 13)
    have b7178 := hb (x 5 12)
    clear * - r7172 e7173 e7174 b7175 b7176 b7177 b7178 d7150 g2
    omega
  have d7179 : (x 5 4).toNat = 0 := by
    have r7180 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b7181 := hb (x 5 4)
    have b7182 := hb (x 5 12)
    clear * - r7180 b7181 b7182 d7171
    omega
  have d7183 : (x 2 3).toNat = 0 := by
    have r7184 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7185 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e7186 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b7187 := hb (x 2 3)
    have b7188 := hb (x 3 2)
    have b7189 := hb (x 4 13)
    have b7190 := hb (x 5 12)
    clear * - r7184 e7185 e7186 b7187 b7188 b7189 b7190 d7171 d7150 g2
    omega
  have d7191 : (x 2 3 && x 2 14).toNat = 0 := by
    have r7192 := hand1 (x 2 3) (x 2 14)
    have b7193 := hb (x 2 3)
    have b7194 := hb (x 2 3 && x 2 14)
    clear * - r7192 b7193 b7194 d7183
    omega
  have d7195 : (x 5 11).toNat = 1 := by
    have r7196 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7197 := hb (x 1 4)
    have b7198 := hb (x 5 11)
    have b7199 := hb (x 4 1 && x 4 12)
    have b7200 := hb (x 3 2 && x 3 13)
    have b7201 := hb (x 2 3 && x 2 14)
    clear * - r7196 b7197 b7198 b7199 b7200 b7201 d7126 g3 d7191 g1
    omega
  have d7202 : (x 5 3).toNat = 1 := by
    have r7203 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b7204 := hb (x 5 3)
    have b7205 := hb (x 5 11)
    clear * - r7203 b7204 b7205 d7195
    omega
  have d7206 : (x 8 12).toNat = 0 := by
    have r7207 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7208 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e7209 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b7210 := hb (x 5 3)
    have b7211 := hb (x 6 2)
    have b7212 := hb (x 7 13)
    have b7213 := hb (x 8 12)
    clear * - r7207 e7208 e7209 b7210 b7211 b7212 b7213 d7202
    omega
  have d7214 : (x 8 1 && x 8 12).toNat = 0 := by
    have r7215 := hand2 (x 8 1) (x 8 12)
    have b7216 := hb (x 8 12)
    have b7217 := hb (x 8 1 && x 8 12)
    clear * - r7215 b7216 b7217 d7206
    omega
  have d7218 : (x 8 4).toNat = 0 := by
    have r7219 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b7220 := hb (x 8 4)
    have b7221 := hb (x 8 12)
    clear * - r7219 b7220 b7221 d7206
    omega
  have d7222 : (x 7 13).toNat = 0 := by
    have r7223 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7224 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e7225 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b7226 := hb (x 5 3)
    have b7227 := hb (x 6 2)
    have b7228 := hb (x 7 13)
    have b7229 := hb (x 8 12)
    clear * - r7223 e7224 e7225 b7226 b7227 b7228 b7229 d7206 d7202
    omega
  have d7230 : (x 7 2 && x 7 13).toNat = 0 := by
    have r7231 := hand2 (x 7 2) (x 7 13)
    have b7232 := hb (x 7 13)
    have b7233 := hb (x 7 2 && x 7 13)
    clear * - r7231 b7232 b7233 d7222
    omega
  have d7234 : (x 6 1 && x 6 14).toNat = 1 := by
    have r7235 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7236 := hb (x 5 2)
    have b7237 := hb (x 7 13)
    have b7238 := hb (x 6 1 && x 6 14)
    clear * - r7235 b7236 b7237 b7238 d7222 d7167
    omega
  have d7239 : (x 6 1).toNat = 1 := by
    have r7240 := hand1 (x 6 1) (x 6 14)
    have b7241 := hb (x 6 1)
    have b7242 := hb (x 6 1 && x 6 14)
    clear * - r7240 b7241 b7242 d7234
    omega
  have d7243 : (x 7 14).toNat = 0 := by
    have r7244 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7245 := hb (x 6 1)
    have b7246 := hb (x 7 14)
    clear * - r7244 b7245 b7246 d7239
    omega
  have d7247 : (x 7 1 && x 7 14).toNat = 0 := by
    have r7248 := hand2 (x 7 1) (x 7 14)
    have b7249 := hb (x 7 14)
    have b7250 := hb (x 7 1 && x 7 14)
    clear * - r7248 b7249 b7250 d7243
    omega
  have d7251 : (x 7 2).toNat = 0 := by
    have r7252 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b7253 := hb (x 7 2)
    have b7254 := hb (x 7 14)
    clear * - r7252 b7253 b7254 d7243
    omega
  have d7255 : (x 6 2).toNat = 0 := by
    have r7256 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7257 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e7258 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b7259 := hb (x 5 3)
    have b7260 := hb (x 6 2)
    have b7261 := hb (x 7 13)
    have b7262 := hb (x 8 12)
    clear * - r7256 e7257 e7258 b7259 b7260 b7261 b7262 d7206 d7222 d7202
    omega
  have d7263 : (x 6 2 && x 6 13).toNat = 0 := by
    have r7264 := hand1 (x 6 2) (x 6 13)
    have b7265 := hb (x 6 2)
    have b7266 := hb (x 6 2 && x 6 13)
    clear * - r7264 b7265 b7266 d7255
    omega
  have d7267 : (x 8 13).toNat = 1 := by
    have r7268 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7269 := hb (x 6 2)
    have b7270 := hb (x 8 13)
    have b7271 := hb (x 7 1 && x 7 14)
    clear * - r7268 b7269 b7270 b7271 d7247 d7255
    omega
  have d7272 : (x 8 1).toNat = 1 := by
    have r7273 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b7274 := hb (x 8 1)
    have b7275 := hb (x 8 13)
    clear * - r7273 b7274 b7275 d7267
    omega
  have d7276 : (x 9 14).toNat = 0 := by
    have r7277 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7278 := hb (x 8 1)
    have b7279 := hb (x 9 14)
    clear * - r7277 b7278 b7279 d7272
    omega
  have d7280 : (x 9 3 && x 9 14).toNat = 0 := by
    have r7281 := hand2 (x 9 3) (x 9 14)
    have b7282 := hb (x 9 14)
    have b7283 := hb (x 9 3 && x 9 14)
    clear * - r7281 b7282 b7283 d7276
    omega
  have d7284 : (x 9 2).toNat = 0 := by
    have r7285 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b7286 := hb (x 9 2)
    have b7287 := hb (x 9 14)
    clear * - r7285 b7286 b7287 d7276
    omega
  have d7288 : (x 9 12).toNat = 0 := by
    have r7289 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7290 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e7291 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b7292 := hb (x 6 3)
    have b7293 := hb (x 7 2)
    have b7294 := hb (x 8 13)
    have b7295 := hb (x 9 12)
    clear * - r7289 e7290 e7291 b7292 b7293 b7294 b7295 d7267 d7251
    omega
  have d7296 : (x 9 4).toNat = 0 := by
    have r7297 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b7298 := hb (x 9 4)
    have b7299 := hb (x 9 12)
    clear * - r7297 b7298 b7299 d7288
    omega
  have d7300 : (x 6 3).toNat = 0 := by
    have r7301 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7302 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e7303 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b7304 := hb (x 6 3)
    have b7305 := hb (x 7 2)
    have b7306 := hb (x 8 13)
    have b7307 := hb (x 9 12)
    clear * - r7301 e7302 e7303 b7304 b7305 b7306 b7307 d7288 d7267 d7251
    omega
  have d7308 : (x 6 3 && x 6 14).toNat = 0 := by
    have r7309 := hand1 (x 6 3) (x 6 14)
    have b7310 := hb (x 6 3)
    have b7311 := hb (x 6 3 && x 6 14)
    clear * - r7309 b7310 b7311 d7300
    omega
  have d7312 : (x 9 11).toNat = 1 := by
    have r7313 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7314 := hb (x 5 4)
    have b7315 := hb (x 9 11)
    have b7316 := hb (x 8 1 && x 8 12)
    have b7317 := hb (x 7 2 && x 7 13)
    have b7318 := hb (x 6 3 && x 6 14)
    clear * - r7313 b7314 b7315 b7316 b7317 b7318 d7214 d7230 d7308 d7179
    omega
  have d7319 : (x 9 3).toNat = 1 := by
    have r7320 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
    have b7321 := hb (x 9 3)
    have b7322 := hb (x 9 11)
    clear * - r7320 b7321 b7322 d7312
    omega
  have d7323 : (x 12 12).toNat = 0 := by
    have r7324 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7325 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e7326 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b7327 := hb (x 9 3)
    have b7328 := hb (x 10 2)
    have b7329 := hb (x 11 13)
    have b7330 := hb (x 12 12)
    clear * - r7324 e7325 e7326 b7327 b7328 b7329 b7330 d7319
    omega
  have d7331 : (x 12 1 && x 12 12).toNat = 0 := by
    have r7332 := hand2 (x 12 1) (x 12 12)
    have b7333 := hb (x 12 12)
    have b7334 := hb (x 12 1 && x 12 12)
    clear * - r7332 b7333 b7334 d7323
    omega
  have d7335 : (x 12 4).toNat = 0 := by
    have r7336 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b7337 := hb (x 12 4)
    have b7338 := hb (x 12 12)
    clear * - r7336 b7337 b7338 d7323
    omega
  have d7339 : (x 11 13).toNat = 0 := by
    have r7340 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7341 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e7342 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b7343 := hb (x 9 3)
    have b7344 := hb (x 10 2)
    have b7345 := hb (x 11 13)
    have b7346 := hb (x 12 12)
    clear * - r7340 e7341 e7342 b7343 b7344 b7345 b7346 d7323 d7319
    omega
  have d7347 : (x 11 2 && x 11 13).toNat = 0 := by
    have r7348 := hand2 (x 11 2) (x 11 13)
    have b7349 := hb (x 11 13)
    have b7350 := hb (x 11 2 && x 11 13)
    clear * - r7348 b7349 b7350 d7339
    omega
  have d7351 : (x 10 1 && x 10 14).toNat = 1 := by
    have r7352 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7353 := hb (x 9 2)
    have b7354 := hb (x 11 13)
    have b7355 := hb (x 10 1 && x 10 14)
    clear * - r7352 b7353 b7354 b7355 d7339 d7284
    omega
  have d7356 : (x 10 14).toNat = 1 := by
    have r7357 := hand2 (x 10 1) (x 10 14)
    have b7358 := hb (x 10 14)
    have b7359 := hb (x 10 1 && x 10 14)
    clear * - r7357 b7358 b7359 d7351
    omega
  have d7360 : (x 9 1).toNat = 0 := by
    have r7361 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7362 := hb (x 9 1)
    have b7363 := hb (x 10 14)
    clear * - r7361 b7362 b7363 d7356
    omega
  have d7364 : (x 9 13).toNat = 0 := by
    have r7365 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b7366 := hb (x 9 1)
    have b7367 := hb (x 9 13)
    clear * - r7365 b7366 b7367 d7360
    omega
  have d7368 : (x 8 1 && x 8 14).toNat = 1 := by
    have r7369 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7370 := hb (x 7 2)
    have b7371 := hb (x 9 13)
    have b7372 := hb (x 8 1 && x 8 14)
    clear * - r7369 b7370 b7371 b7372 d7364 d7251
    omega
  have d7373 : (x 8 14).toNat = 1 := by
    have r7374 := hand2 (x 8 1) (x 8 14)
    have b7375 := hb (x 8 14)
    have b7376 := hb (x 8 1 && x 8 14)
    clear * - r7374 b7375 b7376 d7368
    omega
  have d7377 : (x 7 1).toNat = 0 := by
    have r7378 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7379 := hb (x 7 1)
    have b7380 := hb (x 8 14)
    clear * - r7378 b7379 b7380 d7373
    omega
  have d7381 : (x 7 1 && x 7 12).toNat = 0 := by
    have r7382 := hand1 (x 7 1) (x 7 12)
    have b7383 := hb (x 7 1)
    have b7384 := hb (x 7 1 && x 7 12)
    clear * - r7382 b7383 b7384 d7377
    omega
  have d7385 : (x 8 11).toNat = 1 := by
    have r7386 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7387 := hb (x 4 4)
    have b7388 := hb (x 8 11)
    have b7389 := hb (x 7 1 && x 7 12)
    have b7390 := hb (x 6 2 && x 6 13)
    have b7391 := hb (x 5 3 && x 5 14)
    clear * - r7386 b7387 b7388 b7389 b7390 b7391 d7381 d7263 d7163 d7130
    omega
  have d7392 : (x 8 3).toNat = 1 := by
    have r7393 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b7394 := hb (x 8 3)
    have b7395 := hb (x 8 11)
    clear * - r7393 b7394 b7395 d7385
    omega
  have d7396 : (x 11 12).toNat = 0 := by
    have r7397 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7398 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e7399 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b7400 := hb (x 8 3)
    have b7401 := hb (x 9 2)
    have b7402 := hb (x 10 13)
    have b7403 := hb (x 11 12)
    clear * - r7397 e7398 e7399 b7400 b7401 b7402 b7403 d7284 d7392
    omega
  have d7404 : (x 11 1 && x 11 12).toNat = 0 := by
    have r7405 := hand2 (x 11 1) (x 11 12)
    have b7406 := hb (x 11 12)
    have b7407 := hb (x 11 1 && x 11 12)
    clear * - r7405 b7406 b7407 d7396
    omega
  have d7408 : (x 10 13).toNat = 0 := by
    have r7409 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7410 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e7411 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b7412 := hb (x 8 3)
    have b7413 := hb (x 9 2)
    have b7414 := hb (x 10 13)
    have b7415 := hb (x 11 12)
    clear * - r7409 e7410 e7411 b7412 b7413 b7414 b7415 d7396 d7284 d7392
    omega
  have d7416 : (x 10 2 && x 10 13).toNat = 0 := by
    have r7417 := hand2 (x 10 2) (x 10 13)
    have b7418 := hb (x 10 13)
    have b7419 := hb (x 10 2 && x 10 13)
    clear * - r7417 b7418 b7419 d7408
    omega
  have d7420 : (x 12 11).toNat = 1 := by
    have r7421 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7422 := hb (x 8 4)
    have b7423 := hb (x 12 11)
    have b7424 := hb (x 11 1 && x 11 12)
    have b7425 := hb (x 10 2 && x 10 13)
    have b7426 := hb (x 9 3 && x 9 14)
    clear * - r7421 b7422 b7423 b7424 b7425 b7426 d7404 d7416 d7280 d7218
    omega
  have d7427 : (x 12 3).toNat = 1 := by
    have r7428 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b7429 := hb (x 12 3)
    have b7430 := hb (x 12 11)
    clear * - r7428 b7429 b7430 d7420
    omega
  have d7431 : (x 15 12).toNat = 0 := by
    have r7432 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7433 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e7434 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b7435 := hb (x 12 3)
    have b7436 := hb (x 13 2)
    have b7437 := hb (x 14 13)
    have b7438 := hb (x 15 12)
    clear * - r7432 e7433 e7434 b7435 b7436 b7437 b7438 d7427
    omega
  have d7439 : (x 15 1 && x 15 12).toNat = 0 := by
    have r7440 := hand2 (x 15 1) (x 15 12)
    have b7441 := hb (x 15 12)
    have b7442 := hb (x 15 1 && x 15 12)
    clear * - r7440 b7441 b7442 d7431
    omega
  have d7443 : (x 14 13).toNat = 0 := by
    have r7444 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7445 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e7446 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b7447 := hb (x 12 3)
    have b7448 := hb (x 13 2)
    have b7449 := hb (x 14 13)
    have b7450 := hb (x 15 12)
    clear * - r7444 e7445 e7446 b7447 b7448 b7449 b7450 d7431 d7427
    omega
  have d7451 : (x 14 2 && x 14 13).toNat = 0 := by
    have r7452 := hand2 (x 14 2) (x 14 13)
    have b7453 := hb (x 14 13)
    have b7454 := hb (x 14 2 && x 14 13)
    clear * - r7452 b7453 b7454 d7443
    omega
  have d7455 : (x 13 2).toNat = 0 := by
    have r7456 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7457 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e7458 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b7459 := hb (x 12 3)
    have b7460 := hb (x 13 2)
    have b7461 := hb (x 14 13)
    have b7462 := hb (x 15 12)
    clear * - r7456 e7457 e7458 b7459 b7460 b7461 b7462 d7431 d7443 d7427
    omega
  have d7463 : (x 10 1).toNat = 1 := by
    have r7464 := hand1 (x 10 1) (x 10 14)
    have b7465 := hb (x 10 1)
    have b7466 := hb (x 10 1 && x 10 14)
    clear * - r7464 b7465 b7466 d7351
    omega
  have d7467 : (x 11 14).toNat = 0 := by
    have r7468 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7469 := hb (x 10 1)
    have b7470 := hb (x 11 14)
    clear * - r7468 b7469 b7470 d7463
    omega
  have d7471 : (x 11 1 && x 11 14).toNat = 0 := by
    have r7472 := hand2 (x 11 1) (x 11 14)
    have b7473 := hb (x 11 14)
    have b7474 := hb (x 11 1 && x 11 14)
    clear * - r7472 b7473 b7474 d7467
    omega
  have d7475 : (x 11 2).toNat = 0 := by
    have r7476 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b7477 := hb (x 11 2)
    have b7478 := hb (x 11 14)
    clear * - r7476 b7477 b7478 d7467
    omega
  have d7479 : (x 10 2).toNat = 0 := by
    have r7480 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7481 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e7482 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b7483 := hb (x 9 3)
    have b7484 := hb (x 10 2)
    have b7485 := hb (x 11 13)
    have b7486 := hb (x 12 12)
    clear * - r7480 e7481 e7482 b7483 b7484 b7485 b7486 d7323 d7339 d7319
    omega
  have d7487 : (x 12 13).toNat = 1 := by
    have r7488 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7489 := hb (x 10 2)
    have b7490 := hb (x 12 13)
    have b7491 := hb (x 11 1 && x 11 14)
    clear * - r7488 b7489 b7490 b7491 d7471 d7479
    omega
  have d7492 : (x 12 1).toNat = 1 := by
    have r7493 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b7494 := hb (x 12 1)
    have b7495 := hb (x 12 13)
    clear * - r7493 b7494 b7495 d7487
    omega
  have d7496 : (x 13 14).toNat = 0 := by
    have r7497 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7498 := hb (x 12 1)
    have b7499 := hb (x 13 14)
    clear * - r7497 b7498 b7499 d7492
    omega
  have d7500 : (x 13 1 && x 13 14).toNat = 0 := by
    have r7501 := hand2 (x 13 1) (x 13 14)
    have b7502 := hb (x 13 14)
    have b7503 := hb (x 13 1 && x 13 14)
    clear * - r7501 b7502 b7503 d7496
    omega
  have d7504 : (x 12 2).toNat = 1 := by
    have r7505 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7506 := hb (x 12 2)
    have b7507 := hb (x 14 13)
    have b7508 := hb (x 13 1 && x 13 14)
    clear * - r7505 b7506 b7507 b7508 d7443 d7500
    omega
  have d7509 : (x 14 12).toNat = 0 := by
    have r7510 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7511 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e7512 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b7513 := hb (x 11 3)
    have b7514 := hb (x 12 2)
    have b7515 := hb (x 13 13)
    have b7516 := hb (x 14 12)
    clear * - r7510 e7511 e7512 b7513 b7514 b7515 b7516 d7504
    omega
  have d7517 : (x 14 4).toNat = 0 := by
    have r7518 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
    have b7519 := hb (x 14 4)
    have b7520 := hb (x 14 12)
    clear * - r7518 b7519 b7520 d7509
    omega
  have d7521 : (x 14 4 && x 14 14).toNat = 0 := by
    have r7522 := hand1 (x 14 4) (x 14 14)
    have b7523 := hb (x 14 4)
    have b7524 := hb (x 14 4 && x 14 14)
    clear * - r7522 b7523 b7524 d7517
    omega
  have d7525 : (x 13 13).toNat = 0 := by
    have r7526 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7527 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e7528 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b7529 := hb (x 11 3)
    have b7530 := hb (x 12 2)
    have b7531 := hb (x 13 13)
    have b7532 := hb (x 14 12)
    clear * - r7526 e7527 e7528 b7529 b7530 b7531 b7532 d7509 d7504
    omega
  have d7533 : (x 13 5).toNat = 0 := by
    have r7534 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
    have b7535 := hb (x 13 5)
    have b7536 := hb (x 13 13)
    clear * - r7534 b7535 b7536 d7525
    omega
  have d7537 : (x 13 3 && x 13 14).toNat = 0 := by
    have r7538 := hand2 (x 13 3) (x 13 14)
    have b7539 := hb (x 13 14)
    have b7540 := hb (x 13 3 && x 13 14)
    clear * - r7538 b7539 b7540 d7496
    omega
  have d7541 : (x 16 11).toNat = 1 := by
    have r7542 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7543 := hb (x 12 4)
    have b7544 := hb (x 16 11)
    have b7545 := hb (x 15 1 && x 15 12)
    have b7546 := hb (x 14 2 && x 14 13)
    have b7547 := hb (x 13 3 && x 13 14)
    clear * - r7542 b7543 b7544 b7545 b7546 b7547 d7439 d7451 d7537 d7335
    omega
  have d7548 : (x 16 3).toNat = 1 := by
    have r7549 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
    have b7550 := hb (x 16 3)
    have b7551 := hb (x 16 11)
    clear * - r7549 b7550 b7551 d7541
    omega
  have d7552 : (x 19 12).toNat = 0 := by
    have r7553 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7554 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e7555 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b7556 := hb (x 16 3)
    have b7557 := hb (x 17 2)
    have b7558 := hb (x 18 13)
    have b7559 := hb (x 19 12)
    clear * - r7553 e7554 e7555 b7556 b7557 b7558 b7559 d7548
    omega
  have d7560 : (x 18 13).toNat = 0 := by
    have r7561 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7562 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e7563 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b7564 := hb (x 16 3)
    have b7565 := hb (x 17 2)
    have b7566 := hb (x 18 13)
    have b7567 := hb (x 19 12)
    clear * - r7561 e7562 e7563 b7564 b7565 b7566 b7567 d7552 d7548
    omega
  have d7568 : (x 17 2).toNat = 0 := by
    have r7569 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7570 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e7571 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b7572 := hb (x 16 3)
    have b7573 := hb (x 17 2)
    have b7574 := hb (x 18 13)
    have b7575 := hb (x 19 12)
    clear * - r7569 e7570 e7571 b7572 b7573 b7574 b7575 d7552 d7560 d7548
    omega
  have d7576 : (x 13 12).toNat = 0 := by
    have r7577 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7578 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e7579 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b7580 := hb (x 10 3)
    have b7581 := hb (x 11 2)
    have b7582 := hb (x 12 13)
    have b7583 := hb (x 13 12)
    clear * - r7577 e7578 e7579 b7580 b7581 b7582 b7583 d7487 d7475
    omega
  have d7584 : (x 13 4).toNat = 0 := by
    have r7585 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b7586 := hb (x 13 4)
    have b7587 := hb (x 13 12)
    clear * - r7585 b7586 b7587 d7576
    omega
  have d7588 : (x 10 3).toNat = 0 := by
    have r7589 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7590 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e7591 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b7592 := hb (x 10 3)
    have b7593 := hb (x 11 2)
    have b7594 := hb (x 12 13)
    have b7595 := hb (x 13 12)
    clear * - r7589 e7590 e7591 b7592 b7593 b7594 b7595 d7576 d7487 d7475
    omega
  have d7596 : (x 10 3 && x 10 14).toNat = 0 := by
    have r7597 := hand1 (x 10 3) (x 10 14)
    have b7598 := hb (x 10 3)
    have b7599 := hb (x 10 3 && x 10 14)
    clear * - r7597 b7598 b7599 d7588
    omega
  have d7600 : (x 13 11).toNat = 1 := by
    have r7601 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7602 := hb (x 9 4)
    have b7603 := hb (x 13 11)
    have b7604 := hb (x 12 1 && x 12 12)
    have b7605 := hb (x 11 2 && x 11 13)
    have b7606 := hb (x 10 3 && x 10 14)
    clear * - r7601 b7602 b7603 b7604 b7605 b7606 d7331 d7347 d7596 d7296
    omega
  have d7607 : (x 13 3).toNat = 1 := by
    have r7608 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
    have b7609 := hb (x 13 3)
    have b7610 := hb (x 13 11)
    clear * - r7608 b7609 b7610 d7600
    omega
  have d7611 : (x 16 12).toNat = 0 := by
    have r7612 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7613 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e7614 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b7615 := hb (x 13 3)
    have b7616 := hb (x 14 2)
    have b7617 := hb (x 15 13)
    have b7618 := hb (x 16 12)
    clear * - r7612 e7613 e7614 b7615 b7616 b7617 b7618 d7607
    omega
  have d7619 : (x 16 1 && x 16 12).toNat = 0 := by
    have r7620 := hand2 (x 16 1) (x 16 12)
    have b7621 := hb (x 16 12)
    have b7622 := hb (x 16 1 && x 16 12)
    clear * - r7620 b7621 b7622 d7611
    omega
  have d7623 : (x 16 2 && x 16 12).toNat = 0 := by
    have r7624 := hand2 (x 16 2) (x 16 12)
    have b7625 := hb (x 16 12)
    have b7626 := hb (x 16 2 && x 16 12)
    clear * - r7624 b7625 b7626 d7611
    omega
  have d7627 : (x 15 13).toNat = 0 := by
    have r7628 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7629 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e7630 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b7631 := hb (x 13 3)
    have b7632 := hb (x 14 2)
    have b7633 := hb (x 15 13)
    have b7634 := hb (x 16 12)
    clear * - r7628 e7629 e7630 b7631 b7632 b7633 b7634 d7611 d7607
    omega
  have d7635 : (x 15 2 && x 15 13).toNat = 0 := by
    have r7636 := hand2 (x 15 2) (x 15 13)
    have b7637 := hb (x 15 13)
    have b7638 := hb (x 15 2 && x 15 13)
    clear * - r7636 b7637 b7638 d7627
    omega
  have d7639 : (x 15 3 && x 15 13).toNat = 0 := by
    have r7640 := hand2 (x 15 3) (x 15 13)
    have b7641 := hb (x 15 13)
    have b7642 := hb (x 15 3 && x 15 13)
    clear * - r7640 b7641 b7642 d7627
    omega
  have d7643 : (x 14 1 && x 14 14).toNat = 1 := by
    have r7644 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7645 := hb (x 13 2)
    have b7646 := hb (x 15 13)
    have b7647 := hb (x 14 1 && x 14 14)
    clear * - r7644 b7645 b7646 b7647 d7627 d7455
    omega
  have d7648 : (x 14 1).toNat = 1 := by
    have r7649 := hand1 (x 14 1) (x 14 14)
    have b7650 := hb (x 14 1)
    have b7651 := hb (x 14 1 && x 14 14)
    clear * - r7649 b7650 b7651 d7643
    omega
  have d7652 : (x 15 14).toNat = 0 := by
    have r7653 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7654 := hb (x 14 1)
    have b7655 := hb (x 15 14)
    clear * - r7653 b7654 b7655 d7648
    omega
  have d7656 : (x 15 1 && x 15 14).toNat = 0 := by
    have r7657 := hand2 (x 15 1) (x 15 14)
    have b7658 := hb (x 15 14)
    have b7659 := hb (x 15 1 && x 15 14)
    clear * - r7657 b7658 b7659 d7652
    omega
  have d7660 : (x 15 2).toNat = 0 := by
    have r7661 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b7662 := hb (x 15 2)
    have b7663 := hb (x 15 14)
    clear * - r7661 b7662 b7663 d7652
    omega
  have d7664 : (x 14 2).toNat = 0 := by
    have r7665 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7666 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e7667 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b7668 := hb (x 13 3)
    have b7669 := hb (x 14 2)
    have b7670 := hb (x 15 13)
    have b7671 := hb (x 16 12)
    clear * - r7665 e7666 e7667 b7668 b7669 b7670 b7671 d7611 d7627 d7607
    omega
  have d7672 : (x 16 13).toNat = 1 := by
    have r7673 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7674 := hb (x 14 2)
    have b7675 := hb (x 16 13)
    have b7676 := hb (x 15 1 && x 15 14)
    clear * - r7673 b7674 b7675 b7676 d7656 d7664
    omega
  have d7677 : (x 17 12).toNat = 0 := by
    have r7678 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7679 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e7680 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b7681 := hb (x 14 3)
    have b7682 := hb (x 15 2)
    have b7683 := hb (x 16 13)
    have b7684 := hb (x 17 12)
    clear * - r7678 e7679 e7680 b7681 b7682 b7683 b7684 d7672 d7660
    omega
  have d7685 : (x 14 3).toNat = 0 := by
    have r7686 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7687 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e7688 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b7689 := hb (x 14 3)
    have b7690 := hb (x 15 2)
    have b7691 := hb (x 16 13)
    have b7692 := hb (x 17 12)
    clear * - r7686 e7687 e7688 b7689 b7690 b7691 b7692 d7677 d7672 d7660
    omega
  have d7693 : (x 14 3 && x 14 14).toNat = 0 := by
    have r7694 := hand1 (x 14 3) (x 14 14)
    have b7695 := hb (x 14 3)
    have b7696 := hb (x 14 3 && x 14 14)
    clear * - r7694 b7695 b7696 d7685
    omega
  have d7697 : (x 17 11).toNat = 1 := by
    have r7698 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7699 := hb (x 13 4)
    have b7700 := hb (x 17 11)
    have b7701 := hb (x 16 1 && x 16 12)
    have b7702 := hb (x 15 2 && x 15 13)
    have b7703 := hb (x 14 3 && x 14 14)
    clear * - r7698 b7699 b7700 b7701 b7702 b7703 d7619 d7635 d7693 d7584
    omega
  have d7704 : (x 17 3).toNat = 1 := by
    have r7705 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b7706 := hb (x 17 3)
    have b7707 := hb (x 17 11)
    clear * - r7705 b7706 b7707 d7697
    omega
  have d7708 : (x 20 12).toNat = 0 := by
    have r7709 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7710 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e7711 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b7712 := hb (x 17 3)
    have b7713 := hb (x 18 2)
    have b7714 := hb (x 19 13)
    have b7715 := hb (x 20 12)
    clear * - r7709 e7710 e7711 b7712 b7713 b7714 b7715 d7704
    omega
  have d7716 : (x 19 13).toNat = 0 := by
    have r7717 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7718 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e7719 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b7720 := hb (x 17 3)
    have b7721 := hb (x 18 2)
    have b7722 := hb (x 19 13)
    have b7723 := hb (x 20 12)
    clear * - r7717 e7718 e7719 b7720 b7721 b7722 b7723 d7708 d7704
    omega
  have d7724 : (x 18 1 && x 18 14).toNat = 1 := by
    have r7725 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7726 := hb (x 17 2)
    have b7727 := hb (x 19 13)
    have b7728 := hb (x 18 1 && x 18 14)
    clear * - r7725 b7726 b7727 b7728 d7716 d7568
    omega
  have d7729 : (x 18 14).toNat = 1 := by
    have r7730 := hand2 (x 18 1) (x 18 14)
    have b7731 := hb (x 18 14)
    have b7732 := hb (x 18 1 && x 18 14)
    clear * - r7730 b7731 b7732 d7724
    omega
  have d7733 : (x 17 1).toNat = 0 := by
    have r7734 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7735 := hb (x 17 1)
    have b7736 := hb (x 18 14)
    clear * - r7734 b7735 b7736 d7729
    omega
  have d7737 : (x 17 1 && x 17 11).toNat = 0 := by
    have r7738 := hand1 (x 17 1) (x 17 11)
    have b7739 := hb (x 17 1)
    have b7740 := hb (x 17 1 && x 17 11)
    clear * - r7738 b7739 b7740 d7733
    omega
  have d7741 : (x 18 2).toNat = 0 := by
    have r7742 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7743 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e7744 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b7745 := hb (x 17 3)
    have b7746 := hb (x 18 2)
    have b7747 := hb (x 19 13)
    have b7748 := hb (x 20 12)
    clear * - r7742 e7743 e7744 b7745 b7746 b7747 b7748 d7708 d7716 d7704
    omega
  have d7749 : (x 18 10).toNat = 0 := by
    have r7750 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
    have b7751 := hb (x 18 2)
    have b7752 := hb (x 18 10)
    clear * - r7750 b7751 b7752 d7741
    omega
  have r7753 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b7754 := hb (x 13 5)
  have b7755 := hb (x 18 10)
  have b7756 := hb (x 17 1 && x 17 11)
  have b7757 := hb (x 16 2 && x 16 12)
  have b7758 := hb (x 15 3 && x 15 13)
  have b7759 := hb (x 14 4 && x 14 14)
  linarith only [r7753, b7754, b7755, b7756, b7757, b7758, b7759, d7749, d7737, d7623, d7639, d7521, d7533]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b000010001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 3).toNat = 1)
    (g2 : (x (-1) 5).toNat = 0)
    (g3 : (x (-1) 10).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 2).toNat = 0)
    (g6 : (x 0 4).toNat = 0)
    (g7 : (x 0 9).toNat = 0)
    (g8 : (x 0 11).toNat = 0)
    (g9 : (x 1 9).toNat = 0)
    (g10 : (x 1 10).toNat = 0)
    (g11 : (x 1 13).toNat = 0)
    (g12 : (x 3 2).toNat = 0)
    (g13 : (x 0 1 && x 0 10).toNat = 0)
    (g14 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g15 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g16 : (x 1 2 && x 1 11).toNat = 0)
    (g17 : (x 0 3 && x 0 12).toNat = 0)
    (g18 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g19 : (x 1 3 && x 1 13).toNat = 0)
    (g20 : (x 0 4 && x 0 14).toNat = 0)
    (g21 : (x 0 1 && x 0 12).toNat = 0)
    (g22 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g23 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g24 : (x 1 2 && x 1 13).toNat = 0)
    (g25 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d7761 : (x 2 12).toNat = 0 := by
    have r7762 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e7763 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e7764 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b7765 := hb (x (-1) 3)
    have b7766 := hb (x 0 2)
    have b7767 := hb (x 1 13)
    have b7768 := hb (x 2 12)
    clear * - r7762 e7763 e7764 b7765 b7766 b7767 b7768 g11 g5 g1
    omega
  have d7769 : (x 2 1 && x 2 12).toNat = 0 := by
    have r7770 := hand2 (x 2 1) (x 2 12)
    have b7771 := hb (x 2 12)
    have b7772 := hb (x 2 1 && x 2 12)
    clear * - r7770 b7771 b7772 d7761
    omega
  have d7773 : (x 2 2 && x 2 12).toNat = 0 := by
    have r7774 := hand2 (x 2 2) (x 2 12)
    have b7775 := hb (x 2 12)
    have b7776 := hb (x 2 2 && x 2 12)
    clear * - r7774 b7775 b7776 d7761
    omega
  have r7777 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7778 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
  have e7779 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
  have e7780 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
  have e7781 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
  have e7782 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
  have e7783 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
  have r7784 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7785 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
  have e7786 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
  have e7787 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
  have e7788 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
  have e7789 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
  have e7790 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
  have r7791 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7792 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
  have e7793 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
  have e7794 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
  have e7795 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
  have e7796 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
  have e7797 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
  have r7798 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7799 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
  have e7800 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
  have r7801 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e7802 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
  have e7803 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
  have r7804 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7805 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7806 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7807 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7808 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7809 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7810 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7811 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7812 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r7813 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
  have r7814 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
  have r7815 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
  have r7816 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
  have r7817 := hand2 (x (-3) 4) (x (-3) 13)
  have r7818 := hand1 (x (-4) 5) (x (-4) 14)
  have r7819 := hand2 (x 2 1) (x 2 10)
  have r7820 := hand1 (x (-2) 5) (x (-2) 14)
  have r7821 := hand1 (x 3 1) (x 3 11)
  have r7822 := hand2 (x (-2) 1) (x (-2) 14)
  have r7823 := hand2 (x 4 1) (x 4 14)
  linarith only [r7777, e7778, e7779, e7780, e7781, e7782, e7783, r7784, e7785, e7786, e7787, e7788, e7789, e7790, r7791, e7792, e7793, e7794, e7795, e7796, e7797, r7798, e7799, e7800, r7801, e7802, e7803, r7804, r7805, r7806, r7807, r7808, r7809, r7810, r7811, r7812, r7813, r7814, r7815, r7816, r7817, r7818, r7819, r7820, r7821, r7822, r7823, g0, g2, g3, g4, g6, g7, g8, g9, g10, g12, g13, g14, g15, g16, g17, g18, d7773, g19, g20, g21, g22, g23, d7769, g24, g25]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00001001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 1 1).toNat = 1)
    (g1 : (x 1 2).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d7889 : (x 2 14).toNat = 0 := by
    have r7890 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7891 := hb (x 1 1)
    have b7892 := hb (x 2 14)
    clear * - r7890 b7891 b7892 g0
    omega
  have d7893 : (x 2 1 && x 2 14).toNat = 0 := by
    have r7894 := hand2 (x 2 1) (x 2 14)
    have b7895 := hb (x 2 14)
    have b7896 := hb (x 2 1 && x 2 14)
    clear * - r7894 b7895 b7896 d7889
    omega
  have d7897 : (x 2 2).toNat = 0 := by
    have r7898 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b7899 := hb (x 2 2)
    have b7900 := hb (x 2 14)
    clear * - r7898 b7899 b7900 d7889
    omega
  have d7901 : (x 4 13).toNat = 1 := by
    have r7902 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7903 := hb (x 2 2)
    have b7904 := hb (x 4 13)
    have b7905 := hb (x 3 1 && x 3 14)
    clear * - r7902 b7903 b7904 b7905 g3 d7897
    omega
  have d7906 : (x 4 1).toNat = 1 := by
    have r7907 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b7908 := hb (x 4 1)
    have b7909 := hb (x 4 13)
    clear * - r7907 b7908 b7909 d7901
    omega
  have d7910 : (x 5 14).toNat = 0 := by
    have r7911 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7912 := hb (x 4 1)
    have b7913 := hb (x 5 14)
    clear * - r7911 b7912 b7913 d7906
    omega
  have d7914 : (x 5 1 && x 5 14).toNat = 0 := by
    have r7915 := hand2 (x 5 1) (x 5 14)
    have b7916 := hb (x 5 14)
    have b7917 := hb (x 5 1 && x 5 14)
    clear * - r7915 b7916 b7917 d7910
    omega
  have d7918 : (x 5 2).toNat = 0 := by
    have r7919 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b7920 := hb (x 5 2)
    have b7921 := hb (x 5 14)
    clear * - r7919 b7920 b7921 d7910
    omega
  have d7922 : (x 3 13).toNat = 1 := by
    have r7923 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7924 := hb (x 1 2)
    have b7925 := hb (x 3 13)
    have b7926 := hb (x 2 1 && x 2 14)
    clear * - r7923 b7924 b7925 b7926 d7893 g1
    omega
  have d7927 : (x 3 1).toNat = 1 := by
    have r7928 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b7929 := hb (x 3 1)
    have b7930 := hb (x 3 13)
    clear * - r7928 b7929 b7930 d7922
    omega
  have d7931 : (x 4 14).toNat = 0 := by
    have r7932 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7933 := hb (x 3 1)
    have b7934 := hb (x 4 14)
    clear * - r7932 b7933 b7934 d7927
    omega
  have d7935 : (x 4 1 && x 4 14).toNat = 0 := by
    have r7936 := hand2 (x 4 1) (x 4 14)
    have b7937 := hb (x 4 14)
    have b7938 := hb (x 4 1 && x 4 14)
    clear * - r7936 b7937 b7938 d7931
    omega
  have d7939 : (x 5 13).toNat = 1 := by
    have r7940 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7941 := hb (x 3 2)
    have b7942 := hb (x 5 13)
    have b7943 := hb (x 4 1 && x 4 14)
    clear * - r7940 b7941 b7942 b7943 d7935 g2
    omega
  have d7944 : (x 5 1).toNat = 1 := by
    have r7945 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b7946 := hb (x 5 1)
    have b7947 := hb (x 5 13)
    clear * - r7945 b7946 b7947 d7939
    omega
  have d7948 : (x 6 14).toNat = 0 := by
    have r7949 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7950 := hb (x 5 1)
    have b7951 := hb (x 6 14)
    clear * - r7949 b7950 b7951 d7944
    omega
  have d7952 : (x 6 1 && x 6 14).toNat = 0 := by
    have r7953 := hand2 (x 6 1) (x 6 14)
    have b7954 := hb (x 6 14)
    have b7955 := hb (x 6 1 && x 6 14)
    clear * - r7953 b7954 b7955 d7948
    omega
  have d7956 : (x 7 13).toNat = 1 := by
    have r7957 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7958 := hb (x 5 2)
    have b7959 := hb (x 7 13)
    have b7960 := hb (x 6 1 && x 6 14)
    clear * - r7957 b7958 b7959 b7960 d7952 d7918
    omega
  have d7961 : (x 7 1).toNat = 1 := by
    have r7962 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b7963 := hb (x 7 1)
    have b7964 := hb (x 7 13)
    clear * - r7962 b7963 b7964 d7956
    omega
  have d7965 : (x 8 14).toNat = 0 := by
    have r7966 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7967 := hb (x 7 1)
    have b7968 := hb (x 8 14)
    clear * - r7966 b7967 b7968 d7961
    omega
  have d7969 : (x 8 1 && x 8 14).toNat = 0 := by
    have r7970 := hand2 (x 8 1) (x 8 14)
    have b7971 := hb (x 8 14)
    have b7972 := hb (x 8 1 && x 8 14)
    clear * - r7970 b7971 b7972 d7965
    omega
  have d7973 : (x 8 2).toNat = 0 := by
    have r7974 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b7975 := hb (x 8 2)
    have b7976 := hb (x 8 14)
    clear * - r7974 b7975 b7976 d7965
    omega
  have d7977 : (x 6 2).toNat = 0 := by
    have r7978 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b7979 := hb (x 6 2)
    have b7980 := hb (x 6 14)
    clear * - r7978 b7979 b7980 d7948
    omega
  have d7981 : (x 4 2).toNat = 0 := by
    have r7982 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b7983 := hb (x 4 2)
    have b7984 := hb (x 4 14)
    clear * - r7982 b7983 b7984 d7931
    omega
  have d7985 : (x 6 13).toNat = 1 := by
    have r7986 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7987 := hb (x 4 2)
    have b7988 := hb (x 6 13)
    have b7989 := hb (x 5 1 && x 5 14)
    clear * - r7986 b7987 b7988 b7989 d7914 d7981
    omega
  have d7990 : (x 6 1).toNat = 1 := by
    have r7991 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b7992 := hb (x 6 1)
    have b7993 := hb (x 6 13)
    clear * - r7991 b7992 b7993 d7985
    omega
  have d7994 : (x 7 14).toNat = 0 := by
    have r7995 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b7996 := hb (x 6 1)
    have b7997 := hb (x 7 14)
    clear * - r7995 b7996 b7997 d7990
    omega
  have d7998 : (x 7 1 && x 7 14).toNat = 0 := by
    have r7999 := hand2 (x 7 1) (x 7 14)
    have b8000 := hb (x 7 14)
    have b8001 := hb (x 7 1 && x 7 14)
    clear * - r7999 b8000 b8001 d7994
    omega
  have d8002 : (x 8 13).toNat = 1 := by
    have r8003 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8004 := hb (x 6 2)
    have b8005 := hb (x 8 13)
    have b8006 := hb (x 7 1 && x 7 14)
    clear * - r8003 b8004 b8005 b8006 d7998 d7977
    omega
  have d8007 : (x 8 1).toNat = 1 := by
    have r8008 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b8009 := hb (x 8 1)
    have b8010 := hb (x 8 13)
    clear * - r8008 b8009 b8010 d8002
    omega
  have d8011 : (x 9 14).toNat = 0 := by
    have r8012 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8013 := hb (x 8 1)
    have b8014 := hb (x 9 14)
    clear * - r8012 b8013 b8014 d8007
    omega
  have d8015 : (x 9 1 && x 9 14).toNat = 0 := by
    have r8016 := hand2 (x 9 1) (x 9 14)
    have b8017 := hb (x 9 14)
    have b8018 := hb (x 9 1 && x 9 14)
    clear * - r8016 b8017 b8018 d8011
    omega
  have d8019 : (x 10 13).toNat = 1 := by
    have r8020 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8021 := hb (x 8 2)
    have b8022 := hb (x 10 13)
    have b8023 := hb (x 9 1 && x 9 14)
    clear * - r8020 b8021 b8022 b8023 d8015 d7973
    omega
  have d8024 : (x 10 1).toNat = 1 := by
    have r8025 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b8026 := hb (x 10 1)
    have b8027 := hb (x 10 13)
    clear * - r8025 b8026 b8027 d8019
    omega
  have d8028 : (x 11 14).toNat = 0 := by
    have r8029 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8030 := hb (x 10 1)
    have b8031 := hb (x 11 14)
    clear * - r8029 b8030 b8031 d8024
    omega
  have d8032 : (x 11 1 && x 11 14).toNat = 0 := by
    have r8033 := hand2 (x 11 1) (x 11 14)
    have b8034 := hb (x 11 14)
    have b8035 := hb (x 11 1 && x 11 14)
    clear * - r8033 b8034 b8035 d8028
    omega
  have d8036 : (x 11 2).toNat = 0 := by
    have r8037 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b8038 := hb (x 11 2)
    have b8039 := hb (x 11 14)
    clear * - r8037 b8038 b8039 d8028
    omega
  have d8040 : (x 9 2).toNat = 0 := by
    have r8041 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b8042 := hb (x 9 2)
    have b8043 := hb (x 9 14)
    clear * - r8041 b8042 b8043 d8011
    omega
  have d8044 : (x 7 2).toNat = 0 := by
    have r8045 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b8046 := hb (x 7 2)
    have b8047 := hb (x 7 14)
    clear * - r8045 b8046 b8047 d7994
    omega
  have d8048 : (x 9 13).toNat = 1 := by
    have r8049 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8050 := hb (x 7 2)
    have b8051 := hb (x 9 13)
    have b8052 := hb (x 8 1 && x 8 14)
    clear * - r8049 b8050 b8051 b8052 d7969 d8044
    omega
  have d8053 : (x 9 1).toNat = 1 := by
    have r8054 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b8055 := hb (x 9 1)
    have b8056 := hb (x 9 13)
    clear * - r8054 b8055 b8056 d8048
    omega
  have d8057 : (x 10 14).toNat = 0 := by
    have r8058 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8059 := hb (x 9 1)
    have b8060 := hb (x 10 14)
    clear * - r8058 b8059 b8060 d8053
    omega
  have d8061 : (x 10 1 && x 10 14).toNat = 0 := by
    have r8062 := hand2 (x 10 1) (x 10 14)
    have b8063 := hb (x 10 14)
    have b8064 := hb (x 10 1 && x 10 14)
    clear * - r8062 b8063 b8064 d8057
    omega
  have d8065 : (x 11 13).toNat = 1 := by
    have r8066 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8067 := hb (x 9 2)
    have b8068 := hb (x 11 13)
    have b8069 := hb (x 10 1 && x 10 14)
    clear * - r8066 b8067 b8068 b8069 d8061 d8040
    omega
  have d8070 : (x 11 1).toNat = 1 := by
    have r8071 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b8072 := hb (x 11 1)
    have b8073 := hb (x 11 13)
    clear * - r8071 b8072 b8073 d8065
    omega
  have d8074 : (x 12 14).toNat = 0 := by
    have r8075 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8076 := hb (x 11 1)
    have b8077 := hb (x 12 14)
    clear * - r8075 b8076 b8077 d8070
    omega
  have d8078 : (x 12 1 && x 12 14).toNat = 0 := by
    have r8079 := hand2 (x 12 1) (x 12 14)
    have b8080 := hb (x 12 14)
    have b8081 := hb (x 12 1 && x 12 14)
    clear * - r8079 b8080 b8081 d8074
    omega
  have d8082 : (x 13 13).toNat = 1 := by
    have r8083 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8084 := hb (x 11 2)
    have b8085 := hb (x 13 13)
    have b8086 := hb (x 12 1 && x 12 14)
    clear * - r8083 b8084 b8085 b8086 d8078 d8036
    omega
  have d8087 : (x 13 1).toNat = 1 := by
    have r8088 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
    have b8089 := hb (x 13 1)
    have b8090 := hb (x 13 13)
    clear * - r8088 b8089 b8090 d8082
    omega
  have d8091 : (x 14 14).toNat = 0 := by
    have r8092 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8093 := hb (x 13 1)
    have b8094 := hb (x 14 14)
    clear * - r8092 b8093 b8094 d8087
    omega
  have d8095 : (x 14 1 && x 14 14).toNat = 0 := by
    have r8096 := hand2 (x 14 1) (x 14 14)
    have b8097 := hb (x 14 14)
    have b8098 := hb (x 14 1 && x 14 14)
    clear * - r8096 b8097 b8098 d8091
    omega
  have d8099 : (x 14 3 && x 14 14).toNat = 0 := by
    have r8100 := hand2 (x 14 3) (x 14 14)
    have b8101 := hb (x 14 14)
    have b8102 := hb (x 14 3 && x 14 14)
    clear * - r8100 b8101 b8102 d8091
    omega
  have d8103 : (x 14 2).toNat = 0 := by
    have r8104 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
    have b8105 := hb (x 14 2)
    have b8106 := hb (x 14 14)
    clear * - r8104 b8105 b8106 d8091
    omega
  have d8107 : (x 12 2).toNat = 0 := by
    have r8108 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
    have b8109 := hb (x 12 2)
    have b8110 := hb (x 12 14)
    clear * - r8108 b8109 b8110 d8074
    omega
  have d8111 : (x 10 2).toNat = 0 := by
    have r8112 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
    have b8113 := hb (x 10 2)
    have b8114 := hb (x 10 14)
    clear * - r8112 b8113 b8114 d8057
    omega
  have d8115 : (x 12 13).toNat = 1 := by
    have r8116 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8117 := hb (x 10 2)
    have b8118 := hb (x 12 13)
    have b8119 := hb (x 11 1 && x 11 14)
    clear * - r8116 b8117 b8118 b8119 d8032 d8111
    omega
  have d8120 : (x 12 1).toNat = 1 := by
    have r8121 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b8122 := hb (x 12 1)
    have b8123 := hb (x 12 13)
    clear * - r8121 b8122 b8123 d8115
    omega
  have d8124 : (x 13 14).toNat = 0 := by
    have r8125 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8126 := hb (x 12 1)
    have b8127 := hb (x 13 14)
    clear * - r8125 b8126 b8127 d8120
    omega
  have d8128 : (x 13 1 && x 13 14).toNat = 0 := by
    have r8129 := hand2 (x 13 1) (x 13 14)
    have b8130 := hb (x 13 14)
    have b8131 := hb (x 13 1 && x 13 14)
    clear * - r8129 b8130 b8131 d8124
    omega
  have d8132 : (x 14 13).toNat = 1 := by
    have r8133 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8134 := hb (x 12 2)
    have b8135 := hb (x 14 13)
    have b8136 := hb (x 13 1 && x 13 14)
    clear * - r8133 b8134 b8135 b8136 d8128 d8107
    omega
  have d8137 : (x 14 1).toNat = 1 := by
    have r8138 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b8139 := hb (x 14 1)
    have b8140 := hb (x 14 13)
    clear * - r8138 b8139 b8140 d8132
    omega
  have d8141 : (x 15 14).toNat = 0 := by
    have r8142 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8143 := hb (x 14 1)
    have b8144 := hb (x 15 14)
    clear * - r8142 b8143 b8144 d8137
    omega
  have d8145 : (x 15 1 && x 15 14).toNat = 0 := by
    have r8146 := hand2 (x 15 1) (x 15 14)
    have b8147 := hb (x 15 14)
    have b8148 := hb (x 15 1 && x 15 14)
    clear * - r8146 b8147 b8148 d8141
    omega
  have d8149 : (x 16 13).toNat = 1 := by
    have r8150 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8151 := hb (x 14 2)
    have b8152 := hb (x 16 13)
    have b8153 := hb (x 15 1 && x 15 14)
    clear * - r8150 b8151 b8152 b8153 d8145 d8103
    omega
  have d8154 : (x 16 1).toNat = 1 := by
    have r8155 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
    have b8156 := hb (x 16 1)
    have b8157 := hb (x 16 13)
    clear * - r8155 b8156 b8157 d8149
    omega
  have d8158 : (x 17 14).toNat = 0 := by
    have r8159 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8160 := hb (x 16 1)
    have b8161 := hb (x 17 14)
    clear * - r8159 b8160 b8161 d8154
    omega
  have d8162 : (x 17 2).toNat = 0 := by
    have r8163 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
    have b8164 := hb (x 17 2)
    have b8165 := hb (x 17 14)
    clear * - r8163 b8164 b8165 d8158
    omega
  have d8166 : (x 15 2).toNat = 0 := by
    have r8167 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b8168 := hb (x 15 2)
    have b8169 := hb (x 15 14)
    clear * - r8167 b8168 b8169 d8141
    omega
  have d8170 : (x 15 2 && x 15 13).toNat = 0 := by
    have r8171 := hand1 (x 15 2) (x 15 13)
    have b8172 := hb (x 15 2)
    have b8173 := hb (x 15 2 && x 15 13)
    clear * - r8171 b8172 b8173 d8166
    omega
  have d8174 : (x 13 2).toNat = 0 := by
    have r8175 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
    have b8176 := hb (x 13 2)
    have b8177 := hb (x 13 14)
    clear * - r8175 b8176 b8177 d8124
    omega
  have d8178 : (x 15 13).toNat = 1 := by
    have r8179 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8180 := hb (x 13 2)
    have b8181 := hb (x 15 13)
    have b8182 := hb (x 14 1 && x 14 14)
    clear * - r8179 b8180 b8181 b8182 d8095 d8174
    omega
  have d8183 : (x 15 1).toNat = 1 := by
    have r8184 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have b8185 := hb (x 15 1)
    have b8186 := hb (x 15 13)
    clear * - r8184 b8185 b8186 d8178
    omega
  have d8187 : (x 16 14).toNat = 0 := by
    have r8188 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8189 := hb (x 15 1)
    have b8190 := hb (x 16 14)
    clear * - r8188 b8189 b8190 d8183
    omega
  have d8191 : (x 16 1 && x 16 14).toNat = 0 := by
    have r8192 := hand2 (x 16 1) (x 16 14)
    have b8193 := hb (x 16 14)
    have b8194 := hb (x 16 1 && x 16 14)
    clear * - r8192 b8193 b8194 d8187
    omega
  have d8195 : (x 17 13).toNat = 1 := by
    have r8196 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8197 := hb (x 15 2)
    have b8198 := hb (x 17 13)
    have b8199 := hb (x 16 1 && x 16 14)
    clear * - r8196 b8197 b8198 b8199 d8191 d8166
    omega
  have d8200 : (x 17 1).toNat = 1 := by
    have r8201 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
    have b8202 := hb (x 17 1)
    have b8203 := hb (x 17 13)
    clear * - r8201 b8202 b8203 d8195
    omega
  have d8204 : (x 18 14).toNat = 0 := by
    have r8205 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8206 := hb (x 17 1)
    have b8207 := hb (x 18 14)
    clear * - r8205 b8206 b8207 d8200
    omega
  have d8208 : (x 18 1 && x 18 14).toNat = 0 := by
    have r8209 := hand2 (x 18 1) (x 18 14)
    have b8210 := hb (x 18 14)
    have b8211 := hb (x 18 1 && x 18 14)
    clear * - r8209 b8210 b8211 d8204
    omega
  have d8212 : (x 19 13).toNat = 1 := by
    have r8213 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8214 := hb (x 17 2)
    have b8215 := hb (x 19 13)
    have b8216 := hb (x 18 1 && x 18 14)
    clear * - r8213 b8214 b8215 b8216 d8208 d8162
    omega
  have d8217 : (x 18 2).toNat = 0 := by
    have r8218 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
    have b8219 := hb (x 18 2)
    have b8220 := hb (x 18 14)
    clear * - r8218 b8219 b8220 d8204
    omega
  have d8221 : (x 20 12).toNat = 0 := by
    have r8222 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8223 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e8224 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b8225 := hb (x 17 3)
    have b8226 := hb (x 18 2)
    have b8227 := hb (x 19 13)
    have b8228 := hb (x 20 12)
    clear * - r8222 e8223 e8224 b8225 b8226 b8227 b8228 d8212 d8217
    omega
  have d8229 : (x 17 3).toNat = 0 := by
    have r8230 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8231 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e8232 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b8233 := hb (x 17 3)
    have b8234 := hb (x 18 2)
    have b8235 := hb (x 19 13)
    have b8236 := hb (x 20 12)
    clear * - r8230 e8231 e8232 b8233 b8234 b8235 b8236 d8221 d8212 d8217
    omega
  have d8237 : (x 17 11).toNat = 0 := by
    have r8238 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b8239 := hb (x 17 3)
    have b8240 := hb (x 17 11)
    clear * - r8238 b8239 b8240 d8229
    omega
  have d8241 : (x 16 12).toNat = 0 := by
    have r8242 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8243 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e8244 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b8245 := hb (x 13 3)
    have b8246 := hb (x 14 2)
    have b8247 := hb (x 15 13)
    have b8248 := hb (x 16 12)
    clear * - r8242 e8243 e8244 b8245 b8246 b8247 b8248 d8178 d8103
    omega
  have d8249 : (x 16 1 && x 16 12).toNat = 0 := by
    have r8250 := hand2 (x 16 1) (x 16 12)
    have b8251 := hb (x 16 12)
    have b8252 := hb (x 16 1 && x 16 12)
    clear * - r8250 b8251 b8252 d8241
    omega
  have d8253 : (x 13 12).toNat = 0 := by
    have r8254 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8255 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e8256 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b8257 := hb (x 10 3)
    have b8258 := hb (x 11 2)
    have b8259 := hb (x 12 13)
    have b8260 := hb (x 13 12)
    clear * - r8254 e8255 e8256 b8257 b8258 b8259 b8260 d8115 d8036
    omega
  have d8261 : (x 13 4).toNat = 0 := by
    have r8262 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b8263 := hb (x 13 4)
    have b8264 := hb (x 13 12)
    clear * - r8262 b8263 b8264 d8253
    omega
  have r8265 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b8266 := hb (x 13 4)
  have b8267 := hb (x 17 11)
  have b8268 := hb (x 16 1 && x 16 12)
  have b8269 := hb (x 15 2 && x 15 13)
  have b8270 := hb (x 14 3 && x 14 14)
  linarith only [r8265, b8266, b8267, b8268, b8269, b8270, d8237, d8249, d8170, d8099, d8261]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b0000101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 5).toNat = 0)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x 0 4).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 9).toNat = 1)
    (g6 : (x 1 2).toNat = 0)
    (g7 : (x 1 4).toNat = 0)
    (g8 : (x 3 2).toNat = 0)
    (g9 : (x 0 4 && x 0 14).toNat = 0)
    (g10 : (x 0 1 && x 0 12).toNat = 0)
    (g11 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g12 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g13 : (x 3 1 && x 3 12).toNat = 0)
    (g14 : (x 1 3 && x 1 14).toNat = 0)
    (g15 : (x 3 2 && x 3 13).toNat = 0)
    (g16 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8272 : (x 1 8).toNat = 0 := by
    have r8273 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8274 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e8275 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e8276 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e8277 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e8278 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e8279 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b8280 := hb (x (-6) 7)
    have b8281 := hb (x (-5) 6)
    have b8282 := hb (x (-4) 5)
    have b8283 := hb (x (-3) 4)
    have b8284 := hb (x (-2) 11)
    have b8285 := hb (x (-1) 10)
    have b8286 := hb (x 0 9)
    have b8287 := hb (x 1 8)
    clear * - r8273 e8274 e8275 e8276 e8277 e8278 e8279 b8280 b8281 b8282 b8283 b8284 b8285 b8286 b8287 g5 g2 g0
    omega
  have d8288 : (x (-3) 4).toNat = 0 := by
    have r8289 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8290 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e8291 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e8292 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e8293 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e8294 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e8295 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b8296 := hb (x (-6) 7)
    have b8297 := hb (x (-5) 6)
    have b8298 := hb (x (-4) 5)
    have b8299 := hb (x (-3) 4)
    have b8300 := hb (x (-2) 11)
    have b8301 := hb (x (-1) 10)
    have b8302 := hb (x 0 9)
    have b8303 := hb (x 1 8)
    clear * - r8289 e8290 e8291 e8292 e8293 e8294 e8295 b8296 b8297 b8298 b8299 b8300 b8301 b8302 b8303 d8272 g5 g2 g0
    omega
  have d8304 : (x 1 11).toNat = 1 := by
    have r8305 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8306 := hb (x (-3) 4)
    have b8307 := hb (x 1 11)
    have b8308 := hb (x 0 1 && x 0 12)
    have b8309 := hb (x (-1) 2 && x (-1) 13)
    have b8310 := hb (x (-2) 3 && x (-2) 14)
    clear * - r8305 b8306 b8307 b8308 b8309 b8310 g10 g11 g12 d8288
    omega
  have d8311 : (x 1 3).toNat = 1 := by
    have r8312 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b8313 := hb (x 1 3)
    have b8314 := hb (x 1 11)
    clear * - r8312 b8313 b8314 d8304
    omega
  have d8315 : (x 4 12).toNat = 0 := by
    have r8316 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8317 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8318 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8319 := hb (x 1 3)
    have b8320 := hb (x 2 2)
    have b8321 := hb (x 3 13)
    have b8322 := hb (x 4 12)
    clear * - r8316 e8317 e8318 b8319 b8320 b8321 b8322 d8311
    omega
  have d8323 : (x 4 1 && x 4 12).toNat = 0 := by
    have r8324 := hand2 (x 4 1) (x 4 12)
    have b8325 := hb (x 4 12)
    have b8326 := hb (x 4 1 && x 4 12)
    clear * - r8324 b8325 b8326 d8315
    omega
  have d8327 : (x 4 2 && x 4 12).toNat = 0 := by
    have r8328 := hand2 (x 4 2) (x 4 12)
    have b8329 := hb (x 4 12)
    have b8330 := hb (x 4 2 && x 4 12)
    clear * - r8328 b8329 b8330 d8315
    omega
  have d8331 : (x 3 13).toNat = 0 := by
    have r8332 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8333 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8334 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8335 := hb (x 1 3)
    have b8336 := hb (x 2 2)
    have b8337 := hb (x 3 13)
    have b8338 := hb (x 4 12)
    clear * - r8332 e8333 e8334 b8335 b8336 b8337 b8338 d8315 d8311
    omega
  have d8339 : (x 3 3 && x 3 13).toNat = 0 := by
    have r8340 := hand2 (x 3 3) (x 3 13)
    have b8341 := hb (x 3 13)
    have b8342 := hb (x 3 3 && x 3 13)
    clear * - r8340 b8341 b8342 d8331
    omega
  have d8343 : (x 2 1 && x 2 14).toNat = 1 := by
    have r8344 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8345 := hb (x 1 2)
    have b8346 := hb (x 3 13)
    have b8347 := hb (x 2 1 && x 2 14)
    clear * - r8344 b8345 b8346 b8347 d8331 g6
    omega
  have d8348 : (x 2 14).toNat = 1 := by
    have r8349 := hand2 (x 2 1) (x 2 14)
    have b8350 := hb (x 2 14)
    have b8351 := hb (x 2 1 && x 2 14)
    clear * - r8349 b8350 b8351 d8343
    omega
  have d8352 : (x 1 1).toNat = 0 := by
    have r8353 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8354 := hb (x 1 1)
    have b8355 := hb (x 2 14)
    clear * - r8353 b8354 b8355 d8348
    omega
  have d8356 : (x 1 13).toNat = 0 := by
    have r8357 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b8358 := hb (x 1 1)
    have b8359 := hb (x 1 13)
    clear * - r8357 b8358 b8359 d8352
    omega
  have d8360 : (x 1 3 && x 1 13).toNat = 0 := by
    have r8361 := hand2 (x 1 3) (x 1 13)
    have b8362 := hb (x 1 13)
    have b8363 := hb (x 1 3 && x 1 13)
    clear * - r8361 b8362 b8363 d8356
    omega
  have d8364 : (x 1 5).toNat = 0 := by
    have r8365 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b8366 := hb (x 1 5)
    have b8367 := hb (x 1 13)
    clear * - r8365 b8366 b8367 d8356
    omega
  have d8368 : (x 2 2).toNat = 0 := by
    have r8369 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8370 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8371 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8372 := hb (x 1 3)
    have b8373 := hb (x 2 2)
    have b8374 := hb (x 3 13)
    have b8375 := hb (x 4 12)
    clear * - r8369 e8370 e8371 b8372 b8373 b8374 b8375 d8315 d8331 d8311
    omega
  have d8376 : (x 2 2 && x 2 13).toNat = 0 := by
    have r8377 := hand1 (x 2 2) (x 2 13)
    have b8378 := hb (x 2 2)
    have b8379 := hb (x 2 2 && x 2 13)
    clear * - r8377 b8378 b8379 d8368
    omega
  have d8380 : (x 4 11).toNat = 1 := by
    have r8381 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8382 := hb (x 0 4)
    have b8383 := hb (x 4 11)
    have b8384 := hb (x 3 1 && x 3 12)
    have b8385 := hb (x 2 2 && x 2 13)
    have b8386 := hb (x 1 3 && x 1 14)
    clear * - r8381 b8382 b8383 b8384 b8385 b8386 g13 d8376 g14 g3
    omega
  have d8387 : (x 4 3).toNat = 1 := by
    have r8388 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b8389 := hb (x 4 3)
    have b8390 := hb (x 4 11)
    clear * - r8388 b8389 b8390 d8380
    omega
  have d8391 : (x 7 12).toNat = 0 := by
    have r8392 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8393 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e8394 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b8395 := hb (x 4 3)
    have b8396 := hb (x 5 2)
    have b8397 := hb (x 6 13)
    have b8398 := hb (x 7 12)
    clear * - r8392 e8393 e8394 b8395 b8396 b8397 b8398 d8387
    omega
  have d8399 : (x 6 13).toNat = 0 := by
    have r8400 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8401 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e8402 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b8403 := hb (x 4 3)
    have b8404 := hb (x 5 2)
    have b8405 := hb (x 6 13)
    have b8406 := hb (x 7 12)
    clear * - r8400 e8401 e8402 b8403 b8404 b8405 b8406 d8391 d8387
    omega
  have d8407 : (x 5 2).toNat = 0 := by
    have r8408 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8409 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e8410 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b8411 := hb (x 4 3)
    have b8412 := hb (x 5 2)
    have b8413 := hb (x 6 13)
    have b8414 := hb (x 7 12)
    clear * - r8408 e8409 e8410 b8411 b8412 b8413 b8414 d8391 d8399 d8387
    omega
  have d8415 : (x 2 2 && x 2 12).toNat = 0 := by
    have r8416 := hand1 (x 2 2) (x 2 12)
    have b8417 := hb (x 2 2)
    have b8418 := hb (x 2 2 && x 2 12)
    clear * - r8416 b8417 b8418 d8368
    omega
  have d8419 : (x 4 13).toNat = 1 := by
    have r8420 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8421 := hb (x 2 2)
    have b8422 := hb (x 4 13)
    have b8423 := hb (x 3 1 && x 3 14)
    clear * - r8420 b8421 b8422 b8423 g16 d8368
    omega
  have d8424 : (x 4 1).toNat = 1 := by
    have r8425 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b8426 := hb (x 4 1)
    have b8427 := hb (x 4 13)
    clear * - r8425 b8426 b8427 d8419
    omega
  have d8428 : (x 5 14).toNat = 0 := by
    have r8429 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8430 := hb (x 4 1)
    have b8431 := hb (x 5 14)
    clear * - r8429 b8430 b8431 d8424
    omega
  have d8432 : (x 5 1 && x 5 14).toNat = 0 := by
    have r8433 := hand2 (x 5 1) (x 5 14)
    have b8434 := hb (x 5 14)
    have b8435 := hb (x 5 1 && x 5 14)
    clear * - r8433 b8434 b8435 d8428
    omega
  have d8436 : (x 4 2).toNat = 1 := by
    have r8437 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8438 := hb (x 4 2)
    have b8439 := hb (x 6 13)
    have b8440 := hb (x 5 1 && x 5 14)
    clear * - r8437 b8438 b8439 b8440 d8399 d8432
    omega
  have d8441 : (x 4 14).toNat = 1 := by
    have r8442 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b8443 := hb (x 4 2)
    have b8444 := hb (x 4 14)
    clear * - r8442 b8443 b8444 d8436
    omega
  have d8445 : (x 3 1).toNat = 0 := by
    have r8446 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8447 := hb (x 3 1)
    have b8448 := hb (x 4 14)
    clear * - r8446 b8447 b8448 d8441
    omega
  have d8449 : (x 3 1 && x 3 11).toNat = 0 := by
    have r8450 := hand1 (x 3 1) (x 3 11)
    have b8451 := hb (x 3 1)
    have b8452 := hb (x 3 1 && x 3 11)
    clear * - r8450 b8451 b8452 d8445
    omega
  have d8453 : (x 4 10).toNat = 1 := by
    have r8454 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8455 := hb (x (-1) 5)
    have b8456 := hb (x 4 10)
    have b8457 := hb (x 3 1 && x 3 11)
    have b8458 := hb (x 2 2 && x 2 12)
    have b8459 := hb (x 1 3 && x 1 13)
    have b8460 := hb (x 0 4 && x 0 14)
    clear * - r8454 b8455 b8456 b8457 b8458 b8459 b8460 d8449 d8415 d8360 g9 g1
    omega
  have d8461 : (x 6 8).toNat = 0 := by
    have r8462 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8463 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e8464 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e8465 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e8466 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e8467 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e8468 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b8469 := hb (x (-1) 7)
    have b8470 := hb (x 0 6)
    have b8471 := hb (x 1 5)
    have b8472 := hb (x 2 4)
    have b8473 := hb (x 3 11)
    have b8474 := hb (x 4 10)
    have b8475 := hb (x 5 9)
    have b8476 := hb (x 6 8)
    clear * - r8462 e8463 e8464 e8465 e8466 e8467 e8468 b8469 b8470 b8471 b8472 b8473 b8474 b8475 b8476 d8453 d8364 g4
    omega
  have d8477 : (x 5 9).toNat = 0 := by
    have r8478 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8479 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e8480 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e8481 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e8482 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e8483 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e8484 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b8485 := hb (x (-1) 7)
    have b8486 := hb (x 0 6)
    have b8487 := hb (x 1 5)
    have b8488 := hb (x 2 4)
    have b8489 := hb (x 3 11)
    have b8490 := hb (x 4 10)
    have b8491 := hb (x 5 9)
    have b8492 := hb (x 6 8)
    clear * - r8478 e8479 e8480 e8481 e8482 e8483 e8484 b8485 b8486 b8487 b8488 b8489 b8490 b8491 b8492 d8461 d8453 d8364 g4
    omega
  have d8493 : (x 3 11).toNat = 0 := by
    have r8494 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8495 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e8496 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e8497 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e8498 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e8499 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e8500 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b8501 := hb (x (-1) 7)
    have b8502 := hb (x 0 6)
    have b8503 := hb (x 1 5)
    have b8504 := hb (x 2 4)
    have b8505 := hb (x 3 11)
    have b8506 := hb (x 4 10)
    have b8507 := hb (x 5 9)
    have b8508 := hb (x 6 8)
    clear * - r8494 e8495 e8496 e8497 e8498 e8499 e8500 b8501 b8502 b8503 b8504 b8505 b8506 b8507 b8508 d8461 d8477 d8453 d8364 g4
    omega
  have d8509 : (x 2 4).toNat = 0 := by
    have r8510 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8511 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e8512 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e8513 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e8514 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e8515 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e8516 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b8517 := hb (x (-1) 7)
    have b8518 := hb (x 0 6)
    have b8519 := hb (x 1 5)
    have b8520 := hb (x 2 4)
    have b8521 := hb (x 3 11)
    have b8522 := hb (x 4 10)
    have b8523 := hb (x 5 9)
    have b8524 := hb (x 6 8)
    clear * - r8510 e8511 e8512 e8513 e8514 e8515 e8516 b8517 b8518 b8519 b8520 b8521 b8522 b8523 b8524 d8461 d8477 d8453 d8493 d8364 g4
    omega
  have d8525 : (x 2 4 && x 2 14).toNat = 0 := by
    have r8526 := hand1 (x 2 4) (x 2 14)
    have b8527 := hb (x 2 4)
    have b8528 := hb (x 2 4 && x 2 14)
    clear * - r8526 b8527 b8528 d8509
    omega
  have d8529 : (x 5 12).toNat = 0 := by
    have r8530 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8531 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e8532 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b8533 := hb (x 2 3)
    have b8534 := hb (x 3 2)
    have b8535 := hb (x 4 13)
    have b8536 := hb (x 5 12)
    clear * - r8530 e8531 e8532 b8533 b8534 b8535 b8536 d8419 g8
    omega
  have d8537 : (x 2 3).toNat = 0 := by
    have r8538 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8539 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e8540 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b8541 := hb (x 2 3)
    have b8542 := hb (x 3 2)
    have b8543 := hb (x 4 13)
    have b8544 := hb (x 5 12)
    clear * - r8538 e8539 e8540 b8541 b8542 b8543 b8544 d8529 d8419 g8
    omega
  have d8545 : (x 2 3 && x 2 14).toNat = 0 := by
    have r8546 := hand1 (x 2 3) (x 2 14)
    have b8547 := hb (x 2 3)
    have b8548 := hb (x 2 3 && x 2 14)
    clear * - r8546 b8547 b8548 d8537
    omega
  have d8549 : (x 5 11).toNat = 1 := by
    have r8550 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8551 := hb (x 1 4)
    have b8552 := hb (x 5 11)
    have b8553 := hb (x 4 1 && x 4 12)
    have b8554 := hb (x 3 2 && x 3 13)
    have b8555 := hb (x 2 3 && x 2 14)
    clear * - r8550 b8551 b8552 b8553 b8554 b8555 d8323 g15 d8545 g7
    omega
  have d8556 : (x 5 3).toNat = 1 := by
    have r8557 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b8558 := hb (x 5 3)
    have b8559 := hb (x 5 11)
    clear * - r8557 b8558 b8559 d8549
    omega
  have d8560 : (x 8 12).toNat = 0 := by
    have r8561 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8562 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e8563 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b8564 := hb (x 5 3)
    have b8565 := hb (x 6 2)
    have b8566 := hb (x 7 13)
    have b8567 := hb (x 8 12)
    clear * - r8561 e8562 e8563 b8564 b8565 b8566 b8567 d8556
    omega
  have d8568 : (x 7 13).toNat = 0 := by
    have r8569 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8570 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e8571 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b8572 := hb (x 5 3)
    have b8573 := hb (x 6 2)
    have b8574 := hb (x 7 13)
    have b8575 := hb (x 8 12)
    clear * - r8569 e8570 e8571 b8572 b8573 b8574 b8575 d8560 d8556
    omega
  have d8576 : (x 6 1 && x 6 14).toNat = 1 := by
    have r8577 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8578 := hb (x 5 2)
    have b8579 := hb (x 7 13)
    have b8580 := hb (x 6 1 && x 6 14)
    clear * - r8577 b8578 b8579 b8580 d8568 d8407
    omega
  have d8581 : (x 6 14).toNat = 1 := by
    have r8582 := hand2 (x 6 1) (x 6 14)
    have b8583 := hb (x 6 14)
    have b8584 := hb (x 6 1 && x 6 14)
    clear * - r8582 b8583 b8584 d8576
    omega
  have d8585 : (x 5 1).toNat = 0 := by
    have r8586 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8587 := hb (x 5 1)
    have b8588 := hb (x 6 14)
    clear * - r8586 b8587 b8588 d8581
    omega
  have d8589 : (x 5 1 && x 5 11).toNat = 0 := by
    have r8590 := hand1 (x 5 1) (x 5 11)
    have b8591 := hb (x 5 1)
    have b8592 := hb (x 5 1 && x 5 11)
    clear * - r8590 b8591 b8592 d8585
    omega
  have d8593 : (x 6 10).toNat = 1 := by
    have r8594 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8595 := hb (x 1 5)
    have b8596 := hb (x 6 10)
    have b8597 := hb (x 5 1 && x 5 11)
    have b8598 := hb (x 4 2 && x 4 12)
    have b8599 := hb (x 3 3 && x 3 13)
    have b8600 := hb (x 2 4 && x 2 14)
    clear * - r8594 b8595 b8596 b8597 b8598 b8599 b8600 d8589 d8327 d8339 d8525 d8364
    omega
  have d8601 : (x 6 2).toNat = 1 := by
    have r8602 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
    have b8603 := hb (x 6 2)
    have b8604 := hb (x 6 10)
    clear * - r8602 b8603 b8604 d8593
    omega
  have r8605 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e8606 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
  have e8607 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
  have b8608 := hb (x 5 3)
  have b8609 := hb (x 6 2)
  have b8610 := hb (x 7 13)
  have b8611 := hb (x 8 12)
  linarith only [r8605, e8606, e8607, b8608, b8609, b8610, b8611, d8560, d8568, d8601, d8556]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b000011 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x 0 4).toNat = 0)
    (g2 : (x 0 5).toNat = 1)
    (g3 : (x 1 4).toNat = 0)
    (g4 : (x 1 10).toNat = 0)
    (g5 : (x 3 10).toNat = 0)
    (g6 : (x 3 1 && x 3 10).toNat = 0)
    (g7 : (x 1 3 && x 1 12).toNat = 0)
    (g8 : (x 0 4 && x 0 13).toNat = 0)
    (g9 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g10 : (x 0 1 && x 0 11).toNat = 0)
    (g11 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g12 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g13 : (x 0 1 && x 0 12).toNat = 0)
    (g14 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g15 : (x (-2) 3 && x (-2) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8613 : (x 5 8).toNat = 0 := by
    have r8614 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8615 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e8616 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e8617 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e8618 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e8619 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e8620 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b8621 := hb (x (-2) 7)
    have b8622 := hb (x (-1) 6)
    have b8623 := hb (x 0 5)
    have b8624 := hb (x 1 4)
    have b8625 := hb (x 2 11)
    have b8626 := hb (x 3 10)
    have b8627 := hb (x 4 9)
    have b8628 := hb (x 5 8)
    clear * - r8614 e8615 e8616 e8617 e8618 e8619 e8620 b8621 b8622 b8623 b8624 b8625 b8626 b8627 b8628 g5 g3 g2
    omega
  have d8629 : (x 4 9).toNat = 0 := by
    have r8630 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8631 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e8632 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e8633 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e8634 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e8635 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e8636 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b8637 := hb (x (-2) 7)
    have b8638 := hb (x (-1) 6)
    have b8639 := hb (x 0 5)
    have b8640 := hb (x 1 4)
    have b8641 := hb (x 2 11)
    have b8642 := hb (x 3 10)
    have b8643 := hb (x 4 9)
    have b8644 := hb (x 5 8)
    clear * - r8630 e8631 e8632 e8633 e8634 e8635 e8636 b8637 b8638 b8639 b8640 b8641 b8642 b8643 b8644 d8613 g5 g3 g2
    omega
  have d8645 : (x 2 11).toNat = 0 := by
    have r8646 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8647 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e8648 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e8649 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e8650 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e8651 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e8652 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b8653 := hb (x (-2) 7)
    have b8654 := hb (x (-1) 6)
    have b8655 := hb (x 0 5)
    have b8656 := hb (x 1 4)
    have b8657 := hb (x 2 11)
    have b8658 := hb (x 3 10)
    have b8659 := hb (x 4 9)
    have b8660 := hb (x 5 8)
    clear * - r8646 e8647 e8648 e8649 e8650 e8651 e8652 b8653 b8654 b8655 b8656 b8657 b8658 b8659 b8660 d8613 d8629 g5 g3 g2
    omega
  have d8661 : (x 2 2 && x 2 11).toNat = 0 := by
    have r8662 := hand2 (x 2 2) (x 2 11)
    have b8663 := hb (x 2 11)
    have b8664 := hb (x 2 2 && x 2 11)
    clear * - r8662 b8663 b8664 d8645
    omega
  have d8665 : (x (-2) 6).toNat = 1 := by
    have r8666 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8667 := hb (x (-2) 6)
    have b8668 := hb (x 4 9)
    have b8669 := hb (x 3 1 && x 3 10)
    have b8670 := hb (x 2 2 && x 2 11)
    have b8671 := hb (x 1 3 && x 1 12)
    have b8672 := hb (x 0 4 && x 0 13)
    have b8673 := hb (x (-1) 5 && x (-1) 14)
    clear * - r8666 b8667 b8668 b8669 b8670 b8671 b8672 b8673 d8629 g6 d8661 g7 g8 g9
    omega
  have d8674 : (x (-2) 14).toNat = 1 := by
    have r8675 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b8676 := hb (x (-2) 6)
    have b8677 := hb (x (-2) 14)
    clear * - r8675 b8676 b8677 d8665
    omega
  have d8678 : (x (-3) 1).toNat = 0 := by
    have r8679 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8680 := hb (x (-3) 1)
    have b8681 := hb (x (-2) 14)
    clear * - r8679 b8680 b8681 d8674
    omega
  have d8682 : (x (-3) 13).toNat = 0 := by
    have r8683 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b8684 := hb (x (-3) 1)
    have b8685 := hb (x (-3) 13)
    clear * - r8683 b8684 b8685 d8678
    omega
  have d8686 : (x 4 8).toNat = 0 := by
    have r8687 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8688 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e8689 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e8690 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e8691 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e8692 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e8693 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b8694 := hb (x (-3) 7)
    have b8695 := hb (x (-2) 6)
    have b8696 := hb (x (-1) 5)
    have b8697 := hb (x 0 4)
    have b8698 := hb (x 1 11)
    have b8699 := hb (x 2 10)
    have b8700 := hb (x 3 9)
    have b8701 := hb (x 4 8)
    clear * - r8687 e8688 e8689 e8690 e8691 e8692 e8693 b8694 b8695 b8696 b8697 b8698 b8699 b8700 b8701 g1 g0 d8665
    omega
  have d8702 : (x 3 9).toNat = 0 := by
    have r8703 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8704 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e8705 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e8706 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e8707 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e8708 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e8709 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b8710 := hb (x (-3) 7)
    have b8711 := hb (x (-2) 6)
    have b8712 := hb (x (-1) 5)
    have b8713 := hb (x 0 4)
    have b8714 := hb (x 1 11)
    have b8715 := hb (x 2 10)
    have b8716 := hb (x 3 9)
    have b8717 := hb (x 4 8)
    clear * - r8703 e8704 e8705 e8706 e8707 e8708 e8709 b8710 b8711 b8712 b8713 b8714 b8715 b8716 b8717 d8686 g1 g0 d8665
    omega
  have d8718 : (x 2 10).toNat = 0 := by
    have r8719 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8720 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e8721 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e8722 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e8723 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e8724 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e8725 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b8726 := hb (x (-3) 7)
    have b8727 := hb (x (-2) 6)
    have b8728 := hb (x (-1) 5)
    have b8729 := hb (x 0 4)
    have b8730 := hb (x 1 11)
    have b8731 := hb (x 2 10)
    have b8732 := hb (x 3 9)
    have b8733 := hb (x 4 8)
    clear * - r8719 e8720 e8721 e8722 e8723 e8724 e8725 b8726 b8727 b8728 b8729 b8730 b8731 b8732 b8733 d8686 d8702 g1 g0 d8665
    omega
  have d8734 : (x 1 11).toNat = 0 := by
    have r8735 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8736 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e8737 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e8738 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e8739 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e8740 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e8741 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b8742 := hb (x (-3) 7)
    have b8743 := hb (x (-2) 6)
    have b8744 := hb (x (-1) 5)
    have b8745 := hb (x 0 4)
    have b8746 := hb (x 1 11)
    have b8747 := hb (x 2 10)
    have b8748 := hb (x 3 9)
    have b8749 := hb (x 4 8)
    clear * - r8735 e8736 e8737 e8738 e8739 e8740 e8741 b8742 b8743 b8744 b8745 b8746 b8747 b8748 b8749 d8686 d8702 d8718 g1 g0 d8665
    omega
  have d8750 : (x (-3) 4).toNat = 1 := by
    have r8751 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8752 := hb (x (-3) 4)
    have b8753 := hb (x 1 11)
    have b8754 := hb (x 0 1 && x 0 12)
    have b8755 := hb (x (-1) 2 && x (-1) 13)
    have b8756 := hb (x (-2) 3 && x (-2) 14)
    clear * - r8751 b8752 b8753 b8754 b8755 b8756 d8734 g13 g14 g15
    omega
  have d8757 : (x (-3) 12).toNat = 1 := by
    have r8758 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b8759 := hb (x (-3) 4)
    have b8760 := hb (x (-3) 12)
    clear * - r8758 b8759 b8760 d8750
    omega
  have d8761 : (x (-4) 13).toNat = 0 := by
    have r8762 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8763 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e8764 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b8765 := hb (x (-6) 3)
    have b8766 := hb (x (-5) 2)
    have b8767 := hb (x (-4) 13)
    have b8768 := hb (x (-3) 12)
    clear * - r8762 e8763 e8764 b8765 b8766 b8767 b8768 d8757
    omega
  have d8769 : (x (-4) 5).toNat = 0 := by
    have r8770 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b8771 := hb (x (-4) 5)
    have b8772 := hb (x (-4) 13)
    clear * - r8770 b8771 b8772 d8761
    omega
  have d8773 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r8774 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8775 := hb (x (-4) 5)
    have b8776 := hb (x 1 10)
    have b8777 := hb (x 0 1 && x 0 11)
    have b8778 := hb (x (-1) 2 && x (-1) 12)
    have b8779 := hb (x (-2) 3 && x (-2) 13)
    have b8780 := hb (x (-3) 4 && x (-3) 14)
    clear * - r8774 b8775 b8776 b8777 b8778 b8779 b8780 g4 g10 g11 g12 d8769
    omega
  have d8781 : (x (-3) 14).toNat = 1 := by
    have r8782 := hand2 (x (-3) 4) (x (-3) 14)
    have b8783 := hb (x (-3) 14)
    have b8784 := hb (x (-3) 4 && x (-3) 14)
    clear * - r8782 b8783 b8784 d8773
    omega
  have d8785 : (x (-4) 1).toNat = 0 := by
    have r8786 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8787 := hb (x (-4) 1)
    have b8788 := hb (x (-3) 14)
    clear * - r8786 b8787 b8788 d8781
    omega
  have d8789 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r8790 := hand1 (x (-4) 1) (x (-4) 14)
    have b8791 := hb (x (-4) 1)
    have b8792 := hb (x (-4) 1 && x (-4) 14)
    clear * - r8790 b8791 b8792 d8785
    omega
  have d8793 : (x (-5) 2).toNat = 1 := by
    have r8794 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8795 := hb (x (-5) 2)
    have b8796 := hb (x (-3) 13)
    have b8797 := hb (x (-4) 1 && x (-4) 14)
    clear * - r8794 b8795 b8796 b8797 d8682 d8789
    omega
  have r8798 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e8799 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
  have e8800 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
  have b8801 := hb (x (-6) 3)
  have b8802 := hb (x (-5) 2)
  have b8803 := hb (x (-4) 13)
  have b8804 := hb (x (-3) 12)
  linarith only [r8798, e8799, e8800, b8801, b8802, b8803, b8804, d8757, d8761, d8793]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b0001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 11).toNat = 0)
    (g1 : (x (-1) 2).toNat = 0)
    (g2 : (x (-1) 10).toNat = 0)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 4).toNat = 0)
    (g5 : (x 0 6).toNat = 0)
    (g6 : (x 0 7).toNat = 1)
    (g7 : (x 0 13).toNat = 1)
    (g8 : (x 1 4).toNat = 0)
    (g9 : (x 1 6).toNat = 0)
    (g10 : (x 1 10).toNat = 0)
    (g11 : (x 1 12).toNat = 0)
    (g12 : (x 3 2).toNat = 0)
    (g13 : (x 3 4).toNat = 0)
    (g14 : (x 3 6).toNat = 0)
    (g15 : (x 3 10).toNat = 0)
    (g16 : (x 3 6 && x 3 10).toNat = 0)
    (g17 : (x 1 8 && x 1 12).toNat = 0)
    (g18 : (x 3 6 && x 3 11).toNat = 0)
    (g19 : (x 3 3 && x 3 12).toNat = 0)
    (g20 : (x 1 5 && x 1 14).toNat = 0)
    (g21 : (x 0 1 && x 0 11).toNat = 0)
    (g22 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g23 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g24 : (x 1 2 && x 1 12).toNat = 0)
    (g25 : (x 0 3 && x 0 13).toNat = 0)
    (g26 : (x 3 4 && x 3 14).toNat = 0)
    (g27 : (x 0 1 && x 0 12).toNat = 0)
    (g28 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g29 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g30 : (x 3 1 && x 3 12).toNat = 0)
    (g31 : (x 1 3 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d8806 : (x 7 8).toNat = 0 := by
    have r8807 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8808 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8809 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8810 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8811 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8812 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8813 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8814 := hb (x 0 7)
    have b8815 := hb (x 1 6)
    have b8816 := hb (x 2 5)
    have b8817 := hb (x 3 4)
    have b8818 := hb (x 4 11)
    have b8819 := hb (x 5 10)
    have b8820 := hb (x 6 9)
    have b8821 := hb (x 7 8)
    clear * - r8807 e8808 e8809 e8810 e8811 e8812 e8813 b8814 b8815 b8816 b8817 b8818 b8819 b8820 b8821 g13 g9 g6
    omega
  have d8822 : (x 6 9).toNat = 0 := by
    have r8823 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8824 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8825 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8826 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8827 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8828 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8829 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8830 := hb (x 0 7)
    have b8831 := hb (x 1 6)
    have b8832 := hb (x 2 5)
    have b8833 := hb (x 3 4)
    have b8834 := hb (x 4 11)
    have b8835 := hb (x 5 10)
    have b8836 := hb (x 6 9)
    have b8837 := hb (x 7 8)
    clear * - r8823 e8824 e8825 e8826 e8827 e8828 e8829 b8830 b8831 b8832 b8833 b8834 b8835 b8836 b8837 d8806 g13 g9 g6
    omega
  have d8838 : (x 5 10).toNat = 0 := by
    have r8839 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8840 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8841 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8842 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8843 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8844 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8845 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8846 := hb (x 0 7)
    have b8847 := hb (x 1 6)
    have b8848 := hb (x 2 5)
    have b8849 := hb (x 3 4)
    have b8850 := hb (x 4 11)
    have b8851 := hb (x 5 10)
    have b8852 := hb (x 6 9)
    have b8853 := hb (x 7 8)
    clear * - r8839 e8840 e8841 e8842 e8843 e8844 e8845 b8846 b8847 b8848 b8849 b8850 b8851 b8852 b8853 d8806 d8822 g13 g9 g6
    omega
  have d8854 : (x 5 1 && x 5 10).toNat = 0 := by
    have r8855 := hand2 (x 5 1) (x 5 10)
    have b8856 := hb (x 5 10)
    have b8857 := hb (x 5 1 && x 5 10)
    clear * - r8855 b8856 b8857 d8838
    omega
  have d8858 : (x 4 11).toNat = 0 := by
    have r8859 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8860 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e8861 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e8862 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e8863 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e8864 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e8865 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b8866 := hb (x 0 7)
    have b8867 := hb (x 1 6)
    have b8868 := hb (x 2 5)
    have b8869 := hb (x 3 4)
    have b8870 := hb (x 4 11)
    have b8871 := hb (x 5 10)
    have b8872 := hb (x 6 9)
    have b8873 := hb (x 7 8)
    clear * - r8859 e8860 e8861 e8862 e8863 e8864 e8865 b8866 b8867 b8868 b8869 b8870 b8871 b8872 b8873 d8806 d8822 d8838 g13 g9 g6
    omega
  have d8874 : (x 4 2 && x 4 11).toNat = 0 := by
    have r8875 := hand2 (x 4 2) (x 4 11)
    have b8876 := hb (x 4 11)
    have b8877 := hb (x 4 2 && x 4 11)
    clear * - r8875 b8876 b8877 d8858
    omega
  have d8878 : (x 2 4 && x 2 13).toNat = 1 := by
    have r8879 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8880 := hb (x 0 6)
    have b8881 := hb (x 6 9)
    have b8882 := hb (x 5 1 && x 5 10)
    have b8883 := hb (x 4 2 && x 4 11)
    have b8884 := hb (x 3 3 && x 3 12)
    have b8885 := hb (x 2 4 && x 2 13)
    have b8886 := hb (x 1 5 && x 1 14)
    clear * - r8879 b8880 b8881 b8882 b8883 b8884 b8885 b8886 d8822 d8854 d8874 g19 g20 g5
    omega
  have d8887 : (x 2 4).toNat = 1 := by
    have r8888 := hand1 (x 2 4) (x 2 13)
    have b8889 := hb (x 2 4)
    have b8890 := hb (x 2 4 && x 2 13)
    clear * - r8888 b8889 b8890 d8878
    omega
  have d8891 : (x 2 12).toNat = 1 := by
    have r8892 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b8893 := hb (x 2 4)
    have b8894 := hb (x 2 12)
    clear * - r8892 b8893 b8894 d8887
    omega
  have d8895 : (x 1 13).toNat = 0 := by
    have r8896 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8897 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e8898 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b8899 := hb (x (-1) 3)
    have b8900 := hb (x 0 2)
    have b8901 := hb (x 1 13)
    have b8902 := hb (x 2 12)
    clear * - r8896 e8897 e8898 b8899 b8900 b8901 b8902 d8891 g3
    omega
  have d8903 : (x 1 8 && x 1 13).toNat = 0 := by
    have r8904 := hand2 (x 1 8) (x 1 13)
    have b8905 := hb (x 1 13)
    have b8906 := hb (x 1 8 && x 1 13)
    clear * - r8904 b8905 b8906 d8895
    omega
  have d8907 : (x 1 5).toNat = 0 := by
    have r8908 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b8909 := hb (x 1 5)
    have b8910 := hb (x 1 13)
    clear * - r8908 b8909 b8910 d8895
    omega
  have d8911 : (x 0 1 && x 0 14).toNat = 1 := by
    have r8912 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8913 := hb (x (-1) 2)
    have b8914 := hb (x 1 13)
    have b8915 := hb (x 0 1 && x 0 14)
    clear * - r8912 b8913 b8914 b8915 d8895 g1
    omega
  have d8916 : (x 0 14).toNat = 1 := by
    have r8917 := hand2 (x 0 1) (x 0 14)
    have b8918 := hb (x 0 14)
    have b8919 := hb (x 0 1 && x 0 14)
    clear * - r8917 b8918 b8919 d8911
    omega
  have d8920 : (x (-1) 1).toNat = 0 := by
    have r8921 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8922 := hb (x (-1) 1)
    have b8923 := hb (x 0 14)
    clear * - r8921 b8922 b8923 d8916
    omega
  have d8924 : (x (-1) 13).toNat = 0 := by
    have r8925 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b8926 := hb (x (-1) 1)
    have b8927 := hb (x (-1) 13)
    clear * - r8925 b8926 b8927 d8920
    omega
  have d8928 : (x 2 2 && x 2 13).toNat = 1 := by
    have r8929 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8930 := hb (x 0 4)
    have b8931 := hb (x 4 11)
    have b8932 := hb (x 3 1 && x 3 12)
    have b8933 := hb (x 2 2 && x 2 13)
    have b8934 := hb (x 1 3 && x 1 14)
    clear * - r8929 b8930 b8931 b8932 b8933 b8934 d8858 g30 g31 g4
    omega
  have d8935 : (x 2 2).toNat = 1 := by
    have r8936 := hand1 (x 2 2) (x 2 13)
    have b8937 := hb (x 2 2)
    have b8938 := hb (x 2 2 && x 2 13)
    clear * - r8936 b8937 b8938 d8928
    omega
  have d8939 : (x 4 12).toNat = 0 := by
    have r8940 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8941 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8942 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8943 := hb (x 1 3)
    have b8944 := hb (x 2 2)
    have b8945 := hb (x 3 13)
    have b8946 := hb (x 4 12)
    clear * - r8940 e8941 e8942 b8943 b8944 b8945 b8946 d8935
    omega
  have d8947 : (x 3 13).toNat = 0 := by
    have r8948 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8949 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8950 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8951 := hb (x 1 3)
    have b8952 := hb (x 2 2)
    have b8953 := hb (x 3 13)
    have b8954 := hb (x 4 12)
    clear * - r8948 e8949 e8950 b8951 b8952 b8953 b8954 d8939 d8935
    omega
  have d8955 : (x 1 3).toNat = 0 := by
    have r8956 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8957 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e8958 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b8959 := hb (x 1 3)
    have b8960 := hb (x 2 2)
    have b8961 := hb (x 3 13)
    have b8962 := hb (x 4 12)
    clear * - r8956 e8957 e8958 b8959 b8960 b8961 b8962 d8939 d8947 d8935
    omega
  have d8963 : (x 1 11).toNat = 0 := by
    have r8964 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b8965 := hb (x 1 3)
    have b8966 := hb (x 1 11)
    clear * - r8964 b8965 b8966 d8955
    omega
  have d8967 : (x (-3) 4).toNat = 1 := by
    have r8968 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8969 := hb (x (-3) 4)
    have b8970 := hb (x 1 11)
    have b8971 := hb (x 0 1 && x 0 12)
    have b8972 := hb (x (-1) 2 && x (-1) 13)
    have b8973 := hb (x (-2) 3 && x (-2) 14)
    clear * - r8968 b8969 b8970 b8971 b8972 b8973 d8963 g27 g28 g29
    omega
  have d8974 : (x (-3) 12).toNat = 1 := by
    have r8975 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b8976 := hb (x (-3) 4)
    have b8977 := hb (x (-3) 12)
    clear * - r8975 b8976 b8977 d8967
    omega
  have d8978 : (x (-4) 13).toNat = 0 := by
    have r8979 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8980 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e8981 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b8982 := hb (x (-6) 3)
    have b8983 := hb (x (-5) 2)
    have b8984 := hb (x (-4) 13)
    have b8985 := hb (x (-3) 12)
    clear * - r8979 e8980 e8981 b8982 b8983 b8984 b8985 d8974
    omega
  have d8986 : (x (-4) 5).toNat = 0 := by
    have r8987 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b8988 := hb (x (-4) 5)
    have b8989 := hb (x (-4) 13)
    clear * - r8987 b8988 b8989 d8978
    omega
  have d8990 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r8991 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b8992 := hb (x (-4) 5)
    have b8993 := hb (x 1 10)
    have b8994 := hb (x 0 1 && x 0 11)
    have b8995 := hb (x (-1) 2 && x (-1) 12)
    have b8996 := hb (x (-2) 3 && x (-2) 13)
    have b8997 := hb (x (-3) 4 && x (-3) 14)
    clear * - r8991 b8992 b8993 b8994 b8995 b8996 b8997 g10 g21 g22 g23 d8986
    omega
  have d8998 : (x (-3) 14).toNat = 1 := by
    have r8999 := hand2 (x (-3) 4) (x (-3) 14)
    have b9000 := hb (x (-3) 14)
    have b9001 := hb (x (-3) 4 && x (-3) 14)
    clear * - r8999 b9000 b9001 d8990
    omega
  have d9002 : (x (-4) 1).toNat = 0 := by
    have r9003 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9004 := hb (x (-4) 1)
    have b9005 := hb (x (-3) 14)
    clear * - r9003 b9004 b9005 d8998
    omega
  have d9006 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r9007 := hand1 (x (-4) 1) (x (-4) 14)
    have b9008 := hb (x (-4) 1)
    have b9009 := hb (x (-4) 1 && x (-4) 14)
    clear * - r9007 b9008 b9009 d9002
    omega
  have d9010 : (x (-5) 2).toNat = 0 := by
    have r9011 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9012 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e9013 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b9014 := hb (x (-6) 3)
    have b9015 := hb (x (-5) 2)
    have b9016 := hb (x (-4) 13)
    have b9017 := hb (x (-3) 12)
    clear * - r9011 e9012 e9013 b9014 b9015 b9016 b9017 d8974 d8978
    omega
  have d9018 : (x (-3) 13).toNat = 1 := by
    have r9019 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9020 := hb (x (-5) 2)
    have b9021 := hb (x (-3) 13)
    have b9022 := hb (x (-4) 1 && x (-4) 14)
    clear * - r9019 b9020 b9021 b9022 d9006 d9010
    omega
  have d9023 : (x (-3) 1).toNat = 1 := by
    have r9024 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b9025 := hb (x (-3) 1)
    have b9026 := hb (x (-3) 13)
    clear * - r9024 b9025 b9026 d9018
    omega
  have d9027 : (x (-2) 14).toNat = 0 := by
    have r9028 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9029 := hb (x (-3) 1)
    have b9030 := hb (x (-2) 14)
    clear * - r9028 b9029 b9030 d9023
    omega
  have d9031 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r9032 := hand2 (x (-2) 1) (x (-2) 14)
    have b9033 := hb (x (-2) 14)
    have b9034 := hb (x (-2) 1 && x (-2) 14)
    clear * - r9032 b9033 b9034 d9027
    omega
  have d9035 : (x (-3) 2).toNat = 1 := by
    have r9036 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9037 := hb (x (-3) 2)
    have b9038 := hb (x (-1) 13)
    have b9039 := hb (x (-2) 1 && x (-2) 14)
    clear * - r9036 b9037 b9038 b9039 d8924 d9031
    omega
  have d9040 : (x (-1) 12).toNat = 0 := by
    have r9041 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9042 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e9043 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b9044 := hb (x (-4) 3)
    have b9045 := hb (x (-3) 2)
    have b9046 := hb (x (-2) 13)
    have b9047 := hb (x (-1) 12)
    clear * - r9041 e9042 e9043 b9044 b9045 b9046 b9047 d9035
    omega
  have d9048 : (x (-1) 4).toNat = 0 := by
    have r9049 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b9050 := hb (x (-1) 4)
    have b9051 := hb (x (-1) 12)
    clear * - r9049 b9050 b9051 d9040
    omega
  have d9052 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
    have r9053 := hand1 (x (-1) 4) (x (-1) 14)
    have b9054 := hb (x (-1) 4)
    have b9055 := hb (x (-1) 4 && x (-1) 14)
    clear * - r9053 b9054 b9055 d9048
    omega
  have d9056 : (x (-2) 13).toNat = 0 := by
    have r9057 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9058 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e9059 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b9060 := hb (x (-4) 3)
    have b9061 := hb (x (-3) 2)
    have b9062 := hb (x (-2) 13)
    have b9063 := hb (x (-1) 12)
    clear * - r9057 e9058 e9059 b9060 b9061 b9062 b9063 d9040 d9035
    omega
  have d9064 : (x (-2) 5).toNat = 0 := by
    have r9065 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b9066 := hb (x (-2) 5)
    have b9067 := hb (x (-2) 13)
    clear * - r9065 b9066 b9067 d9056
    omega
  have d9068 : (x 2 1 && x 2 11).toNat = 1 := by
    have r9069 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9070 := hb (x (-2) 5)
    have b9071 := hb (x 3 10)
    have b9072 := hb (x 2 1 && x 2 11)
    have b9073 := hb (x 1 2 && x 1 12)
    have b9074 := hb (x 0 3 && x 0 13)
    have b9075 := hb (x (-1) 4 && x (-1) 14)
    clear * - r9069 b9070 b9071 b9072 b9073 b9074 b9075 g15 g24 g25 d9052 d9064
    omega
  have d9076 : (x 2 11).toNat = 1 := by
    have r9077 := hand2 (x 2 1) (x 2 11)
    have b9078 := hb (x 2 11)
    have b9079 := hb (x 2 1 && x 2 11)
    clear * - r9077 b9078 b9079 d9068
    omega
  have d9080 : (x 2 3).toNat = 1 := by
    have r9081 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b9082 := hb (x 2 3)
    have b9083 := hb (x 2 11)
    clear * - r9081 b9082 b9083 d9076
    omega
  have d9084 : (x 5 12).toNat = 0 := by
    have r9085 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9086 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e9087 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b9088 := hb (x 2 3)
    have b9089 := hb (x 3 2)
    have b9090 := hb (x 4 13)
    have b9091 := hb (x 5 12)
    clear * - r9085 e9086 e9087 b9088 b9089 b9090 b9091 g12 d9080
    omega
  have d9092 : (x 5 2 && x 5 12).toNat = 0 := by
    have r9093 := hand2 (x 5 2) (x 5 12)
    have b9094 := hb (x 5 12)
    have b9095 := hb (x 5 2 && x 5 12)
    clear * - r9093 b9094 b9095 d9084
    omega
  have d9096 : (x 5 4).toNat = 0 := by
    have r9097 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b9098 := hb (x 5 4)
    have b9099 := hb (x 5 12)
    clear * - r9097 b9098 b9099 d9084
    omega
  have d9100 : (x 5 4 && x 5 9).toNat = 0 := by
    have r9101 := hand1 (x 5 4) (x 5 9)
    have b9102 := hb (x 5 4)
    have b9103 := hb (x 5 4 && x 5 9)
    clear * - r9101 b9102 b9103 d9096
    omega
  have d9104 : (x 5 4 && x 5 8).toNat = 0 := by
    have r9105 := hand1 (x 5 4) (x 5 8)
    have b9106 := hb (x 5 4)
    have b9107 := hb (x 5 4 && x 5 8)
    clear * - r9105 b9106 b9107 d9096
    omega
  have d9108 : (x 4 13).toNat = 0 := by
    have r9109 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9110 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e9111 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b9112 := hb (x 2 3)
    have b9113 := hb (x 3 2)
    have b9114 := hb (x 4 13)
    have b9115 := hb (x 5 12)
    clear * - r9109 e9110 e9111 b9112 b9113 b9114 b9115 d9084 g12 d9080
    omega
  have d9116 : (x 4 3 && x 4 13).toNat = 0 := by
    have r9117 := hand2 (x 4 3) (x 4 13)
    have b9118 := hb (x 4 13)
    have b9119 := hb (x 4 3 && x 4 13)
    clear * - r9117 b9118 b9119 d9108
    omega
  have d9120 : (x 4 5).toNat = 0 := by
    have r9121 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b9122 := hb (x 4 5)
    have b9123 := hb (x 4 13)
    clear * - r9121 b9122 b9123 d9108
    omega
  have d9124 : (x 4 5 && x 4 10).toNat = 0 := by
    have r9125 := hand1 (x 4 5) (x 4 10)
    have b9126 := hb (x 4 5)
    have b9127 := hb (x 4 5 && x 4 10)
    clear * - r9125 b9126 b9127 d9120
    omega
  have d9128 : (x 4 5 && x 4 9).toNat = 0 := by
    have r9129 := hand1 (x 4 5) (x 4 9)
    have b9130 := hb (x 4 5)
    have b9131 := hb (x 4 5 && x 4 9)
    clear * - r9129 b9130 b9131 d9120
    omega
  have d9132 : (x 2 5).toNat = 0 := by
    have r9133 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9134 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e9135 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e9136 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e9137 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e9138 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e9139 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b9140 := hb (x 0 7)
    have b9141 := hb (x 1 6)
    have b9142 := hb (x 2 5)
    have b9143 := hb (x 3 4)
    have b9144 := hb (x 4 11)
    have b9145 := hb (x 5 10)
    have b9146 := hb (x 6 9)
    have b9147 := hb (x 7 8)
    clear * - r9133 e9134 e9135 e9136 e9137 e9138 e9139 b9140 b9141 b9142 b9143 b9144 b9145 b9146 b9147 d8806 d8822 d8838 d8858 g13 g9 g6
    omega
  have d9148 : (x 6 8).toNat = 0 := by
    have r9149 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9150 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9151 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9152 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9153 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9154 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9155 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9156 := hb (x (-1) 7)
    have b9157 := hb (x 0 6)
    have b9158 := hb (x 1 5)
    have b9159 := hb (x 2 4)
    have b9160 := hb (x 3 11)
    have b9161 := hb (x 4 10)
    have b9162 := hb (x 5 9)
    have b9163 := hb (x 6 8)
    clear * - r9149 e9150 e9151 e9152 e9153 e9154 e9155 b9156 b9157 b9158 b9159 b9160 b9161 b9162 b9163 d8887 d8907 g5
    omega
  have d9164 : (x 6 3 && x 6 8).toNat = 0 := by
    have r9165 := hand2 (x 6 3) (x 6 8)
    have b9166 := hb (x 6 8)
    have b9167 := hb (x 6 3 && x 6 8)
    clear * - r9165 b9166 b9167 d9148
    omega
  have d9168 : (x 5 9).toNat = 0 := by
    have r9169 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9170 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9171 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9172 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9173 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9174 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9175 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9176 := hb (x (-1) 7)
    have b9177 := hb (x 0 6)
    have b9178 := hb (x 1 5)
    have b9179 := hb (x 2 4)
    have b9180 := hb (x 3 11)
    have b9181 := hb (x 4 10)
    have b9182 := hb (x 5 9)
    have b9183 := hb (x 6 8)
    clear * - r9169 e9170 e9171 e9172 e9173 e9174 e9175 b9176 b9177 b9178 b9179 b9180 b9181 b9182 b9183 d9148 d8887 d8907 g5
    omega
  have d9184 : (x 4 10).toNat = 0 := by
    have r9185 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9186 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9187 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9188 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9189 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9190 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9191 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9192 := hb (x (-1) 7)
    have b9193 := hb (x 0 6)
    have b9194 := hb (x 1 5)
    have b9195 := hb (x 2 4)
    have b9196 := hb (x 3 11)
    have b9197 := hb (x 4 10)
    have b9198 := hb (x 5 9)
    have b9199 := hb (x 6 8)
    clear * - r9185 e9186 e9187 e9188 e9189 e9190 e9191 b9192 b9193 b9194 b9195 b9196 b9197 b9198 b9199 d9148 d9168 d8887 d8907 g5
    omega
  have d9200 : (x 3 11).toNat = 0 := by
    have r9201 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9202 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9203 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9204 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9205 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9206 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9207 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9208 := hb (x (-1) 7)
    have b9209 := hb (x 0 6)
    have b9210 := hb (x 1 5)
    have b9211 := hb (x 2 4)
    have b9212 := hb (x 3 11)
    have b9213 := hb (x 4 10)
    have b9214 := hb (x 5 9)
    have b9215 := hb (x 6 8)
    clear * - r9201 e9202 e9203 e9204 e9205 e9206 e9207 b9208 b9209 b9210 b9211 b9212 b9213 b9214 b9215 d9148 d9168 d9184 d8887 d8907 g5
    omega
  have d9216 : (x 5 8).toNat = 0 := by
    have r9217 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9218 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e9219 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e9220 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e9221 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e9222 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e9223 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b9224 := hb (x (-2) 7)
    have b9225 := hb (x (-1) 6)
    have b9226 := hb (x 0 5)
    have b9227 := hb (x 1 4)
    have b9228 := hb (x 2 11)
    have b9229 := hb (x 3 10)
    have b9230 := hb (x 4 9)
    have b9231 := hb (x 5 8)
    clear * - r9217 e9218 e9219 e9220 e9221 e9222 e9223 b9224 b9225 b9226 b9227 b9228 b9229 b9230 b9231 g15 d9076 g8
    omega
  have d9232 : (x 4 9).toNat = 0 := by
    have r9233 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9234 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e9235 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e9236 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e9237 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e9238 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e9239 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b9240 := hb (x (-2) 7)
    have b9241 := hb (x (-1) 6)
    have b9242 := hb (x 0 5)
    have b9243 := hb (x 1 4)
    have b9244 := hb (x 2 11)
    have b9245 := hb (x 3 10)
    have b9246 := hb (x 4 9)
    have b9247 := hb (x 5 8)
    clear * - r9233 e9234 e9235 e9236 e9237 e9238 e9239 b9240 b9241 b9242 b9243 b9244 b9245 b9246 b9247 d9216 g15 d9076 g8
    omega
  have d9248 : (x 1 8).toNat = 0 := by
    have r9249 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9250 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e9251 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e9252 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e9253 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e9254 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e9255 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b9256 := hb (x (-6) 7)
    have b9257 := hb (x (-5) 6)
    have b9258 := hb (x (-4) 5)
    have b9259 := hb (x (-3) 4)
    have b9260 := hb (x (-2) 11)
    have b9261 := hb (x (-1) 10)
    have b9262 := hb (x 0 9)
    have b9263 := hb (x 1 8)
    clear * - r9249 e9250 e9251 e9252 e9253 e9254 e9255 b9256 b9257 b9258 b9259 b9260 b9261 b9262 b9263 g2 g0 d8967 d8986
    omega
  have d9264 : (x 0 9).toNat = 0 := by
    have r9265 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9266 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e9267 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e9268 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e9269 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e9270 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e9271 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b9272 := hb (x (-6) 7)
    have b9273 := hb (x (-5) 6)
    have b9274 := hb (x (-4) 5)
    have b9275 := hb (x (-3) 4)
    have b9276 := hb (x (-2) 11)
    have b9277 := hb (x (-1) 10)
    have b9278 := hb (x 0 9)
    have b9279 := hb (x 1 8)
    clear * - r9265 e9266 e9267 e9268 e9269 e9270 e9271 b9272 b9273 b9274 b9275 b9276 b9277 b9278 b9279 d9248 g2 g0 d8967 d8986
    omega
  have d9280 : (x 0 9 && x 0 14).toNat = 0 := by
    have r9281 := hand1 (x 0 9) (x 0 14)
    have b9282 := hb (x 0 9)
    have b9283 := hb (x 0 9 && x 0 14)
    clear * - r9281 b9282 b9283 d9264
    omega
  have d9284 : (x 0 9 && x 0 13).toNat = 0 := by
    have r9285 := hand1 (x 0 9) (x 0 13)
    have b9286 := hb (x 0 9)
    have b9287 := hb (x 0 9 && x 0 13)
    clear * - r9285 b9286 b9287 d9264
    omega
  have r9288 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9289 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9290 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9291 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
  have e9292 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
  have e9293 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
  have e9294 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
  have e9295 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
  have e9296 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
  have r9297 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9298 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
  have e9299 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
  have r9300 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9301 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9302 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9303 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
  have r9304 := hand2 (x 7 2) (x 7 6)
  have r9305 := hand2 (x 6 3) (x 6 7)
  have r9306 := hand1 (x 2 7) (x 2 11)
  have r9307 := hand2 (x 8 1) (x 8 6)
  have r9308 := hand2 (x 7 2) (x 7 7)
  have r9309 := hand1 (x 2 7) (x 2 12)
  have r9310 := hand2 (x 6 1) (x 6 11)
  have r9311 := hand1 (x 12 1) (x 12 14)
  linarith only [r9288, r9289, r9290, e9291, e9292, e9293, e9294, e9295, e9296, r9297, e9298, e9299, r9300, r9301, r9302, r9303, r9304, r9305, r9306, r9307, r9308, r9309, r9310, r9311, g0, g2, g7, d8916, g11, d8895, d9132, d9076, d8891, g14, g15, d9200, d9120, d9232, d9184, d9096, d9216, d9168, d9148, d9104, d9128, g16, g17, d9284, d9164, d9100, d9124, g18, d8903, d9280, d9092, d9116, g26]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 6).toNat = 1)
    (g1 : (x 0 13).toNat = 1)
    (g2 : (x 1 10).toNat = 0)
    (g3 : (x 1 12).toNat = 0)
    (g4 : (x 3 10).toNat = 0)
    (g5 : (x 0 8 && x 0 14).toNat = 0)
    (g6 : (x 0 1 && x 0 11).toNat = 0)
    (g7 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g8 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g9 : (x 1 2 && x 1 12).toNat = 0)
    (g10 : (x 0 3 && x 0 13).toNat = 0)
    (g11 : (x 0 4 && x 0 14).toNat = 0)
    (g12 : (x 0 1 && x 0 12).toNat = 0)
    (g13 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g14 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g15 : (x 1 2 && x 1 13).toNat = 0)
    (g16 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d9375 : (x 0 14).toNat = 1 := by
    have r9376 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
    have b9377 := hb (x 0 6)
    have b9378 := hb (x 0 14)
    clear * - r9376 b9377 b9378 g0
    omega
  have d9379 : (x (-1) 1).toNat = 0 := by
    have r9380 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b9381 := hb (x (-1) 1)
    have b9382 := hb (x 0 14)
    clear * - r9380 b9381 b9382 d9375
    omega
  have d9383 : (x (-1) 13).toNat = 0 := by
    have r9384 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b9385 := hb (x (-1) 1)
    have b9386 := hb (x (-1) 13)
    clear * - r9384 b9385 b9386 d9379
    omega
  have d9387 : (x (-1) 5).toNat = 0 := by
    have r9388 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b9389 := hb (x (-1) 5)
    have b9390 := hb (x (-1) 13)
    clear * - r9388 b9389 b9390 d9383
    omega
  have d9391 : (x (-1) 9).toNat = 0 := by
    have r9392 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b9393 := hb (x (-1) 1)
    have b9394 := hb (x (-1) 9)
    clear * - r9392 b9393 b9394 d9379
    omega
  have d9395 : (x 6 8).toNat = 0 := by
    have r9396 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9397 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9398 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9399 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9400 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9401 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9402 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9403 := hb (x (-1) 7)
    have b9404 := hb (x 0 6)
    have b9405 := hb (x 1 5)
    have b9406 := hb (x 2 4)
    have b9407 := hb (x 3 11)
    have b9408 := hb (x 4 10)
    have b9409 := hb (x 5 9)
    have b9410 := hb (x 6 8)
    clear * - r9396 e9397 e9398 e9399 e9400 e9401 e9402 b9403 b9404 b9405 b9406 b9407 b9408 b9409 b9410 g0
    omega
  have d9411 : (x 6 2 && x 6 8).toNat = 0 := by
    have r9412 := hand2 (x 6 2) (x 6 8)
    have b9413 := hb (x 6 8)
    have b9414 := hb (x 6 2 && x 6 8)
    clear * - r9412 b9413 b9414 d9395
    omega
  have d9415 : (x 5 9).toNat = 0 := by
    have r9416 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9417 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9418 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9419 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9420 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9421 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9422 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9423 := hb (x (-1) 7)
    have b9424 := hb (x 0 6)
    have b9425 := hb (x 1 5)
    have b9426 := hb (x 2 4)
    have b9427 := hb (x 3 11)
    have b9428 := hb (x 4 10)
    have b9429 := hb (x 5 9)
    have b9430 := hb (x 6 8)
    clear * - r9416 e9417 e9418 e9419 e9420 e9421 e9422 b9423 b9424 b9425 b9426 b9427 b9428 b9429 b9430 d9395 g0
    omega
  have d9431 : (x 5 3 && x 5 9).toNat = 0 := by
    have r9432 := hand2 (x 5 3) (x 5 9)
    have b9433 := hb (x 5 9)
    have b9434 := hb (x 5 3 && x 5 9)
    clear * - r9432 b9433 b9434 d9415
    omega
  have d9435 : (x 4 10).toNat = 0 := by
    have r9436 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9437 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9438 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9439 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9440 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9441 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9442 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9443 := hb (x (-1) 7)
    have b9444 := hb (x 0 6)
    have b9445 := hb (x 1 5)
    have b9446 := hb (x 2 4)
    have b9447 := hb (x 3 11)
    have b9448 := hb (x 4 10)
    have b9449 := hb (x 5 9)
    have b9450 := hb (x 6 8)
    clear * - r9436 e9437 e9438 e9439 e9440 e9441 e9442 b9443 b9444 b9445 b9446 b9447 b9448 b9449 b9450 d9395 d9415 g0
    omega
  have d9451 : (x 4 4 && x 4 10).toNat = 0 := by
    have r9452 := hand2 (x 4 4) (x 4 10)
    have b9453 := hb (x 4 10)
    have b9454 := hb (x 4 4 && x 4 10)
    clear * - r9452 b9453 b9454 d9435
    omega
  have d9455 : (x 3 11).toNat = 0 := by
    have r9456 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9457 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9458 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9459 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9460 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9461 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9462 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9463 := hb (x (-1) 7)
    have b9464 := hb (x 0 6)
    have b9465 := hb (x 1 5)
    have b9466 := hb (x 2 4)
    have b9467 := hb (x 3 11)
    have b9468 := hb (x 4 10)
    have b9469 := hb (x 5 9)
    have b9470 := hb (x 6 8)
    clear * - r9456 e9457 e9458 e9459 e9460 e9461 e9462 b9463 b9464 b9465 b9466 b9467 b9468 b9469 b9470 d9395 d9415 d9435 g0
    omega
  have d9471 : (x 3 1 && x 3 11).toNat = 0 := by
    have r9472 := hand2 (x 3 1) (x 3 11)
    have b9473 := hb (x 3 11)
    have b9474 := hb (x 3 1 && x 3 11)
    clear * - r9472 b9473 b9474 d9455
    omega
  have d9475 : (x 3 5 && x 3 11).toNat = 0 := by
    have r9476 := hand2 (x 3 5) (x 3 11)
    have b9477 := hb (x 3 11)
    have b9478 := hb (x 3 5 && x 3 11)
    clear * - r9476 b9477 b9478 d9455
    omega
  have d9479 : (x 2 4).toNat = 0 := by
    have r9480 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9481 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9482 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9483 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9484 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9485 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9486 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9487 := hb (x (-1) 7)
    have b9488 := hb (x 0 6)
    have b9489 := hb (x 1 5)
    have b9490 := hb (x 2 4)
    have b9491 := hb (x 3 11)
    have b9492 := hb (x 4 10)
    have b9493 := hb (x 5 9)
    have b9494 := hb (x 6 8)
    clear * - r9480 e9481 e9482 e9483 e9484 e9485 e9486 b9487 b9488 b9489 b9490 b9491 b9492 b9493 b9494 d9395 d9415 d9435 d9455 g0
    omega
  have d9495 : (x 2 4 && x 2 14).toNat = 0 := by
    have r9496 := hand1 (x 2 4) (x 2 14)
    have b9497 := hb (x 2 4)
    have b9498 := hb (x 2 4 && x 2 14)
    clear * - r9496 b9497 b9498 d9479
    omega
  have d9499 : (x 1 5).toNat = 0 := by
    have r9500 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e9501 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e9502 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e9503 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e9504 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e9505 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e9506 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b9507 := hb (x (-1) 7)
    have b9508 := hb (x 0 6)
    have b9509 := hb (x 1 5)
    have b9510 := hb (x 2 4)
    have b9511 := hb (x 3 11)
    have b9512 := hb (x 4 10)
    have b9513 := hb (x 5 9)
    have b9514 := hb (x 6 8)
    clear * - r9500 e9501 e9502 e9503 e9504 e9505 e9506 b9507 b9508 b9509 b9510 b9511 b9512 b9513 b9514 d9395 d9415 d9435 d9455 d9479 g0
    omega
  have r9515 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9516 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9517 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9518 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
  have e9519 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
  have e9520 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
  have e9521 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
  have e9522 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
  have e9523 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
  have r9524 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9525 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
  have e9526 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
  have e9527 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
  have e9528 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
  have e9529 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
  have e9530 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
  have r9531 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9532 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
  have e9533 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
  have r9534 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9535 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
  have e9536 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
  have r9537 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e9538 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
  have e9539 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
  have r9540 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9541 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9542 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9543 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9544 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9545 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9546 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9547 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9548 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9549 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9550 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9551 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9552 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r9553 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
  have r9554 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
  have r9555 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
  have r9556 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
  have r9557 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
  have r9558 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
  have r9559 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
  have r9560 := hand2 (x 7 1) (x 7 7)
  have r9561 := hand1 (x 2 6) (x 2 12)
  have r9562 := hand1 (x 1 7) (x 1 13)
  have r9563 := hand2 (x 12 1) (x 12 10)
  have r9564 := hand2 (x 11 2) (x 11 11)
  have r9565 := hand1 (x 10 3) (x 10 12)
  have r9566 := hand1 (x 9 4) (x 9 13)
  have r9567 := hand1 (x 8 5) (x 8 14)
  have r9568 := hand2 (x (-3) 4) (x (-3) 14)
  have r9569 := hand2 (x 2 1) (x 2 11)
  have r9570 := hand2 (x (-1) 4) (x (-1) 14)
  have r9571 := hand1 (x 2 2) (x 2 12)
  have r9572 := hand1 (x 1 3) (x 1 13)
  have r9573 := hand2 (x 1 3) (x 1 13)
  have r9574 := hand2 (x 5 1) (x 5 11)
  have r9575 := hand2 (x 4 2) (x 4 12)
  have r9576 := hand2 (x 3 3) (x 3 13)
  have r9577 := hand2 (x 2 1) (x 2 12)
  have r9578 := hand1 (x (-4) 1) (x (-4) 14)
  have r9579 := hand2 (x (-2) 1) (x (-2) 14)
  have r9580 := hand1 (x 12 1) (x 12 14)
  linarith only [r9515, r9516, r9517, e9518, e9519, e9520, e9521, e9522, e9523, r9524, e9525, e9526, e9527, e9528, e9529, e9530, r9531, e9532, e9533, r9534, e9535, e9536, r9537, e9538, e9539, r9540, r9541, r9542, r9543, r9544, r9545, r9546, r9547, r9548, r9549, r9550, r9551, r9552, r9553, r9554, r9555, r9556, r9557, r9558, r9559, r9560, r9561, r9562, r9563, r9564, r9565, r9566, r9567, r9568, r9569, r9570, r9571, r9572, r9573, r9574, r9575, r9576, r9577, r9578, r9579, r9580, d9387, d9391, d9383, g1, d9375, d9499, g2, g3, g4, d9455, d9435, d9415, d9395, d9411, d9431, d9451, d9475, g5, g6, g7, g8, g9, g10, d9471, g11, d9495, g12, g13, g14, g15, g16]

theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 6).toNat = 1)
    (g1 : (x 0 13).toNat = 1)
    (g2 : (x 1 10).toNat = 0)
    (g3 : (x 1 12).toNat = 0)
    (g4 : (x 3 10).toNat = 0)
    (g5 : (x 0 8 && x 0 14).toNat = 0)
    (g6 : (x 0 1 && x 0 11).toNat = 0)
    (g7 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g8 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g9 : (x 1 2 && x 1 12).toNat = 0)
    (g10 : (x 0 3 && x 0 13).toNat = 0)
    (g11 : (x 0 4 && x 0 14).toNat = 0)
    (g12 : (x 0 1 && x 0 12).toNat = 0)
    (g13 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g14 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g15 : (x 1 2 && x 1 13).toNat = 0)
    (g16 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16
