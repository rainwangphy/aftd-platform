import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_a1

Topic: combinatorics   Node: 8652f2c6f099

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core: under the layer-free tight-cover constraints for k = 15 and 14 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b1101, cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b111, cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_a0.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b1101 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-1) 10).toNat = 0)
    (g2 : (x 0 3).toNat = 1)
    (g3 : (x 0 8).toNat = 1)
    (g4 : (x 1 2).toNat = 0)
    (g5 : (x 1 4).toNat = 0)
    (g6 : (x 1 6).toNat = 0)
    (g7 : (x 2 1).toNat = 1)
    (g8 : (x 2 5).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 3 5).toNat = 0)
    (g12 : (x 3 9).toNat = 0)
    (g13 : (x 3 13).toNat = 0)
    (g14 : (x 5 2).toNat = 0)
    (g15 : (x 5 6).toNat = 0)
    (g16 : (x 6 5).toNat = 0)
    (g17 : (x 7 4).toNat = 0)
    (g18 : (x 1 2 && x 1 6).toNat = 0)
    (g19 : (x 0 3 && x 0 7).toNat = 0)
    (g20 : (x 5 2 && x 5 6).toNat = 0)
    (g21 : (x 3 4 && x 3 8).toNat = 0)
    (g22 : (x 2 5 && x 2 9).toNat = 0)
    (g23 : (x 1 6 && x 1 10).toNat = 0)
    (g24 : (x 0 7 && x 0 11).toNat = 0)
    (g25 : (x 1 2 && x 1 11).toNat = 0)
    (g26 : (x 0 3 && x 0 12).toNat = 0)
    (g27 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g28 : (x 5 2 && x 5 11).toNat = 0)
    (g29 : (x 3 4 && x 3 13).toNat = 0)
    (g30 : (x 2 5 && x 2 14).toNat = 0)
    (g31 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g32 : (x 0 1 && x 0 12).toNat = 0)
    (g33 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g34 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g35 : (x 3 2 && x 3 13).toNat = 0)
    (g36 : (x 7 1 && x 7 12).toNat = 0)
    (g37 : (x 6 2 && x 6 13).toNat = 0)
    (g38 : (x 5 3 && x 5 14).toNat = 0)
    (g39 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d23063 : (x (-2) 10).toNat = 0 := by
    have r23064 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23065 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e23066 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e23067 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e23068 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e23069 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e23070 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b23071 := hb (x (-7) 7)
    have b23072 := hb (x (-6) 6)
    have b23073 := hb (x (-5) 5)
    have b23074 := hb (x (-4) 4)
    have b23075 := hb (x (-3) 11)
    have b23076 := hb (x (-2) 10)
    have b23077 := hb (x (-1) 9)
    have b23078 := hb (x 0 8)
    clear * - r23064 e23065 e23066 e23067 e23068 e23069 e23070 b23071 b23072 b23073 b23074 b23075 b23076 b23077 b23078 g3 g0
    omega
  have d23079 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r23080 := hand2 (x (-2) 1) (x (-2) 10)
    have b23081 := hb (x (-2) 10)
    have b23082 := hb (x (-2) 1 && x (-2) 10)
    clear * - r23080 b23081 b23082 d23063
    omega
  have d23083 : (x (-3) 11).toNat = 0 := by
    have r23084 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23085 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e23086 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e23087 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e23088 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e23089 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e23090 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b23091 := hb (x (-7) 7)
    have b23092 := hb (x (-6) 6)
    have b23093 := hb (x (-5) 5)
    have b23094 := hb (x (-4) 4)
    have b23095 := hb (x (-3) 11)
    have b23096 := hb (x (-2) 10)
    have b23097 := hb (x (-1) 9)
    have b23098 := hb (x 0 8)
    clear * - r23084 e23085 e23086 e23087 e23088 e23089 e23090 b23091 b23092 b23093 b23094 b23095 b23096 b23097 b23098 g3 g0 d23063
    omega
  have d23099 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r23100 := hand2 (x (-3) 2) (x (-3) 11)
    have b23101 := hb (x (-3) 11)
    have b23102 := hb (x (-3) 2 && x (-3) 11)
    clear * - r23100 b23101 b23102 d23083
    omega
  cases h23103 : x 1 3
  · have f23104 : (x 1 3).toNat = 0 := by rw [h23103]; rfl
    have d23105 : (x 1 11).toNat = 0 := by
      have r23106 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b23107 := hb (x 1 3)
      have b23108 := hb (x 1 11)
      clear * - r23106 b23107 b23108 f23104
      omega
    have d23109 : (x (-3) 4).toNat = 1 := by
      have r23110 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23111 := hb (x (-3) 4)
      have b23112 := hb (x 1 11)
      have b23113 := hb (x 0 1 && x 0 12)
      have b23114 := hb (x (-1) 2 && x (-1) 13)
      have b23115 := hb (x (-2) 3 && x (-2) 14)
      clear * - r23110 b23111 b23112 b23113 b23114 b23115 d23105 g32 g33 g34
      omega
    have d23116 : (x (-3) 12).toNat = 1 := by
      have r23117 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b23118 := hb (x (-3) 4)
      have b23119 := hb (x (-3) 12)
      clear * - r23117 b23118 b23119 d23109
      omega
    have d23120 : (x (-4) 13).toNat = 0 := by
      have r23121 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23122 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e23123 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b23124 := hb (x (-6) 3)
      have b23125 := hb (x (-5) 2)
      have b23126 := hb (x (-4) 13)
      have b23127 := hb (x (-3) 12)
      clear * - r23121 e23122 e23123 b23124 b23125 b23126 b23127 d23116
      omega
    have d23128 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
      have r23129 := hand2 (x (-4) 3) (x (-4) 13)
      have b23130 := hb (x (-4) 13)
      have b23131 := hb (x (-4) 3 && x (-4) 13)
      clear * - r23129 b23130 b23131 d23120
      omega
    have d23132 : (x (-5) 2).toNat = 0 := by
      have r23133 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23134 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e23135 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b23136 := hb (x (-6) 3)
      have b23137 := hb (x (-5) 2)
      have b23138 := hb (x (-4) 13)
      have b23139 := hb (x (-3) 12)
      clear * - r23133 e23134 e23135 b23136 b23137 b23138 b23139 d23116 d23120
      omega
    have d23140 : (x (-5) 10).toNat = 0 := by
      have r23141 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
      have b23142 := hb (x (-5) 2)
      have b23143 := hb (x (-5) 10)
      clear * - r23141 b23142 b23143 d23132
      omega
    have d23144 : (x (-6) 3).toNat = 0 := by
      have r23145 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23146 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e23147 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b23148 := hb (x (-6) 3)
      have b23149 := hb (x (-5) 2)
      have b23150 := hb (x (-4) 13)
      have b23151 := hb (x (-3) 12)
      clear * - r23145 e23146 e23147 b23148 b23149 b23150 b23151 d23116 d23120 d23132
      omega
    have d23152 : (x (-6) 11).toNat = 0 := by
      have r23153 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
      have b23154 := hb (x (-6) 3)
      have b23155 := hb (x (-6) 11)
      clear * - r23153 b23154 b23155 d23144
      omega
    have d23156 : (x (-6) 1 && x (-6) 11).toNat = 0 := by
      have r23157 := hand2 (x (-6) 1) (x (-6) 11)
      have b23158 := hb (x (-6) 11)
      have b23159 := hb (x (-6) 1 && x (-6) 11)
      clear * - r23157 b23158 b23159 d23152
      omega
    have r23160 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r23161 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23162 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e23163 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e23164 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e23165 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e23166 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e23167 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have r23168 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23169 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e23170 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e23171 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e23172 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e23173 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e23174 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have r23175 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23176 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e23177 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e23178 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e23179 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e23180 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e23181 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have r23182 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23183 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e23184 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have r23185 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23186 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e23187 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have r23188 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23189 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e23190 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have r23191 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23192 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
    have e23193 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
    have r23194 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23195 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
    have e23196 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
    have r23197 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r23198 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r23199 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r23200 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r23201 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r23202 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r23203 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
    have r23204 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
    have r23205 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
    have r23206 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
    have r23207 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
    have r23208 := hand1 (x (-1) 4) (x (-1) 8)
    have r23209 := hand2 (x (-2) 5) (x (-2) 9)
    have r23210 := hand2 (x (-3) 6) (x (-3) 10)
    have r23211 := hand2 (x (-4) 7) (x (-4) 11)
    have r23212 := hand1 (x (-5) 8) (x (-5) 12)
    have r23213 := hand1 (x (-6) 9) (x (-6) 13)
    have r23214 := hand2 (x 4 3) (x 4 7)
    have r23215 := hand1 (x (-1) 8) (x (-1) 12)
    have r23216 := hand2 (x (-2) 9) (x (-2) 13)
    have r23217 := hand1 (x (-4) 3) (x (-4) 12)
    have r23218 := hand1 (x (-5) 4) (x (-5) 13)
    have r23219 := hand1 (x (-6) 5) (x (-6) 14)
    have r23220 := hand2 (x 2 1) (x 2 10)
    have r23221 := hand1 (x (-2) 5) (x (-2) 14)
    have r23222 := hand2 (x 6 1) (x 6 10)
    have r23223 := hand2 (x 4 3) (x 4 12)
    have r23224 := hand1 (x (-7) 2) (x (-7) 12)
    have r23225 := hand1 (x (-8) 3) (x (-8) 13)
    have r23226 := hand1 (x (-9) 4) (x (-9) 14)
    have r23227 := hand1 (x (-3) 2) (x (-3) 12)
    have r23228 := hand1 (x (-5) 4) (x (-5) 14)
    linarith only [r23160, r23161, e23162, e23163, e23164, e23165, e23166, e23167, r23168, e23169, e23170, e23171, e23172, e23173, e23174, r23175, e23176, e23177, e23178, e23179, e23180, e23181, r23182, e23183, e23184, r23185, e23186, e23187, r23188, e23189, e23190, r23191, e23192, e23193, r23194, e23195, e23196, r23197, r23198, r23199, r23200, r23201, r23202, r23203, r23204, r23205, r23206, r23207, r23208, r23209, r23210, r23211, r23212, r23213, r23214, r23215, r23216, r23217, r23218, r23219, r23220, r23221, r23222, r23223, r23224, r23225, r23226, r23227, r23228, d23140, g0, g1, g2, g4, f23104, g6, g7, g8, g10, g11, g12, g13, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, d23079, d23099, g25, g26, g27, g28, g29, g30, d23156, g31, d23128, g36, g37, g38]
  · have f23331 : (x 1 3).toNat = 1 := by rw [h23103]; rfl
    have d23332 : (x 4 12).toNat = 0 := by
      have r23333 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23334 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e23335 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b23336 := hb (x 1 3)
      have b23337 := hb (x 2 2)
      have b23338 := hb (x 3 13)
      have b23339 := hb (x 4 12)
      clear * - r23333 e23334 e23335 b23336 b23337 b23338 b23339 g13 f23331
      omega
    have d23340 : (x 4 1 && x 4 12).toNat = 0 := by
      have r23341 := hand2 (x 4 1) (x 4 12)
      have b23342 := hb (x 4 12)
      have b23343 := hb (x 4 1 && x 4 12)
      clear * - r23341 b23342 b23343 d23332
      omega
    have d23344 : (x 4 4).toNat = 0 := by
      have r23345 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b23346 := hb (x 4 4)
      have b23347 := hb (x 4 12)
      clear * - r23345 b23346 b23347 d23332
      omega
    have d23348 : (x 2 2).toNat = 0 := by
      have r23349 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23350 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e23351 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b23352 := hb (x 1 3)
      have b23353 := hb (x 2 2)
      have b23354 := hb (x 3 13)
      have b23355 := hb (x 4 12)
      clear * - r23349 e23350 e23351 b23352 b23353 b23354 b23355 d23332 g13 f23331
      omega
    have d23356 : (x 4 13).toNat = 1 := by
      have r23357 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23358 := hb (x 2 2)
      have b23359 := hb (x 4 13)
      have b23360 := hb (x 3 1 && x 3 14)
      clear * - r23357 b23358 b23359 b23360 g39 d23348
      omega
    have d23361 : (x 5 12).toNat = 0 := by
      have r23362 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23363 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e23364 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b23365 := hb (x 2 3)
      have b23366 := hb (x 3 2)
      have b23367 := hb (x 4 13)
      have b23368 := hb (x 5 12)
      clear * - r23362 e23363 e23364 b23365 b23366 b23367 b23368 d23356 g9
      omega
    have d23369 : (x 5 4).toNat = 0 := by
      have r23370 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b23371 := hb (x 5 4)
      have b23372 := hb (x 5 12)
      clear * - r23370 b23371 b23372 d23361
      omega
    have d23373 : (x 2 3).toNat = 0 := by
      have r23374 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23375 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e23376 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b23377 := hb (x 2 3)
      have b23378 := hb (x 3 2)
      have b23379 := hb (x 4 13)
      have b23380 := hb (x 5 12)
      clear * - r23374 e23375 e23376 b23377 b23378 b23379 b23380 d23361 d23356 g9
      omega
    have d23381 : (x 2 3 && x 2 14).toNat = 0 := by
      have r23382 := hand1 (x 2 3) (x 2 14)
      have b23383 := hb (x 2 3)
      have b23384 := hb (x 2 3 && x 2 14)
      clear * - r23382 b23383 b23384 d23373
      omega
    have d23385 : (x 8 11).toNat = 1 := by
      have r23386 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23387 := hb (x 4 4)
      have b23388 := hb (x 8 11)
      have b23389 := hb (x 7 1 && x 7 12)
      have b23390 := hb (x 6 2 && x 6 13)
      have b23391 := hb (x 5 3 && x 5 14)
      clear * - r23386 b23387 b23388 b23389 b23390 b23391 g36 g37 g38 d23344
      omega
    have d23392 : (x 8 3).toNat = 1 := by
      have r23393 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b23394 := hb (x 8 3)
      have b23395 := hb (x 8 11)
      clear * - r23393 b23394 b23395 d23385
      omega
    have d23396 : (x 11 12).toNat = 0 := by
      have r23397 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23398 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e23399 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b23400 := hb (x 8 3)
      have b23401 := hb (x 9 2)
      have b23402 := hb (x 10 13)
      have b23403 := hb (x 11 12)
      clear * - r23397 e23398 e23399 b23400 b23401 b23402 b23403 d23392
      omega
    have d23404 : (x 11 1 && x 11 12).toNat = 0 := by
      have r23405 := hand2 (x 11 1) (x 11 12)
      have b23406 := hb (x 11 12)
      have b23407 := hb (x 11 1 && x 11 12)
      clear * - r23405 b23406 b23407 d23396
      omega
    have d23408 : (x 10 13).toNat = 0 := by
      have r23409 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23410 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e23411 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b23412 := hb (x 8 3)
      have b23413 := hb (x 9 2)
      have b23414 := hb (x 10 13)
      have b23415 := hb (x 11 12)
      clear * - r23409 e23410 e23411 b23412 b23413 b23414 b23415 d23396 d23392
      omega
    have d23416 : (x 10 2 && x 10 13).toNat = 0 := by
      have r23417 := hand2 (x 10 2) (x 10 13)
      have b23418 := hb (x 10 13)
      have b23419 := hb (x 10 2 && x 10 13)
      clear * - r23417 b23418 b23419 d23408
      omega
    have d23420 : (x 9 2).toNat = 0 := by
      have r23421 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23422 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e23423 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b23424 := hb (x 8 3)
      have b23425 := hb (x 9 2)
      have b23426 := hb (x 10 13)
      have b23427 := hb (x 11 12)
      clear * - r23421 e23422 e23423 b23424 b23425 b23426 b23427 d23396 d23408 d23392
      omega
    have d23428 : (x 5 11).toNat = 1 := by
      have r23429 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23430 := hb (x 1 4)
      have b23431 := hb (x 5 11)
      have b23432 := hb (x 4 1 && x 4 12)
      have b23433 := hb (x 3 2 && x 3 13)
      have b23434 := hb (x 2 3 && x 2 14)
      clear * - r23429 b23430 b23431 b23432 b23433 b23434 d23340 g35 d23381 g5
      omega
    have d23435 : (x 5 3).toNat = 1 := by
      have r23436 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
      have b23437 := hb (x 5 3)
      have b23438 := hb (x 5 11)
      clear * - r23436 b23437 b23438 d23428
      omega
    have d23439 : (x 8 12).toNat = 0 := by
      have r23440 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23441 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e23442 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b23443 := hb (x 5 3)
      have b23444 := hb (x 6 2)
      have b23445 := hb (x 7 13)
      have b23446 := hb (x 8 12)
      clear * - r23440 e23441 e23442 b23443 b23444 b23445 b23446 d23435
      omega
    have d23447 : (x 8 1 && x 8 12).toNat = 0 := by
      have r23448 := hand2 (x 8 1) (x 8 12)
      have b23449 := hb (x 8 12)
      have b23450 := hb (x 8 1 && x 8 12)
      clear * - r23448 b23449 b23450 d23439
      omega
    have d23451 : (x 8 4).toNat = 0 := by
      have r23452 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
      have b23453 := hb (x 8 4)
      have b23454 := hb (x 8 12)
      clear * - r23452 b23453 b23454 d23439
      omega
    have d23455 : (x 7 13).toNat = 0 := by
      have r23456 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23457 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e23458 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b23459 := hb (x 5 3)
      have b23460 := hb (x 6 2)
      have b23461 := hb (x 7 13)
      have b23462 := hb (x 8 12)
      clear * - r23456 e23457 e23458 b23459 b23460 b23461 b23462 d23439 d23435
      omega
    have d23463 : (x 7 2 && x 7 13).toNat = 0 := by
      have r23464 := hand2 (x 7 2) (x 7 13)
      have b23465 := hb (x 7 13)
      have b23466 := hb (x 7 2 && x 7 13)
      clear * - r23464 b23465 b23466 d23455
      omega
    have d23467 : (x 6 1 && x 6 14).toNat = 1 := by
      have r23468 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23469 := hb (x 5 2)
      have b23470 := hb (x 7 13)
      have b23471 := hb (x 6 1 && x 6 14)
      clear * - r23468 b23469 b23470 b23471 d23455 g14
      omega
    have d23472 : (x 6 1).toNat = 1 := by
      have r23473 := hand1 (x 6 1) (x 6 14)
      have b23474 := hb (x 6 1)
      have b23475 := hb (x 6 1 && x 6 14)
      clear * - r23473 b23474 b23475 d23467
      omega
    have d23476 : (x 7 14).toNat = 0 := by
      have r23477 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23478 := hb (x 6 1)
      have b23479 := hb (x 7 14)
      clear * - r23477 b23478 b23479 d23472
      omega
    have d23480 : (x 7 1 && x 7 14).toNat = 0 := by
      have r23481 := hand2 (x 7 1) (x 7 14)
      have b23482 := hb (x 7 14)
      have b23483 := hb (x 7 1 && x 7 14)
      clear * - r23481 b23482 b23483 d23476
      omega
    have d23484 : (x 7 2).toNat = 0 := by
      have r23485 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b23486 := hb (x 7 2)
      have b23487 := hb (x 7 14)
      clear * - r23485 b23486 b23487 d23476
      omega
    have d23488 : (x 6 2).toNat = 0 := by
      have r23489 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23490 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e23491 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b23492 := hb (x 5 3)
      have b23493 := hb (x 6 2)
      have b23494 := hb (x 7 13)
      have b23495 := hb (x 8 12)
      clear * - r23489 e23490 e23491 b23492 b23493 b23494 b23495 d23439 d23455 d23435
      omega
    have d23496 : (x 8 13).toNat = 1 := by
      have r23497 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23498 := hb (x 6 2)
      have b23499 := hb (x 8 13)
      have b23500 := hb (x 7 1 && x 7 14)
      clear * - r23497 b23498 b23499 b23500 d23480 d23488
      omega
    have d23501 : (x 8 1).toNat = 1 := by
      have r23502 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b23503 := hb (x 8 1)
      have b23504 := hb (x 8 13)
      clear * - r23502 b23503 b23504 d23496
      omega
    have d23505 : (x 9 14).toNat = 0 := by
      have r23506 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23507 := hb (x 8 1)
      have b23508 := hb (x 9 14)
      clear * - r23506 b23507 b23508 d23501
      omega
    have d23509 : (x 9 3 && x 9 14).toNat = 0 := by
      have r23510 := hand2 (x 9 3) (x 9 14)
      have b23511 := hb (x 9 14)
      have b23512 := hb (x 9 3 && x 9 14)
      clear * - r23510 b23511 b23512 d23505
      omega
    have d23513 : (x 12 11).toNat = 1 := by
      have r23514 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23515 := hb (x 8 4)
      have b23516 := hb (x 12 11)
      have b23517 := hb (x 11 1 && x 11 12)
      have b23518 := hb (x 10 2 && x 10 13)
      have b23519 := hb (x 9 3 && x 9 14)
      clear * - r23514 b23515 b23516 b23517 b23518 b23519 d23404 d23416 d23509 d23451
      omega
    have d23520 : (x 12 3).toNat = 1 := by
      have r23521 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
      have b23522 := hb (x 12 3)
      have b23523 := hb (x 12 11)
      clear * - r23521 b23522 b23523 d23513
      omega
    have d23524 : (x 15 12).toNat = 0 := by
      have r23525 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23526 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e23527 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b23528 := hb (x 12 3)
      have b23529 := hb (x 13 2)
      have b23530 := hb (x 14 13)
      have b23531 := hb (x 15 12)
      clear * - r23525 e23526 e23527 b23528 b23529 b23530 b23531 d23520
      omega
    have d23532 : (x 15 1 && x 15 12).toNat = 0 := by
      have r23533 := hand2 (x 15 1) (x 15 12)
      have b23534 := hb (x 15 12)
      have b23535 := hb (x 15 1 && x 15 12)
      clear * - r23533 b23534 b23535 d23524
      omega
    have d23536 : (x 14 13).toNat = 0 := by
      have r23537 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23538 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e23539 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b23540 := hb (x 12 3)
      have b23541 := hb (x 13 2)
      have b23542 := hb (x 14 13)
      have b23543 := hb (x 15 12)
      clear * - r23537 e23538 e23539 b23540 b23541 b23542 b23543 d23524 d23520
      omega
    have d23544 : (x 14 2 && x 14 13).toNat = 0 := by
      have r23545 := hand2 (x 14 2) (x 14 13)
      have b23546 := hb (x 14 13)
      have b23547 := hb (x 14 2 && x 14 13)
      clear * - r23545 b23546 b23547 d23536
      omega
    have d23548 : (x 13 2).toNat = 0 := by
      have r23549 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23550 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e23551 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b23552 := hb (x 12 3)
      have b23553 := hb (x 13 2)
      have b23554 := hb (x 14 13)
      have b23555 := hb (x 15 12)
      clear * - r23549 e23550 e23551 b23552 b23553 b23554 b23555 d23524 d23536 d23520
      omega
    have d23556 : (x 9 12).toNat = 0 := by
      have r23557 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23558 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e23559 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b23560 := hb (x 6 3)
      have b23561 := hb (x 7 2)
      have b23562 := hb (x 8 13)
      have b23563 := hb (x 9 12)
      clear * - r23557 e23558 e23559 b23560 b23561 b23562 b23563 d23496 d23484
      omega
    have d23564 : (x 9 4).toNat = 0 := by
      have r23565 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
      have b23566 := hb (x 9 4)
      have b23567 := hb (x 9 12)
      clear * - r23565 b23566 b23567 d23556
      omega
    have d23568 : (x 6 3).toNat = 0 := by
      have r23569 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23570 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e23571 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b23572 := hb (x 6 3)
      have b23573 := hb (x 7 2)
      have b23574 := hb (x 8 13)
      have b23575 := hb (x 9 12)
      clear * - r23569 e23570 e23571 b23572 b23573 b23574 b23575 d23556 d23496 d23484
      omega
    have d23576 : (x 6 3 && x 6 14).toNat = 0 := by
      have r23577 := hand1 (x 6 3) (x 6 14)
      have b23578 := hb (x 6 3)
      have b23579 := hb (x 6 3 && x 6 14)
      clear * - r23577 b23578 b23579 d23568
      omega
    have d23580 : (x 9 11).toNat = 1 := by
      have r23581 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23582 := hb (x 5 4)
      have b23583 := hb (x 9 11)
      have b23584 := hb (x 8 1 && x 8 12)
      have b23585 := hb (x 7 2 && x 7 13)
      have b23586 := hb (x 6 3 && x 6 14)
      clear * - r23581 b23582 b23583 b23584 b23585 b23586 d23447 d23463 d23576 d23369
      omega
    have d23587 : (x 9 3).toNat = 1 := by
      have r23588 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
      have b23589 := hb (x 9 3)
      have b23590 := hb (x 9 11)
      clear * - r23588 b23589 b23590 d23580
      omega
    have d23591 : (x 12 12).toNat = 0 := by
      have r23592 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23593 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e23594 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b23595 := hb (x 9 3)
      have b23596 := hb (x 10 2)
      have b23597 := hb (x 11 13)
      have b23598 := hb (x 12 12)
      clear * - r23592 e23593 e23594 b23595 b23596 b23597 b23598 d23587
      omega
    have d23599 : (x 12 1 && x 12 12).toNat = 0 := by
      have r23600 := hand2 (x 12 1) (x 12 12)
      have b23601 := hb (x 12 12)
      have b23602 := hb (x 12 1 && x 12 12)
      clear * - r23600 b23601 b23602 d23591
      omega
    have d23603 : (x 12 4).toNat = 0 := by
      have r23604 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b23605 := hb (x 12 4)
      have b23606 := hb (x 12 12)
      clear * - r23604 b23605 b23606 d23591
      omega
    have d23607 : (x 11 13).toNat = 0 := by
      have r23608 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23609 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e23610 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b23611 := hb (x 9 3)
      have b23612 := hb (x 10 2)
      have b23613 := hb (x 11 13)
      have b23614 := hb (x 12 12)
      clear * - r23608 e23609 e23610 b23611 b23612 b23613 b23614 d23591 d23587
      omega
    have d23615 : (x 11 2 && x 11 13).toNat = 0 := by
      have r23616 := hand2 (x 11 2) (x 11 13)
      have b23617 := hb (x 11 13)
      have b23618 := hb (x 11 2 && x 11 13)
      clear * - r23616 b23617 b23618 d23607
      omega
    have d23619 : (x 10 1 && x 10 14).toNat = 1 := by
      have r23620 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23621 := hb (x 9 2)
      have b23622 := hb (x 11 13)
      have b23623 := hb (x 10 1 && x 10 14)
      clear * - r23620 b23621 b23622 b23623 d23607 d23420
      omega
    have d23624 : (x 10 1).toNat = 1 := by
      have r23625 := hand1 (x 10 1) (x 10 14)
      have b23626 := hb (x 10 1)
      have b23627 := hb (x 10 1 && x 10 14)
      clear * - r23625 b23626 b23627 d23619
      omega
    have d23628 : (x 11 14).toNat = 0 := by
      have r23629 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23630 := hb (x 10 1)
      have b23631 := hb (x 11 14)
      clear * - r23629 b23630 b23631 d23624
      omega
    have d23632 : (x 11 1 && x 11 14).toNat = 0 := by
      have r23633 := hand2 (x 11 1) (x 11 14)
      have b23634 := hb (x 11 14)
      have b23635 := hb (x 11 1 && x 11 14)
      clear * - r23633 b23634 b23635 d23628
      omega
    have d23636 : (x 11 2).toNat = 0 := by
      have r23637 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
      have b23638 := hb (x 11 2)
      have b23639 := hb (x 11 14)
      clear * - r23637 b23638 b23639 d23628
      omega
    have d23640 : (x 10 2).toNat = 0 := by
      have r23641 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23642 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e23643 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b23644 := hb (x 9 3)
      have b23645 := hb (x 10 2)
      have b23646 := hb (x 11 13)
      have b23647 := hb (x 12 12)
      clear * - r23641 e23642 e23643 b23644 b23645 b23646 b23647 d23591 d23607 d23587
      omega
    have d23648 : (x 12 13).toNat = 1 := by
      have r23649 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23650 := hb (x 10 2)
      have b23651 := hb (x 12 13)
      have b23652 := hb (x 11 1 && x 11 14)
      clear * - r23649 b23650 b23651 b23652 d23632 d23640
      omega
    have d23653 : (x 12 1).toNat = 1 := by
      have r23654 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
      have b23655 := hb (x 12 1)
      have b23656 := hb (x 12 13)
      clear * - r23654 b23655 b23656 d23648
      omega
    have d23657 : (x 13 14).toNat = 0 := by
      have r23658 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23659 := hb (x 12 1)
      have b23660 := hb (x 13 14)
      clear * - r23658 b23659 b23660 d23653
      omega
    have d23661 : (x 13 1 && x 13 14).toNat = 0 := by
      have r23662 := hand2 (x 13 1) (x 13 14)
      have b23663 := hb (x 13 14)
      have b23664 := hb (x 13 1 && x 13 14)
      clear * - r23662 b23663 b23664 d23657
      omega
    have d23665 : (x 12 2).toNat = 1 := by
      have r23666 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23667 := hb (x 12 2)
      have b23668 := hb (x 14 13)
      have b23669 := hb (x 13 1 && x 13 14)
      clear * - r23666 b23667 b23668 b23669 d23536 d23661
      omega
    have d23670 : (x 14 12).toNat = 0 := by
      have r23671 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23672 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e23673 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b23674 := hb (x 11 3)
      have b23675 := hb (x 12 2)
      have b23676 := hb (x 13 13)
      have b23677 := hb (x 14 12)
      clear * - r23671 e23672 e23673 b23674 b23675 b23676 b23677 d23665
      omega
    have d23678 : (x 14 4).toNat = 0 := by
      have r23679 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
      have b23680 := hb (x 14 4)
      have b23681 := hb (x 14 12)
      clear * - r23679 b23680 b23681 d23670
      omega
    have d23682 : (x 14 4 && x 14 14).toNat = 0 := by
      have r23683 := hand1 (x 14 4) (x 14 14)
      have b23684 := hb (x 14 4)
      have b23685 := hb (x 14 4 && x 14 14)
      clear * - r23683 b23684 b23685 d23678
      omega
    have d23686 : (x 13 13).toNat = 0 := by
      have r23687 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23688 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e23689 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b23690 := hb (x 11 3)
      have b23691 := hb (x 12 2)
      have b23692 := hb (x 13 13)
      have b23693 := hb (x 14 12)
      clear * - r23687 e23688 e23689 b23690 b23691 b23692 b23693 d23670 d23665
      omega
    have d23694 : (x 13 5).toNat = 0 := by
      have r23695 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
      have b23696 := hb (x 13 5)
      have b23697 := hb (x 13 13)
      clear * - r23695 b23696 b23697 d23686
      omega
    have d23698 : (x 13 3 && x 13 14).toNat = 0 := by
      have r23699 := hand2 (x 13 3) (x 13 14)
      have b23700 := hb (x 13 14)
      have b23701 := hb (x 13 3 && x 13 14)
      clear * - r23699 b23700 b23701 d23657
      omega
    have d23702 : (x 16 11).toNat = 1 := by
      have r23703 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23704 := hb (x 12 4)
      have b23705 := hb (x 16 11)
      have b23706 := hb (x 15 1 && x 15 12)
      have b23707 := hb (x 14 2 && x 14 13)
      have b23708 := hb (x 13 3 && x 13 14)
      clear * - r23703 b23704 b23705 b23706 b23707 b23708 d23532 d23544 d23698 d23603
      omega
    have d23709 : (x 16 3).toNat = 1 := by
      have r23710 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
      have b23711 := hb (x 16 3)
      have b23712 := hb (x 16 11)
      clear * - r23710 b23711 b23712 d23702
      omega
    have d23713 : (x 19 12).toNat = 0 := by
      have r23714 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23715 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e23716 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b23717 := hb (x 16 3)
      have b23718 := hb (x 17 2)
      have b23719 := hb (x 18 13)
      have b23720 := hb (x 19 12)
      clear * - r23714 e23715 e23716 b23717 b23718 b23719 b23720 d23709
      omega
    have d23721 : (x 18 13).toNat = 0 := by
      have r23722 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23723 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e23724 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b23725 := hb (x 16 3)
      have b23726 := hb (x 17 2)
      have b23727 := hb (x 18 13)
      have b23728 := hb (x 19 12)
      clear * - r23722 e23723 e23724 b23725 b23726 b23727 b23728 d23713 d23709
      omega
    have d23729 : (x 17 2).toNat = 0 := by
      have r23730 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23731 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e23732 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b23733 := hb (x 16 3)
      have b23734 := hb (x 17 2)
      have b23735 := hb (x 18 13)
      have b23736 := hb (x 19 12)
      clear * - r23730 e23731 e23732 b23733 b23734 b23735 b23736 d23713 d23721 d23709
      omega
    have d23737 : (x 13 12).toNat = 0 := by
      have r23738 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23739 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e23740 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b23741 := hb (x 10 3)
      have b23742 := hb (x 11 2)
      have b23743 := hb (x 12 13)
      have b23744 := hb (x 13 12)
      clear * - r23738 e23739 e23740 b23741 b23742 b23743 b23744 d23648 d23636
      omega
    have d23745 : (x 13 4).toNat = 0 := by
      have r23746 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b23747 := hb (x 13 4)
      have b23748 := hb (x 13 12)
      clear * - r23746 b23747 b23748 d23737
      omega
    have d23749 : (x 10 3).toNat = 0 := by
      have r23750 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23751 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e23752 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b23753 := hb (x 10 3)
      have b23754 := hb (x 11 2)
      have b23755 := hb (x 12 13)
      have b23756 := hb (x 13 12)
      clear * - r23750 e23751 e23752 b23753 b23754 b23755 b23756 d23737 d23648 d23636
      omega
    have d23757 : (x 10 3 && x 10 14).toNat = 0 := by
      have r23758 := hand1 (x 10 3) (x 10 14)
      have b23759 := hb (x 10 3)
      have b23760 := hb (x 10 3 && x 10 14)
      clear * - r23758 b23759 b23760 d23749
      omega
    have d23761 : (x 13 11).toNat = 1 := by
      have r23762 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23763 := hb (x 9 4)
      have b23764 := hb (x 13 11)
      have b23765 := hb (x 12 1 && x 12 12)
      have b23766 := hb (x 11 2 && x 11 13)
      have b23767 := hb (x 10 3 && x 10 14)
      clear * - r23762 b23763 b23764 b23765 b23766 b23767 d23599 d23615 d23757 d23564
      omega
    have d23768 : (x 13 3).toNat = 1 := by
      have r23769 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
      have b23770 := hb (x 13 3)
      have b23771 := hb (x 13 11)
      clear * - r23769 b23770 b23771 d23761
      omega
    have d23772 : (x 16 12).toNat = 0 := by
      have r23773 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23774 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e23775 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b23776 := hb (x 13 3)
      have b23777 := hb (x 14 2)
      have b23778 := hb (x 15 13)
      have b23779 := hb (x 16 12)
      clear * - r23773 e23774 e23775 b23776 b23777 b23778 b23779 d23768
      omega
    have d23780 : (x 16 1 && x 16 12).toNat = 0 := by
      have r23781 := hand2 (x 16 1) (x 16 12)
      have b23782 := hb (x 16 12)
      have b23783 := hb (x 16 1 && x 16 12)
      clear * - r23781 b23782 b23783 d23772
      omega
    have d23784 : (x 16 2 && x 16 12).toNat = 0 := by
      have r23785 := hand2 (x 16 2) (x 16 12)
      have b23786 := hb (x 16 12)
      have b23787 := hb (x 16 2 && x 16 12)
      clear * - r23785 b23786 b23787 d23772
      omega
    have d23788 : (x 15 13).toNat = 0 := by
      have r23789 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23790 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e23791 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b23792 := hb (x 13 3)
      have b23793 := hb (x 14 2)
      have b23794 := hb (x 15 13)
      have b23795 := hb (x 16 12)
      clear * - r23789 e23790 e23791 b23792 b23793 b23794 b23795 d23772 d23768
      omega
    have d23796 : (x 15 2 && x 15 13).toNat = 0 := by
      have r23797 := hand2 (x 15 2) (x 15 13)
      have b23798 := hb (x 15 13)
      have b23799 := hb (x 15 2 && x 15 13)
      clear * - r23797 b23798 b23799 d23788
      omega
    have d23800 : (x 15 3 && x 15 13).toNat = 0 := by
      have r23801 := hand2 (x 15 3) (x 15 13)
      have b23802 := hb (x 15 13)
      have b23803 := hb (x 15 3 && x 15 13)
      clear * - r23801 b23802 b23803 d23788
      omega
    have d23804 : (x 14 1 && x 14 14).toNat = 1 := by
      have r23805 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23806 := hb (x 13 2)
      have b23807 := hb (x 15 13)
      have b23808 := hb (x 14 1 && x 14 14)
      clear * - r23805 b23806 b23807 b23808 d23788 d23548
      omega
    have d23809 : (x 14 1).toNat = 1 := by
      have r23810 := hand1 (x 14 1) (x 14 14)
      have b23811 := hb (x 14 1)
      have b23812 := hb (x 14 1 && x 14 14)
      clear * - r23810 b23811 b23812 d23804
      omega
    have d23813 : (x 15 14).toNat = 0 := by
      have r23814 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23815 := hb (x 14 1)
      have b23816 := hb (x 15 14)
      clear * - r23814 b23815 b23816 d23809
      omega
    have d23817 : (x 15 1 && x 15 14).toNat = 0 := by
      have r23818 := hand2 (x 15 1) (x 15 14)
      have b23819 := hb (x 15 14)
      have b23820 := hb (x 15 1 && x 15 14)
      clear * - r23818 b23819 b23820 d23813
      omega
    have d23821 : (x 15 2).toNat = 0 := by
      have r23822 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
      have b23823 := hb (x 15 2)
      have b23824 := hb (x 15 14)
      clear * - r23822 b23823 b23824 d23813
      omega
    have d23825 : (x 14 2).toNat = 0 := by
      have r23826 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23827 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e23828 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b23829 := hb (x 13 3)
      have b23830 := hb (x 14 2)
      have b23831 := hb (x 15 13)
      have b23832 := hb (x 16 12)
      clear * - r23826 e23827 e23828 b23829 b23830 b23831 b23832 d23772 d23788 d23768
      omega
    have d23833 : (x 16 13).toNat = 1 := by
      have r23834 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23835 := hb (x 14 2)
      have b23836 := hb (x 16 13)
      have b23837 := hb (x 15 1 && x 15 14)
      clear * - r23834 b23835 b23836 b23837 d23817 d23825
      omega
    have d23838 : (x 17 12).toNat = 0 := by
      have r23839 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23840 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e23841 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b23842 := hb (x 14 3)
      have b23843 := hb (x 15 2)
      have b23844 := hb (x 16 13)
      have b23845 := hb (x 17 12)
      clear * - r23839 e23840 e23841 b23842 b23843 b23844 b23845 d23833 d23821
      omega
    have d23846 : (x 14 3).toNat = 0 := by
      have r23847 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23848 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e23849 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b23850 := hb (x 14 3)
      have b23851 := hb (x 15 2)
      have b23852 := hb (x 16 13)
      have b23853 := hb (x 17 12)
      clear * - r23847 e23848 e23849 b23850 b23851 b23852 b23853 d23838 d23833 d23821
      omega
    have d23854 : (x 14 3 && x 14 14).toNat = 0 := by
      have r23855 := hand1 (x 14 3) (x 14 14)
      have b23856 := hb (x 14 3)
      have b23857 := hb (x 14 3 && x 14 14)
      clear * - r23855 b23856 b23857 d23846
      omega
    have d23858 : (x 17 11).toNat = 1 := by
      have r23859 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23860 := hb (x 13 4)
      have b23861 := hb (x 17 11)
      have b23862 := hb (x 16 1 && x 16 12)
      have b23863 := hb (x 15 2 && x 15 13)
      have b23864 := hb (x 14 3 && x 14 14)
      clear * - r23859 b23860 b23861 b23862 b23863 b23864 d23780 d23796 d23854 d23745
      omega
    have d23865 : (x 17 3).toNat = 1 := by
      have r23866 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
      have b23867 := hb (x 17 3)
      have b23868 := hb (x 17 11)
      clear * - r23866 b23867 b23868 d23858
      omega
    have d23869 : (x 20 12).toNat = 0 := by
      have r23870 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23871 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e23872 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b23873 := hb (x 17 3)
      have b23874 := hb (x 18 2)
      have b23875 := hb (x 19 13)
      have b23876 := hb (x 20 12)
      clear * - r23870 e23871 e23872 b23873 b23874 b23875 b23876 d23865
      omega
    have d23877 : (x 19 13).toNat = 0 := by
      have r23878 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23879 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e23880 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b23881 := hb (x 17 3)
      have b23882 := hb (x 18 2)
      have b23883 := hb (x 19 13)
      have b23884 := hb (x 20 12)
      clear * - r23878 e23879 e23880 b23881 b23882 b23883 b23884 d23869 d23865
      omega
    have d23885 : (x 18 1 && x 18 14).toNat = 1 := by
      have r23886 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23887 := hb (x 17 2)
      have b23888 := hb (x 19 13)
      have b23889 := hb (x 18 1 && x 18 14)
      clear * - r23886 b23887 b23888 b23889 d23877 d23729
      omega
    have d23890 : (x 18 14).toNat = 1 := by
      have r23891 := hand2 (x 18 1) (x 18 14)
      have b23892 := hb (x 18 14)
      have b23893 := hb (x 18 1 && x 18 14)
      clear * - r23891 b23892 b23893 d23885
      omega
    have d23894 : (x 17 1).toNat = 0 := by
      have r23895 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b23896 := hb (x 17 1)
      have b23897 := hb (x 18 14)
      clear * - r23895 b23896 b23897 d23890
      omega
    have d23898 : (x 17 1 && x 17 11).toNat = 0 := by
      have r23899 := hand1 (x 17 1) (x 17 11)
      have b23900 := hb (x 17 1)
      have b23901 := hb (x 17 1 && x 17 11)
      clear * - r23899 b23900 b23901 d23894
      omega
    have d23902 : (x 18 2).toNat = 0 := by
      have r23903 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23904 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e23905 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b23906 := hb (x 17 3)
      have b23907 := hb (x 18 2)
      have b23908 := hb (x 19 13)
      have b23909 := hb (x 20 12)
      clear * - r23903 e23904 e23905 b23906 b23907 b23908 b23909 d23869 d23877 d23865
      omega
    have d23910 : (x 18 10).toNat = 0 := by
      have r23911 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
      have b23912 := hb (x 18 2)
      have b23913 := hb (x 18 10)
      clear * - r23911 b23912 b23913 d23902
      omega
    have r23914 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b23915 := hb (x 13 5)
    have b23916 := hb (x 18 10)
    have b23917 := hb (x 17 1 && x 17 11)
    have b23918 := hb (x 16 2 && x 16 12)
    have b23919 := hb (x 15 3 && x 15 13)
    have b23920 := hb (x 14 4 && x 14 14)
    linarith only [r23914, b23915, b23916, b23917, b23918, b23919, b23920, d23910, d23898, d23784, d23800, d23682, d23694]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b111 (x : ℤ → Fin 16 → Bool)
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
    (g5 : (x 1 2 && x 1 11).toNat = 0)
    (g6 : (x 0 3 && x 0 12).toNat = 0)
    (g7 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g8 : (x 1 3 && x 1 12).toNat = 0)
    (g9 : (x 0 4 && x 0 13).toNat = 0)
    (g10 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g11 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g12 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g13 : (x 0 2 && x 0 12).toNat = 0)
    (g14 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g15 : (x 0 1 && x 0 12).toNat = 0)
    (g16 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g17 : (x (-2) 3 && x (-2) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d23922 : (x 5 8).toNat = 0 := by
    have r23923 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23924 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e23925 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e23926 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e23927 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e23928 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e23929 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b23930 := hb (x (-2) 7)
    have b23931 := hb (x (-1) 6)
    have b23932 := hb (x 0 5)
    have b23933 := hb (x 1 4)
    have b23934 := hb (x 2 11)
    have b23935 := hb (x 3 10)
    have b23936 := hb (x 4 9)
    have b23937 := hb (x 5 8)
    clear * - r23923 e23924 e23925 e23926 e23927 e23928 e23929 b23930 b23931 b23932 b23933 b23934 b23935 b23936 b23937 g3 g2
    omega
  have d23938 : (x 4 9).toNat = 0 := by
    have r23939 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23940 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e23941 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e23942 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e23943 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e23944 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e23945 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b23946 := hb (x (-2) 7)
    have b23947 := hb (x (-1) 6)
    have b23948 := hb (x 0 5)
    have b23949 := hb (x 1 4)
    have b23950 := hb (x 2 11)
    have b23951 := hb (x 3 10)
    have b23952 := hb (x 4 9)
    have b23953 := hb (x 5 8)
    clear * - r23939 e23940 e23941 e23942 e23943 e23944 e23945 b23946 b23947 b23948 b23949 b23950 b23951 b23952 b23953 d23922 g3 g2
    omega
  have d23954 : (x 3 10).toNat = 0 := by
    have r23955 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23956 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e23957 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e23958 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e23959 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e23960 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e23961 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b23962 := hb (x (-2) 7)
    have b23963 := hb (x (-1) 6)
    have b23964 := hb (x 0 5)
    have b23965 := hb (x 1 4)
    have b23966 := hb (x 2 11)
    have b23967 := hb (x 3 10)
    have b23968 := hb (x 4 9)
    have b23969 := hb (x 5 8)
    clear * - r23955 e23956 e23957 e23958 e23959 e23960 e23961 b23962 b23963 b23964 b23965 b23966 b23967 b23968 b23969 d23922 d23938 g3 g2
    omega
  have d23970 : (x 3 1 && x 3 10).toNat = 0 := by
    have r23971 := hand2 (x 3 1) (x 3 10)
    have b23972 := hb (x 3 10)
    have b23973 := hb (x 3 1 && x 3 10)
    clear * - r23971 b23972 b23973 d23954
    omega
  have d23974 : (x 2 11).toNat = 0 := by
    have r23975 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e23976 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e23977 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e23978 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e23979 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e23980 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e23981 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b23982 := hb (x (-2) 7)
    have b23983 := hb (x (-1) 6)
    have b23984 := hb (x 0 5)
    have b23985 := hb (x 1 4)
    have b23986 := hb (x 2 11)
    have b23987 := hb (x 3 10)
    have b23988 := hb (x 4 9)
    have b23989 := hb (x 5 8)
    clear * - r23975 e23976 e23977 e23978 e23979 e23980 e23981 b23982 b23983 b23984 b23985 b23986 b23987 b23988 b23989 d23922 d23938 d23954 g3 g2
    omega
  have d23990 : (x 2 2 && x 2 11).toNat = 0 := by
    have r23991 := hand2 (x 2 2) (x 2 11)
    have b23992 := hb (x 2 11)
    have b23993 := hb (x 2 2 && x 2 11)
    clear * - r23991 b23992 b23993 d23974
    omega
  have d23994 : (x (-2) 6).toNat = 1 := by
    have r23995 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b23996 := hb (x (-2) 6)
    have b23997 := hb (x 4 9)
    have b23998 := hb (x 3 1 && x 3 10)
    have b23999 := hb (x 2 2 && x 2 11)
    have b24000 := hb (x 1 3 && x 1 12)
    have b24001 := hb (x 0 4 && x 0 13)
    have b24002 := hb (x (-1) 5 && x (-1) 14)
    clear * - r23995 b23996 b23997 b23998 b23999 b24000 b24001 b24002 d23938 d23970 d23990 g8 g9 g10
    omega
  have d24003 : (x (-2) 14).toNat = 1 := by
    have r24004 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b24005 := hb (x (-2) 6)
    have b24006 := hb (x (-2) 14)
    clear * - r24004 b24005 b24006 d23994
    omega
  have d24007 : (x (-3) 1).toNat = 0 := by
    have r24008 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24009 := hb (x (-3) 1)
    have b24010 := hb (x (-2) 14)
    clear * - r24008 b24009 b24010 d24003
    omega
  have d24011 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r24012 := hand1 (x (-3) 1) (x (-3) 14)
    have b24013 := hb (x (-3) 1)
    have b24014 := hb (x (-3) 1 && x (-3) 14)
    clear * - r24012 b24013 b24014 d24007
    omega
  have d24015 : (x (-3) 13).toNat = 0 := by
    have r24016 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b24017 := hb (x (-3) 1)
    have b24018 := hb (x (-3) 13)
    clear * - r24016 b24017 b24018 d24007
    omega
  have d24019 : (x (-3) 5).toNat = 0 := by
    have r24020 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b24021 := hb (x (-3) 5)
    have b24022 := hb (x (-3) 13)
    clear * - r24020 b24021 b24022 d24015
    omega
  have d24023 : (x 4 8).toNat = 0 := by
    have r24024 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24025 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e24026 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e24027 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e24028 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e24029 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e24030 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b24031 := hb (x (-3) 7)
    have b24032 := hb (x (-2) 6)
    have b24033 := hb (x (-1) 5)
    have b24034 := hb (x 0 4)
    have b24035 := hb (x 1 11)
    have b24036 := hb (x 2 10)
    have b24037 := hb (x 3 9)
    have b24038 := hb (x 4 8)
    clear * - r24024 e24025 e24026 e24027 e24028 e24029 e24030 b24031 b24032 b24033 b24034 b24035 b24036 b24037 b24038 g1 g0 d23994
    omega
  have d24039 : (x 3 9).toNat = 0 := by
    have r24040 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24041 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e24042 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e24043 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e24044 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e24045 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e24046 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b24047 := hb (x (-3) 7)
    have b24048 := hb (x (-2) 6)
    have b24049 := hb (x (-1) 5)
    have b24050 := hb (x 0 4)
    have b24051 := hb (x 1 11)
    have b24052 := hb (x 2 10)
    have b24053 := hb (x 3 9)
    have b24054 := hb (x 4 8)
    clear * - r24040 e24041 e24042 e24043 e24044 e24045 e24046 b24047 b24048 b24049 b24050 b24051 b24052 b24053 b24054 d24023 g1 g0 d23994
    omega
  have d24055 : (x 2 10).toNat = 0 := by
    have r24056 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24057 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e24058 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e24059 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e24060 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e24061 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e24062 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b24063 := hb (x (-3) 7)
    have b24064 := hb (x (-2) 6)
    have b24065 := hb (x (-1) 5)
    have b24066 := hb (x 0 4)
    have b24067 := hb (x 1 11)
    have b24068 := hb (x 2 10)
    have b24069 := hb (x 3 9)
    have b24070 := hb (x 4 8)
    clear * - r24056 e24057 e24058 e24059 e24060 e24061 e24062 b24063 b24064 b24065 b24066 b24067 b24068 b24069 b24070 d24023 d24039 g1 g0 d23994
    omega
  have d24071 : (x 2 1 && x 2 10).toNat = 0 := by
    have r24072 := hand2 (x 2 1) (x 2 10)
    have b24073 := hb (x 2 10)
    have b24074 := hb (x 2 1 && x 2 10)
    clear * - r24072 b24073 b24074 d24055
    omega
  have d24075 : (x 1 11).toNat = 0 := by
    have r24076 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24077 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e24078 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e24079 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e24080 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e24081 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e24082 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b24083 := hb (x (-3) 7)
    have b24084 := hb (x (-2) 6)
    have b24085 := hb (x (-1) 5)
    have b24086 := hb (x 0 4)
    have b24087 := hb (x 1 11)
    have b24088 := hb (x 2 10)
    have b24089 := hb (x 3 9)
    have b24090 := hb (x 4 8)
    clear * - r24076 e24077 e24078 e24079 e24080 e24081 e24082 b24083 b24084 b24085 b24086 b24087 b24088 b24089 b24090 d24023 d24039 d24055 g1 g0 d23994
    omega
  have d24091 : (x 1 1 && x 1 11).toNat = 0 := by
    have r24092 := hand2 (x 1 1) (x 1 11)
    have b24093 := hb (x 1 11)
    have b24094 := hb (x 1 1 && x 1 11)
    clear * - r24092 b24093 b24094 d24075
    omega
  have d24095 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
    have r24096 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24097 := hb (x (-3) 5)
    have b24098 := hb (x 2 10)
    have b24099 := hb (x 1 1 && x 1 11)
    have b24100 := hb (x 0 2 && x 0 12)
    have b24101 := hb (x (-1) 3 && x (-1) 13)
    have b24102 := hb (x (-2) 4 && x (-2) 14)
    clear * - r24096 b24097 b24098 b24099 b24100 b24101 b24102 d24055 d24091 g13 g14 d24019
    omega
  have d24103 : (x (-2) 4).toNat = 1 := by
    have r24104 := hand1 (x (-2) 4) (x (-2) 14)
    have b24105 := hb (x (-2) 4)
    have b24106 := hb (x (-2) 4 && x (-2) 14)
    clear * - r24104 b24105 b24106 d24095
    omega
  have d24107 : (x (-2) 12).toNat = 1 := by
    have r24108 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b24109 := hb (x (-2) 4)
    have b24110 := hb (x (-2) 12)
    clear * - r24108 b24109 b24110 d24103
    omega
  have d24111 : (x (-4) 2).toNat = 0 := by
    have r24112 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24113 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e24114 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b24115 := hb (x (-5) 3)
    have b24116 := hb (x (-4) 2)
    have b24117 := hb (x (-3) 13)
    have b24118 := hb (x (-2) 12)
    clear * - r24112 e24113 e24114 b24115 b24116 b24117 b24118 d24107 d24015
    omega
  have d24119 : (x (-2) 13).toNat = 1 := by
    have r24120 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24121 := hb (x (-4) 2)
    have b24122 := hb (x (-2) 13)
    have b24123 := hb (x (-3) 1 && x (-3) 14)
    clear * - r24120 b24121 b24122 b24123 d24011 d24111
    omega
  have d24124 : (x (-1) 12).toNat = 0 := by
    have r24125 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24126 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e24127 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b24128 := hb (x (-4) 3)
    have b24129 := hb (x (-3) 2)
    have b24130 := hb (x (-2) 13)
    have b24131 := hb (x (-1) 12)
    clear * - r24125 e24126 e24127 b24128 b24129 b24130 b24131 d24119
    omega
  have d24132 : (x (-1) 4).toNat = 0 := by
    have r24133 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b24134 := hb (x (-1) 4)
    have b24135 := hb (x (-1) 12)
    clear * - r24133 b24134 b24135 d24124
    omega
  have d24136 : (x (-3) 4).toNat = 1 := by
    have r24137 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24138 := hb (x (-3) 4)
    have b24139 := hb (x 1 11)
    have b24140 := hb (x 0 1 && x 0 12)
    have b24141 := hb (x (-1) 2 && x (-1) 13)
    have b24142 := hb (x (-2) 3 && x (-2) 14)
    clear * - r24137 b24138 b24139 b24140 b24141 b24142 d24075 g15 g16 g17
    omega
  have d24143 : (x (-3) 12).toNat = 1 := by
    have r24144 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b24145 := hb (x (-3) 4)
    have b24146 := hb (x (-3) 12)
    clear * - r24144 b24145 b24146 d24136
    omega
  have d24147 : (x (-4) 13).toNat = 0 := by
    have r24148 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24149 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e24150 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b24151 := hb (x (-6) 3)
    have b24152 := hb (x (-5) 2)
    have b24153 := hb (x (-4) 13)
    have b24154 := hb (x (-3) 12)
    clear * - r24148 e24149 e24150 b24151 b24152 b24153 b24154 d24143
    omega
  have d24155 : (x (-4) 5).toNat = 0 := by
    have r24156 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b24157 := hb (x (-4) 5)
    have b24158 := hb (x (-4) 13)
    clear * - r24156 b24157 b24158 d24147
    omega
  have d24159 : (x (-5) 2).toNat = 0 := by
    have r24160 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e24161 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e24162 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b24163 := hb (x (-6) 3)
    have b24164 := hb (x (-5) 2)
    have b24165 := hb (x (-4) 13)
    have b24166 := hb (x (-3) 12)
    clear * - r24160 e24161 e24162 b24163 b24164 b24165 b24166 d24143 d24147
    omega
  have d24167 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
    have r24168 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24169 := hb (x (-5) 2)
    have b24170 := hb (x (-3) 13)
    have b24171 := hb (x (-4) 1 && x (-4) 14)
    clear * - r24168 b24169 b24170 b24171 d24015 d24159
    omega
  have d24172 : (x (-4) 1).toNat = 1 := by
    have r24173 := hand1 (x (-4) 1) (x (-4) 14)
    have b24174 := hb (x (-4) 1)
    have b24175 := hb (x (-4) 1 && x (-4) 14)
    clear * - r24173 b24174 b24175 d24167
    omega
  have d24176 : (x (-3) 14).toNat = 0 := by
    have r24177 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24178 := hb (x (-4) 1)
    have b24179 := hb (x (-3) 14)
    clear * - r24177 b24178 b24179 d24172
    omega
  have d24180 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
    have r24181 := hand2 (x (-3) 4) (x (-3) 14)
    have b24182 := hb (x (-3) 14)
    have b24183 := hb (x (-3) 4 && x (-3) 14)
    clear * - r24181 b24182 b24183 d24176
    omega
  have d24184 : (x 0 1 && x 0 11).toNat = 1 := by
    have r24185 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24186 := hb (x (-4) 5)
    have b24187 := hb (x 1 10)
    have b24188 := hb (x 0 1 && x 0 11)
    have b24189 := hb (x (-1) 2 && x (-1) 12)
    have b24190 := hb (x (-2) 3 && x (-2) 13)
    have b24191 := hb (x (-3) 4 && x (-3) 14)
    clear * - r24185 b24186 b24187 b24188 b24189 b24190 b24191 g4 g11 g12 d24180 d24155
    omega
  have d24192 : (x 0 11).toNat = 1 := by
    have r24193 := hand2 (x 0 1) (x 0 11)
    have b24194 := hb (x 0 11)
    have b24195 := hb (x 0 1 && x 0 11)
    clear * - r24193 b24194 b24195 d24184
    omega
  have d24196 : (x (-3) 6).toNat = 0 := by
    have r24197 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
    have b24198 := hb (x (-3) 6)
    have b24199 := hb (x (-3) 14)
    clear * - r24197 b24198 b24199 d24176
    omega
  have d24200 : (x (-2) 5 && x (-2) 14).toNat = 1 := by
    have r24201 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24202 := hb (x (-3) 6)
    have b24203 := hb (x 3 9)
    have b24204 := hb (x 2 1 && x 2 10)
    have b24205 := hb (x 1 2 && x 1 11)
    have b24206 := hb (x 0 3 && x 0 12)
    have b24207 := hb (x (-1) 4 && x (-1) 13)
    have b24208 := hb (x (-2) 5 && x (-2) 14)
    clear * - r24201 b24202 b24203 b24204 b24205 b24206 b24207 b24208 d24039 d24071 g5 g6 g7 d24196
    omega
  have d24209 : (x (-2) 5).toNat = 1 := by
    have r24210 := hand1 (x (-2) 5) (x (-2) 14)
    have b24211 := hb (x (-2) 5)
    have b24212 := hb (x (-2) 5 && x (-2) 14)
    clear * - r24210 b24211 b24212 d24200
    omega
  have r24213 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e24214 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
  have e24215 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
  have e24216 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
  have e24217 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
  have e24218 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
  have e24219 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
  have b24220 := hb (x (-4) 7)
  have b24221 := hb (x (-3) 6)
  have b24222 := hb (x (-2) 5)
  have b24223 := hb (x (-1) 4)
  have b24224 := hb (x 0 11)
  have b24225 := hb (x 1 10)
  have b24226 := hb (x 2 9)
  have b24227 := hb (x 3 8)
  linarith only [r24213, e24214, e24215, e24216, e24217, e24218, e24219, b24220, b24221, b24222, b24223, b24224, b24225, b24226, b24227, g4, d24192, d24132, d24209, d24196]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_a0 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 5).toNat = 0)
    (g1 : (x (-4) 9).toNat = 0)
    (g2 : (x (-4) 11).toNat = 0)
    (g3 : (x (-4) 13).toNat = 0)
    (g4 : (x (-3) 11).toNat = 0)
    (g5 : (x (-2) 5).toNat = 0)
    (g6 : (x (-1) 5).toNat = 0)
    (g7 : (x 0 1).toNat = 0)
    (g8 : (x 0 2).toNat = 0)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 5 && x 0 10).toNat = 0)
    (g11 : (x (-4) 9 && x (-4) 14).toNat = 0)
    (g12 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g13 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g14 : (x 0 3 && x 0 13).toNat = 0)
    (g15 : (x (-1) 4 && x (-1) 14).toNat = 0)
    (g16 : (x 0 4 && x 0 14).toNat = 0)
    (g17 : (x (-4) 1 && x (-4) 12).toNat = 0)
    (g18 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g19 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g20 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g21 : (x (-4) 1 && x (-4) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d24416 : (x 0 1 && x 0 11).toNat = 0 := by
    have r24417 := hand1 (x 0 1) (x 0 11)
    have b24418 := hb (x 0 1)
    have b24419 := hb (x 0 1 && x 0 11)
    clear * - r24417 b24418 b24419 g7
    omega
  cases h24420 : x 0 3
  · have f24421 : (x 0 3).toNat = 0 := by rw [h24420]; rfl
    have d24422 : (x 0 11).toNat = 0 := by
      have r24423 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
      have b24424 := hb (x 0 3)
      have b24425 := hb (x 0 11)
      clear * - r24423 b24424 b24425 f24421
      omega
    have d24426 : (x (-4) 4).toNat = 1 := by
      have r24427 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24428 := hb (x (-4) 4)
      have b24429 := hb (x 0 11)
      have b24430 := hb (x (-1) 1 && x (-1) 12)
      have b24431 := hb (x (-2) 2 && x (-2) 13)
      have b24432 := hb (x (-3) 3 && x (-3) 14)
      clear * - r24427 b24428 b24429 b24430 b24431 b24432 d24422 g18 g19 g20
      omega
    have d24433 : (x (-4) 12).toNat = 1 := by
      have r24434 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b24435 := hb (x (-4) 4)
      have b24436 := hb (x (-4) 12)
      clear * - r24434 b24435 b24436 d24426
      omega
    have d24437 : (x (-5) 13).toNat = 0 := by
      have r24438 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24439 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e24440 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b24441 := hb (x (-7) 3)
      have b24442 := hb (x (-6) 2)
      have b24443 := hb (x (-5) 13)
      have b24444 := hb (x (-4) 12)
      clear * - r24438 e24439 e24440 b24441 b24442 b24443 b24444 d24433
      omega
    have d24445 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
      have r24446 := hand2 (x (-5) 2) (x (-5) 13)
      have b24447 := hb (x (-5) 13)
      have b24448 := hb (x (-5) 2 && x (-5) 13)
      clear * - r24446 b24447 b24448 d24437
      omega
    have d24449 : (x (-6) 2).toNat = 0 := by
      have r24450 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24451 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e24452 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b24453 := hb (x (-7) 3)
      have b24454 := hb (x (-6) 2)
      have b24455 := hb (x (-5) 13)
      have b24456 := hb (x (-4) 12)
      clear * - r24450 e24451 e24452 b24453 b24454 b24455 b24456 d24433 d24437
      omega
    have d24457 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
      have r24458 := hand1 (x (-6) 2) (x (-6) 13)
      have b24459 := hb (x (-6) 2)
      have b24460 := hb (x (-6) 2 && x (-6) 13)
      clear * - r24458 b24459 b24460 d24449
      omega
    have d24461 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
      have r24462 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24463 := hb (x (-6) 2)
      have b24464 := hb (x (-4) 13)
      have b24465 := hb (x (-5) 1 && x (-5) 14)
      clear * - r24462 b24463 b24464 b24465 g3 d24449
      omega
    have d24466 : (x (-5) 14).toNat = 1 := by
      have r24467 := hand2 (x (-5) 1) (x (-5) 14)
      have b24468 := hb (x (-5) 14)
      have b24469 := hb (x (-5) 1 && x (-5) 14)
      clear * - r24467 b24468 b24469 d24461
      omega
    have d24470 : (x (-6) 1).toNat = 0 := by
      have r24471 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24472 := hb (x (-6) 1)
      have b24473 := hb (x (-5) 14)
      clear * - r24471 b24472 b24473 d24466
      omega
    have d24474 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
      have r24475 := hand1 (x (-6) 1) (x (-6) 14)
      have b24476 := hb (x (-6) 1)
      have b24477 := hb (x (-6) 1 && x (-6) 14)
      clear * - r24475 b24476 b24477 d24470
      omega
    have d24478 : (x (-7) 2).toNat = 1 := by
      have r24479 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24480 := hb (x (-7) 2)
      have b24481 := hb (x (-5) 13)
      have b24482 := hb (x (-6) 1 && x (-6) 14)
      clear * - r24479 b24480 b24481 b24482 d24437 d24474
      omega
    have d24483 : (x (-7) 14).toNat = 1 := by
      have r24484 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
      have b24485 := hb (x (-7) 2)
      have b24486 := hb (x (-7) 14)
      clear * - r24484 b24485 b24486 d24478
      omega
    have d24487 : (x (-8) 1).toNat = 0 := by
      have r24488 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24489 := hb (x (-8) 1)
      have b24490 := hb (x (-7) 14)
      clear * - r24488 b24489 b24490 d24483
      omega
    have d24491 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
      have r24492 := hand1 (x (-8) 1) (x (-8) 14)
      have b24493 := hb (x (-8) 1)
      have b24494 := hb (x (-8) 1 && x (-8) 14)
      clear * - r24492 b24493 b24494 d24487
      omega
    have d24495 : (x (-8) 13).toNat = 0 := by
      have r24496 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
      have b24497 := hb (x (-8) 1)
      have b24498 := hb (x (-8) 13)
      clear * - r24496 b24497 b24498 d24487
      omega
    have d24499 : (x (-5) 12).toNat = 0 := by
      have r24500 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24501 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e24502 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b24503 := hb (x (-8) 3)
      have b24504 := hb (x (-7) 2)
      have b24505 := hb (x (-6) 13)
      have b24506 := hb (x (-5) 12)
      clear * - r24500 e24501 e24502 b24503 b24504 b24505 b24506 d24478
      omega
    have d24507 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
      have r24508 := hand2 (x (-5) 1) (x (-5) 12)
      have b24509 := hb (x (-5) 12)
      have b24510 := hb (x (-5) 1 && x (-5) 12)
      clear * - r24508 b24509 b24510 d24499
      omega
    have d24511 : (x (-6) 13).toNat = 0 := by
      have r24512 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24513 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e24514 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b24515 := hb (x (-8) 3)
      have b24516 := hb (x (-7) 2)
      have b24517 := hb (x (-6) 13)
      have b24518 := hb (x (-5) 12)
      clear * - r24512 e24513 e24514 b24515 b24516 b24517 b24518 d24499 d24478
      omega
    have d24519 : (x (-8) 3).toNat = 0 := by
      have r24520 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24521 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e24522 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b24523 := hb (x (-8) 3)
      have b24524 := hb (x (-7) 2)
      have b24525 := hb (x (-6) 13)
      have b24526 := hb (x (-5) 12)
      clear * - r24520 e24521 e24522 b24523 b24524 b24525 b24526 d24499 d24511 d24478
      omega
    have d24527 : (x (-8) 11).toNat = 0 := by
      have r24528 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
      have b24529 := hb (x (-8) 3)
      have b24530 := hb (x (-8) 11)
      clear * - r24528 b24529 b24530 d24519
      omega
    have d24531 : (x (-7) 3).toNat = 0 := by
      have r24532 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24533 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e24534 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b24535 := hb (x (-7) 3)
      have b24536 := hb (x (-6) 2)
      have b24537 := hb (x (-5) 13)
      have b24538 := hb (x (-4) 12)
      clear * - r24532 e24533 e24534 b24535 b24536 b24537 b24538 d24433 d24437 d24449
      omega
    have d24539 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
      have r24540 := hand1 (x (-7) 3) (x (-7) 14)
      have b24541 := hb (x (-7) 3)
      have b24542 := hb (x (-7) 3 && x (-7) 14)
      clear * - r24540 b24541 b24542 d24531
      omega
    have d24543 : (x (-8) 4).toNat = 1 := by
      have r24544 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24545 := hb (x (-8) 4)
      have b24546 := hb (x (-4) 11)
      have b24547 := hb (x (-5) 1 && x (-5) 12)
      have b24548 := hb (x (-6) 2 && x (-6) 13)
      have b24549 := hb (x (-7) 3 && x (-7) 14)
      clear * - r24544 b24545 b24546 b24547 b24548 b24549 g2 d24507 d24457 d24539
      omega
    have d24550 : (x (-8) 12).toNat = 1 := by
      have r24551 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
      have b24552 := hb (x (-8) 4)
      have b24553 := hb (x (-8) 12)
      clear * - r24551 b24552 b24553 d24543
      omega
    have d24554 : (x (-9) 13).toNat = 0 := by
      have r24555 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24556 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e24557 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b24558 := hb (x (-11) 3)
      have b24559 := hb (x (-10) 2)
      have b24560 := hb (x (-9) 13)
      have b24561 := hb (x (-8) 12)
      clear * - r24555 e24556 e24557 b24558 b24559 b24560 b24561 d24550
      omega
    have d24562 : (x (-10) 2).toNat = 0 := by
      have r24563 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24564 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e24565 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b24566 := hb (x (-11) 3)
      have b24567 := hb (x (-10) 2)
      have b24568 := hb (x (-9) 13)
      have b24569 := hb (x (-8) 12)
      clear * - r24563 e24564 e24565 b24566 b24567 b24568 b24569 d24550 d24554
      omega
    have d24570 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
      have r24571 := hand1 (x (-10) 2) (x (-10) 13)
      have b24572 := hb (x (-10) 2)
      have b24573 := hb (x (-10) 2 && x (-10) 13)
      clear * - r24571 b24572 b24573 d24562
      omega
    have d24574 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
      have r24575 := hand1 (x (-10) 2) (x (-10) 12)
      have b24576 := hb (x (-10) 2)
      have b24577 := hb (x (-10) 2 && x (-10) 12)
      clear * - r24575 b24576 b24577 d24562
      omega
    have d24578 : (x (-9) 1 && x (-9) 14).toNat = 1 := by
      have r24579 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24580 := hb (x (-10) 2)
      have b24581 := hb (x (-8) 13)
      have b24582 := hb (x (-9) 1 && x (-9) 14)
      clear * - r24579 b24580 b24581 b24582 d24495 d24562
      omega
    have d24583 : (x (-9) 14).toNat = 1 := by
      have r24584 := hand2 (x (-9) 1) (x (-9) 14)
      have b24585 := hb (x (-9) 14)
      have b24586 := hb (x (-9) 1 && x (-9) 14)
      clear * - r24584 b24585 b24586 d24578
      omega
    have d24587 : (x (-10) 1).toNat = 0 := by
      have r24588 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24589 := hb (x (-10) 1)
      have b24590 := hb (x (-9) 14)
      clear * - r24588 b24589 b24590 d24583
      omega
    have d24591 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
      have r24592 := hand1 (x (-10) 1) (x (-10) 14)
      have b24593 := hb (x (-10) 1)
      have b24594 := hb (x (-10) 1 && x (-10) 14)
      clear * - r24592 b24593 b24594 d24587
      omega
    have d24595 : (x (-11) 2).toNat = 1 := by
      have r24596 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24597 := hb (x (-11) 2)
      have b24598 := hb (x (-9) 13)
      have b24599 := hb (x (-10) 1 && x (-10) 14)
      clear * - r24596 b24597 b24598 b24599 d24554 d24591
      omega
    have d24600 : (x (-11) 14).toNat = 1 := by
      have r24601 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
      have b24602 := hb (x (-11) 2)
      have b24603 := hb (x (-11) 14)
      clear * - r24601 b24602 b24603 d24595
      omega
    have d24604 : (x (-12) 1).toNat = 0 := by
      have r24605 : (x (-11) 14).toNat + (x (-12) 1).toNat = 1 := by have q := hd14 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24606 := hb (x (-12) 1)
      have b24607 := hb (x (-11) 14)
      clear * - r24605 b24606 b24607 d24600
      omega
    have d24608 : (x (-12) 13).toNat = 0 := by
      have r24609 : (x (-12) 13).toNat ≤ (x (-12) 1).toNat := himp _ _ (hp13 (-12))
      have b24610 := hb (x (-12) 1)
      have b24611 := hb (x (-12) 13)
      clear * - r24609 b24610 b24611 d24604
      omega
    have d24612 : (x (-9) 12).toNat = 0 := by
      have r24613 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24614 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
      have e24615 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
      have b24616 := hb (x (-12) 3)
      have b24617 := hb (x (-11) 2)
      have b24618 := hb (x (-10) 13)
      have b24619 := hb (x (-9) 12)
      clear * - r24613 e24614 e24615 b24616 b24617 b24618 b24619 d24595
      omega
    have d24620 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
      have r24621 := hand2 (x (-9) 1) (x (-9) 12)
      have b24622 := hb (x (-9) 12)
      have b24623 := hb (x (-9) 1 && x (-9) 12)
      clear * - r24621 b24622 b24623 d24612
      omega
    have d24624 : (x (-9) 1).toNat = 1 := by
      have r24625 := hand1 (x (-9) 1) (x (-9) 14)
      have b24626 := hb (x (-9) 1)
      have b24627 := hb (x (-9) 1 && x (-9) 14)
      clear * - r24625 b24626 b24627 d24578
      omega
    have d24628 : (x (-8) 14).toNat = 0 := by
      have r24629 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24630 := hb (x (-9) 1)
      have b24631 := hb (x (-8) 14)
      clear * - r24629 b24630 b24631 d24624
      omega
    have d24632 : (x (-8) 2).toNat = 0 := by
      have r24633 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
      have b24634 := hb (x (-8) 2)
      have b24635 := hb (x (-8) 14)
      clear * - r24633 b24634 b24635 d24628
      omega
    have d24636 : (x (-8) 10).toNat = 0 := by
      have r24637 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have b24638 := hb (x (-8) 2)
      have b24639 := hb (x (-8) 10)
      clear * - r24637 b24638 b24639 d24632
      omega
    have d24640 : (x (-7) 1 && x (-7) 14).toNat = 1 := by
      have r24641 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24642 := hb (x (-8) 2)
      have b24643 := hb (x (-6) 13)
      have b24644 := hb (x (-7) 1 && x (-7) 14)
      clear * - r24641 b24642 b24643 b24644 d24511 d24632
      omega
    have d24645 : (x (-7) 1).toNat = 1 := by
      have r24646 := hand1 (x (-7) 1) (x (-7) 14)
      have b24647 := hb (x (-7) 1)
      have b24648 := hb (x (-7) 1 && x (-7) 14)
      clear * - r24646 b24647 b24648 d24640
      omega
    have d24649 : (x (-6) 14).toNat = 0 := by
      have r24650 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24651 := hb (x (-7) 1)
      have b24652 := hb (x (-6) 14)
      clear * - r24650 b24651 b24652 d24645
      omega
    have d24653 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
      have r24654 := hand2 (x (-6) 3) (x (-6) 14)
      have b24655 := hb (x (-6) 14)
      have b24656 := hb (x (-6) 3 && x (-6) 14)
      clear * - r24654 b24655 b24656 d24649
      omega
    have d24657 : (x (-7) 4).toNat = 1 := by
      have r24658 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24659 := hb (x (-7) 4)
      have b24660 := hb (x (-3) 11)
      have b24661 := hb (x (-4) 1 && x (-4) 12)
      have b24662 := hb (x (-5) 2 && x (-5) 13)
      have b24663 := hb (x (-6) 3 && x (-6) 14)
      clear * - r24658 b24659 b24660 b24661 b24662 b24663 g4 g17 d24445 d24653
      omega
    have d24664 : (x (-7) 12).toNat = 1 := by
      have r24665 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
      have b24666 := hb (x (-7) 4)
      have b24667 := hb (x (-7) 12)
      clear * - r24665 b24666 b24667 d24657
      omega
    have d24668 : (x (-9) 2).toNat = 0 := by
      have r24669 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24670 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e24671 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b24672 := hb (x (-10) 3)
      have b24673 := hb (x (-9) 2)
      have b24674 := hb (x (-8) 13)
      have b24675 := hb (x (-7) 12)
      clear * - r24669 e24670 e24671 b24672 b24673 b24674 b24675 d24664 d24495
      omega
    have d24676 : (x (-7) 13).toNat = 1 := by
      have r24677 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24678 := hb (x (-9) 2)
      have b24679 := hb (x (-7) 13)
      have b24680 := hb (x (-8) 1 && x (-8) 14)
      clear * - r24677 b24678 b24679 b24680 d24491 d24668
      omega
    have d24681 : (x (-6) 12).toNat = 0 := by
      have r24682 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24683 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e24684 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b24685 := hb (x (-9) 3)
      have b24686 := hb (x (-8) 2)
      have b24687 := hb (x (-7) 13)
      have b24688 := hb (x (-6) 12)
      clear * - r24682 e24683 e24684 b24685 b24686 b24687 b24688 d24676 d24632
      omega
    have d24689 : (x (-9) 3).toNat = 0 := by
      have r24690 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24691 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e24692 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b24693 := hb (x (-9) 3)
      have b24694 := hb (x (-8) 2)
      have b24695 := hb (x (-7) 13)
      have b24696 := hb (x (-6) 12)
      clear * - r24690 e24691 e24692 b24693 b24694 b24695 b24696 d24681 d24676 d24632
      omega
    have d24697 : (x (-9) 11).toNat = 0 := by
      have r24698 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
      have b24699 := hb (x (-9) 3)
      have b24700 := hb (x (-9) 11)
      clear * - r24698 b24699 b24700 d24689
      omega
    have d24701 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
      have r24702 := hand2 (x (-9) 1) (x (-9) 11)
      have b24703 := hb (x (-9) 11)
      have b24704 := hb (x (-9) 1 && x (-9) 11)
      clear * - r24702 b24703 b24704 d24697
      omega
    have d24705 : (x (-11) 3).toNat = 0 := by
      have r24706 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24707 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e24708 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b24709 := hb (x (-11) 3)
      have b24710 := hb (x (-10) 2)
      have b24711 := hb (x (-9) 13)
      have b24712 := hb (x (-8) 12)
      clear * - r24706 e24707 e24708 b24709 b24710 b24711 b24712 d24550 d24554 d24562
      omega
    have d24713 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
      have r24714 := hand1 (x (-11) 3) (x (-11) 14)
      have b24715 := hb (x (-11) 3)
      have b24716 := hb (x (-11) 3 && x (-11) 14)
      clear * - r24714 b24715 b24716 d24705
      omega
    have d24717 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
      have r24718 := hand1 (x (-11) 3) (x (-11) 13)
      have b24719 := hb (x (-11) 3)
      have b24720 := hb (x (-11) 3 && x (-11) 13)
      clear * - r24718 b24719 b24720 d24705
      omega
    have d24721 : (x (-12) 4).toNat = 1 := by
      have r24722 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24723 := hb (x (-12) 4)
      have b24724 := hb (x (-8) 11)
      have b24725 := hb (x (-9) 1 && x (-9) 12)
      have b24726 := hb (x (-10) 2 && x (-10) 13)
      have b24727 := hb (x (-11) 3 && x (-11) 14)
      clear * - r24722 b24723 b24724 b24725 b24726 b24727 d24527 d24620 d24570 d24713
      omega
    have d24728 : (x (-12) 12).toNat = 1 := by
      have r24729 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
      have b24730 := hb (x (-12) 4)
      have b24731 := hb (x (-12) 12)
      clear * - r24729 b24730 b24731 d24721
      omega
    have d24732 : (x (-13) 13).toNat = 0 := by
      have r24733 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24734 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
      have e24735 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
      have b24736 := hb (x (-15) 3)
      have b24737 := hb (x (-14) 2)
      have b24738 := hb (x (-13) 13)
      have b24739 := hb (x (-12) 12)
      clear * - r24733 e24734 e24735 b24736 b24737 b24738 b24739 d24728
      omega
    have d24740 : (x (-13) 5).toNat = 0 := by
      have r24741 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
      have b24742 := hb (x (-13) 5)
      have b24743 := hb (x (-13) 13)
      clear * - r24741 b24742 b24743 d24732
      omega
    have d24744 : (x (-14) 2).toNat = 0 := by
      have r24745 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24746 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
      have e24747 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
      have b24748 := hb (x (-15) 3)
      have b24749 := hb (x (-14) 2)
      have b24750 := hb (x (-13) 13)
      have b24751 := hb (x (-12) 12)
      clear * - r24745 e24746 e24747 b24748 b24749 b24750 b24751 d24728 d24732
      omega
    have d24752 : (x (-13) 1 && x (-13) 14).toNat = 1 := by
      have r24753 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24754 := hb (x (-14) 2)
      have b24755 := hb (x (-12) 13)
      have b24756 := hb (x (-13) 1 && x (-13) 14)
      clear * - r24753 b24754 b24755 b24756 d24608 d24744
      omega
    have d24757 : (x (-13) 1).toNat = 1 := by
      have r24758 := hand1 (x (-13) 1) (x (-13) 14)
      have b24759 := hb (x (-13) 1)
      have b24760 := hb (x (-13) 1 && x (-13) 14)
      clear * - r24758 b24759 b24760 d24752
      omega
    have d24761 : (x (-12) 14).toNat = 0 := by
      have r24762 : (x (-12) 14).toNat + (x (-13) 1).toNat = 1 := by have q := hd14 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24763 := hb (x (-13) 1)
      have b24764 := hb (x (-12) 14)
      clear * - r24762 b24763 b24764 d24757
      omega
    have d24765 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
      have r24766 := hand2 (x (-12) 4) (x (-12) 14)
      have b24767 := hb (x (-12) 14)
      have b24768 := hb (x (-12) 4 && x (-12) 14)
      clear * - r24766 b24767 b24768 d24761
      omega
    have r24769 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b24770 := hb (x (-13) 5)
    have b24771 := hb (x (-8) 10)
    have b24772 := hb (x (-9) 1 && x (-9) 11)
    have b24773 := hb (x (-10) 2 && x (-10) 12)
    have b24774 := hb (x (-11) 3 && x (-11) 13)
    have b24775 := hb (x (-12) 4 && x (-12) 14)
    linarith only [r24769, b24770, b24771, b24772, b24773, b24774, b24775, d24636, d24701, d24574, d24717, d24765, d24740]
  · have f24776 : (x 0 3).toNat = 1 := by rw [h24420]; rfl
    have d24777 : (x 3 12).toNat = 0 := by
      have r24778 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24779 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e24780 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b24781 := hb (x 0 3)
      have b24782 := hb (x 1 2)
      have b24783 := hb (x 2 13)
      have b24784 := hb (x 3 12)
      clear * - r24778 e24779 e24780 b24781 b24782 b24783 b24784 f24776
      omega
    have d24785 : (x 3 4).toNat = 0 := by
      have r24786 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
      have b24787 := hb (x 3 4)
      have b24788 := hb (x 3 12)
      clear * - r24786 b24787 b24788 d24777
      omega
    have d24789 : (x 2 13).toNat = 0 := by
      have r24790 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24791 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e24792 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b24793 := hb (x 0 3)
      have b24794 := hb (x 1 2)
      have b24795 := hb (x 2 13)
      have b24796 := hb (x 3 12)
      clear * - r24790 e24791 e24792 b24793 b24794 b24795 b24796 d24777 f24776
      omega
    have d24797 : (x 1 1 && x 1 14).toNat = 1 := by
      have r24798 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24799 := hb (x 0 2)
      have b24800 := hb (x 2 13)
      have b24801 := hb (x 1 1 && x 1 14)
      clear * - r24798 b24799 b24800 b24801 d24789 g8
      omega
    have d24802 : (x 1 1).toNat = 1 := by
      have r24803 := hand1 (x 1 1) (x 1 14)
      have b24804 := hb (x 1 1)
      have b24805 := hb (x 1 1 && x 1 14)
      clear * - r24803 b24804 b24805 d24797
      omega
    have d24806 : (x 2 14).toNat = 0 := by
      have r24807 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24808 := hb (x 1 1)
      have b24809 := hb (x 2 14)
      clear * - r24807 b24808 b24809 d24802
      omega
    have d24810 : (x 2 1 && x 2 14).toNat = 0 := by
      have r24811 := hand2 (x 2 1) (x 2 14)
      have b24812 := hb (x 2 14)
      have b24813 := hb (x 2 1 && x 2 14)
      clear * - r24811 b24812 b24813 d24806
      omega
    have d24814 : (x 2 2).toNat = 0 := by
      have r24815 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b24816 := hb (x 2 2)
      have b24817 := hb (x 2 14)
      clear * - r24815 b24816 b24817 d24806
      omega
    have d24818 : (x 2 2 && x 2 12).toNat = 0 := by
      have r24819 := hand1 (x 2 2) (x 2 12)
      have b24820 := hb (x 2 2)
      have b24821 := hb (x 2 2 && x 2 12)
      clear * - r24819 b24820 b24821 d24814
      omega
    have d24822 : (x 1 2).toNat = 0 := by
      have r24823 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24824 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e24825 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b24826 := hb (x 0 3)
      have b24827 := hb (x 1 2)
      have b24828 := hb (x 2 13)
      have b24829 := hb (x 3 12)
      clear * - r24823 e24824 e24825 b24826 b24827 b24828 b24829 d24777 d24789 f24776
      omega
    have d24830 : (x 1 2 && x 1 12).toNat = 0 := by
      have r24831 := hand1 (x 1 2) (x 1 12)
      have b24832 := hb (x 1 2)
      have b24833 := hb (x 1 2 && x 1 12)
      clear * - r24831 b24832 b24833 d24822
      omega
    have d24834 : (x 1 10).toNat = 0 := by
      have r24835 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b24836 := hb (x 1 2)
      have b24837 := hb (x 1 10)
      clear * - r24835 b24836 b24837 d24822
      omega
    have d24838 : (x 3 13).toNat = 1 := by
      have r24839 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24840 := hb (x 1 2)
      have b24841 := hb (x 3 13)
      have b24842 := hb (x 2 1 && x 2 14)
      clear * - r24839 b24840 b24841 b24842 d24810 d24822
      omega
    have d24843 : (x 3 1).toNat = 1 := by
      have r24844 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b24845 := hb (x 3 1)
      have b24846 := hb (x 3 13)
      clear * - r24844 b24845 b24846 d24838
      omega
    have d24847 : (x 4 14).toNat = 0 := by
      have r24848 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24849 := hb (x 3 1)
      have b24850 := hb (x 4 14)
      clear * - r24848 b24849 b24850 d24843
      omega
    have d24851 : (x 4 1 && x 4 14).toNat = 0 := by
      have r24852 := hand2 (x 4 1) (x 4 14)
      have b24853 := hb (x 4 14)
      have b24854 := hb (x 4 1 && x 4 14)
      clear * - r24852 b24853 b24854 d24847
      omega
    have d24855 : (x 4 3 && x 4 14).toNat = 0 := by
      have r24856 := hand2 (x 4 3) (x 4 14)
      have b24857 := hb (x 4 14)
      have b24858 := hb (x 4 3 && x 4 14)
      clear * - r24856 b24857 b24858 d24847
      omega
    have d24859 : (x 4 6).toNat = 0 := by
      have r24860 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
      have b24861 := hb (x 4 6)
      have b24862 := hb (x 4 14)
      clear * - r24860 b24861 b24862 d24847
      omega
    have d24863 : (x 4 1 && x 4 6).toNat = 0 := by
      have r24864 := hand2 (x 4 1) (x 4 6)
      have b24865 := hb (x 4 6)
      have b24866 := hb (x 4 1 && x 4 6)
      clear * - r24864 b24865 b24866 d24859
      omega
    have d24867 : (x 4 2).toNat = 0 := by
      have r24868 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b24869 := hb (x 4 2)
      have b24870 := hb (x 4 14)
      clear * - r24868 b24869 b24870 d24847
      omega
    have d24871 : (x 4 10).toNat = 0 := by
      have r24872 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
      have b24873 := hb (x 4 2)
      have b24874 := hb (x 4 10)
      clear * - r24872 b24873 b24874 d24867
      omega
    have d24875 : (x 4 12).toNat = 0 := by
      have r24876 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24877 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e24878 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b24879 := hb (x 1 3)
      have b24880 := hb (x 2 2)
      have b24881 := hb (x 3 13)
      have b24882 := hb (x 4 12)
      clear * - r24876 e24877 e24878 b24879 b24880 b24881 b24882 d24838 d24814
      omega
    have d24883 : (x 1 3).toNat = 0 := by
      have r24884 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24885 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e24886 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b24887 := hb (x 1 3)
      have b24888 := hb (x 2 2)
      have b24889 := hb (x 3 13)
      have b24890 := hb (x 4 12)
      clear * - r24884 e24885 e24886 b24887 b24888 b24889 b24890 d24875 d24838 d24814
      omega
    have d24891 : (x 1 3 && x 1 13).toNat = 0 := by
      have r24892 := hand1 (x 1 3) (x 1 13)
      have b24893 := hb (x 1 3)
      have b24894 := hb (x 1 3 && x 1 13)
      clear * - r24892 b24893 b24894 d24883
      omega
    have d24895 : (x 3 1 && x 3 11).toNat = 1 := by
      have r24896 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24897 := hb (x (-1) 5)
      have b24898 := hb (x 4 10)
      have b24899 := hb (x 3 1 && x 3 11)
      have b24900 := hb (x 2 2 && x 2 12)
      have b24901 := hb (x 1 3 && x 1 13)
      have b24902 := hb (x 0 4 && x 0 14)
      clear * - r24896 b24897 b24898 b24899 b24900 b24901 b24902 d24871 d24818 d24891 g16 g6
      omega
    have d24903 : (x 3 11).toNat = 1 := by
      have r24904 := hand2 (x 3 1) (x 3 11)
      have b24905 := hb (x 3 11)
      have b24906 := hb (x 3 1 && x 3 11)
      clear * - r24904 b24905 b24906 d24895
      omega
    have d24907 : (x 3 3).toNat = 1 := by
      have r24908 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b24909 := hb (x 3 3)
      have b24910 := hb (x 3 11)
      clear * - r24908 b24909 b24910 d24903
      omega
    have d24911 : (x 6 12).toNat = 0 := by
      have r24912 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24913 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e24914 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b24915 := hb (x 3 3)
      have b24916 := hb (x 4 2)
      have b24917 := hb (x 5 13)
      have b24918 := hb (x 6 12)
      clear * - r24912 e24913 e24914 b24915 b24916 b24917 b24918 d24867 d24907
      omega
    have d24919 : (x 6 1 && x 6 12).toNat = 0 := by
      have r24920 := hand2 (x 6 1) (x 6 12)
      have b24921 := hb (x 6 12)
      have b24922 := hb (x 6 1 && x 6 12)
      clear * - r24920 b24921 b24922 d24911
      omega
    have d24923 : (x 6 4).toNat = 0 := by
      have r24924 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b24925 := hb (x 6 4)
      have b24926 := hb (x 6 12)
      clear * - r24924 b24925 b24926 d24911
      omega
    have d24927 : (x 5 13).toNat = 0 := by
      have r24928 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24929 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e24930 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b24931 := hb (x 3 3)
      have b24932 := hb (x 4 2)
      have b24933 := hb (x 5 13)
      have b24934 := hb (x 6 12)
      clear * - r24928 e24929 e24930 b24931 b24932 b24933 b24934 d24911 d24867 d24907
      omega
    have d24935 : (x 5 2 && x 5 13).toNat = 0 := by
      have r24936 := hand2 (x 5 2) (x 5 13)
      have b24937 := hb (x 5 13)
      have b24938 := hb (x 5 2 && x 5 13)
      clear * - r24936 b24937 b24938 d24927
      omega
    have d24939 : (x 7 11).toNat = 1 := by
      have r24940 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24941 := hb (x 3 4)
      have b24942 := hb (x 7 11)
      have b24943 := hb (x 6 1 && x 6 12)
      have b24944 := hb (x 5 2 && x 5 13)
      have b24945 := hb (x 4 3 && x 4 14)
      clear * - r24940 b24941 b24942 b24943 b24944 b24945 d24919 d24935 d24855 d24785
      omega
    have d24946 : (x 7 3).toNat = 1 := by
      have r24947 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b24948 := hb (x 7 3)
      have b24949 := hb (x 7 11)
      clear * - r24947 b24948 b24949 d24939
      omega
    have d24950 : (x 10 12).toNat = 0 := by
      have r24951 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24952 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e24953 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b24954 := hb (x 7 3)
      have b24955 := hb (x 8 2)
      have b24956 := hb (x 9 13)
      have b24957 := hb (x 10 12)
      clear * - r24951 e24952 e24953 b24954 b24955 b24956 b24957 d24946
      omega
    have d24958 : (x 9 13).toNat = 0 := by
      have r24959 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24960 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e24961 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b24962 := hb (x 7 3)
      have b24963 := hb (x 8 2)
      have b24964 := hb (x 9 13)
      have b24965 := hb (x 10 12)
      clear * - r24959 e24960 e24961 b24962 b24963 b24964 b24965 d24950 d24946
      omega
    have d24966 : (x 8 2).toNat = 0 := by
      have r24967 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e24968 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e24969 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b24970 := hb (x 7 3)
      have b24971 := hb (x 8 2)
      have b24972 := hb (x 9 13)
      have b24973 := hb (x 10 12)
      clear * - r24967 e24968 e24969 b24970 b24971 b24972 b24973 d24950 d24958 d24946
      omega
    have d24974 : (x 8 10).toNat = 0 := by
      have r24975 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
      have b24976 := hb (x 8 2)
      have b24977 := hb (x 8 10)
      clear * - r24975 b24976 b24977 d24966
      omega
    have d24978 : (x 5 5).toNat = 0 := by
      have r24979 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
      have b24980 := hb (x 5 5)
      have b24981 := hb (x 5 13)
      clear * - r24979 b24980 b24981 d24927
      omega
    have d24982 : (x 3 2).toNat = 1 := by
      have r24983 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24984 := hb (x 3 2)
      have b24985 := hb (x 5 13)
      have b24986 := hb (x 4 1 && x 4 14)
      clear * - r24983 b24984 b24985 b24986 d24927 d24851
      omega
    have d24987 : (x 3 14).toNat = 1 := by
      have r24988 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b24989 := hb (x 3 2)
      have b24990 := hb (x 3 14)
      clear * - r24988 b24989 b24990 d24982
      omega
    have d24991 : (x 2 1).toNat = 0 := by
      have r24992 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b24993 := hb (x 2 1)
      have b24994 := hb (x 3 14)
      clear * - r24992 b24993 b24994 d24987
      omega
    have d24995 : (x 2 1 && x 2 11).toNat = 0 := by
      have r24996 := hand1 (x 2 1) (x 2 11)
      have b24997 := hb (x 2 1)
      have b24998 := hb (x 2 1 && x 2 11)
      clear * - r24996 b24997 b24998 d24991
      omega
    have d24999 : (x 5 12).toNat = 0 := by
      have r25000 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25001 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e25002 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b25003 := hb (x 2 3)
      have b25004 := hb (x 3 2)
      have b25005 := hb (x 4 13)
      have b25006 := hb (x 5 12)
      clear * - r25000 e25001 e25002 b25003 b25004 b25005 b25006 d24982
      omega
    have d25007 : (x 4 13).toNat = 0 := by
      have r25008 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25009 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e25010 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b25011 := hb (x 2 3)
      have b25012 := hb (x 3 2)
      have b25013 := hb (x 4 13)
      have b25014 := hb (x 5 12)
      clear * - r25008 e25009 e25010 b25011 b25012 b25013 b25014 d24999 d24982
      omega
    have d25015 : (x 2 3).toNat = 0 := by
      have r25016 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25017 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e25018 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b25019 := hb (x 2 3)
      have b25020 := hb (x 3 2)
      have b25021 := hb (x 4 13)
      have b25022 := hb (x 5 12)
      clear * - r25016 e25017 e25018 b25019 b25020 b25021 b25022 d24999 d25007 d24982
      omega
    have d25023 : (x 2 3 && x 2 8).toNat = 0 := by
      have r25024 := hand1 (x 2 3) (x 2 8)
      have b25025 := hb (x 2 3)
      have b25026 := hb (x 2 3 && x 2 8)
      clear * - r25024 b25025 b25026 d25015
      omega
    have d25027 : (x 2 11).toNat = 0 := by
      have r25028 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have b25029 := hb (x 2 3)
      have b25030 := hb (x 2 11)
      clear * - r25028 b25029 b25030 d25015
      omega
    have d25031 : (x 3 10).toNat = 1 := by
      have r25032 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25033 := hb (x (-2) 5)
      have b25034 := hb (x 3 10)
      have b25035 := hb (x 2 1 && x 2 11)
      have b25036 := hb (x 1 2 && x 1 12)
      have b25037 := hb (x 0 3 && x 0 13)
      have b25038 := hb (x (-1) 4 && x (-1) 14)
      clear * - r25032 b25033 b25034 b25035 b25036 b25037 b25038 d24995 d24830 g14 g15 g5
      omega
    have d25039 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
      have r25040 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25041 := hb (x (-4) 5)
      have b25042 := hb (x 1 10)
      have b25043 := hb (x 0 1 && x 0 11)
      have b25044 := hb (x (-1) 2 && x (-1) 12)
      have b25045 := hb (x (-2) 3 && x (-2) 13)
      have b25046 := hb (x (-3) 4 && x (-3) 14)
      clear * - r25040 b25041 b25042 b25043 b25044 b25045 b25046 d24834 d24416 g12 g13 g0
      omega
    have d25047 : (x (-3) 4).toNat = 1 := by
      have r25048 := hand1 (x (-3) 4) (x (-3) 14)
      have b25049 := hb (x (-3) 4)
      have b25050 := hb (x (-3) 4 && x (-3) 14)
      clear * - r25048 b25049 b25050 d25039
      omega
    have d25051 : (x (-3) 12).toNat = 1 := by
      have r25052 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b25053 := hb (x (-3) 4)
      have b25054 := hb (x (-3) 12)
      clear * - r25052 b25053 b25054 d25047
      omega
    have d25055 : (x (-5) 2).toNat = 0 := by
      have r25056 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25057 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e25058 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b25059 := hb (x (-6) 3)
      have b25060 := hb (x (-5) 2)
      have b25061 := hb (x (-4) 13)
      have b25062 := hb (x (-3) 12)
      clear * - r25056 e25057 e25058 b25059 b25060 b25061 b25062 d25051 g3
      omega
    have d25063 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
      have r25064 := hand1 (x (-5) 2) (x (-5) 13)
      have b25065 := hb (x (-5) 2)
      have b25066 := hb (x (-5) 2 && x (-5) 13)
      clear * - r25064 b25065 b25066 d25055
      omega
    have d25067 : (x (-5) 10).toNat = 0 := by
      have r25068 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
      have b25069 := hb (x (-5) 2)
      have b25070 := hb (x (-5) 10)
      clear * - r25068 b25069 b25070 d25055
      omega
    have d25071 : (x (-3) 13).toNat = 1 := by
      have r25072 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25073 := hb (x (-5) 2)
      have b25074 := hb (x (-3) 13)
      have b25075 := hb (x (-4) 1 && x (-4) 14)
      clear * - r25072 b25073 b25074 b25075 g21 d25055
      omega
    have d25076 : (x (-2) 12).toNat = 0 := by
      have r25077 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25078 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e25079 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b25080 := hb (x (-5) 3)
      have b25081 := hb (x (-4) 2)
      have b25082 := hb (x (-3) 13)
      have b25083 := hb (x (-2) 12)
      clear * - r25077 e25078 e25079 b25080 b25081 b25082 b25083 d25071
      omega
    have d25084 : (x (-2) 7 && x (-2) 12).toNat = 0 := by
      have r25085 := hand2 (x (-2) 7) (x (-2) 12)
      have b25086 := hb (x (-2) 12)
      have b25087 := hb (x (-2) 7 && x (-2) 12)
      clear * - r25085 b25086 b25087 d25076
      omega
    have d25088 : (x (-6) 3).toNat = 0 := by
      have r25089 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25090 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e25091 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b25092 := hb (x (-6) 3)
      have b25093 := hb (x (-5) 2)
      have b25094 := hb (x (-4) 13)
      have b25095 := hb (x (-3) 12)
      clear * - r25089 e25090 e25091 b25092 b25093 b25094 b25095 d25051 g3 d25055
      omega
    have d25096 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
      have r25097 := hand1 (x (-6) 3) (x (-6) 14)
      have b25098 := hb (x (-6) 3)
      have b25099 := hb (x (-6) 3 && x (-6) 14)
      clear * - r25097 b25098 b25099 d25088
      omega
    have d25100 : (x (-7) 4).toNat = 1 := by
      have r25101 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25102 := hb (x (-7) 4)
      have b25103 := hb (x (-3) 11)
      have b25104 := hb (x (-4) 1 && x (-4) 12)
      have b25105 := hb (x (-5) 2 && x (-5) 13)
      have b25106 := hb (x (-6) 3 && x (-6) 14)
      clear * - r25101 b25102 b25103 b25104 b25105 b25106 g4 g17 d25063 d25096
      omega
    have d25107 : (x (-7) 12).toNat = 1 := by
      have r25108 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
      have b25109 := hb (x (-7) 4)
      have b25110 := hb (x (-7) 12)
      clear * - r25108 b25109 b25110 d25100
      omega
    have d25111 : (x (-8) 13).toNat = 0 := by
      have r25112 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25113 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
      have e25114 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
      have b25115 := hb (x (-10) 3)
      have b25116 := hb (x (-9) 2)
      have b25117 := hb (x (-8) 13)
      have b25118 := hb (x (-7) 12)
      clear * - r25112 e25113 e25114 b25115 b25116 b25117 b25118 d25107
      omega
    have d25119 : (x (-8) 5).toNat = 0 := by
      have r25120 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
      have b25121 := hb (x (-8) 5)
      have b25122 := hb (x (-8) 13)
      clear * - r25120 b25121 b25122 d25111
      omega
    have d25123 : (x (-6) 11).toNat = 0 := by
      have r25124 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
      have b25125 := hb (x (-6) 3)
      have b25126 := hb (x (-6) 11)
      clear * - r25124 b25125 b25126 d25088
      omega
    have d25127 : (x 10 8).toNat = 0 := by
      have r25128 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25129 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e25130 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e25131 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e25132 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e25133 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e25134 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b25135 := hb (x 3 7)
      have b25136 := hb (x 4 6)
      have b25137 := hb (x 5 5)
      have b25138 := hb (x 6 4)
      have b25139 := hb (x 7 11)
      have b25140 := hb (x 8 10)
      have b25141 := hb (x 9 9)
      have b25142 := hb (x 10 8)
      clear * - r25128 e25129 e25130 e25131 e25132 e25133 e25134 b25135 b25136 b25137 b25138 b25139 b25140 b25141 b25142 d24974 d24939 d24923 d24978 d24859
      omega
    have d25143 : (x 9 9).toNat = 0 := by
      have r25144 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25145 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e25146 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e25147 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e25148 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e25149 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e25150 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b25151 := hb (x 3 7)
      have b25152 := hb (x 4 6)
      have b25153 := hb (x 5 5)
      have b25154 := hb (x 6 4)
      have b25155 := hb (x 7 11)
      have b25156 := hb (x 8 10)
      have b25157 := hb (x 9 9)
      have b25158 := hb (x 10 8)
      clear * - r25144 e25145 e25146 e25147 e25148 e25149 e25150 b25151 b25152 b25153 b25154 b25155 b25156 b25157 b25158 d25127 d24974 d24939 d24923 d24978 d24859
      omega
    have d25159 : (x 3 7).toNat = 0 := by
      have r25160 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25161 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e25162 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e25163 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e25164 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e25165 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e25166 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b25167 := hb (x 3 7)
      have b25168 := hb (x 4 6)
      have b25169 := hb (x 5 5)
      have b25170 := hb (x 6 4)
      have b25171 := hb (x 7 11)
      have b25172 := hb (x 8 10)
      have b25173 := hb (x 9 9)
      have b25174 := hb (x 10 8)
      clear * - r25160 e25161 e25162 e25163 e25164 e25165 e25166 b25167 b25168 b25169 b25170 b25171 b25172 b25173 b25174 d25127 d25143 d24974 d24939 d24923 d24978 d24859
      omega
    have d25175 : (x 3 2 && x 3 7).toNat = 0 := by
      have r25176 := hand2 (x 3 2) (x 3 7)
      have b25177 := hb (x 3 7)
      have b25178 := hb (x 3 2 && x 3 7)
      clear * - r25176 b25177 b25178 d25159
      omega
    have d25179 : (x 5 8).toNat = 0 := by
      have r25180 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25181 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e25182 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e25183 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e25184 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e25185 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e25186 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b25187 := hb (x (-2) 7)
      have b25188 := hb (x (-1) 6)
      have b25189 := hb (x 0 5)
      have b25190 := hb (x 1 4)
      have b25191 := hb (x 2 11)
      have b25192 := hb (x 3 10)
      have b25193 := hb (x 4 9)
      have b25194 := hb (x 5 8)
      clear * - r25180 e25181 e25182 e25183 e25184 e25185 e25186 b25187 b25188 b25189 b25190 b25191 b25192 b25193 b25194 d25031 d25027 g9
      omega
    have d25195 : (x 4 9).toNat = 0 := by
      have r25196 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25197 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e25198 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e25199 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e25200 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e25201 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e25202 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b25203 := hb (x (-2) 7)
      have b25204 := hb (x (-1) 6)
      have b25205 := hb (x 0 5)
      have b25206 := hb (x 1 4)
      have b25207 := hb (x 2 11)
      have b25208 := hb (x 3 10)
      have b25209 := hb (x 4 9)
      have b25210 := hb (x 5 8)
      clear * - r25196 e25197 e25198 e25199 e25200 e25201 e25202 b25203 b25204 b25205 b25206 b25207 b25208 b25209 b25210 d25179 d25031 d25027 g9
      omega
    have d25211 : (x 1 4).toNat = 0 := by
      have r25212 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25213 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e25214 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e25215 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e25216 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e25217 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e25218 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b25219 := hb (x (-2) 7)
      have b25220 := hb (x (-1) 6)
      have b25221 := hb (x 0 5)
      have b25222 := hb (x 1 4)
      have b25223 := hb (x 2 11)
      have b25224 := hb (x 3 10)
      have b25225 := hb (x 4 9)
      have b25226 := hb (x 5 8)
      clear * - r25212 e25213 e25214 e25215 e25216 e25217 e25218 b25219 b25220 b25221 b25222 b25223 b25224 b25225 b25226 d25179 d25195 d25031 d25027 g9
      omega
    have d25227 : (x 1 4 && x 1 9).toNat = 0 := by
      have r25228 := hand1 (x 1 4) (x 1 9)
      have b25229 := hb (x 1 4)
      have b25230 := hb (x 1 4 && x 1 9)
      clear * - r25228 b25229 b25230 d25211
      omega
    have d25231 : (x (-1) 6).toNat = 0 := by
      have r25232 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25233 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e25234 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e25235 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e25236 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e25237 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e25238 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b25239 := hb (x (-2) 7)
      have b25240 := hb (x (-1) 6)
      have b25241 := hb (x 0 5)
      have b25242 := hb (x 1 4)
      have b25243 := hb (x 2 11)
      have b25244 := hb (x 3 10)
      have b25245 := hb (x 4 9)
      have b25246 := hb (x 5 8)
      clear * - r25232 e25233 e25234 e25235 e25236 e25237 e25238 b25239 b25240 b25241 b25242 b25243 b25244 b25245 b25246 d25179 d25195 d25031 d25027 d25211 g9
      omega
    have d25247 : (x (-1) 6 && x (-1) 11).toNat = 0 := by
      have r25248 := hand1 (x (-1) 6) (x (-1) 11)
      have b25249 := hb (x (-1) 6)
      have b25250 := hb (x (-1) 6 && x (-1) 11)
      clear * - r25248 b25249 b25250 d25231
      omega
    have d25251 : (x (-3) 8).toNat = 0 := by
      have r25252 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25253 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e25254 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e25255 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e25256 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e25257 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e25258 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have b25259 := hb (x (-10) 7)
      have b25260 := hb (x (-9) 6)
      have b25261 := hb (x (-8) 5)
      have b25262 := hb (x (-7) 4)
      have b25263 := hb (x (-6) 11)
      have b25264 := hb (x (-5) 10)
      have b25265 := hb (x (-4) 9)
      have b25266 := hb (x (-3) 8)
      clear * - r25252 e25253 e25254 e25255 e25256 e25257 e25258 b25259 b25260 b25261 b25262 b25263 b25264 b25265 b25266 g1 d25067 d25123 d25100 d25119
      omega
    have d25267 : (x (-3) 8 && x (-3) 13).toNat = 0 := by
      have r25268 := hand1 (x (-3) 8) (x (-3) 13)
      have b25269 := hb (x (-3) 8)
      have b25270 := hb (x (-3) 8 && x (-3) 13)
      clear * - r25268 b25269 b25270 d25251
      omega
    have r25271 : 1 ≤ (x 5 5).toNat + (x 4 1 && x 4 6).toNat + (x 3 2 && x 3 7).toNat + (x 2 3 && x 2 8).toNat + (x 1 4 && x 1 9).toNat + (x 0 5 && x 0 10).toNat + (x (-1) 6 && x (-1) 11).toNat + (x (-2) 7 && x (-2) 12).toNat + (x (-3) 8 && x (-3) 13).toNat + (x (-4) 9 && x (-4) 14).toNat + (x (-5) 10).toNat := by have q := hcov5 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25272 := hb (x (-5) 10)
    have b25273 := hb (x 5 5)
    have b25274 := hb (x 4 1 && x 4 6)
    have b25275 := hb (x 3 2 && x 3 7)
    have b25276 := hb (x 2 3 && x 2 8)
    have b25277 := hb (x 1 4 && x 1 9)
    have b25278 := hb (x 0 5 && x 0 10)
    have b25279 := hb (x (-1) 6 && x (-1) 11)
    have b25280 := hb (x (-2) 7 && x (-2) 12)
    have b25281 := hb (x (-3) 8 && x (-3) 13)
    have b25282 := hb (x (-4) 9 && x (-4) 14)
    linarith only [r25271, b25272, b25273, b25274, b25275, b25276, b25277, b25278, b25279, b25280, b25281, b25282, d24978, d24863, d25175, d25023, d25227, g10, d25247, d25084, d25267, g11, d25067]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_a1_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-2) 5).toNat = 0)
    (g2 : (x (-1) 4).toNat = 0)
    (g3 : (x 0 1).toNat = 1)
    (g4 : (x 0 2).toNat = 0)
    (g5 : (x 0 10).toNat = 0)
    (g6 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g7 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g8 : (x 0 3 && x 0 13).toNat = 0)
    (g9 : (x (-1) 4 && x (-1) 14).toNat = 0)
    (g10 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g11 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g12 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g13 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d25284 : (x 1 14).toNat = 0 := by
    have r25285 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25286 := hb (x 0 1)
    have b25287 := hb (x 1 14)
    clear * - r25285 b25286 b25287 g3
    omega
  have d25288 : (x 1 1 && x 1 14).toNat = 0 := by
    have r25289 := hand2 (x 1 1) (x 1 14)
    have b25290 := hb (x 1 14)
    have b25291 := hb (x 1 1 && x 1 14)
    clear * - r25289 b25290 b25291 d25284
    omega
  have d25292 : (x 1 2).toNat = 0 := by
    have r25293 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
    have b25294 := hb (x 1 2)
    have b25295 := hb (x 1 14)
    clear * - r25293 b25294 b25295 d25284
    omega
  have d25296 : (x 1 2 && x 1 13).toNat = 0 := by
    have r25297 := hand1 (x 1 2) (x 1 13)
    have b25298 := hb (x 1 2)
    have b25299 := hb (x 1 2 && x 1 13)
    clear * - r25297 b25298 b25299 d25292
    omega
  have d25300 : (x 1 2 && x 1 12).toNat = 0 := by
    have r25301 := hand1 (x 1 2) (x 1 12)
    have b25302 := hb (x 1 2)
    have b25303 := hb (x 1 2 && x 1 12)
    clear * - r25301 b25302 b25303 d25292
    omega
  have d25304 : (x 2 13).toNat = 1 := by
    have r25305 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25306 := hb (x 0 2)
    have b25307 := hb (x 2 13)
    have b25308 := hb (x 1 1 && x 1 14)
    clear * - r25305 b25306 b25307 b25308 d25288 g4
    omega
  have d25309 : (x 2 1).toNat = 1 := by
    have r25310 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b25311 := hb (x 2 1)
    have b25312 := hb (x 2 13)
    clear * - r25310 b25311 b25312 d25304
    omega
  have d25313 : (x 3 14).toNat = 0 := by
    have r25314 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25315 := hb (x 2 1)
    have b25316 := hb (x 3 14)
    clear * - r25314 b25315 b25316 d25309
    omega
  have d25317 : (x 3 1 && x 3 14).toNat = 0 := by
    have r25318 := hand2 (x 3 1) (x 3 14)
    have b25319 := hb (x 3 14)
    have b25320 := hb (x 3 1 && x 3 14)
    clear * - r25318 b25319 b25320 d25313
    omega
  have d25321 : (x 3 2).toNat = 0 := by
    have r25322 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b25323 := hb (x 3 2)
    have b25324 := hb (x 3 14)
    clear * - r25322 b25323 b25324 d25313
    omega
  have d25325 : (x 3 10).toNat = 0 := by
    have r25326 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b25327 := hb (x 3 2)
    have b25328 := hb (x 3 10)
    clear * - r25326 b25327 b25328 d25321
    omega
  have d25329 : (x 3 12).toNat = 0 := by
    have r25330 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25331 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e25332 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b25333 := hb (x 0 3)
    have b25334 := hb (x 1 2)
    have b25335 := hb (x 2 13)
    have b25336 := hb (x 3 12)
    clear * - r25330 e25331 e25332 b25333 b25334 b25335 b25336 d25304 d25292
    omega
  have d25337 : (x 3 4).toNat = 0 := by
    have r25338 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b25339 := hb (x 3 4)
    have b25340 := hb (x 3 12)
    clear * - r25338 b25339 b25340 d25329
    omega
  have d25341 : (x 0 3).toNat = 0 := by
    have r25342 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25343 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e25344 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b25345 := hb (x 0 3)
    have b25346 := hb (x 1 2)
    have b25347 := hb (x 2 13)
    have b25348 := hb (x 3 12)
    clear * - r25342 e25343 e25344 b25345 b25346 b25347 b25348 d25329 d25304 d25292
    omega
  have d25349 : (x 0 11).toNat = 0 := by
    have r25350 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b25351 := hb (x 0 3)
    have b25352 := hb (x 0 11)
    clear * - r25350 b25351 b25352 d25341
    omega
  have d25353 : (x (-4) 4).toNat = 1 := by
    have r25354 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25355 := hb (x (-4) 4)
    have b25356 := hb (x 0 11)
    have b25357 := hb (x (-1) 1 && x (-1) 12)
    have b25358 := hb (x (-2) 2 && x (-2) 13)
    have b25359 := hb (x (-3) 3 && x (-3) 14)
    clear * - r25354 b25355 b25356 b25357 b25358 b25359 d25349 g10 g11 g12
    omega
  have d25360 : (x (-4) 12).toNat = 1 := by
    have r25361 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b25362 := hb (x (-4) 4)
    have b25363 := hb (x (-4) 12)
    clear * - r25361 b25362 b25363 d25353
    omega
  have d25364 : (x (-5) 13).toNat = 0 := by
    have r25365 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25366 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e25367 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b25368 := hb (x (-7) 3)
    have b25369 := hb (x (-6) 2)
    have b25370 := hb (x (-5) 13)
    have b25371 := hb (x (-4) 12)
    clear * - r25365 e25366 e25367 b25368 b25369 b25370 b25371 d25360
    omega
  have d25372 : (x (-5) 5).toNat = 0 := by
    have r25373 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b25374 := hb (x (-5) 5)
    have b25375 := hb (x (-5) 13)
    clear * - r25373 b25374 b25375 d25364
    omega
  have d25376 : (x (-6) 2).toNat = 0 := by
    have r25377 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25378 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e25379 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b25380 := hb (x (-7) 3)
    have b25381 := hb (x (-6) 2)
    have b25382 := hb (x (-5) 13)
    have b25383 := hb (x (-4) 12)
    clear * - r25377 e25378 e25379 b25380 b25381 b25382 b25383 d25360 d25364
    omega
  have d25384 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
    have r25385 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25386 := hb (x (-6) 2)
    have b25387 := hb (x (-4) 13)
    have b25388 := hb (x (-5) 1 && x (-5) 14)
    clear * - r25385 b25386 b25387 b25388 g0 d25376
    omega
  have d25389 : (x (-5) 1).toNat = 1 := by
    have r25390 := hand1 (x (-5) 1) (x (-5) 14)
    have b25391 := hb (x (-5) 1)
    have b25392 := hb (x (-5) 1 && x (-5) 14)
    clear * - r25390 b25391 b25392 d25384
    omega
  have d25393 : (x (-4) 14).toNat = 0 := by
    have r25394 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25395 := hb (x (-5) 1)
    have b25396 := hb (x (-4) 14)
    clear * - r25394 b25395 b25396 d25389
    omega
  have d25397 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r25398 := hand2 (x (-4) 4) (x (-4) 14)
    have b25399 := hb (x (-4) 14)
    have b25400 := hb (x (-4) 4 && x (-4) 14)
    clear * - r25398 b25399 b25400 d25393
    omega
  have d25401 : (x 2 1 && x 2 11).toNat = 1 := by
    have r25402 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25403 := hb (x (-2) 5)
    have b25404 := hb (x 3 10)
    have b25405 := hb (x 2 1 && x 2 11)
    have b25406 := hb (x 1 2 && x 1 12)
    have b25407 := hb (x 0 3 && x 0 13)
    have b25408 := hb (x (-1) 4 && x (-1) 14)
    clear * - r25402 b25403 b25404 b25405 b25406 b25407 b25408 d25325 d25300 g8 g9 g1
    omega
  have d25409 : (x 2 11).toNat = 1 := by
    have r25410 := hand2 (x 2 1) (x 2 11)
    have b25411 := hb (x 2 11)
    have b25412 := hb (x 2 1 && x 2 11)
    clear * - r25410 b25411 b25412 d25401
    omega
  have d25413 : (x 2 3).toNat = 1 := by
    have r25414 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b25415 := hb (x 2 3)
    have b25416 := hb (x 2 11)
    clear * - r25414 b25415 b25416 d25409
    omega
  have d25417 : (x 5 12).toNat = 0 := by
    have r25418 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25419 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e25420 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b25421 := hb (x 2 3)
    have b25422 := hb (x 3 2)
    have b25423 := hb (x 4 13)
    have b25424 := hb (x 5 12)
    clear * - r25418 e25419 e25420 b25421 b25422 b25423 b25424 d25321 d25413
    omega
  have d25425 : (x 4 13).toNat = 0 := by
    have r25426 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25427 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e25428 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b25429 := hb (x 2 3)
    have b25430 := hb (x 3 2)
    have b25431 := hb (x 4 13)
    have b25432 := hb (x 5 12)
    clear * - r25426 e25427 e25428 b25429 b25430 b25431 b25432 d25417 d25321 d25413
    omega
  have d25433 : (x 2 2).toNat = 1 := by
    have r25434 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25435 := hb (x 2 2)
    have b25436 := hb (x 4 13)
    have b25437 := hb (x 3 1 && x 3 14)
    clear * - r25434 b25435 b25436 b25437 d25425 d25317
    omega
  have d25438 : (x 2 14).toNat = 1 := by
    have r25439 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b25440 := hb (x 2 2)
    have b25441 := hb (x 2 14)
    clear * - r25439 b25440 b25441 d25433
    omega
  have d25442 : (x 1 1).toNat = 0 := by
    have r25443 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25444 := hb (x 1 1)
    have b25445 := hb (x 2 14)
    clear * - r25443 b25444 b25445 d25438
    omega
  have d25446 : (x 1 13).toNat = 0 := by
    have r25447 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b25448 := hb (x 1 1)
    have b25449 := hb (x 1 13)
    clear * - r25447 b25448 b25449 d25442
    omega
  have d25450 : (x 4 12).toNat = 0 := by
    have r25451 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25452 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e25453 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b25454 := hb (x 1 3)
    have b25455 := hb (x 2 2)
    have b25456 := hb (x 3 13)
    have b25457 := hb (x 4 12)
    clear * - r25451 e25452 e25453 b25454 b25455 b25456 b25457 d25433
    omega
  have d25458 : (x 4 4).toNat = 0 := by
    have r25459 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b25460 := hb (x 4 4)
    have b25461 := hb (x 4 12)
    clear * - r25459 b25460 b25461 d25450
    omega
  have d25462 : (x 4 4 && x 4 14).toNat = 0 := by
    have r25463 := hand1 (x 4 4) (x 4 14)
    have b25464 := hb (x 4 4)
    have b25465 := hb (x 4 4 && x 4 14)
    clear * - r25463 b25464 b25465 d25458
    omega
  have d25466 : (x 3 13).toNat = 0 := by
    have r25467 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25468 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e25469 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b25470 := hb (x 1 3)
    have b25471 := hb (x 2 2)
    have b25472 := hb (x 3 13)
    have b25473 := hb (x 4 12)
    clear * - r25467 e25468 e25469 b25470 b25471 b25472 b25473 d25450 d25433
    omega
  have d25474 : (x 3 5).toNat = 0 := by
    have r25475 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b25476 := hb (x 3 5)
    have b25477 := hb (x 3 13)
    clear * - r25475 b25476 b25477 d25466
    omega
  have d25478 : (x (-1) 1 && x (-1) 11).toNat = 1 := by
    have r25479 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25480 := hb (x (-5) 5)
    have b25481 := hb (x 0 10)
    have b25482 := hb (x (-1) 1 && x (-1) 11)
    have b25483 := hb (x (-2) 2 && x (-2) 12)
    have b25484 := hb (x (-3) 3 && x (-3) 13)
    have b25485 := hb (x (-4) 4 && x (-4) 14)
    clear * - r25479 b25480 b25481 b25482 b25483 b25484 b25485 g5 g6 g7 d25397 d25372
    omega
  have d25486 : (x (-1) 11).toNat = 1 := by
    have r25487 := hand2 (x (-1) 1) (x (-1) 11)
    have b25488 := hb (x (-1) 11)
    have b25489 := hb (x (-1) 1 && x (-1) 11)
    clear * - r25487 b25488 b25489 d25478
    omega
  have d25490 : (x (-1) 3).toNat = 1 := by
    have r25491 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b25492 := hb (x (-1) 3)
    have b25493 := hb (x (-1) 11)
    clear * - r25491 b25492 b25493 d25486
    omega
  have d25494 : (x 2 12).toNat = 0 := by
    have r25495 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25496 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e25497 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b25498 := hb (x (-1) 3)
    have b25499 := hb (x 0 2)
    have b25500 := hb (x 1 13)
    have b25501 := hb (x 2 12)
    clear * - r25495 e25496 e25497 b25498 b25499 b25500 b25501 d25446 g4 d25490
    omega
  have d25502 : (x 2 1 && x 2 12).toNat = 0 := by
    have r25503 := hand2 (x 2 1) (x 2 12)
    have b25504 := hb (x 2 12)
    have b25505 := hb (x 2 1 && x 2 12)
    clear * - r25503 b25504 b25505 d25494
    omega
  have d25506 : (x 3 11).toNat = 1 := by
    have r25507 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25508 := hb (x (-1) 4)
    have b25509 := hb (x 3 11)
    have b25510 := hb (x 2 1 && x 2 12)
    have b25511 := hb (x 1 2 && x 1 13)
    have b25512 := hb (x 0 3 && x 0 14)
    clear * - r25507 b25508 b25509 b25510 b25511 b25512 d25502 d25296 g13 g2
    omega
  have d25513 : (x 3 3).toNat = 1 := by
    have r25514 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b25515 := hb (x 3 3)
    have b25516 := hb (x 3 11)
    clear * - r25514 b25515 b25516 d25506
    omega
  have d25517 : (x 6 12).toNat = 0 := by
    have r25518 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25519 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e25520 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b25521 := hb (x 3 3)
    have b25522 := hb (x 4 2)
    have b25523 := hb (x 5 13)
    have b25524 := hb (x 6 12)
    clear * - r25518 e25519 e25520 b25521 b25522 b25523 b25524 d25513
    omega
  have d25525 : (x 6 1 && x 6 12).toNat = 0 := by
    have r25526 := hand2 (x 6 1) (x 6 12)
    have b25527 := hb (x 6 12)
    have b25528 := hb (x 6 1 && x 6 12)
    clear * - r25526 b25527 b25528 d25517
    omega
  have d25529 : (x 6 2 && x 6 12).toNat = 0 := by
    have r25530 := hand2 (x 6 2) (x 6 12)
    have b25531 := hb (x 6 12)
    have b25532 := hb (x 6 2 && x 6 12)
    clear * - r25530 b25531 b25532 d25517
    omega
  have d25533 : (x 5 13).toNat = 0 := by
    have r25534 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25535 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e25536 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b25537 := hb (x 3 3)
    have b25538 := hb (x 4 2)
    have b25539 := hb (x 5 13)
    have b25540 := hb (x 6 12)
    clear * - r25534 e25535 e25536 b25537 b25538 b25539 b25540 d25517 d25513
    omega
  have d25541 : (x 5 2 && x 5 13).toNat = 0 := by
    have r25542 := hand2 (x 5 2) (x 5 13)
    have b25543 := hb (x 5 13)
    have b25544 := hb (x 5 2 && x 5 13)
    clear * - r25542 b25543 b25544 d25533
    omega
  have d25545 : (x 5 3 && x 5 13).toNat = 0 := by
    have r25546 := hand2 (x 5 3) (x 5 13)
    have b25547 := hb (x 5 13)
    have b25548 := hb (x 5 3 && x 5 13)
    clear * - r25546 b25547 b25548 d25533
    omega
  have d25549 : (x 4 1 && x 4 14).toNat = 1 := by
    have r25550 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25551 := hb (x 3 2)
    have b25552 := hb (x 5 13)
    have b25553 := hb (x 4 1 && x 4 14)
    clear * - r25550 b25551 b25552 b25553 d25533 d25321
    omega
  have d25554 : (x 4 1).toNat = 1 := by
    have r25555 := hand1 (x 4 1) (x 4 14)
    have b25556 := hb (x 4 1)
    have b25557 := hb (x 4 1 && x 4 14)
    clear * - r25555 b25556 b25557 d25549
    omega
  have d25558 : (x 5 14).toNat = 0 := by
    have r25559 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25560 := hb (x 4 1)
    have b25561 := hb (x 5 14)
    clear * - r25559 b25560 b25561 d25554
    omega
  have d25562 : (x 5 1 && x 5 14).toNat = 0 := by
    have r25563 := hand2 (x 5 1) (x 5 14)
    have b25564 := hb (x 5 14)
    have b25565 := hb (x 5 1 && x 5 14)
    clear * - r25563 b25564 b25565 d25558
    omega
  have d25566 : (x 5 2).toNat = 0 := by
    have r25567 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b25568 := hb (x 5 2)
    have b25569 := hb (x 5 14)
    clear * - r25567 b25568 b25569 d25558
    omega
  have d25570 : (x 4 2).toNat = 0 := by
    have r25571 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25572 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e25573 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b25574 := hb (x 3 3)
    have b25575 := hb (x 4 2)
    have b25576 := hb (x 5 13)
    have b25577 := hb (x 6 12)
    clear * - r25571 e25572 e25573 b25574 b25575 b25576 b25577 d25517 d25533 d25513
    omega
  have d25578 : (x 6 13).toNat = 1 := by
    have r25579 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25580 := hb (x 4 2)
    have b25581 := hb (x 6 13)
    have b25582 := hb (x 5 1 && x 5 14)
    clear * - r25579 b25580 b25581 b25582 d25562 d25570
    omega
  have d25583 : (x 6 1).toNat = 1 := by
    have r25584 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b25585 := hb (x 6 1)
    have b25586 := hb (x 6 13)
    clear * - r25584 b25585 b25586 d25578
    omega
  have d25587 : (x 7 14).toNat = 0 := by
    have r25588 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25589 := hb (x 6 1)
    have b25590 := hb (x 7 14)
    clear * - r25588 b25589 b25590 d25583
    omega
  have d25591 : (x 7 2).toNat = 0 := by
    have r25592 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b25593 := hb (x 7 2)
    have b25594 := hb (x 7 14)
    clear * - r25592 b25593 b25594 d25587
    omega
  have d25595 : (x 7 12).toNat = 0 := by
    have r25596 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25597 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e25598 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b25599 := hb (x 4 3)
    have b25600 := hb (x 5 2)
    have b25601 := hb (x 6 13)
    have b25602 := hb (x 7 12)
    clear * - r25596 e25597 e25598 b25599 b25600 b25601 b25602 d25578 d25566
    omega
  have d25603 : (x 4 3).toNat = 0 := by
    have r25604 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25605 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e25606 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b25607 := hb (x 4 3)
    have b25608 := hb (x 5 2)
    have b25609 := hb (x 6 13)
    have b25610 := hb (x 7 12)
    clear * - r25604 e25605 e25606 b25607 b25608 b25609 b25610 d25595 d25578 d25566
    omega
  have d25611 : (x 4 3 && x 4 14).toNat = 0 := by
    have r25612 := hand1 (x 4 3) (x 4 14)
    have b25613 := hb (x 4 3)
    have b25614 := hb (x 4 3 && x 4 14)
    clear * - r25612 b25613 b25614 d25603
    omega
  have d25615 : (x 7 11).toNat = 1 := by
    have r25616 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25617 := hb (x 3 4)
    have b25618 := hb (x 7 11)
    have b25619 := hb (x 6 1 && x 6 12)
    have b25620 := hb (x 5 2 && x 5 13)
    have b25621 := hb (x 4 3 && x 4 14)
    clear * - r25616 b25617 b25618 b25619 b25620 b25621 d25525 d25541 d25611 d25337
    omega
  have d25622 : (x 7 3).toNat = 1 := by
    have r25623 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b25624 := hb (x 7 3)
    have b25625 := hb (x 7 11)
    clear * - r25623 b25624 b25625 d25615
    omega
  have d25626 : (x 10 12).toNat = 0 := by
    have r25627 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25628 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e25629 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b25630 := hb (x 7 3)
    have b25631 := hb (x 8 2)
    have b25632 := hb (x 9 13)
    have b25633 := hb (x 10 12)
    clear * - r25627 e25628 e25629 b25630 b25631 b25632 b25633 d25622
    omega
  have d25634 : (x 9 13).toNat = 0 := by
    have r25635 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25636 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e25637 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b25638 := hb (x 7 3)
    have b25639 := hb (x 8 2)
    have b25640 := hb (x 9 13)
    have b25641 := hb (x 10 12)
    clear * - r25635 e25636 e25637 b25638 b25639 b25640 b25641 d25626 d25622
    omega
  have d25642 : (x 8 1 && x 8 14).toNat = 1 := by
    have r25643 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25644 := hb (x 7 2)
    have b25645 := hb (x 9 13)
    have b25646 := hb (x 8 1 && x 8 14)
    clear * - r25643 b25644 b25645 b25646 d25634 d25591
    omega
  have d25647 : (x 8 14).toNat = 1 := by
    have r25648 := hand2 (x 8 1) (x 8 14)
    have b25649 := hb (x 8 14)
    have b25650 := hb (x 8 1 && x 8 14)
    clear * - r25648 b25649 b25650 d25642
    omega
  have d25651 : (x 7 1).toNat = 0 := by
    have r25652 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25653 := hb (x 7 1)
    have b25654 := hb (x 8 14)
    clear * - r25652 b25653 b25654 d25647
    omega
  have d25655 : (x 7 1 && x 7 11).toNat = 0 := by
    have r25656 := hand1 (x 7 1) (x 7 11)
    have b25657 := hb (x 7 1)
    have b25658 := hb (x 7 1 && x 7 11)
    clear * - r25656 b25657 b25658 d25651
    omega
  have d25659 : (x 8 10).toNat = 1 := by
    have r25660 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b25661 := hb (x 3 5)
    have b25662 := hb (x 8 10)
    have b25663 := hb (x 7 1 && x 7 11)
    have b25664 := hb (x 6 2 && x 6 12)
    have b25665 := hb (x 5 3 && x 5 13)
    have b25666 := hb (x 4 4 && x 4 14)
    clear * - r25660 b25661 b25662 b25663 b25664 b25665 b25666 d25655 d25529 d25545 d25462 d25474
    omega
  have d25667 : (x 8 2).toNat = 1 := by
    have r25668 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
    have b25669 := hb (x 8 2)
    have b25670 := hb (x 8 10)
    clear * - r25668 b25669 b25670 d25659
    omega
  have r25671 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e25672 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
  have e25673 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
  have b25674 := hb (x 7 3)
  have b25675 := hb (x 8 2)
  have b25676 := hb (x 9 13)
  have b25677 := hb (x 10 12)
  linarith only [r25671, e25672, e25673, b25674, b25675, b25676, b25677, d25626, d25634, d25667, d25622]

theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_a1 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-2) 5).toNat = 0)
    (g2 : (x (-1) 4).toNat = 0)
    (g3 : (x 0 1).toNat = 1)
    (g4 : (x 0 2).toNat = 0)
    (g5 : (x 0 10).toNat = 0)
    (g6 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g7 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g8 : (x 0 3 && x 0 13).toNat = 0)
    (g9 : (x (-1) 4 && x (-1) 14).toNat = 0)
    (g10 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g11 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g12 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g13 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_a1_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
