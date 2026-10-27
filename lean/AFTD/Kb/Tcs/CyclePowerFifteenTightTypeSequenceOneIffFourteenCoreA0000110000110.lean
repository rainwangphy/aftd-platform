import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA00001100001100000
import AFTD.Kb.Tcs.CyclePowerFifteenTightTypeSequenceOneIffFourteenCoreA00001100001100001
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000110

Topic: combinatorics   Node: e7e95e752401

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 136 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000110_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 7).toNat = 0)
    (g1 : (x (-5) 6).toNat = 0)
    (g2 : (x (-4) 5).toNat = 0)
    (g3 : (x (-4) 7).toNat = 0)
    (g4 : (x (-4) 11).toNat = 0)
    (g5 : (x (-3) 4).toNat = 0)
    (g6 : (x (-3) 6).toNat = 0)
    (g7 : (x (-3) 10).toNat = 0)
    (g8 : (x (-3) 11).toNat = 0)
    (g9 : (x (-2) 3).toNat = 0)
    (g10 : (x (-2) 5).toNat = 0)
    (g11 : (x (-2) 9).toNat = 0)
    (g12 : (x (-2) 10).toNat = 0)
    (g13 : (x (-2) 11).toNat = 0)
    (g14 : (x (-2) 13).toNat = 0)
    (g15 : (x (-1) 2).toNat = 1)
    (g16 : (x (-1) 4).toNat = 1)
    (g17 : (x (-1) 6).toNat = 0)
    (g18 : (x (-1) 8).toNat = 1)
    (g19 : (x (-1) 9).toNat = 1)
    (g20 : (x (-1) 10).toNat = 1)
    (g21 : (x (-1) 11).toNat = 1)
    (g22 : (x (-1) 13).toNat = 1)
    (g23 : (x 0 1).toNat = 1)
    (g24 : (x 0 3).toNat = 0)
    (g25 : (x 0 4).toNat = 0)
    (g26 : (x 0 6).toNat = 0)
    (g27 : (x 0 7).toNat = 0)
    (g28 : (x 0 8).toNat = 0)
    (g29 : (x 0 9).toNat = 0)
    (g30 : (x 0 10).toNat = 0)
    (g31 : (x 0 11).toNat = 0)
    (g32 : (x 0 12).toNat = 0)
    (g33 : (x 1 2).toNat = 0)
    (g34 : (x 1 3).toNat = 0)
    (g35 : (x 1 5).toNat = 0)
    (g36 : (x 1 6).toNat = 0)
    (g37 : (x 1 8).toNat = 0)
    (g38 : (x 1 9).toNat = 0)
    (g39 : (x 1 10).toNat = 0)
    (g40 : (x 1 11).toNat = 0)
    (g41 : (x 1 14).toNat = 0)
    (g42 : (x 2 1).toNat = 1)
    (g43 : (x 2 4).toNat = 0)
    (g44 : (x 2 8).toNat = 0)
    (g45 : (x 2 10).toNat = 0)
    (g46 : (x 2 13).toNat = 1)
    (g47 : (x 2 14).toNat = 1)
    (g48 : (x 3 2).toNat = 0)
    (g49 : (x 3 4).toNat = 0)
    (g50 : (x 3 6).toNat = 0)
    (g51 : (x 3 9).toNat = 0)
    (g52 : (x 3 12).toNat = 0)
    (g53 : (x 4 8).toNat = 0)
    (g54 : (x 3 3 && x 3 4).toNat = 0)
    (g55 : (x 2 4 && x 2 5).toNat = 0)
    (g56 : (x 1 5 && x 1 6).toNat = 0)
    (g57 : (x 0 6 && x 0 7).toNat = 0)
    (g58 : (x (-2) 8 && x (-2) 9).toNat = 0)
    (g59 : (x (-3) 9 && x (-3) 10).toNat = 0)
    (g60 : (x (-4) 10 && x (-4) 11).toNat = 0)
    (g61 : (x 2 4 && x 2 8).toNat = 0)
    (g62 : (x 1 5 && x 1 9).toNat = 0)
    (g63 : (x 0 6 && x 0 10).toNat = 0)
    (g64 : (x 3 8 && x 3 12).toNat = 0)
    (g65 : (x 2 9 && x 2 13).toNat = 0)
    (g66 : (x 4 8 && x 4 12).toNat = 0)
    (g67 : (x 3 9 && x 3 13).toNat = 0)
    (g68 : (x (-3) 1 && x (-3) 6).toNat = 0)
    (g69 : (x (-4) 2 && x (-4) 7).toNat = 0)
    (g70 : (x 0 1 && x 0 6).toNat = 0)
    (g71 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g72 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g73 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g74 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g75 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g76 : (x 3 2 && x 3 7).toNat = 0)
    (g77 : (x 2 3 && x 2 8).toNat = 0)
    (g78 : (x 1 4 && x 1 9).toNat = 0)
    (g79 : (x 0 5 && x 0 10).toNat = 0)
    (g80 : (x 3 3 && x 3 8).toNat = 0)
    (g81 : (x 2 4 && x 2 9).toNat = 0)
    (g82 : (x 1 5 && x 1 10).toNat = 0)
    (g83 : (x 0 6 && x 0 11).toNat = 0)
    (g84 : (x (-2) 8 && x (-2) 13).toNat = 0)
    (g85 : (x 3 8 && x 3 13).toNat = 0)
    (g86 : (x 2 9 && x 2 14).toNat = 0)
    (g87 : (x (-2) 1 && x (-2) 7).toNat = 0)
    (g88 : (x (-3) 2 && x (-3) 8).toNat = 0)
    (g89 : (x (-4) 3 && x (-4) 9).toNat = 0)
    (g90 : (x (-5) 4 && x (-5) 10).toNat = 0)
    (g91 : (x (-6) 5 && x (-6) 11).toNat = 0)
    (g92 : (x (-7) 6 && x (-7) 12).toNat = 0)
    (g93 : (x (-8) 7 && x (-8) 13).toNat = 0)
    (g94 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g95 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g96 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g97 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g98 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g99 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g100 : (x 4 2 && x 4 8).toNat = 0)
    (g101 : (x 3 3 && x 3 9).toNat = 0)
    (g102 : (x 2 4 && x 2 10).toNat = 0)
    (g103 : (x 1 5 && x 1 11).toNat = 0)
    (g104 : (x 0 6 && x 0 12).toNat = 0)
    (g105 : (x 4 8 && x 4 14).toNat = 0)
    (g106 : (x (-2) 1 && x (-2) 8).toNat = 0)
    (g107 : (x (-3) 2 && x (-3) 9).toNat = 0)
    (g108 : (x (-4) 3 && x (-4) 10).toNat = 0)
    (g109 : (x (-5) 4 && x (-5) 11).toNat = 0)
    (g110 : (x (-6) 5 && x (-6) 12).toNat = 0)
    (g111 : (x (-7) 6 && x (-7) 13).toNat = 0)
    (g112 : (x (-8) 7 && x (-8) 14).toNat = 0)
    (g113 : (x 4 1 && x 4 8).toNat = 0)
    (g114 : (x 3 2 && x 3 9).toNat = 0)
    (g115 : (x 2 3 && x 2 10).toNat = 0)
    (g116 : (x 1 4 && x 1 11).toNat = 0)
    (g117 : (x 0 5 && x 0 12).toNat = 0)
    (g118 : (x 3 5 && x 3 12).toNat = 0)
    (g119 : (x 1 7 && x 1 14).toNat = 0)
    (g120 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g121 : (x (-4) 2 && x (-4) 11).toNat = 0)
    (g122 : (x 3 2 && x 3 11).toNat = 0)
    (g123 : (x 2 3 && x 2 12).toNat = 0)
    (g124 : (x 1 4 && x 1 13).toNat = 0)
    (g125 : (x 0 5 && x 0 14).toNat = 0)
    (g126 : (x 3 3 && x 3 12).toNat = 0)
    (g127 : (x 2 4 && x 2 13).toNat = 0)
    (g128 : (x 1 5 && x 1 14).toNat = 0)
    (g129 : (x 3 4 && x 3 13).toNat = 0)
    (g130 : (x 3 5 && x 3 14).toNat = 0)
    (g131 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g132 : (x 2 4 && x 2 14).toNat = 0)
    (g133 : (x 3 1 && x 3 12).toNat = 0)
    (g134 : (x 1 3 && x 1 14).toNat = 0)
    (g135 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d34083 : (x (-1) 6 && x (-1) 13).toNat = 0 := by
    have r34084 := hand1 (x (-1) 6) (x (-1) 13)
    have b34085 := hb (x (-1) 6)
    have b34086 := hb (x (-1) 6 && x (-1) 13)
    clear * - r34084 b34085 b34086 g17
    omega
  have d34087 : (x (-1) 6 && x (-1) 11).toNat = 0 := by
    have r34088 := hand1 (x (-1) 6) (x (-1) 11)
    have b34089 := hb (x (-1) 6)
    have b34090 := hb (x (-1) 6 && x (-1) 11)
    clear * - r34088 b34089 b34090 g17
    omega
  cases h34091 : x (-1) 7
  · have f34092 : (x (-1) 7).toNat = 0 := by rw [h34091]; rfl
    have d34093 : (x (-1) 7 && x (-1) 13).toNat = 0 := by
      have r34094 := hand1 (x (-1) 7) (x (-1) 13)
      have b34095 := hb (x (-1) 7)
      have b34096 := hb (x (-1) 7 && x (-1) 13)
      clear * - r34094 b34095 b34096 f34092
      omega
    have d34097 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
      have r34098 := hand2 (x (-1) 1) (x (-1) 7)
      have b34099 := hb (x (-1) 7)
      have b34100 := hb (x (-1) 1 && x (-1) 7)
      clear * - r34098 b34099 b34100 f34092
      omega
    have d34101 : (x (-1) 7 && x (-1) 12).toNat = 0 := by
      have r34102 := hand1 (x (-1) 7) (x (-1) 12)
      have b34103 := hb (x (-1) 7)
      have b34104 := hb (x (-1) 7 && x (-1) 12)
      clear * - r34102 b34103 b34104 f34092
      omega
    have d34105 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
      have r34106 := hand2 (x (-1) 2) (x (-1) 7)
      have b34107 := hb (x (-1) 7)
      have b34108 := hb (x (-1) 2 && x (-1) 7)
      clear * - r34106 b34107 b34108 f34092
      omega
    have d34109 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
      have r34110 := hand1 (x (-1) 7) (x (-1) 11)
      have b34111 := hb (x (-1) 7)
      have b34112 := hb (x (-1) 7 && x (-1) 11)
      clear * - r34110 b34111 b34112 f34092
      omega
    have d34113 : (x (-1) 7 && x (-1) 8).toNat = 0 := by
      have r34114 := hand1 (x (-1) 7) (x (-1) 8)
      have b34115 := hb (x (-1) 7)
      have b34116 := hb (x (-1) 7 && x (-1) 8)
      clear * - r34114 b34115 b34116 f34092
      omega
    have d34117 : (x (-9) 8).toNat = 1 := by
      have r34118 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34119 := hb (x (-9) 8)
      have b34120 := hb (x (-1) 7)
      have b34121 := hb (x (-2) 1 && x (-2) 8)
      have b34122 := hb (x (-3) 2 && x (-3) 9)
      have b34123 := hb (x (-4) 3 && x (-4) 10)
      have b34124 := hb (x (-5) 4 && x (-5) 11)
      have b34125 := hb (x (-6) 5 && x (-6) 12)
      have b34126 := hb (x (-7) 6 && x (-7) 13)
      have b34127 := hb (x (-8) 7 && x (-8) 14)
      clear * - r34118 b34119 b34120 b34121 b34122 b34123 b34124 b34125 b34126 b34127 f34092 g106 g107 g108 g109 g110 g111 g112
      omega
    have d34128 : (x (-10) 9).toNat = 0 := by
      have r34129 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34130 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e34131 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e34132 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e34133 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e34134 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e34135 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b34136 := hb (x (-16) 7)
      have b34137 := hb (x (-15) 6)
      have b34138 := hb (x (-14) 5)
      have b34139 := hb (x (-13) 4)
      have b34140 := hb (x (-12) 11)
      have b34141 := hb (x (-11) 10)
      have b34142 := hb (x (-10) 9)
      have b34143 := hb (x (-9) 8)
      clear * - r34129 e34130 e34131 e34132 e34133 e34134 e34135 b34136 b34137 b34138 b34139 b34140 b34141 b34142 b34143 d34117
      omega
    have d34144 : (x (-11) 10).toNat = 0 := by
      have r34145 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34146 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e34147 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e34148 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e34149 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e34150 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e34151 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b34152 := hb (x (-16) 7)
      have b34153 := hb (x (-15) 6)
      have b34154 := hb (x (-14) 5)
      have b34155 := hb (x (-13) 4)
      have b34156 := hb (x (-12) 11)
      have b34157 := hb (x (-11) 10)
      have b34158 := hb (x (-10) 9)
      have b34159 := hb (x (-9) 8)
      clear * - r34145 e34146 e34147 e34148 e34149 e34150 e34151 b34152 b34153 b34154 b34155 b34156 b34157 b34158 b34159 d34117 d34128
      omega
    have d34160 : (x (-12) 11).toNat = 0 := by
      have r34161 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34162 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e34163 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e34164 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e34165 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e34166 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e34167 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b34168 := hb (x (-16) 7)
      have b34169 := hb (x (-15) 6)
      have b34170 := hb (x (-14) 5)
      have b34171 := hb (x (-13) 4)
      have b34172 := hb (x (-12) 11)
      have b34173 := hb (x (-11) 10)
      have b34174 := hb (x (-10) 9)
      have b34175 := hb (x (-9) 8)
      clear * - r34161 e34162 e34163 e34164 e34165 e34166 e34167 b34168 b34169 b34170 b34171 b34172 b34173 b34174 b34175 d34117 d34128 d34144
      omega
    have d34176 : (x (-13) 4).toNat = 0 := by
      have r34177 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e34178 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e34179 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e34180 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e34181 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e34182 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e34183 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have b34184 := hb (x (-16) 7)
      have b34185 := hb (x (-15) 6)
      have b34186 := hb (x (-14) 5)
      have b34187 := hb (x (-13) 4)
      have b34188 := hb (x (-12) 11)
      have b34189 := hb (x (-11) 10)
      have b34190 := hb (x (-10) 9)
      have b34191 := hb (x (-9) 8)
      clear * - r34177 e34178 e34179 e34180 e34181 e34182 e34183 b34184 b34185 b34186 b34187 b34188 b34189 b34190 b34191 d34117 d34128 d34144 d34160
      omega
    have d34192 : (x (-9) 8 && x (-9) 14).toNat = 1 := by
      have r34193 : 1 ≤ (x (-1) 6).toNat + (x (-2) 1 && x (-2) 7).toNat + (x (-3) 2 && x (-3) 8).toNat + (x (-4) 3 && x (-4) 9).toNat + (x (-5) 4 && x (-5) 10).toNat + (x (-6) 5 && x (-6) 11).toNat + (x (-7) 6 && x (-7) 12).toNat + (x (-8) 7 && x (-8) 13).toNat + (x (-9) 8 && x (-9) 14).toNat + (x (-10) 9).toNat := by have q := hcov6 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34194 := hb (x (-10) 9)
      have b34195 := hb (x (-1) 6)
      have b34196 := hb (x (-2) 1 && x (-2) 7)
      have b34197 := hb (x (-3) 2 && x (-3) 8)
      have b34198 := hb (x (-4) 3 && x (-4) 9)
      have b34199 := hb (x (-5) 4 && x (-5) 10)
      have b34200 := hb (x (-6) 5 && x (-6) 11)
      have b34201 := hb (x (-7) 6 && x (-7) 12)
      have b34202 := hb (x (-8) 7 && x (-8) 13)
      have b34203 := hb (x (-9) 8 && x (-9) 14)
      clear * - r34193 b34194 b34195 b34196 b34197 b34198 b34199 b34200 b34201 b34202 b34203 g17 g87 g88 g89 g90 g91 g92 g93 d34128
      omega
    have d34204 : (x (-9) 14).toNat = 1 := by
      have r34205 := hand2 (x (-9) 8) (x (-9) 14)
      have b34206 := hb (x (-9) 14)
      have b34207 := hb (x (-9) 8 && x (-9) 14)
      clear * - r34205 b34206 b34207 d34192
      omega
    have d34208 : (x (-10) 1).toNat = 0 := by
      have r34209 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b34210 := hb (x (-10) 1)
      have b34211 := hb (x (-9) 14)
      clear * - r34209 b34210 b34211 d34204
      omega
    have d34212 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
      have r34213 := hand1 (x (-10) 1) (x (-10) 14)
      have b34214 := hb (x (-10) 1)
      have b34215 := hb (x (-10) 1 && x (-10) 14)
      clear * - r34213 b34214 b34215 d34208
      omega
    have d34216 : (x (-10) 1 && x (-10) 12).toNat = 0 := by
      have r34217 := hand1 (x (-10) 1) (x (-10) 12)
      have b34218 := hb (x (-10) 1)
      have b34219 := hb (x (-10) 1 && x (-10) 12)
      clear * - r34217 b34218 b34219 d34208
      omega
    have d34220 : (x (-10) 13).toNat = 0 := by
      have r34221 : (x (-10) 13).toNat ≤ (x (-10) 1).toNat := himp _ _ (hp13 (-10))
      have b34222 := hb (x (-10) 1)
      have b34223 := hb (x (-10) 13)
      clear * - r34221 b34222 b34223 d34208
      omega
    have d34224 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
      have r34225 := hand2 (x (-10) 2) (x (-10) 13)
      have b34226 := hb (x (-10) 13)
      have b34227 := hb (x (-10) 2 && x (-10) 13)
      clear * - r34225 b34226 b34227 d34220
      omega
    have d34228 : (x (-10) 8 && x (-10) 13).toNat = 0 := by
      have r34229 := hand2 (x (-10) 8) (x (-10) 13)
      have b34230 := hb (x (-10) 13)
      have b34231 := hb (x (-10) 8 && x (-10) 13)
      clear * - r34229 b34230 b34231 d34220
      omega
    cases h34232 : x 1 7
    · have f34233 : (x 1 7).toNat = 0 := by rw [h34232]; rfl
      cases h34234 : x 2 5
      · have f34235 : (x 2 5).toNat = 0 := by rw [h34234]; rfl
        have d34236 : (x 2 5 && x 2 14).toNat = 0 := by
          have r34237 := hand1 (x 2 5) (x 2 14)
          have b34238 := hb (x 2 5)
          have b34239 := hb (x 2 5 && x 2 14)
          clear * - r34237 b34238 b34239 f34235
          omega
        cases h34240 : x 2 6
        · exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100000 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125 g126 g127 g128 g129 g130 g131 g132 g133 g134 g135 h34091 h34232 h34234 h34240
        · exact cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100001 x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125 g126 g127 g128 g129 g130 g131 g132 g133 g134 g135 h34091 h34232 h34234 h34240
      · have f38033 : (x 2 5).toNat = 1 := by rw [h34234]; rfl
        have d38034 : (x 7 8).toNat = 0 := by
          have r38035 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e38036 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e38037 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e38038 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e38039 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e38040 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e38041 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b38042 := hb (x 0 7)
          have b38043 := hb (x 1 6)
          have b38044 := hb (x 2 5)
          have b38045 := hb (x 3 4)
          have b38046 := hb (x 4 11)
          have b38047 := hb (x 5 10)
          have b38048 := hb (x 6 9)
          have b38049 := hb (x 7 8)
          clear * - r38035 e38036 e38037 e38038 e38039 e38040 e38041 b38042 b38043 b38044 b38045 b38046 b38047 b38048 b38049 g49 f38033 g36 g27
          omega
        have d38050 : (x 6 9).toNat = 0 := by
          have r38051 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e38052 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e38053 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e38054 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e38055 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e38056 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e38057 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b38058 := hb (x 0 7)
          have b38059 := hb (x 1 6)
          have b38060 := hb (x 2 5)
          have b38061 := hb (x 3 4)
          have b38062 := hb (x 4 11)
          have b38063 := hb (x 5 10)
          have b38064 := hb (x 6 9)
          have b38065 := hb (x 7 8)
          clear * - r38051 e38052 e38053 e38054 e38055 e38056 e38057 b38058 b38059 b38060 b38061 b38062 b38063 b38064 b38065 d38034 g49 f38033 g36 g27
          omega
        have d38066 : (x 5 10).toNat = 0 := by
          have r38067 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e38068 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e38069 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e38070 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e38071 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e38072 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e38073 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b38074 := hb (x 0 7)
          have b38075 := hb (x 1 6)
          have b38076 := hb (x 2 5)
          have b38077 := hb (x 3 4)
          have b38078 := hb (x 4 11)
          have b38079 := hb (x 5 10)
          have b38080 := hb (x 6 9)
          have b38081 := hb (x 7 8)
          clear * - r38067 e38068 e38069 e38070 e38071 e38072 e38073 b38074 b38075 b38076 b38077 b38078 b38079 b38080 b38081 d38034 d38050 g49 f38033 g36 g27
          omega
        have d38082 : (x 5 1 && x 5 10).toNat = 0 := by
          have r38083 := hand2 (x 5 1) (x 5 10)
          have b38084 := hb (x 5 10)
          have b38085 := hb (x 5 1 && x 5 10)
          clear * - r38083 b38084 b38085 d38066
          omega
        have d38086 : (x 4 2 && x 4 11).toNat = 1 := by
          have r38087 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b38088 := hb (x 0 6)
          have b38089 := hb (x 6 9)
          have b38090 := hb (x 5 1 && x 5 10)
          have b38091 := hb (x 4 2 && x 4 11)
          have b38092 := hb (x 3 3 && x 3 12)
          have b38093 := hb (x 2 4 && x 2 13)
          have b38094 := hb (x 1 5 && x 1 14)
          clear * - r38087 b38088 b38089 b38090 b38091 b38092 b38093 b38094 d38050 d38082 g126 g127 g128 g26
          omega
        have d38095 : (x 4 11).toNat = 1 := by
          have r38096 := hand2 (x 4 2) (x 4 11)
          have b38097 := hb (x 4 11)
          have b38098 := hb (x 4 2 && x 4 11)
          clear * - r38096 b38097 b38098 d38086
          omega
        have r38099 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38100 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e38101 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e38102 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e38103 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e38104 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e38105 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b38106 := hb (x 0 7)
        have b38107 := hb (x 1 6)
        have b38108 := hb (x 2 5)
        have b38109 := hb (x 3 4)
        have b38110 := hb (x 4 11)
        have b38111 := hb (x 5 10)
        have b38112 := hb (x 6 9)
        have b38113 := hb (x 7 8)
        linarith only [r38099, e38100, e38101, e38102, e38103, e38104, e38105, b38106, b38107, b38108, b38109, b38110, b38111, b38112, b38113, d38034, d38050, d38066, d38095, g49, f38033, g36, g27]
    · have f38114 : (x 1 7).toNat = 1 := by rw [h34232]; rfl
      have d38115 : (x 8 8).toNat = 0 := by
        have r38116 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38117 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38118 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38119 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38120 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38121 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e38122 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b38123 := hb (x 1 7)
        have b38124 := hb (x 2 6)
        have b38125 := hb (x 3 5)
        have b38126 := hb (x 4 4)
        have b38127 := hb (x 5 11)
        have b38128 := hb (x 6 10)
        have b38129 := hb (x 7 9)
        have b38130 := hb (x 8 8)
        clear * - r38116 e38117 e38118 e38119 e38120 e38121 e38122 b38123 b38124 b38125 b38126 b38127 b38128 b38129 b38130 f38114
        omega
      have d38131 : (x 8 4 && x 8 8).toNat = 0 := by
        have r38132 := hand2 (x 8 4) (x 8 8)
        have b38133 := hb (x 8 8)
        have b38134 := hb (x 8 4 && x 8 8)
        clear * - r38132 b38133 b38134 d38115
        omega
      have d38135 : (x 7 9).toNat = 0 := by
        have r38136 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38137 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38138 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38139 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38140 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38141 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e38142 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b38143 := hb (x 1 7)
        have b38144 := hb (x 2 6)
        have b38145 := hb (x 3 5)
        have b38146 := hb (x 4 4)
        have b38147 := hb (x 5 11)
        have b38148 := hb (x 6 10)
        have b38149 := hb (x 7 9)
        have b38150 := hb (x 8 8)
        clear * - r38136 e38137 e38138 e38139 e38140 e38141 e38142 b38143 b38144 b38145 b38146 b38147 b38148 b38149 b38150 d38115 f38114
        omega
      have d38151 : (x 7 5 && x 7 9).toNat = 0 := by
        have r38152 := hand2 (x 7 5) (x 7 9)
        have b38153 := hb (x 7 9)
        have b38154 := hb (x 7 5 && x 7 9)
        clear * - r38152 b38153 b38154 d38135
        omega
      have d38155 : (x 6 10).toNat = 0 := by
        have r38156 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38157 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38158 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38159 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38160 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38161 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e38162 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b38163 := hb (x 1 7)
        have b38164 := hb (x 2 6)
        have b38165 := hb (x 3 5)
        have b38166 := hb (x 4 4)
        have b38167 := hb (x 5 11)
        have b38168 := hb (x 6 10)
        have b38169 := hb (x 7 9)
        have b38170 := hb (x 8 8)
        clear * - r38156 e38157 e38158 e38159 e38160 e38161 e38162 b38163 b38164 b38165 b38166 b38167 b38168 b38169 b38170 d38115 d38135 f38114
        omega
      have d38171 : (x 6 6 && x 6 10).toNat = 0 := by
        have r38172 := hand2 (x 6 6) (x 6 10)
        have b38173 := hb (x 6 10)
        have b38174 := hb (x 6 6 && x 6 10)
        clear * - r38172 b38173 b38174 d38155
        omega
      have d38175 : (x 5 11).toNat = 0 := by
        have r38176 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38177 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38178 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38179 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38180 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38181 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e38182 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b38183 := hb (x 1 7)
        have b38184 := hb (x 2 6)
        have b38185 := hb (x 3 5)
        have b38186 := hb (x 4 4)
        have b38187 := hb (x 5 11)
        have b38188 := hb (x 6 10)
        have b38189 := hb (x 7 9)
        have b38190 := hb (x 8 8)
        clear * - r38176 e38177 e38178 e38179 e38180 e38181 e38182 b38183 b38184 b38185 b38186 b38187 b38188 b38189 b38190 d38115 d38135 d38155 f38114
        omega
      have d38191 : (x 5 1 && x 5 11).toNat = 0 := by
        have r38192 := hand2 (x 5 1) (x 5 11)
        have b38193 := hb (x 5 11)
        have b38194 := hb (x 5 1 && x 5 11)
        clear * - r38192 b38193 b38194 d38175
        omega
      have d38195 : (x 5 7 && x 5 11).toNat = 0 := by
        have r38196 := hand2 (x 5 7) (x 5 11)
        have b38197 := hb (x 5 11)
        have b38198 := hb (x 5 7 && x 5 11)
        clear * - r38196 b38197 b38198 d38175
        omega
      have d38199 : (x 4 4).toNat = 0 := by
        have r38200 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38201 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38202 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38203 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38204 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38205 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e38206 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b38207 := hb (x 1 7)
        have b38208 := hb (x 2 6)
        have b38209 := hb (x 3 5)
        have b38210 := hb (x 4 4)
        have b38211 := hb (x 5 11)
        have b38212 := hb (x 6 10)
        have b38213 := hb (x 7 9)
        have b38214 := hb (x 8 8)
        clear * - r38200 e38201 e38202 e38203 e38204 e38205 e38206 b38207 b38208 b38209 b38210 b38211 b38212 b38213 b38214 d38115 d38135 d38155 d38175 f38114
        omega
      have d38215 : (x 4 4 && x 4 11).toNat = 0 := by
        have r38216 := hand1 (x 4 4) (x 4 11)
        have b38217 := hb (x 4 4)
        have b38218 := hb (x 4 4 && x 4 11)
        clear * - r38216 b38217 b38218 d38199
        omega
      have d38219 : (x 3 5).toNat = 0 := by
        have r38220 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38221 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38222 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38223 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38224 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38225 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e38226 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b38227 := hb (x 1 7)
        have b38228 := hb (x 2 6)
        have b38229 := hb (x 3 5)
        have b38230 := hb (x 4 4)
        have b38231 := hb (x 5 11)
        have b38232 := hb (x 6 10)
        have b38233 := hb (x 7 9)
        have b38234 := hb (x 8 8)
        clear * - r38220 e38221 e38222 e38223 e38224 e38225 e38226 b38227 b38228 b38229 b38230 b38231 b38232 b38233 b38234 d38115 d38135 d38155 d38175 d38199 f38114
        omega
      have d38235 : (x 2 6).toNat = 0 := by
        have r38236 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e38237 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e38238 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e38239 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e38240 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e38241 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e38242 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b38243 := hb (x 1 7)
        have b38244 := hb (x 2 6)
        have b38245 := hb (x 3 5)
        have b38246 := hb (x 4 4)
        have b38247 := hb (x 5 11)
        have b38248 := hb (x 6 10)
        have b38249 := hb (x 7 9)
        have b38250 := hb (x 8 8)
        clear * - r38236 e38237 e38238 e38239 e38240 e38241 e38242 b38243 b38244 b38245 b38246 b38247 b38248 b38249 b38250 d38115 d38135 d38155 d38175 d38199 d38219 f38114
        omega
      have d38251 : (x 2 6 && x 2 13).toNat = 0 := by
        have r38252 := hand1 (x 2 6) (x 2 13)
        have b38253 := hb (x 2 6)
        have b38254 := hb (x 2 6 && x 2 13)
        clear * - r38252 b38253 b38254 d38235
        omega
      have r38255 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r38256 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e38257 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
      have e38258 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
      have e38259 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
      have e38260 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
      have e38261 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
      have e38262 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
      have r38263 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e38264 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e38265 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have r38266 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := by have q := hcov4 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e38267 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
      have e38268 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
      have r38269 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r38270 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r38271 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r38272 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r38273 := hand2 (x 10 2) (x 10 6)
      have r38274 := hand2 (x 9 3) (x 9 7)
      have r38275 := hand2 (x 7 1) (x 7 8)
      have r38276 := hand2 (x 6 2) (x 6 9)
      have r38277 := hand2 (x 5 3) (x 5 10)
      have r38278 := hand2 (x 14 1) (x 14 10)
      have r38279 := hand2 (x 13 2) (x 13 11)
      have r38280 := hand1 (x 12 3) (x 12 12)
      have r38281 := hand1 (x 11 4) (x 11 13)
      have r38282 := hand1 (x 10 5) (x 10 14)
      have r38283 := hand2 (x 4 2) (x 4 12)
      have r38284 := hand2 (x 3 3) (x 3 13)
      have r38285 := hand1 (x 2 2) (x 2 13)
      linarith only [r38255, r38256, e38257, e38258, e38259, e38260, e38261, e38262, r38263, e38264, e38265, r38266, e38267, e38268, r38269, r38270, r38271, r38272, r38273, r38274, r38275, r38276, r38277, r38278, r38279, r38280, r38281, r38282, r38283, r38284, r38285, g25, g28, g34, g35, g40, g41, g45, g46, g52, d38155, d38131, d38151, d38171, d38195, g66, g67, d38215, g118, d38251, g119, d38191, g132, g133, g134]
  · have f38345 : (x (-1) 7).toNat = 1 := by rw [h34091]; rfl
    have d38346 : (x 6 8).toNat = 0 := by
      have r38347 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e38348 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e38349 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e38350 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e38351 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e38352 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e38353 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b38354 := hb (x (-1) 7)
      have b38355 := hb (x 0 6)
      have b38356 := hb (x 1 5)
      have b38357 := hb (x 2 4)
      have b38358 := hb (x 3 11)
      have b38359 := hb (x 4 10)
      have b38360 := hb (x 5 9)
      have b38361 := hb (x 6 8)
      clear * - r38347 e38348 e38349 e38350 e38351 e38352 e38353 b38354 b38355 b38356 b38357 b38358 b38359 b38360 b38361 g43 g35 g26 f38345
      omega
    have d38362 : (x 5 9).toNat = 0 := by
      have r38363 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e38364 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e38365 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e38366 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e38367 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e38368 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e38369 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b38370 := hb (x (-1) 7)
      have b38371 := hb (x 0 6)
      have b38372 := hb (x 1 5)
      have b38373 := hb (x 2 4)
      have b38374 := hb (x 3 11)
      have b38375 := hb (x 4 10)
      have b38376 := hb (x 5 9)
      have b38377 := hb (x 6 8)
      clear * - r38363 e38364 e38365 e38366 e38367 e38368 e38369 b38370 b38371 b38372 b38373 b38374 b38375 b38376 b38377 d38346 g43 g35 g26 f38345
      omega
    have d38378 : (x 4 1 && x 4 10).toNat = 1 := by
      have r38379 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b38380 := hb (x (-1) 6)
      have b38381 := hb (x 5 9)
      have b38382 := hb (x 4 1 && x 4 10)
      have b38383 := hb (x 3 2 && x 3 11)
      have b38384 := hb (x 2 3 && x 2 12)
      have b38385 := hb (x 1 4 && x 1 13)
      have b38386 := hb (x 0 5 && x 0 14)
      clear * - r38379 b38380 b38381 b38382 b38383 b38384 b38385 b38386 d38362 g122 g123 g124 g125 g17
      omega
    have d38387 : (x 4 10).toNat = 1 := by
      have r38388 := hand2 (x 4 1) (x 4 10)
      have b38389 := hb (x 4 10)
      have b38390 := hb (x 4 1 && x 4 10)
      clear * - r38388 b38389 b38390 d38378
      omega
    have d38391 : (x 4 2).toNat = 1 := by
      have r38392 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
      have b38393 := hb (x 4 2)
      have b38394 := hb (x 4 10)
      clear * - r38392 b38393 b38394 d38387
      omega
    have d38395 : (x 6 12).toNat = 0 := by
      have r38396 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e38397 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e38398 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b38399 := hb (x 3 3)
      have b38400 := hb (x 4 2)
      have b38401 := hb (x 5 13)
      have b38402 := hb (x 6 12)
      clear * - r38396 e38397 e38398 b38399 b38400 b38401 b38402 d38391
      omega
    have d38403 : (x 5 13).toNat = 0 := by
      have r38404 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e38405 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e38406 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b38407 := hb (x 3 3)
      have b38408 := hb (x 4 2)
      have b38409 := hb (x 5 13)
      have b38410 := hb (x 6 12)
      clear * - r38404 e38405 e38406 b38407 b38408 b38409 b38410 d38395 d38391
      omega
    have d38411 : (x 3 3).toNat = 0 := by
      have r38412 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e38413 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e38414 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b38415 := hb (x 3 3)
      have b38416 := hb (x 4 2)
      have b38417 := hb (x 5 13)
      have b38418 := hb (x 6 12)
      clear * - r38412 e38413 e38414 b38415 b38416 b38417 b38418 d38395 d38403 d38391
      omega
    have d38419 : (x 3 11).toNat = 0 := by
      have r38420 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b38421 := hb (x 3 3)
      have b38422 := hb (x 3 11)
      clear * - r38420 b38421 b38422 d38411
      omega
    have r38423 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e38424 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e38425 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e38426 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e38427 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e38428 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e38429 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b38430 := hb (x (-1) 7)
    have b38431 := hb (x 0 6)
    have b38432 := hb (x 1 5)
    have b38433 := hb (x 2 4)
    have b38434 := hb (x 3 11)
    have b38435 := hb (x 4 10)
    have b38436 := hb (x 5 9)
    have b38437 := hb (x 6 8)
    linarith only [r38423, e38424, e38425, e38426, e38427, e38428, e38429, b38430, b38431, b38432, b38433, b38434, b38435, b38436, b38437, d38346, d38362, d38387, d38419, g43, g35, g26, f38345]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000110 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 7).toNat = 0)
    (g1 : (x (-5) 6).toNat = 0)
    (g2 : (x (-4) 5).toNat = 0)
    (g3 : (x (-4) 7).toNat = 0)
    (g4 : (x (-4) 11).toNat = 0)
    (g5 : (x (-3) 4).toNat = 0)
    (g6 : (x (-3) 6).toNat = 0)
    (g7 : (x (-3) 10).toNat = 0)
    (g8 : (x (-3) 11).toNat = 0)
    (g9 : (x (-2) 3).toNat = 0)
    (g10 : (x (-2) 5).toNat = 0)
    (g11 : (x (-2) 9).toNat = 0)
    (g12 : (x (-2) 10).toNat = 0)
    (g13 : (x (-2) 11).toNat = 0)
    (g14 : (x (-2) 13).toNat = 0)
    (g15 : (x (-1) 2).toNat = 1)
    (g16 : (x (-1) 4).toNat = 1)
    (g17 : (x (-1) 6).toNat = 0)
    (g18 : (x (-1) 8).toNat = 1)
    (g19 : (x (-1) 9).toNat = 1)
    (g20 : (x (-1) 10).toNat = 1)
    (g21 : (x (-1) 11).toNat = 1)
    (g22 : (x (-1) 13).toNat = 1)
    (g23 : (x 0 1).toNat = 1)
    (g24 : (x 0 3).toNat = 0)
    (g25 : (x 0 4).toNat = 0)
    (g26 : (x 0 6).toNat = 0)
    (g27 : (x 0 7).toNat = 0)
    (g28 : (x 0 8).toNat = 0)
    (g29 : (x 0 9).toNat = 0)
    (g30 : (x 0 10).toNat = 0)
    (g31 : (x 0 11).toNat = 0)
    (g32 : (x 0 12).toNat = 0)
    (g33 : (x 1 2).toNat = 0)
    (g34 : (x 1 3).toNat = 0)
    (g35 : (x 1 5).toNat = 0)
    (g36 : (x 1 6).toNat = 0)
    (g37 : (x 1 8).toNat = 0)
    (g38 : (x 1 9).toNat = 0)
    (g39 : (x 1 10).toNat = 0)
    (g40 : (x 1 11).toNat = 0)
    (g41 : (x 1 14).toNat = 0)
    (g42 : (x 2 1).toNat = 1)
    (g43 : (x 2 4).toNat = 0)
    (g44 : (x 2 8).toNat = 0)
    (g45 : (x 2 10).toNat = 0)
    (g46 : (x 2 13).toNat = 1)
    (g47 : (x 2 14).toNat = 1)
    (g48 : (x 3 2).toNat = 0)
    (g49 : (x 3 4).toNat = 0)
    (g50 : (x 3 6).toNat = 0)
    (g51 : (x 3 9).toNat = 0)
    (g52 : (x 3 12).toNat = 0)
    (g53 : (x 4 8).toNat = 0)
    (g54 : (x 3 3 && x 3 4).toNat = 0)
    (g55 : (x 2 4 && x 2 5).toNat = 0)
    (g56 : (x 1 5 && x 1 6).toNat = 0)
    (g57 : (x 0 6 && x 0 7).toNat = 0)
    (g58 : (x (-2) 8 && x (-2) 9).toNat = 0)
    (g59 : (x (-3) 9 && x (-3) 10).toNat = 0)
    (g60 : (x (-4) 10 && x (-4) 11).toNat = 0)
    (g61 : (x 2 4 && x 2 8).toNat = 0)
    (g62 : (x 1 5 && x 1 9).toNat = 0)
    (g63 : (x 0 6 && x 0 10).toNat = 0)
    (g64 : (x 3 8 && x 3 12).toNat = 0)
    (g65 : (x 2 9 && x 2 13).toNat = 0)
    (g66 : (x 4 8 && x 4 12).toNat = 0)
    (g67 : (x 3 9 && x 3 13).toNat = 0)
    (g68 : (x (-3) 1 && x (-3) 6).toNat = 0)
    (g69 : (x (-4) 2 && x (-4) 7).toNat = 0)
    (g70 : (x 0 1 && x 0 6).toNat = 0)
    (g71 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g72 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g73 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g74 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g75 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g76 : (x 3 2 && x 3 7).toNat = 0)
    (g77 : (x 2 3 && x 2 8).toNat = 0)
    (g78 : (x 1 4 && x 1 9).toNat = 0)
    (g79 : (x 0 5 && x 0 10).toNat = 0)
    (g80 : (x 3 3 && x 3 8).toNat = 0)
    (g81 : (x 2 4 && x 2 9).toNat = 0)
    (g82 : (x 1 5 && x 1 10).toNat = 0)
    (g83 : (x 0 6 && x 0 11).toNat = 0)
    (g84 : (x (-2) 8 && x (-2) 13).toNat = 0)
    (g85 : (x 3 8 && x 3 13).toNat = 0)
    (g86 : (x 2 9 && x 2 14).toNat = 0)
    (g87 : (x (-2) 1 && x (-2) 7).toNat = 0)
    (g88 : (x (-3) 2 && x (-3) 8).toNat = 0)
    (g89 : (x (-4) 3 && x (-4) 9).toNat = 0)
    (g90 : (x (-5) 4 && x (-5) 10).toNat = 0)
    (g91 : (x (-6) 5 && x (-6) 11).toNat = 0)
    (g92 : (x (-7) 6 && x (-7) 12).toNat = 0)
    (g93 : (x (-8) 7 && x (-8) 13).toNat = 0)
    (g94 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g95 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g96 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g97 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g98 : (x (-6) 6 && x (-6) 12).toNat = 0)
    (g99 : (x (-7) 7 && x (-7) 13).toNat = 0)
    (g100 : (x 4 2 && x 4 8).toNat = 0)
    (g101 : (x 3 3 && x 3 9).toNat = 0)
    (g102 : (x 2 4 && x 2 10).toNat = 0)
    (g103 : (x 1 5 && x 1 11).toNat = 0)
    (g104 : (x 0 6 && x 0 12).toNat = 0)
    (g105 : (x 4 8 && x 4 14).toNat = 0)
    (g106 : (x (-2) 1 && x (-2) 8).toNat = 0)
    (g107 : (x (-3) 2 && x (-3) 9).toNat = 0)
    (g108 : (x (-4) 3 && x (-4) 10).toNat = 0)
    (g109 : (x (-5) 4 && x (-5) 11).toNat = 0)
    (g110 : (x (-6) 5 && x (-6) 12).toNat = 0)
    (g111 : (x (-7) 6 && x (-7) 13).toNat = 0)
    (g112 : (x (-8) 7 && x (-8) 14).toNat = 0)
    (g113 : (x 4 1 && x 4 8).toNat = 0)
    (g114 : (x 3 2 && x 3 9).toNat = 0)
    (g115 : (x 2 3 && x 2 10).toNat = 0)
    (g116 : (x 1 4 && x 1 11).toNat = 0)
    (g117 : (x 0 5 && x 0 12).toNat = 0)
    (g118 : (x 3 5 && x 3 12).toNat = 0)
    (g119 : (x 1 7 && x 1 14).toNat = 0)
    (g120 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g121 : (x (-4) 2 && x (-4) 11).toNat = 0)
    (g122 : (x 3 2 && x 3 11).toNat = 0)
    (g123 : (x 2 3 && x 2 12).toNat = 0)
    (g124 : (x 1 4 && x 1 13).toNat = 0)
    (g125 : (x 0 5 && x 0 14).toNat = 0)
    (g126 : (x 3 3 && x 3 12).toNat = 0)
    (g127 : (x 2 4 && x 2 13).toNat = 0)
    (g128 : (x 1 5 && x 1 14).toNat = 0)
    (g129 : (x 3 4 && x 3 13).toNat = 0)
    (g130 : (x 3 5 && x 3 14).toNat = 0)
    (g131 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g132 : (x 2 4 && x 2 14).toNat = 0)
    (g133 : (x 3 1 && x 3 12).toNat = 0)
    (g134 : (x 1 3 && x 1 14).toNat = 0)
    (g135 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0000110000110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125 g126 g127 g128 g129 g130 g131 g132 g133 g134 g135
