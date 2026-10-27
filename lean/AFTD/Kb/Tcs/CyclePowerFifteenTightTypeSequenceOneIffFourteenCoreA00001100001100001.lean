import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100001

Topic: combinatorics   Node: e20fde5a5ac9

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 140 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100001_aux (x : ℤ → Fin 16 → Bool)
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
    (h34091 : x (-1) 7 = false)
    (h34232 : x 1 7 = false)
    (h34234 : x 2 5 = false)
    (h34240 : x 2 6 = true)
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
  have f34092 : (x (-1) 7).toNat = 0 := by rw [h34091]; rfl
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
  have f34233 : (x 1 7).toNat = 0 := by rw [h34232]; rfl
  have f34235 : (x 2 5).toNat = 0 := by rw [h34234]; rfl
  have d34236 : (x 2 5 && x 2 14).toNat = 0 := by
    have r34237 := hand1 (x 2 5) (x 2 14)
    have b34238 := hb (x 2 5)
    have b34239 := hb (x 2 5 && x 2 14)
    clear * - r34237 b34238 b34239 f34235
    omega
  have f36289 : (x 2 6).toNat = 1 := by rw [h34240]; rfl
  have d36290 : (x 8 8).toNat = 0 := by
    have r36291 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36292 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e36293 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e36294 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e36295 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e36296 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e36297 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b36298 := hb (x 1 7)
    have b36299 := hb (x 2 6)
    have b36300 := hb (x 3 5)
    have b36301 := hb (x 4 4)
    have b36302 := hb (x 5 11)
    have b36303 := hb (x 6 10)
    have b36304 := hb (x 7 9)
    have b36305 := hb (x 8 8)
    clear * - r36291 e36292 e36293 e36294 e36295 e36296 e36297 b36298 b36299 b36300 b36301 b36302 b36303 b36304 b36305 f36289 f34233
    omega
  have d36306 : (x 8 8 && x 8 13).toNat = 0 := by
    have r36307 := hand1 (x 8 8) (x 8 13)
    have b36308 := hb (x 8 8)
    have b36309 := hb (x 8 8 && x 8 13)
    clear * - r36307 b36308 b36309 d36290
    omega
  have d36310 : (x 8 3 && x 8 8).toNat = 0 := by
    have r36311 := hand2 (x 8 3) (x 8 8)
    have b36312 := hb (x 8 8)
    have b36313 := hb (x 8 3 && x 8 8)
    clear * - r36311 b36312 b36313 d36290
    omega
  have d36314 : (x 8 8 && x 8 12).toNat = 0 := by
    have r36315 := hand1 (x 8 8) (x 8 12)
    have b36316 := hb (x 8 8)
    have b36317 := hb (x 8 8 && x 8 12)
    clear * - r36315 b36316 b36317 d36290
    omega
  have d36318 : (x 7 9).toNat = 0 := by
    have r36319 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36320 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e36321 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e36322 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e36323 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e36324 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e36325 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b36326 := hb (x 1 7)
    have b36327 := hb (x 2 6)
    have b36328 := hb (x 3 5)
    have b36329 := hb (x 4 4)
    have b36330 := hb (x 5 11)
    have b36331 := hb (x 6 10)
    have b36332 := hb (x 7 9)
    have b36333 := hb (x 8 8)
    clear * - r36319 e36320 e36321 e36322 e36323 e36324 e36325 b36326 b36327 b36328 b36329 b36330 b36331 b36332 b36333 d36290 f36289 f34233
    omega
  have d36334 : (x 7 9 && x 7 14).toNat = 0 := by
    have r36335 := hand1 (x 7 9) (x 7 14)
    have b36336 := hb (x 7 9)
    have b36337 := hb (x 7 9 && x 7 14)
    clear * - r36335 b36336 b36337 d36318
    omega
  have d36338 : (x 7 4 && x 7 9).toNat = 0 := by
    have r36339 := hand2 (x 7 4) (x 7 9)
    have b36340 := hb (x 7 9)
    have b36341 := hb (x 7 4 && x 7 9)
    clear * - r36339 b36340 b36341 d36318
    omega
  have d36342 : (x 7 9 && x 7 13).toNat = 0 := by
    have r36343 := hand1 (x 7 9) (x 7 13)
    have b36344 := hb (x 7 9)
    have b36345 := hb (x 7 9 && x 7 13)
    clear * - r36343 b36344 b36345 d36318
    omega
  have d36346 : (x 6 10).toNat = 0 := by
    have r36347 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36348 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e36349 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e36350 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e36351 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e36352 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e36353 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b36354 := hb (x 1 7)
    have b36355 := hb (x 2 6)
    have b36356 := hb (x 3 5)
    have b36357 := hb (x 4 4)
    have b36358 := hb (x 5 11)
    have b36359 := hb (x 6 10)
    have b36360 := hb (x 7 9)
    have b36361 := hb (x 8 8)
    clear * - r36347 e36348 e36349 e36350 e36351 e36352 e36353 b36354 b36355 b36356 b36357 b36358 b36359 b36360 b36361 d36290 d36318 f36289 f34233
    omega
  have d36362 : (x 6 1 && x 6 10).toNat = 0 := by
    have r36363 := hand2 (x 6 1) (x 6 10)
    have b36364 := hb (x 6 10)
    have b36365 := hb (x 6 1 && x 6 10)
    clear * - r36363 b36364 b36365 d36346
    omega
  have d36366 : (x 6 5 && x 6 10).toNat = 0 := by
    have r36367 := hand2 (x 6 5) (x 6 10)
    have b36368 := hb (x 6 10)
    have b36369 := hb (x 6 5 && x 6 10)
    clear * - r36367 b36368 b36369 d36346
    omega
  have d36370 : (x 5 11).toNat = 0 := by
    have r36371 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36372 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e36373 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e36374 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e36375 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e36376 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e36377 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b36378 := hb (x 1 7)
    have b36379 := hb (x 2 6)
    have b36380 := hb (x 3 5)
    have b36381 := hb (x 4 4)
    have b36382 := hb (x 5 11)
    have b36383 := hb (x 6 10)
    have b36384 := hb (x 7 9)
    have b36385 := hb (x 8 8)
    clear * - r36371 e36372 e36373 e36374 e36375 e36376 e36377 b36378 b36379 b36380 b36381 b36382 b36383 b36384 b36385 d36290 d36318 d36346 f36289 f34233
    omega
  have d36386 : (x 5 1 && x 5 11).toNat = 0 := by
    have r36387 := hand2 (x 5 1) (x 5 11)
    have b36388 := hb (x 5 11)
    have b36389 := hb (x 5 1 && x 5 11)
    clear * - r36387 b36388 b36389 d36370
    omega
  have d36390 : (x 5 2 && x 5 11).toNat = 0 := by
    have r36391 := hand2 (x 5 2) (x 5 11)
    have b36392 := hb (x 5 11)
    have b36393 := hb (x 5 2 && x 5 11)
    clear * - r36391 b36392 b36393 d36370
    omega
  have d36394 : (x 4 3 && x 4 12).toNat = 1 := by
    have r36395 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36396 := hb (x 1 6)
    have b36397 := hb (x 7 9)
    have b36398 := hb (x 6 1 && x 6 10)
    have b36399 := hb (x 5 2 && x 5 11)
    have b36400 := hb (x 4 3 && x 4 12)
    have b36401 := hb (x 3 4 && x 3 13)
    have b36402 := hb (x 2 5 && x 2 14)
    clear * - r36395 b36396 b36397 b36398 b36399 b36400 b36401 b36402 d36318 d36362 d36390 g129 d34236 g36
    omega
  have d36403 : (x 4 12).toNat = 1 := by
    have r36404 := hand2 (x 4 3) (x 4 12)
    have b36405 := hb (x 4 12)
    have b36406 := hb (x 4 3 && x 4 12)
    clear * - r36404 b36405 b36406 d36394
    omega
  have d36407 : (x 3 13).toNat = 0 := by
    have r36408 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36409 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e36410 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b36411 := hb (x 1 3)
    have b36412 := hb (x 2 2)
    have b36413 := hb (x 3 13)
    have b36414 := hb (x 4 12)
    clear * - r36408 e36409 e36410 b36411 b36412 b36413 b36414 d36403 g34
    omega
  have d36415 : (x 3 3 && x 3 13).toNat = 0 := by
    have r36416 := hand2 (x 3 3) (x 3 13)
    have b36417 := hb (x 3 13)
    have b36418 := hb (x 3 3 && x 3 13)
    clear * - r36416 b36417 b36418 d36407
    omega
  have d36419 : (x 4 2 && x 4 12).toNat = 1 := by
    have r36420 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36421 := hb (x 1 5)
    have b36422 := hb (x 6 10)
    have b36423 := hb (x 5 1 && x 5 11)
    have b36424 := hb (x 4 2 && x 4 12)
    have b36425 := hb (x 3 3 && x 3 13)
    have b36426 := hb (x 2 4 && x 2 14)
    clear * - r36420 b36421 b36422 b36423 b36424 b36425 b36426 d36346 d36386 d36415 g132 g35
    omega
  have d36427 : (x 4 2).toNat = 1 := by
    have r36428 := hand1 (x 4 2) (x 4 12)
    have b36429 := hb (x 4 2)
    have b36430 := hb (x 4 2 && x 4 12)
    clear * - r36428 b36429 b36430 d36419
    omega
  have d36431 : (x 6 12).toNat = 0 := by
    have r36432 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36433 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e36434 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b36435 := hb (x 3 3)
    have b36436 := hb (x 4 2)
    have b36437 := hb (x 5 13)
    have b36438 := hb (x 6 12)
    clear * - r36432 e36433 e36434 b36435 b36436 b36437 b36438 d36427
    omega
  have d36439 : (x 6 2 && x 6 12).toNat = 0 := by
    have r36440 := hand2 (x 6 2) (x 6 12)
    have b36441 := hb (x 6 12)
    have b36442 := hb (x 6 2 && x 6 12)
    clear * - r36440 b36441 b36442 d36431
    omega
  have d36443 : (x 6 6 && x 6 12).toNat = 0 := by
    have r36444 := hand2 (x 6 6) (x 6 12)
    have b36445 := hb (x 6 12)
    have b36446 := hb (x 6 6 && x 6 12)
    clear * - r36444 b36445 b36446 d36431
    omega
  have d36447 : (x 6 4).toNat = 0 := by
    have r36448 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b36449 := hb (x 6 4)
    have b36450 := hb (x 6 12)
    clear * - r36448 b36449 b36450 d36431
    omega
  have d36451 : (x 5 13).toNat = 0 := by
    have r36452 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36453 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e36454 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b36455 := hb (x 3 3)
    have b36456 := hb (x 4 2)
    have b36457 := hb (x 5 13)
    have b36458 := hb (x 6 12)
    clear * - r36452 e36453 e36454 b36455 b36456 b36457 b36458 d36431 d36427
    omega
  have d36459 : (x 5 3 && x 5 13).toNat = 0 := by
    have r36460 := hand2 (x 5 3) (x 5 13)
    have b36461 := hb (x 5 13)
    have b36462 := hb (x 5 3 && x 5 13)
    clear * - r36460 b36461 b36462 d36451
    omega
  have d36463 : (x 5 7 && x 5 13).toNat = 0 := by
    have r36464 := hand2 (x 5 7) (x 5 13)
    have b36465 := hb (x 5 13)
    have b36466 := hb (x 5 7 && x 5 13)
    clear * - r36464 b36465 b36466 d36451
    omega
  have d36467 : (x 5 5).toNat = 0 := by
    have r36468 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b36469 := hb (x 5 5)
    have b36470 := hb (x 5 13)
    clear * - r36468 b36469 b36470 d36451
    omega
  have d36471 : (x 4 1 && x 4 14).toNat = 1 := by
    have r36472 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36473 := hb (x 3 2)
    have b36474 := hb (x 5 13)
    have b36475 := hb (x 4 1 && x 4 14)
    clear * - r36472 b36473 b36474 b36475 d36451 g48
    omega
  have d36476 : (x 4 1).toNat = 1 := by
    have r36477 := hand1 (x 4 1) (x 4 14)
    have b36478 := hb (x 4 1)
    have b36479 := hb (x 4 1 && x 4 14)
    clear * - r36477 b36478 b36479 d36471
    omega
  have d36480 : (x 5 14).toNat = 0 := by
    have r36481 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36482 := hb (x 4 1)
    have b36483 := hb (x 5 14)
    clear * - r36481 b36482 b36483 d36476
    omega
  have d36484 : (x 5 3 && x 5 14).toNat = 0 := by
    have r36485 := hand2 (x 5 3) (x 5 14)
    have b36486 := hb (x 5 14)
    have b36487 := hb (x 5 3 && x 5 14)
    clear * - r36485 b36486 b36487 d36480
    omega
  have d36488 : (x 5 6).toNat = 0 := by
    have r36489 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
    have b36490 := hb (x 5 6)
    have b36491 := hb (x 5 14)
    clear * - r36489 b36490 b36491 d36480
    omega
  have d36492 : (x 5 6 && x 5 11).toNat = 0 := by
    have r36493 := hand1 (x 5 6) (x 5 11)
    have b36494 := hb (x 5 6)
    have b36495 := hb (x 5 6 && x 5 11)
    clear * - r36493 b36494 b36495 d36488
    omega
  have d36496 : (x 5 6 && x 5 10).toNat = 0 := by
    have r36497 := hand1 (x 5 6) (x 5 10)
    have b36498 := hb (x 5 6)
    have b36499 := hb (x 5 6 && x 5 10)
    clear * - r36497 b36498 b36499 d36488
    omega
  have d36500 : (x 5 2).toNat = 0 := by
    have r36501 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b36502 := hb (x 5 2)
    have b36503 := hb (x 5 14)
    clear * - r36501 b36502 b36503 d36480
    omega
  have d36504 : (x 5 10).toNat = 0 := by
    have r36505 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b36506 := hb (x 5 2)
    have b36507 := hb (x 5 10)
    clear * - r36505 b36506 b36507 d36500
    omega
  have d36508 : (x 3 5).toNat = 0 := by
    have r36509 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b36510 := hb (x 3 5)
    have b36511 := hb (x 3 13)
    clear * - r36509 b36510 b36511 d36407
    omega
  have d36512 : (x 2 2).toNat = 0 := by
    have r36513 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36514 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e36515 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b36516 := hb (x 1 3)
    have b36517 := hb (x 2 2)
    have b36518 := hb (x 3 13)
    have b36519 := hb (x 4 12)
    clear * - r36513 e36514 e36515 b36516 b36517 b36518 b36519 d36403 d36407 g34
    omega
  have d36520 : (x 2 2 && x 2 13).toNat = 0 := by
    have r36521 := hand1 (x 2 2) (x 2 13)
    have b36522 := hb (x 2 2)
    have b36523 := hb (x 2 2 && x 2 13)
    clear * - r36521 b36522 b36523 d36512
    omega
  have d36524 : (x 4 11).toNat = 1 := by
    have r36525 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36526 := hb (x 0 4)
    have b36527 := hb (x 4 11)
    have b36528 := hb (x 3 1 && x 3 12)
    have b36529 := hb (x 2 2 && x 2 13)
    have b36530 := hb (x 1 3 && x 1 14)
    clear * - r36525 b36526 b36527 b36528 b36529 b36530 g133 d36520 g134 g25
    omega
  have d36531 : (x 4 3).toNat = 1 := by
    have r36532 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b36533 := hb (x 4 3)
    have b36534 := hb (x 4 11)
    clear * - r36532 b36533 b36534 d36524
    omega
  have d36535 : (x 7 12).toNat = 0 := by
    have r36536 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36537 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e36538 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b36539 := hb (x 4 3)
    have b36540 := hb (x 5 2)
    have b36541 := hb (x 6 13)
    have b36542 := hb (x 7 12)
    clear * - r36536 e36537 e36538 b36539 b36540 b36541 b36542 d36500 d36531
    omega
  have d36543 : (x 7 1 && x 7 12).toNat = 0 := by
    have r36544 := hand2 (x 7 1) (x 7 12)
    have b36545 := hb (x 7 12)
    have b36546 := hb (x 7 1 && x 7 12)
    clear * - r36544 b36545 b36546 d36535
    omega
  have d36547 : (x 7 4).toNat = 0 := by
    have r36548 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b36549 := hb (x 7 4)
    have b36550 := hb (x 7 12)
    clear * - r36548 b36549 b36550 d36535
    omega
  have d36551 : (x 7 4 && x 7 8).toNat = 0 := by
    have r36552 := hand1 (x 7 4) (x 7 8)
    have b36553 := hb (x 7 4)
    have b36554 := hb (x 7 4 && x 7 8)
    clear * - r36552 b36553 b36554 d36547
    omega
  have d36555 : (x 6 13).toNat = 0 := by
    have r36556 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36557 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e36558 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b36559 := hb (x 4 3)
    have b36560 := hb (x 5 2)
    have b36561 := hb (x 6 13)
    have b36562 := hb (x 7 12)
    clear * - r36556 e36557 e36558 b36559 b36560 b36561 b36562 d36535 d36500 d36531
    omega
  have d36563 : (x 6 2 && x 6 13).toNat = 0 := by
    have r36564 := hand2 (x 6 2) (x 6 13)
    have b36565 := hb (x 6 13)
    have b36566 := hb (x 6 2 && x 6 13)
    clear * - r36564 b36565 b36566 d36555
    omega
  have d36567 : (x 6 5).toNat = 0 := by
    have r36568 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
    have b36569 := hb (x 6 5)
    have b36570 := hb (x 6 13)
    clear * - r36568 b36569 b36570 d36555
    omega
  have d36571 : (x 6 5 && x 6 9).toNat = 0 := by
    have r36572 := hand1 (x 6 5) (x 6 9)
    have b36573 := hb (x 6 5)
    have b36574 := hb (x 6 5 && x 6 9)
    clear * - r36572 b36573 b36574 d36567
    omega
  have d36575 : (x 4 4).toNat = 0 := by
    have r36576 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36577 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e36578 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e36579 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e36580 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e36581 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e36582 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b36583 := hb (x 1 7)
    have b36584 := hb (x 2 6)
    have b36585 := hb (x 3 5)
    have b36586 := hb (x 4 4)
    have b36587 := hb (x 5 11)
    have b36588 := hb (x 6 10)
    have b36589 := hb (x 7 9)
    have b36590 := hb (x 8 8)
    clear * - r36576 e36577 e36578 e36579 e36580 e36581 e36582 b36583 b36584 b36585 b36586 b36587 b36588 b36589 b36590 d36290 d36318 d36346 d36370 d36508 f36289 f34233
    omega
  have d36591 : (x 4 4 && x 4 14).toNat = 0 := by
    have r36592 := hand1 (x 4 4) (x 4 14)
    have b36593 := hb (x 4 4)
    have b36594 := hb (x 4 4 && x 4 14)
    clear * - r36592 b36593 b36594 d36575
    omega
  have d36595 : (x 8 11).toNat = 1 := by
    have r36596 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36597 := hb (x 4 4)
    have b36598 := hb (x 8 11)
    have b36599 := hb (x 7 1 && x 7 12)
    have b36600 := hb (x 6 2 && x 6 13)
    have b36601 := hb (x 5 3 && x 5 14)
    clear * - r36596 b36597 b36598 b36599 b36600 b36601 d36543 d36563 d36484 d36575
    omega
  have d36602 : (x 8 3).toNat = 1 := by
    have r36603 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b36604 := hb (x 8 3)
    have b36605 := hb (x 8 11)
    clear * - r36603 b36604 b36605 d36595
    omega
  have d36606 : (x 11 12).toNat = 0 := by
    have r36607 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36608 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e36609 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b36610 := hb (x 8 3)
    have b36611 := hb (x 9 2)
    have b36612 := hb (x 10 13)
    have b36613 := hb (x 11 12)
    clear * - r36607 e36608 e36609 b36610 b36611 b36612 b36613 d36602
    omega
  have d36614 : (x 11 2 && x 11 12).toNat = 0 := by
    have r36615 := hand2 (x 11 2) (x 11 12)
    have b36616 := hb (x 11 12)
    have b36617 := hb (x 11 2 && x 11 12)
    clear * - r36615 b36616 b36617 d36606
    omega
  have d36618 : (x 11 3 && x 11 12).toNat = 0 := by
    have r36619 := hand2 (x 11 3) (x 11 12)
    have b36620 := hb (x 11 12)
    have b36621 := hb (x 11 3 && x 11 12)
    clear * - r36619 b36620 b36621 d36606
    omega
  have d36622 : (x 11 5 && x 11 12).toNat = 0 := by
    have r36623 := hand2 (x 11 5) (x 11 12)
    have b36624 := hb (x 11 12)
    have b36625 := hb (x 11 5 && x 11 12)
    clear * - r36623 b36624 b36625 d36606
    omega
  have d36626 : (x 11 4).toNat = 0 := by
    have r36627 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b36628 := hb (x 11 4)
    have b36629 := hb (x 11 12)
    clear * - r36627 b36628 b36629 d36606
    omega
  have d36630 : (x 10 13).toNat = 0 := by
    have r36631 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36632 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e36633 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b36634 := hb (x 8 3)
    have b36635 := hb (x 9 2)
    have b36636 := hb (x 10 13)
    have b36637 := hb (x 11 12)
    clear * - r36631 e36632 e36633 b36634 b36635 b36636 b36637 d36606 d36602
    omega
  have d36638 : (x 10 3 && x 10 13).toNat = 0 := by
    have r36639 := hand2 (x 10 3) (x 10 13)
    have b36640 := hb (x 10 13)
    have b36641 := hb (x 10 3 && x 10 13)
    clear * - r36639 b36640 b36641 d36630
    omega
  have d36642 : (x 10 4 && x 10 13).toNat = 0 := by
    have r36643 := hand2 (x 10 4) (x 10 13)
    have b36644 := hb (x 10 13)
    have b36645 := hb (x 10 4 && x 10 13)
    clear * - r36643 b36644 b36645 d36630
    omega
  have d36646 : (x 10 6 && x 10 13).toNat = 0 := by
    have r36647 := hand2 (x 10 6) (x 10 13)
    have b36648 := hb (x 10 13)
    have b36649 := hb (x 10 6 && x 10 13)
    clear * - r36647 b36648 b36649 d36630
    omega
  have d36650 : (x 10 5).toNat = 0 := by
    have r36651 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
    have b36652 := hb (x 10 5)
    have b36653 := hb (x 10 13)
    clear * - r36651 b36652 b36653 d36630
    omega
  have d36654 : (x 9 2).toNat = 0 := by
    have r36655 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36656 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e36657 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b36658 := hb (x 8 3)
    have b36659 := hb (x 9 2)
    have b36660 := hb (x 10 13)
    have b36661 := hb (x 11 12)
    clear * - r36655 e36656 e36657 b36658 b36659 b36660 b36661 d36606 d36630 d36602
    omega
  have d36662 : (x 9 2 && x 9 7).toNat = 0 := by
    have r36663 := hand1 (x 9 2) (x 9 7)
    have b36664 := hb (x 9 2)
    have b36665 := hb (x 9 2 && x 9 7)
    clear * - r36663 b36664 b36665 d36654
    omega
  have d36666 : (x 9 2 && x 9 6).toNat = 0 := by
    have r36667 := hand1 (x 9 2) (x 9 6)
    have b36668 := hb (x 9 2)
    have b36669 := hb (x 9 2 && x 9 6)
    clear * - r36667 b36668 b36669 d36654
    omega
  have d36670 : (x 9 10).toNat = 0 := by
    have r36671 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
    have b36672 := hb (x 9 2)
    have b36673 := hb (x 9 10)
    clear * - r36671 b36672 b36673 d36654
    omega
  have d36674 : (x 11 8).toNat = 0 := by
    have r36675 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36676 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e36677 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e36678 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e36679 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e36680 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e36681 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b36682 := hb (x 4 7)
    have b36683 := hb (x 5 6)
    have b36684 := hb (x 6 5)
    have b36685 := hb (x 7 4)
    have b36686 := hb (x 8 11)
    have b36687 := hb (x 9 10)
    have b36688 := hb (x 10 9)
    have b36689 := hb (x 11 8)
    clear * - r36675 e36676 e36677 e36678 e36679 e36680 e36681 b36682 b36683 b36684 b36685 b36686 b36687 b36688 b36689 d36670 d36595 d36547 d36567 d36488
    omega
  have d36690 : (x 10 9).toNat = 0 := by
    have r36691 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36692 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e36693 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e36694 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e36695 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e36696 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e36697 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b36698 := hb (x 4 7)
    have b36699 := hb (x 5 6)
    have b36700 := hb (x 6 5)
    have b36701 := hb (x 7 4)
    have b36702 := hb (x 8 11)
    have b36703 := hb (x 9 10)
    have b36704 := hb (x 10 9)
    have b36705 := hb (x 11 8)
    clear * - r36691 e36692 e36693 e36694 e36695 e36696 e36697 b36698 b36699 b36700 b36701 b36702 b36703 b36704 b36705 d36674 d36670 d36595 d36547 d36567 d36488
    omega
  have d36706 : (x 4 7).toNat = 0 := by
    have r36707 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36708 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e36709 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e36710 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e36711 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e36712 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e36713 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b36714 := hb (x 4 7)
    have b36715 := hb (x 5 6)
    have b36716 := hb (x 6 5)
    have b36717 := hb (x 7 4)
    have b36718 := hb (x 8 11)
    have b36719 := hb (x 9 10)
    have b36720 := hb (x 10 9)
    have b36721 := hb (x 11 8)
    clear * - r36707 e36708 e36709 e36710 e36711 e36712 e36713 b36714 b36715 b36716 b36717 b36718 b36719 b36720 b36721 d36674 d36690 d36670 d36595 d36547 d36567 d36488
    omega
  have d36722 : (x 4 7 && x 4 12).toNat = 0 := by
    have r36723 := hand1 (x 4 7) (x 4 12)
    have b36724 := hb (x 4 7)
    have b36725 := hb (x 4 7 && x 4 12)
    clear * - r36723 b36724 b36725 d36706
    omega
  have d36726 : (x 4 7 && x 4 11).toNat = 0 := by
    have r36727 := hand1 (x 4 7) (x 4 11)
    have b36728 := hb (x 4 7)
    have b36729 := hb (x 4 7 && x 4 11)
    clear * - r36727 b36728 b36729 d36706
    omega
  have d36730 : (x 7 8).toNat = 0 := by
    have r36731 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36732 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e36733 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e36734 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e36735 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e36736 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e36737 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b36738 := hb (x 0 7)
    have b36739 := hb (x 1 6)
    have b36740 := hb (x 2 5)
    have b36741 := hb (x 3 4)
    have b36742 := hb (x 4 11)
    have b36743 := hb (x 5 10)
    have b36744 := hb (x 6 9)
    have b36745 := hb (x 7 8)
    clear * - r36731 e36732 e36733 e36734 e36735 e36736 e36737 b36738 b36739 b36740 b36741 b36742 b36743 b36744 b36745 d36504 d36524 g49 f34235 g36 g27
    omega
  have d36746 : (x 6 9).toNat = 0 := by
    have r36747 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36748 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e36749 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e36750 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e36751 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e36752 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e36753 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b36754 := hb (x 0 7)
    have b36755 := hb (x 1 6)
    have b36756 := hb (x 2 5)
    have b36757 := hb (x 3 4)
    have b36758 := hb (x 4 11)
    have b36759 := hb (x 5 10)
    have b36760 := hb (x 6 9)
    have b36761 := hb (x 7 8)
    clear * - r36747 e36748 e36749 e36750 e36751 e36752 e36753 b36754 b36755 b36756 b36757 b36758 b36759 b36760 b36761 d36730 d36504 d36524 g49 f34235 g36 g27
    omega
  have d36762 : (x 8 3 && x 8 7).toNat = 1 := by
    have r36763 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36764 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
    have e36765 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
    have b36766 := hb (x 0 11)
    have b36767 := hb (x 1 10)
    have b36768 := hb (x 10 5)
    have b36769 := hb (x 11 4)
    have b36770 := hb (x 9 2 && x 9 6)
    have b36771 := hb (x 8 3 && x 8 7)
    have b36772 := hb (x 7 4 && x 7 8)
    have b36773 := hb (x 6 5 && x 6 9)
    have b36774 := hb (x 5 6 && x 5 10)
    have b36775 := hb (x 4 7 && x 4 11)
    have b36776 := hb (x 3 8 && x 3 12)
    have b36777 := hb (x 2 9 && x 2 13)
    clear * - r36763 e36764 e36765 b36766 b36767 b36768 b36769 b36770 b36771 b36772 b36773 b36774 b36775 b36776 b36777 d36626 d36650 d36666 d36551 d36571 d36496 d36726 g64 g65 g39 g31
    omega
  have d36778 : (x 8 7).toNat = 1 := by
    have r36779 := hand2 (x 8 3) (x 8 7)
    have b36780 := hb (x 8 7)
    have b36781 := hb (x 8 3 && x 8 7)
    clear * - r36779 b36780 b36781 d36762
    omega
  have d36782 : (x 15 8).toNat = 0 := by
    have r36783 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36784 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e36785 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e36786 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e36787 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e36788 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e36789 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b36790 := hb (x 8 7)
    have b36791 := hb (x 9 6)
    have b36792 := hb (x 10 5)
    have b36793 := hb (x 11 4)
    have b36794 := hb (x 12 11)
    have b36795 := hb (x 13 10)
    have b36796 := hb (x 14 9)
    have b36797 := hb (x 15 8)
    clear * - r36783 e36784 e36785 e36786 e36787 e36788 e36789 b36790 b36791 b36792 b36793 b36794 b36795 b36796 b36797 d36626 d36650 d36778
    omega
  have d36798 : (x 15 1 && x 15 8).toNat = 0 := by
    have r36799 := hand2 (x 15 1) (x 15 8)
    have b36800 := hb (x 15 8)
    have b36801 := hb (x 15 1 && x 15 8)
    clear * - r36799 b36800 b36801 d36782
    omega
  have d36802 : (x 14 9).toNat = 0 := by
    have r36803 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36804 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e36805 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e36806 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e36807 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e36808 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e36809 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b36810 := hb (x 8 7)
    have b36811 := hb (x 9 6)
    have b36812 := hb (x 10 5)
    have b36813 := hb (x 11 4)
    have b36814 := hb (x 12 11)
    have b36815 := hb (x 13 10)
    have b36816 := hb (x 14 9)
    have b36817 := hb (x 15 8)
    clear * - r36803 e36804 e36805 e36806 e36807 e36808 e36809 b36810 b36811 b36812 b36813 b36814 b36815 b36816 b36817 d36782 d36626 d36650 d36778
    omega
  have d36818 : (x 14 2 && x 14 9).toNat = 0 := by
    have r36819 := hand2 (x 14 2) (x 14 9)
    have b36820 := hb (x 14 9)
    have b36821 := hb (x 14 2 && x 14 9)
    clear * - r36819 b36820 b36821 d36802
    omega
  have d36822 : (x 13 10).toNat = 0 := by
    have r36823 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36824 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e36825 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e36826 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e36827 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e36828 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e36829 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b36830 := hb (x 8 7)
    have b36831 := hb (x 9 6)
    have b36832 := hb (x 10 5)
    have b36833 := hb (x 11 4)
    have b36834 := hb (x 12 11)
    have b36835 := hb (x 13 10)
    have b36836 := hb (x 14 9)
    have b36837 := hb (x 15 8)
    clear * - r36823 e36824 e36825 e36826 e36827 e36828 e36829 b36830 b36831 b36832 b36833 b36834 b36835 b36836 b36837 d36782 d36802 d36626 d36650 d36778
    omega
  have d36838 : (x 13 1 && x 13 10).toNat = 0 := by
    have r36839 := hand2 (x 13 1) (x 13 10)
    have b36840 := hb (x 13 10)
    have b36841 := hb (x 13 1 && x 13 10)
    clear * - r36839 b36840 b36841 d36822
    omega
  have d36842 : (x 13 3 && x 13 10).toNat = 0 := by
    have r36843 := hand2 (x 13 3) (x 13 10)
    have b36844 := hb (x 13 10)
    have b36845 := hb (x 13 3 && x 13 10)
    clear * - r36843 b36844 b36845 d36822
    omega
  have d36846 : (x 12 11).toNat = 0 := by
    have r36847 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36848 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e36849 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e36850 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e36851 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e36852 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e36853 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b36854 := hb (x 8 7)
    have b36855 := hb (x 9 6)
    have b36856 := hb (x 10 5)
    have b36857 := hb (x 11 4)
    have b36858 := hb (x 12 11)
    have b36859 := hb (x 13 10)
    have b36860 := hb (x 14 9)
    have b36861 := hb (x 15 8)
    clear * - r36847 e36848 e36849 e36850 e36851 e36852 e36853 b36854 b36855 b36856 b36857 b36858 b36859 b36860 b36861 d36782 d36802 d36822 d36626 d36650 d36778
    omega
  have d36862 : (x 12 1 && x 12 11).toNat = 0 := by
    have r36863 := hand2 (x 12 1) (x 12 11)
    have b36864 := hb (x 12 11)
    have b36865 := hb (x 12 1 && x 12 11)
    clear * - r36863 b36864 b36865 d36846
    omega
  have d36866 : (x 12 2 && x 12 11).toNat = 0 := by
    have r36867 := hand2 (x 12 2) (x 12 11)
    have b36868 := hb (x 12 11)
    have b36869 := hb (x 12 2 && x 12 11)
    clear * - r36867 b36868 b36869 d36846
    omega
  have d36870 : (x 12 4 && x 12 11).toNat = 0 := by
    have r36871 := hand2 (x 12 4) (x 12 11)
    have b36872 := hb (x 12 11)
    have b36873 := hb (x 12 4 && x 12 11)
    clear * - r36871 b36872 b36873 d36846
    omega
  have d36874 : (x 9 6).toNat = 0 := by
    have r36875 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36876 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e36877 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e36878 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e36879 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e36880 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e36881 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b36882 := hb (x 8 7)
    have b36883 := hb (x 9 6)
    have b36884 := hb (x 10 5)
    have b36885 := hb (x 11 4)
    have b36886 := hb (x 12 11)
    have b36887 := hb (x 13 10)
    have b36888 := hb (x 14 9)
    have b36889 := hb (x 15 8)
    clear * - r36875 e36876 e36877 e36878 e36879 e36880 e36881 b36882 b36883 b36884 b36885 b36886 b36887 b36888 b36889 d36782 d36802 d36822 d36846 d36626 d36650 d36778
    omega
  have d36890 : (x 14 1).toNat = 0 := by
    have r36891 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36892 := hb (x 1 14)
    have b36893 := hb (x 2 13)
    have b36894 := hb (x 3 12)
    have b36895 := hb (x 4 11)
    have b36896 := hb (x 5 10)
    have b36897 := hb (x 6 9)
    have b36898 := hb (x 7 8)
    have b36899 := hb (x 8 7)
    have b36900 := hb (x 9 6)
    have b36901 := hb (x 10 5)
    have b36902 := hb (x 11 4)
    have b36903 := hb (x 12 3)
    have b36904 := hb (x 13 2)
    have b36905 := hb (x 14 1)
    clear * - r36891 b36892 b36893 b36894 b36895 b36896 b36897 b36898 b36899 b36900 b36901 b36902 b36903 b36904 b36905 d36626 d36650 d36874 d36778 d36730 d36746 d36504 d36524 g52 g46 g41
    omega
  have d36906 : (x 14 1 && x 14 14).toNat = 0 := by
    have r36907 := hand1 (x 14 1) (x 14 14)
    have b36908 := hb (x 14 1)
    have b36909 := hb (x 14 1 && x 14 14)
    clear * - r36907 b36908 b36909 d36890
    omega
  have d36910 : (x 14 13).toNat = 0 := by
    have r36911 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b36912 := hb (x 14 1)
    have b36913 := hb (x 14 13)
    clear * - r36911 b36912 b36913 d36890
    omega
  have d36914 : (x 13 2).toNat = 0 := by
    have r36915 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36916 := hb (x 1 14)
    have b36917 := hb (x 2 13)
    have b36918 := hb (x 3 12)
    have b36919 := hb (x 4 11)
    have b36920 := hb (x 5 10)
    have b36921 := hb (x 6 9)
    have b36922 := hb (x 7 8)
    have b36923 := hb (x 8 7)
    have b36924 := hb (x 9 6)
    have b36925 := hb (x 10 5)
    have b36926 := hb (x 11 4)
    have b36927 := hb (x 12 3)
    have b36928 := hb (x 13 2)
    have b36929 := hb (x 14 1)
    clear * - r36915 b36916 b36917 b36918 b36919 b36920 b36921 b36922 b36923 b36924 b36925 b36926 b36927 b36928 b36929 d36890 d36626 d36650 d36874 d36778 d36730 d36746 d36504 d36524 g52 g46 g41
    omega
  have d36930 : (x 15 13).toNat = 1 := by
    have r36931 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36932 := hb (x 13 2)
    have b36933 := hb (x 15 13)
    have b36934 := hb (x 14 1 && x 14 14)
    clear * - r36931 b36932 b36933 b36934 d36906 d36914
    omega
  have d36935 : (x 15 1).toNat = 1 := by
    have r36936 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have b36937 := hb (x 15 1)
    have b36938 := hb (x 15 13)
    clear * - r36936 b36937 b36938 d36930
    omega
  have d36939 : (x 16 14).toNat = 0 := by
    have r36940 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36941 := hb (x 15 1)
    have b36942 := hb (x 16 14)
    clear * - r36940 b36941 b36942 d36935
    omega
  have d36943 : (x 16 1 && x 16 14).toNat = 0 := by
    have r36944 := hand2 (x 16 1) (x 16 14)
    have b36945 := hb (x 16 14)
    have b36946 := hb (x 16 1 && x 16 14)
    clear * - r36944 b36945 b36946 d36939
    omega
  have d36947 : (x 16 6).toNat = 0 := by
    have r36948 : (x 16 6).toNat ≤ (x 16 14).toNat := himp _ _ (hp6 16)
    have b36949 := hb (x 16 6)
    have b36950 := hb (x 16 14)
    clear * - r36948 b36949 b36950 d36939
    omega
  have d36951 : (x 16 2).toNat = 0 := by
    have r36952 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
    have b36953 := hb (x 16 2)
    have b36954 := hb (x 16 14)
    clear * - r36952 b36953 b36954 d36939
    omega
  have d36955 : (x 16 10).toNat = 0 := by
    have r36956 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
    have b36957 := hb (x 16 2)
    have b36958 := hb (x 16 10)
    clear * - r36956 b36957 b36958 d36951
    omega
  have d36959 : (x 14 2).toNat = 0 := by
    have r36960 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36961 := hb (x 2 14)
    have b36962 := hb (x 3 13)
    have b36963 := hb (x 4 12)
    have b36964 := hb (x 5 11)
    have b36965 := hb (x 6 10)
    have b36966 := hb (x 7 9)
    have b36967 := hb (x 8 8)
    have b36968 := hb (x 9 7)
    have b36969 := hb (x 10 6)
    have b36970 := hb (x 11 5)
    have b36971 := hb (x 12 4)
    have b36972 := hb (x 13 3)
    have b36973 := hb (x 14 2)
    have b36974 := hb (x 15 1)
    clear * - r36960 b36961 b36962 b36963 b36964 b36965 b36966 b36967 b36968 b36969 b36970 b36971 b36972 b36973 b36974 d36935 d36290 d36318 d36346 d36370 d36403 d36407 g47
    omega
  have d36975 : (x 14 2 && x 14 12).toNat = 0 := by
    have r36976 := hand1 (x 14 2) (x 14 12)
    have b36977 := hb (x 14 2)
    have b36978 := hb (x 14 2 && x 14 12)
    clear * - r36976 b36977 b36978 d36959
    omega
  have d36979 : (x 14 2 && x 14 7).toNat = 0 := by
    have r36980 := hand1 (x 14 2) (x 14 7)
    have b36981 := hb (x 14 2)
    have b36982 := hb (x 14 2 && x 14 7)
    clear * - r36980 b36981 b36982 d36959
    omega
  have d36983 : (x 14 2 && x 14 6).toNat = 0 := by
    have r36984 := hand1 (x 14 2) (x 14 6)
    have b36985 := hb (x 14 2)
    have b36986 := hb (x 14 2 && x 14 6)
    clear * - r36984 b36985 b36986 d36959
    omega
  have d36987 : (x 14 10).toNat = 0 := by
    have r36988 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
    have b36989 := hb (x 14 2)
    have b36990 := hb (x 14 10)
    clear * - r36988 b36989 b36990 d36959
    omega
  have d36991 : (x 13 3).toNat = 0 := by
    have r36992 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b36993 := hb (x 2 14)
    have b36994 := hb (x 3 13)
    have b36995 := hb (x 4 12)
    have b36996 := hb (x 5 11)
    have b36997 := hb (x 6 10)
    have b36998 := hb (x 7 9)
    have b36999 := hb (x 8 8)
    have b37000 := hb (x 9 7)
    have b37001 := hb (x 10 6)
    have b37002 := hb (x 11 5)
    have b37003 := hb (x 12 4)
    have b37004 := hb (x 13 3)
    have b37005 := hb (x 14 2)
    have b37006 := hb (x 15 1)
    clear * - r36992 b36993 b36994 b36995 b36996 b36997 b36998 b36999 b37000 b37001 b37002 b37003 b37004 b37005 b37006 d36935 d36959 d36290 d36318 d36346 d36370 d36403 d36407 g47
    omega
  have d37007 : (x 13 3 && x 13 13).toNat = 0 := by
    have r37008 := hand1 (x 13 3) (x 13 13)
    have b37009 := hb (x 13 3)
    have b37010 := hb (x 13 3 && x 13 13)
    clear * - r37008 b37009 b37010 d36991
    omega
  have d37011 : (x 13 3 && x 13 8).toNat = 0 := by
    have r37012 := hand1 (x 13 3) (x 13 8)
    have b37013 := hb (x 13 3)
    have b37014 := hb (x 13 3 && x 13 8)
    clear * - r37012 b37013 b37014 d36991
    omega
  have d37015 : (x 13 3 && x 13 7).toNat = 0 := by
    have r37016 := hand1 (x 13 3) (x 13 7)
    have b37017 := hb (x 13 3)
    have b37018 := hb (x 13 3 && x 13 7)
    clear * - r37016 b37017 b37018 d36991
    omega
  have d37019 : (x 13 11).toNat = 0 := by
    have r37020 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
    have b37021 := hb (x 13 3)
    have b37022 := hb (x 13 11)
    clear * - r37020 b37021 b37022 d36991
    omega
  have d37023 : (x 13 1 && x 13 11).toNat = 0 := by
    have r37024 := hand2 (x 13 1) (x 13 11)
    have b37025 := hb (x 13 11)
    have b37026 := hb (x 13 1 && x 13 11)
    clear * - r37024 b37025 b37026 d37019
    omega
  have d37027 : (x 12 4).toNat = 0 := by
    have r37028 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37029 := hb (x 2 14)
    have b37030 := hb (x 3 13)
    have b37031 := hb (x 4 12)
    have b37032 := hb (x 5 11)
    have b37033 := hb (x 6 10)
    have b37034 := hb (x 7 9)
    have b37035 := hb (x 8 8)
    have b37036 := hb (x 9 7)
    have b37037 := hb (x 10 6)
    have b37038 := hb (x 11 5)
    have b37039 := hb (x 12 4)
    have b37040 := hb (x 13 3)
    have b37041 := hb (x 14 2)
    have b37042 := hb (x 15 1)
    clear * - r37028 b37029 b37030 b37031 b37032 b37033 b37034 b37035 b37036 b37037 b37038 b37039 b37040 b37041 b37042 d36935 d36959 d36991 d36290 d36318 d36346 d36370 d36403 d36407 g47
    omega
  have d37043 : (x 12 4 && x 12 14).toNat = 0 := by
    have r37044 := hand1 (x 12 4) (x 12 14)
    have b37045 := hb (x 12 4)
    have b37046 := hb (x 12 4 && x 12 14)
    clear * - r37044 b37045 b37046 d37027
    omega
  have d37047 : (x 12 4 && x 12 9).toNat = 0 := by
    have r37048 := hand1 (x 12 4) (x 12 9)
    have b37049 := hb (x 12 4)
    have b37050 := hb (x 12 4 && x 12 9)
    clear * - r37048 b37049 b37050 d37027
    omega
  have d37051 : (x 12 4 && x 12 8).toNat = 0 := by
    have r37052 := hand1 (x 12 4) (x 12 8)
    have b37053 := hb (x 12 4)
    have b37054 := hb (x 12 4 && x 12 8)
    clear * - r37052 b37053 b37054 d37027
    omega
  have d37055 : (x 11 5).toNat = 0 := by
    have r37056 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37057 := hb (x 2 14)
    have b37058 := hb (x 3 13)
    have b37059 := hb (x 4 12)
    have b37060 := hb (x 5 11)
    have b37061 := hb (x 6 10)
    have b37062 := hb (x 7 9)
    have b37063 := hb (x 8 8)
    have b37064 := hb (x 9 7)
    have b37065 := hb (x 10 6)
    have b37066 := hb (x 11 5)
    have b37067 := hb (x 12 4)
    have b37068 := hb (x 13 3)
    have b37069 := hb (x 14 2)
    have b37070 := hb (x 15 1)
    clear * - r37056 b37057 b37058 b37059 b37060 b37061 b37062 b37063 b37064 b37065 b37066 b37067 b37068 b37069 b37070 d36935 d36959 d36991 d37027 d36290 d36318 d36346 d36370 d36403 d36407 g47
    omega
  have d37071 : (x 11 5 && x 11 10).toNat = 0 := by
    have r37072 := hand1 (x 11 5) (x 11 10)
    have b37073 := hb (x 11 5)
    have b37074 := hb (x 11 5 && x 11 10)
    clear * - r37072 b37073 b37074 d37055
    omega
  have d37075 : (x 11 5 && x 11 9).toNat = 0 := by
    have r37076 := hand1 (x 11 5) (x 11 9)
    have b37077 := hb (x 11 5)
    have b37078 := hb (x 11 5 && x 11 9)
    clear * - r37076 b37077 b37078 d37055
    omega
  have d37079 : (x 15 1 && x 15 11).toNat = 1 := by
    have r37080 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37081 := hb (x 11 5)
    have b37082 := hb (x 16 10)
    have b37083 := hb (x 15 1 && x 15 11)
    have b37084 := hb (x 14 2 && x 14 12)
    have b37085 := hb (x 13 3 && x 13 13)
    have b37086 := hb (x 12 4 && x 12 14)
    clear * - r37080 b37081 b37082 b37083 b37084 b37085 b37086 d36955 d36975 d37007 d37043 d37055
    omega
  have d37087 : (x 15 11).toNat = 1 := by
    have r37088 := hand2 (x 15 1) (x 15 11)
    have b37089 := hb (x 15 11)
    have b37090 := hb (x 15 1 && x 15 11)
    clear * - r37088 b37089 b37090 d37079
    omega
  have d37091 : (x 15 3).toNat = 1 := by
    have r37092 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
    have b37093 := hb (x 15 3)
    have b37094 := hb (x 15 11)
    clear * - r37092 b37093 b37094 d37087
    omega
  have d37095 : (x 18 12).toNat = 0 := by
    have r37096 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37097 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e37098 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b37099 := hb (x 15 3)
    have b37100 := hb (x 16 2)
    have b37101 := hb (x 17 13)
    have b37102 := hb (x 18 12)
    clear * - r37096 e37097 e37098 b37099 b37100 b37101 b37102 d36951 d37091
    omega
  have d37103 : (x 18 4).toNat = 0 := by
    have r37104 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
    have b37105 := hb (x 18 4)
    have b37106 := hb (x 18 12)
    clear * - r37104 b37105 b37106 d37095
    omega
  have d37107 : (x 18 4 && x 18 13).toNat = 0 := by
    have r37108 := hand1 (x 18 4) (x 18 13)
    have b37109 := hb (x 18 4)
    have b37110 := hb (x 18 4 && x 18 13)
    clear * - r37108 b37109 b37110 d37103
    omega
  have d37111 : (x 17 13).toNat = 0 := by
    have r37112 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37113 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e37114 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b37115 := hb (x 15 3)
    have b37116 := hb (x 16 2)
    have b37117 := hb (x 17 13)
    have b37118 := hb (x 18 12)
    clear * - r37112 e37113 e37114 b37115 b37116 b37117 b37118 d37095 d36951 d37091
    omega
  have d37119 : (x 17 5).toNat = 0 := by
    have r37120 : (x 17 5).toNat ≤ (x 17 13).toNat := himp _ _ (hp5 17)
    have b37121 := hb (x 17 5)
    have b37122 := hb (x 17 13)
    clear * - r37120 b37121 b37122 d37111
    omega
  have d37123 : (x 17 5 && x 17 14).toNat = 0 := by
    have r37124 := hand1 (x 17 5) (x 17 14)
    have b37125 := hb (x 17 5)
    have b37126 := hb (x 17 5 && x 17 14)
    clear * - r37124 b37125 b37126 d37119
    omega
  have d37127 : (x 15 2).toNat = 1 := by
    have r37128 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37129 := hb (x 15 2)
    have b37130 := hb (x 17 13)
    have b37131 := hb (x 16 1 && x 16 14)
    clear * - r37128 b37129 b37130 b37131 d37111 d36943
    omega
  have d37132 : (x 17 12).toNat = 0 := by
    have r37133 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37134 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e37135 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b37136 := hb (x 14 3)
    have b37137 := hb (x 15 2)
    have b37138 := hb (x 16 13)
    have b37139 := hb (x 17 12)
    clear * - r37133 e37134 e37135 b37136 b37137 b37138 b37139 d37127
    omega
  have d37140 : (x 17 3 && x 17 12).toNat = 0 := by
    have r37141 := hand2 (x 17 3) (x 17 12)
    have b37142 := hb (x 17 12)
    have b37143 := hb (x 17 3 && x 17 12)
    clear * - r37141 b37142 b37143 d37132
    omega
  have d37144 : (x 17 4).toNat = 0 := by
    have r37145 : (x 17 4).toNat ≤ (x 17 12).toNat := himp _ _ (hp4 17)
    have b37146 := hb (x 17 4)
    have b37147 := hb (x 17 12)
    clear * - r37145 b37146 b37147 d37132
    omega
  have d37148 : (x 16 13).toNat = 0 := by
    have r37149 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37150 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e37151 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b37152 := hb (x 14 3)
    have b37153 := hb (x 15 2)
    have b37154 := hb (x 16 13)
    have b37155 := hb (x 17 12)
    clear * - r37149 e37150 e37151 b37152 b37153 b37154 b37155 d37132 d37127
    omega
  have d37156 : (x 16 4 && x 16 13).toNat = 0 := by
    have r37157 := hand2 (x 16 4) (x 16 13)
    have b37158 := hb (x 16 13)
    have b37159 := hb (x 16 4 && x 16 13)
    clear * - r37157 b37158 b37159 d37148
    omega
  have d37160 : (x 16 5).toNat = 0 := by
    have r37161 : (x 16 5).toNat ≤ (x 16 13).toNat := himp _ _ (hp5 16)
    have b37162 := hb (x 16 5)
    have b37163 := hb (x 16 13)
    clear * - r37161 b37162 b37163 d37148
    omega
  have d37164 : (x 18 8).toNat = 0 := by
    have r37165 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37166 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e37167 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e37168 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e37169 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e37170 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e37171 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b37172 := hb (x 11 7)
    have b37173 := hb (x 12 6)
    have b37174 := hb (x 13 5)
    have b37175 := hb (x 14 4)
    have b37176 := hb (x 15 11)
    have b37177 := hb (x 16 10)
    have b37178 := hb (x 17 9)
    have b37179 := hb (x 18 8)
    clear * - r37165 e37166 e37167 e37168 e37169 e37170 e37171 b37172 b37173 b37174 b37175 b37176 b37177 b37178 b37179 d36955 d37087
    omega
  have d37180 : (x 17 9).toNat = 0 := by
    have r37181 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37182 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e37183 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e37184 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e37185 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e37186 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e37187 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b37188 := hb (x 11 7)
    have b37189 := hb (x 12 6)
    have b37190 := hb (x 13 5)
    have b37191 := hb (x 14 4)
    have b37192 := hb (x 15 11)
    have b37193 := hb (x 16 10)
    have b37194 := hb (x 17 9)
    have b37195 := hb (x 18 8)
    clear * - r37181 e37182 e37183 e37184 e37185 e37186 e37187 b37188 b37189 b37190 b37191 b37192 b37193 b37194 b37195 d37164 d36955 d37087
    omega
  have d37196 : (x 14 4).toNat = 0 := by
    have r37197 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37198 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e37199 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e37200 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e37201 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e37202 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e37203 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b37204 := hb (x 11 7)
    have b37205 := hb (x 12 6)
    have b37206 := hb (x 13 5)
    have b37207 := hb (x 14 4)
    have b37208 := hb (x 15 11)
    have b37209 := hb (x 16 10)
    have b37210 := hb (x 17 9)
    have b37211 := hb (x 18 8)
    clear * - r37197 e37198 e37199 e37200 e37201 e37202 e37203 b37204 b37205 b37206 b37207 b37208 b37209 b37210 b37211 d37164 d37180 d36955 d37087
    omega
  have d37212 : (x 13 5).toNat = 0 := by
    have r37213 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37214 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e37215 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e37216 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e37217 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e37218 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e37219 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b37220 := hb (x 11 7)
    have b37221 := hb (x 12 6)
    have b37222 := hb (x 13 5)
    have b37223 := hb (x 14 4)
    have b37224 := hb (x 15 11)
    have b37225 := hb (x 16 10)
    have b37226 := hb (x 17 9)
    have b37227 := hb (x 18 8)
    clear * - r37213 e37214 e37215 e37216 e37217 e37218 e37219 b37220 b37221 b37222 b37223 b37224 b37225 b37226 b37227 d37164 d37180 d36955 d37087 d37196
    omega
  have d37228 : (x 12 6).toNat = 0 := by
    have r37229 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37230 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e37231 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e37232 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e37233 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e37234 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e37235 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b37236 := hb (x 11 7)
    have b37237 := hb (x 12 6)
    have b37238 := hb (x 13 5)
    have b37239 := hb (x 14 4)
    have b37240 := hb (x 15 11)
    have b37241 := hb (x 16 10)
    have b37242 := hb (x 17 9)
    have b37243 := hb (x 18 8)
    clear * - r37229 e37230 e37231 e37232 e37233 e37234 e37235 b37236 b37237 b37238 b37239 b37240 b37241 b37242 b37243 d37164 d37180 d36955 d37087 d37196 d37212
    omega
  have d37244 : (x 11 7).toNat = 0 := by
    have r37245 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37246 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e37247 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e37248 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e37249 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e37250 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e37251 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b37252 := hb (x 11 7)
    have b37253 := hb (x 12 6)
    have b37254 := hb (x 13 5)
    have b37255 := hb (x 14 4)
    have b37256 := hb (x 15 11)
    have b37257 := hb (x 16 10)
    have b37258 := hb (x 17 9)
    have b37259 := hb (x 18 8)
    clear * - r37245 e37246 e37247 e37248 e37249 e37250 e37251 b37252 b37253 b37254 b37255 b37256 b37257 b37258 b37259 d37164 d37180 d36955 d37087 d37196 d37212 d37228
    omega
  have d37260 : (x 11 1 && x 11 7).toNat = 0 := by
    have r37261 := hand2 (x 11 1) (x 11 7)
    have b37262 := hb (x 11 7)
    have b37263 := hb (x 11 1 && x 11 7)
    clear * - r37261 b37262 b37263 d37244
    omega
  have d37264 : (x 10 1 && x 10 6).toNat = 1 := by
    have r37265 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37266 := hb (x 1 10)
    have b37267 := hb (x 11 5)
    have b37268 := hb (x 10 1 && x 10 6)
    have b37269 := hb (x 9 2 && x 9 7)
    have b37270 := hb (x 8 3 && x 8 8)
    have b37271 := hb (x 7 4 && x 7 9)
    have b37272 := hb (x 6 5 && x 6 10)
    have b37273 := hb (x 5 6 && x 5 11)
    have b37274 := hb (x 4 7 && x 4 12)
    have b37275 := hb (x 3 8 && x 3 13)
    have b37276 := hb (x 2 9 && x 2 14)
    clear * - r37265 b37266 b37267 b37268 b37269 b37270 b37271 b37272 b37273 b37274 b37275 b37276 d37055 d36662 d36310 d36338 d36366 d36492 d36722 g85 g86 g39
    omega
  have d37277 : (x 10 6).toNat = 1 := by
    have r37278 := hand2 (x 10 1) (x 10 6)
    have b37279 := hb (x 10 6)
    have b37280 := hb (x 10 1 && x 10 6)
    clear * - r37278 b37279 b37280 d37264
    omega
  have d37281 : (x 10 14).toNat = 1 := by
    have r37282 : (x 10 6).toNat ≤ (x 10 14).toNat := himp _ _ (hp6 10)
    have b37283 := hb (x 10 6)
    have b37284 := hb (x 10 14)
    clear * - r37282 b37283 b37284 d37277
    omega
  have d37285 : (x 9 1).toNat = 0 := by
    have r37286 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37287 := hb (x 9 1)
    have b37288 := hb (x 10 14)
    clear * - r37286 b37287 b37288 d37281
    omega
  have d37289 : (x 9 1 && x 9 14).toNat = 0 := by
    have r37290 := hand1 (x 9 1) (x 9 14)
    have b37291 := hb (x 9 1)
    have b37292 := hb (x 9 1 && x 9 14)
    clear * - r37290 b37291 b37292 d37285
    omega
  have d37293 : (x 8 2).toNat = 1 := by
    have r37294 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37295 := hb (x 8 2)
    have b37296 := hb (x 10 13)
    have b37297 := hb (x 9 1 && x 9 14)
    clear * - r37294 b37295 b37296 b37297 d36630 d37289
    omega
  have d37298 : (x 8 14).toNat = 1 := by
    have r37299 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b37300 := hb (x 8 2)
    have b37301 := hb (x 8 14)
    clear * - r37299 b37300 b37301 d37293
    omega
  have d37302 : (x 7 1).toNat = 0 := by
    have r37303 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37304 := hb (x 7 1)
    have b37305 := hb (x 8 14)
    clear * - r37303 b37304 b37305 d37298
    omega
  have d37306 : (x 7 1 && x 7 14).toNat = 0 := by
    have r37307 := hand1 (x 7 1) (x 7 14)
    have b37308 := hb (x 7 1)
    have b37309 := hb (x 7 1 && x 7 14)
    clear * - r37307 b37308 b37309 d37302
    omega
  have d37310 : (x 7 1 && x 7 11).toNat = 0 := by
    have r37311 := hand1 (x 7 1) (x 7 11)
    have b37312 := hb (x 7 1)
    have b37313 := hb (x 7 1 && x 7 11)
    clear * - r37311 b37312 b37313 d37302
    omega
  have d37314 : (x 8 10).toNat = 1 := by
    have r37315 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37316 := hb (x 3 5)
    have b37317 := hb (x 8 10)
    have b37318 := hb (x 7 1 && x 7 11)
    have b37319 := hb (x 6 2 && x 6 12)
    have b37320 := hb (x 5 3 && x 5 13)
    have b37321 := hb (x 4 4 && x 4 14)
    clear * - r37315 b37316 b37317 b37318 b37319 b37320 b37321 d37310 d36439 d36459 d36591 d36508
    omega
  have d37322 : (x 10 8).toNat = 0 := by
    have r37323 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37324 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e37325 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e37326 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e37327 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e37328 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e37329 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b37330 := hb (x 3 7)
    have b37331 := hb (x 4 6)
    have b37332 := hb (x 5 5)
    have b37333 := hb (x 6 4)
    have b37334 := hb (x 7 11)
    have b37335 := hb (x 8 10)
    have b37336 := hb (x 9 9)
    have b37337 := hb (x 10 8)
    clear * - r37323 e37324 e37325 e37326 e37327 e37328 e37329 b37330 b37331 b37332 b37333 b37334 b37335 b37336 b37337 d37314 d36447 d36467
    omega
  have d37338 : (x 10 2 && x 10 8).toNat = 0 := by
    have r37339 := hand2 (x 10 2) (x 10 8)
    have b37340 := hb (x 10 8)
    have b37341 := hb (x 10 2 && x 10 8)
    clear * - r37339 b37340 b37341 d37322
    omega
  have d37342 : (x 9 9).toNat = 0 := by
    have r37343 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37344 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e37345 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e37346 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e37347 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e37348 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e37349 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b37350 := hb (x 3 7)
    have b37351 := hb (x 4 6)
    have b37352 := hb (x 5 5)
    have b37353 := hb (x 6 4)
    have b37354 := hb (x 7 11)
    have b37355 := hb (x 8 10)
    have b37356 := hb (x 9 9)
    have b37357 := hb (x 10 8)
    clear * - r37343 e37344 e37345 e37346 e37347 e37348 e37349 b37350 b37351 b37352 b37353 b37354 b37355 b37356 b37357 d37322 d37314 d36447 d36467
    omega
  have d37358 : (x 9 3 && x 9 9).toNat = 0 := by
    have r37359 := hand2 (x 9 3) (x 9 9)
    have b37360 := hb (x 9 9)
    have b37361 := hb (x 9 3 && x 9 9)
    clear * - r37359 b37360 b37361 d37342
    omega
  have d37362 : (x 7 11).toNat = 0 := by
    have r37363 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37364 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e37365 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e37366 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e37367 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e37368 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e37369 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b37370 := hb (x 3 7)
    have b37371 := hb (x 4 6)
    have b37372 := hb (x 5 5)
    have b37373 := hb (x 6 4)
    have b37374 := hb (x 7 11)
    have b37375 := hb (x 8 10)
    have b37376 := hb (x 9 9)
    have b37377 := hb (x 10 8)
    clear * - r37363 e37364 e37365 e37366 e37367 e37368 e37369 b37370 b37371 b37372 b37373 b37374 b37375 b37376 b37377 d37322 d37342 d37314 d36447 d36467
    omega
  have d37378 : (x 7 5 && x 7 11).toNat = 0 := by
    have r37379 := hand2 (x 7 5) (x 7 11)
    have b37380 := hb (x 7 11)
    have b37381 := hb (x 7 5 && x 7 11)
    clear * - r37379 b37380 b37381 d37362
    omega
  have d37382 : (x 8 4 && x 8 10).toNat = 1 := by
    have r37383 : 1 ≤ (x 12 6).toNat + (x 11 1 && x 11 7).toNat + (x 10 2 && x 10 8).toNat + (x 9 3 && x 9 9).toNat + (x 8 4 && x 8 10).toNat + (x 7 5 && x 7 11).toNat + (x 6 6 && x 6 12).toNat + (x 5 7 && x 5 13).toNat + (x 4 8 && x 4 14).toNat + (x 3 9).toNat := by have q := hcov6 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37384 := hb (x 3 9)
    have b37385 := hb (x 12 6)
    have b37386 := hb (x 11 1 && x 11 7)
    have b37387 := hb (x 10 2 && x 10 8)
    have b37388 := hb (x 9 3 && x 9 9)
    have b37389 := hb (x 8 4 && x 8 10)
    have b37390 := hb (x 7 5 && x 7 11)
    have b37391 := hb (x 6 6 && x 6 12)
    have b37392 := hb (x 5 7 && x 5 13)
    have b37393 := hb (x 4 8 && x 4 14)
    clear * - r37383 b37384 b37385 b37386 b37387 b37388 b37389 b37390 b37391 b37392 b37393 d37228 d37260 d37338 d37358 d37378 d36443 d36463 g105 g51
    omega
  have d37394 : (x 8 4).toNat = 1 := by
    have r37395 := hand1 (x 8 4) (x 8 10)
    have b37396 := hb (x 8 4)
    have b37397 := hb (x 8 4 && x 8 10)
    clear * - r37395 b37396 b37397 d37382
    omega
  have d37398 : (x 8 12).toNat = 1 := by
    have r37399 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b37400 := hb (x 8 4)
    have b37401 := hb (x 8 12)
    clear * - r37399 b37400 b37401 d37394
    omega
  have d37402 : (x 7 13).toNat = 0 := by
    have r37403 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37404 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e37405 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b37406 := hb (x 5 3)
    have b37407 := hb (x 6 2)
    have b37408 := hb (x 7 13)
    have b37409 := hb (x 8 12)
    clear * - r37403 e37404 e37405 b37406 b37407 b37408 b37409 d37398
    omega
  have d37410 : (x 6 1 && x 6 14).toNat = 1 := by
    have r37411 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37412 := hb (x 5 2)
    have b37413 := hb (x 7 13)
    have b37414 := hb (x 6 1 && x 6 14)
    clear * - r37411 b37412 b37413 b37414 d37402 d36500
    omega
  have d37415 : (x 6 14).toNat = 1 := by
    have r37416 := hand2 (x 6 1) (x 6 14)
    have b37417 := hb (x 6 14)
    have b37418 := hb (x 6 1 && x 6 14)
    clear * - r37416 b37417 b37418 d37410
    omega
  have d37419 : (x 6 1).toNat = 1 := by
    have r37420 := hand1 (x 6 1) (x 6 14)
    have b37421 := hb (x 6 1)
    have b37422 := hb (x 6 1 && x 6 14)
    clear * - r37420 b37421 b37422 d37410
    omega
  have d37423 : (x 7 14).toNat = 0 := by
    have r37424 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37425 := hb (x 6 1)
    have b37426 := hb (x 7 14)
    clear * - r37424 b37425 b37426 d37419
    omega
  have d37427 : (x 7 6).toNat = 0 := by
    have r37428 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
    have b37429 := hb (x 7 6)
    have b37430 := hb (x 7 14)
    clear * - r37428 b37429 b37430 d37423
    omega
  have d37431 : (x 7 2).toNat = 0 := by
    have r37432 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b37433 := hb (x 7 2)
    have b37434 := hb (x 7 14)
    clear * - r37432 b37433 b37434 d37423
    omega
  have d37435 : (x 6 2).toNat = 0 := by
    have r37436 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37437 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e37438 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b37439 := hb (x 5 3)
    have b37440 := hb (x 6 2)
    have b37441 := hb (x 7 13)
    have b37442 := hb (x 8 12)
    clear * - r37436 e37437 e37438 b37439 b37440 b37441 b37442 d37398 d37402
    omega
  have d37443 : (x 8 13).toNat = 1 := by
    have r37444 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37445 := hb (x 6 2)
    have b37446 := hb (x 8 13)
    have b37447 := hb (x 7 1 && x 7 14)
    clear * - r37444 b37445 b37446 b37447 d37306 d37435
    omega
  have d37448 : (x 8 1).toNat = 1 := by
    have r37449 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b37450 := hb (x 8 1)
    have b37451 := hb (x 8 13)
    clear * - r37449 b37450 b37451 d37443
    omega
  have d37452 : (x 9 14).toNat = 0 := by
    have r37453 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37454 := hb (x 8 1)
    have b37455 := hb (x 9 14)
    clear * - r37453 b37454 b37455 d37448
    omega
  have d37456 : (x 9 4 && x 9 14).toNat = 0 := by
    have r37457 := hand2 (x 9 4) (x 9 14)
    have b37458 := hb (x 9 14)
    have b37459 := hb (x 9 4 && x 9 14)
    clear * - r37457 b37458 b37459 d37452
    omega
  have d37460 : (x 8 5).toNat = 1 := by
    have r37461 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37462 := hb (x 8 5)
    have b37463 := hb (x 13 10)
    have b37464 := hb (x 12 1 && x 12 11)
    have b37465 := hb (x 11 2 && x 11 12)
    have b37466 := hb (x 10 3 && x 10 13)
    have b37467 := hb (x 9 4 && x 9 14)
    clear * - r37461 b37462 b37463 b37464 b37465 b37466 b37467 d36822 d36862 d36614 d36638 d37456
    omega
  have d37468 : (x 13 8).toNat = 0 := by
    have r37469 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37470 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e37471 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e37472 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e37473 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e37474 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e37475 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b37476 := hb (x 6 7)
    have b37477 := hb (x 7 6)
    have b37478 := hb (x 8 5)
    have b37479 := hb (x 9 4)
    have b37480 := hb (x 10 11)
    have b37481 := hb (x 11 10)
    have b37482 := hb (x 12 9)
    have b37483 := hb (x 13 8)
    clear * - r37469 e37470 e37471 e37472 e37473 e37474 e37475 b37476 b37477 b37478 b37479 b37480 b37481 b37482 b37483 d37460 d37427
    omega
  have d37484 : (x 12 9).toNat = 0 := by
    have r37485 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37486 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e37487 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e37488 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e37489 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e37490 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e37491 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b37492 := hb (x 6 7)
    have b37493 := hb (x 7 6)
    have b37494 := hb (x 8 5)
    have b37495 := hb (x 9 4)
    have b37496 := hb (x 10 11)
    have b37497 := hb (x 11 10)
    have b37498 := hb (x 12 9)
    have b37499 := hb (x 13 8)
    clear * - r37485 e37486 e37487 e37488 e37489 e37490 e37491 b37492 b37493 b37494 b37495 b37496 b37497 b37498 b37499 d37468 d37460 d37427
    omega
  have d37500 : (x 11 10).toNat = 0 := by
    have r37501 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37502 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e37503 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e37504 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e37505 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e37506 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e37507 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b37508 := hb (x 6 7)
    have b37509 := hb (x 7 6)
    have b37510 := hb (x 8 5)
    have b37511 := hb (x 9 4)
    have b37512 := hb (x 10 11)
    have b37513 := hb (x 11 10)
    have b37514 := hb (x 12 9)
    have b37515 := hb (x 13 8)
    clear * - r37501 e37502 e37503 e37504 e37505 e37506 e37507 b37508 b37509 b37510 b37511 b37512 b37513 b37514 b37515 d37468 d37484 d37460 d37427
    omega
  have d37516 : (x 10 11).toNat = 0 := by
    have r37517 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37518 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e37519 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e37520 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e37521 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e37522 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e37523 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b37524 := hb (x 6 7)
    have b37525 := hb (x 7 6)
    have b37526 := hb (x 8 5)
    have b37527 := hb (x 9 4)
    have b37528 := hb (x 10 11)
    have b37529 := hb (x 11 10)
    have b37530 := hb (x 12 9)
    have b37531 := hb (x 13 8)
    clear * - r37517 e37518 e37519 e37520 e37521 e37522 e37523 b37524 b37525 b37526 b37527 b37528 b37529 b37530 b37531 d37468 d37484 d37500 d37460 d37427
    omega
  have d37532 : (x 10 6 && x 10 11).toNat = 0 := by
    have r37533 := hand2 (x 10 6) (x 10 11)
    have b37534 := hb (x 10 11)
    have b37535 := hb (x 10 6 && x 10 11)
    clear * - r37533 b37534 b37535 d37516
    omega
  have d37536 : (x 9 5 && x 9 14).toNat = 0 := by
    have r37537 := hand2 (x 9 5) (x 9 14)
    have b37538 := hb (x 9 14)
    have b37539 := hb (x 9 5 && x 9 14)
    clear * - r37537 b37538 b37539 d37452
    omega
  have d37540 : (x 8 6).toNat = 1 := by
    have r37541 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37542 := hb (x 8 6)
    have b37543 := hb (x 14 9)
    have b37544 := hb (x 13 1 && x 13 10)
    have b37545 := hb (x 12 2 && x 12 11)
    have b37546 := hb (x 11 3 && x 11 12)
    have b37547 := hb (x 10 4 && x 10 13)
    have b37548 := hb (x 9 5 && x 9 14)
    clear * - r37541 b37542 b37543 b37544 b37545 b37546 b37547 b37548 d36802 d36838 d36866 d36618 d36642 d37536
    omega
  have d37549 : (x 14 8).toNat = 0 := by
    have r37550 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37551 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e37552 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e37553 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e37554 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e37555 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e37556 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b37557 := hb (x 7 7)
    have b37558 := hb (x 8 6)
    have b37559 := hb (x 9 5)
    have b37560 := hb (x 10 4)
    have b37561 := hb (x 11 11)
    have b37562 := hb (x 12 10)
    have b37563 := hb (x 13 9)
    have b37564 := hb (x 14 8)
    clear * - r37550 e37551 e37552 e37553 e37554 e37555 e37556 b37557 b37558 b37559 b37560 b37561 b37562 b37563 b37564 d37540
    omega
  have d37565 : (x 13 9).toNat = 0 := by
    have r37566 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37567 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e37568 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e37569 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e37570 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e37571 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e37572 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b37573 := hb (x 7 7)
    have b37574 := hb (x 8 6)
    have b37575 := hb (x 9 5)
    have b37576 := hb (x 10 4)
    have b37577 := hb (x 11 11)
    have b37578 := hb (x 12 10)
    have b37579 := hb (x 13 9)
    have b37580 := hb (x 14 8)
    clear * - r37566 e37567 e37568 e37569 e37570 e37571 e37572 b37573 b37574 b37575 b37576 b37577 b37578 b37579 b37580 d37549 d37540
    omega
  have d37581 : (x 12 10).toNat = 0 := by
    have r37582 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37583 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e37584 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e37585 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e37586 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e37587 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e37588 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b37589 := hb (x 7 7)
    have b37590 := hb (x 8 6)
    have b37591 := hb (x 9 5)
    have b37592 := hb (x 10 4)
    have b37593 := hb (x 11 11)
    have b37594 := hb (x 12 10)
    have b37595 := hb (x 13 9)
    have b37596 := hb (x 14 8)
    clear * - r37582 e37583 e37584 e37585 e37586 e37587 e37588 b37589 b37590 b37591 b37592 b37593 b37594 b37595 b37596 d37549 d37565 d37540
    omega
  have d37597 : (x 11 11).toNat = 0 := by
    have r37598 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37599 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e37600 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e37601 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e37602 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e37603 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e37604 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b37605 := hb (x 7 7)
    have b37606 := hb (x 8 6)
    have b37607 := hb (x 9 5)
    have b37608 := hb (x 10 4)
    have b37609 := hb (x 11 11)
    have b37610 := hb (x 12 10)
    have b37611 := hb (x 13 9)
    have b37612 := hb (x 14 8)
    clear * - r37598 e37599 e37600 e37601 e37602 e37603 e37604 b37605 b37606 b37607 b37608 b37609 b37610 b37611 b37612 d37549 d37565 d37581 d37540
    omega
  have d37613 : (x 10 4).toNat = 0 := by
    have r37614 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37615 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e37616 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e37617 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e37618 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e37619 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e37620 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b37621 := hb (x 7 7)
    have b37622 := hb (x 8 6)
    have b37623 := hb (x 9 5)
    have b37624 := hb (x 10 4)
    have b37625 := hb (x 11 11)
    have b37626 := hb (x 12 10)
    have b37627 := hb (x 13 9)
    have b37628 := hb (x 14 8)
    clear * - r37614 e37615 e37616 e37617 e37618 e37619 e37620 b37621 b37622 b37623 b37624 b37625 b37626 b37627 b37628 d37549 d37565 d37581 d37597 d37540
    omega
  have d37629 : (x 10 4 && x 10 14).toNat = 0 := by
    have r37630 := hand1 (x 10 4) (x 10 14)
    have b37631 := hb (x 10 4)
    have b37632 := hb (x 10 4 && x 10 14)
    clear * - r37630 b37631 b37632 d37613
    omega
  have d37633 : (x 9 5).toNat = 0 := by
    have r37634 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37635 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e37636 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e37637 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e37638 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e37639 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e37640 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b37641 := hb (x 7 7)
    have b37642 := hb (x 8 6)
    have b37643 := hb (x 9 5)
    have b37644 := hb (x 10 4)
    have b37645 := hb (x 11 11)
    have b37646 := hb (x 12 10)
    have b37647 := hb (x 13 9)
    have b37648 := hb (x 14 8)
    clear * - r37634 e37635 e37636 e37637 e37638 e37639 e37640 b37641 b37642 b37643 b37644 b37645 b37646 b37647 b37648 d37549 d37565 d37581 d37597 d37613 d37540
    omega
  have d37649 : (x 9 7 && x 9 14).toNat = 0 := by
    have r37650 := hand2 (x 9 7) (x 9 14)
    have b37651 := hb (x 9 14)
    have b37652 := hb (x 9 7 && x 9 14)
    clear * - r37650 b37651 b37652 d37452
    omega
  have d37653 : (x 16 7).toNat = 1 := by
    have r37654 : 1 ≤ (x 16 7).toNat + (x 15 1 && x 15 8).toNat + (x 14 2 && x 14 9).toNat + (x 13 3 && x 13 10).toNat + (x 12 4 && x 12 11).toNat + (x 11 5 && x 11 12).toNat + (x 10 6 && x 10 13).toNat + (x 9 7 && x 9 14).toNat + (x 8 8).toNat := by have q := hcov7 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37655 := hb (x 8 8)
    have b37656 := hb (x 16 7)
    have b37657 := hb (x 15 1 && x 15 8)
    have b37658 := hb (x 14 2 && x 14 9)
    have b37659 := hb (x 13 3 && x 13 10)
    have b37660 := hb (x 12 4 && x 12 11)
    have b37661 := hb (x 11 5 && x 11 12)
    have b37662 := hb (x 10 6 && x 10 13)
    have b37663 := hb (x 9 7 && x 9 14)
    clear * - r37654 b37655 b37656 b37657 b37658 b37659 b37660 b37661 b37662 b37663 d36798 d36818 d36842 d36870 d36622 d36646 d37649 d36290
    omega
  have d37664 : (x 23 8).toNat = 0 := by
    have r37665 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37666 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e37667 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e37668 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e37669 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e37670 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e37671 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b37672 := hb (x 16 7)
    have b37673 := hb (x 17 6)
    have b37674 := hb (x 18 5)
    have b37675 := hb (x 19 4)
    have b37676 := hb (x 20 11)
    have b37677 := hb (x 21 10)
    have b37678 := hb (x 22 9)
    have b37679 := hb (x 23 8)
    clear * - r37665 e37666 e37667 e37668 e37669 e37670 e37671 b37672 b37673 b37674 b37675 b37676 b37677 b37678 b37679 d37653
    omega
  have d37680 : (x 22 9).toNat = 0 := by
    have r37681 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37682 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e37683 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e37684 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e37685 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e37686 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e37687 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b37688 := hb (x 16 7)
    have b37689 := hb (x 17 6)
    have b37690 := hb (x 18 5)
    have b37691 := hb (x 19 4)
    have b37692 := hb (x 20 11)
    have b37693 := hb (x 21 10)
    have b37694 := hb (x 22 9)
    have b37695 := hb (x 23 8)
    clear * - r37681 e37682 e37683 e37684 e37685 e37686 e37687 b37688 b37689 b37690 b37691 b37692 b37693 b37694 b37695 d37664 d37653
    omega
  have d37696 : (x 21 10).toNat = 0 := by
    have r37697 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37698 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e37699 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e37700 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e37701 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e37702 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e37703 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b37704 := hb (x 16 7)
    have b37705 := hb (x 17 6)
    have b37706 := hb (x 18 5)
    have b37707 := hb (x 19 4)
    have b37708 := hb (x 20 11)
    have b37709 := hb (x 21 10)
    have b37710 := hb (x 22 9)
    have b37711 := hb (x 23 8)
    clear * - r37697 e37698 e37699 e37700 e37701 e37702 e37703 b37704 b37705 b37706 b37707 b37708 b37709 b37710 b37711 d37664 d37680 d37653
    omega
  have d37712 : (x 21 1 && x 21 10).toNat = 0 := by
    have r37713 := hand2 (x 21 1) (x 21 10)
    have b37714 := hb (x 21 10)
    have b37715 := hb (x 21 1 && x 21 10)
    clear * - r37713 b37714 b37715 d37696
    omega
  have d37716 : (x 20 11).toNat = 0 := by
    have r37717 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37718 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e37719 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e37720 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e37721 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e37722 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e37723 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b37724 := hb (x 16 7)
    have b37725 := hb (x 17 6)
    have b37726 := hb (x 18 5)
    have b37727 := hb (x 19 4)
    have b37728 := hb (x 20 11)
    have b37729 := hb (x 21 10)
    have b37730 := hb (x 22 9)
    have b37731 := hb (x 23 8)
    clear * - r37717 e37718 e37719 e37720 e37721 e37722 e37723 b37724 b37725 b37726 b37727 b37728 b37729 b37730 b37731 d37664 d37680 d37696 d37653
    omega
  have d37732 : (x 20 2 && x 20 11).toNat = 0 := by
    have r37733 := hand2 (x 20 2) (x 20 11)
    have b37734 := hb (x 20 11)
    have b37735 := hb (x 20 2 && x 20 11)
    clear * - r37733 b37734 b37735 d37716
    omega
  have d37736 : (x 19 3 && x 19 12).toNat = 1 := by
    have r37737 : 1 ≤ (x 22 9).toNat + (x 21 1 && x 21 10).toNat + (x 20 2 && x 20 11).toNat + (x 19 3 && x 19 12).toNat + (x 18 4 && x 18 13).toNat + (x 17 5 && x 17 14).toNat + (x 16 6).toNat := by have q := hcov9 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37738 := hb (x 16 6)
    have b37739 := hb (x 22 9)
    have b37740 := hb (x 21 1 && x 21 10)
    have b37741 := hb (x 20 2 && x 20 11)
    have b37742 := hb (x 19 3 && x 19 12)
    have b37743 := hb (x 18 4 && x 18 13)
    have b37744 := hb (x 17 5 && x 17 14)
    clear * - r37737 b37738 b37739 b37740 b37741 b37742 b37743 b37744 d37680 d37712 d37732 d37107 d37123 d36947
    omega
  have d37745 : (x 19 12).toNat = 1 := by
    have r37746 := hand2 (x 19 3) (x 19 12)
    have b37747 := hb (x 19 12)
    have b37748 := hb (x 19 3 && x 19 12)
    clear * - r37746 b37747 b37748 d37736
    omega
  have d37749 : (x 18 13).toNat = 0 := by
    have r37750 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37751 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e37752 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b37753 := hb (x 16 3)
    have b37754 := hb (x 17 2)
    have b37755 := hb (x 18 13)
    have b37756 := hb (x 19 12)
    clear * - r37750 e37751 e37752 b37753 b37754 b37755 b37756 d37745
    omega
  have d37757 : (x 17 1 && x 17 14).toNat = 1 := by
    have r37758 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37759 := hb (x 16 2)
    have b37760 := hb (x 18 13)
    have b37761 := hb (x 17 1 && x 17 14)
    clear * - r37758 b37759 b37760 b37761 d37749 d36951
    omega
  have d37762 : (x 17 1).toNat = 1 := by
    have r37763 := hand1 (x 17 1) (x 17 14)
    have b37764 := hb (x 17 1)
    have b37765 := hb (x 17 1 && x 17 14)
    clear * - r37763 b37764 b37765 d37757
    omega
  have d37766 : (x 18 14).toNat = 0 := by
    have r37767 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37768 := hb (x 17 1)
    have b37769 := hb (x 18 14)
    clear * - r37767 b37768 b37769 d37762
    omega
  have d37770 : (x 18 1 && x 18 14).toNat = 0 := by
    have r37771 := hand2 (x 18 1) (x 18 14)
    have b37772 := hb (x 18 14)
    have b37773 := hb (x 18 1 && x 18 14)
    clear * - r37771 b37772 b37773 d37766
    omega
  have d37774 : (x 18 2).toNat = 0 := by
    have r37775 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
    have b37776 := hb (x 18 2)
    have b37777 := hb (x 18 14)
    clear * - r37775 b37776 b37777 d37766
    omega
  have d37778 : (x 18 2 && x 18 11).toNat = 0 := by
    have r37779 := hand1 (x 18 2) (x 18 11)
    have b37780 := hb (x 18 2)
    have b37781 := hb (x 18 2 && x 18 11)
    clear * - r37779 b37780 b37781 d37774
    omega
  have d37782 : (x 17 2).toNat = 0 := by
    have r37783 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37784 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e37785 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b37786 := hb (x 16 3)
    have b37787 := hb (x 17 2)
    have b37788 := hb (x 18 13)
    have b37789 := hb (x 19 12)
    clear * - r37783 e37784 e37785 b37786 b37787 b37788 b37789 d37745 d37749
    omega
  have d37790 : (x 19 13).toNat = 1 := by
    have r37791 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37792 := hb (x 17 2)
    have b37793 := hb (x 19 13)
    have b37794 := hb (x 18 1 && x 18 14)
    clear * - r37791 b37792 b37793 b37794 d37770 d37782
    omega
  have d37795 : (x 19 1).toNat = 1 := by
    have r37796 : (x 19 13).toNat ≤ (x 19 1).toNat := himp _ _ (hp13 19)
    have b37797 := hb (x 19 1)
    have b37798 := hb (x 19 13)
    clear * - r37796 b37797 b37798 d37790
    omega
  have d37799 : (x 20 12).toNat = 0 := by
    have r37800 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37801 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e37802 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b37803 := hb (x 17 3)
    have b37804 := hb (x 18 2)
    have b37805 := hb (x 19 13)
    have b37806 := hb (x 20 12)
    clear * - r37800 e37801 e37802 b37803 b37804 b37805 b37806 d37790 d37774
    omega
  have d37807 : (x 17 3).toNat = 0 := by
    have r37808 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37809 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e37810 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b37811 := hb (x 17 3)
    have b37812 := hb (x 18 2)
    have b37813 := hb (x 19 13)
    have b37814 := hb (x 20 12)
    clear * - r37808 e37809 e37810 b37811 b37812 b37813 b37814 d37799 d37790 d37774
    omega
  have d37815 : (x 9 12).toNat = 0 := by
    have r37816 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37817 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e37818 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b37819 := hb (x 6 3)
    have b37820 := hb (x 7 2)
    have b37821 := hb (x 8 13)
    have b37822 := hb (x 9 12)
    clear * - r37816 e37817 e37818 b37819 b37820 b37821 b37822 d37443 d37431
    omega
  have d37823 : (x 9 7 && x 9 12).toNat = 0 := by
    have r37824 := hand2 (x 9 7) (x 9 12)
    have b37825 := hb (x 9 12)
    have b37826 := hb (x 9 7 && x 9 12)
    clear * - r37824 b37825 b37826 d37815
    omega
  have d37827 : (x 15 1 && x 15 6).toNat = 1 := by
    have r37828 : 1 ≤ (x 16 5).toNat + (x 15 1 && x 15 6).toNat + (x 14 2 && x 14 7).toNat + (x 13 3 && x 13 8).toNat + (x 12 4 && x 12 9).toNat + (x 11 5 && x 11 10).toNat + (x 10 6 && x 10 11).toNat + (x 9 7 && x 9 12).toNat + (x 8 8 && x 8 13).toNat + (x 7 9 && x 7 14).toNat + (x 6 10).toNat := by have q := hcov5 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37829 := hb (x 6 10)
    have b37830 := hb (x 16 5)
    have b37831 := hb (x 15 1 && x 15 6)
    have b37832 := hb (x 14 2 && x 14 7)
    have b37833 := hb (x 13 3 && x 13 8)
    have b37834 := hb (x 12 4 && x 12 9)
    have b37835 := hb (x 11 5 && x 11 10)
    have b37836 := hb (x 10 6 && x 10 11)
    have b37837 := hb (x 9 7 && x 9 12)
    have b37838 := hb (x 8 8 && x 8 13)
    have b37839 := hb (x 7 9 && x 7 14)
    clear * - r37828 b37829 b37830 b37831 b37832 b37833 b37834 b37835 b37836 b37837 b37838 b37839 d37160 d36979 d37011 d37047 d37071 d37532 d37823 d36306 d36334 d36346
    omega
  have d37840 : (x 15 6).toNat = 1 := by
    have r37841 := hand2 (x 15 1) (x 15 6)
    have b37842 := hb (x 15 6)
    have b37843 := hb (x 15 1 && x 15 6)
    clear * - r37841 b37842 b37843 d37827
    omega
  have d37844 : (x 21 8).toNat = 0 := by
    have r37845 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37846 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
    have e37847 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
    have e37848 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
    have e37849 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
    have e37850 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
    have e37851 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
    have b37852 := hb (x 14 7)
    have b37853 := hb (x 15 6)
    have b37854 := hb (x 16 5)
    have b37855 := hb (x 17 4)
    have b37856 := hb (x 18 11)
    have b37857 := hb (x 19 10)
    have b37858 := hb (x 20 9)
    have b37859 := hb (x 21 8)
    clear * - r37845 e37846 e37847 e37848 e37849 e37850 e37851 b37852 b37853 b37854 b37855 b37856 b37857 b37858 b37859 d37144 d37160 d37840
    omega
  have d37860 : (x 20 9).toNat = 0 := by
    have r37861 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37862 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
    have e37863 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
    have e37864 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
    have e37865 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
    have e37866 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
    have e37867 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
    have b37868 := hb (x 14 7)
    have b37869 := hb (x 15 6)
    have b37870 := hb (x 16 5)
    have b37871 := hb (x 17 4)
    have b37872 := hb (x 18 11)
    have b37873 := hb (x 19 10)
    have b37874 := hb (x 20 9)
    have b37875 := hb (x 21 8)
    clear * - r37861 e37862 e37863 e37864 e37865 e37866 e37867 b37868 b37869 b37870 b37871 b37872 b37873 b37874 b37875 d37844 d37144 d37160 d37840
    omega
  have d37876 : (x 19 10).toNat = 0 := by
    have r37877 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37878 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
    have e37879 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
    have e37880 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
    have e37881 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
    have e37882 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
    have e37883 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
    have b37884 := hb (x 14 7)
    have b37885 := hb (x 15 6)
    have b37886 := hb (x 16 5)
    have b37887 := hb (x 17 4)
    have b37888 := hb (x 18 11)
    have b37889 := hb (x 19 10)
    have b37890 := hb (x 20 9)
    have b37891 := hb (x 21 8)
    clear * - r37877 e37878 e37879 e37880 e37881 e37882 e37883 b37884 b37885 b37886 b37887 b37888 b37889 b37890 b37891 d37844 d37860 d37144 d37160 d37840
    omega
  have d37892 : (x 19 1 && x 19 10).toNat = 0 := by
    have r37893 := hand2 (x 19 1) (x 19 10)
    have b37894 := hb (x 19 10)
    have b37895 := hb (x 19 1 && x 19 10)
    clear * - r37893 b37894 b37895 d37876
    omega
  have d37896 : (x 16 4).toNat = 0 := by
    have r37897 : (x 19 1).toNat + (x 18 2).toNat + (x 17 3).toNat + (x 16 4).toNat + (x 15 5).toNat + (x 14 6).toNat + (x 13 7).toNat + (x 12 8).toNat + (x 11 9).toNat + (x 10 10).toNat + (x 9 11).toNat + (x 8 12).toNat + (x 7 13).toNat + (x 6 14).toNat = 3 := by have q := hcount 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37898 := hb (x 6 14)
    have b37899 := hb (x 7 13)
    have b37900 := hb (x 8 12)
    have b37901 := hb (x 9 11)
    have b37902 := hb (x 10 10)
    have b37903 := hb (x 11 9)
    have b37904 := hb (x 12 8)
    have b37905 := hb (x 13 7)
    have b37906 := hb (x 14 6)
    have b37907 := hb (x 15 5)
    have b37908 := hb (x 16 4)
    have b37909 := hb (x 17 3)
    have b37910 := hb (x 18 2)
    have b37911 := hb (x 19 1)
    clear * - r37897 b37898 b37899 b37900 b37901 b37902 b37903 b37904 b37905 b37906 b37907 b37908 b37909 b37910 b37911 d37795 d37774 d37807 d37398 d37402 d37415
    omega
  have d37912 : (x 15 5).toNat = 0 := by
    have r37913 : (x 19 1).toNat + (x 18 2).toNat + (x 17 3).toNat + (x 16 4).toNat + (x 15 5).toNat + (x 14 6).toNat + (x 13 7).toNat + (x 12 8).toNat + (x 11 9).toNat + (x 10 10).toNat + (x 9 11).toNat + (x 8 12).toNat + (x 7 13).toNat + (x 6 14).toNat = 3 := by have q := hcount 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37914 := hb (x 6 14)
    have b37915 := hb (x 7 13)
    have b37916 := hb (x 8 12)
    have b37917 := hb (x 9 11)
    have b37918 := hb (x 10 10)
    have b37919 := hb (x 11 9)
    have b37920 := hb (x 12 8)
    have b37921 := hb (x 13 7)
    have b37922 := hb (x 14 6)
    have b37923 := hb (x 15 5)
    have b37924 := hb (x 16 4)
    have b37925 := hb (x 17 3)
    have b37926 := hb (x 18 2)
    have b37927 := hb (x 19 1)
    clear * - r37913 b37914 b37915 b37916 b37917 b37918 b37919 b37920 b37921 b37922 b37923 b37924 b37925 b37926 b37927 d37795 d37774 d37807 d37896 d37398 d37402 d37415
    omega
  have d37928 : (x 15 5 && x 15 14).toNat = 0 := by
    have r37929 := hand1 (x 15 5) (x 15 14)
    have b37930 := hb (x 15 5)
    have b37931 := hb (x 15 5 && x 15 14)
    clear * - r37929 b37930 b37931 d37912
    omega
  have d37932 : (x 14 6).toNat = 1 := by
    have r37933 : 1 ≤ (x 20 9).toNat + (x 19 1 && x 19 10).toNat + (x 18 2 && x 18 11).toNat + (x 17 3 && x 17 12).toNat + (x 16 4 && x 16 13).toNat + (x 15 5 && x 15 14).toNat + (x 14 6).toNat := by have q := hcov9 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37934 := hb (x 14 6)
    have b37935 := hb (x 20 9)
    have b37936 := hb (x 19 1 && x 19 10)
    have b37937 := hb (x 18 2 && x 18 11)
    have b37938 := hb (x 17 3 && x 17 12)
    have b37939 := hb (x 16 4 && x 16 13)
    have b37940 := hb (x 15 5 && x 15 14)
    clear * - r37933 b37934 b37935 b37936 b37937 b37938 b37939 b37940 d37860 d37892 d37778 d37140 d37156 d37928
    omega
  have d37941 : (x 14 14).toNat = 1 := by
    have r37942 : (x 14 6).toNat ≤ (x 14 14).toNat := himp _ _ (hp6 14)
    have b37943 := hb (x 14 6)
    have b37944 := hb (x 14 14)
    clear * - r37942 b37943 b37944 d37932
    omega
  have d37945 : (x 13 1).toNat = 0 := by
    have r37946 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37947 := hb (x 13 1)
    have b37948 := hb (x 14 14)
    clear * - r37946 b37947 b37948 d37941
    omega
  have d37949 : (x 13 1 && x 13 14).toNat = 0 := by
    have r37950 := hand1 (x 13 1) (x 13 14)
    have b37951 := hb (x 13 1)
    have b37952 := hb (x 13 1 && x 13 14)
    clear * - r37950 b37951 b37952 d37945
    omega
  have d37953 : (x 12 2).toNat = 1 := by
    have r37954 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37955 := hb (x 12 2)
    have b37956 := hb (x 14 13)
    have b37957 := hb (x 13 1 && x 13 14)
    clear * - r37954 b37955 b37956 b37957 d36910 d37949
    omega
  have d37958 : (x 12 14).toNat = 1 := by
    have r37959 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
    have b37960 := hb (x 12 2)
    have b37961 := hb (x 12 14)
    clear * - r37959 b37960 b37961 d37953
    omega
  have d37962 : (x 11 1).toNat = 0 := by
    have r37963 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37964 := hb (x 11 1)
    have b37965 := hb (x 12 14)
    clear * - r37963 b37964 b37965 d37958
    omega
  have d37966 : (x 11 13).toNat = 0 := by
    have r37967 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b37968 := hb (x 11 1)
    have b37969 := hb (x 11 13)
    clear * - r37967 b37968 b37969 d37962
    omega
  have d37970 : (x 11 3 && x 11 13).toNat = 0 := by
    have r37971 := hand2 (x 11 3) (x 11 13)
    have b37972 := hb (x 11 13)
    have b37973 := hb (x 11 3 && x 11 13)
    clear * - r37971 b37972 b37973 d37966
    omega
  have d37974 : (x 12 2 && x 12 12).toNat = 1 := by
    have r37975 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b37976 := hb (x 9 5)
    have b37977 := hb (x 14 10)
    have b37978 := hb (x 13 1 && x 13 11)
    have b37979 := hb (x 12 2 && x 12 12)
    have b37980 := hb (x 11 3 && x 11 13)
    have b37981 := hb (x 10 4 && x 10 14)
    clear * - r37975 b37976 b37977 b37978 b37979 b37980 b37981 d36987 d37023 d37970 d37629 d37633
    omega
  have d37982 : (x 12 12).toNat = 1 := by
    have r37983 := hand2 (x 12 2) (x 12 12)
    have b37984 := hb (x 12 12)
    have b37985 := hb (x 12 2 && x 12 12)
    clear * - r37983 b37984 b37985 d37974
    omega
  have d37986 : (x 10 2).toNat = 0 := by
    have r37987 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e37988 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e37989 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b37990 := hb (x 9 3)
    have b37991 := hb (x 10 2)
    have b37992 := hb (x 11 13)
    have b37993 := hb (x 12 12)
    clear * - r37987 e37988 e37989 b37990 b37991 b37992 b37993 d37982 d37966
    omega
  have d37994 : (x 10 10).toNat = 0 := by
    have r37995 : (x 10 10).toNat ≤ (x 10 2).toNat := himp _ _ (hp10 10)
    have b37996 := hb (x 10 2)
    have b37997 := hb (x 10 10)
    clear * - r37995 b37996 b37997 d37986
    omega
  have d37998 : (x 10 6 && x 10 10).toNat = 0 := by
    have r37999 := hand2 (x 10 6) (x 10 10)
    have b38000 := hb (x 10 10)
    have b38001 := hb (x 10 6 && x 10 10)
    clear * - r37999 b38000 b38001 d37994
    omega
  have d38002 : (x 9 3).toNat = 0 := by
    have r38003 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e38004 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e38005 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b38006 := hb (x 9 3)
    have b38007 := hb (x 10 2)
    have b38008 := hb (x 11 13)
    have b38009 := hb (x 12 12)
    clear * - r38003 e38004 e38005 b38006 b38007 b38008 b38009 d37982 d37966 d37986
    omega
  have d38010 : (x 9 11).toNat = 0 := by
    have r38011 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
    have b38012 := hb (x 9 3)
    have b38013 := hb (x 9 11)
    clear * - r38011 b38012 b38013 d38002
    omega
  have d38014 : (x 9 7 && x 9 11).toNat = 0 := by
    have r38015 := hand2 (x 9 7) (x 9 11)
    have b38016 := hb (x 9 11)
    have b38017 := hb (x 9 7 && x 9 11)
    clear * - r38015 b38016 b38017 d38010
    omega
  have r38018 : 1 ≤ (x 16 4).toNat + (x 15 1 && x 15 5).toNat + (x 14 2 && x 14 6).toNat + (x 13 3 && x 13 7).toNat + (x 12 4 && x 12 8).toNat + (x 11 5 && x 11 9).toNat + (x 10 6 && x 10 10).toNat + (x 9 7 && x 9 11).toNat + (x 8 8 && x 8 12).toNat + (x 7 9 && x 7 13).toNat + (x 6 10 && x 6 14).toNat + (x 5 11).toNat := by have q := hcov4 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e38019 : (x 15 1 && x 15 5).toNat = (x 15 5).toNat := handr _ _ (fun h => hp13 15 (hp5 15 (h)))
  have e38020 : (x 6 10 && x 6 14).toNat = (x 6 10).toNat := handl _ _ (fun h => hp2 6 (hp10 6 (h)))
  have b38021 := hb (x 5 11)
  have b38022 := hb (x 6 10)
  have b38023 := hb (x 15 5)
  have b38024 := hb (x 16 4)
  have b38025 := hb (x 14 2 && x 14 6)
  have b38026 := hb (x 13 3 && x 13 7)
  have b38027 := hb (x 12 4 && x 12 8)
  have b38028 := hb (x 11 5 && x 11 9)
  have b38029 := hb (x 10 6 && x 10 10)
  have b38030 := hb (x 9 7 && x 9 11)
  have b38031 := hb (x 8 8 && x 8 12)
  have b38032 := hb (x 7 9 && x 7 13)
  linarith only [r38018, e38019, e38020, b38021, b38022, b38023, b38024, b38025, b38026, b38027, b38028, b38029, b38030, b38031, b38032, d37896, d37912, d36983, d37015, d37051, d37075, d37998, d38014, d36314, d36342, d36346, d36370]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100001 (x : ℤ → Fin 16 → Bool)
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
    (h34091 : x (-1) 7 = false)
    (h34232 : x 1 7 = false)
    (h34234 : x 2 5 = false)
    (h34240 : x 2 6 = true)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125 g126 g127 g128 g129 g130 g131 g132 g133 g134 g135 h34091 h34232 h34234 h34240
