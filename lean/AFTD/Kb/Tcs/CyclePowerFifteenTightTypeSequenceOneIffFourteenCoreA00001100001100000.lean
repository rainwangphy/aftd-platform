import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100000

Topic: combinatorics   Node: 7a3a9bba4cda

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 140 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100000_aux (x : ℤ → Fin 16 → Bool)
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
    (h34240 : x 2 6 = false)
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
  have f34241 : (x 2 6).toNat = 0 := by rw [h34240]; rfl
  cases h34242 : x 2 7
  · have f34243 : (x 2 7).toNat = 0 := by rw [h34242]; rfl
    cases h34244 : x (-2) 8
    · have f34245 : (x (-2) 8).toNat = 0 := by rw [h34244]; rfl
      have d34246 : (x (-2) 8 && x (-2) 14).toNat = 0 := by
        have r34247 := hand1 (x (-2) 8) (x (-2) 14)
        have b34248 := hb (x (-2) 8)
        have b34249 := hb (x (-2) 8 && x (-2) 14)
        clear * - r34247 b34248 b34249 f34245
        omega
      have d34250 : (x (-2) 8 && x (-2) 12).toNat = 0 := by
        have r34251 := hand1 (x (-2) 8) (x (-2) 12)
        have b34252 := hb (x (-2) 8)
        have b34253 := hb (x (-2) 8 && x (-2) 12)
        clear * - r34251 b34252 b34253 f34245
        omega
      cases h34254 : x (-2) 12
      · have f34255 : (x (-2) 12).toNat = 0 := by rw [h34254]; rfl
        cases h34256 : x (-2) 14
        · have f34257 : (x (-2) 14).toNat = 0 := by rw [h34256]; rfl
          have d34258 : (x (-3) 1).toNat = 1 := by
            have r34259 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b34260 := hb (x (-3) 1)
            have b34261 := hb (x (-2) 14)
            clear * - r34259 b34260 b34261 f34257
            omega
          have r34262 : (x (-3) 1).toNat + (x (-4) 2).toNat + (x (-5) 3).toNat + (x (-6) 4).toNat + (x (-7) 5).toNat + (x (-8) 6).toNat + (x (-9) 7).toNat + (x (-10) 8).toNat + (x (-11) 9).toNat + (x (-12) 10).toNat + (x (-13) 11).toNat + (x (-14) 12).toNat + (x (-15) 13).toNat + (x (-16) 14).toNat = 3 := by have q := hcount (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34263 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34264 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34265 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34266 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
          have e34267 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
          have e34268 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
          have e34269 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
          have e34270 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
          have e34271 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
          have r34272 : 1 ≤ (x (-2) 5).toNat + (x (-3) 1 && x (-3) 6).toNat + (x (-4) 2 && x (-4) 7).toNat + (x (-5) 3 && x (-5) 8).toNat + (x (-6) 4 && x (-6) 9).toNat + (x (-7) 5 && x (-7) 10).toNat + (x (-8) 6 && x (-8) 11).toNat + (x (-9) 7 && x (-9) 12).toNat + (x (-10) 8 && x (-10) 13).toNat + (x (-11) 9 && x (-11) 14).toNat + (x (-12) 10).toNat := by have q := hcov5 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34273 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34274 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34275 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34276 : 1 ≤ (x (-10) 11).toNat + (x (-11) 1 && x (-11) 12).toNat + (x (-12) 2 && x (-12) 13).toNat + (x (-13) 3 && x (-13) 14).toNat + (x (-14) 4).toNat := by have q := hcov11 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34277 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34278 : (x (-14) 4).toNat ≤ (x (-14) 12).toNat := himp _ _ (hp4 (-14))
          have r34279 := hand2 (x (-5) 3) (x (-5) 8)
          have r34280 := hand2 (x (-6) 4) (x (-6) 9)
          have r34281 := hand2 (x (-7) 5) (x (-7) 10)
          have r34282 := hand1 (x (-8) 6) (x (-8) 11)
          have r34283 := hand1 (x (-9) 7) (x (-9) 12)
          have r34284 := hand1 (x (-11) 9) (x (-11) 14)
          have r34285 := hand1 (x (-7) 8) (x (-7) 13)
          have r34286 := hand1 (x (-8) 9) (x (-8) 14)
          have r34287 := hand1 (x (-8) 8) (x (-8) 14)
          have r34288 := hand1 (x (-4) 2) (x (-4) 12)
          have r34289 := hand1 (x (-5) 3) (x (-5) 13)
          have r34290 := hand1 (x (-6) 4) (x (-6) 14)
          have r34291 := hand2 (x (-11) 1) (x (-11) 12)
          have r34292 := hand2 (x (-12) 2) (x (-12) 13)
          have r34293 := hand2 (x (-13) 3) (x (-13) 14)
          have r34294 := hand2 (x (-9) 1) (x (-9) 12)
          have r34295 := hand2 (x (-11) 3) (x (-11) 14)
          linarith only [r34262, r34263, r34264, r34265, e34266, e34267, e34268, e34269, e34270, e34271, r34272, r34273, r34274, r34275, r34276, r34277, r34278, r34279, r34280, r34281, r34282, r34283, r34284, r34285, r34286, r34287, r34288, r34289, r34290, r34291, r34292, r34293, r34294, r34295, d34220, g0, g1, g2, g3, d34258, g5, g6, g9, g10, g12, g15, g16, g23, g24, g26, g33, g35, g42, g68, g69, d34228, g70, d34105, g71, g72, g73, g74, g75, d34097, g94, g95, g96, g97, g98, g99, g131, d34224]
        · have f34386 : (x (-2) 14).toNat = 1 := by rw [h34256]; rfl
          have d34387 : (x (-3) 1).toNat = 0 := by
            have r34388 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b34389 := hb (x (-3) 1)
            have b34390 := hb (x (-2) 14)
            clear * - r34388 b34389 b34390 f34386
            omega
          have d34391 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
            have r34392 := hand1 (x (-3) 1) (x (-3) 14)
            have b34393 := hb (x (-3) 1)
            have b34394 := hb (x (-3) 1 && x (-3) 14)
            clear * - r34392 b34393 b34394 d34387
            omega
          have d34395 : (x (-3) 13).toNat = 0 := by
            have r34396 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
            have b34397 := hb (x (-3) 1)
            have b34398 := hb (x (-3) 13)
            clear * - r34396 b34397 b34398 d34387
            omega
          have d34399 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
            have r34400 := hand2 (x (-3) 9) (x (-3) 13)
            have b34401 := hb (x (-3) 13)
            have b34402 := hb (x (-3) 9 && x (-3) 13)
            clear * - r34400 b34401 b34402 d34395
            omega
          have d34403 : (x (-3) 9).toNat = 0 := by
            have r34404 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
            have b34405 := hb (x (-3) 1)
            have b34406 := hb (x (-3) 9)
            clear * - r34404 b34405 b34406 d34387
            omega
          have d34407 : (x (-4) 2).toNat = 1 := by
            have r34408 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b34409 := hb (x (-4) 2)
            have b34410 := hb (x (-2) 13)
            have b34411 := hb (x (-3) 1 && x (-3) 14)
            clear * - r34408 b34409 b34410 b34411 g14 d34391
            omega
          have d34412 : (x (-4) 14).toNat = 1 := by
            have r34413 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b34414 := hb (x (-4) 2)
            have b34415 := hb (x (-4) 14)
            clear * - r34413 b34414 b34415 d34407
            omega
          have d34416 : (x (-5) 3).toNat = 0 := by
            have r34417 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e34418 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e34419 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b34420 := hb (x (-5) 3)
            have b34421 := hb (x (-4) 2)
            have b34422 := hb (x (-3) 13)
            have b34423 := hb (x (-2) 12)
            clear * - r34417 e34418 e34419 b34420 b34421 b34422 b34423 f34255 d34395 d34407
            omega
          have d34424 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
            have r34425 := hand1 (x (-5) 3) (x (-5) 12)
            have b34426 := hb (x (-5) 3)
            have b34427 := hb (x (-5) 3 && x (-5) 12)
            clear * - r34425 b34426 b34427 d34416
            omega
          have d34428 : (x (-5) 11).toNat = 0 := by
            have r34429 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
            have b34430 := hb (x (-5) 3)
            have b34431 := hb (x (-5) 11)
            clear * - r34429 b34430 b34431 d34416
            omega
          have r34432 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34433 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34434 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34435 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34436 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
          have e34437 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
          have e34438 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
          have e34439 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
          have e34440 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
          have e34441 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
          have r34442 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34443 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
          have e34444 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
          have e34445 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
          have e34446 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
          have e34447 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
          have e34448 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
          have r34449 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34450 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e34451 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have r34452 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34453 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e34454 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have r34455 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34456 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e34457 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have r34458 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34459 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34460 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
          have e34461 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
          have r34462 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34463 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34464 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34465 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34466 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r34467 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have r34468 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
          have r34469 := hand2 (x 4 2) (x 4 6)
          have r34470 := hand2 (x 3 3) (x 3 7)
          have r34471 := hand2 (x 5 1) (x 5 7)
          have r34472 := hand1 (x (-6) 4) (x (-6) 13)
          have r34473 := hand1 (x (-7) 5) (x (-7) 14)
          have r34474 := hand1 (x 9 1) (x 9 11)
          have r34475 := hand1 (x 8 2) (x 8 12)
          have r34476 := hand1 (x 7 3) (x 7 13)
          have r34477 := hand2 (x 6 4) (x 6 14)
          have r34478 := hand1 (x 9 1) (x 9 12)
          have r34479 := hand1 (x 8 2) (x 8 13)
          have r34480 := hand1 (x 7 3) (x 7 14)
          have r34481 := hand1 (x 11 1) (x 11 14)
          have b34486 := hb (x (-8) 14)
          linarith only [r34432, r34433, r34434, r34435, e34436, e34437, e34438, e34439, e34440, e34441, r34442, e34443, e34444, e34445, e34446, e34447, e34448, r34449, e34450, e34451, r34452, e34453, e34454, r34455, e34456, e34457, r34458, r34459, e34460, e34461, r34462, r34463, r34464, r34465, r34466, r34467, r34468, r34469, r34470, r34471, r34472, r34473, r34474, r34475, r34476, r34477, r34478, r34479, r34480, r34481, b34486, d34428, d34412, d34403, d34395, f34245, g11, f34255, f34386, f34092, g21, g22, g26, g30, g32, g35, g38, g40, g43, g44, g45, g51, g53, g61, g62, g63, d34109, d34250, d34399, g100, g101, g102, g103, g104, d34093, d34246, g120, g121, d34424]
      · have f34572 : (x (-2) 12).toNat = 1 := by rw [h34254]; rfl
        have d34573 : (x (-3) 13).toNat = 0 := by
          have r34574 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34575 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e34576 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b34577 := hb (x (-5) 3)
          have b34578 := hb (x (-4) 2)
          have b34579 := hb (x (-3) 13)
          have b34580 := hb (x (-2) 12)
          clear * - r34574 e34575 e34576 b34577 b34578 b34579 b34580 f34572
          omega
        have d34581 : (x (-4) 2).toNat = 0 := by
          have r34582 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34583 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e34584 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b34585 := hb (x (-5) 3)
          have b34586 := hb (x (-4) 2)
          have b34587 := hb (x (-3) 13)
          have b34588 := hb (x (-2) 12)
          clear * - r34582 e34583 e34584 b34585 b34586 b34587 b34588 f34572 d34573
          omega
        have d34589 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
          have r34590 := hand1 (x (-4) 2) (x (-4) 13)
          have b34591 := hb (x (-4) 2)
          have b34592 := hb (x (-4) 2 && x (-4) 13)
          clear * - r34590 b34591 b34592 d34581
          omega
        have d34593 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
          have r34594 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34595 := hb (x (-4) 2)
          have b34596 := hb (x (-2) 13)
          have b34597 := hb (x (-3) 1 && x (-3) 14)
          clear * - r34594 b34595 b34596 b34597 g14 d34581
          omega
        have d34598 : (x (-3) 14).toNat = 1 := by
          have r34599 := hand2 (x (-3) 1) (x (-3) 14)
          have b34600 := hb (x (-3) 14)
          have b34601 := hb (x (-3) 1 && x (-3) 14)
          clear * - r34599 b34600 b34601 d34593
          omega
        have d34602 : (x (-4) 1).toNat = 0 := by
          have r34603 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34604 := hb (x (-4) 1)
          have b34605 := hb (x (-3) 14)
          clear * - r34603 b34604 b34605 d34598
          omega
        have d34606 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
          have r34607 := hand1 (x (-4) 1) (x (-4) 14)
          have b34608 := hb (x (-4) 1)
          have b34609 := hb (x (-4) 1 && x (-4) 14)
          clear * - r34607 b34608 b34609 d34602
          omega
        have d34610 : (x (-5) 2).toNat = 1 := by
          have r34611 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34612 := hb (x (-5) 2)
          have b34613 := hb (x (-3) 13)
          have b34614 := hb (x (-4) 1 && x (-4) 14)
          clear * - r34611 b34612 b34613 b34614 d34573 d34606
          omega
        have d34615 : (x (-5) 14).toNat = 1 := by
          have r34616 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
          have b34617 := hb (x (-5) 2)
          have b34618 := hb (x (-5) 14)
          clear * - r34616 b34617 b34618 d34610
          omega
        have d34619 : (x (-6) 1).toNat = 0 := by
          have r34620 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34621 := hb (x (-6) 1)
          have b34622 := hb (x (-5) 14)
          clear * - r34620 b34621 b34622 d34615
          omega
        have d34623 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
          have r34624 := hand1 (x (-6) 1) (x (-6) 12)
          have b34625 := hb (x (-6) 1)
          have b34626 := hb (x (-6) 1 && x (-6) 12)
          clear * - r34624 b34625 b34626 d34619
          omega
        have d34627 : (x (-6) 13).toNat = 0 := by
          have r34628 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
          have b34629 := hb (x (-6) 1)
          have b34630 := hb (x (-6) 13)
          clear * - r34628 b34629 b34630 d34619
          omega
        have d34631 : (x (-4) 13).toNat = 0 := by
          have r34632 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b34633 := hb (x (-4) 1)
          have b34634 := hb (x (-4) 13)
          clear * - r34632 b34633 b34634 d34602
          omega
        have d34635 : (x (-5) 3).toNat = 0 := by
          have r34636 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34637 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e34638 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b34639 := hb (x (-5) 3)
          have b34640 := hb (x (-4) 2)
          have b34641 := hb (x (-3) 13)
          have b34642 := hb (x (-2) 12)
          clear * - r34636 e34637 e34638 b34639 b34640 b34641 b34642 f34572 d34573 d34581
          omega
        have d34643 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
          have r34644 := hand1 (x (-5) 3) (x (-5) 14)
          have b34645 := hb (x (-5) 3)
          have b34646 := hb (x (-5) 3 && x (-5) 14)
          clear * - r34644 b34645 b34646 d34635
          omega
        have d34647 : (x (-5) 11).toNat = 0 := by
          have r34648 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
          have b34649 := hb (x (-5) 3)
          have b34650 := hb (x (-5) 11)
          clear * - r34648 b34649 b34650 d34635
          omega
        have d34651 : (x (-3) 12).toNat = 0 := by
          have r34652 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34653 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e34654 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b34655 := hb (x (-6) 3)
          have b34656 := hb (x (-5) 2)
          have b34657 := hb (x (-4) 13)
          have b34658 := hb (x (-3) 12)
          clear * - r34652 e34653 e34654 b34655 b34656 b34657 b34658 d34631 d34610
          omega
        have d34659 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
          have r34660 := hand2 (x (-3) 1) (x (-3) 12)
          have b34661 := hb (x (-3) 12)
          have b34662 := hb (x (-3) 1 && x (-3) 12)
          clear * - r34660 b34661 b34662 d34651
          omega
        have d34663 : (x (-6) 3).toNat = 0 := by
          have r34664 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34665 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e34666 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b34667 := hb (x (-6) 3)
          have b34668 := hb (x (-5) 2)
          have b34669 := hb (x (-4) 13)
          have b34670 := hb (x (-3) 12)
          clear * - r34664 e34665 e34666 b34667 b34668 b34669 b34670 d34651 d34631 d34610
          omega
        have d34671 : (x (-6) 11).toNat = 0 := by
          have r34672 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
          have b34673 := hb (x (-6) 3)
          have b34674 := hb (x (-6) 11)
          clear * - r34672 b34673 b34674 d34663
          omega
        have d34675 : (x (-6) 4).toNat = 1 := by
          have r34676 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34677 := hb (x (-6) 4)
          have b34678 := hb (x (-2) 11)
          have b34679 := hb (x (-3) 1 && x (-3) 12)
          have b34680 := hb (x (-4) 2 && x (-4) 13)
          have b34681 := hb (x (-5) 3 && x (-5) 14)
          clear * - r34676 b34677 b34678 b34679 b34680 b34681 g13 d34659 d34589 d34643
          omega
        have d34682 : (x (-6) 12).toNat = 1 := by
          have r34683 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
          have b34684 := hb (x (-6) 4)
          have b34685 := hb (x (-6) 12)
          clear * - r34683 b34684 b34685 d34675
          omega
        have d34686 : (x (-7) 13).toNat = 0 := by
          have r34687 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34688 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e34689 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b34690 := hb (x (-9) 3)
          have b34691 := hb (x (-8) 2)
          have b34692 := hb (x (-7) 13)
          have b34693 := hb (x (-6) 12)
          clear * - r34687 e34688 e34689 b34690 b34691 b34692 b34693 d34682
          omega
        have d34694 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
          have r34695 := hand2 (x (-7) 2) (x (-7) 13)
          have b34696 := hb (x (-7) 13)
          have b34697 := hb (x (-7) 2 && x (-7) 13)
          clear * - r34695 b34696 b34697 d34686
          omega
        have d34698 : (x (-8) 2).toNat = 0 := by
          have r34699 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34700 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e34701 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b34702 := hb (x (-9) 3)
          have b34703 := hb (x (-8) 2)
          have b34704 := hb (x (-7) 13)
          have b34705 := hb (x (-6) 12)
          clear * - r34699 e34700 e34701 b34702 b34703 b34704 b34705 d34682 d34686
          omega
        have d34706 : (x (-8) 2 && x (-8) 13).toNat = 0 := by
          have r34707 := hand1 (x (-8) 2) (x (-8) 13)
          have b34708 := hb (x (-8) 2)
          have b34709 := hb (x (-8) 2 && x (-8) 13)
          clear * - r34707 b34708 b34709 d34698
          omega
        have d34710 : (x (-7) 1 && x (-7) 14).toNat = 1 := by
          have r34711 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34712 := hb (x (-8) 2)
          have b34713 := hb (x (-6) 13)
          have b34714 := hb (x (-7) 1 && x (-7) 14)
          clear * - r34711 b34712 b34713 b34714 d34627 d34698
          omega
        have d34715 : (x (-7) 14).toNat = 1 := by
          have r34716 := hand2 (x (-7) 1) (x (-7) 14)
          have b34717 := hb (x (-7) 14)
          have b34718 := hb (x (-7) 1 && x (-7) 14)
          clear * - r34716 b34717 b34718 d34710
          omega
        have d34719 : (x (-8) 1).toNat = 0 := by
          have r34720 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34721 := hb (x (-8) 1)
          have b34722 := hb (x (-7) 14)
          clear * - r34720 b34721 b34722 d34715
          omega
        have d34723 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
          have r34724 := hand1 (x (-8) 1) (x (-8) 14)
          have b34725 := hb (x (-8) 1)
          have b34726 := hb (x (-8) 1 && x (-8) 14)
          clear * - r34724 b34725 b34726 d34719
          omega
        have d34727 : (x (-9) 2).toNat = 1 := by
          have r34728 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34729 := hb (x (-9) 2)
          have b34730 := hb (x (-7) 13)
          have b34731 := hb (x (-8) 1 && x (-8) 14)
          clear * - r34728 b34729 b34730 b34731 d34686 d34723
          omega
        have d34732 : (x (-7) 12).toNat = 0 := by
          have r34733 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34734 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
          have e34735 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
          have b34736 := hb (x (-10) 3)
          have b34737 := hb (x (-9) 2)
          have b34738 := hb (x (-8) 13)
          have b34739 := hb (x (-7) 12)
          clear * - r34733 e34734 e34735 b34736 b34737 b34738 b34739 d34727
          omega
        have d34740 : (x (-7) 1 && x (-7) 12).toNat = 0 := by
          have r34741 := hand2 (x (-7) 1) (x (-7) 12)
          have b34742 := hb (x (-7) 12)
          have b34743 := hb (x (-7) 1 && x (-7) 12)
          clear * - r34741 b34742 b34743 d34732
          omega
        have d34744 : (x (-8) 13).toNat = 0 := by
          have r34745 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34746 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
          have e34747 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
          have b34748 := hb (x (-10) 3)
          have b34749 := hb (x (-9) 2)
          have b34750 := hb (x (-8) 13)
          have b34751 := hb (x (-7) 12)
          clear * - r34745 e34746 e34747 b34748 b34749 b34750 b34751 d34732 d34727
          omega
        have d34752 : (x (-9) 3).toNat = 0 := by
          have r34753 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34754 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e34755 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have b34756 := hb (x (-9) 3)
          have b34757 := hb (x (-8) 2)
          have b34758 := hb (x (-7) 13)
          have b34759 := hb (x (-6) 12)
          clear * - r34753 e34754 e34755 b34756 b34757 b34758 b34759 d34682 d34686 d34698
          omega
        have d34760 : (x (-9) 3 && x (-9) 14).toNat = 0 := by
          have r34761 := hand1 (x (-9) 3) (x (-9) 14)
          have b34762 := hb (x (-9) 3)
          have b34763 := hb (x (-9) 3 && x (-9) 14)
          clear * - r34761 b34762 b34763 d34752
          omega
        have d34764 : (x (-9) 11).toNat = 0 := by
          have r34765 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
          have b34766 := hb (x (-9) 3)
          have b34767 := hb (x (-9) 11)
          clear * - r34765 b34766 b34767 d34752
          omega
        have d34768 : (x (-10) 4).toNat = 1 := by
          have r34769 : 1 ≤ (x (-6) 11).toNat + (x (-7) 1 && x (-7) 12).toNat + (x (-8) 2 && x (-8) 13).toNat + (x (-9) 3 && x (-9) 14).toNat + (x (-10) 4).toNat := by have q := hcov11 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34770 := hb (x (-10) 4)
          have b34771 := hb (x (-6) 11)
          have b34772 := hb (x (-7) 1 && x (-7) 12)
          have b34773 := hb (x (-8) 2 && x (-8) 13)
          have b34774 := hb (x (-9) 3 && x (-9) 14)
          clear * - r34769 b34770 b34771 b34772 b34773 b34774 d34671 d34740 d34706 d34760
          omega
        have d34775 : (x (-10) 12).toNat = 1 := by
          have r34776 : (x (-10) 4).toNat ≤ (x (-10) 12).toNat := himp _ _ (hp4 (-10))
          have b34777 := hb (x (-10) 4)
          have b34778 := hb (x (-10) 12)
          clear * - r34776 b34777 b34778 d34768
          omega
        have d34779 : (x (-11) 13).toNat = 0 := by
          have r34780 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34781 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
          have e34782 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
          have b34783 := hb (x (-13) 3)
          have b34784 := hb (x (-12) 2)
          have b34785 := hb (x (-11) 13)
          have b34786 := hb (x (-10) 12)
          clear * - r34780 e34781 e34782 b34783 b34784 b34785 b34786 d34775
          omega
        have d34787 : (x (-11) 2 && x (-11) 13).toNat = 0 := by
          have r34788 := hand2 (x (-11) 2) (x (-11) 13)
          have b34789 := hb (x (-11) 13)
          have b34790 := hb (x (-11) 2 && x (-11) 13)
          clear * - r34788 b34789 b34790 d34779
          omega
        have d34791 : (x (-12) 2).toNat = 0 := by
          have r34792 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34793 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
          have e34794 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
          have b34795 := hb (x (-13) 3)
          have b34796 := hb (x (-12) 2)
          have b34797 := hb (x (-11) 13)
          have b34798 := hb (x (-10) 12)
          clear * - r34792 e34793 e34794 b34795 b34796 b34797 b34798 d34775 d34779
          omega
        have d34799 : (x (-11) 1 && x (-11) 14).toNat = 1 := by
          have r34800 : 1 ≤ (x (-10) 13).toNat + (x (-11) 1 && x (-11) 14).toNat + (x (-12) 2).toNat := by have q := hcov13 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34801 := hb (x (-12) 2)
          have b34802 := hb (x (-10) 13)
          have b34803 := hb (x (-11) 1 && x (-11) 14)
          clear * - r34800 b34801 b34802 b34803 d34220 d34791
          omega
        have d34804 : (x (-11) 1).toNat = 1 := by
          have r34805 := hand1 (x (-11) 1) (x (-11) 14)
          have b34806 := hb (x (-11) 1)
          have b34807 := hb (x (-11) 1 && x (-11) 14)
          clear * - r34805 b34806 b34807 d34799
          omega
        have d34808 : (x (-10) 14).toNat = 0 := by
          have r34809 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34810 := hb (x (-11) 1)
          have b34811 := hb (x (-10) 14)
          clear * - r34809 b34810 b34811 d34804
          omega
        have d34812 : (x (-10) 2).toNat = 0 := by
          have r34813 : (x (-10) 2).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp2 (-10))
          have b34814 := hb (x (-10) 2)
          have b34815 := hb (x (-10) 14)
          clear * - r34813 b34814 b34815 d34808
          omega
        have d34816 : (x (-9) 1 && x (-9) 14).toNat = 1 := by
          have r34817 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34818 := hb (x (-10) 2)
          have b34819 := hb (x (-8) 13)
          have b34820 := hb (x (-9) 1 && x (-9) 14)
          clear * - r34817 b34818 b34819 b34820 d34744 d34812
          omega
        have d34821 : (x (-9) 1).toNat = 1 := by
          have r34822 := hand1 (x (-9) 1) (x (-9) 14)
          have b34823 := hb (x (-9) 1)
          have b34824 := hb (x (-9) 1 && x (-9) 14)
          clear * - r34822 b34823 b34824 d34816
          omega
        have d34825 : (x (-8) 14).toNat = 0 := by
          have r34826 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34827 := hb (x (-9) 1)
          have b34828 := hb (x (-8) 14)
          clear * - r34826 b34827 b34828 d34821
          omega
        have d34829 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
          have r34830 := hand2 (x (-8) 3) (x (-8) 14)
          have b34831 := hb (x (-8) 14)
          have b34832 := hb (x (-8) 3 && x (-8) 14)
          clear * - r34830 b34831 b34832 d34825
          omega
        have d34833 : (x (-9) 4).toNat = 1 := by
          have r34834 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b34835 := hb (x (-9) 4)
          have b34836 := hb (x (-5) 11)
          have b34837 := hb (x (-6) 1 && x (-6) 12)
          have b34838 := hb (x (-7) 2 && x (-7) 13)
          have b34839 := hb (x (-8) 3 && x (-8) 14)
          clear * - r34834 b34835 b34836 b34837 b34838 b34839 d34647 d34623 d34694 d34829
          omega
        have d34840 : (x (-9) 12).toNat = 1 := by
          have r34841 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
          have b34842 := hb (x (-9) 4)
          have b34843 := hb (x (-9) 12)
          clear * - r34841 b34842 b34843 d34833
          omega
        have d34844 : (x (-11) 2).toNat = 0 := by
          have r34845 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34846 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
          have e34847 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
          have b34848 := hb (x (-12) 3)
          have b34849 := hb (x (-11) 2)
          have b34850 := hb (x (-10) 13)
          have b34851 := hb (x (-9) 12)
          clear * - r34845 e34846 e34847 b34848 b34849 b34850 b34851 d34840 d34220
          omega
        have d34852 : (x (-12) 3).toNat = 0 := by
          have r34853 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e34854 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
          have e34855 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
          have b34856 := hb (x (-12) 3)
          have b34857 := hb (x (-11) 2)
          have b34858 := hb (x (-10) 13)
          have b34859 := hb (x (-9) 12)
          clear * - r34853 e34854 e34855 b34856 b34857 b34858 b34859 d34840 d34220 d34844
          omega
        have d34860 : (x (-12) 3 && x (-12) 14).toNat = 0 := by
          have r34861 := hand1 (x (-12) 3) (x (-12) 14)
          have b34862 := hb (x (-12) 3)
          have b34863 := hb (x (-12) 3 && x (-12) 14)
          clear * - r34861 b34862 b34863 d34852
          omega
        have r34864 : 1 ≤ (x (-9) 11).toNat + (x (-10) 1 && x (-10) 12).toNat + (x (-11) 2 && x (-11) 13).toNat + (x (-12) 3 && x (-12) 14).toNat + (x (-13) 4).toNat := by have q := hcov11 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34865 := hb (x (-13) 4)
        have b34866 := hb (x (-9) 11)
        have b34867 := hb (x (-10) 1 && x (-10) 12)
        have b34868 := hb (x (-11) 2 && x (-11) 13)
        have b34869 := hb (x (-12) 3 && x (-12) 14)
        linarith only [r34864, b34865, b34866, b34867, b34868, b34869, d34764, d34216, d34787, d34860, d34176]
    · have f34870 : (x (-2) 8).toNat = 1 := by rw [h34244]; rfl
      have d34871 : (x (-3) 9).toNat = 0 := by
        have r34872 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34873 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e34874 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e34875 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e34876 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e34877 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e34878 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b34879 := hb (x (-9) 7)
        have b34880 := hb (x (-8) 6)
        have b34881 := hb (x (-7) 5)
        have b34882 := hb (x (-6) 4)
        have b34883 := hb (x (-5) 11)
        have b34884 := hb (x (-4) 10)
        have b34885 := hb (x (-3) 9)
        have b34886 := hb (x (-2) 8)
        clear * - r34872 e34873 e34874 e34875 e34876 e34877 e34878 b34879 b34880 b34881 b34882 b34883 b34884 b34885 b34886 f34870
        omega
      have d34887 : (x (-3) 9 && x (-3) 14).toNat = 0 := by
        have r34888 := hand1 (x (-3) 9) (x (-3) 14)
        have b34889 := hb (x (-3) 9)
        have b34890 := hb (x (-3) 9 && x (-3) 14)
        clear * - r34888 b34889 b34890 d34871
        omega
      have d34891 : (x (-4) 10).toNat = 0 := by
        have r34892 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34893 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e34894 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e34895 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e34896 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e34897 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e34898 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b34899 := hb (x (-9) 7)
        have b34900 := hb (x (-8) 6)
        have b34901 := hb (x (-7) 5)
        have b34902 := hb (x (-6) 4)
        have b34903 := hb (x (-5) 11)
        have b34904 := hb (x (-4) 10)
        have b34905 := hb (x (-3) 9)
        have b34906 := hb (x (-2) 8)
        clear * - r34892 e34893 e34894 e34895 e34896 e34897 e34898 b34899 b34900 b34901 b34902 b34903 b34904 b34905 b34906 f34870 d34871
        omega
      have d34907 : (x (-4) 1 && x (-4) 10).toNat = 0 := by
        have r34908 := hand2 (x (-4) 1) (x (-4) 10)
        have b34909 := hb (x (-4) 10)
        have b34910 := hb (x (-4) 1 && x (-4) 10)
        clear * - r34908 b34909 b34910 d34891
        omega
      have d34911 : (x (-5) 11).toNat = 0 := by
        have r34912 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34913 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e34914 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e34915 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e34916 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e34917 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e34918 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b34919 := hb (x (-9) 7)
        have b34920 := hb (x (-8) 6)
        have b34921 := hb (x (-7) 5)
        have b34922 := hb (x (-6) 4)
        have b34923 := hb (x (-5) 11)
        have b34924 := hb (x (-4) 10)
        have b34925 := hb (x (-3) 9)
        have b34926 := hb (x (-2) 8)
        clear * - r34912 e34913 e34914 e34915 e34916 e34917 e34918 b34919 b34920 b34921 b34922 b34923 b34924 b34925 b34926 f34870 d34871 d34891
        omega
      have d34927 : (x (-5) 2 && x (-5) 11).toNat = 0 := by
        have r34928 := hand2 (x (-5) 2) (x (-5) 11)
        have b34929 := hb (x (-5) 11)
        have b34930 := hb (x (-5) 2 && x (-5) 11)
        clear * - r34928 b34929 b34930 d34911
        omega
      have d34931 : (x (-5) 11 && x (-5) 12).toNat = 0 := by
        have r34932 := hand1 (x (-5) 11) (x (-5) 12)
        have b34933 := hb (x (-5) 11)
        have b34934 := hb (x (-5) 11 && x (-5) 12)
        clear * - r34932 b34933 b34934 d34911
        omega
      have d34935 : (x (-6) 4).toNat = 0 := by
        have r34936 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34937 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e34938 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e34939 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e34940 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e34941 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e34942 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b34943 := hb (x (-9) 7)
        have b34944 := hb (x (-8) 6)
        have b34945 := hb (x (-7) 5)
        have b34946 := hb (x (-6) 4)
        have b34947 := hb (x (-5) 11)
        have b34948 := hb (x (-4) 10)
        have b34949 := hb (x (-3) 9)
        have b34950 := hb (x (-2) 8)
        clear * - r34936 e34937 e34938 e34939 e34940 e34941 e34942 b34943 b34944 b34945 b34946 b34947 b34948 b34949 b34950 f34870 d34871 d34891 d34911
        omega
      have d34951 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
        have r34952 := hand1 (x (-6) 4) (x (-6) 14)
        have b34953 := hb (x (-6) 4)
        have b34954 := hb (x (-6) 4 && x (-6) 14)
        clear * - r34952 b34953 b34954 d34935
        omega
      have d34955 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
        have r34956 := hand1 (x (-6) 4) (x (-6) 13)
        have b34957 := hb (x (-6) 4)
        have b34958 := hb (x (-6) 4 && x (-6) 13)
        clear * - r34956 b34957 b34958 d34935
        omega
      have d34959 : (x (-7) 5).toNat = 0 := by
        have r34960 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34961 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e34962 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e34963 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e34964 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e34965 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e34966 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b34967 := hb (x (-9) 7)
        have b34968 := hb (x (-8) 6)
        have b34969 := hb (x (-7) 5)
        have b34970 := hb (x (-6) 4)
        have b34971 := hb (x (-5) 11)
        have b34972 := hb (x (-4) 10)
        have b34973 := hb (x (-3) 9)
        have b34974 := hb (x (-2) 8)
        clear * - r34960 e34961 e34962 e34963 e34964 e34965 e34966 b34967 b34968 b34969 b34970 b34971 b34972 b34973 b34974 f34870 d34871 d34891 d34911 d34935
        omega
      have d34975 : (x (-7) 5 && x (-7) 14).toNat = 0 := by
        have r34976 := hand1 (x (-7) 5) (x (-7) 14)
        have b34977 := hb (x (-7) 5)
        have b34978 := hb (x (-7) 5 && x (-7) 14)
        clear * - r34976 b34977 b34978 d34959
        omega
      have d34979 : (x (-8) 6).toNat = 0 := by
        have r34980 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e34981 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e34982 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e34983 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e34984 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e34985 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e34986 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have b34987 := hb (x (-9) 7)
        have b34988 := hb (x (-8) 6)
        have b34989 := hb (x (-7) 5)
        have b34990 := hb (x (-6) 4)
        have b34991 := hb (x (-5) 11)
        have b34992 := hb (x (-4) 10)
        have b34993 := hb (x (-3) 9)
        have b34994 := hb (x (-2) 8)
        clear * - r34980 e34981 e34982 e34983 e34984 e34985 e34986 b34987 b34988 b34989 b34990 b34991 b34992 b34993 b34994 f34870 d34871 d34891 d34911 d34935 d34959
        omega
      have d34995 : (x (-5) 3 && x (-5) 12).toNat = 1 := by
        have r34996 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b34997 := hb (x (-8) 6)
        have b34998 := hb (x (-2) 9)
        have b34999 := hb (x (-3) 1 && x (-3) 10)
        have b35000 := hb (x (-4) 2 && x (-4) 11)
        have b35001 := hb (x (-5) 3 && x (-5) 12)
        have b35002 := hb (x (-6) 4 && x (-6) 13)
        have b35003 := hb (x (-7) 5 && x (-7) 14)
        clear * - r34996 b34997 b34998 b34999 b35000 b35001 b35002 b35003 g11 g120 g121 d34955 d34975 d34979
        omega
      have d35004 : (x (-5) 12).toNat = 1 := by
        have r35005 := hand2 (x (-5) 3) (x (-5) 12)
        have b35006 := hb (x (-5) 12)
        have b35007 := hb (x (-5) 3 && x (-5) 12)
        clear * - r35005 b35006 b35007 d34995
        omega
      have d35008 : (x (-6) 13).toNat = 0 := by
        have r35009 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35010 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e35011 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b35012 := hb (x (-8) 3)
        have b35013 := hb (x (-7) 2)
        have b35014 := hb (x (-6) 13)
        have b35015 := hb (x (-5) 12)
        clear * - r35009 e35010 e35011 b35012 b35013 b35014 b35015 d35004
        omega
      have d35016 : (x (-6) 12 && x (-6) 13).toNat = 0 := by
        have r35017 := hand2 (x (-6) 12) (x (-6) 13)
        have b35018 := hb (x (-6) 13)
        have b35019 := hb (x (-6) 12 && x (-6) 13)
        clear * - r35017 b35018 b35019 d35008
        omega
      have d35020 : (x (-7) 2).toNat = 0 := by
        have r35021 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35022 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e35023 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b35024 := hb (x (-8) 3)
        have b35025 := hb (x (-7) 2)
        have b35026 := hb (x (-6) 13)
        have b35027 := hb (x (-5) 12)
        clear * - r35021 e35022 e35023 b35024 b35025 b35026 b35027 d35004 d35008
        omega
      have d35028 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
        have r35029 := hand1 (x (-7) 2) (x (-7) 13)
        have b35030 := hb (x (-7) 2)
        have b35031 := hb (x (-7) 2 && x (-7) 13)
        clear * - r35029 b35030 b35031 d35020
        omega
      have d35032 : (x (-8) 3).toNat = 0 := by
        have r35033 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35034 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e35035 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b35036 := hb (x (-8) 3)
        have b35037 := hb (x (-7) 2)
        have b35038 := hb (x (-6) 13)
        have b35039 := hb (x (-5) 12)
        clear * - r35033 e35034 e35035 b35036 b35037 b35038 b35039 d35004 d35008 d35020
        omega
      have d35040 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
        have r35041 := hand1 (x (-8) 3) (x (-8) 14)
        have b35042 := hb (x (-8) 3)
        have b35043 := hb (x (-8) 3 && x (-8) 14)
        clear * - r35041 b35042 b35043 d35032
        omega
      have d35044 : (x (-5) 3).toNat = 1 := by
        have r35045 := hand1 (x (-5) 3) (x (-5) 12)
        have b35046 := hb (x (-5) 3)
        have b35047 := hb (x (-5) 3 && x (-5) 12)
        clear * - r35045 b35046 b35047 d34995
        omega
      have d35048 : (x (-2) 12).toNat = 0 := by
        have r35049 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35050 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e35051 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b35052 := hb (x (-5) 3)
        have b35053 := hb (x (-4) 2)
        have b35054 := hb (x (-3) 13)
        have b35055 := hb (x (-2) 12)
        clear * - r35049 e35050 e35051 b35052 b35053 b35054 b35055 d35044
        omega
      have d35056 : (x (-2) 7 && x (-2) 12).toNat = 0 := by
        have r35057 := hand2 (x (-2) 7) (x (-2) 12)
        have b35058 := hb (x (-2) 12)
        have b35059 := hb (x (-2) 7 && x (-2) 12)
        clear * - r35057 b35058 b35059 d35048
        omega
      have d35060 : (x (-3) 13).toNat = 0 := by
        have r35061 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35062 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e35063 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b35064 := hb (x (-5) 3)
        have b35065 := hb (x (-4) 2)
        have b35066 := hb (x (-3) 13)
        have b35067 := hb (x (-2) 12)
        clear * - r35061 e35062 e35063 b35064 b35065 b35066 b35067 d35048 d35044
        omega
      have d35068 : (x (-3) 8 && x (-3) 13).toNat = 0 := by
        have r35069 := hand2 (x (-3) 8) (x (-3) 13)
        have b35070 := hb (x (-3) 13)
        have b35071 := hb (x (-3) 8 && x (-3) 13)
        clear * - r35069 b35070 b35071 d35060
        omega
      have d35072 : (x (-4) 2).toNat = 0 := by
        have r35073 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35074 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e35075 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b35076 := hb (x (-5) 3)
        have b35077 := hb (x (-4) 2)
        have b35078 := hb (x (-3) 13)
        have b35079 := hb (x (-2) 12)
        clear * - r35073 e35074 e35075 b35076 b35077 b35078 b35079 d35048 d35060 d35044
        omega
      have d35080 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
        have r35081 := hand1 (x (-4) 2) (x (-4) 12)
        have b35082 := hb (x (-4) 2)
        have b35083 := hb (x (-4) 2 && x (-4) 12)
        clear * - r35081 b35082 b35083 d35072
        omega
      have d35084 : (x (-5) 3 && x (-5) 13).toNat = 1 := by
        have r35085 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35086 := hb (x (-7) 5)
        have b35087 := hb (x (-2) 10)
        have b35088 := hb (x (-3) 1 && x (-3) 11)
        have b35089 := hb (x (-4) 2 && x (-4) 12)
        have b35090 := hb (x (-5) 3 && x (-5) 13)
        have b35091 := hb (x (-6) 4 && x (-6) 14)
        clear * - r35085 b35086 b35087 b35088 b35089 b35090 b35091 g12 g131 d35080 d34951 d34959
        omega
      have d35092 : (x (-5) 13).toNat = 1 := by
        have r35093 := hand2 (x (-5) 3) (x (-5) 13)
        have b35094 := hb (x (-5) 13)
        have b35095 := hb (x (-5) 3 && x (-5) 13)
        clear * - r35093 b35094 b35095 d35084
        omega
      have d35096 : (x (-5) 1).toNat = 1 := by
        have r35097 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
        have b35098 := hb (x (-5) 1)
        have b35099 := hb (x (-5) 13)
        clear * - r35097 b35098 b35099 d35092
        omega
      have d35100 : (x (-4) 14).toNat = 0 := by
        have r35101 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35102 := hb (x (-5) 1)
        have b35103 := hb (x (-4) 14)
        clear * - r35101 b35102 b35103 d35096
        omega
      have d35104 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
        have r35105 := hand2 (x (-4) 1) (x (-4) 14)
        have b35106 := hb (x (-4) 14)
        have b35107 := hb (x (-4) 1 && x (-4) 14)
        clear * - r35105 b35106 b35107 d35100
        omega
      have d35108 : (x (-5) 2).toNat = 1 := by
        have r35109 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35110 := hb (x (-5) 2)
        have b35111 := hb (x (-3) 13)
        have b35112 := hb (x (-4) 1 && x (-4) 14)
        clear * - r35109 b35110 b35111 b35112 d35060 d35104
        omega
      have d35113 : (x (-5) 14).toNat = 1 := by
        have r35114 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
        have b35115 := hb (x (-5) 2)
        have b35116 := hb (x (-5) 14)
        clear * - r35114 b35115 b35116 d35108
        omega
      have d35117 : (x (-6) 1).toNat = 0 := by
        have r35118 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35119 := hb (x (-6) 1)
        have b35120 := hb (x (-5) 14)
        clear * - r35118 b35119 b35120 d35113
        omega
      have d35121 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
        have r35122 := hand1 (x (-6) 1) (x (-6) 12)
        have b35123 := hb (x (-6) 1)
        have b35124 := hb (x (-6) 1 && x (-6) 12)
        clear * - r35122 b35123 b35124 d35117
        omega
      have d35125 : (x (-9) 4).toNat = 1 := by
        have r35126 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35127 := hb (x (-9) 4)
        have b35128 := hb (x (-5) 11)
        have b35129 := hb (x (-6) 1 && x (-6) 12)
        have b35130 := hb (x (-7) 2 && x (-7) 13)
        have b35131 := hb (x (-8) 3 && x (-8) 14)
        clear * - r35126 b35127 b35128 b35129 b35130 b35131 d34911 d35121 d35028 d35040
        omega
      have d35132 : (x (-9) 12).toNat = 1 := by
        have r35133 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
        have b35134 := hb (x (-9) 4)
        have b35135 := hb (x (-9) 12)
        clear * - r35133 b35134 b35135 d35125
        omega
      have d35136 : (x (-11) 2).toNat = 0 := by
        have r35137 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35138 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
        have e35139 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
        have b35140 := hb (x (-12) 3)
        have b35141 := hb (x (-11) 2)
        have b35142 := hb (x (-10) 13)
        have b35143 := hb (x (-9) 12)
        clear * - r35137 e35138 e35139 b35140 b35141 b35142 b35143 d35132 d34220
        omega
      have d35144 : (x (-11) 2 && x (-11) 13).toNat = 0 := by
        have r35145 := hand1 (x (-11) 2) (x (-11) 13)
        have b35146 := hb (x (-11) 2)
        have b35147 := hb (x (-11) 2 && x (-11) 13)
        clear * - r35145 b35146 b35147 d35136
        omega
      have d35148 : (x (-9) 13).toNat = 1 := by
        have r35149 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35150 := hb (x (-11) 2)
        have b35151 := hb (x (-9) 13)
        have b35152 := hb (x (-10) 1 && x (-10) 14)
        clear * - r35149 b35150 b35151 b35152 d34212 d35136
        omega
      have d35153 : (x (-9) 1).toNat = 1 := by
        have r35154 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
        have b35155 := hb (x (-9) 1)
        have b35156 := hb (x (-9) 13)
        clear * - r35154 b35155 b35156 d35148
        omega
      have d35157 : (x (-8) 14).toNat = 0 := by
        have r35158 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35159 := hb (x (-9) 1)
        have b35160 := hb (x (-8) 14)
        clear * - r35158 b35159 b35160 d35153
        omega
      have d35161 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
        have r35162 := hand2 (x (-8) 1) (x (-8) 14)
        have b35163 := hb (x (-8) 14)
        have b35164 := hb (x (-8) 1 && x (-8) 14)
        clear * - r35162 b35163 b35164 d35157
        omega
      have d35165 : (x (-8) 5 && x (-8) 14).toNat = 0 := by
        have r35166 := hand2 (x (-8) 5) (x (-8) 14)
        have b35167 := hb (x (-8) 14)
        have b35168 := hb (x (-8) 5 && x (-8) 14)
        clear * - r35166 b35167 b35168 d35157
        omega
      have d35169 : (x (-8) 2).toNat = 0 := by
        have r35170 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
        have b35171 := hb (x (-8) 2)
        have b35172 := hb (x (-8) 14)
        clear * - r35170 b35171 b35172 d35157
        omega
      have d35173 : (x (-7) 1 && x (-7) 14).toNat = 1 := by
        have r35174 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35175 := hb (x (-8) 2)
        have b35176 := hb (x (-6) 13)
        have b35177 := hb (x (-7) 1 && x (-7) 14)
        clear * - r35174 b35175 b35176 b35177 d35008 d35169
        omega
      have d35178 : (x (-7) 14).toNat = 1 := by
        have r35179 := hand2 (x (-7) 1) (x (-7) 14)
        have b35180 := hb (x (-7) 14)
        have b35181 := hb (x (-7) 1 && x (-7) 14)
        clear * - r35179 b35180 b35181 d35173
        omega
      have d35182 : (x (-8) 1).toNat = 0 := by
        have r35183 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35184 := hb (x (-8) 1)
        have b35185 := hb (x (-7) 14)
        clear * - r35183 b35184 b35185 d35178
        omega
      have d35186 : (x (-8) 13).toNat = 0 := by
        have r35187 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b35188 := hb (x (-8) 1)
        have b35189 := hb (x (-8) 13)
        clear * - r35187 b35188 b35189 d35182
        omega
      have d35190 : (x (-8) 5).toNat = 0 := by
        have r35191 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
        have b35192 := hb (x (-8) 5)
        have b35193 := hb (x (-8) 13)
        clear * - r35191 b35192 b35193 d35186
        omega
      have d35194 : (x (-12) 3).toNat = 0 := by
        have r35195 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35196 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
        have e35197 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
        have b35198 := hb (x (-12) 3)
        have b35199 := hb (x (-11) 2)
        have b35200 := hb (x (-10) 13)
        have b35201 := hb (x (-9) 12)
        clear * - r35195 e35196 e35197 b35198 b35199 b35200 b35201 d35132 d34220 d35136
        omega
      have d35202 : (x (-12) 3 && x (-12) 14).toNat = 0 := by
        have r35203 := hand1 (x (-12) 3) (x (-12) 14)
        have b35204 := hb (x (-12) 3)
        have b35205 := hb (x (-12) 3 && x (-12) 14)
        clear * - r35203 b35204 b35205 d35194
        omega
      have d35206 : (x (-9) 11).toNat = 1 := by
        have r35207 : 1 ≤ (x (-9) 11).toNat + (x (-10) 1 && x (-10) 12).toNat + (x (-11) 2 && x (-11) 13).toNat + (x (-12) 3 && x (-12) 14).toNat + (x (-13) 4).toNat := by have q := hcov11 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35208 := hb (x (-13) 4)
        have b35209 := hb (x (-9) 11)
        have b35210 := hb (x (-10) 1 && x (-10) 12)
        have b35211 := hb (x (-11) 2 && x (-11) 13)
        have b35212 := hb (x (-12) 3 && x (-12) 14)
        clear * - r35207 b35208 b35209 b35210 b35211 b35212 d34216 d35144 d35202 d34176
        omega
      have d35213 : (x (-9) 3).toNat = 1 := by
        have r35214 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
        have b35215 := hb (x (-9) 3)
        have b35216 := hb (x (-9) 11)
        clear * - r35214 b35215 b35216 d35206
        omega
      have d35217 : (x (-6) 12).toNat = 0 := by
        have r35218 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35219 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e35220 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b35221 := hb (x (-9) 3)
        have b35222 := hb (x (-8) 2)
        have b35223 := hb (x (-7) 13)
        have b35224 := hb (x (-6) 12)
        clear * - r35218 e35219 e35220 b35221 b35222 b35223 b35224 d35169 d35213
        omega
      have d35225 : (x (-6) 3 && x (-6) 12).toNat = 0 := by
        have r35226 := hand2 (x (-6) 3) (x (-6) 12)
        have b35227 := hb (x (-6) 12)
        have b35228 := hb (x (-6) 3 && x (-6) 12)
        clear * - r35226 b35227 b35228 d35217
        omega
      have d35229 : (x (-7) 13).toNat = 0 := by
        have r35230 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35231 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e35232 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b35233 := hb (x (-9) 3)
        have b35234 := hb (x (-8) 2)
        have b35235 := hb (x (-7) 13)
        have b35236 := hb (x (-6) 12)
        clear * - r35230 e35231 e35232 b35233 b35234 b35235 b35236 d35217 d35169 d35213
        omega
      have d35237 : (x (-7) 4 && x (-7) 13).toNat = 0 := by
        have r35238 := hand2 (x (-7) 4) (x (-7) 13)
        have b35239 := hb (x (-7) 13)
        have b35240 := hb (x (-7) 4 && x (-7) 13)
        clear * - r35238 b35239 b35240 d35229
        omega
      have d35241 : (x (-9) 6).toNat = 1 := by
        have r35242 : 1 ≤ (x (-3) 9).toNat + (x (-4) 1 && x (-4) 10).toNat + (x (-5) 2 && x (-5) 11).toNat + (x (-6) 3 && x (-6) 12).toNat + (x (-7) 4 && x (-7) 13).toNat + (x (-8) 5 && x (-8) 14).toNat + (x (-9) 6).toNat := by have q := hcov9 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35243 := hb (x (-9) 6)
        have b35244 := hb (x (-3) 9)
        have b35245 := hb (x (-4) 1 && x (-4) 10)
        have b35246 := hb (x (-5) 2 && x (-5) 11)
        have b35247 := hb (x (-6) 3 && x (-6) 12)
        have b35248 := hb (x (-7) 4 && x (-7) 13)
        have b35249 := hb (x (-8) 5 && x (-8) 14)
        clear * - r35242 b35243 b35244 b35245 b35246 b35247 b35248 b35249 d34871 d34907 d34927 d35225 d35237 d35165
        omega
      have d35250 : (x (-7) 13 && x (-7) 14).toNat = 0 := by
        have r35251 := hand1 (x (-7) 13) (x (-7) 14)
        have b35252 := hb (x (-7) 13)
        have b35253 := hb (x (-7) 13 && x (-7) 14)
        clear * - r35251 b35252 b35253 d35229
        omega
      have d35254 : (x (-9) 2).toNat = 1 := by
        have r35255 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35256 := hb (x (-9) 2)
        have b35257 := hb (x (-7) 13)
        have b35258 := hb (x (-8) 1 && x (-8) 14)
        clear * - r35255 b35256 b35257 b35258 d35229 d35161
        omega
      have d35259 : (x (-7) 12).toNat = 0 := by
        have r35260 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35261 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e35262 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b35263 := hb (x (-10) 3)
        have b35264 := hb (x (-9) 2)
        have b35265 := hb (x (-8) 13)
        have b35266 := hb (x (-7) 12)
        clear * - r35260 e35261 e35262 b35263 b35264 b35265 b35266 d35186 d35254
        omega
      have d35267 : (x (-7) 4).toNat = 0 := by
        have r35268 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
        have b35269 := hb (x (-7) 4)
        have b35270 := hb (x (-7) 12)
        clear * - r35268 b35269 b35270 d35259
        omega
      have d35271 : (x (-3) 12).toNat = 0 := by
        have r35272 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35273 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e35274 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b35275 := hb (x (-6) 3)
        have b35276 := hb (x (-5) 2)
        have b35277 := hb (x (-4) 13)
        have b35278 := hb (x (-3) 12)
        clear * - r35272 e35273 e35274 b35275 b35276 b35277 b35278 d35108
        omega
      have d35279 : (x (-4) 13).toNat = 0 := by
        have r35280 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35281 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e35282 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b35283 := hb (x (-6) 3)
        have b35284 := hb (x (-5) 2)
        have b35285 := hb (x (-4) 13)
        have b35286 := hb (x (-3) 12)
        clear * - r35280 e35281 e35282 b35283 b35284 b35285 b35286 d35271 d35108
        omega
      have d35287 : (x (-6) 3).toNat = 0 := by
        have r35288 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35289 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e35290 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b35291 := hb (x (-6) 3)
        have b35292 := hb (x (-5) 2)
        have b35293 := hb (x (-4) 13)
        have b35294 := hb (x (-3) 12)
        clear * - r35288 e35289 e35290 b35291 b35292 b35293 b35294 d35271 d35279 d35108
        omega
      have d35295 : (x (-6) 11).toNat = 0 := by
        have r35296 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
        have b35297 := hb (x (-6) 3)
        have b35298 := hb (x (-6) 11)
        clear * - r35296 b35297 b35298 d35287
        omega
      have d35299 : (x (-4) 9 && x (-4) 14).toNat = 0 := by
        have r35300 := hand2 (x (-4) 9) (x (-4) 14)
        have b35301 := hb (x (-4) 14)
        have b35302 := hb (x (-4) 9 && x (-4) 14)
        clear * - r35300 b35301 b35302 d35100
        omega
      have d35303 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
        have r35304 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35305 := hb (x (-4) 2)
        have b35306 := hb (x (-2) 13)
        have b35307 := hb (x (-3) 1 && x (-3) 14)
        clear * - r35304 b35305 b35306 b35307 g14 d35072
        omega
      have d35308 : (x (-3) 14).toNat = 1 := by
        have r35309 := hand2 (x (-3) 1) (x (-3) 14)
        have b35310 := hb (x (-3) 14)
        have b35311 := hb (x (-3) 1 && x (-3) 14)
        clear * - r35309 b35310 b35311 d35303
        omega
      have d35312 : (x (-4) 1).toNat = 0 := by
        have r35313 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35314 := hb (x (-4) 1)
        have b35315 := hb (x (-3) 14)
        clear * - r35313 b35314 b35315 d35308
        omega
      have d35316 : (x (-4) 9).toNat = 0 := by
        have r35317 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
        have b35318 := hb (x (-4) 1)
        have b35319 := hb (x (-4) 9)
        clear * - r35317 b35318 b35319 d35312
        omega
      have d35320 : (x (-3) 1).toNat = 1 := by
        have r35321 := hand1 (x (-3) 1) (x (-3) 14)
        have b35322 := hb (x (-3) 1)
        have b35323 := hb (x (-3) 1 && x (-3) 14)
        clear * - r35321 b35322 b35323 d35303
        omega
      have d35324 : (x (-2) 14).toNat = 0 := by
        have r35325 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35326 := hb (x (-3) 1)
        have b35327 := hb (x (-2) 14)
        clear * - r35325 b35326 b35327 d35320
        omega
      have d35328 : (x (-2) 7 && x (-2) 14).toNat = 0 := by
        have r35329 := hand2 (x (-2) 7) (x (-2) 14)
        have b35330 := hb (x (-2) 14)
        have b35331 := hb (x (-2) 7 && x (-2) 14)
        clear * - r35329 b35330 b35331 d35324
        omega
      have d35332 : (x (-2) 8 && x (-2) 14).toNat = 0 := by
        have r35333 := hand2 (x (-2) 8) (x (-2) 14)
        have b35334 := hb (x (-2) 14)
        have b35335 := hb (x (-2) 8 && x (-2) 14)
        clear * - r35333 b35334 b35335 d35324
        omega
      have d35336 : (x (-3) 8).toNat = 0 := by
        have r35337 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35338 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
        have e35339 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
        have e35340 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
        have e35341 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
        have e35342 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
        have e35343 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
        have b35344 := hb (x (-10) 7)
        have b35345 := hb (x (-9) 6)
        have b35346 := hb (x (-8) 5)
        have b35347 := hb (x (-7) 4)
        have b35348 := hb (x (-6) 11)
        have b35349 := hb (x (-5) 10)
        have b35350 := hb (x (-4) 9)
        have b35351 := hb (x (-3) 8)
        clear * - r35337 e35338 e35339 e35340 e35341 e35342 e35343 b35344 b35345 b35346 b35347 b35348 b35349 b35350 b35351 d35316 d35295 d35267 d35190 d35241
        omega
      have d35352 : (x (-5) 10).toNat = 0 := by
        have r35353 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35354 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
        have e35355 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
        have e35356 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
        have e35357 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
        have e35358 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
        have e35359 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
        have b35360 := hb (x (-10) 7)
        have b35361 := hb (x (-9) 6)
        have b35362 := hb (x (-8) 5)
        have b35363 := hb (x (-7) 4)
        have b35364 := hb (x (-6) 11)
        have b35365 := hb (x (-5) 10)
        have b35366 := hb (x (-4) 9)
        have b35367 := hb (x (-3) 8)
        clear * - r35353 e35354 e35355 e35356 e35357 e35358 e35359 b35360 b35361 b35362 b35363 b35364 b35365 b35366 b35367 d35336 d35316 d35295 d35267 d35190 d35241
        omega
      have d35368 : (x 5 7).toNat = 1 := by
        have r35369 : 1 ≤ (x 5 7).toNat + (x 4 1 && x 4 8).toNat + (x 3 2 && x 3 9).toNat + (x 2 3 && x 2 10).toNat + (x 1 4 && x 1 11).toNat + (x 0 5 && x 0 12).toNat + (x (-1) 6 && x (-1) 13).toNat + (x (-2) 7 && x (-2) 14).toNat + (x (-3) 8).toNat := by have q := hcov7 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35370 := hb (x (-3) 8)
        have b35371 := hb (x 5 7)
        have b35372 := hb (x 4 1 && x 4 8)
        have b35373 := hb (x 3 2 && x 3 9)
        have b35374 := hb (x 2 3 && x 2 10)
        have b35375 := hb (x 1 4 && x 1 11)
        have b35376 := hb (x 0 5 && x 0 12)
        have b35377 := hb (x (-1) 6 && x (-1) 13)
        have b35378 := hb (x (-2) 7 && x (-2) 14)
        clear * - r35369 b35370 b35371 b35372 b35373 b35374 b35375 b35376 b35377 b35378 g113 g114 g115 g116 g117 d34083 d35328 d35336
        omega
      have d35379 : (x 12 8).toNat = 0 := by
        have r35380 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35381 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e35382 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e35383 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e35384 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e35385 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e35386 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b35387 := hb (x 5 7)
        have b35388 := hb (x 6 6)
        have b35389 := hb (x 7 5)
        have b35390 := hb (x 8 4)
        have b35391 := hb (x 9 11)
        have b35392 := hb (x 10 10)
        have b35393 := hb (x 11 9)
        have b35394 := hb (x 12 8)
        clear * - r35380 e35381 e35382 e35383 e35384 e35385 e35386 b35387 b35388 b35389 b35390 b35391 b35392 b35393 b35394 d35368
        omega
      have d35395 : (x 11 9).toNat = 0 := by
        have r35396 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35397 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e35398 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e35399 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e35400 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e35401 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e35402 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b35403 := hb (x 5 7)
        have b35404 := hb (x 6 6)
        have b35405 := hb (x 7 5)
        have b35406 := hb (x 8 4)
        have b35407 := hb (x 9 11)
        have b35408 := hb (x 10 10)
        have b35409 := hb (x 11 9)
        have b35410 := hb (x 12 8)
        clear * - r35396 e35397 e35398 e35399 e35400 e35401 e35402 b35403 b35404 b35405 b35406 b35407 b35408 b35409 b35410 d35379 d35368
        omega
      have d35411 : (x 10 10).toNat = 0 := by
        have r35412 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35413 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e35414 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e35415 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e35416 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e35417 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e35418 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b35419 := hb (x 5 7)
        have b35420 := hb (x 6 6)
        have b35421 := hb (x 7 5)
        have b35422 := hb (x 8 4)
        have b35423 := hb (x 9 11)
        have b35424 := hb (x 10 10)
        have b35425 := hb (x 11 9)
        have b35426 := hb (x 12 8)
        clear * - r35412 e35413 e35414 e35415 e35416 e35417 e35418 b35419 b35420 b35421 b35422 b35423 b35424 b35425 b35426 d35379 d35395 d35368
        omega
      have d35427 : (x 10 1 && x 10 10).toNat = 0 := by
        have r35428 := hand2 (x 10 1) (x 10 10)
        have b35429 := hb (x 10 10)
        have b35430 := hb (x 10 1 && x 10 10)
        clear * - r35428 b35429 b35430 d35411
        omega
      have d35431 : (x 9 11).toNat = 0 := by
        have r35432 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35433 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e35434 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e35435 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e35436 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e35437 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e35438 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b35439 := hb (x 5 7)
        have b35440 := hb (x 6 6)
        have b35441 := hb (x 7 5)
        have b35442 := hb (x 8 4)
        have b35443 := hb (x 9 11)
        have b35444 := hb (x 10 10)
        have b35445 := hb (x 11 9)
        have b35446 := hb (x 12 8)
        clear * - r35432 e35433 e35434 e35435 e35436 e35437 e35438 b35439 b35440 b35441 b35442 b35443 b35444 b35445 b35446 d35379 d35395 d35411 d35368
        omega
      have d35447 : (x 9 1 && x 9 11).toNat = 0 := by
        have r35448 := hand2 (x 9 1) (x 9 11)
        have b35449 := hb (x 9 11)
        have b35450 := hb (x 9 1 && x 9 11)
        clear * - r35448 b35449 b35450 d35431
        omega
      have d35451 : (x 9 2 && x 9 11).toNat = 0 := by
        have r35452 := hand2 (x 9 2) (x 9 11)
        have b35453 := hb (x 9 11)
        have b35454 := hb (x 9 2 && x 9 11)
        clear * - r35452 b35453 b35454 d35431
        omega
      have d35455 : (x 8 4).toNat = 0 := by
        have r35456 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35457 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e35458 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e35459 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e35460 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e35461 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e35462 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b35463 := hb (x 5 7)
        have b35464 := hb (x 6 6)
        have b35465 := hb (x 7 5)
        have b35466 := hb (x 8 4)
        have b35467 := hb (x 9 11)
        have b35468 := hb (x 10 10)
        have b35469 := hb (x 11 9)
        have b35470 := hb (x 12 8)
        clear * - r35456 e35457 e35458 e35459 e35460 e35461 e35462 b35463 b35464 b35465 b35466 b35467 b35468 b35469 b35470 d35379 d35395 d35411 d35431 d35368
        omega
      have d35471 : (x 7 5).toNat = 0 := by
        have r35472 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35473 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e35474 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e35475 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e35476 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e35477 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e35478 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b35479 := hb (x 5 7)
        have b35480 := hb (x 6 6)
        have b35481 := hb (x 7 5)
        have b35482 := hb (x 8 4)
        have b35483 := hb (x 9 11)
        have b35484 := hb (x 10 10)
        have b35485 := hb (x 11 9)
        have b35486 := hb (x 12 8)
        clear * - r35472 e35473 e35474 e35475 e35476 e35477 e35478 b35479 b35480 b35481 b35482 b35483 b35484 b35485 b35486 d35379 d35395 d35411 d35431 d35455 d35368
        omega
      have d35487 : (x 6 6).toNat = 0 := by
        have r35488 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35489 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e35490 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e35491 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e35492 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e35493 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e35494 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b35495 := hb (x 5 7)
        have b35496 := hb (x 6 6)
        have b35497 := hb (x 7 5)
        have b35498 := hb (x 8 4)
        have b35499 := hb (x 9 11)
        have b35500 := hb (x 10 10)
        have b35501 := hb (x 11 9)
        have b35502 := hb (x 12 8)
        clear * - r35488 e35489 e35490 e35491 e35492 e35493 e35494 b35495 b35496 b35497 b35498 b35499 b35500 b35501 b35502 d35379 d35395 d35411 d35431 d35455 d35471 d35368
        omega
      have d35503 : (x 5 1 && x 5 7).toNat = 1 := by
        have r35504 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35505 := hb (x (-3) 9)
        have b35506 := hb (x 6 6)
        have b35507 := hb (x 5 1 && x 5 7)
        have b35508 := hb (x 4 2 && x 4 8)
        have b35509 := hb (x 3 3 && x 3 9)
        have b35510 := hb (x 2 4 && x 2 10)
        have b35511 := hb (x 1 5 && x 1 11)
        have b35512 := hb (x 0 6 && x 0 12)
        have b35513 := hb (x (-1) 7 && x (-1) 13)
        have b35514 := hb (x (-2) 8 && x (-2) 14)
        clear * - r35504 b35505 b35506 b35507 b35508 b35509 b35510 b35511 b35512 b35513 b35514 d35487 g100 g101 g102 g103 g104 d34093 d35332 d34871
        omega
      have d35515 : (x 5 1).toNat = 1 := by
        have r35516 := hand1 (x 5 1) (x 5 7)
        have b35517 := hb (x 5 1)
        have b35518 := hb (x 5 1 && x 5 7)
        clear * - r35516 b35517 b35518 d35503
        omega
      have d35519 : (x 6 14).toNat = 0 := by
        have r35520 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35521 := hb (x 5 1)
        have b35522 := hb (x 6 14)
        clear * - r35520 b35521 b35522 d35515
        omega
      have d35523 : (x 6 4 && x 6 14).toNat = 0 := by
        have r35524 := hand2 (x 6 4) (x 6 14)
        have b35525 := hb (x 6 14)
        have b35526 := hb (x 6 4 && x 6 14)
        clear * - r35524 b35525 b35526 d35519
        omega
      have d35527 : (x 6 5 && x 6 14).toNat = 0 := by
        have r35528 := hand2 (x 6 5) (x 6 14)
        have b35529 := hb (x 6 14)
        have b35530 := hb (x 6 5 && x 6 14)
        clear * - r35528 b35529 b35530 d35519
        omega
      have d35531 : (x 6 2).toNat = 0 := by
        have r35532 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have b35533 := hb (x 6 2)
        have b35534 := hb (x 6 14)
        clear * - r35532 b35533 b35534 d35519
        omega
      have d35535 : (x 6 2 && x 6 12).toNat = 0 := by
        have r35536 := hand1 (x 6 2) (x 6 12)
        have b35537 := hb (x 6 2)
        have b35538 := hb (x 6 2 && x 6 12)
        clear * - r35536 b35537 b35538 d35531
        omega
      have d35539 : (x 6 1).toNat = 0 := by
        have r35540 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35541 := hb (x (-7) 14)
        have b35542 := hb (x (-6) 13)
        have b35543 := hb (x (-5) 12)
        have b35544 := hb (x (-4) 11)
        have b35545 := hb (x (-3) 10)
        have b35546 := hb (x (-2) 9)
        have b35547 := hb (x (-1) 8)
        have b35548 := hb (x 0 7)
        have b35549 := hb (x 1 6)
        have b35550 := hb (x 2 5)
        have b35551 := hb (x 3 4)
        have b35552 := hb (x 4 3)
        have b35553 := hb (x 5 2)
        have b35554 := hb (x 6 1)
        clear * - r35540 b35541 b35542 b35543 b35544 b35545 b35546 b35547 b35548 b35549 b35550 b35551 b35552 b35553 b35554 g49 f34235 g36 g27 g18 g11 g7 g4 d35004 d35008 d35178
        omega
      have d35555 : (x 6 13).toNat = 0 := by
        have r35556 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
        have b35557 := hb (x 6 1)
        have b35558 := hb (x 6 13)
        clear * - r35556 b35557 b35558 d35539
        omega
      have d35559 : (x 6 3 && x 6 13).toNat = 0 := by
        have r35560 := hand2 (x 6 3) (x 6 13)
        have b35561 := hb (x 6 13)
        have b35562 := hb (x 6 3 && x 6 13)
        clear * - r35560 b35561 b35562 d35555
        omega
      have d35563 : (x 6 5).toNat = 0 := by
        have r35564 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
        have b35565 := hb (x 6 5)
        have b35566 := hb (x 6 13)
        clear * - r35564 b35565 b35566 d35555
        omega
      have d35567 : (x 5 2).toNat = 0 := by
        have r35568 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35569 := hb (x (-7) 14)
        have b35570 := hb (x (-6) 13)
        have b35571 := hb (x (-5) 12)
        have b35572 := hb (x (-4) 11)
        have b35573 := hb (x (-3) 10)
        have b35574 := hb (x (-2) 9)
        have b35575 := hb (x (-1) 8)
        have b35576 := hb (x 0 7)
        have b35577 := hb (x 1 6)
        have b35578 := hb (x 2 5)
        have b35579 := hb (x 3 4)
        have b35580 := hb (x 4 3)
        have b35581 := hb (x 5 2)
        have b35582 := hb (x 6 1)
        clear * - r35568 b35569 b35570 b35571 b35572 b35573 b35574 b35575 b35576 b35577 b35578 b35579 b35580 b35581 b35582 d35539 g49 f34235 g36 g27 g18 g11 g7 g4 d35004 d35008 d35178
        omega
      have d35583 : (x 5 1 && x 5 2).toNat = 0 := by
        have r35584 := hand2 (x 5 1) (x 5 2)
        have b35585 := hb (x 5 2)
        have b35586 := hb (x 5 1 && x 5 2)
        clear * - r35584 b35585 b35586 d35567
        omega
      have d35587 : (x 4 2 && x 4 3).toNat = 1 := by
        have r35588 : 1 ≤ (x 6 1).toNat + (x 5 1 && x 5 2).toNat + (x 4 2 && x 4 3).toNat + (x 3 3 && x 3 4).toNat + (x 2 4 && x 2 5).toNat + (x 1 5 && x 1 6).toNat + (x 0 6 && x 0 7).toNat + (x (-1) 7 && x (-1) 8).toNat + (x (-2) 8 && x (-2) 9).toNat + (x (-3) 9 && x (-3) 10).toNat + (x (-4) 10 && x (-4) 11).toNat + (x (-5) 11 && x (-5) 12).toNat + (x (-6) 12 && x (-6) 13).toNat + (x (-7) 13 && x (-7) 14).toNat + (x (-8) 14).toNat := by have q := hcov1 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35589 := hb (x (-8) 14)
        have b35590 := hb (x 6 1)
        have b35591 := hb (x 5 1 && x 5 2)
        have b35592 := hb (x 4 2 && x 4 3)
        have b35593 := hb (x 3 3 && x 3 4)
        have b35594 := hb (x 2 4 && x 2 5)
        have b35595 := hb (x 1 5 && x 1 6)
        have b35596 := hb (x 0 6 && x 0 7)
        have b35597 := hb (x (-1) 7 && x (-1) 8)
        have b35598 := hb (x (-2) 8 && x (-2) 9)
        have b35599 := hb (x (-3) 9 && x (-3) 10)
        have b35600 := hb (x (-4) 10 && x (-4) 11)
        have b35601 := hb (x (-5) 11 && x (-5) 12)
        have b35602 := hb (x (-6) 12 && x (-6) 13)
        have b35603 := hb (x (-7) 13 && x (-7) 14)
        clear * - r35588 b35589 b35590 b35591 b35592 b35593 b35594 b35595 b35596 b35597 b35598 b35599 b35600 b35601 b35602 b35603 d35539 d35583 g54 g55 g56 g57 d34113 g58 g59 g60 d34931 d35016 d35250 d35157
        omega
      have d35604 : (x 4 2).toNat = 1 := by
        have r35605 := hand1 (x 4 2) (x 4 3)
        have b35606 := hb (x 4 2)
        have b35607 := hb (x 4 2 && x 4 3)
        clear * - r35605 b35606 b35607 d35587
        omega
      have d35608 : (x 4 14).toNat = 1 := by
        have r35609 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
        have b35610 := hb (x 4 2)
        have b35611 := hb (x 4 14)
        clear * - r35609 b35610 b35611 d35604
        omega
      have d35612 : (x 3 1).toNat = 0 := by
        have r35613 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35614 := hb (x 3 1)
        have b35615 := hb (x 4 14)
        clear * - r35613 b35614 b35615 d35608
        omega
      have d35616 : (x 3 13).toNat = 0 := by
        have r35617 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b35618 := hb (x 3 1)
        have b35619 := hb (x 3 13)
        clear * - r35617 b35618 b35619 d35612
        omega
      have d35620 : (x 3 5).toNat = 0 := by
        have r35621 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
        have b35622 := hb (x 3 5)
        have b35623 := hb (x 3 13)
        clear * - r35621 b35622 b35623 d35616
        omega
      have d35624 : (x 6 12).toNat = 0 := by
        have r35625 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35626 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e35627 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b35628 := hb (x 3 3)
        have b35629 := hb (x 4 2)
        have b35630 := hb (x 5 13)
        have b35631 := hb (x 6 12)
        clear * - r35625 e35626 e35627 b35628 b35629 b35630 b35631 d35604
        omega
      have d35632 : (x 6 4).toNat = 0 := by
        have r35633 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
        have b35634 := hb (x 6 4)
        have b35635 := hb (x 6 12)
        clear * - r35633 b35634 b35635 d35624
        omega
      have d35636 : (x 5 13).toNat = 0 := by
        have r35637 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35638 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e35639 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b35640 := hb (x 3 3)
        have b35641 := hb (x 4 2)
        have b35642 := hb (x 5 13)
        have b35643 := hb (x 6 12)
        clear * - r35637 e35638 e35639 b35640 b35641 b35642 b35643 d35624 d35604
        omega
      have d35644 : (x 5 3 && x 5 13).toNat = 0 := by
        have r35645 := hand2 (x 5 3) (x 5 13)
        have b35646 := hb (x 5 13)
        have b35647 := hb (x 5 3 && x 5 13)
        clear * - r35645 b35646 b35647 d35636
        omega
      have d35648 : (x 5 5).toNat = 0 := by
        have r35649 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
        have b35650 := hb (x 5 5)
        have b35651 := hb (x 5 13)
        clear * - r35649 b35650 b35651 d35636
        omega
      have d35652 : (x 4 1 && x 4 6).toNat = 1 := by
        have r35653 : 1 ≤ (x 5 5).toNat + (x 4 1 && x 4 6).toNat + (x 3 2 && x 3 7).toNat + (x 2 3 && x 2 8).toNat + (x 1 4 && x 1 9).toNat + (x 0 5 && x 0 10).toNat + (x (-1) 6 && x (-1) 11).toNat + (x (-2) 7 && x (-2) 12).toNat + (x (-3) 8 && x (-3) 13).toNat + (x (-4) 9 && x (-4) 14).toNat + (x (-5) 10).toNat := by have q := hcov5 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35654 := hb (x (-5) 10)
        have b35655 := hb (x 5 5)
        have b35656 := hb (x 4 1 && x 4 6)
        have b35657 := hb (x 3 2 && x 3 7)
        have b35658 := hb (x 2 3 && x 2 8)
        have b35659 := hb (x 1 4 && x 1 9)
        have b35660 := hb (x 0 5 && x 0 10)
        have b35661 := hb (x (-1) 6 && x (-1) 11)
        have b35662 := hb (x (-2) 7 && x (-2) 12)
        have b35663 := hb (x (-3) 8 && x (-3) 13)
        have b35664 := hb (x (-4) 9 && x (-4) 14)
        clear * - r35653 b35654 b35655 b35656 b35657 b35658 b35659 b35660 b35661 b35662 b35663 b35664 d35648 g76 g77 g78 g79 d34087 d35056 d35068 d35299 d35352
        omega
      have d35665 : (x 4 6).toNat = 1 := by
        have r35666 := hand2 (x 4 1) (x 4 6)
        have b35667 := hb (x 4 6)
        have b35668 := hb (x 4 1 && x 4 6)
        clear * - r35666 b35667 b35668 d35652
        omega
      have d35669 : (x 10 8).toNat = 0 := by
        have r35670 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35671 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e35672 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e35673 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e35674 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e35675 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e35676 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b35677 := hb (x 3 7)
        have b35678 := hb (x 4 6)
        have b35679 := hb (x 5 5)
        have b35680 := hb (x 6 4)
        have b35681 := hb (x 7 11)
        have b35682 := hb (x 8 10)
        have b35683 := hb (x 9 9)
        have b35684 := hb (x 10 8)
        clear * - r35670 e35671 e35672 e35673 e35674 e35675 e35676 b35677 b35678 b35679 b35680 b35681 b35682 b35683 b35684 d35632 d35648 d35665
        omega
      have d35685 : (x 9 9).toNat = 0 := by
        have r35686 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35687 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e35688 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e35689 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e35690 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e35691 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e35692 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b35693 := hb (x 3 7)
        have b35694 := hb (x 4 6)
        have b35695 := hb (x 5 5)
        have b35696 := hb (x 6 4)
        have b35697 := hb (x 7 11)
        have b35698 := hb (x 8 10)
        have b35699 := hb (x 9 9)
        have b35700 := hb (x 10 8)
        clear * - r35686 e35687 e35688 e35689 e35690 e35691 e35692 b35693 b35694 b35695 b35696 b35697 b35698 b35699 b35700 d35669 d35632 d35648 d35665
        omega
      have d35701 : (x 8 10).toNat = 0 := by
        have r35702 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35703 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e35704 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e35705 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e35706 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e35707 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e35708 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b35709 := hb (x 3 7)
        have b35710 := hb (x 4 6)
        have b35711 := hb (x 5 5)
        have b35712 := hb (x 6 4)
        have b35713 := hb (x 7 11)
        have b35714 := hb (x 8 10)
        have b35715 := hb (x 9 9)
        have b35716 := hb (x 10 8)
        clear * - r35702 e35703 e35704 e35705 e35706 e35707 e35708 b35709 b35710 b35711 b35712 b35713 b35714 b35715 b35716 d35669 d35685 d35632 d35648 d35665
        omega
      have d35717 : (x 7 11).toNat = 0 := by
        have r35718 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35719 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e35720 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e35721 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e35722 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e35723 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e35724 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b35725 := hb (x 3 7)
        have b35726 := hb (x 4 6)
        have b35727 := hb (x 5 5)
        have b35728 := hb (x 6 4)
        have b35729 := hb (x 7 11)
        have b35730 := hb (x 8 10)
        have b35731 := hb (x 9 9)
        have b35732 := hb (x 10 8)
        clear * - r35718 e35719 e35720 e35721 e35722 e35723 e35724 b35725 b35726 b35727 b35728 b35729 b35730 b35731 b35732 d35669 d35685 d35701 d35632 d35648 d35665
        omega
      have d35733 : (x 7 1 && x 7 11).toNat = 0 := by
        have r35734 := hand2 (x 7 1) (x 7 11)
        have b35735 := hb (x 7 11)
        have b35736 := hb (x 7 1 && x 7 11)
        clear * - r35734 b35735 b35736 d35717
        omega
      have d35737 : (x 4 4 && x 4 14).toNat = 1 := by
        have r35738 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35739 := hb (x 3 5)
        have b35740 := hb (x 8 10)
        have b35741 := hb (x 7 1 && x 7 11)
        have b35742 := hb (x 6 2 && x 6 12)
        have b35743 := hb (x 5 3 && x 5 13)
        have b35744 := hb (x 4 4 && x 4 14)
        clear * - r35738 b35739 b35740 b35741 b35742 b35743 b35744 d35701 d35733 d35535 d35644 d35620
        omega
      have d35745 : (x 4 4).toNat = 1 := by
        have r35746 := hand1 (x 4 4) (x 4 14)
        have b35747 := hb (x 4 4)
        have b35748 := hb (x 4 4 && x 4 14)
        clear * - r35746 b35747 b35748 d35737
        omega
      have d35749 : (x 4 12).toNat = 1 := by
        have r35750 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b35751 := hb (x 4 4)
        have b35752 := hb (x 4 12)
        clear * - r35750 b35751 b35752 d35745
        omega
      have d35753 : (x 2 2).toNat = 0 := by
        have r35754 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35755 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e35756 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b35757 := hb (x 1 3)
        have b35758 := hb (x 2 2)
        have b35759 := hb (x 3 13)
        have b35760 := hb (x 4 12)
        clear * - r35754 e35755 e35756 b35757 b35758 b35759 b35760 d35749 d35616 g34
        omega
      have d35761 : (x 4 13).toNat = 1 := by
        have r35762 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35763 := hb (x 2 2)
        have b35764 := hb (x 4 13)
        have b35765 := hb (x 3 1 && x 3 14)
        clear * - r35762 b35763 b35764 b35765 g135 d35753
        omega
      have d35766 : (x 4 1).toNat = 1 := by
        have r35767 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b35768 := hb (x 4 1)
        have b35769 := hb (x 4 13)
        clear * - r35767 b35768 b35769 d35761
        omega
      have d35770 : (x 5 14).toNat = 0 := by
        have r35771 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35772 := hb (x 4 1)
        have b35773 := hb (x 5 14)
        clear * - r35771 b35772 b35773 d35766
        omega
      have d35774 : (x 5 4 && x 5 14).toNat = 0 := by
        have r35775 := hand2 (x 5 4) (x 5 14)
        have b35776 := hb (x 5 14)
        have b35777 := hb (x 5 4 && x 5 14)
        clear * - r35775 b35776 b35777 d35770
        omega
      have d35778 : (x 5 6).toNat = 0 := by
        have r35779 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
        have b35780 := hb (x 5 6)
        have b35781 := hb (x 5 14)
        clear * - r35779 b35780 b35781 d35770
        omega
      have d35782 : (x 5 1 && x 5 6).toNat = 0 := by
        have r35783 := hand2 (x 5 1) (x 5 6)
        have b35784 := hb (x 5 6)
        have b35785 := hb (x 5 1 && x 5 6)
        clear * - r35783 b35784 b35785 d35778
        omega
      have d35786 : (x 4 2 && x 4 7).toNat = 1 := by
        have r35787 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35788 := hb (x (-4) 10)
        have b35789 := hb (x 6 5)
        have b35790 := hb (x 5 1 && x 5 6)
        have b35791 := hb (x 4 2 && x 4 7)
        have b35792 := hb (x 3 3 && x 3 8)
        have b35793 := hb (x 2 4 && x 2 9)
        have b35794 := hb (x 1 5 && x 1 10)
        have b35795 := hb (x 0 6 && x 0 11)
        have b35796 := hb (x (-1) 7 && x (-1) 12)
        have b35797 := hb (x (-2) 8 && x (-2) 13)
        have b35798 := hb (x (-3) 9 && x (-3) 14)
        clear * - r35787 b35788 b35789 b35790 b35791 b35792 b35793 b35794 b35795 b35796 b35797 b35798 d35563 d35782 g80 g81 g82 g83 d34101 g84 d34887 d34891
        omega
      have d35799 : (x 4 7).toNat = 1 := by
        have r35800 := hand2 (x 4 2) (x 4 7)
        have b35801 := hb (x 4 7)
        have b35802 := hb (x 4 2 && x 4 7)
        clear * - r35800 b35801 b35802 d35786
        omega
      have d35803 : (x 11 8).toNat = 0 := by
        have r35804 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35805 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e35806 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e35807 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e35808 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e35809 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e35810 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b35811 := hb (x 4 7)
        have b35812 := hb (x 5 6)
        have b35813 := hb (x 6 5)
        have b35814 := hb (x 7 4)
        have b35815 := hb (x 8 11)
        have b35816 := hb (x 9 10)
        have b35817 := hb (x 10 9)
        have b35818 := hb (x 11 8)
        clear * - r35804 e35805 e35806 e35807 e35808 e35809 e35810 b35811 b35812 b35813 b35814 b35815 b35816 b35817 b35818 d35563 d35778 d35799
        omega
      have d35819 : (x 10 9).toNat = 0 := by
        have r35820 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35821 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e35822 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e35823 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e35824 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e35825 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e35826 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b35827 := hb (x 4 7)
        have b35828 := hb (x 5 6)
        have b35829 := hb (x 6 5)
        have b35830 := hb (x 7 4)
        have b35831 := hb (x 8 11)
        have b35832 := hb (x 9 10)
        have b35833 := hb (x 10 9)
        have b35834 := hb (x 11 8)
        clear * - r35820 e35821 e35822 e35823 e35824 e35825 e35826 b35827 b35828 b35829 b35830 b35831 b35832 b35833 b35834 d35803 d35563 d35778 d35799
        omega
      have d35835 : (x 9 10).toNat = 0 := by
        have r35836 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35837 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e35838 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e35839 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e35840 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e35841 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e35842 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b35843 := hb (x 4 7)
        have b35844 := hb (x 5 6)
        have b35845 := hb (x 6 5)
        have b35846 := hb (x 7 4)
        have b35847 := hb (x 8 11)
        have b35848 := hb (x 9 10)
        have b35849 := hb (x 10 9)
        have b35850 := hb (x 11 8)
        clear * - r35836 e35837 e35838 e35839 e35840 e35841 e35842 b35843 b35844 b35845 b35846 b35847 b35848 b35849 b35850 d35803 d35819 d35563 d35778 d35799
        omega
      have d35851 : (x 8 11).toNat = 0 := by
        have r35852 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35853 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e35854 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e35855 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e35856 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e35857 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e35858 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b35859 := hb (x 4 7)
        have b35860 := hb (x 5 6)
        have b35861 := hb (x 6 5)
        have b35862 := hb (x 7 4)
        have b35863 := hb (x 8 11)
        have b35864 := hb (x 9 10)
        have b35865 := hb (x 10 9)
        have b35866 := hb (x 11 8)
        clear * - r35852 e35853 e35854 e35855 e35856 e35857 e35858 b35859 b35860 b35861 b35862 b35863 b35864 b35865 b35866 d35803 d35819 d35835 d35563 d35778 d35799
        omega
      have d35867 : (x 8 1 && x 8 11).toNat = 0 := by
        have r35868 := hand2 (x 8 1) (x 8 11)
        have b35869 := hb (x 8 11)
        have b35870 := hb (x 8 1 && x 8 11)
        clear * - r35868 b35869 b35870 d35851
        omega
      have d35871 : (x 7 4).toNat = 0 := by
        have r35872 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35873 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
        have e35874 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
        have e35875 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
        have e35876 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
        have e35877 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
        have e35878 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
        have b35879 := hb (x 4 7)
        have b35880 := hb (x 5 6)
        have b35881 := hb (x 6 5)
        have b35882 := hb (x 7 4)
        have b35883 := hb (x 8 11)
        have b35884 := hb (x 9 10)
        have b35885 := hb (x 10 9)
        have b35886 := hb (x 11 8)
        clear * - r35872 e35873 e35874 e35875 e35876 e35877 e35878 b35879 b35880 b35881 b35882 b35883 b35884 b35885 b35886 d35803 d35819 d35835 d35851 d35563 d35778 d35799
        omega
      have d35887 : (x 7 4 && x 7 13).toNat = 0 := by
        have r35888 := hand1 (x 7 4) (x 7 13)
        have b35889 := hb (x 7 4)
        have b35890 := hb (x 7 4 && x 7 13)
        clear * - r35888 b35889 b35890 d35871
        omega
      have d35891 : (x 8 3 && x 8 12).toNat = 1 := by
        have r35892 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35893 := hb (x 5 6)
        have b35894 := hb (x 11 9)
        have b35895 := hb (x 10 1 && x 10 10)
        have b35896 := hb (x 9 2 && x 9 11)
        have b35897 := hb (x 8 3 && x 8 12)
        have b35898 := hb (x 7 4 && x 7 13)
        have b35899 := hb (x 6 5 && x 6 14)
        clear * - r35892 b35893 b35894 b35895 b35896 b35897 b35898 b35899 d35395 d35427 d35451 d35887 d35527 d35778
        omega
      have d35900 : (x 8 12).toNat = 1 := by
        have r35901 := hand2 (x 8 3) (x 8 12)
        have b35902 := hb (x 8 12)
        have b35903 := hb (x 8 3 && x 8 12)
        clear * - r35901 b35902 b35903 d35891
        omega
      have d35904 : (x 7 13).toNat = 0 := by
        have r35905 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35906 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e35907 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b35908 := hb (x 5 3)
        have b35909 := hb (x 6 2)
        have b35910 := hb (x 7 13)
        have b35911 := hb (x 8 12)
        clear * - r35905 e35906 e35907 b35908 b35909 b35910 b35911 d35900 d35531
        omega
      have d35912 : (x 7 3 && x 7 13).toNat = 0 := by
        have r35913 := hand2 (x 7 3) (x 7 13)
        have b35914 := hb (x 7 13)
        have b35915 := hb (x 7 3 && x 7 13)
        clear * - r35913 b35914 b35915 d35904
        omega
      have d35916 : (x 8 2 && x 8 12).toNat = 1 := by
        have r35917 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35918 := hb (x 5 5)
        have b35919 := hb (x 10 10)
        have b35920 := hb (x 9 1 && x 9 11)
        have b35921 := hb (x 8 2 && x 8 12)
        have b35922 := hb (x 7 3 && x 7 13)
        have b35923 := hb (x 6 4 && x 6 14)
        clear * - r35917 b35918 b35919 b35920 b35921 b35922 b35923 d35411 d35447 d35912 d35523 d35648
        omega
      have d35924 : (x 8 2).toNat = 1 := by
        have r35925 := hand1 (x 8 2) (x 8 12)
        have b35926 := hb (x 8 2)
        have b35927 := hb (x 8 2 && x 8 12)
        clear * - r35925 b35926 b35927 d35916
        omega
      have d35928 : (x 8 14).toNat = 1 := by
        have r35929 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
        have b35930 := hb (x 8 2)
        have b35931 := hb (x 8 14)
        clear * - r35929 b35930 b35931 d35924
        omega
      have d35932 : (x 7 1).toNat = 0 := by
        have r35933 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35934 := hb (x 7 1)
        have b35935 := hb (x 8 14)
        clear * - r35933 b35934 b35935 d35928
        omega
      have d35936 : (x 7 1 && x 7 14).toNat = 0 := by
        have r35937 := hand1 (x 7 1) (x 7 14)
        have b35938 := hb (x 7 1)
        have b35939 := hb (x 7 1 && x 7 14)
        clear * - r35937 b35938 b35939 d35932
        omega
      have d35940 : (x 8 13).toNat = 1 := by
        have r35941 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35942 := hb (x 6 2)
        have b35943 := hb (x 8 13)
        have b35944 := hb (x 7 1 && x 7 14)
        clear * - r35941 b35942 b35943 b35944 d35936 d35531
        omega
      have d35945 : (x 8 1).toNat = 1 := by
        have r35946 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b35947 := hb (x 8 1)
        have b35948 := hb (x 8 13)
        clear * - r35946 b35947 b35948 d35940
        omega
      have d35949 : (x 7 2).toNat = 0 := by
        have r35950 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35951 := hb (x (-5) 14)
        have b35952 := hb (x (-4) 13)
        have b35953 := hb (x (-3) 12)
        have b35954 := hb (x (-2) 11)
        have b35955 := hb (x (-1) 10)
        have b35956 := hb (x 0 9)
        have b35957 := hb (x 1 8)
        have b35958 := hb (x 2 7)
        have b35959 := hb (x 3 6)
        have b35960 := hb (x 4 5)
        have b35961 := hb (x 5 4)
        have b35962 := hb (x 6 3)
        have b35963 := hb (x 7 2)
        have b35964 := hb (x 8 1)
        clear * - r35950 b35951 b35952 b35953 b35954 b35955 b35956 b35957 b35958 b35959 b35960 b35961 b35962 b35963 b35964 d35945 g50 f34243 g37 g29 g20 g13 d35271 d35279 d35113
        omega
      have d35965 : (x 7 2 && x 7 12).toNat = 0 := by
        have r35966 := hand1 (x 7 2) (x 7 12)
        have b35967 := hb (x 7 2)
        have b35968 := hb (x 7 2 && x 7 12)
        clear * - r35966 b35967 b35968 d35949
        omega
      have d35969 : (x 4 5).toNat = 1 := by
        have r35970 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b35971 := hb (x 4 5)
        have b35972 := hb (x 9 10)
        have b35973 := hb (x 8 1 && x 8 11)
        have b35974 := hb (x 7 2 && x 7 12)
        have b35975 := hb (x 6 3 && x 6 13)
        have b35976 := hb (x 5 4 && x 5 14)
        clear * - r35970 b35971 b35972 b35973 b35974 b35975 b35976 d35835 d35867 d35965 d35559 d35774
        omega
      have d35977 : (x 9 8).toNat = 0 := by
        have r35978 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35979 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e35980 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e35981 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e35982 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e35983 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e35984 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b35985 := hb (x 2 7)
        have b35986 := hb (x 3 6)
        have b35987 := hb (x 4 5)
        have b35988 := hb (x 5 4)
        have b35989 := hb (x 6 11)
        have b35990 := hb (x 7 10)
        have b35991 := hb (x 8 9)
        have b35992 := hb (x 9 8)
        clear * - r35978 e35979 e35980 e35981 e35982 e35983 e35984 b35985 b35986 b35987 b35988 b35989 b35990 b35991 b35992 d35969 g50 f34243
        omega
      have d35993 : (x 8 9).toNat = 0 := by
        have r35994 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e35995 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e35996 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e35997 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e35998 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e35999 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e36000 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b36001 := hb (x 2 7)
        have b36002 := hb (x 3 6)
        have b36003 := hb (x 4 5)
        have b36004 := hb (x 5 4)
        have b36005 := hb (x 6 11)
        have b36006 := hb (x 7 10)
        have b36007 := hb (x 8 9)
        have b36008 := hb (x 9 8)
        clear * - r35994 e35995 e35996 e35997 e35998 e35999 e36000 b36001 b36002 b36003 b36004 b36005 b36006 b36007 b36008 d35977 d35969 g50 f34243
        omega
      have d36009 : (x 7 10).toNat = 0 := by
        have r36010 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36011 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e36012 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e36013 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e36014 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e36015 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e36016 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b36017 := hb (x 2 7)
        have b36018 := hb (x 3 6)
        have b36019 := hb (x 4 5)
        have b36020 := hb (x 5 4)
        have b36021 := hb (x 6 11)
        have b36022 := hb (x 7 10)
        have b36023 := hb (x 8 9)
        have b36024 := hb (x 9 8)
        clear * - r36010 e36011 e36012 e36013 e36014 e36015 e36016 b36017 b36018 b36019 b36020 b36021 b36022 b36023 b36024 d35977 d35993 d35969 g50 f34243
        omega
      have d36025 : (x 6 11).toNat = 0 := by
        have r36026 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36027 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e36028 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e36029 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e36030 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e36031 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e36032 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b36033 := hb (x 2 7)
        have b36034 := hb (x 3 6)
        have b36035 := hb (x 4 5)
        have b36036 := hb (x 5 4)
        have b36037 := hb (x 6 11)
        have b36038 := hb (x 7 10)
        have b36039 := hb (x 8 9)
        have b36040 := hb (x 9 8)
        clear * - r36026 e36027 e36028 e36029 e36030 e36031 e36032 b36033 b36034 b36035 b36036 b36037 b36038 b36039 b36040 d35977 d35993 d36009 d35969 g50 f34243
        omega
      have d36041 : (x 5 4).toNat = 0 := by
        have r36042 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e36043 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e36044 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e36045 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e36046 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e36047 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e36048 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b36049 := hb (x 2 7)
        have b36050 := hb (x 3 6)
        have b36051 := hb (x 4 5)
        have b36052 := hb (x 5 4)
        have b36053 := hb (x 6 11)
        have b36054 := hb (x 7 10)
        have b36055 := hb (x 8 9)
        have b36056 := hb (x 9 8)
        clear * - r36042 e36043 e36044 e36045 e36046 e36047 e36048 b36049 b36050 b36051 b36052 b36053 b36054 b36055 b36056 d35977 d35993 d36009 d36025 d35969 g50 f34243
        omega
      have r36057 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b36058 := hb (x (-5) 14)
      have b36059 := hb (x (-4) 13)
      have b36060 := hb (x (-3) 12)
      have b36061 := hb (x (-2) 11)
      have b36062 := hb (x (-1) 10)
      have b36063 := hb (x 0 9)
      have b36064 := hb (x 1 8)
      have b36065 := hb (x 2 7)
      have b36066 := hb (x 3 6)
      have b36067 := hb (x 4 5)
      have b36068 := hb (x 5 4)
      have b36069 := hb (x 6 3)
      have b36070 := hb (x 7 2)
      have b36071 := hb (x 8 1)
      linarith only [r36057, b36058, b36059, b36060, b36061, b36062, b36063, b36064, b36065, b36066, b36067, b36068, b36069, b36070, b36071, d35945, d35949, d36041, d35969, g50, f34243, g37, g29, g20, g13, d35271, d35279, d35113]
  · have f36072 : (x 2 7).toNat = 1 := by rw [h34242]; rfl
    have d36073 : (x 9 8).toNat = 0 := by
      have r36074 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36075 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e36076 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e36077 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e36078 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e36079 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e36080 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b36081 := hb (x 2 7)
      have b36082 := hb (x 3 6)
      have b36083 := hb (x 4 5)
      have b36084 := hb (x 5 4)
      have b36085 := hb (x 6 11)
      have b36086 := hb (x 7 10)
      have b36087 := hb (x 8 9)
      have b36088 := hb (x 9 8)
      clear * - r36074 e36075 e36076 e36077 e36078 e36079 e36080 b36081 b36082 b36083 b36084 b36085 b36086 b36087 b36088 g50 f36072
      omega
    have d36089 : (x 8 9).toNat = 0 := by
      have r36090 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36091 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e36092 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e36093 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e36094 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e36095 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e36096 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b36097 := hb (x 2 7)
      have b36098 := hb (x 3 6)
      have b36099 := hb (x 4 5)
      have b36100 := hb (x 5 4)
      have b36101 := hb (x 6 11)
      have b36102 := hb (x 7 10)
      have b36103 := hb (x 8 9)
      have b36104 := hb (x 9 8)
      clear * - r36090 e36091 e36092 e36093 e36094 e36095 e36096 b36097 b36098 b36099 b36100 b36101 b36102 b36103 b36104 d36073 g50 f36072
      omega
    have d36105 : (x 7 10).toNat = 0 := by
      have r36106 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36107 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e36108 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e36109 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e36110 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e36111 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e36112 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b36113 := hb (x 2 7)
      have b36114 := hb (x 3 6)
      have b36115 := hb (x 4 5)
      have b36116 := hb (x 5 4)
      have b36117 := hb (x 6 11)
      have b36118 := hb (x 7 10)
      have b36119 := hb (x 8 9)
      have b36120 := hb (x 9 8)
      clear * - r36106 e36107 e36108 e36109 e36110 e36111 e36112 b36113 b36114 b36115 b36116 b36117 b36118 b36119 b36120 d36073 d36089 g50 f36072
      omega
    have d36121 : (x 7 1 && x 7 10).toNat = 0 := by
      have r36122 := hand2 (x 7 1) (x 7 10)
      have b36123 := hb (x 7 10)
      have b36124 := hb (x 7 1 && x 7 10)
      clear * - r36122 b36123 b36124 d36105
      omega
    have d36125 : (x 6 11).toNat = 0 := by
      have r36126 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36127 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e36128 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e36129 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e36130 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e36131 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e36132 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b36133 := hb (x 2 7)
      have b36134 := hb (x 3 6)
      have b36135 := hb (x 4 5)
      have b36136 := hb (x 5 4)
      have b36137 := hb (x 6 11)
      have b36138 := hb (x 7 10)
      have b36139 := hb (x 8 9)
      have b36140 := hb (x 9 8)
      clear * - r36126 e36127 e36128 e36129 e36130 e36131 e36132 b36133 b36134 b36135 b36136 b36137 b36138 b36139 b36140 d36073 d36089 d36105 g50 f36072
      omega
    have d36141 : (x 6 2 && x 6 11).toNat = 0 := by
      have r36142 := hand2 (x 6 2) (x 6 11)
      have b36143 := hb (x 6 11)
      have b36144 := hb (x 6 2 && x 6 11)
      clear * - r36142 b36143 b36144 d36125
      omega
    have d36145 : (x 5 4).toNat = 0 := by
      have r36146 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36147 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e36148 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e36149 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e36150 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e36151 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e36152 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b36153 := hb (x 2 7)
      have b36154 := hb (x 3 6)
      have b36155 := hb (x 4 5)
      have b36156 := hb (x 5 4)
      have b36157 := hb (x 6 11)
      have b36158 := hb (x 7 10)
      have b36159 := hb (x 8 9)
      have b36160 := hb (x 9 8)
      clear * - r36146 e36147 e36148 e36149 e36150 e36151 e36152 b36153 b36154 b36155 b36156 b36157 b36158 b36159 b36160 d36073 d36089 d36105 d36125 g50 f36072
      omega
    have d36161 : (x 5 4 && x 5 14).toNat = 0 := by
      have r36162 := hand1 (x 5 4) (x 5 14)
      have b36163 := hb (x 5 4)
      have b36164 := hb (x 5 4 && x 5 14)
      clear * - r36162 b36163 b36164 d36145
      omega
    have d36165 : (x 4 5).toNat = 0 := by
      have r36166 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e36167 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e36168 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e36169 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e36170 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e36171 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e36172 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b36173 := hb (x 2 7)
      have b36174 := hb (x 3 6)
      have b36175 := hb (x 4 5)
      have b36176 := hb (x 5 4)
      have b36177 := hb (x 6 11)
      have b36178 := hb (x 7 10)
      have b36179 := hb (x 8 9)
      have b36180 := hb (x 9 8)
      clear * - r36166 e36167 e36168 e36169 e36170 e36171 e36172 b36173 b36174 b36175 b36176 b36177 b36178 b36179 b36180 d36073 d36089 d36105 d36125 d36145 g50 f36072
      omega
    have r36181 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r36182 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r36183 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36184 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e36185 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e36186 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e36187 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e36188 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e36189 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have r36190 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e36191 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e36192 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e36193 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e36194 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e36195 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e36196 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have r36197 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r36198 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r36199 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r36200 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r36201 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r36202 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r36203 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
    have r36204 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have r36205 := hand2 (x 5 1) (x 5 6)
    have r36206 := hand2 (x 4 2) (x 4 7)
    have r36207 := hand1 (x (-3) 9) (x (-3) 14)
    have r36208 := hand1 (x 5 3) (x 5 12)
    have r36209 := hand1 (x 4 4) (x 4 13)
    have r36210 := hand2 (x (-4) 2) (x (-4) 12)
    have r36211 := hand2 (x (-5) 3) (x (-5) 13)
    have r36212 := hand1 (x (-6) 4) (x (-6) 14)
    have r36213 := hand2 (x 8 1) (x 8 11)
    have r36214 := hand1 (x 7 2) (x 7 12)
    have r36215 := hand1 (x 6 3) (x 6 13)
    have r36216 := hand2 (x (-5) 1) (x (-5) 14)
    have r36217 := hand1 (x 7 1) (x 7 14)
    linarith only [r36181, r36182, r36183, e36184, e36185, e36186, e36187, e36188, e36189, r36190, e36191, e36192, e36193, e36194, e36195, e36196, r36197, r36198, r36199, r36200, r36201, r36202, r36203, r36204, r36205, r36206, r36207, r36208, r36209, r36210, r36211, r36212, r36213, r36214, r36215, r36216, r36217, g8, g12, g13, g19, g20, g28, g29, f34233, g37, f34241, f36072, g50, d36165, d36145, d36089, g80, g81, g82, g83, d34101, g84, d36121, d36141, g130, g131, d36161]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100000 (x : ℤ → Fin 16 → Bool)
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
    (h34240 : x 2 6 = false)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a00001100001100000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125 g126 g127 g128 g129 g130 g131 g132 g133 g134 g135 h34091 h34232 h34234 h34240
