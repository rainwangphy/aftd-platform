import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00001000000

Topic: combinatorics   Node: 8ccbefa0ef48

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core: under the layer-free tight-cover constraints for k = 15 and 161 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00001000000_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-6) 11).toNat = 0)
    (g2 : (x (-5) 6).toNat = 0)
    (g3 : (x (-5) 10).toNat = 0)
    (g4 : (x (-5) 11).toNat = 0)
    (g5 : (x (-4) 3).toNat = 0)
    (g6 : (x (-4) 5).toNat = 0)
    (g7 : (x (-4) 9).toNat = 0)
    (g8 : (x (-4) 10).toNat = 0)
    (g9 : (x (-4) 11).toNat = 0)
    (g10 : (x (-4) 13).toNat = 0)
    (g11 : (x (-3) 2).toNat = 1)
    (g12 : (x (-3) 4).toNat = 1)
    (g13 : (x (-3) 12).toNat = 1)
    (g14 : (x (-3) 13).toNat = 1)
    (g15 : (x (-2) 3).toNat = 0)
    (g16 : (x (-2) 4).toNat = 0)
    (g17 : (x (-2) 6).toNat = 0)
    (g18 : (x (-2) 7).toNat = 0)
    (g19 : (x (-2) 10).toNat = 0)
    (g20 : (x (-2) 11).toNat = 0)
    (g21 : (x (-2) 12).toNat = 0)
    (g22 : (x (-1) 2).toNat = 0)
    (g23 : (x (-1) 3).toNat = 0)
    (g24 : (x (-1) 5).toNat = 0)
    (g25 : (x (-1) 6).toNat = 0)
    (g26 : (x (-1) 7).toNat = 0)
    (g27 : (x (-1) 9).toNat = 0)
    (g28 : (x (-1) 10).toNat = 0)
    (g29 : (x (-1) 11).toNat = 0)
    (g30 : (x 0 1).toNat = 1)
    (g31 : (x 0 2).toNat = 0)
    (g32 : (x 0 4).toNat = 0)
    (g33 : (x 0 6).toNat = 0)
    (g34 : (x 0 7).toNat = 0)
    (g35 : (x 0 8).toNat = 0)
    (g36 : (x 0 9).toNat = 0)
    (g37 : (x 0 10).toNat = 0)
    (g38 : (x 0 13).toNat = 1)
    (g39 : (x 0 14).toNat = 1)
    (g40 : (x 1 1).toNat = 0)
    (g41 : (x 1 3).toNat = 0)
    (g42 : (x 1 5).toNat = 0)
    (g43 : (x 1 6).toNat = 0)
    (g44 : (x 1 8).toNat = 0)
    (g45 : (x 1 9).toNat = 0)
    (g46 : (x 1 11).toNat = 0)
    (g47 : (x 1 12).toNat = 0)
    (g48 : (x 1 13).toNat = 0)
    (g49 : (x 1 14).toNat = 0)
    (g50 : (x 2 2).toNat = 1)
    (g51 : (x 2 11).toNat = 1)
    (g52 : (x 2 12).toNat = 1)
    (g53 : (x 2 13).toNat = 1)
    (g54 : (x 2 14).toNat = 1)
    (g55 : (x 3 2).toNat = 0)
    (g56 : (x 3 4).toNat = 0)
    (g57 : (x 3 5).toNat = 0)
    (g58 : (x 3 6).toNat = 0)
    (g59 : (x 3 10).toNat = 0)
    (g60 : (x 3 12).toNat = 0)
    (g61 : (x 3 13).toNat = 0)
    (g62 : (x 3 14).toNat = 0)
    (g63 : (x 4 4).toNat = 0)
    (g64 : (x 4 5).toNat = 0)
    (g65 : (x 4 9).toNat = 0)
    (g66 : (x 4 12).toNat = 0)
    (g67 : (x 5 4).toNat = 0)
    (g68 : (x 5 8).toNat = 0)
    (g69 : (x 5 12 && x 5 13).toNat = 0)
    (g70 : (x 4 13 && x 4 14).toNat = 0)
    (g71 : (x 5 5 && x 5 8).toNat = 0)
    (g72 : (x 4 6 && x 4 9).toNat = 0)
    (g73 : (x 3 7 && x 3 10).toNat = 0)
    (g74 : (x 1 9 && x 1 12).toNat = 0)
    (g75 : (x 0 10 && x 0 13).toNat = 0)
    (g76 : (x (-1) 11 && x (-1) 14).toNat = 0)
    (g77 : (x (-2) 2 && x (-2) 6).toNat = 0)
    (g78 : (x 5 4 && x 5 8).toNat = 0)
    (g79 : (x 4 5 && x 4 9).toNat = 0)
    (g80 : (x 3 6 && x 3 10).toNat = 0)
    (g81 : (x 1 8 && x 1 12).toNat = 0)
    (g82 : (x 0 9 && x 0 13).toNat = 0)
    (g83 : (x 1 9 && x 1 13).toNat = 0)
    (g84 : (x (-5) 1 && x (-5) 6).toNat = 0)
    (g85 : (x (-6) 2 && x (-6) 7).toNat = 0)
    (g86 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g87 : (x (-4) 3 && x (-4) 8).toNat = 0)
    (g88 : (x 0 1 && x 0 6).toNat = 0)
    (g89 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g90 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g91 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g92 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g93 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g94 : (x 5 3 && x 5 8).toNat = 0)
    (g95 : (x 4 4 && x 4 9).toNat = 0)
    (g96 : (x 3 5 && x 3 10).toNat = 0)
    (g97 : (x 1 7 && x 1 12).toNat = 0)
    (g98 : (x 0 8 && x 0 13).toNat = 0)
    (g99 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g100 : (x 5 4 && x 5 9).toNat = 0)
    (g101 : (x 4 5 && x 4 10).toNat = 0)
    (g102 : (x 3 6 && x 3 11).toNat = 0)
    (g103 : (x 1 8 && x 1 13).toNat = 0)
    (g104 : (x 0 9 && x 0 14).toNat = 0)
    (g105 : (x (-2) 1 && x (-2) 7).toNat = 0)
    (g106 : (x (-4) 3 && x (-4) 9).toNat = 0)
    (g107 : (x (-5) 4 && x (-5) 10).toNat = 0)
    (g108 : (x (-6) 5 && x (-6) 11).toNat = 0)
    (g109 : (x 0 1 && x 0 7).toNat = 0)
    (g110 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g111 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g112 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g113 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g114 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g115 : (x 4 4 && x 4 10).toNat = 0)
    (g116 : (x 3 5 && x 3 11).toNat = 0)
    (g117 : (x 1 7 && x 1 13).toNat = 0)
    (g118 : (x 0 8 && x 0 14).toNat = 0)
    (g119 : (x (-4) 2 && x (-4) 9).toNat = 0)
    (g120 : (x (-5) 3 && x (-5) 10).toNat = 0)
    (g121 : (x (-6) 4 && x (-6) 11).toNat = 0)
    (g122 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g123 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g124 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g125 : (x 0 1 && x 0 8).toNat = 0)
    (g126 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g127 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g128 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g129 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g130 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g131 : (x 3 4 && x 3 11).toNat = 0)
    (g132 : (x 1 6 && x 1 13).toNat = 0)
    (g133 : (x 0 7 && x 0 14).toNat = 0)
    (g134 : (x (-4) 1 && x (-4) 10).toNat = 0)
    (g135 : (x (-5) 2 && x (-5) 11).toNat = 0)
    (g136 : (x (-6) 3 && x (-6) 12).toNat = 0)
    (g137 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g138 : (x (-4) 3 && x (-4) 12).toNat = 0)
    (g139 : (x 5 3 && x 5 12).toNat = 0)
    (g140 : (x 4 4 && x 4 13).toNat = 0)
    (g141 : (x 3 5 && x 3 14).toNat = 0)
    (g142 : (x 5 4 && x 5 13).toNat = 0)
    (g143 : (x 4 5 && x 4 14).toNat = 0)
    (g144 : (x (-5) 1 && x (-5) 11).toNat = 0)
    (g145 : (x (-4) 1 && x (-4) 11).toNat = 0)
    (g146 : (x (-5) 2 && x (-5) 12).toNat = 0)
    (g147 : (x (-6) 3 && x (-6) 13).toNat = 0)
    (g148 : (x 1 1 && x 1 11).toNat = 0)
    (g149 : (x 0 2 && x 0 12).toNat = 0)
    (g150 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g151 : (x (-2) 4 && x (-2) 14).toNat = 0)
    (g152 : (x 4 2 && x 4 12).toNat = 0)
    (g153 : (x 3 3 && x 3 13).toNat = 0)
    (g154 : (x 5 2 && x 5 12).toNat = 0)
    (g155 : (x 4 3 && x 4 13).toNat = 0)
    (g156 : (x 3 4 && x 3 14).toNat = 0)
    (g157 : (x 4 4 && x 4 14).toNat = 0)
    (g158 : (x 5 1 && x 5 12).toNat = 0)
    (g159 : (x 4 2 && x 4 13).toNat = 0)
    (g160 : (x 3 3 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  cases h1542 : x 1 7
  · have f1543 : (x 1 7).toNat = 0 := by rw [h1542]; rfl
    cases h1544 : x (-1) 8
    · have f1545 : (x (-1) 8).toNat = 0 := by rw [h1544]; rfl
      cases h1546 : x (-1) 14
      · have f1547 : (x (-1) 14).toNat = 0 := by rw [h1546]; rfl
        have d1548 : (x (-2) 1).toNat = 1 := by
          have r1549 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b1550 := hb (x (-2) 1)
          have b1551 := hb (x (-1) 14)
          clear * - r1549 b1550 b1551 f1547
          omega
        cases h1552 : x 2 4
        · have f1553 : (x 2 4).toNat = 0 := by rw [h1552]; rfl
          have d1554 : (x 6 11).toNat = 1 := by
            have r1555 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1556 := hb (x 2 4)
            have b1557 := hb (x 6 11)
            have b1558 := hb (x 5 1 && x 5 12)
            have b1559 := hb (x 4 2 && x 4 13)
            have b1560 := hb (x 3 3 && x 3 14)
            clear * - r1555 b1556 b1557 b1558 b1559 b1560 g158 g159 g160 f1553
            omega
          have d1561 : (x 6 3).toNat = 1 := by
            have r1562 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
            have b1563 := hb (x 6 3)
            have b1564 := hb (x 6 11)
            clear * - r1562 b1563 b1564 d1554
            omega
          have d1565 : (x 9 12).toNat = 0 := by
            have r1566 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1567 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e1568 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b1569 := hb (x 6 3)
            have b1570 := hb (x 7 2)
            have b1571 := hb (x 8 13)
            have b1572 := hb (x 9 12)
            clear * - r1566 e1567 e1568 b1569 b1570 b1571 b1572 d1561
            omega
          have d1573 : (x 9 4).toNat = 0 := by
            have r1574 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
            have b1575 := hb (x 9 4)
            have b1576 := hb (x 9 12)
            clear * - r1574 b1575 b1576 d1565
            omega
          have d1577 : (x 8 13).toNat = 0 := by
            have r1578 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1579 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e1580 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b1581 := hb (x 6 3)
            have b1582 := hb (x 7 2)
            have b1583 := hb (x 8 13)
            have b1584 := hb (x 9 12)
            clear * - r1578 e1579 e1580 b1581 b1582 b1583 b1584 d1565 d1561
            omega
          have d1585 : (x 8 5).toNat = 0 := by
            have r1586 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
            have b1587 := hb (x 8 5)
            have b1588 := hb (x 8 13)
            clear * - r1586 b1587 b1588 d1577
            omega
          have d1589 : (x 7 2).toNat = 0 := by
            have r1590 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1591 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e1592 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b1593 := hb (x 6 3)
            have b1594 := hb (x 7 2)
            have b1595 := hb (x 8 13)
            have b1596 := hb (x 9 12)
            clear * - r1590 e1591 e1592 b1593 b1594 b1595 b1596 d1565 d1577 d1561
            omega
          have d1597 : (x 7 2 && x 7 7).toNat = 0 := by
            have r1598 := hand1 (x 7 2) (x 7 7)
            have b1599 := hb (x 7 2)
            have b1600 := hb (x 7 2 && x 7 7)
            clear * - r1598 b1599 b1600 d1589
            omega
          have d1601 : (x 7 2 && x 7 6).toNat = 0 := by
            have r1602 := hand1 (x 7 2) (x 7 6)
            have b1603 := hb (x 7 2)
            have b1604 := hb (x 7 2 && x 7 6)
            clear * - r1602 b1603 b1604 d1589
            omega
          have d1605 : (x 7 10).toNat = 0 := by
            have r1606 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
            have b1607 := hb (x 7 2)
            have b1608 := hb (x 7 10)
            clear * - r1606 b1607 b1608 d1589
            omega
          have d1609 : (x 9 8).toNat = 0 := by
            have r1610 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1611 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e1612 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e1613 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e1614 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e1615 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e1616 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b1617 := hb (x 2 7)
            have b1618 := hb (x 3 6)
            have b1619 := hb (x 4 5)
            have b1620 := hb (x 5 4)
            have b1621 := hb (x 6 11)
            have b1622 := hb (x 7 10)
            have b1623 := hb (x 8 9)
            have b1624 := hb (x 9 8)
            clear * - r1610 e1611 e1612 e1613 e1614 e1615 e1616 b1617 b1618 b1619 b1620 b1621 b1622 b1623 b1624 d1605 d1554 g67 g64 g58
            omega
          have d1625 : (x 8 9).toNat = 0 := by
            have r1626 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1627 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e1628 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e1629 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e1630 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e1631 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e1632 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b1633 := hb (x 2 7)
            have b1634 := hb (x 3 6)
            have b1635 := hb (x 4 5)
            have b1636 := hb (x 5 4)
            have b1637 := hb (x 6 11)
            have b1638 := hb (x 7 10)
            have b1639 := hb (x 8 9)
            have b1640 := hb (x 9 8)
            clear * - r1626 e1627 e1628 e1629 e1630 e1631 e1632 b1633 b1634 b1635 b1636 b1637 b1638 b1639 b1640 d1609 d1605 d1554 g67 g64 g58
            omega
          have d1641 : (x 2 7).toNat = 0 := by
            have r1642 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1643 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e1644 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e1645 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e1646 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e1647 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e1648 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b1649 := hb (x 2 7)
            have b1650 := hb (x 3 6)
            have b1651 := hb (x 4 5)
            have b1652 := hb (x 5 4)
            have b1653 := hb (x 6 11)
            have b1654 := hb (x 7 10)
            have b1655 := hb (x 8 9)
            have b1656 := hb (x 9 8)
            clear * - r1642 e1643 e1644 e1645 e1646 e1647 e1648 b1649 b1650 b1651 b1652 b1653 b1654 b1655 b1656 d1609 d1625 d1605 d1554 g67 g64 g58
            omega
          have d1657 : (x 2 7 && x 2 12).toNat = 0 := by
            have r1658 := hand1 (x 2 7) (x 2 12)
            have b1659 := hb (x 2 7)
            have b1660 := hb (x 2 7 && x 2 12)
            clear * - r1658 b1659 b1660 d1641
            omega
          have d1661 : (x 2 7 && x 2 11).toNat = 0 := by
            have r1662 := hand1 (x 2 7) (x 2 11)
            have b1663 := hb (x 2 7)
            have b1664 := hb (x 2 7 && x 2 11)
            clear * - r1662 b1663 b1664 d1641
            omega
          have d1665 : (x 6 3 && x 6 7).toNat = 1 := by
            have r1666 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1667 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
            have e1668 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
            have b1669 := hb (x (-2) 11)
            have b1670 := hb (x (-1) 10)
            have b1671 := hb (x 8 5)
            have b1672 := hb (x 9 4)
            have b1673 := hb (x 7 2 && x 7 6)
            have b1674 := hb (x 6 3 && x 6 7)
            have b1675 := hb (x 5 4 && x 5 8)
            have b1676 := hb (x 4 5 && x 4 9)
            have b1677 := hb (x 3 6 && x 3 10)
            have b1678 := hb (x 2 7 && x 2 11)
            have b1679 := hb (x 1 8 && x 1 12)
            have b1680 := hb (x 0 9 && x 0 13)
            clear * - r1666 e1667 e1668 b1669 b1670 b1671 b1672 b1673 b1674 b1675 b1676 b1677 b1678 b1679 b1680 d1573 d1585 d1601 g78 g79 g80 d1661 g81 g82 g28 g20
            omega
          have d1681 : (x 6 7).toNat = 1 := by
            have r1682 := hand2 (x 6 3) (x 6 7)
            have b1683 := hb (x 6 7)
            have b1684 := hb (x 6 3 && x 6 7)
            clear * - r1682 b1683 b1684 d1665
            omega
          have d1685 : (x 13 8).toNat = 0 := by
            have r1686 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1687 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e1688 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e1689 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e1690 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e1691 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e1692 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b1693 := hb (x 6 7)
            have b1694 := hb (x 7 6)
            have b1695 := hb (x 8 5)
            have b1696 := hb (x 9 4)
            have b1697 := hb (x 10 11)
            have b1698 := hb (x 11 10)
            have b1699 := hb (x 12 9)
            have b1700 := hb (x 13 8)
            clear * - r1686 e1687 e1688 e1689 e1690 e1691 e1692 b1693 b1694 b1695 b1696 b1697 b1698 b1699 b1700 d1573 d1585 d1681
            omega
          have d1701 : (x 12 9).toNat = 0 := by
            have r1702 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1703 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e1704 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e1705 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e1706 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e1707 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e1708 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b1709 := hb (x 6 7)
            have b1710 := hb (x 7 6)
            have b1711 := hb (x 8 5)
            have b1712 := hb (x 9 4)
            have b1713 := hb (x 10 11)
            have b1714 := hb (x 11 10)
            have b1715 := hb (x 12 9)
            have b1716 := hb (x 13 8)
            clear * - r1702 e1703 e1704 e1705 e1706 e1707 e1708 b1709 b1710 b1711 b1712 b1713 b1714 b1715 b1716 d1685 d1573 d1585 d1681
            omega
          have d1717 : (x 11 10).toNat = 0 := by
            have r1718 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1719 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e1720 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e1721 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e1722 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e1723 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e1724 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b1725 := hb (x 6 7)
            have b1726 := hb (x 7 6)
            have b1727 := hb (x 8 5)
            have b1728 := hb (x 9 4)
            have b1729 := hb (x 10 11)
            have b1730 := hb (x 11 10)
            have b1731 := hb (x 12 9)
            have b1732 := hb (x 13 8)
            clear * - r1718 e1719 e1720 e1721 e1722 e1723 e1724 b1725 b1726 b1727 b1728 b1729 b1730 b1731 b1732 d1685 d1701 d1573 d1585 d1681
            omega
          have d1733 : (x 10 11).toNat = 0 := by
            have r1734 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1735 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e1736 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e1737 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e1738 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e1739 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e1740 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b1741 := hb (x 6 7)
            have b1742 := hb (x 7 6)
            have b1743 := hb (x 8 5)
            have b1744 := hb (x 9 4)
            have b1745 := hb (x 10 11)
            have b1746 := hb (x 11 10)
            have b1747 := hb (x 12 9)
            have b1748 := hb (x 13 8)
            clear * - r1734 e1735 e1736 e1737 e1738 e1739 e1740 b1741 b1742 b1743 b1744 b1745 b1746 b1747 b1748 d1685 d1701 d1717 d1573 d1585 d1681
            omega
          have d1749 : (x 7 6).toNat = 0 := by
            have r1750 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1751 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e1752 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e1753 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e1754 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e1755 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e1756 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have b1757 := hb (x 6 7)
            have b1758 := hb (x 7 6)
            have b1759 := hb (x 8 5)
            have b1760 := hb (x 9 4)
            have b1761 := hb (x 10 11)
            have b1762 := hb (x 11 10)
            have b1763 := hb (x 12 9)
            have b1764 := hb (x 13 8)
            clear * - r1750 e1751 e1752 e1753 e1754 e1755 e1756 b1757 b1758 b1759 b1760 b1761 b1762 b1763 b1764 d1685 d1701 d1717 d1733 d1573 d1585 d1681
            omega
          have d1765 : (x 12 1).toNat = 0 := by
            have r1766 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1767 := hb (x (-1) 14)
            have b1768 := hb (x 0 13)
            have b1769 := hb (x 1 12)
            have b1770 := hb (x 2 11)
            have b1771 := hb (x 3 10)
            have b1772 := hb (x 4 9)
            have b1773 := hb (x 5 8)
            have b1774 := hb (x 6 7)
            have b1775 := hb (x 7 6)
            have b1776 := hb (x 8 5)
            have b1777 := hb (x 9 4)
            have b1778 := hb (x 10 3)
            have b1779 := hb (x 11 2)
            have b1780 := hb (x 12 1)
            clear * - r1766 b1767 b1768 b1769 b1770 b1771 b1772 b1773 b1774 b1775 b1776 b1777 b1778 b1779 b1780 d1573 d1585 d1749 d1681 g68 g65 g59 g51 g47 g38 f1547
            omega
          have d1781 : (x 12 1 && x 12 14).toNat = 0 := by
            have r1782 := hand1 (x 12 1) (x 12 14)
            have b1783 := hb (x 12 1)
            have b1784 := hb (x 12 1 && x 12 14)
            clear * - r1782 b1783 b1784 d1765
            omega
          have d1785 : (x 11 2).toNat = 0 := by
            have r1786 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1787 := hb (x (-1) 14)
            have b1788 := hb (x 0 13)
            have b1789 := hb (x 1 12)
            have b1790 := hb (x 2 11)
            have b1791 := hb (x 3 10)
            have b1792 := hb (x 4 9)
            have b1793 := hb (x 5 8)
            have b1794 := hb (x 6 7)
            have b1795 := hb (x 7 6)
            have b1796 := hb (x 8 5)
            have b1797 := hb (x 9 4)
            have b1798 := hb (x 10 3)
            have b1799 := hb (x 11 2)
            have b1800 := hb (x 12 1)
            clear * - r1786 b1787 b1788 b1789 b1790 b1791 b1792 b1793 b1794 b1795 b1796 b1797 b1798 b1799 b1800 d1765 d1573 d1585 d1749 d1681 g68 g65 g59 g51 g47 g38 f1547
            omega
          have d1801 : (x 13 13).toNat = 1 := by
            have r1802 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1803 := hb (x 11 2)
            have b1804 := hb (x 13 13)
            have b1805 := hb (x 12 1 && x 12 14)
            clear * - r1802 b1803 b1804 b1805 d1781 d1785
            omega
          have d1806 : (x 13 1).toNat = 1 := by
            have r1807 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
            have b1808 := hb (x 13 1)
            have b1809 := hb (x 13 13)
            clear * - r1807 b1808 b1809 d1801
            omega
          have d1810 : (x 12 2).toNat = 0 := by
            have r1811 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1812 := hb (x 0 14)
            have b1813 := hb (x 1 13)
            have b1814 := hb (x 2 12)
            have b1815 := hb (x 3 11)
            have b1816 := hb (x 4 10)
            have b1817 := hb (x 5 9)
            have b1818 := hb (x 6 8)
            have b1819 := hb (x 7 7)
            have b1820 := hb (x 8 6)
            have b1821 := hb (x 9 5)
            have b1822 := hb (x 10 4)
            have b1823 := hb (x 11 3)
            have b1824 := hb (x 12 2)
            have b1825 := hb (x 13 1)
            clear * - r1811 b1812 b1813 b1814 b1815 b1816 b1817 b1818 b1819 b1820 b1821 b1822 b1823 b1824 b1825 d1806 g52 g48 g39
            omega
          have d1826 : (x 11 3).toNat = 0 := by
            have r1827 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1828 := hb (x 0 14)
            have b1829 := hb (x 1 13)
            have b1830 := hb (x 2 12)
            have b1831 := hb (x 3 11)
            have b1832 := hb (x 4 10)
            have b1833 := hb (x 5 9)
            have b1834 := hb (x 6 8)
            have b1835 := hb (x 7 7)
            have b1836 := hb (x 8 6)
            have b1837 := hb (x 9 5)
            have b1838 := hb (x 10 4)
            have b1839 := hb (x 11 3)
            have b1840 := hb (x 12 2)
            have b1841 := hb (x 13 1)
            clear * - r1827 b1828 b1829 b1830 b1831 b1832 b1833 b1834 b1835 b1836 b1837 b1838 b1839 b1840 b1841 d1806 d1810 g52 g48 g39
            omega
          have d1842 : (x 10 4).toNat = 0 := by
            have r1843 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1844 := hb (x 0 14)
            have b1845 := hb (x 1 13)
            have b1846 := hb (x 2 12)
            have b1847 := hb (x 3 11)
            have b1848 := hb (x 4 10)
            have b1849 := hb (x 5 9)
            have b1850 := hb (x 6 8)
            have b1851 := hb (x 7 7)
            have b1852 := hb (x 8 6)
            have b1853 := hb (x 9 5)
            have b1854 := hb (x 10 4)
            have b1855 := hb (x 11 3)
            have b1856 := hb (x 12 2)
            have b1857 := hb (x 13 1)
            clear * - r1843 b1844 b1845 b1846 b1847 b1848 b1849 b1850 b1851 b1852 b1853 b1854 b1855 b1856 b1857 d1806 d1810 d1826 g52 g48 g39
            omega
          have d1858 : (x 9 5).toNat = 0 := by
            have r1859 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1860 := hb (x 0 14)
            have b1861 := hb (x 1 13)
            have b1862 := hb (x 2 12)
            have b1863 := hb (x 3 11)
            have b1864 := hb (x 4 10)
            have b1865 := hb (x 5 9)
            have b1866 := hb (x 6 8)
            have b1867 := hb (x 7 7)
            have b1868 := hb (x 8 6)
            have b1869 := hb (x 9 5)
            have b1870 := hb (x 10 4)
            have b1871 := hb (x 11 3)
            have b1872 := hb (x 12 2)
            have b1873 := hb (x 13 1)
            clear * - r1859 b1860 b1861 b1862 b1863 b1864 b1865 b1866 b1867 b1868 b1869 b1870 b1871 b1872 b1873 d1806 d1810 d1826 d1842 g52 g48 g39
            omega
          have d1874 : (x 8 6).toNat = 0 := by
            have r1875 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1876 := hb (x 0 14)
            have b1877 := hb (x 1 13)
            have b1878 := hb (x 2 12)
            have b1879 := hb (x 3 11)
            have b1880 := hb (x 4 10)
            have b1881 := hb (x 5 9)
            have b1882 := hb (x 6 8)
            have b1883 := hb (x 7 7)
            have b1884 := hb (x 8 6)
            have b1885 := hb (x 9 5)
            have b1886 := hb (x 10 4)
            have b1887 := hb (x 11 3)
            have b1888 := hb (x 12 2)
            have b1889 := hb (x 13 1)
            clear * - r1875 b1876 b1877 b1878 b1879 b1880 b1881 b1882 b1883 b1884 b1885 b1886 b1887 b1888 b1889 d1806 d1810 d1826 d1842 d1858 g52 g48 g39
            omega
          have d1890 : (x 8 1 && x 8 6).toNat = 0 := by
            have r1891 := hand2 (x 8 1) (x 8 6)
            have b1892 := hb (x 8 6)
            have b1893 := hb (x 8 1 && x 8 6)
            clear * - r1891 b1892 b1893 d1874
            omega
          have d1894 : (x 6 3 && x 6 8).toNat = 1 := by
            have r1895 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b1896 := hb (x (-1) 10)
            have b1897 := hb (x 9 5)
            have b1898 := hb (x 8 1 && x 8 6)
            have b1899 := hb (x 7 2 && x 7 7)
            have b1900 := hb (x 6 3 && x 6 8)
            have b1901 := hb (x 5 4 && x 5 9)
            have b1902 := hb (x 4 5 && x 4 10)
            have b1903 := hb (x 3 6 && x 3 11)
            have b1904 := hb (x 2 7 && x 2 12)
            have b1905 := hb (x 1 8 && x 1 13)
            have b1906 := hb (x 0 9 && x 0 14)
            clear * - r1895 b1896 b1897 b1898 b1899 b1900 b1901 b1902 b1903 b1904 b1905 b1906 d1858 d1890 d1597 g100 g101 g102 d1657 g103 g104 g28
            omega
          have d1907 : (x 6 8).toNat = 1 := by
            have r1908 := hand2 (x 6 3) (x 6 8)
            have b1909 := hb (x 6 8)
            have b1910 := hb (x 6 3 && x 6 8)
            clear * - r1908 b1909 b1910 d1894
            omega
          have d1911 : (x 5 9).toNat = 0 := by
            have r1912 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1913 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e1914 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e1915 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e1916 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e1917 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e1918 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b1919 := hb (x (-1) 7)
            have b1920 := hb (x 0 6)
            have b1921 := hb (x 1 5)
            have b1922 := hb (x 2 4)
            have b1923 := hb (x 3 11)
            have b1924 := hb (x 4 10)
            have b1925 := hb (x 5 9)
            have b1926 := hb (x 6 8)
            clear * - r1912 e1913 e1914 e1915 e1916 e1917 e1918 b1919 b1920 b1921 b1922 b1923 b1924 b1925 b1926 d1907 f1553 g42 g33 g26
            omega
          have d1927 : (x 4 10).toNat = 0 := by
            have r1928 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1929 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e1930 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e1931 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e1932 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e1933 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e1934 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b1935 := hb (x (-1) 7)
            have b1936 := hb (x 0 6)
            have b1937 := hb (x 1 5)
            have b1938 := hb (x 2 4)
            have b1939 := hb (x 3 11)
            have b1940 := hb (x 4 10)
            have b1941 := hb (x 5 9)
            have b1942 := hb (x 6 8)
            clear * - r1928 e1929 e1930 e1931 e1932 e1933 e1934 b1935 b1936 b1937 b1938 b1939 b1940 b1941 b1942 d1907 d1911 f1553 g42 g33 g26
            omega
          have d1943 : (x 3 11).toNat = 0 := by
            have r1944 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1945 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e1946 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e1947 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e1948 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e1949 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e1950 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b1951 := hb (x (-1) 7)
            have b1952 := hb (x 0 6)
            have b1953 := hb (x 1 5)
            have b1954 := hb (x 2 4)
            have b1955 := hb (x 3 11)
            have b1956 := hb (x 4 10)
            have b1957 := hb (x 5 9)
            have b1958 := hb (x 6 8)
            clear * - r1944 e1945 e1946 e1947 e1948 e1949 e1950 b1951 b1952 b1953 b1954 b1955 b1956 b1957 b1958 d1907 d1911 d1927 f1553 g42 g33 g26
            omega
          have r1959 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b1960 := hb (x 0 14)
          have b1961 := hb (x 1 13)
          have b1962 := hb (x 2 12)
          have b1963 := hb (x 3 11)
          have b1964 := hb (x 4 10)
          have b1965 := hb (x 5 9)
          have b1966 := hb (x 6 8)
          have b1967 := hb (x 7 7)
          have b1968 := hb (x 8 6)
          have b1969 := hb (x 9 5)
          have b1970 := hb (x 10 4)
          have b1971 := hb (x 11 3)
          have b1972 := hb (x 12 2)
          have b1973 := hb (x 13 1)
          linarith only [r1959, b1960, b1961, b1962, b1963, b1964, b1965, b1966, b1967, b1968, b1969, b1970, b1971, b1972, b1973, d1806, d1810, d1826, d1842, d1858, d1874, d1907, d1911, d1927, d1943, g52, g48, g39]
        · have f1974 : (x 2 4).toNat = 1 := by rw [h1552]; rfl
          have d1975 : (x 6 8).toNat = 0 := by
            have r1976 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e1977 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e1978 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e1979 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e1980 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e1981 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e1982 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b1983 := hb (x (-1) 7)
            have b1984 := hb (x 0 6)
            have b1985 := hb (x 1 5)
            have b1986 := hb (x 2 4)
            have b1987 := hb (x 3 11)
            have b1988 := hb (x 4 10)
            have b1989 := hb (x 5 9)
            have b1990 := hb (x 6 8)
            clear * - r1976 e1977 e1978 e1979 e1980 e1981 e1982 b1983 b1984 b1985 b1986 b1987 b1988 b1989 b1990 f1974 g42 g33 g26
            omega
          have d1991 : (x 6 1 && x 6 8).toNat = 0 := by
            have r1992 := hand2 (x 6 1) (x 6 8)
            have b1993 := hb (x 6 8)
            have b1994 := hb (x 6 1 && x 6 8)
            clear * - r1992 b1993 b1994 d1975
            omega
          have d1995 : (x 6 2 && x 6 8).toNat = 0 := by
            have r1996 := hand2 (x 6 2) (x 6 8)
            have b1997 := hb (x 6 8)
            have b1998 := hb (x 6 2 && x 6 8)
            clear * - r1996 b1997 b1998 d1975
            omega
          have d1999 : (x 6 3 && x 6 8).toNat = 0 := by
            have r2000 := hand2 (x 6 3) (x 6 8)
            have b2001 := hb (x 6 8)
            have b2002 := hb (x 6 3 && x 6 8)
            clear * - r2000 b2001 b2002 d1975
            omega
          have d2003 : (x 6 4 && x 6 8).toNat = 0 := by
            have r2004 := hand2 (x 6 4) (x 6 8)
            have b2005 := hb (x 6 8)
            have b2006 := hb (x 6 4 && x 6 8)
            clear * - r2004 b2005 b2006 d1975
            omega
          have d2007 : (x 5 9).toNat = 0 := by
            have r2008 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2009 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e2010 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e2011 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e2012 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e2013 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e2014 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b2015 := hb (x (-1) 7)
            have b2016 := hb (x 0 6)
            have b2017 := hb (x 1 5)
            have b2018 := hb (x 2 4)
            have b2019 := hb (x 3 11)
            have b2020 := hb (x 4 10)
            have b2021 := hb (x 5 9)
            have b2022 := hb (x 6 8)
            clear * - r2008 e2009 e2010 e2011 e2012 e2013 e2014 b2015 b2016 b2017 b2018 b2019 b2020 b2021 b2022 d1975 f1974 g42 g33 g26
            omega
          have d2023 : (x 5 2 && x 5 9).toNat = 0 := by
            have r2024 := hand2 (x 5 2) (x 5 9)
            have b2025 := hb (x 5 9)
            have b2026 := hb (x 5 2 && x 5 9)
            clear * - r2024 b2025 b2026 d2007
            omega
          have d2027 : (x 5 3 && x 5 9).toNat = 0 := by
            have r2028 := hand2 (x 5 3) (x 5 9)
            have b2029 := hb (x 5 9)
            have b2030 := hb (x 5 3 && x 5 9)
            clear * - r2028 b2029 b2030 d2007
            omega
          have d2031 : (x 5 5 && x 5 9).toNat = 0 := by
            have r2032 := hand2 (x 5 5) (x 5 9)
            have b2033 := hb (x 5 9)
            have b2034 := hb (x 5 5 && x 5 9)
            clear * - r2032 b2033 b2034 d2007
            omega
          have d2035 : (x 4 10).toNat = 0 := by
            have r2036 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2037 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e2038 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e2039 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e2040 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e2041 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e2042 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b2043 := hb (x (-1) 7)
            have b2044 := hb (x 0 6)
            have b2045 := hb (x 1 5)
            have b2046 := hb (x 2 4)
            have b2047 := hb (x 3 11)
            have b2048 := hb (x 4 10)
            have b2049 := hb (x 5 9)
            have b2050 := hb (x 6 8)
            clear * - r2036 e2037 e2038 e2039 e2040 e2041 e2042 b2043 b2044 b2045 b2046 b2047 b2048 b2049 b2050 d1975 d2007 f1974 g42 g33 g26
            omega
          have d2051 : (x 4 3 && x 4 10).toNat = 0 := by
            have r2052 := hand2 (x 4 3) (x 4 10)
            have b2053 := hb (x 4 10)
            have b2054 := hb (x 4 3 && x 4 10)
            clear * - r2052 b2053 b2054 d2035
            omega
          have d2055 : (x 4 6 && x 4 10).toNat = 0 := by
            have r2056 := hand2 (x 4 6) (x 4 10)
            have b2057 := hb (x 4 10)
            have b2058 := hb (x 4 6 && x 4 10)
            clear * - r2056 b2057 b2058 d2035
            omega
          have d2059 : (x 3 11).toNat = 0 := by
            have r2060 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e2061 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e2062 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e2063 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e2064 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e2065 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e2066 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b2067 := hb (x (-1) 7)
            have b2068 := hb (x 0 6)
            have b2069 := hb (x 1 5)
            have b2070 := hb (x 2 4)
            have b2071 := hb (x 3 11)
            have b2072 := hb (x 4 10)
            have b2073 := hb (x 5 9)
            have b2074 := hb (x 6 8)
            clear * - r2060 e2061 e2062 e2063 e2064 e2065 e2066 b2067 b2068 b2069 b2070 b2071 b2072 b2073 b2074 d1975 d2007 d2035 f1974 g42 g33 g26
            omega
          have d2075 : (x 3 7 && x 3 11).toNat = 0 := by
            have r2076 := hand2 (x 3 7) (x 3 11)
            have b2077 := hb (x 3 11)
            have b2078 := hb (x 3 7 && x 3 11)
            clear * - r2076 b2077 b2078 d2059
            omega
          cases h2079 : x 2 5
          · have f2080 : (x 2 5).toNat = 0 := by rw [h2079]; rfl
            have d2081 : (x 2 5 && x 2 12).toNat = 0 := by
              have r2082 := hand1 (x 2 5) (x 2 12)
              have b2083 := hb (x 2 5)
              have b2084 := hb (x 2 5 && x 2 12)
              clear * - r2082 b2083 b2084 f2080
              omega
            have d2085 : (x 7 7).toNat = 1 := by
              have r2086 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2087 := hb (x (-1) 8)
              have b2088 := hb (x 7 7)
              have b2089 := hb (x 6 1 && x 6 8)
              have b2090 := hb (x 5 2 && x 5 9)
              have b2091 := hb (x 4 3 && x 4 10)
              have b2092 := hb (x 3 4 && x 3 11)
              have b2093 := hb (x 2 5 && x 2 12)
              have b2094 := hb (x 1 6 && x 1 13)
              have b2095 := hb (x 0 7 && x 0 14)
              clear * - r2086 b2087 b2088 b2089 b2090 b2091 b2092 b2093 b2094 b2095 d1991 d2023 d2051 g131 d2081 g132 g133 f1545
              omega
            have d2096 : (x 14 8).toNat = 0 := by
              have r2097 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2098 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e2099 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e2100 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e2101 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e2102 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e2103 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b2104 := hb (x 7 7)
              have b2105 := hb (x 8 6)
              have b2106 := hb (x 9 5)
              have b2107 := hb (x 10 4)
              have b2108 := hb (x 11 11)
              have b2109 := hb (x 12 10)
              have b2110 := hb (x 13 9)
              have b2111 := hb (x 14 8)
              clear * - r2097 e2098 e2099 e2100 e2101 e2102 e2103 b2104 b2105 b2106 b2107 b2108 b2109 b2110 b2111 d2085
              omega
            have d2112 : (x 13 9).toNat = 0 := by
              have r2113 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2114 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e2115 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e2116 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e2117 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e2118 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e2119 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b2120 := hb (x 7 7)
              have b2121 := hb (x 8 6)
              have b2122 := hb (x 9 5)
              have b2123 := hb (x 10 4)
              have b2124 := hb (x 11 11)
              have b2125 := hb (x 12 10)
              have b2126 := hb (x 13 9)
              have b2127 := hb (x 14 8)
              clear * - r2113 e2114 e2115 e2116 e2117 e2118 e2119 b2120 b2121 b2122 b2123 b2124 b2125 b2126 b2127 d2096 d2085
              omega
            have d2128 : (x 12 10).toNat = 0 := by
              have r2129 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2130 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e2131 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e2132 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e2133 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e2134 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e2135 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b2136 := hb (x 7 7)
              have b2137 := hb (x 8 6)
              have b2138 := hb (x 9 5)
              have b2139 := hb (x 10 4)
              have b2140 := hb (x 11 11)
              have b2141 := hb (x 12 10)
              have b2142 := hb (x 13 9)
              have b2143 := hb (x 14 8)
              clear * - r2129 e2130 e2131 e2132 e2133 e2134 e2135 b2136 b2137 b2138 b2139 b2140 b2141 b2142 b2143 d2096 d2112 d2085
              omega
            have d2144 : (x 12 1 && x 12 10).toNat = 0 := by
              have r2145 := hand2 (x 12 1) (x 12 10)
              have b2146 := hb (x 12 10)
              have b2147 := hb (x 12 1 && x 12 10)
              clear * - r2145 b2146 b2147 d2128
              omega
            have d2148 : (x 11 11).toNat = 0 := by
              have r2149 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2150 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e2151 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e2152 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e2153 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e2154 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e2155 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b2156 := hb (x 7 7)
              have b2157 := hb (x 8 6)
              have b2158 := hb (x 9 5)
              have b2159 := hb (x 10 4)
              have b2160 := hb (x 11 11)
              have b2161 := hb (x 12 10)
              have b2162 := hb (x 13 9)
              have b2163 := hb (x 14 8)
              clear * - r2149 e2150 e2151 e2152 e2153 e2154 e2155 b2156 b2157 b2158 b2159 b2160 b2161 b2162 b2163 d2096 d2112 d2128 d2085
              omega
            have d2164 : (x 11 2 && x 11 11).toNat = 0 := by
              have r2165 := hand2 (x 11 2) (x 11 11)
              have b2166 := hb (x 11 11)
              have b2167 := hb (x 11 2 && x 11 11)
              clear * - r2165 b2166 b2167 d2148
              omega
            have d2168 : (x 10 4).toNat = 0 := by
              have r2169 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2170 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e2171 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e2172 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e2173 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e2174 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e2175 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b2176 := hb (x 7 7)
              have b2177 := hb (x 8 6)
              have b2178 := hb (x 9 5)
              have b2179 := hb (x 10 4)
              have b2180 := hb (x 11 11)
              have b2181 := hb (x 12 10)
              have b2182 := hb (x 13 9)
              have b2183 := hb (x 14 8)
              clear * - r2169 e2170 e2171 e2172 e2173 e2174 e2175 b2176 b2177 b2178 b2179 b2180 b2181 b2182 b2183 d2096 d2112 d2128 d2148 d2085
              omega
            have d2184 : (x 9 5).toNat = 0 := by
              have r2185 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2186 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e2187 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e2188 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e2189 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e2190 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e2191 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b2192 := hb (x 7 7)
              have b2193 := hb (x 8 6)
              have b2194 := hb (x 9 5)
              have b2195 := hb (x 10 4)
              have b2196 := hb (x 11 11)
              have b2197 := hb (x 12 10)
              have b2198 := hb (x 13 9)
              have b2199 := hb (x 14 8)
              clear * - r2185 e2186 e2187 e2188 e2189 e2190 e2191 b2192 b2193 b2194 b2195 b2196 b2197 b2198 b2199 d2096 d2112 d2128 d2148 d2168 d2085
              omega
            have d2200 : (x 8 6).toNat = 0 := by
              have r2201 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e2202 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e2203 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e2204 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e2205 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e2206 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e2207 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b2208 := hb (x 7 7)
              have b2209 := hb (x 8 6)
              have b2210 := hb (x 9 5)
              have b2211 := hb (x 10 4)
              have b2212 := hb (x 11 11)
              have b2213 := hb (x 12 10)
              have b2214 := hb (x 13 9)
              have b2215 := hb (x 14 8)
              clear * - r2201 e2202 e2203 e2204 e2205 e2206 e2207 b2208 b2209 b2210 b2211 b2212 b2213 b2214 b2215 d2096 d2112 d2128 d2148 d2168 d2184 d2085
              omega
            have d2216 : (x 13 1).toNat = 0 := by
              have r2217 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2218 := hb (x 0 14)
              have b2219 := hb (x 1 13)
              have b2220 := hb (x 2 12)
              have b2221 := hb (x 3 11)
              have b2222 := hb (x 4 10)
              have b2223 := hb (x 5 9)
              have b2224 := hb (x 6 8)
              have b2225 := hb (x 7 7)
              have b2226 := hb (x 8 6)
              have b2227 := hb (x 9 5)
              have b2228 := hb (x 10 4)
              have b2229 := hb (x 11 3)
              have b2230 := hb (x 12 2)
              have b2231 := hb (x 13 1)
              clear * - r2217 b2218 b2219 b2220 b2221 b2222 b2223 b2224 b2225 b2226 b2227 b2228 b2229 b2230 b2231 d2168 d2184 d2200 d2085 d1975 d2007 d2035 d2059 g52 g48 g39
              omega
            have d2232 : (x 13 13).toNat = 0 := by
              have r2233 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
              have b2234 := hb (x 13 1)
              have b2235 := hb (x 13 13)
              clear * - r2233 b2234 b2235 d2216
              omega
            have r2236 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r2237 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r2238 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r2239 := hand1 (x 10 3) (x 10 12)
            have r2240 := hand1 (x 9 4) (x 9 13)
            have r2241 := hand1 (x 8 5) (x 8 14)
            have r2242 := hand1 (x 12 1) (x 12 14)
            linarith only [r2236, r2237, r2238, r2239, r2240, r2241, r2242, f1547, g38, g47, g51, g59, g65, g68, d2112, d2232, d2144, d2164]
          · have f2265 : (x 2 5).toNat = 1 := by rw [h2079]; rfl
            cases h2266 : x 2 6
            · have f2267 : (x 2 6).toNat = 0 := by rw [h2266]; rfl
              have d2268 : (x 2 6 && x 2 12).toNat = 0 := by
                have r2269 := hand1 (x 2 6) (x 2 12)
                have b2270 := hb (x 2 6)
                have b2271 := hb (x 2 6 && x 2 12)
                clear * - r2269 b2270 b2271 f2267
                omega
              have d2272 : (x 2 6 && x 2 11).toNat = 0 := by
                have r2273 := hand1 (x 2 6) (x 2 11)
                have b2274 := hb (x 2 6)
                have b2275 := hb (x 2 6 && x 2 11)
                clear * - r2273 b2274 b2275 f2267
                omega
              have r2276 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r2277 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r2278 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r2279 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r2280 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r2281 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
              have r2282 := hand2 (x 7 1) (x 7 6)
              have r2283 := hand2 (x 6 2) (x 6 7)
              have r2284 := hand2 (x 7 1) (x 7 7)
              have r2285 := hand1 (x 12 1) (x 12 14)
              linarith only [r2276, r2277, r2278, r2279, r2280, r2281, r2282, r2283, r2284, r2285, g19, g27, f1547, g38, g39, g47, g48, g51, g52, g59, d2059, g65, d2035, g68, d2007, d1975, g94, g95, g96, d2272, g97, g98, g99, d1995, d2027, g115, g116, d2268, g117, g118]
            · have f2335 : (x 2 6).toNat = 1 := by rw [h2266]; rfl
              cases h2336 : x 2 7
              · have f2337 : (x 2 7).toNat = 0 := by rw [h2336]; rfl
                have d2338 : (x 2 7 && x 2 12).toNat = 0 := by
                  have r2339 := hand1 (x 2 7) (x 2 12)
                  have b2340 := hb (x 2 7)
                  have b2341 := hb (x 2 7 && x 2 12)
                  clear * - r2339 b2340 b2341 f2337
                  omega
                have d2342 : (x 2 7 && x 2 11).toNat = 0 := by
                  have r2343 := hand1 (x 2 7) (x 2 11)
                  have b2344 := hb (x 2 7)
                  have b2345 := hb (x 2 7 && x 2 11)
                  clear * - r2343 b2344 b2345 f2337
                  omega
                have r2346 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r2347 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r2348 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2349 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
                have e2350 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
                have r2351 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r2352 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r2353 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have r2354 := hand2 (x 7 2) (x 7 6)
                have r2355 := hand2 (x 6 3) (x 6 7)
                have r2356 := hand2 (x 8 1) (x 8 6)
                have r2357 := hand2 (x 7 2) (x 7 7)
                have r2358 := hand1 (x 12 1) (x 12 14)
                linarith only [r2346, r2347, r2348, e2349, e2350, r2351, r2352, r2353, r2354, r2355, r2356, r2357, r2358, g20, g28, f1547, g38, g39, g47, g48, g51, g52, g59, d2059, g65, d2035, g68, d2007, d1975, g78, g79, g80, d2342, g81, g82, d1999, g100, g101, g102, d2338, g103, g104]
              · have f2408 : (x 2 7).toNat = 1 := by rw [h2336]; rfl
                have d2409 : (x 9 8).toNat = 0 := by
                  have r2410 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e2411 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                  have e2412 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                  have e2413 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                  have e2414 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                  have e2415 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                  have e2416 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                  have b2417 := hb (x 2 7)
                  have b2418 := hb (x 3 6)
                  have b2419 := hb (x 4 5)
                  have b2420 := hb (x 5 4)
                  have b2421 := hb (x 6 11)
                  have b2422 := hb (x 7 10)
                  have b2423 := hb (x 8 9)
                  have b2424 := hb (x 9 8)
                  clear * - r2410 e2411 e2412 e2413 e2414 e2415 e2416 b2417 b2418 b2419 b2420 b2421 b2422 b2423 b2424 g67 g64 g58 f2408
                  omega
                have d2425 : (x 9 8 && x 9 9).toNat = 0 := by
                  have r2426 := hand1 (x 9 8) (x 9 9)
                  have b2427 := hb (x 9 8)
                  have b2428 := hb (x 9 8 && x 9 9)
                  clear * - r2426 b2427 b2428 d2409
                  omega
                have d2429 : (x 8 9).toNat = 0 := by
                  have r2430 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e2431 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                  have e2432 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                  have e2433 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                  have e2434 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                  have e2435 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                  have e2436 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                  have b2437 := hb (x 2 7)
                  have b2438 := hb (x 3 6)
                  have b2439 := hb (x 4 5)
                  have b2440 := hb (x 5 4)
                  have b2441 := hb (x 6 11)
                  have b2442 := hb (x 7 10)
                  have b2443 := hb (x 8 9)
                  have b2444 := hb (x 9 8)
                  clear * - r2430 e2431 e2432 e2433 e2434 e2435 e2436 b2437 b2438 b2439 b2440 b2441 b2442 b2443 b2444 d2409 g67 g64 g58 f2408
                  omega
                have d2445 : (x 8 9 && x 8 10).toNat = 0 := by
                  have r2446 := hand1 (x 8 9) (x 8 10)
                  have b2447 := hb (x 8 9)
                  have b2448 := hb (x 8 9 && x 8 10)
                  clear * - r2446 b2447 b2448 d2429
                  omega
                have d2449 : (x 7 10).toNat = 0 := by
                  have r2450 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e2451 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                  have e2452 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                  have e2453 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                  have e2454 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                  have e2455 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                  have e2456 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                  have b2457 := hb (x 2 7)
                  have b2458 := hb (x 3 6)
                  have b2459 := hb (x 4 5)
                  have b2460 := hb (x 5 4)
                  have b2461 := hb (x 6 11)
                  have b2462 := hb (x 7 10)
                  have b2463 := hb (x 8 9)
                  have b2464 := hb (x 9 8)
                  clear * - r2450 e2451 e2452 e2453 e2454 e2455 e2456 b2457 b2458 b2459 b2460 b2461 b2462 b2463 b2464 d2409 d2429 g67 g64 g58 f2408
                  omega
                have d2465 : (x 7 10 && x 7 11).toNat = 0 := by
                  have r2466 := hand1 (x 7 10) (x 7 11)
                  have b2467 := hb (x 7 10)
                  have b2468 := hb (x 7 10 && x 7 11)
                  clear * - r2466 b2467 b2468 d2449
                  omega
                have d2469 : (x 6 11).toNat = 0 := by
                  have r2470 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e2471 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                  have e2472 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                  have e2473 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                  have e2474 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                  have e2475 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                  have e2476 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                  have b2477 := hb (x 2 7)
                  have b2478 := hb (x 3 6)
                  have b2479 := hb (x 4 5)
                  have b2480 := hb (x 5 4)
                  have b2481 := hb (x 6 11)
                  have b2482 := hb (x 7 10)
                  have b2483 := hb (x 8 9)
                  have b2484 := hb (x 9 8)
                  clear * - r2470 e2471 e2472 e2473 e2474 e2475 e2476 b2477 b2478 b2479 b2480 b2481 b2482 b2483 b2484 d2409 d2429 d2449 g67 g64 g58 f2408
                  omega
                have d2485 : (x 6 11 && x 6 12).toNat = 0 := by
                  have r2486 := hand1 (x 6 11) (x 6 12)
                  have b2487 := hb (x 6 11)
                  have b2488 := hb (x 6 11 && x 6 12)
                  clear * - r2486 b2487 b2488 d2469
                  omega
                cases h2489 : x (-2) 8
                · have f2490 : (x (-2) 8).toNat = 0 := by rw [h2489]; rfl
                  cases h2491 : x 2 8
                  · have f2492 : (x 2 8).toNat = 0 := by rw [h2491]; rfl
                    have d2493 : (x 2 8 && x 2 12).toNat = 0 := by
                      have r2494 := hand1 (x 2 8) (x 2 12)
                      have b2495 := hb (x 2 8)
                      have b2496 := hb (x 2 8 && x 2 12)
                      clear * - r2494 b2495 b2496 f2492
                      omega
                    have d2497 : (x 2 8 && x 2 11).toNat = 0 := by
                      have r2498 := hand1 (x 2 8) (x 2 11)
                      have b2499 := hb (x 2 8)
                      have b2500 := hb (x 2 8 && x 2 11)
                      clear * - r2498 b2499 b2500 f2492
                      omega
                    have r2501 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r2502 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r2503 : 1 ≤ (x 10 3).toNat + (x 9 1 && x 9 4).toNat + (x 8 2 && x 8 5).toNat + (x 7 3 && x 7 6).toNat + (x 6 4 && x 6 7).toNat + (x 5 5 && x 5 8).toNat + (x 4 6 && x 4 9).toNat + (x 3 7 && x 3 10).toNat + (x 2 8 && x 2 11).toNat + (x 1 9 && x 1 12).toNat + (x 0 10 && x 0 13).toNat + (x (-1) 11 && x (-1) 14).toNat + (x (-2) 12).toNat := by have q := hcov3 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r2504 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e2505 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
                    have e2506 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
                    have r2507 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r2508 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                    have r2509 := hand2 (x 9 1) (x 9 4)
                    have r2510 := hand2 (x 8 2) (x 8 5)
                    have r2511 := hand2 (x 7 3) (x 7 6)
                    have r2512 := hand2 (x 6 4) (x 6 7)
                    have r2513 := hand2 (x 8 2) (x 8 6)
                    have r2514 := hand2 (x 7 3) (x 7 7)
                    have r2515 := hand1 (x 12 1) (x 12 14)
                    linarith only [r2501, r2502, r2503, r2504, e2505, e2506, r2507, r2508, r2509, r2510, r2511, r2512, r2513, r2514, r2515, g21, g29, f1547, g37, g38, g39, g47, g48, g51, g52, g59, d2059, g65, d2035, g68, d2007, d1975, g71, g72, g73, d2497, g74, g75, g76, d2003, d2031, d2055, d2075, d2493, g83]
                  · have f2568 : (x 2 8).toNat = 1 := by rw [h2491]; rfl
                    have d2569 : (x (-3) 5).toNat = 0 := by
                      have r2570 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e2571 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                      have e2572 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                      have e2573 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                      have e2574 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                      have e2575 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                      have e2576 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                      have b2577 := hb (x (-5) 7)
                      have b2578 := hb (x (-4) 6)
                      have b2579 := hb (x (-3) 5)
                      have b2580 := hb (x (-2) 4)
                      have b2581 := hb (x (-1) 11)
                      have b2582 := hb (x 0 10)
                      have b2583 := hb (x 1 9)
                      have b2584 := hb (x 2 8)
                      clear * - r2570 e2571 e2572 e2573 e2574 e2575 e2576 b2577 b2578 b2579 b2580 b2581 b2582 b2583 b2584 f2568 g45 g37 g29 g16
                      omega
                    have d2585 : (x 2 10).toNat = 1 := by
                      have r2586 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b2587 := hb (x (-3) 5)
                      have b2588 := hb (x 2 10)
                      have b2589 := hb (x 1 1 && x 1 11)
                      have b2590 := hb (x 0 2 && x 0 12)
                      have b2591 := hb (x (-1) 3 && x (-1) 13)
                      have b2592 := hb (x (-2) 4 && x (-2) 14)
                      clear * - r2586 b2587 b2588 b2589 b2590 b2591 b2592 g148 g149 g150 g151 d2569
                      omega
                    have d2593 : (x 4 8).toNat = 0 := by
                      have r2594 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e2595 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e2596 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e2597 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e2598 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e2599 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e2600 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have b2601 := hb (x (-3) 7)
                      have b2602 := hb (x (-2) 6)
                      have b2603 := hb (x (-1) 5)
                      have b2604 := hb (x 0 4)
                      have b2605 := hb (x 1 11)
                      have b2606 := hb (x 2 10)
                      have b2607 := hb (x 3 9)
                      have b2608 := hb (x 4 8)
                      clear * - r2594 e2595 e2596 e2597 e2598 e2599 e2600 b2601 b2602 b2603 b2604 b2605 b2606 b2607 b2608 d2585 g46 g32 g24 g17
                      omega
                    have d2609 : (x 3 9).toNat = 0 := by
                      have r2610 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e2611 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e2612 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e2613 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e2614 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e2615 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e2616 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have b2617 := hb (x (-3) 7)
                      have b2618 := hb (x (-2) 6)
                      have b2619 := hb (x (-1) 5)
                      have b2620 := hb (x 0 4)
                      have b2621 := hb (x 1 11)
                      have b2622 := hb (x 2 10)
                      have b2623 := hb (x 3 9)
                      have b2624 := hb (x 4 8)
                      clear * - r2610 e2611 e2612 e2613 e2614 e2615 e2616 b2617 b2618 b2619 b2620 b2621 b2622 b2623 b2624 d2593 d2585 g46 g32 g24 g17
                      omega
                    have d2625 : (x (-3) 7).toNat = 0 := by
                      have r2626 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e2627 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e2628 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e2629 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e2630 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e2631 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e2632 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have b2633 := hb (x (-3) 7)
                      have b2634 := hb (x (-2) 6)
                      have b2635 := hb (x (-1) 5)
                      have b2636 := hb (x 0 4)
                      have b2637 := hb (x 1 11)
                      have b2638 := hb (x 2 10)
                      have b2639 := hb (x 3 9)
                      have b2640 := hb (x 4 8)
                      clear * - r2626 e2627 e2628 e2629 e2630 e2631 e2632 b2633 b2634 b2635 b2636 b2637 b2638 b2639 b2640 d2593 d2609 d2585 g46 g32 g24 g17
                      omega
                    have d2641 : (x (-3) 2 && x (-3) 7).toNat = 0 := by
                      have r2642 := hand2 (x (-3) 2) (x (-3) 7)
                      have b2643 := hb (x (-3) 7)
                      have b2644 := hb (x (-3) 2 && x (-3) 7)
                      clear * - r2642 b2643 b2644 d2625
                      omega
                    have d2645 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
                      have r2646 := hand2 (x (-3) 3) (x (-3) 7)
                      have b2647 := hb (x (-3) 7)
                      have b2648 := hb (x (-3) 3 && x (-3) 7)
                      clear * - r2646 b2647 b2648 d2625
                      omega
                    have d2649 : (x (-4) 6).toNat = 0 := by
                      have r2650 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e2651 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                      have e2652 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                      have e2653 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                      have e2654 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                      have e2655 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                      have e2656 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                      have b2657 := hb (x (-5) 7)
                      have b2658 := hb (x (-4) 6)
                      have b2659 := hb (x (-3) 5)
                      have b2660 := hb (x (-2) 4)
                      have b2661 := hb (x (-1) 11)
                      have b2662 := hb (x 0 10)
                      have b2663 := hb (x 1 9)
                      have b2664 := hb (x 2 8)
                      clear * - r2650 e2651 e2652 e2653 e2654 e2655 e2656 b2657 b2658 b2659 b2660 b2661 b2662 b2663 b2664 f2568 g45 g37 g29 g16 d2569
                      omega
                    have d2665 : (x (-5) 7).toNat = 0 := by
                      have r2666 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e2667 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                      have e2668 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                      have e2669 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                      have e2670 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                      have e2671 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                      have e2672 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                      have b2673 := hb (x (-5) 7)
                      have b2674 := hb (x (-4) 6)
                      have b2675 := hb (x (-3) 5)
                      have b2676 := hb (x (-2) 4)
                      have b2677 := hb (x (-1) 11)
                      have b2678 := hb (x 0 10)
                      have b2679 := hb (x 1 9)
                      have b2680 := hb (x 2 8)
                      clear * - r2666 e2667 e2668 e2669 e2670 e2671 e2672 b2673 b2674 b2675 b2676 b2677 b2678 b2679 b2680 f2568 g45 g37 g29 g16 d2569 d2649
                      omega
                    cases h2681 : x (-2) 9
                    · have f2682 : (x (-2) 9).toNat = 0 := by rw [h2681]; rfl
                      cases h2683 : x 3 1
                      · have f2684 : (x 3 1).toNat = 0 := by rw [h2683]; rfl
                        have d2685 : (x 4 14).toNat = 1 := by
                          have r2686 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b2687 := hb (x 3 1)
                          have b2688 := hb (x 4 14)
                          clear * - r2686 b2687 b2688 f2684
                          omega
                        have r2689 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2690 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2691 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2692 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2693 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2694 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2695 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                        have e2696 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                        have e2697 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                        have e2698 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                        have e2699 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                        have e2700 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                        have r2701 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2702 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                        have e2703 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                        have e2704 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                        have e2705 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                        have e2706 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                        have e2707 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                        have r2708 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2709 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
                        have e2710 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
                        have r2711 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2712 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
                        have e2713 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
                        have r2714 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2715 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                        have e2716 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                        have r2717 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2718 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                        have e2719 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                        have r2720 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2721 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                        have e2722 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                        have r2723 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2724 : 1 ≤ (x 17 1).toNat + (x 16 1 && x 16 2).toNat + (x 15 2 && x 15 3).toNat + (x 14 3 && x 14 4).toNat + (x 13 4 && x 13 5).toNat + (x 12 5 && x 12 6).toNat + (x 11 6 && x 11 7).toNat + (x 10 7 && x 10 8).toNat + (x 9 8 && x 9 9).toNat + (x 8 9 && x 8 10).toNat + (x 7 10 && x 7 11).toNat + (x 6 11 && x 6 12).toNat + (x 5 12 && x 5 13).toNat + (x 4 13 && x 4 14).toNat + (x 3 14).toNat := by have q := hcov1 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2725 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2726 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2727 : 1 ≤ (x (-10) 10).toNat + (x (-11) 1 && x (-11) 11).toNat + (x (-12) 2 && x (-12) 12).toNat + (x (-13) 3 && x (-13) 13).toNat + (x (-14) 4 && x (-14) 14).toNat + (x (-15) 5).toNat := by have q := hcov10 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2728 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2729 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2730 : 1 ≤ (x (-6) 11).toNat + (x (-7) 1 && x (-7) 12).toNat + (x (-8) 2 && x (-8) 13).toNat + (x (-9) 3 && x (-9) 14).toNat + (x (-10) 4).toNat := by have q := hcov11 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2731 : 1 ≤ (x (-14) 13).toNat + (x (-15) 1 && x (-15) 14).toNat + (x (-16) 2).toNat := by have q := hcov13 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2732 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2733 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2734 : (x (-15) 5).toNat ≤ (x (-15) 13).toNat := himp _ _ (hp5 (-15))
                        have r2735 : (x (-14) 4).toNat ≤ (x (-14) 12).toNat := himp _ _ (hp4 (-14))
                        have r2736 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
                        have r2737 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
                        have r2738 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
                        have r2739 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                        have r2740 := hand2 (x 16 1) (x 16 2)
                        have r2741 := hand2 (x 15 2) (x 15 3)
                        have r2742 := hand2 (x 14 3) (x 14 4)
                        have r2743 := hand2 (x 13 4) (x 13 5)
                        have r2744 := hand2 (x 12 5) (x 12 6)
                        have r2745 := hand2 (x 11 6) (x 11 7)
                        have r2746 := hand2 (x 10 7) (x 10 8)
                        have r2747 := hand1 (x (-5) 4) (x (-5) 9)
                        have r2748 := hand1 (x (-6) 5) (x (-6) 10)
                        have r2749 := hand1 (x (-7) 6) (x (-7) 11)
                        have r2750 := hand1 (x (-8) 7) (x (-8) 12)
                        have r2751 := hand1 (x (-9) 8) (x (-9) 13)
                        have r2752 := hand1 (x (-10) 9) (x (-10) 14)
                        have r2753 := hand2 (x 8 1) (x 8 10)
                        have r2754 := hand1 (x 7 2) (x 7 11)
                        have r2755 := hand1 (x 6 3) (x 6 12)
                        have r2756 := hand2 (x (-11) 1) (x (-11) 11)
                        have r2757 := hand1 (x (-12) 2) (x (-12) 12)
                        have r2758 := hand1 (x (-13) 3) (x (-13) 13)
                        have r2759 := hand1 (x (-14) 4) (x (-14) 14)
                        have r2760 := hand2 (x (-6) 2) (x (-6) 12)
                        have r2761 := hand2 (x (-7) 3) (x (-7) 13)
                        have r2762 := hand1 (x (-8) 4) (x (-8) 14)
                        have r2763 := hand2 (x 7 1) (x 7 11)
                        have r2764 := hand2 (x 6 2) (x 6 12)
                        have r2765 := hand2 (x 5 3) (x 5 13)
                        have r2766 := hand1 (x (-7) 1) (x (-7) 12)
                        have r2767 := hand1 (x (-8) 2) (x (-8) 13)
                        have r2768 := hand1 (x (-9) 3) (x (-9) 14)
                        have r2769 := hand2 (x (-15) 1) (x (-15) 14)
                        have r2770 := hand2 (x (-5) 1) (x (-5) 14)
                        have r2771 := hand1 (x 8 1) (x 8 14)
                        have b2786 := hb (x (-12) 14)
                        have b2799 := hb (x (-10) 14)
                        linarith only [r2689, r2690, r2691, r2692, r2693, r2694, e2695, e2696, e2697, e2698, e2699, e2700, r2701, e2702, e2703, e2704, e2705, e2706, e2707, r2708, e2709, e2710, r2711, e2712, e2713, r2714, e2715, e2716, r2717, e2718, e2719, r2720, e2721, e2722, r2723, r2724, r2725, r2726, r2727, r2728, r2729, r2730, r2731, r2732, r2733, r2734, r2735, r2736, r2737, r2738, r2739, r2740, r2741, r2742, r2743, r2744, r2745, r2746, r2747, r2748, r2749, r2750, r2751, r2752, r2753, r2754, r2755, r2756, r2757, r2758, r2759, r2760, r2761, r2762, r2763, r2764, r2765, r2766, r2767, r2768, r2769, r2770, r2771, b2786, b2799, g1, d2665, g5, d2649, g8, g10, g11, d2569, d2625, g13, d1548, g16, g17, g20, g23, g24, g28, g31, g32, g36, g40, g41, g44, g50, f2408, f2684, g57, g58, g62, g64, d2685, g67, d2425, d2445, d2465, d2485, g69, g70, g86, d2641, g87, g142, g143, g144, g157]
                      · have f2922 : (x 3 1).toNat = 1 := by rw [h2683]; rfl
                        have d2923 : (x 4 14).toNat = 0 := by
                          have r2924 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b2925 := hb (x 3 1)
                          have b2926 := hb (x 4 14)
                          clear * - r2924 b2925 b2926 f2922
                          omega
                        have d2927 : (x 4 1 && x 4 14).toNat = 0 := by
                          have r2928 := hand2 (x 4 1) (x 4 14)
                          have b2929 := hb (x 4 14)
                          have b2930 := hb (x 4 1 && x 4 14)
                          clear * - r2928 b2929 b2930 d2923
                          omega
                        have d2931 : (x 4 6).toNat = 0 := by
                          have r2932 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
                          have b2933 := hb (x 4 6)
                          have b2934 := hb (x 4 14)
                          clear * - r2932 b2933 b2934 d2923
                          omega
                        have d2935 : (x 4 2).toNat = 0 := by
                          have r2936 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                          have b2937 := hb (x 4 2)
                          have b2938 := hb (x 4 14)
                          clear * - r2936 b2937 b2938 d2923
                          omega
                        have d2939 : (x 5 13).toNat = 1 := by
                          have r2940 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b2941 := hb (x 3 2)
                          have b2942 := hb (x 5 13)
                          have b2943 := hb (x 4 1 && x 4 14)
                          clear * - r2940 b2941 b2942 b2943 d2927 g55
                          omega
                        have d2944 : (x 5 1).toNat = 1 := by
                          have r2945 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                          have b2946 := hb (x 5 1)
                          have b2947 := hb (x 5 13)
                          clear * - r2945 b2946 b2947 d2939
                          omega
                        have d2948 : (x 6 14).toNat = 0 := by
                          have r2949 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b2950 := hb (x 5 1)
                          have b2951 := hb (x 6 14)
                          clear * - r2949 b2950 b2951 d2944
                          omega
                        have d2952 : (x 6 2).toNat = 0 := by
                          have r2953 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                          have b2954 := hb (x 6 2)
                          have b2955 := hb (x 6 14)
                          clear * - r2953 b2954 b2955 d2948
                          omega
                        have d2956 : (x 6 2 && x 6 12).toNat = 0 := by
                          have r2957 := hand1 (x 6 2) (x 6 12)
                          have b2958 := hb (x 6 2)
                          have b2959 := hb (x 6 2 && x 6 12)
                          clear * - r2957 b2958 b2959 d2952
                          omega
                        have d2960 : (x 6 12).toNat = 0 := by
                          have r2961 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e2962 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                          have e2963 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                          have b2964 := hb (x 3 3)
                          have b2965 := hb (x 4 2)
                          have b2966 := hb (x 5 13)
                          have b2967 := hb (x 6 12)
                          clear * - r2961 e2962 e2963 b2964 b2965 b2966 b2967 d2939 d2935
                          omega
                        have d2968 : (x 6 4).toNat = 0 := by
                          have r2969 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                          have b2970 := hb (x 6 4)
                          have b2971 := hb (x 6 12)
                          clear * - r2969 b2970 b2971 d2960
                          omega
                        have r2972 : (x (-5) 1).toNat + (x (-6) 2).toNat + (x (-7) 3).toNat + (x (-8) 4).toNat + (x (-9) 5).toNat + (x (-10) 6).toNat + (x (-11) 7).toNat + (x (-12) 8).toNat + (x (-13) 9).toNat + (x (-14) 10).toNat + (x (-15) 11).toNat + (x (-16) 12).toNat + (x (-17) 13).toNat + (x (-18) 14).toNat = 3 := by have q := hcount (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2973 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2974 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2975 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2976 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2977 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2978 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2979 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
                        have e2980 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
                        have r2981 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2982 : 1 ≤ (x (-4) 5).toNat + (x (-5) 1 && x (-5) 6).toNat + (x (-6) 2 && x (-6) 7).toNat + (x (-7) 3 && x (-7) 8).toNat + (x (-8) 4 && x (-8) 9).toNat + (x (-9) 5 && x (-9) 10).toNat + (x (-10) 6 && x (-10) 11).toNat + (x (-11) 7 && x (-11) 12).toNat + (x (-12) 8 && x (-12) 13).toNat + (x (-13) 9 && x (-13) 14).toNat + (x (-14) 10).toNat := by have q := hcov5 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2983 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2984 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2985 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2986 : 1 ≤ (x (-12) 11).toNat + (x (-13) 1 && x (-13) 12).toNat + (x (-14) 2 && x (-14) 13).toNat + (x (-15) 3 && x (-15) 14).toNat + (x (-16) 4).toNat := by have q := hcov11 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2987 : 1 ≤ (x (-10) 11).toNat + (x (-11) 1 && x (-11) 12).toNat + (x (-12) 2 && x (-12) 13).toNat + (x (-13) 3 && x (-13) 14).toNat + (x (-14) 4).toNat := by have q := hcov11 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2988 : 1 ≤ (x (-14) 13).toNat + (x (-15) 1 && x (-15) 14).toNat + (x (-16) 2).toNat := by have q := hcov13 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2989 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2990 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2991 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r2992 : (x (-16) 4).toNat ≤ (x (-16) 12).toNat := himp _ _ (hp4 (-16))
                        have r2993 : (x (-14) 4).toNat ≤ (x (-14) 12).toNat := himp _ _ (hp4 (-14))
                        have r2994 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
                        have r2995 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                        have r2996 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
                        have r2997 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
                        have r2998 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                        have r2999 := hand2 (x (-7) 3) (x (-7) 8)
                        have r3000 := hand2 (x (-8) 4) (x (-8) 9)
                        have r3001 := hand2 (x (-9) 5) (x (-9) 10)
                        have r3002 := hand1 (x (-10) 6) (x (-10) 11)
                        have r3003 := hand1 (x (-11) 7) (x (-11) 12)
                        have r3004 := hand1 (x (-12) 8) (x (-12) 13)
                        have r3005 := hand1 (x (-13) 9) (x (-13) 14)
                        have r3006 := hand1 (x (-5) 4) (x (-5) 9)
                        have r3007 := hand1 (x (-6) 5) (x (-6) 10)
                        have r3008 := hand1 (x (-7) 6) (x (-7) 11)
                        have r3009 := hand1 (x (-8) 7) (x (-8) 12)
                        have r3010 := hand1 (x (-9) 8) (x (-9) 13)
                        have r3011 := hand1 (x (-10) 9) (x (-10) 14)
                        have r3012 := hand2 (x (-3) 4) (x (-3) 11)
                        have r3013 := hand2 (x 7 1) (x 7 11)
                        have r3014 := hand1 (x 5 3) (x 5 13)
                        have r3015 := hand2 (x (-13) 1) (x (-13) 12)
                        have r3016 := hand2 (x (-14) 2) (x (-14) 13)
                        have r3017 := hand2 (x (-15) 3) (x (-15) 14)
                        have r3018 := hand2 (x (-11) 1) (x (-11) 12)
                        have r3019 := hand2 (x (-12) 2) (x (-12) 13)
                        have r3020 := hand2 (x (-13) 3) (x (-13) 14)
                        have r3021 := hand2 (x (-15) 1) (x (-15) 14)
                        have r3022 := hand2 (x (-5) 1) (x (-5) 14)
                        have r3023 := hand1 (x 7 1) (x 7 14)
                        have r3024 := hand1 (x 8 1) (x 8 14)
                        linarith only [r2972, r2973, r2974, r2975, r2976, r2977, r2978, e2979, e2980, r2981, r2982, r2983, r2984, r2985, r2986, r2987, r2988, r2989, r2990, r2991, r2992, r2993, r2994, r2995, r2996, r2997, r2998, r2999, r3000, r3001, r3002, r3003, r3004, r3005, r3006, r3007, r3008, r3009, r3010, r3011, r3012, r3013, r3014, r3015, r3016, r3017, r3018, r3019, r3020, r3021, r3022, r3023, r3024, g0, g2, g5, g6, g10, g11, g12, g13, g14, d1548, g15, g19, g20, g21, g22, g24, g27, g28, g29, g30, g35, g36, g37, f1543, g44, g45, f2335, f2408, f2568, g57, g58, g63, g64, d2931, g67, d2952, d2968, g84, g85, g86, d2641, g87, g125, g126, g127, g128, g129, g130, d2956, g157]
                    · have f3159 : (x (-2) 9).toNat = 1 := by rw [h2681]; rfl
                      have d3160 : (x (-3) 10).toNat = 0 := by
                        have r3161 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3162 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e3163 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e3164 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e3165 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e3166 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e3167 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b3168 := hb (x (-8) 7)
                        have b3169 := hb (x (-7) 6)
                        have b3170 := hb (x (-6) 5)
                        have b3171 := hb (x (-5) 4)
                        have b3172 := hb (x (-4) 11)
                        have b3173 := hb (x (-3) 10)
                        have b3174 := hb (x (-2) 9)
                        have b3175 := hb (x (-1) 8)
                        clear * - r3161 e3162 e3163 e3164 e3165 e3166 e3167 b3168 b3169 b3170 b3171 b3172 b3173 b3174 b3175 f1545 f3159 g9
                        omega
                      have d3176 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
                        have r3177 := hand2 (x (-3) 3) (x (-3) 10)
                        have b3178 := hb (x (-3) 10)
                        have b3179 := hb (x (-3) 3 && x (-3) 10)
                        clear * - r3177 b3178 b3179 d3160
                        omega
                      have d3180 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
                        have r3181 := hand2 (x (-3) 4) (x (-3) 10)
                        have b3182 := hb (x (-3) 10)
                        have b3183 := hb (x (-3) 4 && x (-3) 10)
                        clear * - r3181 b3182 b3183 d3160
                        omega
                      have d3184 : (x (-5) 4).toNat = 0 := by
                        have r3185 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3186 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e3187 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e3188 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e3189 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e3190 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e3191 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b3192 := hb (x (-8) 7)
                        have b3193 := hb (x (-7) 6)
                        have b3194 := hb (x (-6) 5)
                        have b3195 := hb (x (-5) 4)
                        have b3196 := hb (x (-4) 11)
                        have b3197 := hb (x (-3) 10)
                        have b3198 := hb (x (-2) 9)
                        have b3199 := hb (x (-1) 8)
                        clear * - r3185 e3186 e3187 e3188 e3189 e3190 e3191 b3192 b3193 b3194 b3195 b3196 b3197 b3198 b3199 f1545 f3159 d3160 g9
                        omega
                      have d3200 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                        have r3201 := hand1 (x (-5) 4) (x (-5) 13)
                        have b3202 := hb (x (-5) 4)
                        have b3203 := hb (x (-5) 4 && x (-5) 13)
                        clear * - r3201 b3202 b3203 d3184
                        omega
                      have d3204 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
                        have r3205 := hand1 (x (-5) 4) (x (-5) 9)
                        have b3206 := hb (x (-5) 4)
                        have b3207 := hb (x (-5) 4 && x (-5) 9)
                        clear * - r3205 b3206 b3207 d3184
                        omega
                      have d3208 : (x (-6) 5).toNat = 0 := by
                        have r3209 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3210 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e3211 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e3212 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e3213 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e3214 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e3215 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b3216 := hb (x (-8) 7)
                        have b3217 := hb (x (-7) 6)
                        have b3218 := hb (x (-6) 5)
                        have b3219 := hb (x (-5) 4)
                        have b3220 := hb (x (-4) 11)
                        have b3221 := hb (x (-3) 10)
                        have b3222 := hb (x (-2) 9)
                        have b3223 := hb (x (-1) 8)
                        clear * - r3209 e3210 e3211 e3212 e3213 e3214 e3215 b3216 b3217 b3218 b3219 b3220 b3221 b3222 b3223 f1545 f3159 d3160 g9 d3184
                        omega
                      have d3224 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                        have r3225 := hand1 (x (-6) 5) (x (-6) 14)
                        have b3226 := hb (x (-6) 5)
                        have b3227 := hb (x (-6) 5 && x (-6) 14)
                        clear * - r3225 b3226 b3227 d3208
                        omega
                      have d3228 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
                        have r3229 := hand1 (x (-6) 5) (x (-6) 10)
                        have b3230 := hb (x (-6) 5)
                        have b3231 := hb (x (-6) 5 && x (-6) 10)
                        clear * - r3229 b3230 b3231 d3208
                        omega
                      have d3232 : (x (-7) 6).toNat = 0 := by
                        have r3233 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3234 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e3235 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e3236 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e3237 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e3238 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e3239 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b3240 := hb (x (-8) 7)
                        have b3241 := hb (x (-7) 6)
                        have b3242 := hb (x (-6) 5)
                        have b3243 := hb (x (-5) 4)
                        have b3244 := hb (x (-4) 11)
                        have b3245 := hb (x (-3) 10)
                        have b3246 := hb (x (-2) 9)
                        have b3247 := hb (x (-1) 8)
                        clear * - r3233 e3234 e3235 e3236 e3237 e3238 e3239 b3240 b3241 b3242 b3243 b3244 b3245 b3246 b3247 f1545 f3159 d3160 g9 d3184 d3208
                        omega
                      have d3248 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
                        have r3249 := hand1 (x (-7) 6) (x (-7) 11)
                        have b3250 := hb (x (-7) 6)
                        have b3251 := hb (x (-7) 6 && x (-7) 11)
                        clear * - r3249 b3250 b3251 d3232
                        omega
                      have d3252 : (x (-3) 2 && x (-3) 11).toNat = 1 := by
                        have r3253 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3254 := hb (x (-7) 6)
                        have b3255 := hb (x (-1) 9)
                        have b3256 := hb (x (-2) 1 && x (-2) 10)
                        have b3257 := hb (x (-3) 2 && x (-3) 11)
                        have b3258 := hb (x (-4) 3 && x (-4) 12)
                        have b3259 := hb (x (-5) 4 && x (-5) 13)
                        have b3260 := hb (x (-6) 5 && x (-6) 14)
                        clear * - r3253 b3254 b3255 b3256 b3257 b3258 b3259 b3260 g27 g137 g138 d3200 d3224 d3232
                        omega
                      have d3261 : (x (-3) 11).toNat = 1 := by
                        have r3262 := hand2 (x (-3) 2) (x (-3) 11)
                        have b3263 := hb (x (-3) 11)
                        have b3264 := hb (x (-3) 2 && x (-3) 11)
                        clear * - r3262 b3263 b3264 d3252
                        omega
                      have d3265 : (x (-4) 4).toNat = 0 := by
                        have r3266 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3267 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                        have e3268 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                        have e3269 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                        have e3270 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                        have e3271 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                        have e3272 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                        have b3273 := hb (x (-7) 7)
                        have b3274 := hb (x (-6) 6)
                        have b3275 := hb (x (-5) 5)
                        have b3276 := hb (x (-4) 4)
                        have b3277 := hb (x (-3) 11)
                        have b3278 := hb (x (-2) 10)
                        have b3279 := hb (x (-1) 9)
                        have b3280 := hb (x 0 8)
                        clear * - r3266 e3267 e3268 e3269 e3270 e3271 e3272 b3273 b3274 b3275 b3276 b3277 b3278 b3279 b3280 g35 g27 g19 d3261
                        omega
                      have d3281 : (x (-4) 4 && x (-4) 8).toNat = 0 := by
                        have r3282 := hand1 (x (-4) 4) (x (-4) 8)
                        have b3283 := hb (x (-4) 4)
                        have b3284 := hb (x (-4) 4 && x (-4) 8)
                        clear * - r3282 b3283 b3284 d3265
                        omega
                      have d3285 : (x (-5) 5).toNat = 0 := by
                        have r3286 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3287 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                        have e3288 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                        have e3289 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                        have e3290 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                        have e3291 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                        have e3292 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                        have b3293 := hb (x (-7) 7)
                        have b3294 := hb (x (-6) 6)
                        have b3295 := hb (x (-5) 5)
                        have b3296 := hb (x (-4) 4)
                        have b3297 := hb (x (-3) 11)
                        have b3298 := hb (x (-2) 10)
                        have b3299 := hb (x (-1) 9)
                        have b3300 := hb (x 0 8)
                        clear * - r3286 e3287 e3288 e3289 e3290 e3291 e3292 b3293 b3294 b3295 b3296 b3297 b3298 b3299 b3300 g35 g27 g19 d3261 d3265
                        omega
                      have d3301 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
                        have r3302 := hand1 (x (-5) 5) (x (-5) 12)
                        have b3303 := hb (x (-5) 5)
                        have b3304 := hb (x (-5) 5 && x (-5) 12)
                        clear * - r3302 b3303 b3304 d3285
                        omega
                      have d3305 : (x (-5) 5 && x (-5) 9).toNat = 0 := by
                        have r3306 := hand1 (x (-5) 5) (x (-5) 9)
                        have b3307 := hb (x (-5) 5)
                        have b3308 := hb (x (-5) 5 && x (-5) 9)
                        clear * - r3306 b3307 b3308 d3285
                        omega
                      have d3309 : (x (-6) 6).toNat = 0 := by
                        have r3310 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3311 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                        have e3312 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                        have e3313 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                        have e3314 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                        have e3315 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                        have e3316 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                        have b3317 := hb (x (-7) 7)
                        have b3318 := hb (x (-6) 6)
                        have b3319 := hb (x (-5) 5)
                        have b3320 := hb (x (-4) 4)
                        have b3321 := hb (x (-3) 11)
                        have b3322 := hb (x (-2) 10)
                        have b3323 := hb (x (-1) 9)
                        have b3324 := hb (x 0 8)
                        clear * - r3310 e3311 e3312 e3313 e3314 e3315 e3316 b3317 b3318 b3319 b3320 b3321 b3322 b3323 b3324 g35 g27 g19 d3261 d3265 d3285
                        omega
                      have d3325 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
                        have r3326 := hand1 (x (-6) 6) (x (-6) 13)
                        have b3327 := hb (x (-6) 6)
                        have b3328 := hb (x (-6) 6 && x (-6) 13)
                        clear * - r3326 b3327 b3328 d3309
                        omega
                      have d3329 : (x (-6) 6 && x (-6) 10).toNat = 0 := by
                        have r3330 := hand1 (x (-6) 6) (x (-6) 10)
                        have b3331 := hb (x (-6) 6)
                        have b3332 := hb (x (-6) 6 && x (-6) 10)
                        clear * - r3330 b3331 b3332 d3309
                        omega
                      have d3333 : (x (-7) 7).toNat = 0 := by
                        have r3334 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3335 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                        have e3336 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                        have e3337 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                        have e3338 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                        have e3339 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                        have e3340 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                        have b3341 := hb (x (-7) 7)
                        have b3342 := hb (x (-6) 6)
                        have b3343 := hb (x (-5) 5)
                        have b3344 := hb (x (-4) 4)
                        have b3345 := hb (x (-3) 11)
                        have b3346 := hb (x (-2) 10)
                        have b3347 := hb (x (-1) 9)
                        have b3348 := hb (x 0 8)
                        clear * - r3334 e3335 e3336 e3337 e3338 e3339 e3340 b3341 b3342 b3343 b3344 b3345 b3346 b3347 b3348 g35 g27 g19 d3261 d3265 d3285 d3309
                        omega
                      have d3349 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
                        have r3350 := hand1 (x (-7) 7) (x (-7) 14)
                        have b3351 := hb (x (-7) 7)
                        have b3352 := hb (x (-7) 7 && x (-7) 14)
                        clear * - r3350 b3351 b3352 d3333
                        omega
                      have d3353 : (x (-7) 7 && x (-7) 11).toNat = 0 := by
                        have r3354 := hand1 (x (-7) 7) (x (-7) 11)
                        have b3355 := hb (x (-7) 7)
                        have b3356 := hb (x (-7) 7 && x (-7) 11)
                        clear * - r3354 b3355 b3356 d3333
                        omega
                      have d3357 : (x (-8) 7).toNat = 0 := by
                        have r3358 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3359 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                        have e3360 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                        have e3361 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                        have e3362 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                        have e3363 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                        have e3364 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                        have b3365 := hb (x (-8) 7)
                        have b3366 := hb (x (-7) 6)
                        have b3367 := hb (x (-6) 5)
                        have b3368 := hb (x (-5) 4)
                        have b3369 := hb (x (-4) 11)
                        have b3370 := hb (x (-3) 10)
                        have b3371 := hb (x (-2) 9)
                        have b3372 := hb (x (-1) 8)
                        clear * - r3358 e3359 e3360 e3361 e3362 e3363 e3364 b3365 b3366 b3367 b3368 b3369 b3370 b3371 b3372 f1545 f3159 d3160 g9 d3184 d3208 d3232
                        omega
                      have d3373 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
                        have r3374 := hand1 (x (-8) 7) (x (-8) 12)
                        have b3375 := hb (x (-8) 7)
                        have b3376 := hb (x (-8) 7 && x (-8) 12)
                        clear * - r3374 b3375 b3376 d3357
                        omega
                      have d3377 : (x (-8) 8).toNat = 1 := by
                        have r3378 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3379 := hb (x (-8) 8)
                        have b3380 := hb (x 0 7)
                        have b3381 := hb (x (-1) 1 && x (-1) 8)
                        have b3382 := hb (x (-2) 2 && x (-2) 9)
                        have b3383 := hb (x (-3) 3 && x (-3) 10)
                        have b3384 := hb (x (-4) 4 && x (-4) 11)
                        have b3385 := hb (x (-5) 5 && x (-5) 12)
                        have b3386 := hb (x (-6) 6 && x (-6) 13)
                        have b3387 := hb (x (-7) 7 && x (-7) 14)
                        clear * - r3378 b3379 b3380 b3381 b3382 b3383 b3384 b3385 b3386 b3387 g34 g122 g123 d3176 g124 d3301 d3325 d3349
                        omega
                      have d3388 : (x (-9) 9).toNat = 0 := by
                        have r3389 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3390 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                        have e3391 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                        have e3392 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                        have e3393 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                        have e3394 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                        have e3395 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                        have b3396 := hb (x (-15) 7)
                        have b3397 := hb (x (-14) 6)
                        have b3398 := hb (x (-13) 5)
                        have b3399 := hb (x (-12) 4)
                        have b3400 := hb (x (-11) 11)
                        have b3401 := hb (x (-10) 10)
                        have b3402 := hb (x (-9) 9)
                        have b3403 := hb (x (-8) 8)
                        clear * - r3389 e3390 e3391 e3392 e3393 e3394 e3395 b3396 b3397 b3398 b3399 b3400 b3401 b3402 b3403 d3377
                        omega
                      have d3404 : (x (-9) 9 && x (-9) 13).toNat = 0 := by
                        have r3405 := hand1 (x (-9) 9) (x (-9) 13)
                        have b3406 := hb (x (-9) 9)
                        have b3407 := hb (x (-9) 9 && x (-9) 13)
                        clear * - r3405 b3406 b3407 d3388
                        omega
                      have d3408 : (x (-10) 10).toNat = 0 := by
                        have r3409 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3410 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                        have e3411 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                        have e3412 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                        have e3413 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                        have e3414 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                        have e3415 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                        have b3416 := hb (x (-15) 7)
                        have b3417 := hb (x (-14) 6)
                        have b3418 := hb (x (-13) 5)
                        have b3419 := hb (x (-12) 4)
                        have b3420 := hb (x (-11) 11)
                        have b3421 := hb (x (-10) 10)
                        have b3422 := hb (x (-9) 9)
                        have b3423 := hb (x (-8) 8)
                        clear * - r3409 e3410 e3411 e3412 e3413 e3414 e3415 b3416 b3417 b3418 b3419 b3420 b3421 b3422 b3423 d3377 d3388
                        omega
                      have d3424 : (x (-11) 11).toNat = 0 := by
                        have r3425 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3426 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                        have e3427 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                        have e3428 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                        have e3429 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                        have e3430 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                        have e3431 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                        have b3432 := hb (x (-15) 7)
                        have b3433 := hb (x (-14) 6)
                        have b3434 := hb (x (-13) 5)
                        have b3435 := hb (x (-12) 4)
                        have b3436 := hb (x (-11) 11)
                        have b3437 := hb (x (-10) 10)
                        have b3438 := hb (x (-9) 9)
                        have b3439 := hb (x (-8) 8)
                        clear * - r3425 e3426 e3427 e3428 e3429 e3430 e3431 b3432 b3433 b3434 b3435 b3436 b3437 b3438 b3439 d3377 d3388 d3408
                        omega
                      have d3440 : (x (-8) 8 && x (-8) 12).toNat = 1 := by
                        have r3441 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3442 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
                        have e3443 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
                        have b3444 := hb (x (-11) 11)
                        have b3445 := hb (x (-10) 10)
                        have b3446 := hb (x (-1) 5)
                        have b3447 := hb (x 0 4)
                        have b3448 := hb (x (-2) 2 && x (-2) 6)
                        have b3449 := hb (x (-3) 3 && x (-3) 7)
                        have b3450 := hb (x (-4) 4 && x (-4) 8)
                        have b3451 := hb (x (-5) 5 && x (-5) 9)
                        have b3452 := hb (x (-6) 6 && x (-6) 10)
                        have b3453 := hb (x (-7) 7 && x (-7) 11)
                        have b3454 := hb (x (-8) 8 && x (-8) 12)
                        have b3455 := hb (x (-9) 9 && x (-9) 13)
                        clear * - r3441 e3442 e3443 b3444 b3445 b3446 b3447 b3448 b3449 b3450 b3451 b3452 b3453 b3454 b3455 g32 g24 g77 d2645 d3281 d3305 d3329 d3353 d3404 d3408 d3424
                        omega
                      have d3456 : (x (-8) 12).toNat = 1 := by
                        have r3457 := hand2 (x (-8) 8) (x (-8) 12)
                        have b3458 := hb (x (-8) 12)
                        have b3459 := hb (x (-8) 8 && x (-8) 12)
                        clear * - r3457 b3458 b3459 d3440
                        omega
                      have d3460 : (x (-9) 13).toNat = 0 := by
                        have r3461 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3462 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                        have e3463 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                        have b3464 := hb (x (-11) 3)
                        have b3465 := hb (x (-10) 2)
                        have b3466 := hb (x (-9) 13)
                        have b3467 := hb (x (-8) 12)
                        clear * - r3461 e3462 e3463 b3464 b3465 b3466 b3467 d3456
                        omega
                      have d3468 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
                        have r3469 := hand2 (x (-9) 8) (x (-9) 13)
                        have b3470 := hb (x (-9) 13)
                        have b3471 := hb (x (-9) 8 && x (-9) 13)
                        clear * - r3469 b3470 b3471 d3460
                        omega
                      have r3472 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3473 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3474 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                      have e3475 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                      have e3476 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                      have e3477 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                      have e3478 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                      have e3479 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                      have r3480 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3481 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3482 : 1 ≤ (x (-9) 10).toNat + (x (-10) 1 && x (-10) 11).toNat + (x (-11) 2 && x (-11) 12).toNat + (x (-12) 3 && x (-12) 13).toNat + (x (-13) 4 && x (-13) 14).toNat + (x (-14) 5).toNat := by have q := hcov10 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3483 := hand1 (x (-10) 9) (x (-10) 14)
                      have r3484 := hand1 (x (-7) 8) (x (-7) 14)
                      have r3485 := hand2 (x (-10) 1) (x (-10) 11)
                      have r3486 := hand2 (x (-11) 2) (x (-11) 12)
                      have r3487 := hand2 (x (-12) 3) (x (-12) 13)
                      have r3488 := hand1 (x (-13) 4) (x (-13) 14)
                      linarith only [r3472, r3473, e3474, e3475, e3476, e3477, e3478, e3479, r3480, r3481, r3482, r3483, r3484, r3485, r3486, r3487, r3488, g0, g2, g6, g12, g15, g22, g24, g30, g43, g86, d2641, g87, d3204, d3228, d3248, d3373, d3468, g109, g110, g111, d3180, g112, g113, g114]
                · have f3534 : (x (-2) 8).toNat = 1 := by rw [h2489]; rfl
                  have d3535 : (x (-3) 9).toNat = 0 := by
                    have r3536 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e3537 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e3538 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e3539 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e3540 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e3541 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e3542 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b3543 := hb (x (-9) 7)
                    have b3544 := hb (x (-8) 6)
                    have b3545 := hb (x (-7) 5)
                    have b3546 := hb (x (-6) 4)
                    have b3547 := hb (x (-5) 11)
                    have b3548 := hb (x (-4) 10)
                    have b3549 := hb (x (-3) 9)
                    have b3550 := hb (x (-2) 8)
                    clear * - r3536 e3537 e3538 e3539 e3540 e3541 e3542 b3543 b3544 b3545 b3546 b3547 b3548 b3549 b3550 f3534 g8 g4
                    omega
                  have d3551 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
                    have r3552 := hand2 (x (-3) 4) (x (-3) 9)
                    have b3553 := hb (x (-3) 9)
                    have b3554 := hb (x (-3) 4 && x (-3) 9)
                    clear * - r3552 b3553 b3554 d3535
                    omega
                  have d3555 : (x (-6) 4).toNat = 0 := by
                    have r3556 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e3557 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e3558 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e3559 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e3560 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e3561 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e3562 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b3563 := hb (x (-9) 7)
                    have b3564 := hb (x (-8) 6)
                    have b3565 := hb (x (-7) 5)
                    have b3566 := hb (x (-6) 4)
                    have b3567 := hb (x (-5) 11)
                    have b3568 := hb (x (-4) 10)
                    have b3569 := hb (x (-3) 9)
                    have b3570 := hb (x (-2) 8)
                    clear * - r3556 e3557 e3558 e3559 e3560 e3561 e3562 b3563 b3564 b3565 b3566 b3567 b3568 b3569 b3570 f3534 d3535 g8 g4
                    omega
                  have d3571 : (x (-7) 5).toNat = 0 := by
                    have r3572 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e3573 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e3574 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e3575 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e3576 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e3577 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e3578 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b3579 := hb (x (-9) 7)
                    have b3580 := hb (x (-8) 6)
                    have b3581 := hb (x (-7) 5)
                    have b3582 := hb (x (-6) 4)
                    have b3583 := hb (x (-5) 11)
                    have b3584 := hb (x (-4) 10)
                    have b3585 := hb (x (-3) 9)
                    have b3586 := hb (x (-2) 8)
                    clear * - r3572 e3573 e3574 e3575 e3576 e3577 e3578 b3579 b3580 b3581 b3582 b3583 b3584 b3585 b3586 f3534 d3535 g8 g4 d3555
                    omega
                  have d3587 : (x (-7) 5 && x (-7) 12).toNat = 0 := by
                    have r3588 := hand1 (x (-7) 5) (x (-7) 12)
                    have b3589 := hb (x (-7) 5)
                    have b3590 := hb (x (-7) 5 && x (-7) 12)
                    clear * - r3588 b3589 b3590 d3571
                    omega
                  have d3591 : (x (-8) 6).toNat = 0 := by
                    have r3592 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e3593 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e3594 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e3595 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e3596 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e3597 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e3598 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b3599 := hb (x (-9) 7)
                    have b3600 := hb (x (-8) 6)
                    have b3601 := hb (x (-7) 5)
                    have b3602 := hb (x (-6) 4)
                    have b3603 := hb (x (-5) 11)
                    have b3604 := hb (x (-4) 10)
                    have b3605 := hb (x (-3) 9)
                    have b3606 := hb (x (-2) 8)
                    clear * - r3592 e3593 e3594 e3595 e3596 e3597 e3598 b3599 b3600 b3601 b3602 b3603 b3604 b3605 b3606 f3534 d3535 g8 g4 d3555 d3571
                    omega
                  have d3607 : (x (-8) 6 && x (-8) 13).toNat = 0 := by
                    have r3608 := hand1 (x (-8) 6) (x (-8) 13)
                    have b3609 := hb (x (-8) 6)
                    have b3610 := hb (x (-8) 6 && x (-8) 13)
                    clear * - r3608 b3609 b3610 d3591
                    omega
                  have d3611 : (x (-9) 7).toNat = 0 := by
                    have r3612 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e3613 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e3614 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e3615 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e3616 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e3617 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e3618 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b3619 := hb (x (-9) 7)
                    have b3620 := hb (x (-8) 6)
                    have b3621 := hb (x (-7) 5)
                    have b3622 := hb (x (-6) 4)
                    have b3623 := hb (x (-5) 11)
                    have b3624 := hb (x (-4) 10)
                    have b3625 := hb (x (-3) 9)
                    have b3626 := hb (x (-2) 8)
                    clear * - r3612 e3613 e3614 e3615 e3616 e3617 e3618 b3619 b3620 b3621 b3622 b3623 b3624 b3625 b3626 f3534 d3535 g8 g4 d3555 d3571 d3591
                    omega
                  have d3627 : (x (-9) 7 && x (-9) 14).toNat = 0 := by
                    have r3628 := hand1 (x (-9) 7) (x (-9) 14)
                    have b3629 := hb (x (-9) 7)
                    have b3630 := hb (x (-9) 7 && x (-9) 14)
                    clear * - r3628 b3629 b3630 d3611
                    omega
                  have r3631 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r3632 : (x (-10) 8).toNat + (x (-11) 1 && x (-11) 9).toNat + (x (-12) 2 && x (-12) 10).toNat + (x (-13) 3 && x (-13) 11).toNat + (x (-14) 4 && x (-14) 12).toNat + (x (-15) 5 && x (-15) 13).toNat + (x (-16) 6 && x (-16) 14).toNat + (x (-17) 7).toNat = 1 := by have q := hd8 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e3633 : (x (-11) 1 && x (-11) 9).toNat = (x (-11) 9).toNat := handr _ _ (fun h => hp9 (-11) (h))
                  have e3634 : (x (-12) 2 && x (-12) 10).toNat = (x (-12) 10).toNat := handr _ _ (fun h => hp10 (-12) (h))
                  have e3635 : (x (-13) 3 && x (-13) 11).toNat = (x (-13) 11).toNat := handr _ _ (fun h => hp11 (-13) (h))
                  have e3636 : (x (-14) 4 && x (-14) 12).toNat = (x (-14) 4).toNat := handl _ _ (fun h => hp4 (-14) (h))
                  have e3637 : (x (-15) 5 && x (-15) 13).toNat = (x (-15) 5).toNat := handl _ _ (fun h => hp5 (-15) (h))
                  have e3638 : (x (-16) 6 && x (-16) 14).toNat = (x (-16) 6).toNat := handl _ _ (fun h => hp6 (-16) (h))
                  have r3639 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e3640 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                  have e3641 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                  have e3642 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                  have e3643 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                  have e3644 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                  have e3645 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                  have r3646 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r3647 : 1 ≤ (x (-2) 7).toNat + (x (-3) 1 && x (-3) 8).toNat + (x (-4) 2 && x (-4) 9).toNat + (x (-5) 3 && x (-5) 10).toNat + (x (-6) 4 && x (-6) 11).toNat + (x (-7) 5 && x (-7) 12).toNat + (x (-8) 6 && x (-8) 13).toNat + (x (-9) 7 && x (-9) 14).toNat + (x (-10) 8).toNat := by have q := hcov7 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r3648 : 1 ≤ (x (-3) 9).toNat + (x (-4) 1 && x (-4) 10).toNat + (x (-5) 2 && x (-5) 11).toNat + (x (-6) 3 && x (-6) 12).toNat + (x (-7) 4 && x (-7) 13).toNat + (x (-8) 5 && x (-8) 14).toNat + (x (-9) 6).toNat := by have q := hcov9 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r3649 : 1 ≤ (x (-10) 11).toNat + (x (-11) 1 && x (-11) 12).toNat + (x (-12) 2 && x (-12) 13).toNat + (x (-13) 3 && x (-13) 14).toNat + (x (-14) 4).toNat := by have q := hcov11 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r3650 := hand1 (x (-7) 8) (x (-7) 13)
                  have r3651 := hand1 (x (-8) 9) (x (-8) 14)
                  have r3652 := hand2 (x (-3) 1) (x (-3) 8)
                  have r3653 := hand1 (x (-7) 4) (x (-7) 13)
                  have r3654 := hand1 (x (-8) 5) (x (-8) 14)
                  have r3655 := hand2 (x (-11) 1) (x (-11) 12)
                  have r3656 := hand2 (x (-12) 2) (x (-12) 13)
                  have r3657 := hand2 (x (-13) 3) (x (-13) 14)
                  linarith only [r3631, r3632, e3633, e3634, e3635, e3636, e3637, e3638, r3639, e3640, e3641, e3642, e3643, e3644, e3645, r3646, r3647, r3648, r3649, r3650, r3651, r3652, r3653, r3654, r3655, r3656, r3657, g0, g1, g2, g3, g6, g7, g12, d3535, g15, g18, g22, g30, g42, g88, g89, g90, d3551, g91, g92, g93, g119, g120, g121, d3587, d3607, d3627, g134, g135, g136]
      · have f3715 : (x (-1) 14).toNat = 1 := by rw [h1546]; rfl
        have d3716 : (x 12 1).toNat = 0 := by
          have r3717 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3718 := hb (x (-1) 14)
          have b3719 := hb (x 0 13)
          have b3720 := hb (x 1 12)
          have b3721 := hb (x 2 11)
          have b3722 := hb (x 3 10)
          have b3723 := hb (x 4 9)
          have b3724 := hb (x 5 8)
          have b3725 := hb (x 6 7)
          have b3726 := hb (x 7 6)
          have b3727 := hb (x 8 5)
          have b3728 := hb (x 9 4)
          have b3729 := hb (x 10 3)
          have b3730 := hb (x 11 2)
          have b3731 := hb (x 12 1)
          clear * - r3717 b3718 b3719 b3720 b3721 b3722 b3723 b3724 b3725 b3726 b3727 b3728 b3729 b3730 b3731 g68 g65 g59 g51 g47 g38 f3715
          omega
        have d3732 : (x 12 1 && x 12 14).toNat = 0 := by
          have r3733 := hand1 (x 12 1) (x 12 14)
          have b3734 := hb (x 12 1)
          have b3735 := hb (x 12 1 && x 12 14)
          clear * - r3733 b3734 b3735 d3716
          omega
        have d3736 : (x 12 1 && x 12 11).toNat = 0 := by
          have r3737 := hand1 (x 12 1) (x 12 11)
          have b3738 := hb (x 12 1)
          have b3739 := hb (x 12 1 && x 12 11)
          clear * - r3737 b3738 b3739 d3716
          omega
        have d3740 : (x 12 13).toNat = 0 := by
          have r3741 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b3742 := hb (x 12 1)
          have b3743 := hb (x 12 13)
          clear * - r3741 b3742 b3743 d3716
          omega
        have d3744 : (x 12 5).toNat = 0 := by
          have r3745 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
          have b3746 := hb (x 12 5)
          have b3747 := hb (x 12 13)
          clear * - r3745 b3746 b3747 d3740
          omega
        have d3748 : (x 11 2).toNat = 0 := by
          have r3749 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3750 := hb (x (-1) 14)
          have b3751 := hb (x 0 13)
          have b3752 := hb (x 1 12)
          have b3753 := hb (x 2 11)
          have b3754 := hb (x 3 10)
          have b3755 := hb (x 4 9)
          have b3756 := hb (x 5 8)
          have b3757 := hb (x 6 7)
          have b3758 := hb (x 7 6)
          have b3759 := hb (x 8 5)
          have b3760 := hb (x 9 4)
          have b3761 := hb (x 10 3)
          have b3762 := hb (x 11 2)
          have b3763 := hb (x 12 1)
          clear * - r3749 b3750 b3751 b3752 b3753 b3754 b3755 b3756 b3757 b3758 b3759 b3760 b3761 b3762 b3763 d3716 g68 g65 g59 g51 g47 g38 f3715
          omega
        have d3764 : (x 11 2 && x 11 12).toNat = 0 := by
          have r3765 := hand1 (x 11 2) (x 11 12)
          have b3766 := hb (x 11 2)
          have b3767 := hb (x 11 2 && x 11 12)
          clear * - r3765 b3766 b3767 d3748
          omega
        have d3768 : (x 11 10).toNat = 0 := by
          have r3769 : (x 11 10).toNat ≤ (x 11 2).toNat := himp _ _ (hp10 11)
          have b3770 := hb (x 11 2)
          have b3771 := hb (x 11 10)
          clear * - r3769 b3770 b3771 d3748
          omega
        have d3772 : (x 13 13).toNat = 1 := by
          have r3773 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3774 := hb (x 11 2)
          have b3775 := hb (x 13 13)
          have b3776 := hb (x 12 1 && x 12 14)
          clear * - r3773 b3774 b3775 b3776 d3732 d3748
          omega
        have d3777 : (x 13 1).toNat = 1 := by
          have r3778 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
          have b3779 := hb (x 13 1)
          have b3780 := hb (x 13 13)
          clear * - r3778 b3779 b3780 d3772
          omega
        have d3781 : (x 14 14).toNat = 0 := by
          have r3782 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3783 := hb (x 13 1)
          have b3784 := hb (x 14 14)
          clear * - r3782 b3783 b3784 d3777
          omega
        have d3785 : (x 14 1 && x 14 14).toNat = 0 := by
          have r3786 := hand2 (x 14 1) (x 14 14)
          have b3787 := hb (x 14 14)
          have b3788 := hb (x 14 1 && x 14 14)
          clear * - r3786 b3787 b3788 d3781
          omega
        have d3789 : (x 14 4 && x 14 14).toNat = 0 := by
          have r3790 := hand2 (x 14 4) (x 14 14)
          have b3791 := hb (x 14 14)
          have b3792 := hb (x 14 4 && x 14 14)
          clear * - r3790 b3791 b3792 d3781
          omega
        have d3793 : (x 14 5 && x 14 14).toNat = 0 := by
          have r3794 := hand2 (x 14 5) (x 14 14)
          have b3795 := hb (x 14 14)
          have b3796 := hb (x 14 5 && x 14 14)
          clear * - r3794 b3795 b3796 d3781
          omega
        have d3797 : (x 14 6).toNat = 0 := by
          have r3798 : (x 14 6).toNat ≤ (x 14 14).toNat := himp _ _ (hp6 14)
          have b3799 := hb (x 14 6)
          have b3800 := hb (x 14 14)
          clear * - r3798 b3799 b3800 d3781
          omega
        have d3801 : (x 14 2 && x 14 6).toNat = 0 := by
          have r3802 := hand2 (x 14 2) (x 14 6)
          have b3803 := hb (x 14 6)
          have b3804 := hb (x 14 2 && x 14 6)
          clear * - r3802 b3803 b3804 d3797
          omega
        have d3805 : (x 14 2).toNat = 0 := by
          have r3806 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
          have b3807 := hb (x 14 2)
          have b3808 := hb (x 14 14)
          clear * - r3806 b3807 b3808 d3781
          omega
        have d3809 : (x 14 2 && x 14 8).toNat = 0 := by
          have r3810 := hand1 (x 14 2) (x 14 8)
          have b3811 := hb (x 14 2)
          have b3812 := hb (x 14 2 && x 14 8)
          clear * - r3810 b3811 b3812 d3805
          omega
        have d3813 : (x 14 10).toNat = 0 := by
          have r3814 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
          have b3815 := hb (x 14 2)
          have b3816 := hb (x 14 10)
          clear * - r3814 b3815 b3816 d3805
          omega
        have d3817 : (x 12 2).toNat = 0 := by
          have r3818 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3819 := hb (x 0 14)
          have b3820 := hb (x 1 13)
          have b3821 := hb (x 2 12)
          have b3822 := hb (x 3 11)
          have b3823 := hb (x 4 10)
          have b3824 := hb (x 5 9)
          have b3825 := hb (x 6 8)
          have b3826 := hb (x 7 7)
          have b3827 := hb (x 8 6)
          have b3828 := hb (x 9 5)
          have b3829 := hb (x 10 4)
          have b3830 := hb (x 11 3)
          have b3831 := hb (x 12 2)
          have b3832 := hb (x 13 1)
          clear * - r3818 b3819 b3820 b3821 b3822 b3823 b3824 b3825 b3826 b3827 b3828 b3829 b3830 b3831 b3832 d3777 g52 g48 g39
          omega
        have d3833 : (x 12 2 && x 12 12).toNat = 0 := by
          have r3834 := hand1 (x 12 2) (x 12 12)
          have b3835 := hb (x 12 2)
          have b3836 := hb (x 12 2 && x 12 12)
          clear * - r3834 b3835 b3836 d3817
          omega
        have d3837 : (x 12 10).toNat = 0 := by
          have r3838 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
          have b3839 := hb (x 12 2)
          have b3840 := hb (x 12 10)
          clear * - r3838 b3839 b3840 d3817
          omega
        have d3841 : (x 12 4 && x 12 10).toNat = 0 := by
          have r3842 := hand2 (x 12 4) (x 12 10)
          have b3843 := hb (x 12 10)
          have b3844 := hb (x 12 4 && x 12 10)
          clear * - r3842 b3843 b3844 d3837
          omega
        have d3845 : (x 11 3).toNat = 0 := by
          have r3846 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3847 := hb (x 0 14)
          have b3848 := hb (x 1 13)
          have b3849 := hb (x 2 12)
          have b3850 := hb (x 3 11)
          have b3851 := hb (x 4 10)
          have b3852 := hb (x 5 9)
          have b3853 := hb (x 6 8)
          have b3854 := hb (x 7 7)
          have b3855 := hb (x 8 6)
          have b3856 := hb (x 9 5)
          have b3857 := hb (x 10 4)
          have b3858 := hb (x 11 3)
          have b3859 := hb (x 12 2)
          have b3860 := hb (x 13 1)
          clear * - r3846 b3847 b3848 b3849 b3850 b3851 b3852 b3853 b3854 b3855 b3856 b3857 b3858 b3859 b3860 d3777 d3817 g52 g48 g39
          omega
        have d3861 : (x 11 3 && x 11 13).toNat = 0 := by
          have r3862 := hand1 (x 11 3) (x 11 13)
          have b3863 := hb (x 11 3)
          have b3864 := hb (x 11 3 && x 11 13)
          clear * - r3862 b3863 b3864 d3845
          omega
        have d3865 : (x 11 11).toNat = 0 := by
          have r3866 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
          have b3867 := hb (x 11 3)
          have b3868 := hb (x 11 11)
          clear * - r3866 b3867 b3868 d3845
          omega
        have d3869 : (x 11 5 && x 11 11).toNat = 0 := by
          have r3870 := hand2 (x 11 5) (x 11 11)
          have b3871 := hb (x 11 11)
          have b3872 := hb (x 11 5 && x 11 11)
          clear * - r3870 b3871 b3872 d3865
          omega
        have d3873 : (x 10 4).toNat = 0 := by
          have r3874 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3875 := hb (x 0 14)
          have b3876 := hb (x 1 13)
          have b3877 := hb (x 2 12)
          have b3878 := hb (x 3 11)
          have b3879 := hb (x 4 10)
          have b3880 := hb (x 5 9)
          have b3881 := hb (x 6 8)
          have b3882 := hb (x 7 7)
          have b3883 := hb (x 8 6)
          have b3884 := hb (x 9 5)
          have b3885 := hb (x 10 4)
          have b3886 := hb (x 11 3)
          have b3887 := hb (x 12 2)
          have b3888 := hb (x 13 1)
          clear * - r3874 b3875 b3876 b3877 b3878 b3879 b3880 b3881 b3882 b3883 b3884 b3885 b3886 b3887 b3888 d3777 d3817 d3845 g52 g48 g39
          omega
        have d3889 : (x 10 4 && x 10 14).toNat = 0 := by
          have r3890 := hand1 (x 10 4) (x 10 14)
          have b3891 := hb (x 10 4)
          have b3892 := hb (x 10 4 && x 10 14)
          clear * - r3890 b3891 b3892 d3873
          omega
        have d3893 : (x 9 5).toNat = 0 := by
          have r3894 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3895 := hb (x 0 14)
          have b3896 := hb (x 1 13)
          have b3897 := hb (x 2 12)
          have b3898 := hb (x 3 11)
          have b3899 := hb (x 4 10)
          have b3900 := hb (x 5 9)
          have b3901 := hb (x 6 8)
          have b3902 := hb (x 7 7)
          have b3903 := hb (x 8 6)
          have b3904 := hb (x 9 5)
          have b3905 := hb (x 10 4)
          have b3906 := hb (x 11 3)
          have b3907 := hb (x 12 2)
          have b3908 := hb (x 13 1)
          clear * - r3894 b3895 b3896 b3897 b3898 b3899 b3900 b3901 b3902 b3903 b3904 b3905 b3906 b3907 b3908 d3777 d3817 d3845 d3873 g52 g48 g39
          omega
        have d3909 : (x 13 1 && x 13 11).toNat = 1 := by
          have r3910 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3911 := hb (x 9 5)
          have b3912 := hb (x 14 10)
          have b3913 := hb (x 13 1 && x 13 11)
          have b3914 := hb (x 12 2 && x 12 12)
          have b3915 := hb (x 11 3 && x 11 13)
          have b3916 := hb (x 10 4 && x 10 14)
          clear * - r3910 b3911 b3912 b3913 b3914 b3915 b3916 d3813 d3833 d3861 d3889 d3893
          omega
        have d3917 : (x 13 11).toNat = 1 := by
          have r3918 := hand2 (x 13 1) (x 13 11)
          have b3919 := hb (x 13 11)
          have b3920 := hb (x 13 1 && x 13 11)
          clear * - r3918 b3919 b3920 d3909
          omega
        have d3921 : (x 13 3).toNat = 1 := by
          have r3922 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
          have b3923 := hb (x 13 3)
          have b3924 := hb (x 13 11)
          clear * - r3922 b3923 b3924 d3917
          omega
        have d3925 : (x 16 12).toNat = 0 := by
          have r3926 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3927 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e3928 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b3929 := hb (x 13 3)
          have b3930 := hb (x 14 2)
          have b3931 := hb (x 15 13)
          have b3932 := hb (x 16 12)
          clear * - r3926 e3927 e3928 b3929 b3930 b3931 b3932 d3805 d3921
          omega
        have d3933 : (x 16 2 && x 16 12).toNat = 0 := by
          have r3934 := hand2 (x 16 2) (x 16 12)
          have b3935 := hb (x 16 12)
          have b3936 := hb (x 16 2 && x 16 12)
          clear * - r3934 b3935 b3936 d3925
          omega
        have d3937 : (x 16 3 && x 16 12).toNat = 0 := by
          have r3938 := hand2 (x 16 3) (x 16 12)
          have b3939 := hb (x 16 12)
          have b3940 := hb (x 16 3 && x 16 12)
          clear * - r3938 b3939 b3940 d3925
          omega
        have d3941 : (x 16 4).toNat = 0 := by
          have r3942 : (x 16 4).toNat ≤ (x 16 12).toNat := himp _ _ (hp4 16)
          have b3943 := hb (x 16 4)
          have b3944 := hb (x 16 12)
          clear * - r3942 b3943 b3944 d3925
          omega
        have d3945 : (x 16 4 && x 16 13).toNat = 0 := by
          have r3946 := hand1 (x 16 4) (x 16 13)
          have b3947 := hb (x 16 4)
          have b3948 := hb (x 16 4 && x 16 13)
          clear * - r3946 b3947 b3948 d3941
          omega
        have d3949 : (x 15 13).toNat = 0 := by
          have r3950 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3951 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e3952 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b3953 := hb (x 13 3)
          have b3954 := hb (x 14 2)
          have b3955 := hb (x 15 13)
          have b3956 := hb (x 16 12)
          clear * - r3950 e3951 e3952 b3953 b3954 b3955 b3956 d3925 d3805 d3921
          omega
        have d3957 : (x 15 3 && x 15 13).toNat = 0 := by
          have r3958 := hand2 (x 15 3) (x 15 13)
          have b3959 := hb (x 15 13)
          have b3960 := hb (x 15 3 && x 15 13)
          clear * - r3958 b3959 b3960 d3949
          omega
        have d3961 : (x 15 4 && x 15 13).toNat = 0 := by
          have r3962 := hand2 (x 15 4) (x 15 13)
          have b3963 := hb (x 15 13)
          have b3964 := hb (x 15 4 && x 15 13)
          clear * - r3962 b3963 b3964 d3949
          omega
        have d3965 : (x 15 5).toNat = 0 := by
          have r3966 : (x 15 5).toNat ≤ (x 15 13).toNat := himp _ _ (hp5 15)
          have b3967 := hb (x 15 5)
          have b3968 := hb (x 15 13)
          clear * - r3966 b3967 b3968 d3949
          omega
        have d3969 : (x 15 5 && x 15 14).toNat = 0 := by
          have r3970 := hand1 (x 15 5) (x 15 14)
          have b3971 := hb (x 15 5)
          have b3972 := hb (x 15 5 && x 15 14)
          clear * - r3970 b3971 b3972 d3965
          omega
        have d3973 : (x 13 2).toNat = 1 := by
          have r3974 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b3975 := hb (x 13 2)
          have b3976 := hb (x 15 13)
          have b3977 := hb (x 14 1 && x 14 14)
          clear * - r3974 b3975 b3976 b3977 d3949 d3785
          omega
        have d3978 : (x 15 12).toNat = 0 := by
          have r3979 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3980 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e3981 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b3982 := hb (x 12 3)
          have b3983 := hb (x 13 2)
          have b3984 := hb (x 14 13)
          have b3985 := hb (x 15 12)
          clear * - r3979 e3980 e3981 b3982 b3983 b3984 b3985 d3973
          omega
        have d3986 : (x 15 2 && x 15 12).toNat = 0 := by
          have r3987 := hand2 (x 15 2) (x 15 12)
          have b3988 := hb (x 15 12)
          have b3989 := hb (x 15 2 && x 15 12)
          clear * - r3987 b3988 b3989 d3978
          omega
        have d3990 : (x 15 4).toNat = 0 := by
          have r3991 : (x 15 4).toNat ≤ (x 15 12).toNat := himp _ _ (hp4 15)
          have b3992 := hb (x 15 4)
          have b3993 := hb (x 15 12)
          clear * - r3991 b3992 b3993 d3978
          omega
        have d3994 : (x 14 13).toNat = 0 := by
          have r3995 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e3996 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e3997 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b3998 := hb (x 12 3)
          have b3999 := hb (x 13 2)
          have b4000 := hb (x 14 13)
          have b4001 := hb (x 15 12)
          clear * - r3995 e3996 e3997 b3998 b3999 b4000 b4001 d3978 d3973
          omega
        have d4002 : (x 14 3 && x 14 13).toNat = 0 := by
          have r4003 := hand2 (x 14 3) (x 14 13)
          have b4004 := hb (x 14 13)
          have b4005 := hb (x 14 3 && x 14 13)
          clear * - r4003 b4004 b4005 d3994
          omega
        have d4006 : (x 14 5).toNat = 0 := by
          have r4007 : (x 14 5).toNat ≤ (x 14 13).toNat := himp _ _ (hp5 14)
          have b4008 := hb (x 14 5)
          have b4009 := hb (x 14 13)
          clear * - r4007 b4008 b4009 d3994
          omega
        have d4010 : (x 12 3).toNat = 0 := by
          have r4011 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4012 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e4013 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b4014 := hb (x 12 3)
          have b4015 := hb (x 13 2)
          have b4016 := hb (x 14 13)
          have b4017 := hb (x 15 12)
          clear * - r4011 e4012 e4013 b4014 b4015 b4016 b4017 d3978 d3994 d3973
          omega
        have d4018 : (x 12 11).toNat = 0 := by
          have r4019 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
          have b4020 := hb (x 12 3)
          have b4021 := hb (x 12 11)
          clear * - r4019 b4020 b4021 d4010
          omega
        have d4022 : (x 16 8).toNat = 0 := by
          have r4023 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4024 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e4025 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e4026 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e4027 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e4028 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e4029 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b4030 := hb (x 9 7)
          have b4031 := hb (x 10 6)
          have b4032 := hb (x 11 5)
          have b4033 := hb (x 12 4)
          have b4034 := hb (x 13 11)
          have b4035 := hb (x 14 10)
          have b4036 := hb (x 15 9)
          have b4037 := hb (x 16 8)
          clear * - r4023 e4024 e4025 e4026 e4027 e4028 e4029 b4030 b4031 b4032 b4033 b4034 b4035 b4036 b4037 d3813 d3917
          omega
        have d4038 : (x 15 9).toNat = 0 := by
          have r4039 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4040 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e4041 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e4042 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e4043 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e4044 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e4045 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b4046 := hb (x 9 7)
          have b4047 := hb (x 10 6)
          have b4048 := hb (x 11 5)
          have b4049 := hb (x 12 4)
          have b4050 := hb (x 13 11)
          have b4051 := hb (x 14 10)
          have b4052 := hb (x 15 9)
          have b4053 := hb (x 16 8)
          clear * - r4039 e4040 e4041 e4042 e4043 e4044 e4045 b4046 b4047 b4048 b4049 b4050 b4051 b4052 b4053 d4022 d3813 d3917
          omega
        have d4054 : (x 12 4).toNat = 0 := by
          have r4055 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4056 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e4057 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e4058 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e4059 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e4060 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e4061 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b4062 := hb (x 9 7)
          have b4063 := hb (x 10 6)
          have b4064 := hb (x 11 5)
          have b4065 := hb (x 12 4)
          have b4066 := hb (x 13 11)
          have b4067 := hb (x 14 10)
          have b4068 := hb (x 15 9)
          have b4069 := hb (x 16 8)
          clear * - r4055 e4056 e4057 e4058 e4059 e4060 e4061 b4062 b4063 b4064 b4065 b4066 b4067 b4068 b4069 d4022 d4038 d3813 d3917
          omega
        have d4070 : (x 12 4 && x 12 8).toNat = 0 := by
          have r4071 := hand1 (x 12 4) (x 12 8)
          have b4072 := hb (x 12 4)
          have b4073 := hb (x 12 4 && x 12 8)
          clear * - r4071 b4072 b4073 d4054
          omega
        have d4074 : (x 11 5).toNat = 0 := by
          have r4075 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4076 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e4077 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e4078 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e4079 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e4080 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e4081 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b4082 := hb (x 9 7)
          have b4083 := hb (x 10 6)
          have b4084 := hb (x 11 5)
          have b4085 := hb (x 12 4)
          have b4086 := hb (x 13 11)
          have b4087 := hb (x 14 10)
          have b4088 := hb (x 15 9)
          have b4089 := hb (x 16 8)
          clear * - r4075 e4076 e4077 e4078 e4079 e4080 e4081 b4082 b4083 b4084 b4085 b4086 b4087 b4088 b4089 d4022 d4038 d3813 d3917 d4054
          omega
        have d4090 : (x 11 5 && x 11 9).toNat = 0 := by
          have r4091 := hand1 (x 11 5) (x 11 9)
          have b4092 := hb (x 11 5)
          have b4093 := hb (x 11 5 && x 11 9)
          clear * - r4091 b4092 b4093 d4074
          omega
        have d4094 : (x 10 6).toNat = 0 := by
          have r4095 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4096 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e4097 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e4098 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e4099 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e4100 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e4101 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b4102 := hb (x 9 7)
          have b4103 := hb (x 10 6)
          have b4104 := hb (x 11 5)
          have b4105 := hb (x 12 4)
          have b4106 := hb (x 13 11)
          have b4107 := hb (x 14 10)
          have b4108 := hb (x 15 9)
          have b4109 := hb (x 16 8)
          clear * - r4095 e4096 e4097 e4098 e4099 e4100 e4101 b4102 b4103 b4104 b4105 b4106 b4107 b4108 b4109 d4022 d4038 d3813 d3917 d4054 d4074
          omega
        have d4110 : (x 10 6 && x 10 12).toNat = 0 := by
          have r4111 := hand1 (x 10 6) (x 10 12)
          have b4112 := hb (x 10 6)
          have b4113 := hb (x 10 6 && x 10 12)
          clear * - r4111 b4112 b4113 d4094
          omega
        have d4114 : (x 10 6 && x 10 10).toNat = 0 := by
          have r4115 := hand1 (x 10 6) (x 10 10)
          have b4116 := hb (x 10 6)
          have b4117 := hb (x 10 6 && x 10 10)
          clear * - r4115 b4116 b4117 d4094
          omega
        have d4118 : (x 9 7).toNat = 0 := by
          have r4119 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4120 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e4121 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e4122 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e4123 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e4124 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e4125 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have b4126 := hb (x 9 7)
          have b4127 := hb (x 10 6)
          have b4128 := hb (x 11 5)
          have b4129 := hb (x 12 4)
          have b4130 := hb (x 13 11)
          have b4131 := hb (x 14 10)
          have b4132 := hb (x 15 9)
          have b4133 := hb (x 16 8)
          clear * - r4119 e4120 e4121 e4122 e4123 e4124 e4125 b4126 b4127 b4128 b4129 b4130 b4131 b4132 b4133 d4022 d4038 d3813 d3917 d4054 d4074 d4094
          omega
        have d4134 : (x 9 7 && x 9 13).toNat = 0 := by
          have r4135 := hand1 (x 9 7) (x 9 13)
          have b4136 := hb (x 9 7)
          have b4137 := hb (x 9 7 && x 9 13)
          clear * - r4135 b4136 b4137 d4118
          omega
        have d4138 : (x 9 7 && x 9 11).toNat = 0 := by
          have r4139 := hand1 (x 9 7) (x 9 11)
          have b4140 := hb (x 9 7)
          have b4141 := hb (x 9 7 && x 9 11)
          clear * - r4139 b4140 b4141 d4118
          omega
        have d4142 : (x 8 6).toNat = 0 := by
          have r4143 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4144 := hb (x 0 14)
          have b4145 := hb (x 1 13)
          have b4146 := hb (x 2 12)
          have b4147 := hb (x 3 11)
          have b4148 := hb (x 4 10)
          have b4149 := hb (x 5 9)
          have b4150 := hb (x 6 8)
          have b4151 := hb (x 7 7)
          have b4152 := hb (x 8 6)
          have b4153 := hb (x 9 5)
          have b4154 := hb (x 10 4)
          have b4155 := hb (x 11 3)
          have b4156 := hb (x 12 2)
          have b4157 := hb (x 13 1)
          clear * - r4143 b4144 b4145 b4146 b4147 b4148 b4149 b4150 b4151 b4152 b4153 b4154 b4155 b4156 b4157 d3777 d3817 d3845 d3873 d3893 g52 g48 g39
          omega
        have d4158 : (x 8 1 && x 8 6).toNat = 0 := by
          have r4159 := hand2 (x 8 1) (x 8 6)
          have b4160 := hb (x 8 6)
          have b4161 := hb (x 8 1 && x 8 6)
          clear * - r4159 b4160 b4161 d4142
          omega
        have d4162 : (x 7 7).toNat = 0 := by
          have r4163 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4164 := hb (x 0 14)
          have b4165 := hb (x 1 13)
          have b4166 := hb (x 2 12)
          have b4167 := hb (x 3 11)
          have b4168 := hb (x 4 10)
          have b4169 := hb (x 5 9)
          have b4170 := hb (x 6 8)
          have b4171 := hb (x 7 7)
          have b4172 := hb (x 8 6)
          have b4173 := hb (x 9 5)
          have b4174 := hb (x 10 4)
          have b4175 := hb (x 11 3)
          have b4176 := hb (x 12 2)
          have b4177 := hb (x 13 1)
          clear * - r4163 b4164 b4165 b4166 b4167 b4168 b4169 b4170 b4171 b4172 b4173 b4174 b4175 b4176 b4177 d3777 d3817 d3845 d3873 d3893 d4142 g52 g48 g39
          omega
        have d4178 : (x 7 2 && x 7 7).toNat = 0 := by
          have r4179 := hand2 (x 7 2) (x 7 7)
          have b4180 := hb (x 7 7)
          have b4181 := hb (x 7 2 && x 7 7)
          clear * - r4179 b4180 b4181 d4162
          omega
        have d4182 : (x 6 8).toNat = 0 := by
          have r4183 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4184 := hb (x 0 14)
          have b4185 := hb (x 1 13)
          have b4186 := hb (x 2 12)
          have b4187 := hb (x 3 11)
          have b4188 := hb (x 4 10)
          have b4189 := hb (x 5 9)
          have b4190 := hb (x 6 8)
          have b4191 := hb (x 7 7)
          have b4192 := hb (x 8 6)
          have b4193 := hb (x 9 5)
          have b4194 := hb (x 10 4)
          have b4195 := hb (x 11 3)
          have b4196 := hb (x 12 2)
          have b4197 := hb (x 13 1)
          clear * - r4183 b4184 b4185 b4186 b4187 b4188 b4189 b4190 b4191 b4192 b4193 b4194 b4195 b4196 b4197 d3777 d3817 d3845 d3873 d3893 d4142 d4162 g52 g48 g39
          omega
        have d4198 : (x 6 3 && x 6 8).toNat = 0 := by
          have r4199 := hand2 (x 6 3) (x 6 8)
          have b4200 := hb (x 6 8)
          have b4201 := hb (x 6 3 && x 6 8)
          clear * - r4199 b4200 b4201 d4182
          omega
        have d4202 : (x 2 7 && x 2 12).toNat = 1 := by
          have r4203 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4204 := hb (x (-1) 10)
          have b4205 := hb (x 9 5)
          have b4206 := hb (x 8 1 && x 8 6)
          have b4207 := hb (x 7 2 && x 7 7)
          have b4208 := hb (x 6 3 && x 6 8)
          have b4209 := hb (x 5 4 && x 5 9)
          have b4210 := hb (x 4 5 && x 4 10)
          have b4211 := hb (x 3 6 && x 3 11)
          have b4212 := hb (x 2 7 && x 2 12)
          have b4213 := hb (x 1 8 && x 1 13)
          have b4214 := hb (x 0 9 && x 0 14)
          clear * - r4203 b4204 b4205 b4206 b4207 b4208 b4209 b4210 b4211 b4212 b4213 b4214 d3893 d4158 d4178 d4198 g100 g101 g102 g103 g104 g28
          omega
        have d4215 : (x 2 7).toNat = 1 := by
          have r4216 := hand1 (x 2 7) (x 2 12)
          have b4217 := hb (x 2 7)
          have b4218 := hb (x 2 7 && x 2 12)
          clear * - r4216 b4217 b4218 d4202
          omega
        have d4219 : (x 9 8).toNat = 0 := by
          have r4220 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4221 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e4222 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e4223 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e4224 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e4225 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e4226 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b4227 := hb (x 2 7)
          have b4228 := hb (x 3 6)
          have b4229 := hb (x 4 5)
          have b4230 := hb (x 5 4)
          have b4231 := hb (x 6 11)
          have b4232 := hb (x 7 10)
          have b4233 := hb (x 8 9)
          have b4234 := hb (x 9 8)
          clear * - r4220 e4221 e4222 e4223 e4224 e4225 e4226 b4227 b4228 b4229 b4230 b4231 b4232 b4233 b4234 g67 g64 g58 d4215
          omega
        have d4235 : (x 8 9).toNat = 0 := by
          have r4236 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4237 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e4238 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e4239 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e4240 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e4241 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e4242 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b4243 := hb (x 2 7)
          have b4244 := hb (x 3 6)
          have b4245 := hb (x 4 5)
          have b4246 := hb (x 5 4)
          have b4247 := hb (x 6 11)
          have b4248 := hb (x 7 10)
          have b4249 := hb (x 8 9)
          have b4250 := hb (x 9 8)
          clear * - r4236 e4237 e4238 e4239 e4240 e4241 e4242 b4243 b4244 b4245 b4246 b4247 b4248 b4249 b4250 d4219 g67 g64 g58 d4215
          omega
        have d4251 : (x 7 10).toNat = 0 := by
          have r4252 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4253 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e4254 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e4255 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e4256 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e4257 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e4258 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b4259 := hb (x 2 7)
          have b4260 := hb (x 3 6)
          have b4261 := hb (x 4 5)
          have b4262 := hb (x 5 4)
          have b4263 := hb (x 6 11)
          have b4264 := hb (x 7 10)
          have b4265 := hb (x 8 9)
          have b4266 := hb (x 9 8)
          clear * - r4252 e4253 e4254 e4255 e4256 e4257 e4258 b4259 b4260 b4261 b4262 b4263 b4264 b4265 b4266 d4219 d4235 g67 g64 g58 d4215
          omega
        have d4267 : (x 7 1 && x 7 10).toNat = 0 := by
          have r4268 := hand2 (x 7 1) (x 7 10)
          have b4269 := hb (x 7 10)
          have b4270 := hb (x 7 1 && x 7 10)
          clear * - r4268 b4269 b4270 d4251
          omega
        have d4271 : (x 6 11).toNat = 0 := by
          have r4272 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4273 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e4274 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e4275 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e4276 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e4277 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e4278 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have b4279 := hb (x 2 7)
          have b4280 := hb (x 3 6)
          have b4281 := hb (x 4 5)
          have b4282 := hb (x 5 4)
          have b4283 := hb (x 6 11)
          have b4284 := hb (x 7 10)
          have b4285 := hb (x 8 9)
          have b4286 := hb (x 9 8)
          clear * - r4272 e4273 e4274 e4275 e4276 e4277 e4278 b4279 b4280 b4281 b4282 b4283 b4284 b4285 b4286 d4219 d4235 d4251 g67 g64 g58 d4215
          omega
        have d4287 : (x 6 1 && x 6 11).toNat = 0 := by
          have r4288 := hand2 (x 6 1) (x 6 11)
          have b4289 := hb (x 6 11)
          have b4290 := hb (x 6 1 && x 6 11)
          clear * - r4288 b4289 b4290 d4271
          omega
        have d4291 : (x 2 5).toNat = 1 := by
          have r4292 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4293 := hb (x 2 5)
          have b4294 := hb (x 7 10)
          have b4295 := hb (x 6 1 && x 6 11)
          have b4296 := hb (x 5 2 && x 5 12)
          have b4297 := hb (x 4 3 && x 4 13)
          have b4298 := hb (x 3 4 && x 3 14)
          clear * - r4292 b4293 b4294 b4295 b4296 b4297 b4298 d4251 d4287 g154 g155 g156
          omega
        have d4299 : (x 7 8).toNat = 0 := by
          have r4300 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4301 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e4302 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e4303 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e4304 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e4305 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e4306 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b4307 := hb (x 0 7)
          have b4308 := hb (x 1 6)
          have b4309 := hb (x 2 5)
          have b4310 := hb (x 3 4)
          have b4311 := hb (x 4 11)
          have b4312 := hb (x 5 10)
          have b4313 := hb (x 6 9)
          have b4314 := hb (x 7 8)
          clear * - r4300 e4301 e4302 e4303 e4304 e4305 e4306 b4307 b4308 b4309 b4310 b4311 b4312 b4313 b4314 g56 d4291 g43 g34
          omega
        have d4315 : (x 6 9).toNat = 0 := by
          have r4316 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4317 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e4318 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e4319 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e4320 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e4321 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e4322 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b4323 := hb (x 0 7)
          have b4324 := hb (x 1 6)
          have b4325 := hb (x 2 5)
          have b4326 := hb (x 3 4)
          have b4327 := hb (x 4 11)
          have b4328 := hb (x 5 10)
          have b4329 := hb (x 6 9)
          have b4330 := hb (x 7 8)
          clear * - r4316 e4317 e4318 e4319 e4320 e4321 e4322 b4323 b4324 b4325 b4326 b4327 b4328 b4329 b4330 d4299 g56 d4291 g43 g34
          omega
        have d4331 : (x 5 10).toNat = 0 := by
          have r4332 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4333 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e4334 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e4335 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e4336 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e4337 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e4338 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b4339 := hb (x 0 7)
          have b4340 := hb (x 1 6)
          have b4341 := hb (x 2 5)
          have b4342 := hb (x 3 4)
          have b4343 := hb (x 4 11)
          have b4344 := hb (x 5 10)
          have b4345 := hb (x 6 9)
          have b4346 := hb (x 7 8)
          clear * - r4332 e4333 e4334 e4335 e4336 e4337 e4338 b4339 b4340 b4341 b4342 b4343 b4344 b4345 b4346 d4299 d4315 g56 d4291 g43 g34
          omega
        have d4347 : (x 4 11).toNat = 0 := by
          have r4348 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4349 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
          have e4350 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
          have e4351 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
          have e4352 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
          have e4353 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
          have e4354 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
          have b4355 := hb (x 0 7)
          have b4356 := hb (x 1 6)
          have b4357 := hb (x 2 5)
          have b4358 := hb (x 3 4)
          have b4359 := hb (x 4 11)
          have b4360 := hb (x 5 10)
          have b4361 := hb (x 6 9)
          have b4362 := hb (x 7 8)
          clear * - r4348 e4349 e4350 e4351 e4352 e4353 e4354 b4355 b4356 b4357 b4358 b4359 b4360 b4361 b4362 d4299 d4315 d4331 g56 d4291 g43 g34
          omega
        have d4363 : (x 6 2 && x 6 11).toNat = 0 := by
          have r4364 := hand2 (x 6 2) (x 6 11)
          have b4365 := hb (x 6 11)
          have b4366 := hb (x 6 2 && x 6 11)
          clear * - r4364 b4365 b4366 d4271
          omega
        have d4367 : (x 2 6).toNat = 1 := by
          have r4368 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4369 := hb (x 2 6)
          have b4370 := hb (x 8 9)
          have b4371 := hb (x 7 1 && x 7 10)
          have b4372 := hb (x 6 2 && x 6 11)
          have b4373 := hb (x 5 3 && x 5 12)
          have b4374 := hb (x 4 4 && x 4 13)
          have b4375 := hb (x 3 5 && x 3 14)
          clear * - r4368 b4369 b4370 b4371 b4372 b4373 b4374 b4375 d4235 d4267 d4363 g139 g140 g141
          omega
        have d4376 : (x 8 8).toNat = 0 := by
          have r4377 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4378 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e4379 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e4380 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e4381 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e4382 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e4383 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b4384 := hb (x 1 7)
          have b4385 := hb (x 2 6)
          have b4386 := hb (x 3 5)
          have b4387 := hb (x 4 4)
          have b4388 := hb (x 5 11)
          have b4389 := hb (x 6 10)
          have b4390 := hb (x 7 9)
          have b4391 := hb (x 8 8)
          clear * - r4377 e4378 e4379 e4380 e4381 e4382 e4383 b4384 b4385 b4386 b4387 b4388 b4389 b4390 b4391 g63 g57 d4367 f1543
          omega
        have d4392 : (x 8 8 && x 8 14).toNat = 0 := by
          have r4393 := hand1 (x 8 8) (x 8 14)
          have b4394 := hb (x 8 8)
          have b4395 := hb (x 8 8 && x 8 14)
          clear * - r4393 b4394 b4395 d4376
          omega
        have d4396 : (x 8 8 && x 8 12).toNat = 0 := by
          have r4397 := hand1 (x 8 8) (x 8 12)
          have b4398 := hb (x 8 8)
          have b4399 := hb (x 8 8 && x 8 12)
          clear * - r4397 b4398 b4399 d4376
          omega
        have d4400 : (x 7 9).toNat = 0 := by
          have r4401 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4402 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e4403 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e4404 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e4405 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e4406 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e4407 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b4408 := hb (x 1 7)
          have b4409 := hb (x 2 6)
          have b4410 := hb (x 3 5)
          have b4411 := hb (x 4 4)
          have b4412 := hb (x 5 11)
          have b4413 := hb (x 6 10)
          have b4414 := hb (x 7 9)
          have b4415 := hb (x 8 8)
          clear * - r4401 e4402 e4403 e4404 e4405 e4406 e4407 b4408 b4409 b4410 b4411 b4412 b4413 b4414 b4415 d4376 g63 g57 d4367 f1543
          omega
        have d4416 : (x 7 9 && x 7 13).toNat = 0 := by
          have r4417 := hand1 (x 7 9) (x 7 13)
          have b4418 := hb (x 7 9)
          have b4419 := hb (x 7 9 && x 7 13)
          clear * - r4417 b4418 b4419 d4400
          omega
        have d4420 : (x 6 10).toNat = 0 := by
          have r4421 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4422 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e4423 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e4424 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e4425 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e4426 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e4427 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b4428 := hb (x 1 7)
          have b4429 := hb (x 2 6)
          have b4430 := hb (x 3 5)
          have b4431 := hb (x 4 4)
          have b4432 := hb (x 5 11)
          have b4433 := hb (x 6 10)
          have b4434 := hb (x 7 9)
          have b4435 := hb (x 8 8)
          clear * - r4421 e4422 e4423 e4424 e4425 e4426 e4427 b4428 b4429 b4430 b4431 b4432 b4433 b4434 b4435 d4376 d4400 g63 g57 d4367 f1543
          omega
        have d4436 : (x 5 11).toNat = 0 := by
          have r4437 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4438 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e4439 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e4440 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e4441 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e4442 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e4443 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b4444 := hb (x 1 7)
          have b4445 := hb (x 2 6)
          have b4446 := hb (x 3 5)
          have b4447 := hb (x 4 4)
          have b4448 := hb (x 5 11)
          have b4449 := hb (x 6 10)
          have b4450 := hb (x 7 9)
          have b4451 := hb (x 8 8)
          clear * - r4437 e4438 e4439 e4440 e4441 e4442 e4443 b4444 b4445 b4446 b4447 b4448 b4449 b4450 b4451 d4376 d4400 d4420 g63 g57 d4367 f1543
          omega
        have d4452 : (x 13 3 && x 13 7).toNat = 1 := by
          have r4453 : 1 ≤ (x 16 4).toNat + (x 15 1 && x 15 5).toNat + (x 14 2 && x 14 6).toNat + (x 13 3 && x 13 7).toNat + (x 12 4 && x 12 8).toNat + (x 11 5 && x 11 9).toNat + (x 10 6 && x 10 10).toNat + (x 9 7 && x 9 11).toNat + (x 8 8 && x 8 12).toNat + (x 7 9 && x 7 13).toNat + (x 6 10 && x 6 14).toNat + (x 5 11).toNat := by have q := hcov4 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4454 : (x 15 1 && x 15 5).toNat = (x 15 5).toNat := handr _ _ (fun h => hp13 15 (hp5 15 (h)))
          have e4455 : (x 6 10 && x 6 14).toNat = (x 6 10).toNat := handl _ _ (fun h => hp2 6 (hp10 6 (h)))
          have b4456 := hb (x 5 11)
          have b4457 := hb (x 6 10)
          have b4458 := hb (x 15 5)
          have b4459 := hb (x 16 4)
          have b4460 := hb (x 14 2 && x 14 6)
          have b4461 := hb (x 13 3 && x 13 7)
          have b4462 := hb (x 12 4 && x 12 8)
          have b4463 := hb (x 11 5 && x 11 9)
          have b4464 := hb (x 10 6 && x 10 10)
          have b4465 := hb (x 9 7 && x 9 11)
          have b4466 := hb (x 8 8 && x 8 12)
          have b4467 := hb (x 7 9 && x 7 13)
          clear * - r4453 e4454 e4455 b4456 b4457 b4458 b4459 b4460 b4461 b4462 b4463 b4464 b4465 b4466 b4467 d3941 d3965 d3801 d4070 d4090 d4114 d4138 d4396 d4416 d4420 d4436
          omega
        have d4468 : (x 13 7).toNat = 1 := by
          have r4469 := hand2 (x 13 3) (x 13 7)
          have b4470 := hb (x 13 7)
          have b4471 := hb (x 13 3 && x 13 7)
          clear * - r4469 b4470 b4471 d4452
          omega
        have d4472 : (x 20 8).toNat = 0 := by
          have r4473 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4474 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
          have e4475 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
          have e4476 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
          have e4477 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
          have e4478 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
          have e4479 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
          have b4480 := hb (x 13 7)
          have b4481 := hb (x 14 6)
          have b4482 := hb (x 15 5)
          have b4483 := hb (x 16 4)
          have b4484 := hb (x 17 11)
          have b4485 := hb (x 18 10)
          have b4486 := hb (x 19 9)
          have b4487 := hb (x 20 8)
          clear * - r4473 e4474 e4475 e4476 e4477 e4478 e4479 b4480 b4481 b4482 b4483 b4484 b4485 b4486 b4487 d3941 d3965 d3797 d4468
          omega
        have d4488 : (x 19 9).toNat = 0 := by
          have r4489 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4490 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
          have e4491 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
          have e4492 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
          have e4493 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
          have e4494 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
          have e4495 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
          have b4496 := hb (x 13 7)
          have b4497 := hb (x 14 6)
          have b4498 := hb (x 15 5)
          have b4499 := hb (x 16 4)
          have b4500 := hb (x 17 11)
          have b4501 := hb (x 18 10)
          have b4502 := hb (x 19 9)
          have b4503 := hb (x 20 8)
          clear * - r4489 e4490 e4491 e4492 e4493 e4494 e4495 b4496 b4497 b4498 b4499 b4500 b4501 b4502 b4503 d4472 d3941 d3965 d3797 d4468
          omega
        have d4504 : (x 18 10).toNat = 0 := by
          have r4505 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4506 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
          have e4507 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
          have e4508 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
          have e4509 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
          have e4510 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
          have e4511 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
          have b4512 := hb (x 13 7)
          have b4513 := hb (x 14 6)
          have b4514 := hb (x 15 5)
          have b4515 := hb (x 16 4)
          have b4516 := hb (x 17 11)
          have b4517 := hb (x 18 10)
          have b4518 := hb (x 19 9)
          have b4519 := hb (x 20 8)
          clear * - r4505 e4506 e4507 e4508 e4509 e4510 e4511 b4512 b4513 b4514 b4515 b4516 b4517 b4518 b4519 d4472 d4488 d3941 d3965 d3797 d4468
          omega
        have d4520 : (x 18 1 && x 18 10).toNat = 0 := by
          have r4521 := hand2 (x 18 1) (x 18 10)
          have b4522 := hb (x 18 10)
          have b4523 := hb (x 18 1 && x 18 10)
          clear * - r4521 b4522 b4523 d4504
          omega
        have d4524 : (x 17 11).toNat = 0 := by
          have r4525 : (x 20 8).toNat + (x 19 1 && x 19 9).toNat + (x 18 2 && x 18 10).toNat + (x 17 3 && x 17 11).toNat + (x 16 4 && x 16 12).toNat + (x 15 5 && x 15 13).toNat + (x 14 6 && x 14 14).toNat + (x 13 7).toNat = 1 := by have q := hd8 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4526 : (x 19 1 && x 19 9).toNat = (x 19 9).toNat := handr _ _ (fun h => hp9 19 (h))
          have e4527 : (x 18 2 && x 18 10).toNat = (x 18 10).toNat := handr _ _ (fun h => hp10 18 (h))
          have e4528 : (x 17 3 && x 17 11).toNat = (x 17 11).toNat := handr _ _ (fun h => hp11 17 (h))
          have e4529 : (x 16 4 && x 16 12).toNat = (x 16 4).toNat := handl _ _ (fun h => hp4 16 (h))
          have e4530 : (x 15 5 && x 15 13).toNat = (x 15 5).toNat := handl _ _ (fun h => hp5 15 (h))
          have e4531 : (x 14 6 && x 14 14).toNat = (x 14 6).toNat := handl _ _ (fun h => hp6 14 (h))
          have b4532 := hb (x 13 7)
          have b4533 := hb (x 14 6)
          have b4534 := hb (x 15 5)
          have b4535 := hb (x 16 4)
          have b4536 := hb (x 17 11)
          have b4537 := hb (x 18 10)
          have b4538 := hb (x 19 9)
          have b4539 := hb (x 20 8)
          clear * - r4525 e4526 e4527 e4528 e4529 e4530 e4531 b4532 b4533 b4534 b4535 b4536 b4537 b4538 b4539 d4472 d4488 d4504 d3941 d3965 d3797 d4468
          omega
        have d4540 : (x 17 1 && x 17 11).toNat = 0 := by
          have r4541 := hand2 (x 17 1) (x 17 11)
          have b4542 := hb (x 17 11)
          have b4543 := hb (x 17 1 && x 17 11)
          clear * - r4541 b4542 b4543 d4524
          omega
        have d4544 : (x 13 5).toNat = 1 := by
          have r4545 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4546 := hb (x 13 5)
          have b4547 := hb (x 18 10)
          have b4548 := hb (x 17 1 && x 17 11)
          have b4549 := hb (x 16 2 && x 16 12)
          have b4550 := hb (x 15 3 && x 15 13)
          have b4551 := hb (x 14 4 && x 14 14)
          clear * - r4545 b4546 b4547 b4548 b4549 b4550 b4551 d4504 d4540 d3933 d3957 d3789
          omega
        have d4552 : (x 18 8).toNat = 0 := by
          have r4553 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4554 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
          have e4555 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
          have e4556 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
          have e4557 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
          have e4558 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
          have e4559 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
          have b4560 := hb (x 11 7)
          have b4561 := hb (x 12 6)
          have b4562 := hb (x 13 5)
          have b4563 := hb (x 14 4)
          have b4564 := hb (x 15 11)
          have b4565 := hb (x 16 10)
          have b4566 := hb (x 17 9)
          have b4567 := hb (x 18 8)
          clear * - r4553 e4554 e4555 e4556 e4557 e4558 e4559 b4560 b4561 b4562 b4563 b4564 b4565 b4566 b4567 d4544
          omega
        have d4568 : (x 17 9).toNat = 0 := by
          have r4569 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4570 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
          have e4571 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
          have e4572 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
          have e4573 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
          have e4574 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
          have e4575 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
          have b4576 := hb (x 11 7)
          have b4577 := hb (x 12 6)
          have b4578 := hb (x 13 5)
          have b4579 := hb (x 14 4)
          have b4580 := hb (x 15 11)
          have b4581 := hb (x 16 10)
          have b4582 := hb (x 17 9)
          have b4583 := hb (x 18 8)
          clear * - r4569 e4570 e4571 e4572 e4573 e4574 e4575 b4576 b4577 b4578 b4579 b4580 b4581 b4582 b4583 d4552 d4544
          omega
        have d4584 : (x 16 10).toNat = 0 := by
          have r4585 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4586 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
          have e4587 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
          have e4588 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
          have e4589 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
          have e4590 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
          have e4591 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
          have b4592 := hb (x 11 7)
          have b4593 := hb (x 12 6)
          have b4594 := hb (x 13 5)
          have b4595 := hb (x 14 4)
          have b4596 := hb (x 15 11)
          have b4597 := hb (x 16 10)
          have b4598 := hb (x 17 9)
          have b4599 := hb (x 18 8)
          clear * - r4585 e4586 e4587 e4588 e4589 e4590 e4591 b4592 b4593 b4594 b4595 b4596 b4597 b4598 b4599 d4552 d4568 d4544
          omega
        have d4600 : (x 15 11).toNat = 0 := by
          have r4601 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4602 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
          have e4603 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
          have e4604 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
          have e4605 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
          have e4606 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
          have e4607 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
          have b4608 := hb (x 11 7)
          have b4609 := hb (x 12 6)
          have b4610 := hb (x 13 5)
          have b4611 := hb (x 14 4)
          have b4612 := hb (x 15 11)
          have b4613 := hb (x 16 10)
          have b4614 := hb (x 17 9)
          have b4615 := hb (x 18 8)
          clear * - r4601 e4602 e4603 e4604 e4605 e4606 e4607 b4608 b4609 b4610 b4611 b4612 b4613 b4614 b4615 d4552 d4568 d4584 d4544
          omega
        have d4616 : (x 14 4).toNat = 0 := by
          have r4617 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4618 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
          have e4619 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
          have e4620 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
          have e4621 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
          have e4622 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
          have e4623 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
          have b4624 := hb (x 11 7)
          have b4625 := hb (x 12 6)
          have b4626 := hb (x 13 5)
          have b4627 := hb (x 14 4)
          have b4628 := hb (x 15 11)
          have b4629 := hb (x 16 10)
          have b4630 := hb (x 17 9)
          have b4631 := hb (x 18 8)
          clear * - r4617 e4618 e4619 e4620 e4621 e4622 e4623 b4624 b4625 b4626 b4627 b4628 b4629 b4630 b4631 d4552 d4568 d4584 d4600 d4544
          omega
        have d4632 : (x 12 6).toNat = 0 := by
          have r4633 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4634 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
          have e4635 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
          have e4636 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
          have e4637 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
          have e4638 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
          have e4639 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
          have b4640 := hb (x 11 7)
          have b4641 := hb (x 12 6)
          have b4642 := hb (x 13 5)
          have b4643 := hb (x 14 4)
          have b4644 := hb (x 15 11)
          have b4645 := hb (x 16 10)
          have b4646 := hb (x 17 9)
          have b4647 := hb (x 18 8)
          clear * - r4633 e4634 e4635 e4636 e4637 e4638 e4639 b4640 b4641 b4642 b4643 b4644 b4645 b4646 b4647 d4552 d4568 d4584 d4600 d4616 d4544
          omega
        have d4648 : (x 11 7).toNat = 0 := by
          have r4649 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4650 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
          have e4651 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
          have e4652 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
          have e4653 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
          have e4654 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
          have e4655 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
          have b4656 := hb (x 11 7)
          have b4657 := hb (x 12 6)
          have b4658 := hb (x 13 5)
          have b4659 := hb (x 14 4)
          have b4660 := hb (x 15 11)
          have b4661 := hb (x 16 10)
          have b4662 := hb (x 17 9)
          have b4663 := hb (x 18 8)
          clear * - r4649 e4650 e4651 e4652 e4653 e4654 e4655 b4656 b4657 b4658 b4659 b4660 b4661 b4662 b4663 d4552 d4568 d4584 d4600 d4616 d4544 d4632
          omega
        have d4664 : (x 17 2 && x 17 11).toNat = 0 := by
          have r4665 := hand2 (x 17 2) (x 17 11)
          have b4666 := hb (x 17 11)
          have b4667 := hb (x 17 2 && x 17 11)
          clear * - r4665 b4666 b4667 d4524
          omega
        have d4668 : (x 13 6).toNat = 1 := by
          have r4669 : 1 ≤ (x 19 9).toNat + (x 18 1 && x 18 10).toNat + (x 17 2 && x 17 11).toNat + (x 16 3 && x 16 12).toNat + (x 15 4 && x 15 13).toNat + (x 14 5 && x 14 14).toNat + (x 13 6).toNat := by have q := hcov9 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4670 := hb (x 13 6)
          have b4671 := hb (x 19 9)
          have b4672 := hb (x 18 1 && x 18 10)
          have b4673 := hb (x 17 2 && x 17 11)
          have b4674 := hb (x 16 3 && x 16 12)
          have b4675 := hb (x 15 4 && x 15 13)
          have b4676 := hb (x 14 5 && x 14 14)
          clear * - r4669 b4670 b4671 b4672 b4673 b4674 b4675 b4676 d4488 d4520 d4664 d3937 d3961 d3793
          omega
        have d4677 : (x 19 8).toNat = 0 := by
          have r4678 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4679 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e4680 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e4681 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e4682 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e4683 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e4684 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b4685 := hb (x 12 7)
          have b4686 := hb (x 13 6)
          have b4687 := hb (x 14 5)
          have b4688 := hb (x 15 4)
          have b4689 := hb (x 16 11)
          have b4690 := hb (x 17 10)
          have b4691 := hb (x 18 9)
          have b4692 := hb (x 19 8)
          clear * - r4678 e4679 e4680 e4681 e4682 e4683 e4684 b4685 b4686 b4687 b4688 b4689 b4690 b4691 b4692 d3990 d4006 d4668
          omega
        have d4693 : (x 18 9).toNat = 0 := by
          have r4694 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4695 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e4696 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e4697 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e4698 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e4699 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e4700 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b4701 := hb (x 12 7)
          have b4702 := hb (x 13 6)
          have b4703 := hb (x 14 5)
          have b4704 := hb (x 15 4)
          have b4705 := hb (x 16 11)
          have b4706 := hb (x 17 10)
          have b4707 := hb (x 18 9)
          have b4708 := hb (x 19 8)
          clear * - r4694 e4695 e4696 e4697 e4698 e4699 e4700 b4701 b4702 b4703 b4704 b4705 b4706 b4707 b4708 d4677 d3990 d4006 d4668
          omega
        have d4709 : (x 17 10).toNat = 0 := by
          have r4710 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4711 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e4712 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e4713 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e4714 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e4715 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e4716 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b4717 := hb (x 12 7)
          have b4718 := hb (x 13 6)
          have b4719 := hb (x 14 5)
          have b4720 := hb (x 15 4)
          have b4721 := hb (x 16 11)
          have b4722 := hb (x 17 10)
          have b4723 := hb (x 18 9)
          have b4724 := hb (x 19 8)
          clear * - r4710 e4711 e4712 e4713 e4714 e4715 e4716 b4717 b4718 b4719 b4720 b4721 b4722 b4723 b4724 d4677 d4693 d3990 d4006 d4668
          omega
        have d4725 : (x 16 11).toNat = 0 := by
          have r4726 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4727 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
          have e4728 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
          have e4729 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
          have e4730 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
          have e4731 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
          have e4732 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
          have b4733 := hb (x 12 7)
          have b4734 := hb (x 13 6)
          have b4735 := hb (x 14 5)
          have b4736 := hb (x 15 4)
          have b4737 := hb (x 16 11)
          have b4738 := hb (x 17 10)
          have b4739 := hb (x 18 9)
          have b4740 := hb (x 19 8)
          clear * - r4726 e4727 e4728 e4729 e4730 e4731 e4732 b4733 b4734 b4735 b4736 b4737 b4738 b4739 b4740 d4677 d4693 d4709 d3990 d4006 d4668
          omega
        have d4741 : (x 16 1 && x 16 11).toNat = 0 := by
          have r4742 := hand2 (x 16 1) (x 16 11)
          have b4743 := hb (x 16 11)
          have b4744 := hb (x 16 1 && x 16 11)
          clear * - r4742 b4743 b4744 d4725
          omega
        have d4745 : (x 13 4 && x 13 14).toNat = 1 := by
          have r4746 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := by have q := hcov10 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4747 := hb (x 12 5)
          have b4748 := hb (x 17 10)
          have b4749 := hb (x 16 1 && x 16 11)
          have b4750 := hb (x 15 2 && x 15 12)
          have b4751 := hb (x 14 3 && x 14 13)
          have b4752 := hb (x 13 4 && x 13 14)
          clear * - r4746 b4747 b4748 b4749 b4750 b4751 b4752 d4709 d4741 d3986 d4002 d3744
          omega
        have d4753 : (x 13 4).toNat = 1 := by
          have r4754 := hand1 (x 13 4) (x 13 14)
          have b4755 := hb (x 13 4)
          have b4756 := hb (x 13 4 && x 13 14)
          clear * - r4754 b4755 b4756 d4745
          omega
        have d4757 : (x 13 12).toNat = 1 := by
          have r4758 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b4759 := hb (x 13 4)
          have b4760 := hb (x 13 12)
          clear * - r4758 b4759 b4760 d4753
          omega
        have d4761 : (x 15 1).toNat = 1 := by
          have r4762 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4763 := hb (x 2 14)
          have b4764 := hb (x 3 13)
          have b4765 := hb (x 4 12)
          have b4766 := hb (x 5 11)
          have b4767 := hb (x 6 10)
          have b4768 := hb (x 7 9)
          have b4769 := hb (x 8 8)
          have b4770 := hb (x 9 7)
          have b4771 := hb (x 10 6)
          have b4772 := hb (x 11 5)
          have b4773 := hb (x 12 4)
          have b4774 := hb (x 13 3)
          have b4775 := hb (x 14 2)
          have b4776 := hb (x 15 1)
          clear * - r4762 b4763 b4764 b4765 b4766 b4767 b4768 b4769 b4770 b4771 b4772 b4773 b4774 b4775 b4776 d3805 d3921 d4054 d4074 d4094 d4118 d4376 d4400 d4420 d4436 g66 g61 g54
          omega
        have d4777 : (x 16 14).toNat = 0 := by
          have r4778 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4779 := hb (x 15 1)
          have b4780 := hb (x 16 14)
          clear * - r4778 b4779 b4780 d4761
          omega
        have d4781 : (x 16 1 && x 16 14).toNat = 0 := by
          have r4782 := hand2 (x 16 1) (x 16 14)
          have b4783 := hb (x 16 14)
          have b4784 := hb (x 16 1 && x 16 14)
          clear * - r4782 b4783 b4784 d4777
          omega
        have d4785 : (x 16 3 && x 16 14).toNat = 0 := by
          have r4786 := hand2 (x 16 3) (x 16 14)
          have b4787 := hb (x 16 14)
          have b4788 := hb (x 16 3 && x 16 14)
          clear * - r4786 b4787 b4788 d4777
          omega
        have d4789 : (x 16 6).toNat = 0 := by
          have r4790 : (x 16 6).toNat ≤ (x 16 14).toNat := himp _ _ (hp6 16)
          have b4791 := hb (x 16 6)
          have b4792 := hb (x 16 14)
          clear * - r4790 b4791 b4792 d4777
          omega
        have d4793 : (x 16 2).toNat = 0 := by
          have r4794 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
          have b4795 := hb (x 16 2)
          have b4796 := hb (x 16 14)
          clear * - r4794 b4795 b4796 d4777
          omega
        have d4797 : (x 16 2 && x 16 13).toNat = 0 := by
          have r4798 := hand1 (x 16 2) (x 16 13)
          have b4799 := hb (x 16 2)
          have b4800 := hb (x 16 2 && x 16 13)
          clear * - r4798 b4799 b4800 d4793
          omega
        have d4801 : (x 10 3).toNat = 0 := by
          have r4802 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4803 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e4804 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b4805 := hb (x 10 3)
          have b4806 := hb (x 11 2)
          have b4807 := hb (x 12 13)
          have b4808 := hb (x 13 12)
          clear * - r4802 e4803 e4804 b4805 b4806 b4807 b4808 d4757 d3740 d3748
          omega
        have d4809 : (x 10 3 && x 10 13).toNat = 0 := by
          have r4810 := hand1 (x 10 3) (x 10 13)
          have b4811 := hb (x 10 3)
          have b4812 := hb (x 10 3 && x 10 13)
          clear * - r4810 b4811 b4812 d4801
          omega
        have d4813 : (x 10 11).toNat = 0 := by
          have r4814 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
          have b4815 := hb (x 10 3)
          have b4816 := hb (x 10 11)
          clear * - r4814 b4815 b4816 d4801
          omega
        have d4817 : (x 10 1 && x 10 11).toNat = 0 := by
          have r4818 := hand2 (x 10 1) (x 10 11)
          have b4819 := hb (x 10 11)
          have b4820 := hb (x 10 1 && x 10 11)
          clear * - r4818 b4819 b4820 d4813
          omega
        have d4821 : (x 9 4).toNat = 0 := by
          have r4822 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4823 := hb (x (-1) 14)
          have b4824 := hb (x 0 13)
          have b4825 := hb (x 1 12)
          have b4826 := hb (x 2 11)
          have b4827 := hb (x 3 10)
          have b4828 := hb (x 4 9)
          have b4829 := hb (x 5 8)
          have b4830 := hb (x 6 7)
          have b4831 := hb (x 7 6)
          have b4832 := hb (x 8 5)
          have b4833 := hb (x 9 4)
          have b4834 := hb (x 10 3)
          have b4835 := hb (x 11 2)
          have b4836 := hb (x 12 1)
          clear * - r4822 b4823 b4824 b4825 b4826 b4827 b4828 b4829 b4830 b4831 b4832 b4833 b4834 b4835 b4836 d3716 d3748 d4801 g68 g65 g59 g51 g47 g38 f3715
          omega
        have d4837 : (x 9 4 && x 9 14).toNat = 0 := by
          have r4838 := hand1 (x 9 4) (x 9 14)
          have b4839 := hb (x 9 4)
          have b4840 := hb (x 9 4 && x 9 14)
          clear * - r4838 b4839 b4840 d4821
          omega
        have d4841 : (x 8 5).toNat = 0 := by
          have r4842 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4843 := hb (x (-1) 14)
          have b4844 := hb (x 0 13)
          have b4845 := hb (x 1 12)
          have b4846 := hb (x 2 11)
          have b4847 := hb (x 3 10)
          have b4848 := hb (x 4 9)
          have b4849 := hb (x 5 8)
          have b4850 := hb (x 6 7)
          have b4851 := hb (x 7 6)
          have b4852 := hb (x 8 5)
          have b4853 := hb (x 9 4)
          have b4854 := hb (x 10 3)
          have b4855 := hb (x 11 2)
          have b4856 := hb (x 12 1)
          clear * - r4842 b4843 b4844 b4845 b4846 b4847 b4848 b4849 b4850 b4851 b4852 b4853 b4854 b4855 b4856 d3716 d3748 d4801 d4821 g68 g65 g59 g51 g47 g38 f3715
          omega
        have d4857 : (x 13 10).toNat = 1 := by
          have r4858 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4859 := hb (x 8 5)
          have b4860 := hb (x 13 10)
          have b4861 := hb (x 12 1 && x 12 11)
          have b4862 := hb (x 11 2 && x 11 12)
          have b4863 := hb (x 10 3 && x 10 13)
          have b4864 := hb (x 9 4 && x 9 14)
          clear * - r4858 b4859 b4860 b4861 b4862 b4863 b4864 d3736 d3764 d4809 d4837 d4841
          omega
        have d4865 : (x 15 8).toNat = 0 := by
          have r4866 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4867 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e4868 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e4869 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e4870 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e4871 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e4872 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b4873 := hb (x 8 7)
          have b4874 := hb (x 9 6)
          have b4875 := hb (x 10 5)
          have b4876 := hb (x 11 4)
          have b4877 := hb (x 12 11)
          have b4878 := hb (x 13 10)
          have b4879 := hb (x 14 9)
          have b4880 := hb (x 15 8)
          clear * - r4866 e4867 e4868 e4869 e4870 e4871 e4872 b4873 b4874 b4875 b4876 b4877 b4878 b4879 b4880 d4857 d4018
          omega
        have d4881 : (x 14 9).toNat = 0 := by
          have r4882 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4883 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e4884 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e4885 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e4886 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e4887 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e4888 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b4889 := hb (x 8 7)
          have b4890 := hb (x 9 6)
          have b4891 := hb (x 10 5)
          have b4892 := hb (x 11 4)
          have b4893 := hb (x 12 11)
          have b4894 := hb (x 13 10)
          have b4895 := hb (x 14 9)
          have b4896 := hb (x 15 8)
          clear * - r4882 e4883 e4884 e4885 e4886 e4887 e4888 b4889 b4890 b4891 b4892 b4893 b4894 b4895 b4896 d4865 d4857 d4018
          omega
        have d4897 : (x 11 4).toNat = 0 := by
          have r4898 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4899 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e4900 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e4901 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e4902 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e4903 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e4904 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b4905 := hb (x 8 7)
          have b4906 := hb (x 9 6)
          have b4907 := hb (x 10 5)
          have b4908 := hb (x 11 4)
          have b4909 := hb (x 12 11)
          have b4910 := hb (x 13 10)
          have b4911 := hb (x 14 9)
          have b4912 := hb (x 15 8)
          clear * - r4898 e4899 e4900 e4901 e4902 e4903 e4904 b4905 b4906 b4907 b4908 b4909 b4910 b4911 b4912 d4865 d4881 d4857 d4018
          omega
        have d4913 : (x 10 5).toNat = 0 := by
          have r4914 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4915 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e4916 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e4917 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e4918 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e4919 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e4920 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b4921 := hb (x 8 7)
          have b4922 := hb (x 9 6)
          have b4923 := hb (x 10 5)
          have b4924 := hb (x 11 4)
          have b4925 := hb (x 12 11)
          have b4926 := hb (x 13 10)
          have b4927 := hb (x 14 9)
          have b4928 := hb (x 15 8)
          clear * - r4914 e4915 e4916 e4917 e4918 e4919 e4920 b4921 b4922 b4923 b4924 b4925 b4926 b4927 b4928 d4865 d4881 d4857 d4018 d4897
          omega
        have d4929 : (x 9 6).toNat = 0 := by
          have r4930 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4931 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e4932 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e4933 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e4934 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e4935 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e4936 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b4937 := hb (x 8 7)
          have b4938 := hb (x 9 6)
          have b4939 := hb (x 10 5)
          have b4940 := hb (x 11 4)
          have b4941 := hb (x 12 11)
          have b4942 := hb (x 13 10)
          have b4943 := hb (x 14 9)
          have b4944 := hb (x 15 8)
          clear * - r4930 e4931 e4932 e4933 e4934 e4935 e4936 b4937 b4938 b4939 b4940 b4941 b4942 b4943 b4944 d4865 d4881 d4857 d4018 d4897 d4913
          omega
        have d4945 : (x 8 7).toNat = 0 := by
          have r4946 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4947 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e4948 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e4949 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e4950 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e4951 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e4952 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have b4953 := hb (x 8 7)
          have b4954 := hb (x 9 6)
          have b4955 := hb (x 10 5)
          have b4956 := hb (x 11 4)
          have b4957 := hb (x 12 11)
          have b4958 := hb (x 13 10)
          have b4959 := hb (x 14 9)
          have b4960 := hb (x 15 8)
          clear * - r4946 e4947 e4948 e4949 e4950 e4951 e4952 b4953 b4954 b4955 b4956 b4957 b4958 b4959 b4960 d4865 d4881 d4857 d4018 d4897 d4913 d4929
          omega
        have d4961 : (x 14 1).toNat = 1 := by
          have r4962 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4963 := hb (x 1 14)
          have b4964 := hb (x 2 13)
          have b4965 := hb (x 3 12)
          have b4966 := hb (x 4 11)
          have b4967 := hb (x 5 10)
          have b4968 := hb (x 6 9)
          have b4969 := hb (x 7 8)
          have b4970 := hb (x 8 7)
          have b4971 := hb (x 9 6)
          have b4972 := hb (x 10 5)
          have b4973 := hb (x 11 4)
          have b4974 := hb (x 12 3)
          have b4975 := hb (x 13 2)
          have b4976 := hb (x 14 1)
          clear * - r4962 b4963 b4964 b4965 b4966 b4967 b4968 b4969 b4970 b4971 b4972 b4973 b4974 b4975 b4976 d3973 d4010 d4897 d4913 d4929 d4945 d4299 d4315 d4331 d4347 g60 g53 g49
          omega
        have d4977 : (x 15 14).toNat = 0 := by
          have r4978 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4979 := hb (x 14 1)
          have b4980 := hb (x 15 14)
          clear * - r4978 b4979 b4980 d4961
          omega
        have d4981 : (x 15 1 && x 15 14).toNat = 0 := by
          have r4982 := hand2 (x 15 1) (x 15 14)
          have b4983 := hb (x 15 14)
          have b4984 := hb (x 15 1 && x 15 14)
          clear * - r4982 b4983 b4984 d4977
          omega
        have d4985 : (x 16 13).toNat = 1 := by
          have r4986 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4987 := hb (x 14 2)
          have b4988 := hb (x 16 13)
          have b4989 := hb (x 15 1 && x 15 14)
          clear * - r4986 b4987 b4988 b4989 d4981 d3805
          omega
        have d4990 : (x 16 1).toNat = 1 := by
          have r4991 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
          have b4992 := hb (x 16 1)
          have b4993 := hb (x 16 13)
          clear * - r4991 b4992 b4993 d4985
          omega
        have d4994 : (x 17 14).toNat = 0 := by
          have r4995 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b4996 := hb (x 16 1)
          have b4997 := hb (x 17 14)
          clear * - r4995 b4996 b4997 d4990
          omega
        have d4998 : (x 17 1 && x 17 14).toNat = 0 := by
          have r4999 := hand2 (x 17 1) (x 17 14)
          have b5000 := hb (x 17 14)
          have b5001 := hb (x 17 1 && x 17 14)
          clear * - r4999 b5000 b5001 d4994
          omega
        have d5002 : (x 18 13).toNat = 1 := by
          have r5003 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5004 := hb (x 16 2)
          have b5005 := hb (x 18 13)
          have b5006 := hb (x 17 1 && x 17 14)
          clear * - r5003 b5004 b5005 b5006 d4998 d4793
          omega
        have d5007 : (x 19 12).toNat = 0 := by
          have r5008 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5009 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e5010 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b5011 := hb (x 16 3)
          have b5012 := hb (x 17 2)
          have b5013 := hb (x 18 13)
          have b5014 := hb (x 19 12)
          clear * - r5008 e5009 e5010 b5011 b5012 b5013 b5014 d5002
          omega
        have d5015 : (x 19 1 && x 19 12).toNat = 0 := by
          have r5016 := hand2 (x 19 1) (x 19 12)
          have b5017 := hb (x 19 12)
          have b5018 := hb (x 19 1 && x 19 12)
          clear * - r5016 b5017 b5018 d5007
          omega
        have d5019 : (x 19 3 && x 19 12).toNat = 0 := by
          have r5020 := hand2 (x 19 3) (x 19 12)
          have b5021 := hb (x 19 12)
          have b5022 := hb (x 19 3 && x 19 12)
          clear * - r5020 b5021 b5022 d5007
          omega
        have d5023 : (x 19 4).toNat = 0 := by
          have r5024 : (x 19 4).toNat ≤ (x 19 12).toNat := himp _ _ (hp4 19)
          have b5025 := hb (x 19 4)
          have b5026 := hb (x 19 12)
          clear * - r5024 b5025 b5026 d5007
          omega
        have d5027 : (x 17 2).toNat = 0 := by
          have r5028 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5029 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e5030 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b5031 := hb (x 16 3)
          have b5032 := hb (x 17 2)
          have b5033 := hb (x 18 13)
          have b5034 := hb (x 19 12)
          clear * - r5028 e5029 e5030 b5031 b5032 b5033 b5034 d5007 d5002
          omega
        have d5035 : (x 17 2 && x 17 13).toNat = 0 := by
          have r5036 := hand1 (x 17 2) (x 17 13)
          have b5037 := hb (x 17 2)
          have b5038 := hb (x 17 2 && x 17 13)
          clear * - r5036 b5037 b5038 d5027
          omega
        have d5039 : (x 17 3 && x 17 14).toNat = 0 := by
          have r5040 := hand2 (x 17 3) (x 17 14)
          have b5041 := hb (x 17 14)
          have b5042 := hb (x 17 3 && x 17 14)
          clear * - r5040 b5041 b5042 d4994
          omega
        have d5043 : (x 17 5 && x 17 14).toNat = 0 := by
          have r5044 := hand2 (x 17 5) (x 17 14)
          have b5045 := hb (x 17 14)
          have b5046 := hb (x 17 5 && x 17 14)
          clear * - r5044 b5045 b5046 d4994
          omega
        have d5047 : (x 17 6).toNat = 0 := by
          have r5048 : (x 17 6).toNat ≤ (x 17 14).toNat := himp _ _ (hp6 17)
          have b5049 := hb (x 17 6)
          have b5050 := hb (x 17 14)
          clear * - r5048 b5049 b5050 d4994
          omega
        have d5051 : (x 17 12).toNat = 0 := by
          have r5052 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5053 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e5054 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b5055 := hb (x 14 3)
          have b5056 := hb (x 15 2)
          have b5057 := hb (x 16 13)
          have b5058 := hb (x 17 12)
          clear * - r5052 e5053 e5054 b5055 b5056 b5057 b5058 d4985
          omega
        have d5059 : (x 17 1 && x 17 12).toNat = 0 := by
          have r5060 := hand2 (x 17 1) (x 17 12)
          have b5061 := hb (x 17 12)
          have b5062 := hb (x 17 1 && x 17 12)
          clear * - r5060 b5061 b5062 d5051
          omega
        have d5063 : (x 17 3 && x 17 12).toNat = 0 := by
          have r5064 := hand2 (x 17 3) (x 17 12)
          have b5065 := hb (x 17 12)
          have b5066 := hb (x 17 3 && x 17 12)
          clear * - r5064 b5065 b5066 d5051
          omega
        have d5067 : (x 17 4).toNat = 0 := by
          have r5068 : (x 17 4).toNat ≤ (x 17 12).toNat := himp _ _ (hp4 17)
          have b5069 := hb (x 17 4)
          have b5070 := hb (x 17 12)
          clear * - r5068 b5069 b5070 d5051
          omega
        have d5071 : (x 15 2).toNat = 0 := by
          have r5072 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5073 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e5074 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b5075 := hb (x 14 3)
          have b5076 := hb (x 15 2)
          have b5077 := hb (x 16 13)
          have b5078 := hb (x 17 12)
          clear * - r5072 e5073 e5074 b5075 b5076 b5077 b5078 d5051 d4985
          omega
        have d5079 : (x 17 13).toNat = 1 := by
          have r5080 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5081 := hb (x 15 2)
          have b5082 := hb (x 17 13)
          have b5083 := hb (x 16 1 && x 16 14)
          clear * - r5080 b5081 b5082 b5083 d4781 d5071
          omega
        have d5084 : (x 17 1).toNat = 1 := by
          have r5085 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
          have b5086 := hb (x 17 1)
          have b5087 := hb (x 17 13)
          clear * - r5085 b5086 b5087 d5079
          omega
        have d5088 : (x 18 14).toNat = 0 := by
          have r5089 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5090 := hb (x 17 1)
          have b5091 := hb (x 18 14)
          clear * - r5089 b5090 b5091 d5084
          omega
        have d5092 : (x 18 1 && x 18 14).toNat = 0 := by
          have r5093 := hand2 (x 18 1) (x 18 14)
          have b5094 := hb (x 18 14)
          have b5095 := hb (x 18 1 && x 18 14)
          clear * - r5093 b5094 b5095 d5088
          omega
        have d5096 : (x 19 13).toNat = 1 := by
          have r5097 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5098 := hb (x 17 2)
          have b5099 := hb (x 19 13)
          have b5100 := hb (x 18 1 && x 18 14)
          clear * - r5097 b5098 b5099 b5100 d5092 d5027
          omega
        have d5101 : (x 20 12).toNat = 0 := by
          have r5102 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5103 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e5104 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b5105 := hb (x 17 3)
          have b5106 := hb (x 18 2)
          have b5107 := hb (x 19 13)
          have b5108 := hb (x 20 12)
          clear * - r5102 e5103 e5104 b5105 b5106 b5107 b5108 d5096
          omega
        have d5109 : (x 18 2).toNat = 0 := by
          have r5110 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5111 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e5112 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b5113 := hb (x 17 3)
          have b5114 := hb (x 18 2)
          have b5115 := hb (x 19 13)
          have b5116 := hb (x 20 12)
          clear * - r5110 e5111 e5112 b5113 b5114 b5115 b5116 d5101 d5096
          omega
        have d5117 : (x 18 2 && x 18 13).toNat = 0 := by
          have r5118 := hand1 (x 18 2) (x 18 13)
          have b5119 := hb (x 18 2)
          have b5120 := hb (x 18 2 && x 18 13)
          clear * - r5118 b5119 b5120 d5109
          omega
        have d5121 : (x 20 11).toNat = 1 := by
          have r5122 : 1 ≤ (x 20 11).toNat + (x 19 1 && x 19 12).toNat + (x 18 2 && x 18 13).toNat + (x 17 3 && x 17 14).toNat + (x 16 4).toNat := by have q := hcov11 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5123 := hb (x 16 4)
          have b5124 := hb (x 20 11)
          have b5125 := hb (x 19 1 && x 19 12)
          have b5126 := hb (x 18 2 && x 18 13)
          have b5127 := hb (x 17 3 && x 17 14)
          clear * - r5122 b5123 b5124 b5125 b5126 b5127 d5015 d5117 d5039 d3941
          omega
        have d5128 : (x 23 8).toNat = 0 := by
          have r5129 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5130 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
          have e5131 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
          have e5132 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
          have e5133 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
          have e5134 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
          have e5135 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
          have b5136 := hb (x 16 7)
          have b5137 := hb (x 17 6)
          have b5138 := hb (x 18 5)
          have b5139 := hb (x 19 4)
          have b5140 := hb (x 20 11)
          have b5141 := hb (x 21 10)
          have b5142 := hb (x 22 9)
          have b5143 := hb (x 23 8)
          clear * - r5129 e5130 e5131 e5132 e5133 e5134 e5135 b5136 b5137 b5138 b5139 b5140 b5141 b5142 b5143 d5121 d5023 d5047
          omega
        have d5144 : (x 22 9).toNat = 0 := by
          have r5145 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5146 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
          have e5147 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
          have e5148 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
          have e5149 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
          have e5150 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
          have e5151 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
          have b5152 := hb (x 16 7)
          have b5153 := hb (x 17 6)
          have b5154 := hb (x 18 5)
          have b5155 := hb (x 19 4)
          have b5156 := hb (x 20 11)
          have b5157 := hb (x 21 10)
          have b5158 := hb (x 22 9)
          have b5159 := hb (x 23 8)
          clear * - r5145 e5146 e5147 e5148 e5149 e5150 e5151 b5152 b5153 b5154 b5155 b5156 b5157 b5158 b5159 d5128 d5121 d5023 d5047
          omega
        have d5160 : (x 21 10).toNat = 0 := by
          have r5161 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5162 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
          have e5163 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
          have e5164 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
          have e5165 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
          have e5166 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
          have e5167 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
          have b5168 := hb (x 16 7)
          have b5169 := hb (x 17 6)
          have b5170 := hb (x 18 5)
          have b5171 := hb (x 19 4)
          have b5172 := hb (x 20 11)
          have b5173 := hb (x 21 10)
          have b5174 := hb (x 22 9)
          have b5175 := hb (x 23 8)
          clear * - r5161 e5162 e5163 e5164 e5165 e5166 e5167 b5168 b5169 b5170 b5171 b5172 b5173 b5174 b5175 d5128 d5144 d5121 d5023 d5047
          omega
        have d5176 : (x 21 1 && x 21 10).toNat = 0 := by
          have r5177 := hand2 (x 21 1) (x 21 10)
          have b5178 := hb (x 21 10)
          have b5179 := hb (x 21 1 && x 21 10)
          clear * - r5177 b5178 b5179 d5160
          omega
        have d5180 : (x 18 2 && x 18 11).toNat = 0 := by
          have r5181 := hand1 (x 18 2) (x 18 11)
          have b5182 := hb (x 18 2)
          have b5183 := hb (x 18 2 && x 18 11)
          clear * - r5181 b5182 b5183 d5109
          omega
        have d5184 : (x 18 12).toNat = 0 := by
          have r5185 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5186 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e5187 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b5188 := hb (x 15 3)
          have b5189 := hb (x 16 2)
          have b5190 := hb (x 17 13)
          have b5191 := hb (x 18 12)
          clear * - r5185 e5186 e5187 b5188 b5189 b5190 b5191 d5079 d4793
          omega
        have d5192 : (x 18 1 && x 18 12).toNat = 0 := by
          have r5193 := hand2 (x 18 1) (x 18 12)
          have b5194 := hb (x 18 12)
          have b5195 := hb (x 18 1 && x 18 12)
          clear * - r5193 b5194 b5195 d5184
          omega
        have d5196 : (x 19 11).toNat = 1 := by
          have r5197 : 1 ≤ (x 19 11).toNat + (x 18 1 && x 18 12).toNat + (x 17 2 && x 17 13).toNat + (x 16 3 && x 16 14).toNat + (x 15 4).toNat := by have q := hcov11 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5198 := hb (x 15 4)
          have b5199 := hb (x 19 11)
          have b5200 := hb (x 18 1 && x 18 12)
          have b5201 := hb (x 17 2 && x 17 13)
          have b5202 := hb (x 16 3 && x 16 14)
          clear * - r5197 b5198 b5199 b5200 b5201 b5202 d5192 d5035 d4785 d3990
          omega
        have d5203 : (x 19 3).toNat = 1 := by
          have r5204 : (x 19 11).toNat ≤ (x 19 3).toNat := himp _ _ (hp11 19)
          have b5205 := hb (x 19 3)
          have b5206 := hb (x 19 11)
          clear * - r5204 b5205 b5206 d5196
          omega
        have d5207 : (x 22 8).toNat = 0 := by
          have r5208 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5209 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e5210 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e5211 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e5212 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e5213 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e5214 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b5215 := hb (x 15 7)
          have b5216 := hb (x 16 6)
          have b5217 := hb (x 17 5)
          have b5218 := hb (x 18 4)
          have b5219 := hb (x 19 11)
          have b5220 := hb (x 20 10)
          have b5221 := hb (x 21 9)
          have b5222 := hb (x 22 8)
          clear * - r5208 e5209 e5210 e5211 e5212 e5213 e5214 b5215 b5216 b5217 b5218 b5219 b5220 b5221 b5222 d5196 d4789
          omega
        have d5223 : (x 21 9).toNat = 0 := by
          have r5224 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5225 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e5226 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e5227 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e5228 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e5229 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e5230 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b5231 := hb (x 15 7)
          have b5232 := hb (x 16 6)
          have b5233 := hb (x 17 5)
          have b5234 := hb (x 18 4)
          have b5235 := hb (x 19 11)
          have b5236 := hb (x 20 10)
          have b5237 := hb (x 21 9)
          have b5238 := hb (x 22 8)
          clear * - r5224 e5225 e5226 e5227 e5228 e5229 e5230 b5231 b5232 b5233 b5234 b5235 b5236 b5237 b5238 d5207 d5196 d4789
          omega
        have d5239 : (x 20 10).toNat = 0 := by
          have r5240 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5241 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e5242 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e5243 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e5244 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e5245 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e5246 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b5247 := hb (x 15 7)
          have b5248 := hb (x 16 6)
          have b5249 := hb (x 17 5)
          have b5250 := hb (x 18 4)
          have b5251 := hb (x 19 11)
          have b5252 := hb (x 20 10)
          have b5253 := hb (x 21 9)
          have b5254 := hb (x 22 8)
          clear * - r5240 e5241 e5242 e5243 e5244 e5245 e5246 b5247 b5248 b5249 b5250 b5251 b5252 b5253 b5254 d5207 d5223 d5196 d4789
          omega
        have d5255 : (x 18 4).toNat = 0 := by
          have r5256 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5257 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e5258 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e5259 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e5260 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e5261 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e5262 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b5263 := hb (x 15 7)
          have b5264 := hb (x 16 6)
          have b5265 := hb (x 17 5)
          have b5266 := hb (x 18 4)
          have b5267 := hb (x 19 11)
          have b5268 := hb (x 20 10)
          have b5269 := hb (x 21 9)
          have b5270 := hb (x 22 8)
          clear * - r5256 e5257 e5258 e5259 e5260 e5261 e5262 b5263 b5264 b5265 b5266 b5267 b5268 b5269 b5270 d5207 d5223 d5239 d5196 d4789
          omega
        have d5271 : (x 18 4 && x 18 13).toNat = 0 := by
          have r5272 := hand1 (x 18 4) (x 18 13)
          have b5273 := hb (x 18 4)
          have b5274 := hb (x 18 4 && x 18 13)
          clear * - r5272 b5273 b5274 d5255
          omega
        have d5275 : (x 20 2 && x 20 11).toNat = 1 := by
          have r5276 : 1 ≤ (x 22 9).toNat + (x 21 1 && x 21 10).toNat + (x 20 2 && x 20 11).toNat + (x 19 3 && x 19 12).toNat + (x 18 4 && x 18 13).toNat + (x 17 5 && x 17 14).toNat + (x 16 6).toNat := by have q := hcov9 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5277 := hb (x 16 6)
          have b5278 := hb (x 22 9)
          have b5279 := hb (x 21 1 && x 21 10)
          have b5280 := hb (x 20 2 && x 20 11)
          have b5281 := hb (x 19 3 && x 19 12)
          have b5282 := hb (x 18 4 && x 18 13)
          have b5283 := hb (x 17 5 && x 17 14)
          clear * - r5276 b5277 b5278 b5279 b5280 b5281 b5282 b5283 d5144 d5176 d5019 d5271 d5043 d4789
          omega
        have d5284 : (x 20 2).toNat = 1 := by
          have r5285 := hand1 (x 20 2) (x 20 11)
          have b5286 := hb (x 20 2)
          have b5287 := hb (x 20 2 && x 20 11)
          clear * - r5285 b5286 b5287 d5275
          omega
        have d5288 : (x 17 5).toNat = 0 := by
          have r5289 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5290 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e5291 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e5292 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e5293 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e5294 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e5295 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b5296 := hb (x 15 7)
          have b5297 := hb (x 16 6)
          have b5298 := hb (x 17 5)
          have b5299 := hb (x 18 4)
          have b5300 := hb (x 19 11)
          have b5301 := hb (x 20 10)
          have b5302 := hb (x 21 9)
          have b5303 := hb (x 22 8)
          clear * - r5289 e5290 e5291 e5292 e5293 e5294 e5295 b5296 b5297 b5298 b5299 b5300 b5301 b5302 b5303 d5207 d5223 d5239 d5196 d5255 d4789
          omega
        have d5304 : (x 15 7).toNat = 0 := by
          have r5305 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5306 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
          have e5307 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
          have e5308 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
          have e5309 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
          have e5310 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
          have e5311 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
          have b5312 := hb (x 15 7)
          have b5313 := hb (x 16 6)
          have b5314 := hb (x 17 5)
          have b5315 := hb (x 18 4)
          have b5316 := hb (x 19 11)
          have b5317 := hb (x 20 10)
          have b5318 := hb (x 21 9)
          have b5319 := hb (x 22 8)
          clear * - r5305 e5306 e5307 e5308 e5309 e5310 e5311 b5312 b5313 b5314 b5315 b5316 b5317 b5318 b5319 d5207 d5223 d5239 d5196 d5255 d5288 d4789
          omega
        have d5320 : (x 15 1 && x 15 7).toNat = 0 := by
          have r5321 := hand2 (x 15 1) (x 15 7)
          have b5322 := hb (x 15 7)
          have b5323 := hb (x 15 1 && x 15 7)
          clear * - r5321 b5322 b5323 d5304
          omega
        have d5324 : (x 13 3 && x 13 9).toNat = 1 := by
          have r5325 : 1 ≤ (x 16 6).toNat + (x 15 1 && x 15 7).toNat + (x 14 2 && x 14 8).toNat + (x 13 3 && x 13 9).toNat + (x 12 4 && x 12 10).toNat + (x 11 5 && x 11 11).toNat + (x 10 6 && x 10 12).toNat + (x 9 7 && x 9 13).toNat + (x 8 8 && x 8 14).toNat + (x 7 9).toNat := by have q := hcov6 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5326 := hb (x 7 9)
          have b5327 := hb (x 16 6)
          have b5328 := hb (x 15 1 && x 15 7)
          have b5329 := hb (x 14 2 && x 14 8)
          have b5330 := hb (x 13 3 && x 13 9)
          have b5331 := hb (x 12 4 && x 12 10)
          have b5332 := hb (x 11 5 && x 11 11)
          have b5333 := hb (x 10 6 && x 10 12)
          have b5334 := hb (x 9 7 && x 9 13)
          have b5335 := hb (x 8 8 && x 8 14)
          clear * - r5325 b5326 b5327 b5328 b5329 b5330 b5331 b5332 b5333 b5334 b5335 d4789 d5320 d3809 d3841 d3869 d4110 d4134 d4392 d4400
          omega
        have d5336 : (x 13 9).toNat = 1 := by
          have r5337 := hand2 (x 13 3) (x 13 9)
          have b5338 := hb (x 13 9)
          have b5339 := hb (x 13 3 && x 13 9)
          clear * - r5337 b5338 b5339 d5324
          omega
        have d5340 : (x 14 8).toNat = 0 := by
          have r5341 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5342 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e5343 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e5344 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e5345 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e5346 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e5347 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have b5348 := hb (x 7 7)
          have b5349 := hb (x 8 6)
          have b5350 := hb (x 9 5)
          have b5351 := hb (x 10 4)
          have b5352 := hb (x 11 11)
          have b5353 := hb (x 12 10)
          have b5354 := hb (x 13 9)
          have b5355 := hb (x 14 8)
          clear * - r5341 e5342 e5343 e5344 e5345 e5346 e5347 b5348 b5349 b5350 b5351 b5352 b5353 b5354 b5355 d5336 d3837 d3865 d3873 d3893 d4142 d4162
          omega
        have d5356 : (x 21 1).toNat = 0 := by
          have r5357 : (x 21 1).toNat + (x 20 2).toNat + (x 19 3).toNat + (x 18 4).toNat + (x 17 5).toNat + (x 16 6).toNat + (x 15 7).toNat + (x 14 8).toNat + (x 13 9).toNat + (x 12 10).toNat + (x 11 11).toNat + (x 10 12).toNat + (x 9 13).toNat + (x 8 14).toNat = 3 := by have q := hcount 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5358 := hb (x 8 14)
          have b5359 := hb (x 9 13)
          have b5360 := hb (x 10 12)
          have b5361 := hb (x 11 11)
          have b5362 := hb (x 12 10)
          have b5363 := hb (x 13 9)
          have b5364 := hb (x 14 8)
          have b5365 := hb (x 15 7)
          have b5366 := hb (x 16 6)
          have b5367 := hb (x 17 5)
          have b5368 := hb (x 18 4)
          have b5369 := hb (x 19 3)
          have b5370 := hb (x 20 2)
          have b5371 := hb (x 21 1)
          clear * - r5357 b5358 b5359 b5360 b5361 b5362 b5363 b5364 b5365 b5366 b5367 b5368 b5369 b5370 b5371 d5284 d5203 d5255 d5288 d4789 d5304 d5340 d5336 d3837 d3865
          omega
        have d5372 : (x 10 12).toNat = 0 := by
          have r5373 : (x 21 1).toNat + (x 20 2).toNat + (x 19 3).toNat + (x 18 4).toNat + (x 17 5).toNat + (x 16 6).toNat + (x 15 7).toNat + (x 14 8).toNat + (x 13 9).toNat + (x 12 10).toNat + (x 11 11).toNat + (x 10 12).toNat + (x 9 13).toNat + (x 8 14).toNat = 3 := by have q := hcount 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5374 := hb (x 8 14)
          have b5375 := hb (x 9 13)
          have b5376 := hb (x 10 12)
          have b5377 := hb (x 11 11)
          have b5378 := hb (x 12 10)
          have b5379 := hb (x 13 9)
          have b5380 := hb (x 14 8)
          have b5381 := hb (x 15 7)
          have b5382 := hb (x 16 6)
          have b5383 := hb (x 17 5)
          have b5384 := hb (x 18 4)
          have b5385 := hb (x 19 3)
          have b5386 := hb (x 20 2)
          have b5387 := hb (x 21 1)
          clear * - r5373 b5374 b5375 b5376 b5377 b5378 b5379 b5380 b5381 b5382 b5383 b5384 b5385 b5386 b5387 d5356 d5284 d5203 d5255 d5288 d4789 d5304 d5340 d5336 d3837 d3865
          omega
        have d5388 : (x 9 13).toNat = 0 := by
          have r5389 : (x 21 1).toNat + (x 20 2).toNat + (x 19 3).toNat + (x 18 4).toNat + (x 17 5).toNat + (x 16 6).toNat + (x 15 7).toNat + (x 14 8).toNat + (x 13 9).toNat + (x 12 10).toNat + (x 11 11).toNat + (x 10 12).toNat + (x 9 13).toNat + (x 8 14).toNat = 3 := by have q := hcount 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5390 := hb (x 8 14)
          have b5391 := hb (x 9 13)
          have b5392 := hb (x 10 12)
          have b5393 := hb (x 11 11)
          have b5394 := hb (x 12 10)
          have b5395 := hb (x 13 9)
          have b5396 := hb (x 14 8)
          have b5397 := hb (x 15 7)
          have b5398 := hb (x 16 6)
          have b5399 := hb (x 17 5)
          have b5400 := hb (x 18 4)
          have b5401 := hb (x 19 3)
          have b5402 := hb (x 20 2)
          have b5403 := hb (x 21 1)
          clear * - r5389 b5390 b5391 b5392 b5393 b5394 b5395 b5396 b5397 b5398 b5399 b5400 b5401 b5402 b5403 d5356 d5284 d5203 d5255 d5288 d4789 d5304 d5340 d5336 d3837 d3865 d5372
          omega
        have d5404 : (x 8 14).toNat = 0 := by
          have r5405 : (x 21 1).toNat + (x 20 2).toNat + (x 19 3).toNat + (x 18 4).toNat + (x 17 5).toNat + (x 16 6).toNat + (x 15 7).toNat + (x 14 8).toNat + (x 13 9).toNat + (x 12 10).toNat + (x 11 11).toNat + (x 10 12).toNat + (x 9 13).toNat + (x 8 14).toNat = 3 := by have q := hcount 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5406 := hb (x 8 14)
          have b5407 := hb (x 9 13)
          have b5408 := hb (x 10 12)
          have b5409 := hb (x 11 11)
          have b5410 := hb (x 12 10)
          have b5411 := hb (x 13 9)
          have b5412 := hb (x 14 8)
          have b5413 := hb (x 15 7)
          have b5414 := hb (x 16 6)
          have b5415 := hb (x 17 5)
          have b5416 := hb (x 18 4)
          have b5417 := hb (x 19 3)
          have b5418 := hb (x 20 2)
          have b5419 := hb (x 21 1)
          clear * - r5405 b5406 b5407 b5408 b5409 b5410 b5411 b5412 b5413 b5414 b5415 b5416 b5417 b5418 b5419 d5356 d5284 d5203 d5255 d5288 d4789 d5304 d5340 d5336 d3837 d3865 d5372 d5388
          omega
        have d5420 : (x 8 1 && x 8 14).toNat = 0 := by
          have r5421 := hand2 (x 8 1) (x 8 14)
          have b5422 := hb (x 8 14)
          have b5423 := hb (x 8 1 && x 8 14)
          clear * - r5421 b5422 b5423 d5404
          omega
        have d5424 : (x 7 2).toNat = 1 := by
          have r5425 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5426 := hb (x 7 2)
          have b5427 := hb (x 9 13)
          have b5428 := hb (x 8 1 && x 8 14)
          clear * - r5425 b5426 b5427 b5428 d5388 d5420
          omega
        have d5429 : (x 7 14).toNat = 1 := by
          have r5430 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b5431 := hb (x 7 2)
          have b5432 := hb (x 7 14)
          clear * - r5430 b5431 b5432 d5424
          omega
        have d5433 : (x 6 1).toNat = 0 := by
          have r5434 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5435 := hb (x 6 1)
          have b5436 := hb (x 7 14)
          clear * - r5434 b5435 b5436 d5429
          omega
        have d5437 : (x 6 1 && x 6 12).toNat = 0 := by
          have r5438 := hand1 (x 6 1) (x 6 12)
          have b5439 := hb (x 6 1)
          have b5440 := hb (x 6 1 && x 6 12)
          clear * - r5438 b5439 b5440 d5433
          omega
        have d5441 : (x 6 13).toNat = 0 := by
          have r5442 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b5443 := hb (x 6 1)
          have b5444 := hb (x 6 13)
          clear * - r5442 b5443 b5444 d5433
          omega
        have d5445 : (x 6 5).toNat = 0 := by
          have r5446 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
          have b5447 := hb (x 6 5)
          have b5448 := hb (x 6 13)
          clear * - r5446 b5447 b5448 d5441
          omega
        have d5449 : (x 9 12).toNat = 0 := by
          have r5450 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5451 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e5452 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b5453 := hb (x 6 3)
          have b5454 := hb (x 7 2)
          have b5455 := hb (x 8 13)
          have b5456 := hb (x 9 12)
          clear * - r5450 e5451 e5452 b5453 b5454 b5455 b5456 d5424
          omega
        have d5457 : (x 9 2 && x 9 12).toNat = 0 := by
          have r5458 := hand2 (x 9 2) (x 9 12)
          have b5459 := hb (x 9 12)
          have b5460 := hb (x 9 2 && x 9 12)
          clear * - r5458 b5459 b5460 d5449
          omega
        have d5461 : (x 8 13).toNat = 0 := by
          have r5462 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5463 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e5464 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b5465 := hb (x 6 3)
          have b5466 := hb (x 7 2)
          have b5467 := hb (x 8 13)
          have b5468 := hb (x 9 12)
          clear * - r5462 e5463 e5464 b5465 b5466 b5467 b5468 d5449 d5424
          omega
        have d5469 : (x 8 3 && x 8 13).toNat = 0 := by
          have r5470 := hand2 (x 8 3) (x 8 13)
          have b5471 := hb (x 8 13)
          have b5472 := hb (x 8 3 && x 8 13)
          clear * - r5470 b5471 b5472 d5461
          omega
        have d5473 : (x 7 4 && x 7 14).toNat = 1 := by
          have r5474 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5475 := hb (x 6 5)
          have b5476 := hb (x 11 10)
          have b5477 := hb (x 10 1 && x 10 11)
          have b5478 := hb (x 9 2 && x 9 12)
          have b5479 := hb (x 8 3 && x 8 13)
          have b5480 := hb (x 7 4 && x 7 14)
          clear * - r5474 b5475 b5476 b5477 b5478 b5479 b5480 d3768 d4817 d5457 d5469 d5445
          omega
        have d5481 : (x 7 4).toNat = 1 := by
          have r5482 := hand1 (x 7 4) (x 7 14)
          have b5483 := hb (x 7 4)
          have b5484 := hb (x 7 4 && x 7 14)
          clear * - r5482 b5483 b5484 d5473
          omega
        have d5485 : (x 7 12).toNat = 1 := by
          have r5486 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
          have b5487 := hb (x 7 4)
          have b5488 := hb (x 7 12)
          clear * - r5486 b5487 b5488 d5481
          omega
        have d5489 : (x 5 2).toNat = 0 := by
          have r5490 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5491 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e5492 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b5493 := hb (x 4 3)
          have b5494 := hb (x 5 2)
          have b5495 := hb (x 6 13)
          have b5496 := hb (x 7 12)
          clear * - r5490 e5491 e5492 b5493 b5494 b5495 b5496 d5485 d5441
          omega
        have d5497 : (x 5 2 && x 5 13).toNat = 0 := by
          have r5498 := hand1 (x 5 2) (x 5 13)
          have b5499 := hb (x 5 2)
          have b5500 := hb (x 5 2 && x 5 13)
          clear * - r5498 b5499 b5500 d5489
          omega
        have d5501 : (x 4 3).toNat = 0 := by
          have r5502 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5503 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e5504 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b5505 := hb (x 4 3)
          have b5506 := hb (x 5 2)
          have b5507 := hb (x 6 13)
          have b5508 := hb (x 7 12)
          clear * - r5502 e5503 e5504 b5505 b5506 b5507 b5508 d5485 d5441 d5489
          omega
        have d5509 : (x 4 3 && x 4 14).toNat = 0 := by
          have r5510 := hand1 (x 4 3) (x 4 14)
          have b5511 := hb (x 4 3)
          have b5512 := hb (x 4 3 && x 4 14)
          clear * - r5510 b5511 b5512 d5501
          omega
        have d5513 : (x 7 11).toNat = 1 := by
          have r5514 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5515 := hb (x 3 4)
          have b5516 := hb (x 7 11)
          have b5517 := hb (x 6 1 && x 6 12)
          have b5518 := hb (x 5 2 && x 5 13)
          have b5519 := hb (x 4 3 && x 4 14)
          clear * - r5514 b5515 b5516 b5517 b5518 b5519 d5437 d5497 d5509 g56
          omega
        have d5520 : (x 7 3).toNat = 1 := by
          have r5521 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
          have b5522 := hb (x 7 3)
          have b5523 := hb (x 7 11)
          clear * - r5521 b5522 b5523 d5513
          omega
        have d5524 : (x 8 2).toNat = 0 := by
          have r5525 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5526 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e5527 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b5528 := hb (x 7 3)
          have b5529 := hb (x 8 2)
          have b5530 := hb (x 9 13)
          have b5531 := hb (x 10 12)
          clear * - r5525 e5526 e5527 b5528 b5529 b5530 b5531 d5372 d5388 d5520
          omega
        have d5532 : (x 8 10).toNat = 0 := by
          have r5533 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
          have b5534 := hb (x 8 2)
          have b5535 := hb (x 8 10)
          clear * - r5533 b5534 b5535 d5524
          omega
        have d5536 : (x 10 8).toNat = 0 := by
          have r5537 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5538 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e5539 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e5540 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e5541 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e5542 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e5543 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b5544 := hb (x 3 7)
          have b5545 := hb (x 4 6)
          have b5546 := hb (x 5 5)
          have b5547 := hb (x 6 4)
          have b5548 := hb (x 7 11)
          have b5549 := hb (x 8 10)
          have b5550 := hb (x 9 9)
          have b5551 := hb (x 10 8)
          clear * - r5537 e5538 e5539 e5540 e5541 e5542 e5543 b5544 b5545 b5546 b5547 b5548 b5549 b5550 b5551 d5532 d5513
          omega
        have d5552 : (x 9 9).toNat = 0 := by
          have r5553 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5554 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e5555 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e5556 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e5557 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e5558 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e5559 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have b5560 := hb (x 3 7)
          have b5561 := hb (x 4 6)
          have b5562 := hb (x 5 5)
          have b5563 := hb (x 6 4)
          have b5564 := hb (x 7 11)
          have b5565 := hb (x 8 10)
          have b5566 := hb (x 9 9)
          have b5567 := hb (x 10 8)
          clear * - r5553 e5554 e5555 e5556 e5557 e5558 e5559 b5560 b5561 b5562 b5563 b5564 b5565 b5566 b5567 d5536 d5532 d5513
          omega
        have d5568 : (x 15 3).toNat = 0 := by
          have r5569 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5570 := hb (x 4 14)
          have b5571 := hb (x 5 13)
          have b5572 := hb (x 6 12)
          have b5573 := hb (x 7 11)
          have b5574 := hb (x 8 10)
          have b5575 := hb (x 9 9)
          have b5576 := hb (x 10 8)
          have b5577 := hb (x 11 7)
          have b5578 := hb (x 12 6)
          have b5579 := hb (x 13 5)
          have b5580 := hb (x 14 4)
          have b5581 := hb (x 15 3)
          have b5582 := hb (x 16 2)
          have b5583 := hb (x 17 1)
          clear * - r5569 b5570 b5571 b5572 b5573 b5574 b5575 b5576 b5577 b5578 b5579 b5580 b5581 b5582 b5583 d5084 d4793 d4616 d4544 d4632 d4648 d5536 d5552 d5532 d5513
          omega
        have d5584 : (x 15 3 && x 15 14).toNat = 0 := by
          have r5585 := hand1 (x 15 3) (x 15 14)
          have b5586 := hb (x 15 3)
          have b5587 := hb (x 15 3 && x 15 14)
          clear * - r5585 b5586 b5587 d5568
          omega
        have d5588 : (x 18 11).toNat = 1 := by
          have r5589 : 1 ≤ (x 18 11).toNat + (x 17 1 && x 17 12).toNat + (x 16 2 && x 16 13).toNat + (x 15 3 && x 15 14).toNat + (x 14 4).toNat := by have q := hcov11 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5590 := hb (x 14 4)
          have b5591 := hb (x 18 11)
          have b5592 := hb (x 17 1 && x 17 12)
          have b5593 := hb (x 16 2 && x 16 13)
          have b5594 := hb (x 15 3 && x 15 14)
          clear * - r5589 b5590 b5591 b5592 b5593 b5594 d5059 d4797 d5584 d4616
          omega
        have d5595 : (x 21 8).toNat = 0 := by
          have r5596 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5597 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e5598 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e5599 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e5600 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e5601 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e5602 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b5603 := hb (x 14 7)
          have b5604 := hb (x 15 6)
          have b5605 := hb (x 16 5)
          have b5606 := hb (x 17 4)
          have b5607 := hb (x 18 11)
          have b5608 := hb (x 19 10)
          have b5609 := hb (x 20 9)
          have b5610 := hb (x 21 8)
          clear * - r5596 e5597 e5598 e5599 e5600 e5601 e5602 b5603 b5604 b5605 b5606 b5607 b5608 b5609 b5610 d5588 d5067
          omega
        have d5611 : (x 20 9).toNat = 0 := by
          have r5612 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5613 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
          have e5614 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
          have e5615 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
          have e5616 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
          have e5617 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
          have e5618 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
          have b5619 := hb (x 14 7)
          have b5620 := hb (x 15 6)
          have b5621 := hb (x 16 5)
          have b5622 := hb (x 17 4)
          have b5623 := hb (x 18 11)
          have b5624 := hb (x 19 10)
          have b5625 := hb (x 20 9)
          have b5626 := hb (x 21 8)
          clear * - r5612 e5613 e5614 e5615 e5616 e5617 e5618 b5619 b5620 b5621 b5622 b5623 b5624 b5625 b5626 d5595 d5588 d5067
          omega
        have d5627 : (x 19 1 && x 19 10).toNat = 1 := by
          have r5628 : 1 ≤ (x 20 9).toNat + (x 19 1 && x 19 10).toNat + (x 18 2 && x 18 11).toNat + (x 17 3 && x 17 12).toNat + (x 16 4 && x 16 13).toNat + (x 15 5 && x 15 14).toNat + (x 14 6).toNat := by have q := hcov9 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b5629 := hb (x 14 6)
          have b5630 := hb (x 20 9)
          have b5631 := hb (x 19 1 && x 19 10)
          have b5632 := hb (x 18 2 && x 18 11)
          have b5633 := hb (x 17 3 && x 17 12)
          have b5634 := hb (x 16 4 && x 16 13)
          have b5635 := hb (x 15 5 && x 15 14)
          clear * - r5628 b5629 b5630 b5631 b5632 b5633 b5634 b5635 d5611 d5180 d5063 d3945 d3969 d3797
          omega
        have d5636 : (x 19 10).toNat = 1 := by
          have r5637 := hand2 (x 19 1) (x 19 10)
          have b5638 := hb (x 19 10)
          have b5639 := hb (x 19 1 && x 19 10)
          clear * - r5637 b5638 b5639 d5627
          omega
        have r5640 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5641 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
        have e5642 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
        have e5643 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
        have e5644 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
        have e5645 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
        have e5646 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
        have b5647 := hb (x 14 7)
        have b5648 := hb (x 15 6)
        have b5649 := hb (x 16 5)
        have b5650 := hb (x 17 4)
        have b5651 := hb (x 18 11)
        have b5652 := hb (x 19 10)
        have b5653 := hb (x 20 9)
        have b5654 := hb (x 21 8)
        linarith only [r5640, e5641, e5642, e5643, e5644, e5645, e5646, b5647, b5648, b5649, b5650, b5651, b5652, b5653, b5654, d5595, d5611, d5636, d5588, d5067]
    · have f5655 : (x (-1) 8).toNat = 1 := by rw [h1544]; rfl
      have d5656 : (x (-2) 9).toNat = 0 := by
        have r5657 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5658 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e5659 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e5660 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e5661 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e5662 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e5663 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b5664 := hb (x (-8) 7)
        have b5665 := hb (x (-7) 6)
        have b5666 := hb (x (-6) 5)
        have b5667 := hb (x (-5) 4)
        have b5668 := hb (x (-4) 11)
        have b5669 := hb (x (-3) 10)
        have b5670 := hb (x (-2) 9)
        have b5671 := hb (x (-1) 8)
        clear * - r5657 e5658 e5659 e5660 e5661 e5662 e5663 b5664 b5665 b5666 b5667 b5668 b5669 b5670 b5671 f5655 g9
        omega
      have d5672 : (x (-3) 10).toNat = 0 := by
        have r5673 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5674 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e5675 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e5676 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e5677 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e5678 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e5679 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b5680 := hb (x (-8) 7)
        have b5681 := hb (x (-7) 6)
        have b5682 := hb (x (-6) 5)
        have b5683 := hb (x (-5) 4)
        have b5684 := hb (x (-4) 11)
        have b5685 := hb (x (-3) 10)
        have b5686 := hb (x (-2) 9)
        have b5687 := hb (x (-1) 8)
        clear * - r5673 e5674 e5675 e5676 e5677 e5678 e5679 b5680 b5681 b5682 b5683 b5684 b5685 b5686 b5687 f5655 d5656 g9
        omega
      have d5688 : (x (-3) 4 && x (-3) 10).toNat = 0 := by
        have r5689 := hand2 (x (-3) 4) (x (-3) 10)
        have b5690 := hb (x (-3) 10)
        have b5691 := hb (x (-3) 4 && x (-3) 10)
        clear * - r5689 b5690 b5691 d5672
        omega
      have d5692 : (x (-5) 4).toNat = 0 := by
        have r5693 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5694 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e5695 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e5696 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e5697 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e5698 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e5699 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b5700 := hb (x (-8) 7)
        have b5701 := hb (x (-7) 6)
        have b5702 := hb (x (-6) 5)
        have b5703 := hb (x (-5) 4)
        have b5704 := hb (x (-4) 11)
        have b5705 := hb (x (-3) 10)
        have b5706 := hb (x (-2) 9)
        have b5707 := hb (x (-1) 8)
        clear * - r5693 e5694 e5695 e5696 e5697 e5698 e5699 b5700 b5701 b5702 b5703 b5704 b5705 b5706 b5707 f5655 d5656 d5672 g9
        omega
      have d5708 : (x (-6) 5).toNat = 0 := by
        have r5709 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5710 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e5711 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e5712 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e5713 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e5714 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e5715 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b5716 := hb (x (-8) 7)
        have b5717 := hb (x (-7) 6)
        have b5718 := hb (x (-6) 5)
        have b5719 := hb (x (-5) 4)
        have b5720 := hb (x (-4) 11)
        have b5721 := hb (x (-3) 10)
        have b5722 := hb (x (-2) 9)
        have b5723 := hb (x (-1) 8)
        clear * - r5709 e5710 e5711 e5712 e5713 e5714 e5715 b5716 b5717 b5718 b5719 b5720 b5721 b5722 b5723 f5655 d5656 d5672 g9 d5692
        omega
      have d5724 : (x (-7) 6).toNat = 0 := by
        have r5725 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5726 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e5727 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e5728 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e5729 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e5730 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e5731 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b5732 := hb (x (-8) 7)
        have b5733 := hb (x (-7) 6)
        have b5734 := hb (x (-6) 5)
        have b5735 := hb (x (-5) 4)
        have b5736 := hb (x (-4) 11)
        have b5737 := hb (x (-3) 10)
        have b5738 := hb (x (-2) 9)
        have b5739 := hb (x (-1) 8)
        clear * - r5725 e5726 e5727 e5728 e5729 e5730 e5731 b5732 b5733 b5734 b5735 b5736 b5737 b5738 b5739 f5655 d5656 d5672 g9 d5692 d5708
        omega
      have d5740 : (x (-7) 6 && x (-7) 12).toNat = 0 := by
        have r5741 := hand1 (x (-7) 6) (x (-7) 12)
        have b5742 := hb (x (-7) 6)
        have b5743 := hb (x (-7) 6 && x (-7) 12)
        clear * - r5741 b5742 b5743 d5724
        omega
      have d5744 : (x (-8) 7).toNat = 0 := by
        have r5745 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5746 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e5747 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e5748 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e5749 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e5750 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e5751 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b5752 := hb (x (-8) 7)
        have b5753 := hb (x (-7) 6)
        have b5754 := hb (x (-6) 5)
        have b5755 := hb (x (-5) 4)
        have b5756 := hb (x (-4) 11)
        have b5757 := hb (x (-3) 10)
        have b5758 := hb (x (-2) 9)
        have b5759 := hb (x (-1) 8)
        clear * - r5745 e5746 e5747 e5748 e5749 e5750 e5751 b5752 b5753 b5754 b5755 b5756 b5757 b5758 b5759 f5655 d5656 d5672 g9 d5692 d5708 d5724
        omega
      have d5760 : (x (-8) 7 && x (-8) 13).toNat = 0 := by
        have r5761 := hand1 (x (-8) 7) (x (-8) 13)
        have b5762 := hb (x (-8) 7)
        have b5763 := hb (x (-8) 7 && x (-8) 13)
        clear * - r5761 b5762 b5763 d5744
        omega
      have r5764 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5765 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5766 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
      have e5767 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
      have e5768 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
      have e5769 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
      have e5770 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
      have e5771 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
      have r5772 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5773 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
      have e5774 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
      have e5775 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
      have e5776 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
      have e5777 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
      have e5778 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
      have r5779 : 1 ≤ (x (-1) 6).toNat + (x (-2) 1 && x (-2) 7).toNat + (x (-3) 2 && x (-3) 8).toNat + (x (-4) 3 && x (-4) 9).toNat + (x (-5) 4 && x (-5) 10).toNat + (x (-6) 5 && x (-6) 11).toNat + (x (-7) 6 && x (-7) 12).toNat + (x (-8) 7 && x (-8) 13).toNat + (x (-9) 8 && x (-9) 14).toNat + (x (-10) 9).toNat := by have q := hcov6 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5780 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5781 : 1 ≤ (x (-9) 10).toNat + (x (-10) 1 && x (-10) 11).toNat + (x (-11) 2 && x (-11) 12).toNat + (x (-12) 3 && x (-12) 13).toNat + (x (-13) 4 && x (-13) 14).toNat + (x (-14) 5).toNat := by have q := hcov10 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5782 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r5783 := hand2 (x (-3) 2) (x (-3) 8)
      have r5784 := hand1 (x (-9) 8) (x (-9) 14)
      have r5785 := hand1 (x (-7) 8) (x (-7) 14)
      have r5786 := hand2 (x (-10) 1) (x (-10) 11)
      have r5787 := hand2 (x (-11) 2) (x (-11) 12)
      have r5788 := hand2 (x (-12) 3) (x (-12) 13)
      have r5789 := hand2 (x (-13) 4) (x (-13) 14)
      have r5790 := hand1 (x (-7) 4) (x (-7) 14)
      linarith only [r5764, r5765, e5766, e5767, e5768, e5769, e5770, e5771, r5772, e5773, e5774, e5775, e5776, e5777, e5778, r5779, r5780, r5781, r5782, r5783, r5784, r5785, r5786, r5787, r5788, r5789, r5790, g0, g1, g2, g3, g6, g7, g12, d5672, g15, g22, g25, g30, g43, g105, g106, g107, g108, d5740, d5760, g109, g110, g111, d5688, g112, g113, g114, g145, g146, g147]
  · have f5848 : (x 1 7).toNat = 1 := by rw [h1542]; rfl
    have d5849 : (x 8 8).toNat = 0 := by
      have r5850 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5851 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5852 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5853 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5854 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5855 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5856 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5857 := hb (x 1 7)
      have b5858 := hb (x 2 6)
      have b5859 := hb (x 3 5)
      have b5860 := hb (x 4 4)
      have b5861 := hb (x 5 11)
      have b5862 := hb (x 6 10)
      have b5863 := hb (x 7 9)
      have b5864 := hb (x 8 8)
      clear * - r5850 e5851 e5852 e5853 e5854 e5855 e5856 b5857 b5858 b5859 b5860 b5861 b5862 b5863 b5864 g63 g57 f5848
      omega
    have d5865 : (x 7 9).toNat = 0 := by
      have r5866 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5867 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5868 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5869 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5870 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5871 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5872 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5873 := hb (x 1 7)
      have b5874 := hb (x 2 6)
      have b5875 := hb (x 3 5)
      have b5876 := hb (x 4 4)
      have b5877 := hb (x 5 11)
      have b5878 := hb (x 6 10)
      have b5879 := hb (x 7 9)
      have b5880 := hb (x 8 8)
      clear * - r5866 e5867 e5868 e5869 e5870 e5871 e5872 b5873 b5874 b5875 b5876 b5877 b5878 b5879 b5880 d5849 g63 g57 f5848
      omega
    have d5881 : (x 6 10).toNat = 0 := by
      have r5882 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5883 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5884 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5885 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5886 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5887 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5888 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5889 := hb (x 1 7)
      have b5890 := hb (x 2 6)
      have b5891 := hb (x 3 5)
      have b5892 := hb (x 4 4)
      have b5893 := hb (x 5 11)
      have b5894 := hb (x 6 10)
      have b5895 := hb (x 7 9)
      have b5896 := hb (x 8 8)
      clear * - r5882 e5883 e5884 e5885 e5886 e5887 e5888 b5889 b5890 b5891 b5892 b5893 b5894 b5895 b5896 d5849 d5865 g63 g57 f5848
      omega
    have d5897 : (x 5 11).toNat = 0 := by
      have r5898 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5899 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5900 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5901 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5902 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5903 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5904 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5905 := hb (x 1 7)
      have b5906 := hb (x 2 6)
      have b5907 := hb (x 3 5)
      have b5908 := hb (x 4 4)
      have b5909 := hb (x 5 11)
      have b5910 := hb (x 6 10)
      have b5911 := hb (x 7 9)
      have b5912 := hb (x 8 8)
      clear * - r5898 e5899 e5900 e5901 e5902 e5903 e5904 b5905 b5906 b5907 b5908 b5909 b5910 b5911 b5912 d5849 d5865 d5881 g63 g57 f5848
      omega
    have d5913 : (x 5 1 && x 5 11).toNat = 0 := by
      have r5914 := hand2 (x 5 1) (x 5 11)
      have b5915 := hb (x 5 11)
      have b5916 := hb (x 5 1 && x 5 11)
      clear * - r5914 b5915 b5916 d5897
      omega
    have d5917 : (x 2 4 && x 2 14).toNat = 1 := by
      have r5918 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b5919 := hb (x 1 5)
      have b5920 := hb (x 6 10)
      have b5921 := hb (x 5 1 && x 5 11)
      have b5922 := hb (x 4 2 && x 4 12)
      have b5923 := hb (x 3 3 && x 3 13)
      have b5924 := hb (x 2 4 && x 2 14)
      clear * - r5918 b5919 b5920 b5921 b5922 b5923 b5924 d5881 d5913 g152 g153 g42
      omega
    have d5925 : (x 2 4).toNat = 1 := by
      have r5926 := hand1 (x 2 4) (x 2 14)
      have b5927 := hb (x 2 4)
      have b5928 := hb (x 2 4 && x 2 14)
      clear * - r5926 b5927 b5928 d5917
      omega
    have d5929 : (x 2 6).toNat = 0 := by
      have r5930 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5931 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e5932 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e5933 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e5934 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e5935 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e5936 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b5937 := hb (x 1 7)
      have b5938 := hb (x 2 6)
      have b5939 := hb (x 3 5)
      have b5940 := hb (x 4 4)
      have b5941 := hb (x 5 11)
      have b5942 := hb (x 6 10)
      have b5943 := hb (x 7 9)
      have b5944 := hb (x 8 8)
      clear * - r5930 e5931 e5932 e5933 e5934 e5935 e5936 b5937 b5938 b5939 b5940 b5941 b5942 b5943 b5944 d5849 d5865 d5881 d5897 g63 g57 f5848
      omega
    have d5945 : (x 2 6 && x 2 12).toNat = 0 := by
      have r5946 := hand1 (x 2 6) (x 2 12)
      have b5947 := hb (x 2 6)
      have b5948 := hb (x 2 6 && x 2 12)
      clear * - r5946 b5947 b5948 d5929
      omega
    have d5949 : (x 2 6 && x 2 11).toNat = 0 := by
      have r5950 := hand1 (x 2 6) (x 2 11)
      have b5951 := hb (x 2 6)
      have b5952 := hb (x 2 6 && x 2 11)
      clear * - r5950 b5951 b5952 d5929
      omega
    have d5953 : (x 6 8).toNat = 0 := by
      have r5954 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5955 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5956 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5957 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5958 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5959 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5960 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5961 := hb (x (-1) 7)
      have b5962 := hb (x 0 6)
      have b5963 := hb (x 1 5)
      have b5964 := hb (x 2 4)
      have b5965 := hb (x 3 11)
      have b5966 := hb (x 4 10)
      have b5967 := hb (x 5 9)
      have b5968 := hb (x 6 8)
      clear * - r5954 e5955 e5956 e5957 e5958 e5959 e5960 b5961 b5962 b5963 b5964 b5965 b5966 b5967 b5968 d5925 g42 g33 g26
      omega
    have d5969 : (x 6 2 && x 6 8).toNat = 0 := by
      have r5970 := hand2 (x 6 2) (x 6 8)
      have b5971 := hb (x 6 8)
      have b5972 := hb (x 6 2 && x 6 8)
      clear * - r5970 b5971 b5972 d5953
      omega
    have d5973 : (x 5 9).toNat = 0 := by
      have r5974 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5975 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5976 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5977 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5978 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5979 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e5980 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b5981 := hb (x (-1) 7)
      have b5982 := hb (x 0 6)
      have b5983 := hb (x 1 5)
      have b5984 := hb (x 2 4)
      have b5985 := hb (x 3 11)
      have b5986 := hb (x 4 10)
      have b5987 := hb (x 5 9)
      have b5988 := hb (x 6 8)
      clear * - r5974 e5975 e5976 e5977 e5978 e5979 e5980 b5981 b5982 b5983 b5984 b5985 b5986 b5987 b5988 d5953 d5925 g42 g33 g26
      omega
    have d5989 : (x 5 3 && x 5 9).toNat = 0 := by
      have r5990 := hand2 (x 5 3) (x 5 9)
      have b5991 := hb (x 5 9)
      have b5992 := hb (x 5 3 && x 5 9)
      clear * - r5990 b5991 b5992 d5973
      omega
    have d5993 : (x 4 10).toNat = 0 := by
      have r5994 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e5995 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e5996 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e5997 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e5998 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e5999 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e6000 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b6001 := hb (x (-1) 7)
      have b6002 := hb (x 0 6)
      have b6003 := hb (x 1 5)
      have b6004 := hb (x 2 4)
      have b6005 := hb (x 3 11)
      have b6006 := hb (x 4 10)
      have b6007 := hb (x 5 9)
      have b6008 := hb (x 6 8)
      clear * - r5994 e5995 e5996 e5997 e5998 e5999 e6000 b6001 b6002 b6003 b6004 b6005 b6006 b6007 b6008 d5953 d5973 d5925 g42 g33 g26
      omega
    have d6009 : (x 3 11).toNat = 0 := by
      have r6010 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6011 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e6012 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e6013 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e6014 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e6015 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e6016 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b6017 := hb (x (-1) 7)
      have b6018 := hb (x 0 6)
      have b6019 := hb (x 1 5)
      have b6020 := hb (x 2 4)
      have b6021 := hb (x 3 11)
      have b6022 := hb (x 4 10)
      have b6023 := hb (x 5 9)
      have b6024 := hb (x 6 8)
      clear * - r6010 e6011 e6012 e6013 e6014 e6015 e6016 b6017 b6018 b6019 b6020 b6021 b6022 b6023 b6024 d5953 d5973 d5993 d5925 g42 g33 g26
      omega
    have r6025 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6026 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6027 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6028 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6029 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6030 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
    have r6031 := hand2 (x 7 1) (x 7 6)
    have r6032 := hand2 (x 6 2) (x 6 7)
    have r6033 := hand2 (x 7 1) (x 7 7)
    have r6034 := hand1 (x 12 1) (x 12 14)
    linarith only [r6025, r6026, r6027, r6028, r6029, r6030, r6031, r6032, r6033, r6034, g19, g27, g38, g39, g47, g48, g51, g52, g59, d6009, g65, d5993, g68, d5973, d5953, g94, g95, g96, d5949, g97, g98, g99, d5969, d5989, g115, g116, d5945, g117, g118]

theorem cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00001000000 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-6) 11).toNat = 0)
    (g2 : (x (-5) 6).toNat = 0)
    (g3 : (x (-5) 10).toNat = 0)
    (g4 : (x (-5) 11).toNat = 0)
    (g5 : (x (-4) 3).toNat = 0)
    (g6 : (x (-4) 5).toNat = 0)
    (g7 : (x (-4) 9).toNat = 0)
    (g8 : (x (-4) 10).toNat = 0)
    (g9 : (x (-4) 11).toNat = 0)
    (g10 : (x (-4) 13).toNat = 0)
    (g11 : (x (-3) 2).toNat = 1)
    (g12 : (x (-3) 4).toNat = 1)
    (g13 : (x (-3) 12).toNat = 1)
    (g14 : (x (-3) 13).toNat = 1)
    (g15 : (x (-2) 3).toNat = 0)
    (g16 : (x (-2) 4).toNat = 0)
    (g17 : (x (-2) 6).toNat = 0)
    (g18 : (x (-2) 7).toNat = 0)
    (g19 : (x (-2) 10).toNat = 0)
    (g20 : (x (-2) 11).toNat = 0)
    (g21 : (x (-2) 12).toNat = 0)
    (g22 : (x (-1) 2).toNat = 0)
    (g23 : (x (-1) 3).toNat = 0)
    (g24 : (x (-1) 5).toNat = 0)
    (g25 : (x (-1) 6).toNat = 0)
    (g26 : (x (-1) 7).toNat = 0)
    (g27 : (x (-1) 9).toNat = 0)
    (g28 : (x (-1) 10).toNat = 0)
    (g29 : (x (-1) 11).toNat = 0)
    (g30 : (x 0 1).toNat = 1)
    (g31 : (x 0 2).toNat = 0)
    (g32 : (x 0 4).toNat = 0)
    (g33 : (x 0 6).toNat = 0)
    (g34 : (x 0 7).toNat = 0)
    (g35 : (x 0 8).toNat = 0)
    (g36 : (x 0 9).toNat = 0)
    (g37 : (x 0 10).toNat = 0)
    (g38 : (x 0 13).toNat = 1)
    (g39 : (x 0 14).toNat = 1)
    (g40 : (x 1 1).toNat = 0)
    (g41 : (x 1 3).toNat = 0)
    (g42 : (x 1 5).toNat = 0)
    (g43 : (x 1 6).toNat = 0)
    (g44 : (x 1 8).toNat = 0)
    (g45 : (x 1 9).toNat = 0)
    (g46 : (x 1 11).toNat = 0)
    (g47 : (x 1 12).toNat = 0)
    (g48 : (x 1 13).toNat = 0)
    (g49 : (x 1 14).toNat = 0)
    (g50 : (x 2 2).toNat = 1)
    (g51 : (x 2 11).toNat = 1)
    (g52 : (x 2 12).toNat = 1)
    (g53 : (x 2 13).toNat = 1)
    (g54 : (x 2 14).toNat = 1)
    (g55 : (x 3 2).toNat = 0)
    (g56 : (x 3 4).toNat = 0)
    (g57 : (x 3 5).toNat = 0)
    (g58 : (x 3 6).toNat = 0)
    (g59 : (x 3 10).toNat = 0)
    (g60 : (x 3 12).toNat = 0)
    (g61 : (x 3 13).toNat = 0)
    (g62 : (x 3 14).toNat = 0)
    (g63 : (x 4 4).toNat = 0)
    (g64 : (x 4 5).toNat = 0)
    (g65 : (x 4 9).toNat = 0)
    (g66 : (x 4 12).toNat = 0)
    (g67 : (x 5 4).toNat = 0)
    (g68 : (x 5 8).toNat = 0)
    (g69 : (x 5 12 && x 5 13).toNat = 0)
    (g70 : (x 4 13 && x 4 14).toNat = 0)
    (g71 : (x 5 5 && x 5 8).toNat = 0)
    (g72 : (x 4 6 && x 4 9).toNat = 0)
    (g73 : (x 3 7 && x 3 10).toNat = 0)
    (g74 : (x 1 9 && x 1 12).toNat = 0)
    (g75 : (x 0 10 && x 0 13).toNat = 0)
    (g76 : (x (-1) 11 && x (-1) 14).toNat = 0)
    (g77 : (x (-2) 2 && x (-2) 6).toNat = 0)
    (g78 : (x 5 4 && x 5 8).toNat = 0)
    (g79 : (x 4 5 && x 4 9).toNat = 0)
    (g80 : (x 3 6 && x 3 10).toNat = 0)
    (g81 : (x 1 8 && x 1 12).toNat = 0)
    (g82 : (x 0 9 && x 0 13).toNat = 0)
    (g83 : (x 1 9 && x 1 13).toNat = 0)
    (g84 : (x (-5) 1 && x (-5) 6).toNat = 0)
    (g85 : (x (-6) 2 && x (-6) 7).toNat = 0)
    (g86 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g87 : (x (-4) 3 && x (-4) 8).toNat = 0)
    (g88 : (x 0 1 && x 0 6).toNat = 0)
    (g89 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g90 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g91 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g92 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g93 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g94 : (x 5 3 && x 5 8).toNat = 0)
    (g95 : (x 4 4 && x 4 9).toNat = 0)
    (g96 : (x 3 5 && x 3 10).toNat = 0)
    (g97 : (x 1 7 && x 1 12).toNat = 0)
    (g98 : (x 0 8 && x 0 13).toNat = 0)
    (g99 : (x (-1) 9 && x (-1) 14).toNat = 0)
    (g100 : (x 5 4 && x 5 9).toNat = 0)
    (g101 : (x 4 5 && x 4 10).toNat = 0)
    (g102 : (x 3 6 && x 3 11).toNat = 0)
    (g103 : (x 1 8 && x 1 13).toNat = 0)
    (g104 : (x 0 9 && x 0 14).toNat = 0)
    (g105 : (x (-2) 1 && x (-2) 7).toNat = 0)
    (g106 : (x (-4) 3 && x (-4) 9).toNat = 0)
    (g107 : (x (-5) 4 && x (-5) 10).toNat = 0)
    (g108 : (x (-6) 5 && x (-6) 11).toNat = 0)
    (g109 : (x 0 1 && x 0 7).toNat = 0)
    (g110 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g111 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g112 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g113 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g114 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g115 : (x 4 4 && x 4 10).toNat = 0)
    (g116 : (x 3 5 && x 3 11).toNat = 0)
    (g117 : (x 1 7 && x 1 13).toNat = 0)
    (g118 : (x 0 8 && x 0 14).toNat = 0)
    (g119 : (x (-4) 2 && x (-4) 9).toNat = 0)
    (g120 : (x (-5) 3 && x (-5) 10).toNat = 0)
    (g121 : (x (-6) 4 && x (-6) 11).toNat = 0)
    (g122 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g123 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g124 : (x (-4) 4 && x (-4) 11).toNat = 0)
    (g125 : (x 0 1 && x 0 8).toNat = 0)
    (g126 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g127 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g128 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g129 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g130 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g131 : (x 3 4 && x 3 11).toNat = 0)
    (g132 : (x 1 6 && x 1 13).toNat = 0)
    (g133 : (x 0 7 && x 0 14).toNat = 0)
    (g134 : (x (-4) 1 && x (-4) 10).toNat = 0)
    (g135 : (x (-5) 2 && x (-5) 11).toNat = 0)
    (g136 : (x (-6) 3 && x (-6) 12).toNat = 0)
    (g137 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g138 : (x (-4) 3 && x (-4) 12).toNat = 0)
    (g139 : (x 5 3 && x 5 12).toNat = 0)
    (g140 : (x 4 4 && x 4 13).toNat = 0)
    (g141 : (x 3 5 && x 3 14).toNat = 0)
    (g142 : (x 5 4 && x 5 13).toNat = 0)
    (g143 : (x 4 5 && x 4 14).toNat = 0)
    (g144 : (x (-5) 1 && x (-5) 11).toNat = 0)
    (g145 : (x (-4) 1 && x (-4) 11).toNat = 0)
    (g146 : (x (-5) 2 && x (-5) 12).toNat = 0)
    (g147 : (x (-6) 3 && x (-6) 13).toNat = 0)
    (g148 : (x 1 1 && x 1 11).toNat = 0)
    (g149 : (x 0 2 && x 0 12).toNat = 0)
    (g150 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g151 : (x (-2) 4 && x (-2) 14).toNat = 0)
    (g152 : (x 4 2 && x 4 12).toNat = 0)
    (g153 : (x 3 3 && x 3 13).toNat = 0)
    (g154 : (x 5 2 && x 5 12).toNat = 0)
    (g155 : (x 4 3 && x 4 13).toNat = 0)
    (g156 : (x 3 4 && x 3 14).toNat = 0)
    (g157 : (x 4 4 && x 4 14).toNat = 0)
    (g158 : (x 5 1 && x 5 12).toNat = 0)
    (g159 : (x 4 2 && x 4 13).toNat = 0)
    (g160 : (x 3 3 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_twelve_iff_thirteen_core_b00001000000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125 g126 g127 g128 g129 g130 g131 g132 g133 g134 g135 g136 g137 g138 g139 g140 g141 g142 g143 g144 g145 g146 g147 g148 g149 g150 g151 g152 g153 g154 g155 g156 g157 g158 g159 g160
