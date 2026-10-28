import AFTD.Prelude

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt0000000000

Topic: combinatorics   Node: 90a013fb5d9e

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 165 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt0000000000_aux (x : ℤ → Fin 16 → Bool)
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
    (g5 : (x (-4) 5).toNat = 0)
    (g6 : (x (-4) 9).toNat = 0)
    (g7 : (x (-4) 10).toNat = 0)
    (g8 : (x (-4) 11).toNat = 0)
    (g9 : (x (-4) 13).toNat = 0)
    (g10 : (x (-3) 3).toNat = 1)
    (g11 : (x (-3) 4).toNat = 1)
    (g12 : (x (-3) 12).toNat = 1)
    (g13 : (x (-3) 13).toNat = 1)
    (g14 : (x (-2) 2).toNat = 0)
    (g15 : (x (-2) 3).toNat = 0)
    (g16 : (x (-2) 4).toNat = 0)
    (g17 : (x (-2) 6).toNat = 0)
    (g18 : (x (-2) 9).toNat = 0)
    (g19 : (x (-2) 10).toNat = 0)
    (g20 : (x (-2) 11).toNat = 0)
    (g21 : (x (-2) 12).toNat = 0)
    (g22 : (x (-1) 1).toNat = 1)
    (g23 : (x (-1) 2).toNat = 1)
    (g24 : (x (-1) 3).toNat = 0)
    (g25 : (x (-1) 5).toNat = 0)
    (g26 : (x (-1) 10).toNat = 0)
    (g27 : (x (-1) 14).toNat = 1)
    (g28 : (x 0 1).toNat = 0)
    (g29 : (x 0 2).toNat = 0)
    (g30 : (x 0 4).toNat = 0)
    (g31 : (x 0 5).toNat = 0)
    (g32 : (x 0 6).toNat = 0)
    (g33 : (x 0 7).toNat = 0)
    (g34 : (x 0 8).toNat = 0)
    (g35 : (x 0 9).toNat = 0)
    (g36 : (x 0 10).toNat = 0)
    (g37 : (x 0 13).toNat = 0)
    (g38 : (x 0 14).toNat = 0)
    (g39 : (x 1 3).toNat = 0)
    (g40 : (x 1 4).toNat = 0)
    (g41 : (x 1 5).toNat = 0)
    (g42 : (x 1 8).toNat = 0)
    (g43 : (x 1 9).toNat = 0)
    (g44 : (x 1 11).toNat = 0)
    (g45 : (x 1 12).toNat = 0)
    (g46 : (x 1 13).toNat = 0)
    (g47 : (x 1 14).toNat = 1)
    (g48 : (x 2 11).toNat = 1)
    (g49 : (x 2 13).toNat = 1)
    (g50 : (x 2 14).toNat = 1)
    (g51 : (x 3 2).toNat = 0)
    (g52 : (x 3 4).toNat = 0)
    (g53 : (x 3 5).toNat = 0)
    (g54 : (x 3 6).toNat = 0)
    (g55 : (x 3 10).toNat = 0)
    (g56 : (x 3 12).toNat = 0)
    (g57 : (x 3 13).toNat = 0)
    (g58 : (x 3 14).toNat = 0)
    (g59 : (x 4 4).toNat = 0)
    (g60 : (x 4 5).toNat = 0)
    (g61 : (x 4 9).toNat = 0)
    (g62 : (x 4 12).toNat = 0)
    (g63 : (x 4 13).toNat = 0)
    (g64 : (x 5 4).toNat = 0)
    (g65 : (x 5 8).toNat = 0)
    (g66 : (x 5 12).toNat = 0)
    (g67 : (x 0 1 && x 0 4).toNat = 0)
    (g68 : (x (-1) 2 && x (-1) 5).toNat = 0)
    (g69 : (x (-2) 3 && x (-2) 6).toNat = 0)
    (g70 : (x (-4) 5 && x (-4) 8).toNat = 0)
    (g71 : (x (-5) 6 && x (-5) 9).toNat = 0)
    (g72 : (x (-6) 7 && x (-6) 10).toNat = 0)
    (g73 : (x (-2) 2 && x (-2) 6).toNat = 0)
    (g74 : (x (-1) 2 && x (-1) 6).toNat = 0)
    (g75 : (x (-2) 3 && x (-2) 7).toNat = 0)
    (g76 : (x (-4) 5 && x (-4) 9).toNat = 0)
    (g77 : (x (-5) 6 && x (-5) 10).toNat = 0)
    (g78 : (x (-6) 7 && x (-6) 11).toNat = 0)
    (g79 : (x 3 2 && x 3 6).toNat = 0)
    (g80 : (x 1 4 && x 1 8).toNat = 0)
    (g81 : (x 0 5 && x 0 9).toNat = 0)
    (g82 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g83 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g84 : (x (-4) 9 && x (-4) 13).toNat = 0)
    (g85 : (x 5 4 && x 5 8).toNat = 0)
    (g86 : (x 4 5 && x 4 9).toNat = 0)
    (g87 : (x 3 6 && x 3 10).toNat = 0)
    (g88 : (x 1 8 && x 1 12).toNat = 0)
    (g89 : (x 0 9 && x 0 13).toNat = 0)
    (g90 : (x 4 8 && x 4 12).toNat = 0)
    (g91 : (x 3 9 && x 3 13).toNat = 0)
    (g92 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g93 : (x (-2) 2 && x (-2) 7).toNat = 0)
    (g94 : (x (-4) 4 && x (-4) 9).toNat = 0)
    (g95 : (x (-5) 5 && x (-5) 10).toNat = 0)
    (g96 : (x (-6) 6 && x (-6) 11).toNat = 0)
    (g97 : (x 0 1 && x 0 6).toNat = 0)
    (g98 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g99 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g100 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g101 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g102 : (x 5 3 && x 5 8).toNat = 0)
    (g103 : (x 4 4 && x 4 9).toNat = 0)
    (g104 : (x 3 5 && x 3 10).toNat = 0)
    (g105 : (x 1 7 && x 1 12).toNat = 0)
    (g106 : (x 0 8 && x 0 13).toNat = 0)
    (g107 : (x 5 4 && x 5 9).toNat = 0)
    (g108 : (x 4 5 && x 4 10).toNat = 0)
    (g109 : (x 3 6 && x 3 11).toNat = 0)
    (g110 : (x 1 8 && x 1 13).toNat = 0)
    (g111 : (x 0 9 && x 0 14).toNat = 0)
    (g112 : (x 3 7 && x 3 12).toNat = 0)
    (g113 : (x 1 9 && x 1 14).toNat = 0)
    (g114 : (x 5 7 && x 5 12).toNat = 0)
    (g115 : (x 4 8 && x 4 13).toNat = 0)
    (g116 : (x 3 9 && x 3 14).toNat = 0)
    (g117 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g118 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g119 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g120 : (x 5 2 && x 5 8).toNat = 0)
    (g121 : (x 4 3 && x 4 9).toNat = 0)
    (g122 : (x 3 4 && x 3 10).toNat = 0)
    (g123 : (x 1 6 && x 1 12).toNat = 0)
    (g124 : (x 0 7 && x 0 13).toNat = 0)
    (g125 : (x 4 4 && x 4 10).toNat = 0)
    (g126 : (x 3 5 && x 3 11).toNat = 0)
    (g127 : (x 1 7 && x 1 13).toNat = 0)
    (g128 : (x 0 8 && x 0 14).toNat = 0)
    (g129 : (x 5 4 && x 5 10).toNat = 0)
    (g130 : (x 4 5 && x 4 11).toNat = 0)
    (g131 : (x 3 6 && x 3 12).toNat = 0)
    (g132 : (x 1 8 && x 1 14).toNat = 0)
    (g133 : (x 4 6 && x 4 12).toNat = 0)
    (g134 : (x 3 7 && x 3 13).toNat = 0)
    (g135 : (x 4 4 && x 4 11).toNat = 0)
    (g136 : (x 3 5 && x 3 12).toNat = 0)
    (g137 : (x 5 4 && x 5 11).toNat = 0)
    (g138 : (x 4 5 && x 4 12).toNat = 0)
    (g139 : (x 3 6 && x 3 13).toNat = 0)
    (g140 : (x 5 5 && x 5 12).toNat = 0)
    (g141 : (x 4 6 && x 4 13).toNat = 0)
    (g142 : (x 3 7 && x 3 14).toNat = 0)
    (g143 : (x 5 3 && x 5 12).toNat = 0)
    (g144 : (x 4 4 && x 4 13).toNat = 0)
    (g145 : (x 3 5 && x 3 14).toNat = 0)
    (g146 : (x (-4) 1 && x (-4) 11).toNat = 0)
    (g147 : (x (-5) 2 && x (-5) 12).toNat = 0)
    (g148 : (x (-6) 3 && x (-6) 13).toNat = 0)
    (g149 : (x (-4) 2 && x (-4) 12).toNat = 0)
    (g150 : (x (-5) 3 && x (-5) 13).toNat = 0)
    (g151 : (x 1 1 && x 1 11).toNat = 0)
    (g152 : (x 0 2 && x 0 12).toNat = 0)
    (g153 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g154 : (x (-2) 4 && x (-2) 14).toNat = 0)
    (g155 : (x 5 2 && x 5 12).toNat = 0)
    (g156 : (x 4 3 && x 4 13).toNat = 0)
    (g157 : (x 3 4 && x 3 14).toNat = 0)
    (g158 : (x 5 4 && x 5 14).toNat = 0)
    (g159 : (x (-4) 1 && x (-4) 12).toNat = 0)
    (g160 : (x (-5) 2 && x (-5) 13).toNat = 0)
    (g161 : (x (-6) 3 && x (-6) 14).toNat = 0)
    (g162 : (x 5 1 && x 5 12).toNat = 0)
    (g163 : (x 4 2 && x 4 13).toNat = 0)
    (g164 : (x 3 3 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d1342 : (x (-1) 11).toNat = 0 := by
    have r1343 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b1344 := hb (x (-1) 3)
    have b1345 := hb (x (-1) 11)
    clear * - r1343 b1344 b1345 g24
    omega
  have d1346 : (x 2 12).toNat = 1 := by
    have r1347 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e1348 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e1349 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b1350 := hb (x (-1) 3)
    have b1351 := hb (x 0 2)
    have b1352 := hb (x 1 13)
    have b1353 := hb (x 2 12)
    clear * - r1347 e1348 e1349 b1350 b1351 b1352 b1353 g46 g29 g24
    omega
  cases h1354 : x 1 6
  · have f1355 : (x 1 6).toNat = 0 := by rw [h1354]; rfl
    cases h1356 : x (-1) 7
    · have f1357 : (x (-1) 7).toNat = 0 := by rw [h1356]; rfl
      have d1358 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
        have r1359 := hand2 (x (-1) 1) (x (-1) 7)
        have b1360 := hb (x (-1) 7)
        have b1361 := hb (x (-1) 1 && x (-1) 7)
        clear * - r1359 b1360 b1361 f1357
        omega
      have d1362 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
        have r1363 := hand2 (x (-1) 2) (x (-1) 7)
        have b1364 := hb (x (-1) 7)
        have b1365 := hb (x (-1) 2 && x (-1) 7)
        clear * - r1363 b1364 b1365 f1357
        omega
      cases h1366 : x 1 7
      · have f1367 : (x 1 7).toNat = 0 := by rw [h1366]; rfl
        have d1368 : (x 1 7 && x 1 14).toNat = 0 := by
          have r1369 := hand1 (x 1 7) (x 1 14)
          have b1370 := hb (x 1 7)
          have b1371 := hb (x 1 7 && x 1 14)
          clear * - r1369 b1370 b1371 f1367
          omega
        cases h1372 : x (-1) 8
        · have f1373 : (x (-1) 8).toNat = 0 := by rw [h1372]; rfl
          have d1374 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
            have r1375 := hand1 (x (-1) 8) (x (-1) 14)
            have b1376 := hb (x (-1) 8)
            have b1377 := hb (x (-1) 8 && x (-1) 14)
            clear * - r1375 b1376 b1377 f1373
            omega
          cases h1378 : x (-1) 9
          · have f1379 : (x (-1) 9).toNat = 0 := by rw [h1378]; rfl
            cases h1380 : x 2 4
            · have f1381 : (x 2 4).toNat = 0 := by rw [h1380]; rfl
              have d1382 : (x 6 11).toNat = 1 := by
                have r1383 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1384 := hb (x 2 4)
                have b1385 := hb (x 6 11)
                have b1386 := hb (x 5 1 && x 5 12)
                have b1387 := hb (x 4 2 && x 4 13)
                have b1388 := hb (x 3 3 && x 3 14)
                clear * - r1383 b1384 b1385 b1386 b1387 b1388 g162 g163 g164 f1381
                omega
              have d1389 : (x 6 3).toNat = 1 := by
                have r1390 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                have b1391 := hb (x 6 3)
                have b1392 := hb (x 6 11)
                clear * - r1390 b1391 b1392 d1382
                omega
              have d1393 : (x 9 12).toNat = 0 := by
                have r1394 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1395 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e1396 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b1397 := hb (x 6 3)
                have b1398 := hb (x 7 2)
                have b1399 := hb (x 8 13)
                have b1400 := hb (x 9 12)
                clear * - r1394 e1395 e1396 b1397 b1398 b1399 b1400 d1389
                omega
              have d1401 : (x 9 3 && x 9 12).toNat = 0 := by
                have r1402 := hand2 (x 9 3) (x 9 12)
                have b1403 := hb (x 9 12)
                have b1404 := hb (x 9 3 && x 9 12)
                clear * - r1402 b1403 b1404 d1393
                omega
              have d1405 : (x 9 4).toNat = 0 := by
                have r1406 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                have b1407 := hb (x 9 4)
                have b1408 := hb (x 9 12)
                clear * - r1406 b1407 b1408 d1393
                omega
              have d1409 : (x 8 13).toNat = 0 := by
                have r1410 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1411 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e1412 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b1413 := hb (x 6 3)
                have b1414 := hb (x 7 2)
                have b1415 := hb (x 8 13)
                have b1416 := hb (x 9 12)
                clear * - r1410 e1411 e1412 b1413 b1414 b1415 b1416 d1393 d1389
                omega
              have d1417 : (x 8 4 && x 8 13).toNat = 0 := by
                have r1418 := hand2 (x 8 4) (x 8 13)
                have b1419 := hb (x 8 13)
                have b1420 := hb (x 8 4 && x 8 13)
                clear * - r1418 b1419 b1420 d1409
                omega
              have d1421 : (x 8 5).toNat = 0 := by
                have r1422 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                have b1423 := hb (x 8 5)
                have b1424 := hb (x 8 13)
                clear * - r1422 b1423 b1424 d1409
                omega
              have d1425 : (x 7 2).toNat = 0 := by
                have r1426 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1427 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                have e1428 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                have b1429 := hb (x 6 3)
                have b1430 := hb (x 7 2)
                have b1431 := hb (x 8 13)
                have b1432 := hb (x 9 12)
                clear * - r1426 e1427 e1428 b1429 b1430 b1431 b1432 d1393 d1409 d1389
                omega
              have d1433 : (x 7 2 && x 7 8).toNat = 0 := by
                have r1434 := hand1 (x 7 2) (x 7 8)
                have b1435 := hb (x 7 2)
                have b1436 := hb (x 7 2 && x 7 8)
                clear * - r1434 b1435 b1436 d1425
                omega
              have d1437 : (x 7 2 && x 7 6).toNat = 0 := by
                have r1438 := hand1 (x 7 2) (x 7 6)
                have b1439 := hb (x 7 2)
                have b1440 := hb (x 7 2 && x 7 6)
                clear * - r1438 b1439 b1440 d1425
                omega
              have d1441 : (x 7 10).toNat = 0 := by
                have r1442 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
                have b1443 := hb (x 7 2)
                have b1444 := hb (x 7 10)
                clear * - r1442 b1443 b1444 d1425
                omega
              have d1445 : (x 9 8).toNat = 0 := by
                have r1446 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1447 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e1448 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e1449 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e1450 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e1451 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e1452 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b1453 := hb (x 2 7)
                have b1454 := hb (x 3 6)
                have b1455 := hb (x 4 5)
                have b1456 := hb (x 5 4)
                have b1457 := hb (x 6 11)
                have b1458 := hb (x 7 10)
                have b1459 := hb (x 8 9)
                have b1460 := hb (x 9 8)
                clear * - r1446 e1447 e1448 e1449 e1450 e1451 e1452 b1453 b1454 b1455 b1456 b1457 b1458 b1459 b1460 d1441 d1382 g64 g60 g54
                omega
              have d1461 : (x 8 9).toNat = 0 := by
                have r1462 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1463 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e1464 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e1465 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e1466 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e1467 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e1468 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b1469 := hb (x 2 7)
                have b1470 := hb (x 3 6)
                have b1471 := hb (x 4 5)
                have b1472 := hb (x 5 4)
                have b1473 := hb (x 6 11)
                have b1474 := hb (x 7 10)
                have b1475 := hb (x 8 9)
                have b1476 := hb (x 9 8)
                clear * - r1462 e1463 e1464 e1465 e1466 e1467 e1468 b1469 b1470 b1471 b1472 b1473 b1474 b1475 b1476 d1445 d1441 d1382 g64 g60 g54
                omega
              have d1477 : (x 2 7).toNat = 0 := by
                have r1478 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1479 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                have e1480 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                have e1481 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                have e1482 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                have e1483 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                have e1484 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                have b1485 := hb (x 2 7)
                have b1486 := hb (x 3 6)
                have b1487 := hb (x 4 5)
                have b1488 := hb (x 5 4)
                have b1489 := hb (x 6 11)
                have b1490 := hb (x 7 10)
                have b1491 := hb (x 8 9)
                have b1492 := hb (x 9 8)
                clear * - r1478 e1479 e1480 e1481 e1482 e1483 e1484 b1485 b1486 b1487 b1488 b1489 b1490 b1491 b1492 d1445 d1461 d1441 d1382 g64 g60 g54
                omega
              have d1493 : (x 2 7 && x 2 13).toNat = 0 := by
                have r1494 := hand1 (x 2 7) (x 2 13)
                have b1495 := hb (x 2 7)
                have b1496 := hb (x 2 7 && x 2 13)
                clear * - r1494 b1495 b1496 d1477
                omega
              have d1497 : (x 2 7 && x 2 11).toNat = 0 := by
                have r1498 := hand1 (x 2 7) (x 2 11)
                have b1499 := hb (x 2 7)
                have b1500 := hb (x 2 7 && x 2 11)
                clear * - r1498 b1499 b1500 d1477
                omega
              have d1501 : (x 6 3 && x 6 7).toNat = 1 := by
                have r1502 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1503 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
                have e1504 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
                have b1505 := hb (x (-2) 11)
                have b1506 := hb (x (-1) 10)
                have b1507 := hb (x 8 5)
                have b1508 := hb (x 9 4)
                have b1509 := hb (x 7 2 && x 7 6)
                have b1510 := hb (x 6 3 && x 6 7)
                have b1511 := hb (x 5 4 && x 5 8)
                have b1512 := hb (x 4 5 && x 4 9)
                have b1513 := hb (x 3 6 && x 3 10)
                have b1514 := hb (x 2 7 && x 2 11)
                have b1515 := hb (x 1 8 && x 1 12)
                have b1516 := hb (x 0 9 && x 0 13)
                clear * - r1502 e1503 e1504 b1505 b1506 b1507 b1508 b1509 b1510 b1511 b1512 b1513 b1514 b1515 b1516 d1405 d1421 d1437 g85 g86 g87 d1497 g88 g89 g26 g20
                omega
              have d1517 : (x 6 7).toNat = 1 := by
                have r1518 := hand2 (x 6 3) (x 6 7)
                have b1519 := hb (x 6 7)
                have b1520 := hb (x 6 3 && x 6 7)
                clear * - r1518 b1519 b1520 d1501
                omega
              have d1521 : (x 13 8).toNat = 0 := by
                have r1522 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1523 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e1524 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e1525 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e1526 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e1527 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e1528 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b1529 := hb (x 6 7)
                have b1530 := hb (x 7 6)
                have b1531 := hb (x 8 5)
                have b1532 := hb (x 9 4)
                have b1533 := hb (x 10 11)
                have b1534 := hb (x 11 10)
                have b1535 := hb (x 12 9)
                have b1536 := hb (x 13 8)
                clear * - r1522 e1523 e1524 e1525 e1526 e1527 e1528 b1529 b1530 b1531 b1532 b1533 b1534 b1535 b1536 d1405 d1421 d1517
                omega
              have d1537 : (x 12 9).toNat = 0 := by
                have r1538 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1539 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e1540 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e1541 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e1542 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e1543 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e1544 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b1545 := hb (x 6 7)
                have b1546 := hb (x 7 6)
                have b1547 := hb (x 8 5)
                have b1548 := hb (x 9 4)
                have b1549 := hb (x 10 11)
                have b1550 := hb (x 11 10)
                have b1551 := hb (x 12 9)
                have b1552 := hb (x 13 8)
                clear * - r1538 e1539 e1540 e1541 e1542 e1543 e1544 b1545 b1546 b1547 b1548 b1549 b1550 b1551 b1552 d1521 d1405 d1421 d1517
                omega
              have d1553 : (x 11 10).toNat = 0 := by
                have r1554 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1555 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e1556 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e1557 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e1558 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e1559 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e1560 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b1561 := hb (x 6 7)
                have b1562 := hb (x 7 6)
                have b1563 := hb (x 8 5)
                have b1564 := hb (x 9 4)
                have b1565 := hb (x 10 11)
                have b1566 := hb (x 11 10)
                have b1567 := hb (x 12 9)
                have b1568 := hb (x 13 8)
                clear * - r1554 e1555 e1556 e1557 e1558 e1559 e1560 b1561 b1562 b1563 b1564 b1565 b1566 b1567 b1568 d1521 d1537 d1405 d1421 d1517
                omega
              have d1569 : (x 11 1 && x 11 10).toNat = 0 := by
                have r1570 := hand2 (x 11 1) (x 11 10)
                have b1571 := hb (x 11 10)
                have b1572 := hb (x 11 1 && x 11 10)
                clear * - r1570 b1571 b1572 d1553
                omega
              have d1573 : (x 10 11).toNat = 0 := by
                have r1574 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1575 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e1576 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e1577 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e1578 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e1579 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e1580 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b1581 := hb (x 6 7)
                have b1582 := hb (x 7 6)
                have b1583 := hb (x 8 5)
                have b1584 := hb (x 9 4)
                have b1585 := hb (x 10 11)
                have b1586 := hb (x 11 10)
                have b1587 := hb (x 12 9)
                have b1588 := hb (x 13 8)
                clear * - r1574 e1575 e1576 e1577 e1578 e1579 e1580 b1581 b1582 b1583 b1584 b1585 b1586 b1587 b1588 d1521 d1537 d1553 d1405 d1421 d1517
                omega
              have d1589 : (x 10 2 && x 10 11).toNat = 0 := by
                have r1590 := hand2 (x 10 2) (x 10 11)
                have b1591 := hb (x 10 11)
                have b1592 := hb (x 10 2 && x 10 11)
                clear * - r1590 b1591 b1592 d1573
                omega
              have d1593 : (x 7 6).toNat = 0 := by
                have r1594 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1595 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                have e1596 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                have e1597 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                have e1598 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                have e1599 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                have e1600 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                have b1601 := hb (x 6 7)
                have b1602 := hb (x 7 6)
                have b1603 := hb (x 8 5)
                have b1604 := hb (x 9 4)
                have b1605 := hb (x 10 11)
                have b1606 := hb (x 11 10)
                have b1607 := hb (x 12 9)
                have b1608 := hb (x 13 8)
                clear * - r1594 e1595 e1596 e1597 e1598 e1599 e1600 b1601 b1602 b1603 b1604 b1605 b1606 b1607 b1608 d1521 d1537 d1553 d1573 d1405 d1421 d1517
                omega
              have d1609 : (x 12 1).toNat = 0 := by
                have r1610 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1611 := hb (x (-1) 14)
                have b1612 := hb (x 0 13)
                have b1613 := hb (x 1 12)
                have b1614 := hb (x 2 11)
                have b1615 := hb (x 3 10)
                have b1616 := hb (x 4 9)
                have b1617 := hb (x 5 8)
                have b1618 := hb (x 6 7)
                have b1619 := hb (x 7 6)
                have b1620 := hb (x 8 5)
                have b1621 := hb (x 9 4)
                have b1622 := hb (x 10 3)
                have b1623 := hb (x 11 2)
                have b1624 := hb (x 12 1)
                clear * - r1610 b1611 b1612 b1613 b1614 b1615 b1616 b1617 b1618 b1619 b1620 b1621 b1622 b1623 b1624 d1405 d1421 d1593 d1517 g65 g61 g55 g48 g45 g37 g27
                omega
              have d1625 : (x 12 1 && x 12 14).toNat = 0 := by
                have r1626 := hand1 (x 12 1) (x 12 14)
                have b1627 := hb (x 12 1)
                have b1628 := hb (x 12 1 && x 12 14)
                clear * - r1626 b1627 b1628 d1609
                omega
              have d1629 : (x 12 1 && x 12 12).toNat = 0 := by
                have r1630 := hand1 (x 12 1) (x 12 12)
                have b1631 := hb (x 12 1)
                have b1632 := hb (x 12 1 && x 12 12)
                clear * - r1630 b1631 b1632 d1609
                omega
              have d1633 : (x 11 2).toNat = 0 := by
                have r1634 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1635 := hb (x (-1) 14)
                have b1636 := hb (x 0 13)
                have b1637 := hb (x 1 12)
                have b1638 := hb (x 2 11)
                have b1639 := hb (x 3 10)
                have b1640 := hb (x 4 9)
                have b1641 := hb (x 5 8)
                have b1642 := hb (x 6 7)
                have b1643 := hb (x 7 6)
                have b1644 := hb (x 8 5)
                have b1645 := hb (x 9 4)
                have b1646 := hb (x 10 3)
                have b1647 := hb (x 11 2)
                have b1648 := hb (x 12 1)
                clear * - r1634 b1635 b1636 b1637 b1638 b1639 b1640 b1641 b1642 b1643 b1644 b1645 b1646 b1647 b1648 d1609 d1405 d1421 d1593 d1517 g65 g61 g55 g48 g45 g37 g27
                omega
              have d1649 : (x 11 2 && x 11 13).toNat = 0 := by
                have r1650 := hand1 (x 11 2) (x 11 13)
                have b1651 := hb (x 11 2)
                have b1652 := hb (x 11 2 && x 11 13)
                clear * - r1650 b1651 b1652 d1633
                omega
              have d1653 : (x 13 13).toNat = 1 := by
                have r1654 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1655 := hb (x 11 2)
                have b1656 := hb (x 13 13)
                have b1657 := hb (x 12 1 && x 12 14)
                clear * - r1654 b1655 b1656 b1657 d1625 d1633
                omega
              have d1658 : (x 13 1).toNat = 1 := by
                have r1659 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have b1660 := hb (x 13 1)
                have b1661 := hb (x 13 13)
                clear * - r1659 b1660 b1661 d1653
                omega
              have d1662 : (x 14 14).toNat = 0 := by
                have r1663 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1664 := hb (x 13 1)
                have b1665 := hb (x 14 14)
                clear * - r1663 b1664 b1665 d1658
                omega
              have d1666 : (x 14 1 && x 14 14).toNat = 0 := by
                have r1667 := hand2 (x 14 1) (x 14 14)
                have b1668 := hb (x 14 14)
                have b1669 := hb (x 14 1 && x 14 14)
                clear * - r1667 b1668 b1669 d1662
                omega
              have d1670 : (x 14 2).toNat = 0 := by
                have r1671 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
                have b1672 := hb (x 14 2)
                have b1673 := hb (x 14 14)
                clear * - r1671 b1672 b1673 d1662
                omega
              have d1674 : (x 10 3).toNat = 0 := by
                have r1675 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1676 := hb (x (-1) 14)
                have b1677 := hb (x 0 13)
                have b1678 := hb (x 1 12)
                have b1679 := hb (x 2 11)
                have b1680 := hb (x 3 10)
                have b1681 := hb (x 4 9)
                have b1682 := hb (x 5 8)
                have b1683 := hb (x 6 7)
                have b1684 := hb (x 7 6)
                have b1685 := hb (x 8 5)
                have b1686 := hb (x 9 4)
                have b1687 := hb (x 10 3)
                have b1688 := hb (x 11 2)
                have b1689 := hb (x 12 1)
                clear * - r1675 b1676 b1677 b1678 b1679 b1680 b1681 b1682 b1683 b1684 b1685 b1686 b1687 b1688 b1689 d1609 d1633 d1405 d1421 d1593 d1517 g65 g61 g55 g48 g45 g37 g27
                omega
              have d1690 : (x 10 3 && x 10 14).toNat = 0 := by
                have r1691 := hand1 (x 10 3) (x 10 14)
                have b1692 := hb (x 10 3)
                have b1693 := hb (x 10 3 && x 10 14)
                clear * - r1691 b1692 b1693 d1674
                omega
              have d1694 : (x 13 11).toNat = 1 := by
                have r1695 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1696 := hb (x 9 4)
                have b1697 := hb (x 13 11)
                have b1698 := hb (x 12 1 && x 12 12)
                have b1699 := hb (x 11 2 && x 11 13)
                have b1700 := hb (x 10 3 && x 10 14)
                clear * - r1695 b1696 b1697 b1698 b1699 b1700 d1629 d1649 d1690 d1405
                omega
              have d1701 : (x 13 3).toNat = 1 := by
                have r1702 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                have b1703 := hb (x 13 3)
                have b1704 := hb (x 13 11)
                clear * - r1702 b1703 b1704 d1694
                omega
              have d1705 : (x 16 12).toNat = 0 := by
                have r1706 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1707 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e1708 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b1709 := hb (x 13 3)
                have b1710 := hb (x 14 2)
                have b1711 := hb (x 15 13)
                have b1712 := hb (x 16 12)
                clear * - r1706 e1707 e1708 b1709 b1710 b1711 b1712 d1670 d1701
                omega
              have d1713 : (x 15 13).toNat = 0 := by
                have r1714 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1715 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                have e1716 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                have b1717 := hb (x 13 3)
                have b1718 := hb (x 14 2)
                have b1719 := hb (x 15 13)
                have b1720 := hb (x 16 12)
                clear * - r1714 e1715 e1716 b1717 b1718 b1719 b1720 d1705 d1670 d1701
                omega
              have d1721 : (x 13 2).toNat = 1 := by
                have r1722 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1723 := hb (x 13 2)
                have b1724 := hb (x 15 13)
                have b1725 := hb (x 14 1 && x 14 14)
                clear * - r1722 b1723 b1724 b1725 d1713 d1666
                omega
              have d1726 : (x 15 12).toNat = 0 := by
                have r1727 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1728 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e1729 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b1730 := hb (x 12 3)
                have b1731 := hb (x 13 2)
                have b1732 := hb (x 14 13)
                have b1733 := hb (x 15 12)
                clear * - r1727 e1728 e1729 b1730 b1731 b1732 b1733 d1721
                omega
              have d1734 : (x 14 13).toNat = 0 := by
                have r1735 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1736 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e1737 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b1738 := hb (x 12 3)
                have b1739 := hb (x 13 2)
                have b1740 := hb (x 14 13)
                have b1741 := hb (x 15 12)
                clear * - r1735 e1736 e1737 b1738 b1739 b1740 b1741 d1726 d1721
                omega
              have d1742 : (x 12 3).toNat = 0 := by
                have r1743 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1744 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
                have e1745 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
                have b1746 := hb (x 12 3)
                have b1747 := hb (x 13 2)
                have b1748 := hb (x 14 13)
                have b1749 := hb (x 15 12)
                clear * - r1743 e1744 e1745 b1746 b1747 b1748 b1749 d1726 d1734 d1721
                omega
              have d1750 : (x 14 1).toNat = 0 := by
                have r1751 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1752 := hb (x 1 14)
                have b1753 := hb (x 2 13)
                have b1754 := hb (x 3 12)
                have b1755 := hb (x 4 11)
                have b1756 := hb (x 5 10)
                have b1757 := hb (x 6 9)
                have b1758 := hb (x 7 8)
                have b1759 := hb (x 8 7)
                have b1760 := hb (x 9 6)
                have b1761 := hb (x 10 5)
                have b1762 := hb (x 11 4)
                have b1763 := hb (x 12 3)
                have b1764 := hb (x 13 2)
                have b1765 := hb (x 14 1)
                clear * - r1751 b1752 b1753 b1754 b1755 b1756 b1757 b1758 b1759 b1760 b1761 b1762 b1763 b1764 b1765 d1721 d1742 g56 g49 g47
                omega
              have d1766 : (x 11 4).toNat = 0 := by
                have r1767 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1768 := hb (x 1 14)
                have b1769 := hb (x 2 13)
                have b1770 := hb (x 3 12)
                have b1771 := hb (x 4 11)
                have b1772 := hb (x 5 10)
                have b1773 := hb (x 6 9)
                have b1774 := hb (x 7 8)
                have b1775 := hb (x 8 7)
                have b1776 := hb (x 9 6)
                have b1777 := hb (x 10 5)
                have b1778 := hb (x 11 4)
                have b1779 := hb (x 12 3)
                have b1780 := hb (x 13 2)
                have b1781 := hb (x 14 1)
                clear * - r1767 b1768 b1769 b1770 b1771 b1772 b1773 b1774 b1775 b1776 b1777 b1778 b1779 b1780 b1781 d1750 d1721 d1742 g56 g49 g47
                omega
              have d1782 : (x 10 5).toNat = 0 := by
                have r1783 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1784 := hb (x 1 14)
                have b1785 := hb (x 2 13)
                have b1786 := hb (x 3 12)
                have b1787 := hb (x 4 11)
                have b1788 := hb (x 5 10)
                have b1789 := hb (x 6 9)
                have b1790 := hb (x 7 8)
                have b1791 := hb (x 8 7)
                have b1792 := hb (x 9 6)
                have b1793 := hb (x 10 5)
                have b1794 := hb (x 11 4)
                have b1795 := hb (x 12 3)
                have b1796 := hb (x 13 2)
                have b1797 := hb (x 14 1)
                clear * - r1783 b1784 b1785 b1786 b1787 b1788 b1789 b1790 b1791 b1792 b1793 b1794 b1795 b1796 b1797 d1750 d1721 d1742 d1766 g56 g49 g47
                omega
              have d1798 : (x 9 6).toNat = 0 := by
                have r1799 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1800 := hb (x 1 14)
                have b1801 := hb (x 2 13)
                have b1802 := hb (x 3 12)
                have b1803 := hb (x 4 11)
                have b1804 := hb (x 5 10)
                have b1805 := hb (x 6 9)
                have b1806 := hb (x 7 8)
                have b1807 := hb (x 8 7)
                have b1808 := hb (x 9 6)
                have b1809 := hb (x 10 5)
                have b1810 := hb (x 11 4)
                have b1811 := hb (x 12 3)
                have b1812 := hb (x 13 2)
                have b1813 := hb (x 14 1)
                clear * - r1799 b1800 b1801 b1802 b1803 b1804 b1805 b1806 b1807 b1808 b1809 b1810 b1811 b1812 b1813 d1750 d1721 d1742 d1766 d1782 g56 g49 g47
                omega
              have d1814 : (x 8 7).toNat = 0 := by
                have r1815 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1816 := hb (x 1 14)
                have b1817 := hb (x 2 13)
                have b1818 := hb (x 3 12)
                have b1819 := hb (x 4 11)
                have b1820 := hb (x 5 10)
                have b1821 := hb (x 6 9)
                have b1822 := hb (x 7 8)
                have b1823 := hb (x 8 7)
                have b1824 := hb (x 9 6)
                have b1825 := hb (x 10 5)
                have b1826 := hb (x 11 4)
                have b1827 := hb (x 12 3)
                have b1828 := hb (x 13 2)
                have b1829 := hb (x 14 1)
                clear * - r1815 b1816 b1817 b1818 b1819 b1820 b1821 b1822 b1823 b1824 b1825 b1826 b1827 b1828 b1829 d1750 d1721 d1742 d1766 d1782 d1798 g56 g49 g47
                omega
              have d1830 : (x 8 1 && x 8 7).toNat = 0 := by
                have r1831 := hand2 (x 8 1) (x 8 7)
                have b1832 := hb (x 8 7)
                have b1833 := hb (x 8 1 && x 8 7)
                clear * - r1831 b1832 b1833 d1814
                omega
              have d1834 : (x 6 3 && x 6 9).toNat = 1 := by
                have r1835 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := by have q := hcov6 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1836 := hb (x 0 9)
                have b1837 := hb (x 9 6)
                have b1838 := hb (x 8 1 && x 8 7)
                have b1839 := hb (x 7 2 && x 7 8)
                have b1840 := hb (x 6 3 && x 6 9)
                have b1841 := hb (x 5 4 && x 5 10)
                have b1842 := hb (x 4 5 && x 4 11)
                have b1843 := hb (x 3 6 && x 3 12)
                have b1844 := hb (x 2 7 && x 2 13)
                have b1845 := hb (x 1 8 && x 1 14)
                clear * - r1835 b1836 b1837 b1838 b1839 b1840 b1841 b1842 b1843 b1844 b1845 d1798 d1830 d1433 g129 g130 g131 d1493 g132 g35
                omega
              have d1846 : (x 6 9).toNat = 1 := by
                have r1847 := hand2 (x 6 3) (x 6 9)
                have b1848 := hb (x 6 9)
                have b1849 := hb (x 6 3 && x 6 9)
                clear * - r1847 b1848 b1849 d1834
                omega
              have d1850 : (x 6 1).toNat = 1 := by
                have r1851 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
                have b1852 := hb (x 6 1)
                have b1853 := hb (x 6 9)
                clear * - r1851 b1852 b1853 d1846
                omega
              have d1854 : (x 7 14).toNat = 0 := by
                have r1855 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1856 := hb (x 6 1)
                have b1857 := hb (x 7 14)
                clear * - r1855 b1856 b1857 d1850
                omega
              have d1858 : (x 7 1 && x 7 14).toNat = 0 := by
                have r1859 := hand2 (x 7 1) (x 7 14)
                have b1860 := hb (x 7 14)
                have b1861 := hb (x 7 1 && x 7 14)
                clear * - r1859 b1860 b1861 d1854
                omega
              have d1862 : (x 6 2).toNat = 1 := by
                have r1863 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1864 := hb (x 6 2)
                have b1865 := hb (x 8 13)
                have b1866 := hb (x 7 1 && x 7 14)
                clear * - r1863 b1864 b1865 b1866 d1409 d1858
                omega
              have d1867 : (x 6 14).toNat = 1 := by
                have r1868 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                have b1869 := hb (x 6 2)
                have b1870 := hb (x 6 14)
                clear * - r1868 b1869 b1870 d1862
                omega
              have d1871 : (x 5 1).toNat = 0 := by
                have r1872 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1873 := hb (x 5 1)
                have b1874 := hb (x 6 14)
                clear * - r1872 b1873 b1874 d1867
                omega
              have d1875 : (x 5 1 && x 5 14).toNat = 0 := by
                have r1876 := hand1 (x 5 1) (x 5 14)
                have b1877 := hb (x 5 1)
                have b1878 := hb (x 5 1 && x 5 14)
                clear * - r1876 b1877 b1878 d1871
                omega
              have d1879 : (x 5 13).toNat = 0 := by
                have r1880 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                have b1881 := hb (x 5 1)
                have b1882 := hb (x 5 13)
                clear * - r1880 b1881 b1882 d1871
                omega
              have d1883 : (x 5 5).toNat = 0 := by
                have r1884 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
                have b1885 := hb (x 5 5)
                have b1886 := hb (x 5 13)
                clear * - r1884 b1885 b1886 d1879
                omega
              have d1887 : (x 4 1 && x 4 14).toNat = 1 := by
                have r1888 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1889 := hb (x 3 2)
                have b1890 := hb (x 5 13)
                have b1891 := hb (x 4 1 && x 4 14)
                clear * - r1888 b1889 b1890 b1891 d1879 g51
                omega
              have d1892 : (x 4 1).toNat = 1 := by
                have r1893 := hand1 (x 4 1) (x 4 14)
                have b1894 := hb (x 4 1)
                have b1895 := hb (x 4 1 && x 4 14)
                clear * - r1893 b1894 b1895 d1887
                omega
              have d1896 : (x 5 14).toNat = 0 := by
                have r1897 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1898 := hb (x 4 1)
                have b1899 := hb (x 5 14)
                clear * - r1897 b1898 b1899 d1892
                omega
              have d1900 : (x 5 2).toNat = 0 := by
                have r1901 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                have b1902 := hb (x 5 2)
                have b1903 := hb (x 5 14)
                clear * - r1901 b1902 b1903 d1896
                omega
              have d1904 : (x 5 10).toNat = 0 := by
                have r1905 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                have b1906 := hb (x 5 2)
                have b1907 := hb (x 5 10)
                clear * - r1905 b1906 b1907 d1900
                omega
              have d1908 : (x 8 12).toNat = 0 := by
                have r1909 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1910 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e1911 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b1912 := hb (x 5 3)
                have b1913 := hb (x 6 2)
                have b1914 := hb (x 7 13)
                have b1915 := hb (x 8 12)
                clear * - r1909 e1910 e1911 b1912 b1913 b1914 b1915 d1862
                omega
              have d1916 : (x 8 2 && x 8 12).toNat = 0 := by
                have r1917 := hand2 (x 8 2) (x 8 12)
                have b1918 := hb (x 8 12)
                have b1919 := hb (x 8 2 && x 8 12)
                clear * - r1917 b1918 b1919 d1908
                omega
              have d1920 : (x 8 4).toNat = 0 := by
                have r1921 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                have b1922 := hb (x 8 4)
                have b1923 := hb (x 8 12)
                clear * - r1921 b1922 b1923 d1908
                omega
              have d1924 : (x 7 13).toNat = 0 := by
                have r1925 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1926 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                have e1927 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                have b1928 := hb (x 5 3)
                have b1929 := hb (x 6 2)
                have b1930 := hb (x 7 13)
                have b1931 := hb (x 8 12)
                clear * - r1925 e1926 e1927 b1928 b1929 b1930 b1931 d1908 d1862
                omega
              have d1932 : (x 7 3 && x 7 13).toNat = 0 := by
                have r1933 := hand2 (x 7 3) (x 7 13)
                have b1934 := hb (x 7 13)
                have b1935 := hb (x 7 3 && x 7 13)
                clear * - r1933 b1934 b1935 d1924
                omega
              have d1936 : (x 7 5).toNat = 0 := by
                have r1937 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                have b1938 := hb (x 7 5)
                have b1939 := hb (x 7 13)
                clear * - r1937 b1938 b1939 d1924
                omega
              have d1940 : (x 7 5 && x 7 14).toNat = 0 := by
                have r1941 := hand1 (x 7 5) (x 7 14)
                have b1942 := hb (x 7 5)
                have b1943 := hb (x 7 5 && x 7 14)
                clear * - r1941 b1942 b1943 d1936
                omega
              have d1944 : (x 6 6).toNat = 1 := by
                have r1945 : 1 ≤ (x 12 9).toNat + (x 11 1 && x 11 10).toNat + (x 10 2 && x 10 11).toNat + (x 9 3 && x 9 12).toNat + (x 8 4 && x 8 13).toNat + (x 7 5 && x 7 14).toNat + (x 6 6).toNat := by have q := hcov9 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b1946 := hb (x 6 6)
                have b1947 := hb (x 12 9)
                have b1948 := hb (x 11 1 && x 11 10)
                have b1949 := hb (x 10 2 && x 10 11)
                have b1950 := hb (x 9 3 && x 9 12)
                have b1951 := hb (x 8 4 && x 8 13)
                have b1952 := hb (x 7 5 && x 7 14)
                clear * - r1945 b1946 b1947 b1948 b1949 b1950 b1951 b1952 d1537 d1569 d1589 d1401 d1417 d1940
                omega
              have d1953 : (x 12 8).toNat = 0 := by
                have r1954 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1955 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                have e1956 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                have e1957 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                have e1958 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                have e1959 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                have e1960 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                have b1961 := hb (x 5 7)
                have b1962 := hb (x 6 6)
                have b1963 := hb (x 7 5)
                have b1964 := hb (x 8 4)
                have b1965 := hb (x 9 11)
                have b1966 := hb (x 10 10)
                have b1967 := hb (x 11 9)
                have b1968 := hb (x 12 8)
                clear * - r1954 e1955 e1956 e1957 e1958 e1959 e1960 b1961 b1962 b1963 b1964 b1965 b1966 b1967 b1968 d1920 d1936 d1944
                omega
              have d1969 : (x 11 9).toNat = 0 := by
                have r1970 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1971 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                have e1972 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                have e1973 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                have e1974 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                have e1975 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                have e1976 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                have b1977 := hb (x 5 7)
                have b1978 := hb (x 6 6)
                have b1979 := hb (x 7 5)
                have b1980 := hb (x 8 4)
                have b1981 := hb (x 9 11)
                have b1982 := hb (x 10 10)
                have b1983 := hb (x 11 9)
                have b1984 := hb (x 12 8)
                clear * - r1970 e1971 e1972 e1973 e1974 e1975 e1976 b1977 b1978 b1979 b1980 b1981 b1982 b1983 b1984 d1953 d1920 d1936 d1944
                omega
              have d1985 : (x 10 10).toNat = 0 := by
                have r1986 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e1987 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                have e1988 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                have e1989 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                have e1990 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                have e1991 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                have e1992 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                have b1993 := hb (x 5 7)
                have b1994 := hb (x 6 6)
                have b1995 := hb (x 7 5)
                have b1996 := hb (x 8 4)
                have b1997 := hb (x 9 11)
                have b1998 := hb (x 10 10)
                have b1999 := hb (x 11 9)
                have b2000 := hb (x 12 8)
                clear * - r1986 e1987 e1988 e1989 e1990 e1991 e1992 b1993 b1994 b1995 b1996 b1997 b1998 b1999 b2000 d1953 d1969 d1920 d1936 d1944
                omega
              have d2001 : (x 9 11).toNat = 0 := by
                have r2002 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2003 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                have e2004 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                have e2005 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                have e2006 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                have e2007 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                have e2008 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                have b2009 := hb (x 5 7)
                have b2010 := hb (x 6 6)
                have b2011 := hb (x 7 5)
                have b2012 := hb (x 8 4)
                have b2013 := hb (x 9 11)
                have b2014 := hb (x 10 10)
                have b2015 := hb (x 11 9)
                have b2016 := hb (x 12 8)
                clear * - r2002 e2003 e2004 e2005 e2006 e2007 e2008 b2009 b2010 b2011 b2012 b2013 b2014 b2015 b2016 d1953 d1969 d1985 d1920 d1936 d1944
                omega
              have d2017 : (x 9 1 && x 9 11).toNat = 0 := by
                have r2018 := hand2 (x 9 1) (x 9 11)
                have b2019 := hb (x 9 11)
                have b2020 := hb (x 9 1 && x 9 11)
                clear * - r2018 b2019 b2020 d2001
                omega
              have d2021 : (x 6 4 && x 6 14).toNat = 1 := by
                have r2022 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2023 := hb (x 5 5)
                have b2024 := hb (x 10 10)
                have b2025 := hb (x 9 1 && x 9 11)
                have b2026 := hb (x 8 2 && x 8 12)
                have b2027 := hb (x 7 3 && x 7 13)
                have b2028 := hb (x 6 4 && x 6 14)
                clear * - r2022 b2023 b2024 b2025 b2026 b2027 b2028 d1985 d2017 d1916 d1932 d1883
                omega
              have d2029 : (x 6 4).toNat = 1 := by
                have r2030 := hand1 (x 6 4) (x 6 14)
                have b2031 := hb (x 6 4)
                have b2032 := hb (x 6 4 && x 6 14)
                clear * - r2030 b2031 b2032 d2021
                omega
              have d2033 : (x 6 12).toNat = 1 := by
                have r2034 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                have b2035 := hb (x 6 4)
                have b2036 := hb (x 6 12)
                clear * - r2034 b2035 b2036 d2029
                omega
              have d2037 : (x 4 2).toNat = 0 := by
                have r2038 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2039 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e2040 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b2041 := hb (x 3 3)
                have b2042 := hb (x 4 2)
                have b2043 := hb (x 5 13)
                have b2044 := hb (x 6 12)
                clear * - r2038 e2039 e2040 b2041 b2042 b2043 b2044 d2033 d1879
                omega
              have d2045 : (x 6 13).toNat = 1 := by
                have r2046 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b2047 := hb (x 4 2)
                have b2048 := hb (x 6 13)
                have b2049 := hb (x 5 1 && x 5 14)
                clear * - r2046 b2047 b2048 b2049 d1875 d2037
                omega
              have d2050 : (x 7 12).toNat = 0 := by
                have r2051 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2052 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e2053 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b2054 := hb (x 4 3)
                have b2055 := hb (x 5 2)
                have b2056 := hb (x 6 13)
                have b2057 := hb (x 7 12)
                clear * - r2051 e2052 e2053 b2054 b2055 b2056 b2057 d2045 d1900
                omega
              have d2058 : (x 4 3).toNat = 0 := by
                have r2059 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2060 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e2061 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have b2062 := hb (x 4 3)
                have b2063 := hb (x 5 2)
                have b2064 := hb (x 6 13)
                have b2065 := hb (x 7 12)
                clear * - r2059 e2060 e2061 b2062 b2063 b2064 b2065 d2050 d2045 d1900
                omega
              have d2066 : (x 4 11).toNat = 0 := by
                have r2067 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                have b2068 := hb (x 4 3)
                have b2069 := hb (x 4 11)
                clear * - r2067 b2068 b2069 d2058
                omega
              have d2070 : (x 7 8).toNat = 0 := by
                have r2071 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2072 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                have e2073 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                have e2074 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                have e2075 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                have e2076 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                have e2077 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                have b2078 := hb (x 0 7)
                have b2079 := hb (x 1 6)
                have b2080 := hb (x 2 5)
                have b2081 := hb (x 3 4)
                have b2082 := hb (x 4 11)
                have b2083 := hb (x 5 10)
                have b2084 := hb (x 6 9)
                have b2085 := hb (x 7 8)
                clear * - r2071 e2072 e2073 e2074 e2075 e2076 e2077 b2078 b2079 b2080 b2081 b2082 b2083 b2084 b2085 d1846 d1904 d2066 g52 f1355 g33
                omega
              have r2086 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b2087 := hb (x 1 14)
              have b2088 := hb (x 2 13)
              have b2089 := hb (x 3 12)
              have b2090 := hb (x 4 11)
              have b2091 := hb (x 5 10)
              have b2092 := hb (x 6 9)
              have b2093 := hb (x 7 8)
              have b2094 := hb (x 8 7)
              have b2095 := hb (x 9 6)
              have b2096 := hb (x 10 5)
              have b2097 := hb (x 11 4)
              have b2098 := hb (x 12 3)
              have b2099 := hb (x 13 2)
              have b2100 := hb (x 14 1)
              linarith only [r2086, b2087, b2088, b2089, b2090, b2091, b2092, b2093, b2094, b2095, b2096, b2097, b2098, b2099, b2100, d1750, d1721, d1742, d1766, d1782, d1798, d1814, d2070, d1846, d1904, d2066, g56, g49, g47]
            · have f2101 : (x 2 4).toNat = 1 := by rw [h1380]; rfl
              have d2102 : (x 6 8).toNat = 0 := by
                have r2103 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2104 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e2105 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e2106 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e2107 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e2108 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e2109 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b2110 := hb (x (-1) 7)
                have b2111 := hb (x 0 6)
                have b2112 := hb (x 1 5)
                have b2113 := hb (x 2 4)
                have b2114 := hb (x 3 11)
                have b2115 := hb (x 4 10)
                have b2116 := hb (x 5 9)
                have b2117 := hb (x 6 8)
                clear * - r2103 e2104 e2105 e2106 e2107 e2108 e2109 b2110 b2111 b2112 b2113 b2114 b2115 b2116 b2117 f2101 g41 g32 f1357
                omega
              have d2118 : (x 6 2 && x 6 8).toNat = 0 := by
                have r2119 := hand2 (x 6 2) (x 6 8)
                have b2120 := hb (x 6 8)
                have b2121 := hb (x 6 2 && x 6 8)
                clear * - r2119 b2120 b2121 d2102
                omega
              have d2122 : (x 6 8 && x 6 12).toNat = 0 := by
                have r2123 := hand1 (x 6 8) (x 6 12)
                have b2124 := hb (x 6 8)
                have b2125 := hb (x 6 8 && x 6 12)
                clear * - r2123 b2124 b2125 d2102
                omega
              have d2126 : (x 5 9).toNat = 0 := by
                have r2127 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2128 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e2129 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e2130 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e2131 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e2132 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e2133 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b2134 := hb (x (-1) 7)
                have b2135 := hb (x 0 6)
                have b2136 := hb (x 1 5)
                have b2137 := hb (x 2 4)
                have b2138 := hb (x 3 11)
                have b2139 := hb (x 4 10)
                have b2140 := hb (x 5 9)
                have b2141 := hb (x 6 8)
                clear * - r2127 e2128 e2129 e2130 e2131 e2132 e2133 b2134 b2135 b2136 b2137 b2138 b2139 b2140 b2141 d2102 f2101 g41 g32 f1357
                omega
              have d2142 : (x 5 3 && x 5 9).toNat = 0 := by
                have r2143 := hand2 (x 5 3) (x 5 9)
                have b2144 := hb (x 5 9)
                have b2145 := hb (x 5 3 && x 5 9)
                clear * - r2143 b2144 b2145 d2126
                omega
              have d2146 : (x 5 9 && x 5 13).toNat = 0 := by
                have r2147 := hand1 (x 5 9) (x 5 13)
                have b2148 := hb (x 5 9)
                have b2149 := hb (x 5 9 && x 5 13)
                clear * - r2147 b2148 b2149 d2126
                omega
              have d2150 : (x 4 10).toNat = 0 := by
                have r2151 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2152 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e2153 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e2154 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e2155 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e2156 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e2157 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b2158 := hb (x (-1) 7)
                have b2159 := hb (x 0 6)
                have b2160 := hb (x 1 5)
                have b2161 := hb (x 2 4)
                have b2162 := hb (x 3 11)
                have b2163 := hb (x 4 10)
                have b2164 := hb (x 5 9)
                have b2165 := hb (x 6 8)
                clear * - r2151 e2152 e2153 e2154 e2155 e2156 e2157 b2158 b2159 b2160 b2161 b2162 b2163 b2164 b2165 d2102 d2126 f2101 g41 g32 f1357
                omega
              have d2166 : (x 3 11).toNat = 0 := by
                have r2167 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2168 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e2169 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e2170 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e2171 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e2172 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e2173 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b2174 := hb (x (-1) 7)
                have b2175 := hb (x 0 6)
                have b2176 := hb (x 1 5)
                have b2177 := hb (x 2 4)
                have b2178 := hb (x 3 11)
                have b2179 := hb (x 4 10)
                have b2180 := hb (x 5 9)
                have b2181 := hb (x 6 8)
                clear * - r2167 e2168 e2169 e2170 e2171 e2172 e2173 b2174 b2175 b2176 b2177 b2178 b2179 b2180 b2181 d2102 d2126 d2150 f2101 g41 g32 f1357
                omega
              cases h2182 : x 2 5
              · have f2183 : (x 2 5).toNat = 0 := by rw [h2182]; rfl
                have d2184 : (x 2 5 && x 2 11).toNat = 0 := by
                  have r2185 := hand1 (x 2 5) (x 2 11)
                  have b2186 := hb (x 2 5)
                  have b2187 := hb (x 2 5 && x 2 11)
                  clear * - r2185 b2186 b2187 f2183
                  omega
                have r2188 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r2189 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r2190 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e2191 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                have e2192 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                have e2193 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                have e2194 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                have e2195 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                have e2196 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                have r2197 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r2198 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r2199 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
                have r2200 := hand2 (x 6 1) (x 6 7)
                have r2201 := hand1 (x 12 1) (x 12 11)
                have r2202 := hand1 (x 11 2) (x 11 12)
                have r2203 := hand1 (x 10 3) (x 10 13)
                have r2204 := hand1 (x 9 4) (x 9 14)
                linarith only [r2188, r2189, r2190, e2191, e2192, e2193, e2194, e2195, e2196, r2197, r2198, r2199, r2200, r2201, r2202, r2203, r2204, g18, g27, g33, g37, f1355, g45, g47, f2183, g48, g49, g52, g55, g56, g61, g65, g120, g121, g122, d2184, g123, g124, d1374]
              · have f2251 : (x 2 5).toNat = 1 := by rw [h2182]; rfl
                have d2252 : (x 7 8).toNat = 0 := by
                  have r2253 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e2254 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                  have e2255 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                  have e2256 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                  have e2257 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                  have e2258 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                  have e2259 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                  have b2260 := hb (x 0 7)
                  have b2261 := hb (x 1 6)
                  have b2262 := hb (x 2 5)
                  have b2263 := hb (x 3 4)
                  have b2264 := hb (x 4 11)
                  have b2265 := hb (x 5 10)
                  have b2266 := hb (x 6 9)
                  have b2267 := hb (x 7 8)
                  clear * - r2253 e2254 e2255 e2256 e2257 e2258 e2259 b2260 b2261 b2262 b2263 b2264 b2265 b2266 b2267 g52 f2251 f1355 g33
                  omega
                have d2268 : (x 7 1 && x 7 8).toNat = 0 := by
                  have r2269 := hand2 (x 7 1) (x 7 8)
                  have b2270 := hb (x 7 8)
                  have b2271 := hb (x 7 1 && x 7 8)
                  clear * - r2269 b2270 b2271 d2252
                  omega
                have d2272 : (x 7 3 && x 7 8).toNat = 0 := by
                  have r2273 := hand2 (x 7 3) (x 7 8)
                  have b2274 := hb (x 7 8)
                  have b2275 := hb (x 7 3 && x 7 8)
                  clear * - r2273 b2274 b2275 d2252
                  omega
                have d2276 : (x 6 9).toNat = 0 := by
                  have r2277 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e2278 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                  have e2279 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                  have e2280 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                  have e2281 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                  have e2282 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                  have e2283 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                  have b2284 := hb (x 0 7)
                  have b2285 := hb (x 1 6)
                  have b2286 := hb (x 2 5)
                  have b2287 := hb (x 3 4)
                  have b2288 := hb (x 4 11)
                  have b2289 := hb (x 5 10)
                  have b2290 := hb (x 6 9)
                  have b2291 := hb (x 7 8)
                  clear * - r2277 e2278 e2279 e2280 e2281 e2282 e2283 b2284 b2285 b2286 b2287 b2288 b2289 b2290 b2291 d2252 g52 f2251 f1355 g33
                  omega
                have d2292 : (x 6 2 && x 6 9).toNat = 0 := by
                  have r2293 := hand2 (x 6 2) (x 6 9)
                  have b2294 := hb (x 6 9)
                  have b2295 := hb (x 6 2 && x 6 9)
                  clear * - r2293 b2294 b2295 d2276
                  omega
                have d2296 : (x 6 4 && x 6 9).toNat = 0 := by
                  have r2297 := hand2 (x 6 4) (x 6 9)
                  have b2298 := hb (x 6 9)
                  have b2299 := hb (x 6 4 && x 6 9)
                  clear * - r2297 b2298 b2299 d2276
                  omega
                have d2300 : (x 5 10).toNat = 0 := by
                  have r2301 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e2302 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                  have e2303 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                  have e2304 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                  have e2305 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                  have e2306 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                  have e2307 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                  have b2308 := hb (x 0 7)
                  have b2309 := hb (x 1 6)
                  have b2310 := hb (x 2 5)
                  have b2311 := hb (x 3 4)
                  have b2312 := hb (x 4 11)
                  have b2313 := hb (x 5 10)
                  have b2314 := hb (x 6 9)
                  have b2315 := hb (x 7 8)
                  clear * - r2301 e2302 e2303 e2304 e2305 e2306 e2307 b2308 b2309 b2310 b2311 b2312 b2313 b2314 b2315 d2252 d2276 g52 f2251 f1355 g33
                  omega
                have d2316 : (x 5 3 && x 5 10).toNat = 0 := by
                  have r2317 := hand2 (x 5 3) (x 5 10)
                  have b2318 := hb (x 5 10)
                  have b2319 := hb (x 5 3 && x 5 10)
                  clear * - r2317 b2318 b2319 d2300
                  omega
                have d2320 : (x 5 5 && x 5 10).toNat = 0 := by
                  have r2321 := hand2 (x 5 5) (x 5 10)
                  have b2322 := hb (x 5 10)
                  have b2323 := hb (x 5 5 && x 5 10)
                  clear * - r2321 b2322 b2323 d2300
                  omega
                have d2324 : (x 4 11).toNat = 0 := by
                  have r2325 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e2326 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                  have e2327 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                  have e2328 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                  have e2329 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                  have e2330 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                  have e2331 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                  have b2332 := hb (x 0 7)
                  have b2333 := hb (x 1 6)
                  have b2334 := hb (x 2 5)
                  have b2335 := hb (x 3 4)
                  have b2336 := hb (x 4 11)
                  have b2337 := hb (x 5 10)
                  have b2338 := hb (x 6 9)
                  have b2339 := hb (x 7 8)
                  clear * - r2325 e2326 e2327 e2328 e2329 e2330 e2331 b2332 b2333 b2334 b2335 b2336 b2337 b2338 b2339 d2252 d2276 d2300 g52 f2251 f1355 g33
                  omega
                have d2340 : (x 4 6 && x 4 11).toNat = 0 := by
                  have r2341 := hand2 (x 4 6) (x 4 11)
                  have b2342 := hb (x 4 11)
                  have b2343 := hb (x 4 6 && x 4 11)
                  clear * - r2341 b2342 b2343 d2324
                  omega
                cases h2344 : x (-2) 8
                · have f2345 : (x (-2) 8).toNat = 0 := by rw [h2344]; rfl
                  cases h2346 : x 2 10
                  · have f2347 : (x 2 10).toNat = 0 := by rw [h2346]; rfl
                    have d2348 : (x (-3) 5).toNat = 1 := by
                      have r2349 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b2350 := hb (x (-3) 5)
                      have b2351 := hb (x 2 10)
                      have b2352 := hb (x 1 1 && x 1 11)
                      have b2353 := hb (x 0 2 && x 0 12)
                      have b2354 := hb (x (-1) 3 && x (-1) 13)
                      have b2355 := hb (x (-2) 4 && x (-2) 14)
                      clear * - r2349 b2350 b2351 b2352 b2353 b2354 b2355 f2347 g151 g152 g153 g154
                      omega
                    have d2356 : (x 2 8).toNat = 0 := by
                      have r2357 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e2358 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                      have e2359 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                      have e2360 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                      have e2361 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                      have e2362 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                      have e2363 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                      have b2364 := hb (x (-5) 7)
                      have b2365 := hb (x (-4) 6)
                      have b2366 := hb (x (-3) 5)
                      have b2367 := hb (x (-2) 4)
                      have b2368 := hb (x (-1) 11)
                      have b2369 := hb (x 0 10)
                      have b2370 := hb (x 1 9)
                      have b2371 := hb (x 2 8)
                      clear * - r2357 e2358 e2359 e2360 e2361 e2362 e2363 b2364 b2365 b2366 b2367 b2368 b2369 b2370 b2371 g43 g36 d1342 g16 d2348
                      omega
                    have d2372 : (x 2 8 && x 2 14).toNat = 0 := by
                      have r2373 := hand1 (x 2 8) (x 2 14)
                      have b2374 := hb (x 2 8)
                      have b2375 := hb (x 2 8 && x 2 14)
                      clear * - r2373 b2374 b2375 d2356
                      omega
                    have d2376 : (x 2 8 && x 2 13).toNat = 0 := by
                      have r2377 := hand1 (x 2 8) (x 2 13)
                      have b2378 := hb (x 2 8)
                      have b2379 := hb (x 2 8 && x 2 13)
                      clear * - r2377 b2378 b2379 d2356
                      omega
                    cases h2380 : x 2 6
                    · have f2381 : (x 2 6).toNat = 0 := by rw [h2380]; rfl
                      have d2382 : (x 2 6 && x 2 13).toNat = 0 := by
                        have r2383 := hand1 (x 2 6) (x 2 13)
                        have b2384 := hb (x 2 6)
                        have b2385 := hb (x 2 6 && x 2 13)
                        clear * - r2383 b2384 b2385 f2381
                        omega
                      have d2386 : (x 2 6 && x 2 12).toNat = 0 := by
                        have r2387 := hand1 (x 2 6) (x 2 12)
                        have b2388 := hb (x 2 6)
                        have b2389 := hb (x 2 6 && x 2 12)
                        clear * - r2387 b2388 b2389 f2381
                        omega
                      have d2390 : (x 8 7).toNat = 1 := by
                        have r2391 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2392 := hb (x 0 8)
                        have b2393 := hb (x 8 7)
                        have b2394 := hb (x 7 1 && x 7 8)
                        have b2395 := hb (x 6 2 && x 6 9)
                        have b2396 := hb (x 5 3 && x 5 10)
                        have b2397 := hb (x 4 4 && x 4 11)
                        have b2398 := hb (x 3 5 && x 3 12)
                        have b2399 := hb (x 2 6 && x 2 13)
                        have b2400 := hb (x 1 7 && x 1 14)
                        clear * - r2391 b2392 b2393 b2394 b2395 b2396 b2397 b2398 b2399 b2400 d2268 d2292 d2316 g135 g136 d2382 d1368 g34
                        omega
                      have d2401 : (x 15 8).toNat = 0 := by
                        have r2402 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2403 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e2404 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e2405 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e2406 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e2407 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e2408 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have b2409 := hb (x 8 7)
                        have b2410 := hb (x 9 6)
                        have b2411 := hb (x 10 5)
                        have b2412 := hb (x 11 4)
                        have b2413 := hb (x 12 11)
                        have b2414 := hb (x 13 10)
                        have b2415 := hb (x 14 9)
                        have b2416 := hb (x 15 8)
                        clear * - r2402 e2403 e2404 e2405 e2406 e2407 e2408 b2409 b2410 b2411 b2412 b2413 b2414 b2415 b2416 d2390
                        omega
                      have d2417 : (x 15 8 && x 15 9).toNat = 0 := by
                        have r2418 := hand1 (x 15 8) (x 15 9)
                        have b2419 := hb (x 15 8)
                        have b2420 := hb (x 15 8 && x 15 9)
                        clear * - r2418 b2419 b2420 d2401
                        omega
                      have d2421 : (x 14 9).toNat = 0 := by
                        have r2422 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2423 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e2424 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e2425 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e2426 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e2427 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e2428 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have b2429 := hb (x 8 7)
                        have b2430 := hb (x 9 6)
                        have b2431 := hb (x 10 5)
                        have b2432 := hb (x 11 4)
                        have b2433 := hb (x 12 11)
                        have b2434 := hb (x 13 10)
                        have b2435 := hb (x 14 9)
                        have b2436 := hb (x 15 8)
                        clear * - r2422 e2423 e2424 e2425 e2426 e2427 e2428 b2429 b2430 b2431 b2432 b2433 b2434 b2435 b2436 d2401 d2390
                        omega
                      have d2437 : (x 14 9 && x 14 10).toNat = 0 := by
                        have r2438 := hand1 (x 14 9) (x 14 10)
                        have b2439 := hb (x 14 9)
                        have b2440 := hb (x 14 9 && x 14 10)
                        clear * - r2438 b2439 b2440 d2421
                        omega
                      have d2441 : (x 13 10).toNat = 0 := by
                        have r2442 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2443 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e2444 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e2445 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e2446 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e2447 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e2448 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have b2449 := hb (x 8 7)
                        have b2450 := hb (x 9 6)
                        have b2451 := hb (x 10 5)
                        have b2452 := hb (x 11 4)
                        have b2453 := hb (x 12 11)
                        have b2454 := hb (x 13 10)
                        have b2455 := hb (x 14 9)
                        have b2456 := hb (x 15 8)
                        clear * - r2442 e2443 e2444 e2445 e2446 e2447 e2448 b2449 b2450 b2451 b2452 b2453 b2454 b2455 b2456 d2401 d2421 d2390
                        omega
                      have d2457 : (x 13 10 && x 13 11).toNat = 0 := by
                        have r2458 := hand1 (x 13 10) (x 13 11)
                        have b2459 := hb (x 13 10)
                        have b2460 := hb (x 13 10 && x 13 11)
                        clear * - r2458 b2459 b2460 d2441
                        omega
                      have d2461 : (x 12 11).toNat = 0 := by
                        have r2462 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2463 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e2464 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e2465 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e2466 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e2467 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e2468 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have b2469 := hb (x 8 7)
                        have b2470 := hb (x 9 6)
                        have b2471 := hb (x 10 5)
                        have b2472 := hb (x 11 4)
                        have b2473 := hb (x 12 11)
                        have b2474 := hb (x 13 10)
                        have b2475 := hb (x 14 9)
                        have b2476 := hb (x 15 8)
                        clear * - r2462 e2463 e2464 e2465 e2466 e2467 e2468 b2469 b2470 b2471 b2472 b2473 b2474 b2475 b2476 d2401 d2421 d2441 d2390
                        omega
                      have d2477 : (x 12 1 && x 12 11).toNat = 0 := by
                        have r2478 := hand2 (x 12 1) (x 12 11)
                        have b2479 := hb (x 12 11)
                        have b2480 := hb (x 12 1 && x 12 11)
                        clear * - r2478 b2479 b2480 d2461
                        omega
                      have d2481 : (x 12 11 && x 12 12).toNat = 0 := by
                        have r2482 := hand1 (x 12 11) (x 12 12)
                        have b2483 := hb (x 12 11)
                        have b2484 := hb (x 12 11 && x 12 12)
                        clear * - r2482 b2483 b2484 d2461
                        omega
                      have d2485 : (x 11 4).toNat = 0 := by
                        have r2486 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2487 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e2488 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e2489 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e2490 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e2491 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e2492 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have b2493 := hb (x 8 7)
                        have b2494 := hb (x 9 6)
                        have b2495 := hb (x 10 5)
                        have b2496 := hb (x 11 4)
                        have b2497 := hb (x 12 11)
                        have b2498 := hb (x 13 10)
                        have b2499 := hb (x 14 9)
                        have b2500 := hb (x 15 8)
                        clear * - r2486 e2487 e2488 e2489 e2490 e2491 e2492 b2493 b2494 b2495 b2496 b2497 b2498 b2499 b2500 d2401 d2421 d2441 d2461 d2390
                        omega
                      have d2501 : (x 11 4 && x 11 14).toNat = 0 := by
                        have r2502 := hand1 (x 11 4) (x 11 14)
                        have b2503 := hb (x 11 4)
                        have b2504 := hb (x 11 4 && x 11 14)
                        clear * - r2502 b2503 b2504 d2485
                        omega
                      have d2505 : (x 11 4 && x 11 13).toNat = 0 := by
                        have r2506 := hand1 (x 11 4) (x 11 13)
                        have b2507 := hb (x 11 4)
                        have b2508 := hb (x 11 4 && x 11 13)
                        clear * - r2506 b2507 b2508 d2485
                        omega
                      have d2509 : (x 10 5).toNat = 0 := by
                        have r2510 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2511 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e2512 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e2513 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e2514 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e2515 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e2516 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have b2517 := hb (x 8 7)
                        have b2518 := hb (x 9 6)
                        have b2519 := hb (x 10 5)
                        have b2520 := hb (x 11 4)
                        have b2521 := hb (x 12 11)
                        have b2522 := hb (x 13 10)
                        have b2523 := hb (x 14 9)
                        have b2524 := hb (x 15 8)
                        clear * - r2510 e2511 e2512 e2513 e2514 e2515 e2516 b2517 b2518 b2519 b2520 b2521 b2522 b2523 b2524 d2401 d2421 d2441 d2461 d2485 d2390
                        omega
                      have d2525 : (x 10 5 && x 10 14).toNat = 0 := by
                        have r2526 := hand1 (x 10 5) (x 10 14)
                        have b2527 := hb (x 10 5)
                        have b2528 := hb (x 10 5 && x 10 14)
                        clear * - r2526 b2527 b2528 d2509
                        omega
                      have d2529 : (x 9 6).toNat = 0 := by
                        have r2530 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2531 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                        have e2532 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                        have e2533 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                        have e2534 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                        have e2535 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                        have e2536 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                        have b2537 := hb (x 8 7)
                        have b2538 := hb (x 9 6)
                        have b2539 := hb (x 10 5)
                        have b2540 := hb (x 11 4)
                        have b2541 := hb (x 12 11)
                        have b2542 := hb (x 13 10)
                        have b2543 := hb (x 14 9)
                        have b2544 := hb (x 15 8)
                        clear * - r2530 e2531 e2532 e2533 e2534 e2535 e2536 b2537 b2538 b2539 b2540 b2541 b2542 b2543 b2544 d2401 d2421 d2441 d2461 d2485 d2509 d2390
                        omega
                      have d2545 : (x 9 1 && x 9 6).toNat = 0 := by
                        have r2546 := hand2 (x 9 1) (x 9 6)
                        have b2547 := hb (x 9 6)
                        have b2548 := hb (x 9 1 && x 9 6)
                        clear * - r2546 b2547 b2548 d2529
                        omega
                      have d2549 : (x 8 2 && x 8 7).toNat = 1 := by
                        have r2550 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2551 := hb (x 0 10)
                        have b2552 := hb (x 10 5)
                        have b2553 := hb (x 9 1 && x 9 6)
                        have b2554 := hb (x 8 2 && x 8 7)
                        have b2555 := hb (x 7 3 && x 7 8)
                        have b2556 := hb (x 6 4 && x 6 9)
                        have b2557 := hb (x 5 5 && x 5 10)
                        have b2558 := hb (x 4 6 && x 4 11)
                        have b2559 := hb (x 3 7 && x 3 12)
                        have b2560 := hb (x 2 8 && x 2 13)
                        have b2561 := hb (x 1 9 && x 1 14)
                        clear * - r2550 b2551 b2552 b2553 b2554 b2555 b2556 b2557 b2558 b2559 b2560 b2561 d2509 d2545 d2272 d2296 d2320 d2340 g112 d2376 g113 g36
                        omega
                      have d2562 : (x 8 2).toNat = 1 := by
                        have r2563 := hand1 (x 8 2) (x 8 7)
                        have b2564 := hb (x 8 2)
                        have b2565 := hb (x 8 2 && x 8 7)
                        clear * - r2563 b2564 b2565 d2549
                        omega
                      have d2566 : (x 8 14).toNat = 1 := by
                        have r2567 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                        have b2568 := hb (x 8 2)
                        have b2569 := hb (x 8 14)
                        clear * - r2567 b2568 b2569 d2562
                        omega
                      have d2570 : (x 7 1).toNat = 0 := by
                        have r2571 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2572 := hb (x 7 1)
                        have b2573 := hb (x 8 14)
                        clear * - r2571 b2572 b2573 d2566
                        omega
                      have d2574 : (x 7 1 && x 7 14).toNat = 0 := by
                        have r2575 := hand1 (x 7 1) (x 7 14)
                        have b2576 := hb (x 7 1)
                        have b2577 := hb (x 7 1 && x 7 14)
                        clear * - r2575 b2576 b2577 d2570
                        omega
                      have d2578 : (x 7 1 && x 7 10).toNat = 0 := by
                        have r2579 := hand1 (x 7 1) (x 7 10)
                        have b2580 := hb (x 7 1)
                        have b2581 := hb (x 7 1 && x 7 10)
                        clear * - r2579 b2580 b2581 d2570
                        omega
                      have d2582 : (x 7 1 && x 7 7).toNat = 0 := by
                        have r2583 := hand1 (x 7 1) (x 7 7)
                        have b2584 := hb (x 7 1)
                        have b2585 := hb (x 7 1 && x 7 7)
                        clear * - r2583 b2584 b2585 d2570
                        omega
                      have d2586 : (x 8 6).toNat = 1 := by
                        have r2587 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2588 := hb (x (-1) 9)
                        have b2589 := hb (x 8 6)
                        have b2590 := hb (x 7 1 && x 7 7)
                        have b2591 := hb (x 6 2 && x 6 8)
                        have b2592 := hb (x 5 3 && x 5 9)
                        have b2593 := hb (x 4 4 && x 4 10)
                        have b2594 := hb (x 3 5 && x 3 11)
                        have b2595 := hb (x 2 6 && x 2 12)
                        have b2596 := hb (x 1 7 && x 1 13)
                        have b2597 := hb (x 0 8 && x 0 14)
                        clear * - r2587 b2588 b2589 b2590 b2591 b2592 b2593 b2594 b2595 b2596 b2597 d2582 d2118 d2142 g125 g126 d2386 g127 g128 f1379
                        omega
                      have d2598 : (x 14 8).toNat = 0 := by
                        have r2599 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2600 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e2601 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e2602 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e2603 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e2604 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e2605 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b2606 := hb (x 7 7)
                        have b2607 := hb (x 8 6)
                        have b2608 := hb (x 9 5)
                        have b2609 := hb (x 10 4)
                        have b2610 := hb (x 11 11)
                        have b2611 := hb (x 12 10)
                        have b2612 := hb (x 13 9)
                        have b2613 := hb (x 14 8)
                        clear * - r2599 e2600 e2601 e2602 e2603 e2604 e2605 b2606 b2607 b2608 b2609 b2610 b2611 b2612 b2613 d2586
                        omega
                      have d2614 : (x 13 9).toNat = 0 := by
                        have r2615 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2616 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e2617 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e2618 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e2619 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e2620 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e2621 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b2622 := hb (x 7 7)
                        have b2623 := hb (x 8 6)
                        have b2624 := hb (x 9 5)
                        have b2625 := hb (x 10 4)
                        have b2626 := hb (x 11 11)
                        have b2627 := hb (x 12 10)
                        have b2628 := hb (x 13 9)
                        have b2629 := hb (x 14 8)
                        clear * - r2615 e2616 e2617 e2618 e2619 e2620 e2621 b2622 b2623 b2624 b2625 b2626 b2627 b2628 b2629 d2598 d2586
                        omega
                      have d2630 : (x 12 10).toNat = 0 := by
                        have r2631 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2632 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e2633 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e2634 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e2635 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e2636 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e2637 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b2638 := hb (x 7 7)
                        have b2639 := hb (x 8 6)
                        have b2640 := hb (x 9 5)
                        have b2641 := hb (x 10 4)
                        have b2642 := hb (x 11 11)
                        have b2643 := hb (x 12 10)
                        have b2644 := hb (x 13 9)
                        have b2645 := hb (x 14 8)
                        clear * - r2631 e2632 e2633 e2634 e2635 e2636 e2637 b2638 b2639 b2640 b2641 b2642 b2643 b2644 b2645 d2598 d2614 d2586
                        omega
                      have d2646 : (x 11 11).toNat = 0 := by
                        have r2647 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2648 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e2649 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e2650 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e2651 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e2652 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e2653 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b2654 := hb (x 7 7)
                        have b2655 := hb (x 8 6)
                        have b2656 := hb (x 9 5)
                        have b2657 := hb (x 10 4)
                        have b2658 := hb (x 11 11)
                        have b2659 := hb (x 12 10)
                        have b2660 := hb (x 13 9)
                        have b2661 := hb (x 14 8)
                        clear * - r2647 e2648 e2649 e2650 e2651 e2652 e2653 b2654 b2655 b2656 b2657 b2658 b2659 b2660 b2661 d2598 d2614 d2630 d2586
                        omega
                      have d2662 : (x 11 1 && x 11 11).toNat = 0 := by
                        have r2663 := hand2 (x 11 1) (x 11 11)
                        have b2664 := hb (x 11 11)
                        have b2665 := hb (x 11 1 && x 11 11)
                        clear * - r2663 b2664 b2665 d2646
                        omega
                      have d2666 : (x 10 4).toNat = 0 := by
                        have r2667 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2668 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e2669 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e2670 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e2671 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e2672 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e2673 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b2674 := hb (x 7 7)
                        have b2675 := hb (x 8 6)
                        have b2676 := hb (x 9 5)
                        have b2677 := hb (x 10 4)
                        have b2678 := hb (x 11 11)
                        have b2679 := hb (x 12 10)
                        have b2680 := hb (x 13 9)
                        have b2681 := hb (x 14 8)
                        clear * - r2667 e2668 e2669 e2670 e2671 e2672 e2673 b2674 b2675 b2676 b2677 b2678 b2679 b2680 b2681 d2598 d2614 d2630 d2646 d2586
                        omega
                      have d2682 : (x 10 4 && x 10 14).toNat = 0 := by
                        have r2683 := hand1 (x 10 4) (x 10 14)
                        have b2684 := hb (x 10 4)
                        have b2685 := hb (x 10 4 && x 10 14)
                        clear * - r2683 b2684 b2685 d2666
                        omega
                      have d2686 : (x 9 5).toNat = 0 := by
                        have r2687 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2688 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e2689 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e2690 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e2691 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e2692 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e2693 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b2694 := hb (x 7 7)
                        have b2695 := hb (x 8 6)
                        have b2696 := hb (x 9 5)
                        have b2697 := hb (x 10 4)
                        have b2698 := hb (x 11 11)
                        have b2699 := hb (x 12 10)
                        have b2700 := hb (x 13 9)
                        have b2701 := hb (x 14 8)
                        clear * - r2687 e2688 e2689 e2690 e2691 e2692 e2693 b2694 b2695 b2696 b2697 b2698 b2699 b2700 b2701 d2598 d2614 d2630 d2646 d2666 d2586
                        omega
                      have d2702 : (x 7 7).toNat = 0 := by
                        have r2703 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2704 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e2705 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e2706 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e2707 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e2708 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e2709 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b2710 := hb (x 7 7)
                        have b2711 := hb (x 8 6)
                        have b2712 := hb (x 9 5)
                        have b2713 := hb (x 10 4)
                        have b2714 := hb (x 11 11)
                        have b2715 := hb (x 12 10)
                        have b2716 := hb (x 13 9)
                        have b2717 := hb (x 14 8)
                        clear * - r2703 e2704 e2705 e2706 e2707 e2708 e2709 b2710 b2711 b2712 b2713 b2714 b2715 b2716 b2717 d2598 d2614 d2630 d2646 d2666 d2686 d2586
                        omega
                      have d2718 : (x 7 13).toNat = 0 := by
                        have r2719 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
                        have b2720 := hb (x 7 1)
                        have b2721 := hb (x 7 13)
                        clear * - r2719 b2720 b2721 d2570
                        omega
                      have d2722 : (x 7 5).toNat = 0 := by
                        have r2723 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                        have b2724 := hb (x 7 5)
                        have b2725 := hb (x 7 13)
                        clear * - r2723 b2724 b2725 d2718
                        omega
                      have d2726 : (x 7 9).toNat = 0 := by
                        have r2727 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
                        have b2728 := hb (x 7 1)
                        have b2729 := hb (x 7 9)
                        clear * - r2727 b2728 b2729 d2570
                        omega
                      have d2730 : (x 10 12).toNat = 0 := by
                        have r2731 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2732 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                        have e2733 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                        have b2734 := hb (x 7 3)
                        have b2735 := hb (x 8 2)
                        have b2736 := hb (x 9 13)
                        have b2737 := hb (x 10 12)
                        clear * - r2731 e2732 e2733 b2734 b2735 b2736 b2737 d2562
                        omega
                      have d2738 : (x 10 2 && x 10 12).toNat = 0 := by
                        have r2739 := hand2 (x 10 2) (x 10 12)
                        have b2740 := hb (x 10 12)
                        have b2741 := hb (x 10 2 && x 10 12)
                        clear * - r2739 b2740 b2741 d2730
                        omega
                      have d2742 : (x 9 13).toNat = 0 := by
                        have r2743 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2744 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                        have e2745 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                        have b2746 := hb (x 7 3)
                        have b2747 := hb (x 8 2)
                        have b2748 := hb (x 9 13)
                        have b2749 := hb (x 10 12)
                        clear * - r2743 e2744 e2745 b2746 b2747 b2748 b2749 d2730 d2562
                        omega
                      have d2750 : (x 9 3 && x 9 13).toNat = 0 := by
                        have r2751 := hand2 (x 9 3) (x 9 13)
                        have b2752 := hb (x 9 13)
                        have b2753 := hb (x 9 3 && x 9 13)
                        clear * - r2751 b2752 b2753 d2742
                        omega
                      have d2754 : (x 8 4 && x 8 14).toNat = 1 := by
                        have r2755 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2756 := hb (x 7 5)
                        have b2757 := hb (x 12 10)
                        have b2758 := hb (x 11 1 && x 11 11)
                        have b2759 := hb (x 10 2 && x 10 12)
                        have b2760 := hb (x 9 3 && x 9 13)
                        have b2761 := hb (x 8 4 && x 8 14)
                        clear * - r2755 b2756 b2757 b2758 b2759 b2760 b2761 d2630 d2662 d2738 d2750 d2722
                        omega
                      have d2762 : (x 8 4).toNat = 1 := by
                        have r2763 := hand1 (x 8 4) (x 8 14)
                        have b2764 := hb (x 8 4)
                        have b2765 := hb (x 8 4 && x 8 14)
                        clear * - r2763 b2764 b2765 d2754
                        omega
                      have d2766 : (x 8 12).toNat = 1 := by
                        have r2767 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
                        have b2768 := hb (x 8 4)
                        have b2769 := hb (x 8 12)
                        clear * - r2767 b2768 b2769 d2762
                        omega
                      have d2770 : (x 6 2).toNat = 0 := by
                        have r2771 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2772 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                        have e2773 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                        have b2774 := hb (x 5 3)
                        have b2775 := hb (x 6 2)
                        have b2776 := hb (x 7 13)
                        have b2777 := hb (x 8 12)
                        clear * - r2771 e2772 e2773 b2774 b2775 b2776 b2777 d2766 d2718
                        omega
                      have d2778 : (x 6 2 && x 6 11).toNat = 0 := by
                        have r2779 := hand1 (x 6 2) (x 6 11)
                        have b2780 := hb (x 6 2)
                        have b2781 := hb (x 6 2 && x 6 11)
                        clear * - r2779 b2780 b2781 d2770
                        omega
                      have d2782 : (x 8 9).toNat = 1 := by
                        have r2783 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2784 := hb (x 2 6)
                        have b2785 := hb (x 8 9)
                        have b2786 := hb (x 7 1 && x 7 10)
                        have b2787 := hb (x 6 2 && x 6 11)
                        have b2788 := hb (x 5 3 && x 5 12)
                        have b2789 := hb (x 4 4 && x 4 13)
                        have b2790 := hb (x 3 5 && x 3 14)
                        clear * - r2783 b2784 b2785 b2786 b2787 b2788 b2789 b2790 d2578 d2778 g143 g144 g145 f2381
                        omega
                      have d2791 : (x 8 1).toNat = 1 := by
                        have r2792 : (x 8 9).toNat ≤ (x 8 1).toNat := himp _ _ (hp9 8)
                        have b2793 := hb (x 8 1)
                        have b2794 := hb (x 8 9)
                        clear * - r2792 b2793 b2794 d2782
                        omega
                      have d2795 : (x 9 14).toNat = 0 := by
                        have r2796 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2797 := hb (x 8 1)
                        have b2798 := hb (x 9 14)
                        clear * - r2796 b2797 b2798 d2791
                        omega
                      have d2799 : (x 9 4 && x 9 14).toNat = 0 := by
                        have r2800 := hand2 (x 9 4) (x 9 14)
                        have b2801 := hb (x 9 14)
                        have b2802 := hb (x 9 4 && x 9 14)
                        clear * - r2800 b2801 b2802 d2795
                        omega
                      have d2803 : (x 9 2).toNat = 0 := by
                        have r2804 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                        have b2805 := hb (x 9 2)
                        have b2806 := hb (x 9 14)
                        clear * - r2804 b2805 b2806 d2795
                        omega
                      have d2807 : (x 9 10).toNat = 0 := by
                        have r2808 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                        have b2809 := hb (x 9 2)
                        have b2810 := hb (x 9 10)
                        clear * - r2808 b2809 b2810 d2803
                        omega
                      have d2811 : (x 9 8).toNat = 0 := by
                        have r2812 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2813 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e2814 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e2815 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e2816 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e2817 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e2818 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b2819 := hb (x 2 7)
                        have b2820 := hb (x 3 6)
                        have b2821 := hb (x 4 5)
                        have b2822 := hb (x 5 4)
                        have b2823 := hb (x 6 11)
                        have b2824 := hb (x 7 10)
                        have b2825 := hb (x 8 9)
                        have b2826 := hb (x 9 8)
                        clear * - r2812 e2813 e2814 e2815 e2816 e2817 e2818 b2819 b2820 b2821 b2822 b2823 b2824 b2825 b2826 d2782 g64 g60 g54
                        omega
                      have d2827 : (x 7 10).toNat = 0 := by
                        have r2828 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2829 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e2830 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e2831 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e2832 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e2833 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e2834 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b2835 := hb (x 2 7)
                        have b2836 := hb (x 3 6)
                        have b2837 := hb (x 4 5)
                        have b2838 := hb (x 5 4)
                        have b2839 := hb (x 6 11)
                        have b2840 := hb (x 7 10)
                        have b2841 := hb (x 8 9)
                        have b2842 := hb (x 9 8)
                        clear * - r2828 e2829 e2830 e2831 e2832 e2833 e2834 b2835 b2836 b2837 b2838 b2839 b2840 b2841 b2842 d2811 d2782 g64 g60 g54
                        omega
                      have d2843 : (x 6 11).toNat = 0 := by
                        have r2844 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2845 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e2846 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e2847 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e2848 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e2849 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e2850 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b2851 := hb (x 2 7)
                        have b2852 := hb (x 3 6)
                        have b2853 := hb (x 4 5)
                        have b2854 := hb (x 5 4)
                        have b2855 := hb (x 6 11)
                        have b2856 := hb (x 7 10)
                        have b2857 := hb (x 8 9)
                        have b2858 := hb (x 9 8)
                        clear * - r2844 e2845 e2846 e2847 e2848 e2849 e2850 b2851 b2852 b2853 b2854 b2855 b2856 b2857 b2858 d2811 d2782 d2827 g64 g60 g54
                        omega
                      have d2859 : (x 6 10).toNat = 0 := by
                        have r2860 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
                        have b2861 := hb (x 6 2)
                        have b2862 := hb (x 6 10)
                        clear * - r2860 b2861 b2862 d2770
                        omega
                      have d2863 : (x 8 13).toNat = 1 := by
                        have r2864 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2865 := hb (x 6 2)
                        have b2866 := hb (x 8 13)
                        have b2867 := hb (x 7 1 && x 7 14)
                        clear * - r2864 b2865 b2866 b2867 d2574 d2770
                        omega
                      have d2868 : (x 9 12).toNat = 0 := by
                        have r2869 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2870 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e2871 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b2872 := hb (x 6 3)
                        have b2873 := hb (x 7 2)
                        have b2874 := hb (x 8 13)
                        have b2875 := hb (x 9 12)
                        clear * - r2869 e2870 e2871 b2872 b2873 b2874 b2875 d2863
                        omega
                      have d2876 : (x 9 4).toNat = 0 := by
                        have r2877 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                        have b2878 := hb (x 9 4)
                        have b2879 := hb (x 9 12)
                        clear * - r2877 b2878 b2879 d2868
                        omega
                      have d2880 : (x 7 2).toNat = 0 := by
                        have r2881 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2882 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e2883 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b2884 := hb (x 6 3)
                        have b2885 := hb (x 7 2)
                        have b2886 := hb (x 8 13)
                        have b2887 := hb (x 9 12)
                        clear * - r2881 e2882 e2883 b2884 b2885 b2886 b2887 d2868 d2863
                        omega
                      have d2888 : (x 7 2 && x 7 12).toNat = 0 := by
                        have r2889 := hand1 (x 7 2) (x 7 12)
                        have b2890 := hb (x 7 2)
                        have b2891 := hb (x 7 2 && x 7 12)
                        clear * - r2889 b2890 b2891 d2880
                        omega
                      have d2892 : (x 6 3).toNat = 0 := by
                        have r2893 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2894 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e2895 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b2896 := hb (x 6 3)
                        have b2897 := hb (x 7 2)
                        have b2898 := hb (x 8 13)
                        have b2899 := hb (x 9 12)
                        clear * - r2893 e2894 e2895 b2896 b2897 b2898 b2899 d2868 d2863 d2880
                        omega
                      have d2900 : (x 6 3 && x 6 13).toNat = 0 := by
                        have r2901 := hand1 (x 6 3) (x 6 13)
                        have b2902 := hb (x 6 3)
                        have b2903 := hb (x 6 3 && x 6 13)
                        clear * - r2901 b2902 b2903 d2892
                        omega
                      have d2904 : (x 8 1 && x 8 11).toNat = 1 := by
                        have r2905 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2906 := hb (x 4 5)
                        have b2907 := hb (x 9 10)
                        have b2908 := hb (x 8 1 && x 8 11)
                        have b2909 := hb (x 7 2 && x 7 12)
                        have b2910 := hb (x 6 3 && x 6 13)
                        have b2911 := hb (x 5 4 && x 5 14)
                        clear * - r2905 b2906 b2907 b2908 b2909 b2910 b2911 d2807 d2888 d2900 g158 g60
                        omega
                      have d2912 : (x 8 11).toNat = 1 := by
                        have r2913 := hand2 (x 8 1) (x 8 11)
                        have b2914 := hb (x 8 11)
                        have b2915 := hb (x 8 1 && x 8 11)
                        clear * - r2913 b2914 b2915 d2904
                        omega
                      have d2916 : (x 8 3).toNat = 1 := by
                        have r2917 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                        have b2918 := hb (x 8 3)
                        have b2919 := hb (x 8 11)
                        clear * - r2917 b2918 b2919 d2912
                        omega
                      have d2920 : (x 11 12).toNat = 0 := by
                        have r2921 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2922 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                        have e2923 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                        have b2924 := hb (x 8 3)
                        have b2925 := hb (x 9 2)
                        have b2926 := hb (x 10 13)
                        have b2927 := hb (x 11 12)
                        clear * - r2921 e2922 e2923 b2924 b2925 b2926 b2927 d2803 d2916
                        omega
                      have d2928 : (x 11 2 && x 11 12).toNat = 0 := by
                        have r2929 := hand2 (x 11 2) (x 11 12)
                        have b2930 := hb (x 11 12)
                        have b2931 := hb (x 11 2 && x 11 12)
                        clear * - r2929 b2930 b2931 d2920
                        omega
                      have d2932 : (x 11 12 && x 11 13).toNat = 0 := by
                        have r2933 := hand1 (x 11 12) (x 11 13)
                        have b2934 := hb (x 11 12)
                        have b2935 := hb (x 11 12 && x 11 13)
                        clear * - r2933 b2934 b2935 d2920
                        omega
                      have d2936 : (x 10 13).toNat = 0 := by
                        have r2937 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2938 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                        have e2939 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                        have b2940 := hb (x 8 3)
                        have b2941 := hb (x 9 2)
                        have b2942 := hb (x 10 13)
                        have b2943 := hb (x 11 12)
                        clear * - r2937 e2938 e2939 b2940 b2941 b2942 b2943 d2920 d2803 d2916
                        omega
                      have d2944 : (x 10 3 && x 10 13).toNat = 0 := by
                        have r2945 := hand2 (x 10 3) (x 10 13)
                        have b2946 := hb (x 10 13)
                        have b2947 := hb (x 10 3 && x 10 13)
                        clear * - r2945 b2946 b2947 d2936
                        omega
                      have d2948 : (x 8 5).toNat = 1 := by
                        have r2949 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b2950 := hb (x 8 5)
                        have b2951 := hb (x 13 10)
                        have b2952 := hb (x 12 1 && x 12 11)
                        have b2953 := hb (x 11 2 && x 11 12)
                        have b2954 := hb (x 10 3 && x 10 13)
                        have b2955 := hb (x 9 4 && x 9 14)
                        clear * - r2949 b2950 b2951 b2952 b2953 b2954 b2955 d2441 d2477 d2928 d2944 d2799
                        omega
                      have d2956 : (x 13 8).toNat = 0 := by
                        have r2957 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2958 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                        have e2959 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                        have e2960 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                        have e2961 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                        have e2962 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                        have e2963 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                        have b2964 := hb (x 6 7)
                        have b2965 := hb (x 7 6)
                        have b2966 := hb (x 8 5)
                        have b2967 := hb (x 9 4)
                        have b2968 := hb (x 10 11)
                        have b2969 := hb (x 11 10)
                        have b2970 := hb (x 12 9)
                        have b2971 := hb (x 13 8)
                        clear * - r2957 e2958 e2959 e2960 e2961 e2962 e2963 b2964 b2965 b2966 b2967 b2968 b2969 b2970 b2971 d2876 d2948
                        omega
                      have d2972 : (x 12 9).toNat = 0 := by
                        have r2973 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2974 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                        have e2975 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                        have e2976 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                        have e2977 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                        have e2978 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                        have e2979 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                        have b2980 := hb (x 6 7)
                        have b2981 := hb (x 7 6)
                        have b2982 := hb (x 8 5)
                        have b2983 := hb (x 9 4)
                        have b2984 := hb (x 10 11)
                        have b2985 := hb (x 11 10)
                        have b2986 := hb (x 12 9)
                        have b2987 := hb (x 13 8)
                        clear * - r2973 e2974 e2975 e2976 e2977 e2978 e2979 b2980 b2981 b2982 b2983 b2984 b2985 b2986 b2987 d2956 d2876 d2948
                        omega
                      have d2988 : (x 11 10).toNat = 0 := by
                        have r2989 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e2990 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                        have e2991 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                        have e2992 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                        have e2993 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                        have e2994 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                        have e2995 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                        have b2996 := hb (x 6 7)
                        have b2997 := hb (x 7 6)
                        have b2998 := hb (x 8 5)
                        have b2999 := hb (x 9 4)
                        have b3000 := hb (x 10 11)
                        have b3001 := hb (x 11 10)
                        have b3002 := hb (x 12 9)
                        have b3003 := hb (x 13 8)
                        clear * - r2989 e2990 e2991 e2992 e2993 e2994 e2995 b2996 b2997 b2998 b2999 b3000 b3001 b3002 b3003 d2956 d2972 d2876 d2948
                        omega
                      have d3004 : (x 10 11).toNat = 0 := by
                        have r3005 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3006 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                        have e3007 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                        have e3008 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                        have e3009 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                        have e3010 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                        have e3011 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                        have b3012 := hb (x 6 7)
                        have b3013 := hb (x 7 6)
                        have b3014 := hb (x 8 5)
                        have b3015 := hb (x 9 4)
                        have b3016 := hb (x 10 11)
                        have b3017 := hb (x 11 10)
                        have b3018 := hb (x 12 9)
                        have b3019 := hb (x 13 8)
                        clear * - r3005 e3006 e3007 e3008 e3009 e3010 e3011 b3012 b3013 b3014 b3015 b3016 b3017 b3018 b3019 d2956 d2972 d2988 d2876 d2948
                        omega
                      have d3020 : (x 7 6).toNat = 0 := by
                        have r3021 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3022 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                        have e3023 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                        have e3024 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                        have e3025 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                        have e3026 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                        have e3027 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                        have b3028 := hb (x 6 7)
                        have b3029 := hb (x 7 6)
                        have b3030 := hb (x 8 5)
                        have b3031 := hb (x 9 4)
                        have b3032 := hb (x 10 11)
                        have b3033 := hb (x 11 10)
                        have b3034 := hb (x 12 9)
                        have b3035 := hb (x 13 8)
                        clear * - r3021 e3022 e3023 e3024 e3025 e3026 e3027 b3028 b3029 b3030 b3031 b3032 b3033 b3034 b3035 d2956 d2972 d2988 d3004 d2876 d2948
                        omega
                      have d3036 : (x 6 7).toNat = 0 := by
                        have r3037 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3038 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                        have e3039 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                        have e3040 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                        have e3041 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                        have e3042 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                        have e3043 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                        have b3044 := hb (x 6 7)
                        have b3045 := hb (x 7 6)
                        have b3046 := hb (x 8 5)
                        have b3047 := hb (x 9 4)
                        have b3048 := hb (x 10 11)
                        have b3049 := hb (x 11 10)
                        have b3050 := hb (x 12 9)
                        have b3051 := hb (x 13 8)
                        clear * - r3037 e3038 e3039 e3040 e3041 e3042 e3043 b3044 b3045 b3046 b3047 b3048 b3049 b3050 b3051 d2956 d2972 d2988 d3004 d2876 d2948 d3020
                        omega
                      have d3052 : (x 10 13 && x 10 14).toNat = 0 := by
                        have r3053 := hand1 (x 10 13) (x 10 14)
                        have b3054 := hb (x 10 13)
                        have b3055 := hb (x 10 13 && x 10 14)
                        clear * - r3053 b3054 b3055 d2936
                        omega
                      have d3056 : (x 5 3).toNat = 0 := by
                        have r3057 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3058 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                        have e3059 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                        have b3060 := hb (x 5 3)
                        have b3061 := hb (x 6 2)
                        have b3062 := hb (x 7 13)
                        have b3063 := hb (x 8 12)
                        clear * - r3057 e3058 e3059 b3060 b3061 b3062 b3063 d2766 d2718 d2770
                        omega
                      have d3064 : (x 5 11).toNat = 0 := by
                        have r3065 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                        have b3066 := hb (x 5 3)
                        have b3067 := hb (x 5 11)
                        clear * - r3065 b3066 b3067 d3056
                        omega
                      have d3068 : (x 8 8).toNat = 1 := by
                        have r3069 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3070 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e3071 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e3072 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e3073 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e3074 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e3075 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b3076 := hb (x 1 7)
                        have b3077 := hb (x 2 6)
                        have b3078 := hb (x 3 5)
                        have b3079 := hb (x 4 4)
                        have b3080 := hb (x 5 11)
                        have b3081 := hb (x 6 10)
                        have b3082 := hb (x 7 9)
                        have b3083 := hb (x 8 8)
                        clear * - r3069 e3070 e3071 e3072 e3073 e3074 e3075 b3076 b3077 b3078 b3079 b3080 b3081 b3082 b3083 d2726 d2859 d3064 g59 g53 f2381 f1367
                        omega
                      have d3084 : (x 14 1).toNat = 0 := by
                        have r3085 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3086 := hb (x 1 14)
                        have b3087 := hb (x 2 13)
                        have b3088 := hb (x 3 12)
                        have b3089 := hb (x 4 11)
                        have b3090 := hb (x 5 10)
                        have b3091 := hb (x 6 9)
                        have b3092 := hb (x 7 8)
                        have b3093 := hb (x 8 7)
                        have b3094 := hb (x 9 6)
                        have b3095 := hb (x 10 5)
                        have b3096 := hb (x 11 4)
                        have b3097 := hb (x 12 3)
                        have b3098 := hb (x 13 2)
                        have b3099 := hb (x 14 1)
                        clear * - r3085 b3086 b3087 b3088 b3089 b3090 b3091 b3092 b3093 b3094 b3095 b3096 b3097 b3098 b3099 d2485 d2509 d2529 d2390 d2252 d2276 d2300 d2324 g56 g49 g47
                        omega
                      have d3100 : (x 14 1 && x 14 14).toNat = 0 := by
                        have r3101 := hand1 (x 14 1) (x 14 14)
                        have b3102 := hb (x 14 1)
                        have b3103 := hb (x 14 1 && x 14 14)
                        clear * - r3101 b3102 b3103 d3084
                        omega
                      have d3104 : (x 14 1 && x 14 11).toNat = 0 := by
                        have r3105 := hand1 (x 14 1) (x 14 11)
                        have b3106 := hb (x 14 1)
                        have b3107 := hb (x 14 1 && x 14 11)
                        clear * - r3105 b3106 b3107 d3084
                        omega
                      have d3108 : (x 14 1 && x 14 10).toNat = 0 := by
                        have r3109 := hand1 (x 14 1) (x 14 10)
                        have b3110 := hb (x 14 1)
                        have b3111 := hb (x 14 1 && x 14 10)
                        clear * - r3109 b3110 b3111 d3084
                        omega
                      have d3112 : (x 13 2).toNat = 0 := by
                        have r3113 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3114 := hb (x 1 14)
                        have b3115 := hb (x 2 13)
                        have b3116 := hb (x 3 12)
                        have b3117 := hb (x 4 11)
                        have b3118 := hb (x 5 10)
                        have b3119 := hb (x 6 9)
                        have b3120 := hb (x 7 8)
                        have b3121 := hb (x 8 7)
                        have b3122 := hb (x 9 6)
                        have b3123 := hb (x 10 5)
                        have b3124 := hb (x 11 4)
                        have b3125 := hb (x 12 3)
                        have b3126 := hb (x 13 2)
                        have b3127 := hb (x 14 1)
                        clear * - r3113 b3114 b3115 b3116 b3117 b3118 b3119 b3120 b3121 b3122 b3123 b3124 b3125 b3126 b3127 d3084 d2485 d2509 d2529 d2390 d2252 d2276 d2300 d2324 g56 g49 g47
                        omega
                      have d3128 : (x 13 2 && x 13 12).toNat = 0 := by
                        have r3129 := hand1 (x 13 2) (x 13 12)
                        have b3130 := hb (x 13 2)
                        have b3131 := hb (x 13 2 && x 13 12)
                        clear * - r3129 b3130 b3131 d3112
                        omega
                      have d3132 : (x 13 2 && x 13 11).toNat = 0 := by
                        have r3133 := hand1 (x 13 2) (x 13 11)
                        have b3134 := hb (x 13 2)
                        have b3135 := hb (x 13 2 && x 13 11)
                        clear * - r3133 b3134 b3135 d3112
                        omega
                      have d3136 : (x 15 13).toNat = 1 := by
                        have r3137 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3138 := hb (x 13 2)
                        have b3139 := hb (x 15 13)
                        have b3140 := hb (x 14 1 && x 14 14)
                        clear * - r3137 b3138 b3139 b3140 d3100 d3112
                        omega
                      have d3141 : (x 15 1).toNat = 1 := by
                        have r3142 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
                        have b3143 := hb (x 15 1)
                        have b3144 := hb (x 15 13)
                        clear * - r3142 b3143 b3144 d3136
                        omega
                      have d3145 : (x 16 14).toNat = 0 := by
                        have r3146 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3147 := hb (x 15 1)
                        have b3148 := hb (x 16 14)
                        clear * - r3146 b3147 b3148 d3141
                        omega
                      have d3149 : (x 16 1 && x 16 14).toNat = 0 := by
                        have r3150 := hand2 (x 16 1) (x 16 14)
                        have b3151 := hb (x 16 14)
                        have b3152 := hb (x 16 1 && x 16 14)
                        clear * - r3150 b3151 b3152 d3145
                        omega
                      have d3153 : (x 16 6).toNat = 0 := by
                        have r3154 : (x 16 6).toNat ≤ (x 16 14).toNat := himp _ _ (hp6 16)
                        have b3155 := hb (x 16 6)
                        have b3156 := hb (x 16 14)
                        clear * - r3154 b3155 b3156 d3145
                        omega
                      have d3157 : (x 16 2).toNat = 0 := by
                        have r3158 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
                        have b3159 := hb (x 16 2)
                        have b3160 := hb (x 16 14)
                        clear * - r3158 b3159 b3160 d3145
                        omega
                      have d3161 : (x 16 10).toNat = 0 := by
                        have r3162 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
                        have b3163 := hb (x 16 2)
                        have b3164 := hb (x 16 10)
                        clear * - r3162 b3163 b3164 d3157
                        omega
                      have d3165 : (x 14 2).toNat = 0 := by
                        have r3166 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3167 := hb (x 2 14)
                        have b3168 := hb (x 3 13)
                        have b3169 := hb (x 4 12)
                        have b3170 := hb (x 5 11)
                        have b3171 := hb (x 6 10)
                        have b3172 := hb (x 7 9)
                        have b3173 := hb (x 8 8)
                        have b3174 := hb (x 9 7)
                        have b3175 := hb (x 10 6)
                        have b3176 := hb (x 11 5)
                        have b3177 := hb (x 12 4)
                        have b3178 := hb (x 13 3)
                        have b3179 := hb (x 14 2)
                        have b3180 := hb (x 15 1)
                        clear * - r3166 b3167 b3168 b3169 b3170 b3171 b3172 b3173 b3174 b3175 b3176 b3177 b3178 b3179 b3180 d3141 d3068 d2726 d2859 d3064 g62 g57 g50
                        omega
                      have d3181 : (x 14 2 && x 14 12).toNat = 0 := by
                        have r3182 := hand1 (x 14 2) (x 14 12)
                        have b3183 := hb (x 14 2)
                        have b3184 := hb (x 14 2 && x 14 12)
                        clear * - r3182 b3183 b3184 d3165
                        omega
                      have d3185 : (x 14 10).toNat = 0 := by
                        have r3186 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
                        have b3187 := hb (x 14 2)
                        have b3188 := hb (x 14 10)
                        clear * - r3186 b3187 b3188 d3165
                        omega
                      have d3189 : (x 13 3).toNat = 0 := by
                        have r3190 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3191 := hb (x 2 14)
                        have b3192 := hb (x 3 13)
                        have b3193 := hb (x 4 12)
                        have b3194 := hb (x 5 11)
                        have b3195 := hb (x 6 10)
                        have b3196 := hb (x 7 9)
                        have b3197 := hb (x 8 8)
                        have b3198 := hb (x 9 7)
                        have b3199 := hb (x 10 6)
                        have b3200 := hb (x 11 5)
                        have b3201 := hb (x 12 4)
                        have b3202 := hb (x 13 3)
                        have b3203 := hb (x 14 2)
                        have b3204 := hb (x 15 1)
                        clear * - r3190 b3191 b3192 b3193 b3194 b3195 b3196 b3197 b3198 b3199 b3200 b3201 b3202 b3203 b3204 d3141 d3165 d3068 d2726 d2859 d3064 g62 g57 g50
                        omega
                      have d3205 : (x 13 3 && x 13 13).toNat = 0 := by
                        have r3206 := hand1 (x 13 3) (x 13 13)
                        have b3207 := hb (x 13 3)
                        have b3208 := hb (x 13 3 && x 13 13)
                        clear * - r3206 b3207 b3208 d3189
                        omega
                      have d3209 : (x 13 11).toNat = 0 := by
                        have r3210 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                        have b3211 := hb (x 13 3)
                        have b3212 := hb (x 13 11)
                        clear * - r3210 b3211 b3212 d3189
                        omega
                      have d3213 : (x 13 1 && x 13 11).toNat = 0 := by
                        have r3214 := hand2 (x 13 1) (x 13 11)
                        have b3215 := hb (x 13 11)
                        have b3216 := hb (x 13 1 && x 13 11)
                        clear * - r3214 b3215 b3216 d3209
                        omega
                      have d3217 : (x 12 4).toNat = 0 := by
                        have r3218 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3219 := hb (x 2 14)
                        have b3220 := hb (x 3 13)
                        have b3221 := hb (x 4 12)
                        have b3222 := hb (x 5 11)
                        have b3223 := hb (x 6 10)
                        have b3224 := hb (x 7 9)
                        have b3225 := hb (x 8 8)
                        have b3226 := hb (x 9 7)
                        have b3227 := hb (x 10 6)
                        have b3228 := hb (x 11 5)
                        have b3229 := hb (x 12 4)
                        have b3230 := hb (x 13 3)
                        have b3231 := hb (x 14 2)
                        have b3232 := hb (x 15 1)
                        clear * - r3218 b3219 b3220 b3221 b3222 b3223 b3224 b3225 b3226 b3227 b3228 b3229 b3230 b3231 b3232 d3141 d3165 d3189 d3068 d2726 d2859 d3064 g62 g57 g50
                        omega
                      have d3233 : (x 12 4 && x 12 14).toNat = 0 := by
                        have r3234 := hand1 (x 12 4) (x 12 14)
                        have b3235 := hb (x 12 4)
                        have b3236 := hb (x 12 4 && x 12 14)
                        clear * - r3234 b3235 b3236 d3217
                        omega
                      have d3237 : (x 11 5).toNat = 0 := by
                        have r3238 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3239 := hb (x 2 14)
                        have b3240 := hb (x 3 13)
                        have b3241 := hb (x 4 12)
                        have b3242 := hb (x 5 11)
                        have b3243 := hb (x 6 10)
                        have b3244 := hb (x 7 9)
                        have b3245 := hb (x 8 8)
                        have b3246 := hb (x 9 7)
                        have b3247 := hb (x 10 6)
                        have b3248 := hb (x 11 5)
                        have b3249 := hb (x 12 4)
                        have b3250 := hb (x 13 3)
                        have b3251 := hb (x 14 2)
                        have b3252 := hb (x 15 1)
                        clear * - r3238 b3239 b3240 b3241 b3242 b3243 b3244 b3245 b3246 b3247 b3248 b3249 b3250 b3251 b3252 d3141 d3165 d3189 d3217 d3068 d2726 d2859 d3064 g62 g57 g50
                        omega
                      have d3253 : (x 15 1 && x 15 11).toNat = 1 := by
                        have r3254 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3255 := hb (x 11 5)
                        have b3256 := hb (x 16 10)
                        have b3257 := hb (x 15 1 && x 15 11)
                        have b3258 := hb (x 14 2 && x 14 12)
                        have b3259 := hb (x 13 3 && x 13 13)
                        have b3260 := hb (x 12 4 && x 12 14)
                        clear * - r3254 b3255 b3256 b3257 b3258 b3259 b3260 d3161 d3181 d3205 d3233 d3237
                        omega
                      have d3261 : (x 15 11).toNat = 1 := by
                        have r3262 := hand2 (x 15 1) (x 15 11)
                        have b3263 := hb (x 15 11)
                        have b3264 := hb (x 15 1 && x 15 11)
                        clear * - r3262 b3263 b3264 d3253
                        omega
                      have d3265 : (x 15 3).toNat = 1 := by
                        have r3266 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
                        have b3267 := hb (x 15 3)
                        have b3268 := hb (x 15 11)
                        clear * - r3266 b3267 b3268 d3261
                        omega
                      have d3269 : (x 18 12).toNat = 0 := by
                        have r3270 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3271 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                        have e3272 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                        have b3273 := hb (x 15 3)
                        have b3274 := hb (x 16 2)
                        have b3275 := hb (x 17 13)
                        have b3276 := hb (x 18 12)
                        clear * - r3270 e3271 e3272 b3273 b3274 b3275 b3276 d3157 d3265
                        omega
                      have d3277 : (x 18 4).toNat = 0 := by
                        have r3278 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
                        have b3279 := hb (x 18 4)
                        have b3280 := hb (x 18 12)
                        clear * - r3278 b3279 b3280 d3269
                        omega
                      have d3281 : (x 18 4 && x 18 13).toNat = 0 := by
                        have r3282 := hand1 (x 18 4) (x 18 13)
                        have b3283 := hb (x 18 4)
                        have b3284 := hb (x 18 4 && x 18 13)
                        clear * - r3282 b3283 b3284 d3277
                        omega
                      have d3285 : (x 17 13).toNat = 0 := by
                        have r3286 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3287 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
                        have e3288 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
                        have b3289 := hb (x 15 3)
                        have b3290 := hb (x 16 2)
                        have b3291 := hb (x 17 13)
                        have b3292 := hb (x 18 12)
                        clear * - r3286 e3287 e3288 b3289 b3290 b3291 b3292 d3269 d3157 d3265
                        omega
                      have d3293 : (x 17 5).toNat = 0 := by
                        have r3294 : (x 17 5).toNat ≤ (x 17 13).toNat := himp _ _ (hp5 17)
                        have b3295 := hb (x 17 5)
                        have b3296 := hb (x 17 13)
                        clear * - r3294 b3295 b3296 d3285
                        omega
                      have d3297 : (x 17 5 && x 17 14).toNat = 0 := by
                        have r3298 := hand1 (x 17 5) (x 17 14)
                        have b3299 := hb (x 17 5)
                        have b3300 := hb (x 17 5 && x 17 14)
                        clear * - r3298 b3299 b3300 d3293
                        omega
                      have d3301 : (x 15 2).toNat = 1 := by
                        have r3302 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3303 := hb (x 15 2)
                        have b3304 := hb (x 17 13)
                        have b3305 := hb (x 16 1 && x 16 14)
                        clear * - r3302 b3303 b3304 b3305 d3285 d3149
                        omega
                      have d3306 : (x 17 12).toNat = 0 := by
                        have r3307 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3308 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                        have e3309 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                        have b3310 := hb (x 14 3)
                        have b3311 := hb (x 15 2)
                        have b3312 := hb (x 16 13)
                        have b3313 := hb (x 17 12)
                        clear * - r3307 e3308 e3309 b3310 b3311 b3312 b3313 d3301
                        omega
                      have d3314 : (x 16 13).toNat = 0 := by
                        have r3315 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3316 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                        have e3317 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                        have b3318 := hb (x 14 3)
                        have b3319 := hb (x 15 2)
                        have b3320 := hb (x 16 13)
                        have b3321 := hb (x 17 12)
                        clear * - r3315 e3316 e3317 b3318 b3319 b3320 b3321 d3306 d3301
                        omega
                      have d3322 : (x 14 3).toNat = 0 := by
                        have r3323 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3324 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                        have e3325 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                        have b3326 := hb (x 14 3)
                        have b3327 := hb (x 15 2)
                        have b3328 := hb (x 16 13)
                        have b3329 := hb (x 17 12)
                        clear * - r3323 e3324 e3325 b3326 b3327 b3328 b3329 d3306 d3314 d3301
                        omega
                      have d3330 : (x 14 11).toNat = 0 := by
                        have r3331 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                        have b3332 := hb (x 14 3)
                        have b3333 := hb (x 14 11)
                        clear * - r3331 b3332 b3333 d3322
                        omega
                      have d3334 : (x 10 6).toNat = 0 := by
                        have r3335 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3336 := hb (x 2 14)
                        have b3337 := hb (x 3 13)
                        have b3338 := hb (x 4 12)
                        have b3339 := hb (x 5 11)
                        have b3340 := hb (x 6 10)
                        have b3341 := hb (x 7 9)
                        have b3342 := hb (x 8 8)
                        have b3343 := hb (x 9 7)
                        have b3344 := hb (x 10 6)
                        have b3345 := hb (x 11 5)
                        have b3346 := hb (x 12 4)
                        have b3347 := hb (x 13 3)
                        have b3348 := hb (x 14 2)
                        have b3349 := hb (x 15 1)
                        clear * - r3335 b3336 b3337 b3338 b3339 b3340 b3341 b3342 b3343 b3344 b3345 b3346 b3347 b3348 b3349 d3141 d3165 d3189 d3217 d3237 d3068 d2726 d2859 d3064 g62 g57 g50
                        omega
                      have d3350 : (x 9 7).toNat = 0 := by
                        have r3351 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3352 := hb (x 2 14)
                        have b3353 := hb (x 3 13)
                        have b3354 := hb (x 4 12)
                        have b3355 := hb (x 5 11)
                        have b3356 := hb (x 6 10)
                        have b3357 := hb (x 7 9)
                        have b3358 := hb (x 8 8)
                        have b3359 := hb (x 9 7)
                        have b3360 := hb (x 10 6)
                        have b3361 := hb (x 11 5)
                        have b3362 := hb (x 12 4)
                        have b3363 := hb (x 13 3)
                        have b3364 := hb (x 14 2)
                        have b3365 := hb (x 15 1)
                        clear * - r3351 b3352 b3353 b3354 b3355 b3356 b3357 b3358 b3359 b3360 b3361 b3362 b3363 b3364 b3365 d3141 d3165 d3189 d3217 d3237 d3334 d3068 d2726 d2859 d3064 g62 g57 g50
                        omega
                      have d3366 : (x 12 3).toNat = 0 := by
                        have r3367 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3368 := hb (x 1 14)
                        have b3369 := hb (x 2 13)
                        have b3370 := hb (x 3 12)
                        have b3371 := hb (x 4 11)
                        have b3372 := hb (x 5 10)
                        have b3373 := hb (x 6 9)
                        have b3374 := hb (x 7 8)
                        have b3375 := hb (x 8 7)
                        have b3376 := hb (x 9 6)
                        have b3377 := hb (x 10 5)
                        have b3378 := hb (x 11 4)
                        have b3379 := hb (x 12 3)
                        have b3380 := hb (x 13 2)
                        have b3381 := hb (x 14 1)
                        clear * - r3367 b3368 b3369 b3370 b3371 b3372 b3373 b3374 b3375 b3376 b3377 b3378 b3379 b3380 b3381 d3084 d3112 d2485 d2509 d2529 d2390 d2252 d2276 d2300 d2324 g56 g49 g47
                        omega
                      have d3382 : (x 12 3 && x 12 13).toNat = 0 := by
                        have r3383 := hand1 (x 12 3) (x 12 13)
                        have b3384 := hb (x 12 3)
                        have b3385 := hb (x 12 3 && x 12 13)
                        clear * - r3383 b3384 b3385 d3366
                        omega
                      have d3386 : (x 15 10).toNat = 1 := by
                        have r3387 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3388 := hb (x 10 5)
                        have b3389 := hb (x 15 10)
                        have b3390 := hb (x 14 1 && x 14 11)
                        have b3391 := hb (x 13 2 && x 13 12)
                        have b3392 := hb (x 12 3 && x 12 13)
                        have b3393 := hb (x 11 4 && x 11 14)
                        clear * - r3387 b3388 b3389 b3390 b3391 b3392 b3393 d3104 d3128 d3382 d2501 d2509
                        omega
                      have d3394 : (x 17 8).toNat = 0 := by
                        have r3395 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3396 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                        have e3397 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                        have e3398 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                        have e3399 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                        have e3400 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                        have e3401 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                        have b3402 := hb (x 10 7)
                        have b3403 := hb (x 11 6)
                        have b3404 := hb (x 12 5)
                        have b3405 := hb (x 13 4)
                        have b3406 := hb (x 14 11)
                        have b3407 := hb (x 15 10)
                        have b3408 := hb (x 16 9)
                        have b3409 := hb (x 17 8)
                        clear * - r3395 e3396 e3397 e3398 e3399 e3400 e3401 b3402 b3403 b3404 b3405 b3406 b3407 b3408 b3409 d3386 d3330
                        omega
                      have d3410 : (x 16 9).toNat = 0 := by
                        have r3411 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3412 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                        have e3413 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                        have e3414 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                        have e3415 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                        have e3416 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                        have e3417 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                        have b3418 := hb (x 10 7)
                        have b3419 := hb (x 11 6)
                        have b3420 := hb (x 12 5)
                        have b3421 := hb (x 13 4)
                        have b3422 := hb (x 14 11)
                        have b3423 := hb (x 15 10)
                        have b3424 := hb (x 16 9)
                        have b3425 := hb (x 17 8)
                        clear * - r3411 e3412 e3413 e3414 e3415 e3416 e3417 b3418 b3419 b3420 b3421 b3422 b3423 b3424 b3425 d3394 d3386 d3330
                        omega
                      have d3426 : (x 13 4).toNat = 0 := by
                        have r3427 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3428 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                        have e3429 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                        have e3430 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                        have e3431 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                        have e3432 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                        have e3433 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                        have b3434 := hb (x 10 7)
                        have b3435 := hb (x 11 6)
                        have b3436 := hb (x 12 5)
                        have b3437 := hb (x 13 4)
                        have b3438 := hb (x 14 11)
                        have b3439 := hb (x 15 10)
                        have b3440 := hb (x 16 9)
                        have b3441 := hb (x 17 8)
                        clear * - r3427 e3428 e3429 e3430 e3431 e3432 e3433 b3434 b3435 b3436 b3437 b3438 b3439 b3440 b3441 d3394 d3410 d3386 d3330
                        omega
                      have d3442 : (x 12 5).toNat = 0 := by
                        have r3443 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3444 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                        have e3445 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                        have e3446 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                        have e3447 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                        have e3448 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                        have e3449 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                        have b3450 := hb (x 10 7)
                        have b3451 := hb (x 11 6)
                        have b3452 := hb (x 12 5)
                        have b3453 := hb (x 13 4)
                        have b3454 := hb (x 14 11)
                        have b3455 := hb (x 15 10)
                        have b3456 := hb (x 16 9)
                        have b3457 := hb (x 17 8)
                        clear * - r3443 e3444 e3445 e3446 e3447 e3448 e3449 b3450 b3451 b3452 b3453 b3454 b3455 b3456 b3457 d3394 d3410 d3386 d3330 d3426
                        omega
                      have d3458 : (x 11 6).toNat = 0 := by
                        have r3459 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3460 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                        have e3461 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                        have e3462 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                        have e3463 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                        have e3464 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                        have e3465 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                        have b3466 := hb (x 10 7)
                        have b3467 := hb (x 11 6)
                        have b3468 := hb (x 12 5)
                        have b3469 := hb (x 13 4)
                        have b3470 := hb (x 14 11)
                        have b3471 := hb (x 15 10)
                        have b3472 := hb (x 16 9)
                        have b3473 := hb (x 17 8)
                        clear * - r3459 e3460 e3461 e3462 e3463 e3464 e3465 b3466 b3467 b3468 b3469 b3470 b3471 b3472 b3473 d3394 d3410 d3386 d3330 d3426 d3442
                        omega
                      have d3474 : (x 10 7).toNat = 0 := by
                        have r3475 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3476 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                        have e3477 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                        have e3478 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                        have e3479 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                        have e3480 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                        have e3481 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                        have b3482 := hb (x 10 7)
                        have b3483 := hb (x 11 6)
                        have b3484 := hb (x 12 5)
                        have b3485 := hb (x 13 4)
                        have b3486 := hb (x 14 11)
                        have b3487 := hb (x 15 10)
                        have b3488 := hb (x 16 9)
                        have b3489 := hb (x 17 8)
                        clear * - r3475 e3476 e3477 e3478 e3479 e3480 e3481 b3482 b3483 b3484 b3485 b3486 b3487 b3488 b3489 d3394 d3410 d3386 d3330 d3426 d3442 d3458
                        omega
                      have d3490 : (x 16 1).toNat = 1 := by
                        have r3491 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3492 := hb (x 3 14)
                        have b3493 := hb (x 4 13)
                        have b3494 := hb (x 5 12)
                        have b3495 := hb (x 6 11)
                        have b3496 := hb (x 7 10)
                        have b3497 := hb (x 8 9)
                        have b3498 := hb (x 9 8)
                        have b3499 := hb (x 10 7)
                        have b3500 := hb (x 11 6)
                        have b3501 := hb (x 12 5)
                        have b3502 := hb (x 13 4)
                        have b3503 := hb (x 14 3)
                        have b3504 := hb (x 15 2)
                        have b3505 := hb (x 16 1)
                        clear * - r3491 b3492 b3493 b3494 b3495 b3496 b3497 b3498 b3499 b3500 b3501 b3502 b3503 b3504 b3505 d3301 d3322 d3426 d3442 d3458 d3474 d2811 d2782 d2827 d2843 g66 g63 g58
                        omega
                      have d3506 : (x 17 14).toNat = 0 := by
                        have r3507 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3508 := hb (x 16 1)
                        have b3509 := hb (x 17 14)
                        clear * - r3507 b3508 b3509 d3490
                        omega
                      have d3510 : (x 17 1 && x 17 14).toNat = 0 := by
                        have r3511 := hand2 (x 17 1) (x 17 14)
                        have b3512 := hb (x 17 14)
                        have b3513 := hb (x 17 1 && x 17 14)
                        clear * - r3511 b3512 b3513 d3506
                        omega
                      have d3514 : (x 18 13).toNat = 1 := by
                        have r3515 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3516 := hb (x 16 2)
                        have b3517 := hb (x 18 13)
                        have b3518 := hb (x 17 1 && x 17 14)
                        clear * - r3515 b3516 b3517 b3518 d3510 d3157
                        omega
                      have d3519 : (x 19 12).toNat = 0 := by
                        have r3520 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3521 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
                        have e3522 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
                        have b3523 := hb (x 16 3)
                        have b3524 := hb (x 17 2)
                        have b3525 := hb (x 18 13)
                        have b3526 := hb (x 19 12)
                        clear * - r3520 e3521 e3522 b3523 b3524 b3525 b3526 d3514
                        omega
                      have d3527 : (x 19 3 && x 19 12).toNat = 0 := by
                        have r3528 := hand2 (x 19 3) (x 19 12)
                        have b3529 := hb (x 19 12)
                        have b3530 := hb (x 19 3 && x 19 12)
                        clear * - r3528 b3529 b3530 d3519
                        omega
                      have d3531 : (x 19 4).toNat = 0 := by
                        have r3532 : (x 19 4).toNat ≤ (x 19 12).toNat := himp _ _ (hp4 19)
                        have b3533 := hb (x 19 4)
                        have b3534 := hb (x 19 12)
                        clear * - r3532 b3533 b3534 d3519
                        omega
                      have d3535 : (x 19 4 && x 19 5).toNat = 0 := by
                        have r3536 := hand1 (x 19 4) (x 19 5)
                        have b3537 := hb (x 19 4)
                        have b3538 := hb (x 19 4 && x 19 5)
                        clear * - r3536 b3537 b3538 d3531
                        omega
                      have d3539 : (x 17 6).toNat = 0 := by
                        have r3540 : (x 17 6).toNat ≤ (x 17 14).toNat := himp _ _ (hp6 17)
                        have b3541 := hb (x 17 6)
                        have b3542 := hb (x 17 14)
                        clear * - r3540 b3541 b3542 d3506
                        omega
                      have d3543 : (x 17 6 && x 17 7).toNat = 0 := by
                        have r3544 := hand1 (x 17 6) (x 17 7)
                        have b3545 := hb (x 17 6)
                        have b3546 := hb (x 17 6 && x 17 7)
                        clear * - r3544 b3545 b3546 d3539
                        omega
                      have d3547 : (x 12 3 && x 12 12).toNat = 0 := by
                        have r3548 := hand1 (x 12 3) (x 12 12)
                        have b3549 := hb (x 12 3)
                        have b3550 := hb (x 12 3 && x 12 12)
                        clear * - r3548 b3549 b3550 d3366
                        omega
                      have d3551 : (x 15 9).toNat = 1 := by
                        have r3552 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3553 := hb (x 9 6)
                        have b3554 := hb (x 15 9)
                        have b3555 := hb (x 14 1 && x 14 10)
                        have b3556 := hb (x 13 2 && x 13 11)
                        have b3557 := hb (x 12 3 && x 12 12)
                        have b3558 := hb (x 11 4 && x 11 13)
                        have b3559 := hb (x 10 5 && x 10 14)
                        clear * - r3552 b3553 b3554 b3555 b3556 b3557 b3558 b3559 d3108 d3132 d3547 d2505 d2525 d2529
                        omega
                      have d3560 : (x 16 8).toNat = 0 := by
                        have r3561 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3562 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                        have e3563 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                        have e3564 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                        have e3565 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                        have e3566 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                        have e3567 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                        have b3568 := hb (x 9 7)
                        have b3569 := hb (x 10 6)
                        have b3570 := hb (x 11 5)
                        have b3571 := hb (x 12 4)
                        have b3572 := hb (x 13 11)
                        have b3573 := hb (x 14 10)
                        have b3574 := hb (x 15 9)
                        have b3575 := hb (x 16 8)
                        clear * - r3561 e3562 e3563 e3564 e3565 e3566 e3567 b3568 b3569 b3570 b3571 b3572 b3573 b3574 b3575 d3551 d3185 d3209 d3217 d3237 d3334 d3350
                        omega
                      have d3576 : (x 16 7 && x 16 8).toNat = 0 := by
                        have r3577 := hand2 (x 16 7) (x 16 8)
                        have b3578 := hb (x 16 8)
                        have b3579 := hb (x 16 7 && x 16 8)
                        clear * - r3577 b3578 b3579 d3560
                        omega
                      have d3580 : (x 12 1).toNat = 0 := by
                        have r3581 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3582 := hb (x (-1) 14)
                        have b3583 := hb (x 0 13)
                        have b3584 := hb (x 1 12)
                        have b3585 := hb (x 2 11)
                        have b3586 := hb (x 3 10)
                        have b3587 := hb (x 4 9)
                        have b3588 := hb (x 5 8)
                        have b3589 := hb (x 6 7)
                        have b3590 := hb (x 7 6)
                        have b3591 := hb (x 8 5)
                        have b3592 := hb (x 9 4)
                        have b3593 := hb (x 10 3)
                        have b3594 := hb (x 11 2)
                        have b3595 := hb (x 12 1)
                        clear * - r3581 b3582 b3583 b3584 b3585 b3586 b3587 b3588 b3589 b3590 b3591 b3592 b3593 b3594 b3595 d2876 d2948 d3020 d3036 g65 g61 g55 g48 g45 g37 g27
                        omega
                      have d3596 : (x 12 1 && x 12 14).toNat = 0 := by
                        have r3597 := hand1 (x 12 1) (x 12 14)
                        have b3598 := hb (x 12 1)
                        have b3599 := hb (x 12 1 && x 12 14)
                        clear * - r3597 b3598 b3599 d3580
                        omega
                      have d3600 : (x 12 1 && x 12 12).toNat = 0 := by
                        have r3601 := hand1 (x 12 1) (x 12 12)
                        have b3602 := hb (x 12 1)
                        have b3603 := hb (x 12 1 && x 12 12)
                        clear * - r3601 b3602 b3603 d3580
                        omega
                      have d3604 : (x 11 2).toNat = 0 := by
                        have r3605 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3606 := hb (x (-1) 14)
                        have b3607 := hb (x 0 13)
                        have b3608 := hb (x 1 12)
                        have b3609 := hb (x 2 11)
                        have b3610 := hb (x 3 10)
                        have b3611 := hb (x 4 9)
                        have b3612 := hb (x 5 8)
                        have b3613 := hb (x 6 7)
                        have b3614 := hb (x 7 6)
                        have b3615 := hb (x 8 5)
                        have b3616 := hb (x 9 4)
                        have b3617 := hb (x 10 3)
                        have b3618 := hb (x 11 2)
                        have b3619 := hb (x 12 1)
                        clear * - r3605 b3606 b3607 b3608 b3609 b3610 b3611 b3612 b3613 b3614 b3615 b3616 b3617 b3618 b3619 d3580 d2876 d2948 d3020 d3036 g65 g61 g55 g48 g45 g37 g27
                        omega
                      have d3620 : (x 11 2 && x 11 13).toNat = 0 := by
                        have r3621 := hand1 (x 11 2) (x 11 13)
                        have b3622 := hb (x 11 2)
                        have b3623 := hb (x 11 2 && x 11 13)
                        clear * - r3621 b3622 b3623 d3604
                        omega
                      have d3624 : (x 10 3 && x 10 14).toNat = 1 := by
                        have r3625 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3626 := hb (x 9 4)
                        have b3627 := hb (x 13 11)
                        have b3628 := hb (x 12 1 && x 12 12)
                        have b3629 := hb (x 11 2 && x 11 13)
                        have b3630 := hb (x 10 3 && x 10 14)
                        clear * - r3625 b3626 b3627 b3628 b3629 b3630 d3209 d3600 d3620 d2876
                        omega
                      have d3631 : (x 10 14).toNat = 1 := by
                        have r3632 := hand2 (x 10 3) (x 10 14)
                        have b3633 := hb (x 10 14)
                        have b3634 := hb (x 10 3 && x 10 14)
                        clear * - r3632 b3633 b3634 d3624
                        omega
                      have d3635 : (x 13 13).toNat = 1 := by
                        have r3636 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3637 := hb (x 11 2)
                        have b3638 := hb (x 13 13)
                        have b3639 := hb (x 12 1 && x 12 14)
                        clear * - r3636 b3637 b3638 b3639 d3596 d3604
                        omega
                      have d3640 : (x 13 1).toNat = 1 := by
                        have r3641 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                        have b3642 := hb (x 13 1)
                        have b3643 := hb (x 13 13)
                        clear * - r3641 b3642 b3643 d3635
                        omega
                      have d3644 : (x 12 2).toNat = 0 := by
                        have r3645 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3646 := hb (x 0 14)
                        have b3647 := hb (x 1 13)
                        have b3648 := hb (x 2 12)
                        have b3649 := hb (x 3 11)
                        have b3650 := hb (x 4 10)
                        have b3651 := hb (x 5 9)
                        have b3652 := hb (x 6 8)
                        have b3653 := hb (x 7 7)
                        have b3654 := hb (x 8 6)
                        have b3655 := hb (x 9 5)
                        have b3656 := hb (x 10 4)
                        have b3657 := hb (x 11 3)
                        have b3658 := hb (x 12 2)
                        have b3659 := hb (x 13 1)
                        clear * - r3645 b3646 b3647 b3648 b3649 b3650 b3651 b3652 b3653 b3654 b3655 b3656 b3657 b3658 b3659 d3640 d2666 d2686 d2586 d2702 d2102 d2126 d2150 d2166 d1346 g46 g38
                        omega
                      have d3660 : (x 12 2 && x 12 12).toNat = 0 := by
                        have r3661 := hand1 (x 12 2) (x 12 12)
                        have b3662 := hb (x 12 2)
                        have b3663 := hb (x 12 2 && x 12 12)
                        clear * - r3661 b3662 b3663 d3644
                        omega
                      have d3664 : (x 11 3 && x 11 13).toNat = 1 := by
                        have r3665 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3666 := hb (x 9 5)
                        have b3667 := hb (x 14 10)
                        have b3668 := hb (x 13 1 && x 13 11)
                        have b3669 := hb (x 12 2 && x 12 12)
                        have b3670 := hb (x 11 3 && x 11 13)
                        have b3671 := hb (x 10 4 && x 10 14)
                        clear * - r3665 b3666 b3667 b3668 b3669 b3670 b3671 d3185 d3213 d3660 d2682 d2686
                        omega
                      have d3672 : (x 11 13).toNat = 1 := by
                        have r3673 := hand2 (x 11 3) (x 11 13)
                        have b3674 := hb (x 11 13)
                        have b3675 := hb (x 11 3 && x 11 13)
                        clear * - r3673 b3674 b3675 d3664
                        omega
                      have d3676 : (x 12 12).toNat = 0 := by
                        have r3677 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3678 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                        have e3679 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                        have b3680 := hb (x 9 3)
                        have b3681 := hb (x 10 2)
                        have b3682 := hb (x 11 13)
                        have b3683 := hb (x 12 12)
                        clear * - r3677 e3678 e3679 b3680 b3681 b3682 b3683 d3672
                        omega
                      have d3684 : (x 23 1).toNat = 0 := by
                        have r3685 : (x 23 1).toNat + (x 22 2).toNat + (x 21 3).toNat + (x 20 4).toNat + (x 19 5).toNat + (x 18 6).toNat + (x 17 7).toNat + (x 16 8).toNat + (x 15 9).toNat + (x 14 10).toNat + (x 13 11).toNat + (x 12 12).toNat + (x 11 13).toNat + (x 10 14).toNat = 3 := by have q := hcount 24; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3686 := hb (x 10 14)
                        have b3687 := hb (x 11 13)
                        have b3688 := hb (x 12 12)
                        have b3689 := hb (x 13 11)
                        have b3690 := hb (x 14 10)
                        have b3691 := hb (x 15 9)
                        have b3692 := hb (x 16 8)
                        have b3693 := hb (x 17 7)
                        have b3694 := hb (x 18 6)
                        have b3695 := hb (x 19 5)
                        have b3696 := hb (x 20 4)
                        have b3697 := hb (x 21 3)
                        have b3698 := hb (x 22 2)
                        have b3699 := hb (x 23 1)
                        clear * - r3685 b3686 b3687 b3688 b3689 b3690 b3691 b3692 b3693 b3694 b3695 b3696 b3697 b3698 b3699 d3560 d3551 d3185 d3209 d3676 d3672 d3631
                        omega
                      have d3700 : (x 22 2).toNat = 0 := by
                        have r3701 : (x 23 1).toNat + (x 22 2).toNat + (x 21 3).toNat + (x 20 4).toNat + (x 19 5).toNat + (x 18 6).toNat + (x 17 7).toNat + (x 16 8).toNat + (x 15 9).toNat + (x 14 10).toNat + (x 13 11).toNat + (x 12 12).toNat + (x 11 13).toNat + (x 10 14).toNat = 3 := by have q := hcount 24; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3702 := hb (x 10 14)
                        have b3703 := hb (x 11 13)
                        have b3704 := hb (x 12 12)
                        have b3705 := hb (x 13 11)
                        have b3706 := hb (x 14 10)
                        have b3707 := hb (x 15 9)
                        have b3708 := hb (x 16 8)
                        have b3709 := hb (x 17 7)
                        have b3710 := hb (x 18 6)
                        have b3711 := hb (x 19 5)
                        have b3712 := hb (x 20 4)
                        have b3713 := hb (x 21 3)
                        have b3714 := hb (x 22 2)
                        have b3715 := hb (x 23 1)
                        clear * - r3701 b3702 b3703 b3704 b3705 b3706 b3707 b3708 b3709 b3710 b3711 b3712 b3713 b3714 b3715 d3684 d3560 d3551 d3185 d3209 d3676 d3672 d3631
                        omega
                      have d3716 : (x 22 1 && x 22 2).toNat = 0 := by
                        have r3717 := hand2 (x 22 1) (x 22 2)
                        have b3718 := hb (x 22 2)
                        have b3719 := hb (x 22 1 && x 22 2)
                        clear * - r3717 b3718 b3719 d3700
                        omega
                      have d3720 : (x 21 3).toNat = 0 := by
                        have r3721 : (x 23 1).toNat + (x 22 2).toNat + (x 21 3).toNat + (x 20 4).toNat + (x 19 5).toNat + (x 18 6).toNat + (x 17 7).toNat + (x 16 8).toNat + (x 15 9).toNat + (x 14 10).toNat + (x 13 11).toNat + (x 12 12).toNat + (x 11 13).toNat + (x 10 14).toNat = 3 := by have q := hcount 24; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3722 := hb (x 10 14)
                        have b3723 := hb (x 11 13)
                        have b3724 := hb (x 12 12)
                        have b3725 := hb (x 13 11)
                        have b3726 := hb (x 14 10)
                        have b3727 := hb (x 15 9)
                        have b3728 := hb (x 16 8)
                        have b3729 := hb (x 17 7)
                        have b3730 := hb (x 18 6)
                        have b3731 := hb (x 19 5)
                        have b3732 := hb (x 20 4)
                        have b3733 := hb (x 21 3)
                        have b3734 := hb (x 22 2)
                        have b3735 := hb (x 23 1)
                        clear * - r3721 b3722 b3723 b3724 b3725 b3726 b3727 b3728 b3729 b3730 b3731 b3732 b3733 b3734 b3735 d3684 d3700 d3560 d3551 d3185 d3209 d3676 d3672 d3631
                        omega
                      have d3736 : (x 21 2 && x 21 3).toNat = 0 := by
                        have r3737 := hand2 (x 21 2) (x 21 3)
                        have b3738 := hb (x 21 3)
                        have b3739 := hb (x 21 2 && x 21 3)
                        clear * - r3737 b3738 b3739 d3720
                        omega
                      have d3740 : (x 20 4).toNat = 0 := by
                        have r3741 : (x 23 1).toNat + (x 22 2).toNat + (x 21 3).toNat + (x 20 4).toNat + (x 19 5).toNat + (x 18 6).toNat + (x 17 7).toNat + (x 16 8).toNat + (x 15 9).toNat + (x 14 10).toNat + (x 13 11).toNat + (x 12 12).toNat + (x 11 13).toNat + (x 10 14).toNat = 3 := by have q := hcount 24; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3742 := hb (x 10 14)
                        have b3743 := hb (x 11 13)
                        have b3744 := hb (x 12 12)
                        have b3745 := hb (x 13 11)
                        have b3746 := hb (x 14 10)
                        have b3747 := hb (x 15 9)
                        have b3748 := hb (x 16 8)
                        have b3749 := hb (x 17 7)
                        have b3750 := hb (x 18 6)
                        have b3751 := hb (x 19 5)
                        have b3752 := hb (x 20 4)
                        have b3753 := hb (x 21 3)
                        have b3754 := hb (x 22 2)
                        have b3755 := hb (x 23 1)
                        clear * - r3741 b3742 b3743 b3744 b3745 b3746 b3747 b3748 b3749 b3750 b3751 b3752 b3753 b3754 b3755 d3684 d3700 d3720 d3560 d3551 d3185 d3209 d3676 d3672 d3631
                        omega
                      have d3756 : (x 20 3 && x 20 4).toNat = 0 := by
                        have r3757 := hand2 (x 20 3) (x 20 4)
                        have b3758 := hb (x 20 4)
                        have b3759 := hb (x 20 3 && x 20 4)
                        clear * - r3757 b3758 b3759 d3740
                        omega
                      have d3760 : (x 18 5 && x 18 6).toNat = 1 := by
                        have r3761 : 1 ≤ (x 23 1).toNat + (x 22 1 && x 22 2).toNat + (x 21 2 && x 21 3).toNat + (x 20 3 && x 20 4).toNat + (x 19 4 && x 19 5).toNat + (x 18 5 && x 18 6).toNat + (x 17 6 && x 17 7).toNat + (x 16 7 && x 16 8).toNat + (x 15 8 && x 15 9).toNat + (x 14 9 && x 14 10).toNat + (x 13 10 && x 13 11).toNat + (x 12 11 && x 12 12).toNat + (x 11 12 && x 11 13).toNat + (x 10 13 && x 10 14).toNat + (x 9 14).toNat := by have q := hcov1 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3762 := hb (x 9 14)
                        have b3763 := hb (x 23 1)
                        have b3764 := hb (x 22 1 && x 22 2)
                        have b3765 := hb (x 21 2 && x 21 3)
                        have b3766 := hb (x 20 3 && x 20 4)
                        have b3767 := hb (x 19 4 && x 19 5)
                        have b3768 := hb (x 18 5 && x 18 6)
                        have b3769 := hb (x 17 6 && x 17 7)
                        have b3770 := hb (x 16 7 && x 16 8)
                        have b3771 := hb (x 15 8 && x 15 9)
                        have b3772 := hb (x 14 9 && x 14 10)
                        have b3773 := hb (x 13 10 && x 13 11)
                        have b3774 := hb (x 12 11 && x 12 12)
                        have b3775 := hb (x 11 12 && x 11 13)
                        have b3776 := hb (x 10 13 && x 10 14)
                        clear * - r3761 b3762 b3763 b3764 b3765 b3766 b3767 b3768 b3769 b3770 b3771 b3772 b3773 b3774 b3775 b3776 d3684 d3716 d3736 d3756 d3535 d3543 d3576 d2417 d2437 d2457 d2481 d2932 d3052 d2795
                        omega
                      have d3777 : (x 18 5).toNat = 1 := by
                        have r3778 := hand1 (x 18 5) (x 18 6)
                        have b3779 := hb (x 18 5)
                        have b3780 := hb (x 18 5 && x 18 6)
                        clear * - r3778 b3779 b3780 d3760
                        omega
                      have d3781 : (x 23 8).toNat = 0 := by
                        have r3782 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3783 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
                        have e3784 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
                        have e3785 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
                        have e3786 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
                        have e3787 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
                        have e3788 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
                        have b3789 := hb (x 16 7)
                        have b3790 := hb (x 17 6)
                        have b3791 := hb (x 18 5)
                        have b3792 := hb (x 19 4)
                        have b3793 := hb (x 20 11)
                        have b3794 := hb (x 21 10)
                        have b3795 := hb (x 22 9)
                        have b3796 := hb (x 23 8)
                        clear * - r3782 e3783 e3784 e3785 e3786 e3787 e3788 b3789 b3790 b3791 b3792 b3793 b3794 b3795 b3796 d3531 d3777 d3539
                        omega
                      have d3797 : (x 22 9).toNat = 0 := by
                        have r3798 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3799 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
                        have e3800 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
                        have e3801 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
                        have e3802 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
                        have e3803 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
                        have e3804 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
                        have b3805 := hb (x 16 7)
                        have b3806 := hb (x 17 6)
                        have b3807 := hb (x 18 5)
                        have b3808 := hb (x 19 4)
                        have b3809 := hb (x 20 11)
                        have b3810 := hb (x 21 10)
                        have b3811 := hb (x 22 9)
                        have b3812 := hb (x 23 8)
                        clear * - r3798 e3799 e3800 e3801 e3802 e3803 e3804 b3805 b3806 b3807 b3808 b3809 b3810 b3811 b3812 d3781 d3531 d3777 d3539
                        omega
                      have d3813 : (x 21 10).toNat = 0 := by
                        have r3814 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3815 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
                        have e3816 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
                        have e3817 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
                        have e3818 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
                        have e3819 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
                        have e3820 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
                        have b3821 := hb (x 16 7)
                        have b3822 := hb (x 17 6)
                        have b3823 := hb (x 18 5)
                        have b3824 := hb (x 19 4)
                        have b3825 := hb (x 20 11)
                        have b3826 := hb (x 21 10)
                        have b3827 := hb (x 22 9)
                        have b3828 := hb (x 23 8)
                        clear * - r3814 e3815 e3816 e3817 e3818 e3819 e3820 b3821 b3822 b3823 b3824 b3825 b3826 b3827 b3828 d3781 d3797 d3531 d3777 d3539
                        omega
                      have d3829 : (x 21 1 && x 21 10).toNat = 0 := by
                        have r3830 := hand2 (x 21 1) (x 21 10)
                        have b3831 := hb (x 21 10)
                        have b3832 := hb (x 21 1 && x 21 10)
                        clear * - r3830 b3831 b3832 d3813
                        omega
                      have d3833 : (x 20 2 && x 20 11).toNat = 1 := by
                        have r3834 : 1 ≤ (x 22 9).toNat + (x 21 1 && x 21 10).toNat + (x 20 2 && x 20 11).toNat + (x 19 3 && x 19 12).toNat + (x 18 4 && x 18 13).toNat + (x 17 5 && x 17 14).toNat + (x 16 6).toNat := by have q := hcov9 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b3835 := hb (x 16 6)
                        have b3836 := hb (x 22 9)
                        have b3837 := hb (x 21 1 && x 21 10)
                        have b3838 := hb (x 20 2 && x 20 11)
                        have b3839 := hb (x 19 3 && x 19 12)
                        have b3840 := hb (x 18 4 && x 18 13)
                        have b3841 := hb (x 17 5 && x 17 14)
                        clear * - r3834 b3835 b3836 b3837 b3838 b3839 b3840 b3841 d3797 d3829 d3527 d3281 d3297 d3153
                        omega
                      have d3842 : (x 20 11).toNat = 1 := by
                        have r3843 := hand2 (x 20 2) (x 20 11)
                        have b3844 := hb (x 20 11)
                        have b3845 := hb (x 20 2 && x 20 11)
                        clear * - r3843 b3844 b3845 d3833
                        omega
                      have r3846 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3847 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
                      have e3848 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
                      have e3849 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
                      have e3850 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
                      have e3851 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
                      have e3852 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
                      have b3853 := hb (x 16 7)
                      have b3854 := hb (x 17 6)
                      have b3855 := hb (x 18 5)
                      have b3856 := hb (x 19 4)
                      have b3857 := hb (x 20 11)
                      have b3858 := hb (x 21 10)
                      have b3859 := hb (x 22 9)
                      have b3860 := hb (x 23 8)
                      linarith only [r3846, e3847, e3848, e3849, e3850, e3851, e3852, b3853, b3854, b3855, b3856, b3857, b3858, b3859, b3860, d3781, d3797, d3813, d3842, d3531, d3777, d3539]
                    · have f3861 : (x 2 6).toNat = 1 := by rw [h2380]; rfl
                      have d3862 : (x 8 8).toNat = 0 := by
                        have r3863 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3864 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e3865 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e3866 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e3867 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e3868 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e3869 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b3870 := hb (x 1 7)
                        have b3871 := hb (x 2 6)
                        have b3872 := hb (x 3 5)
                        have b3873 := hb (x 4 4)
                        have b3874 := hb (x 5 11)
                        have b3875 := hb (x 6 10)
                        have b3876 := hb (x 7 9)
                        have b3877 := hb (x 8 8)
                        clear * - r3863 e3864 e3865 e3866 e3867 e3868 e3869 b3870 b3871 b3872 b3873 b3874 b3875 b3876 b3877 g59 g53 f3861 f1367
                        omega
                      have d3878 : (x 8 2 && x 8 8).toNat = 0 := by
                        have r3879 := hand2 (x 8 2) (x 8 8)
                        have b3880 := hb (x 8 8)
                        have b3881 := hb (x 8 2 && x 8 8)
                        clear * - r3879 b3880 b3881 d3862
                        omega
                      have d3882 : (x 8 4 && x 8 8).toNat = 0 := by
                        have r3883 := hand2 (x 8 4) (x 8 8)
                        have b3884 := hb (x 8 8)
                        have b3885 := hb (x 8 4 && x 8 8)
                        clear * - r3883 b3884 b3885 d3862
                        omega
                      have d3886 : (x 7 9).toNat = 0 := by
                        have r3887 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3888 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e3889 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e3890 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e3891 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e3892 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e3893 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b3894 := hb (x 1 7)
                        have b3895 := hb (x 2 6)
                        have b3896 := hb (x 3 5)
                        have b3897 := hb (x 4 4)
                        have b3898 := hb (x 5 11)
                        have b3899 := hb (x 6 10)
                        have b3900 := hb (x 7 9)
                        have b3901 := hb (x 8 8)
                        clear * - r3887 e3888 e3889 e3890 e3891 e3892 e3893 b3894 b3895 b3896 b3897 b3898 b3899 b3900 b3901 d3862 g59 g53 f3861 f1367
                        omega
                      have d3902 : (x 7 3 && x 7 9).toNat = 0 := by
                        have r3903 := hand2 (x 7 3) (x 7 9)
                        have b3904 := hb (x 7 9)
                        have b3905 := hb (x 7 3 && x 7 9)
                        clear * - r3903 b3904 b3905 d3886
                        omega
                      have d3906 : (x 7 5 && x 7 9).toNat = 0 := by
                        have r3907 := hand2 (x 7 5) (x 7 9)
                        have b3908 := hb (x 7 9)
                        have b3909 := hb (x 7 5 && x 7 9)
                        clear * - r3907 b3908 b3909 d3886
                        omega
                      have d3910 : (x 6 10).toNat = 0 := by
                        have r3911 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3912 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e3913 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e3914 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e3915 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e3916 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e3917 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b3918 := hb (x 1 7)
                        have b3919 := hb (x 2 6)
                        have b3920 := hb (x 3 5)
                        have b3921 := hb (x 4 4)
                        have b3922 := hb (x 5 11)
                        have b3923 := hb (x 6 10)
                        have b3924 := hb (x 7 9)
                        have b3925 := hb (x 8 8)
                        clear * - r3911 e3912 e3913 e3914 e3915 e3916 e3917 b3918 b3919 b3920 b3921 b3922 b3923 b3924 b3925 d3862 d3886 g59 g53 f3861 f1367
                        omega
                      have d3926 : (x 6 4 && x 6 10).toNat = 0 := by
                        have r3927 := hand2 (x 6 4) (x 6 10)
                        have b3928 := hb (x 6 10)
                        have b3929 := hb (x 6 4 && x 6 10)
                        clear * - r3927 b3928 b3929 d3910
                        omega
                      have d3930 : (x 6 6 && x 6 10).toNat = 0 := by
                        have r3931 := hand2 (x 6 6) (x 6 10)
                        have b3932 := hb (x 6 10)
                        have b3933 := hb (x 6 6 && x 6 10)
                        clear * - r3931 b3932 b3933 d3910
                        omega
                      have d3934 : (x 5 11).toNat = 0 := by
                        have r3935 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e3936 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e3937 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e3938 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e3939 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e3940 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e3941 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b3942 := hb (x 1 7)
                        have b3943 := hb (x 2 6)
                        have b3944 := hb (x 3 5)
                        have b3945 := hb (x 4 4)
                        have b3946 := hb (x 5 11)
                        have b3947 := hb (x 6 10)
                        have b3948 := hb (x 7 9)
                        have b3949 := hb (x 8 8)
                        clear * - r3935 e3936 e3937 e3938 e3939 e3940 e3941 b3942 b3943 b3944 b3945 b3946 b3947 b3948 b3949 d3862 d3886 d3910 g59 g53 f3861 f1367
                        omega
                      have d3950 : (x 5 5 && x 5 11).toNat = 0 := by
                        have r3951 := hand2 (x 5 5) (x 5 11)
                        have b3952 := hb (x 5 11)
                        have b3953 := hb (x 5 5 && x 5 11)
                        clear * - r3951 b3952 b3953 d3934
                        omega
                      have d3954 : (x 5 7 && x 5 11).toNat = 0 := by
                        have r3955 := hand2 (x 5 7) (x 5 11)
                        have b3956 := hb (x 5 11)
                        have b3957 := hb (x 5 7 && x 5 11)
                        clear * - r3955 b3956 b3957 d3934
                        omega
                      have r3958 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3959 : (x 9 1).toNat + (x 8 2).toNat + (x 7 3).toNat + (x 6 4).toNat + (x 5 5).toNat + (x 4 6).toNat + (x 3 7).toNat + (x 2 8).toNat + (x 1 9).toNat + (x 0 10).toNat + (x (-1) 11).toNat + (x (-2) 12).toNat + (x (-3) 13).toNat + (x (-4) 14).toNat = 3 := by have q := hcount 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3960 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r3961 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3962 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                      have e3963 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                      have e3964 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                      have e3965 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                      have e3966 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                      have e3967 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                      have r3968 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3969 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
                      have e3970 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
                      have e3971 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
                      have e3972 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
                      have e3973 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
                      have e3974 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
                      have r3975 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3976 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                      have e3977 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                      have e3978 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                      have e3979 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                      have e3980 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                      have e3981 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                      have r3982 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3983 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
                      have e3984 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
                      have e3985 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
                      have e3986 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
                      have e3987 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
                      have e3988 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
                      have r3989 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3990 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
                      have e3991 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
                      have e3992 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
                      have e3993 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
                      have e3994 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
                      have e3995 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
                      have r3996 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e3997 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                      have e3998 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                      have r3999 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e4000 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                      have e4001 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                      have r4002 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e4003 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                      have e4004 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                      have r4005 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4006 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4007 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := by have q := hcov4 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e4008 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
                      have e4009 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
                      have r4010 : 1 ≤ (x 14 4).toNat + (x 13 1 && x 13 5).toNat + (x 12 2 && x 12 6).toNat + (x 11 3 && x 11 7).toNat + (x 10 4 && x 10 8).toNat + (x 9 5 && x 9 9).toNat + (x 8 6 && x 8 10).toNat + (x 7 7 && x 7 11).toNat + (x 6 8 && x 6 12).toNat + (x 5 9 && x 5 13).toNat + (x 4 10 && x 4 14).toNat + (x 3 11).toNat := by have q := hcov4 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e4011 : (x 13 1 && x 13 5).toNat = (x 13 5).toNat := handr _ _ (fun h => hp13 13 (hp5 13 (h)))
                      have e4012 : (x 4 10 && x 4 14).toNat = (x 4 10).toNat := handl _ _ (fun h => hp2 4 (hp10 4 (h)))
                      have r4013 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4014 : 1 ≤ (x 12 5).toNat + (x 11 1 && x 11 6).toNat + (x 10 2 && x 10 7).toNat + (x 9 3 && x 9 8).toNat + (x 8 4 && x 8 9).toNat + (x 7 5 && x 7 10).toNat + (x 6 6 && x 6 11).toNat + (x 5 7 && x 5 12).toNat + (x 4 8 && x 4 13).toNat + (x 3 9 && x 3 14).toNat + (x 2 10).toNat := by have q := hcov5 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4015 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4016 : 1 ≤ (x 10 7).toNat + (x 9 1 && x 9 8).toNat + (x 8 2 && x 8 9).toNat + (x 7 3 && x 7 10).toNat + (x 6 4 && x 6 11).toNat + (x 5 5 && x 5 12).toNat + (x 4 6 && x 4 13).toNat + (x 3 7 && x 3 14).toNat + (x 2 8).toNat := by have q := hcov7 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4017 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4018 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4019 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4020 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r4021 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
                      have r4022 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                      have r4023 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
                      have r4024 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
                      have r4025 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                      have r4026 := hand1 (x 10 2) (x 10 6)
                      have r4027 := hand1 (x 9 3) (x 9 7)
                      have r4028 := hand2 (x 12 2) (x 12 6)
                      have r4029 := hand2 (x 11 3) (x 11 7)
                      have r4030 := hand2 (x 10 4) (x 10 8)
                      have r4031 := hand2 (x 9 5) (x 9 9)
                      have r4032 := hand2 (x 8 6) (x 8 10)
                      have r4033 := hand2 (x 7 7) (x 7 11)
                      have r4034 := hand2 (x 9 1) (x 9 6)
                      have r4035 := hand2 (x 8 2) (x 8 7)
                      have r4036 := hand2 (x 11 1) (x 11 6)
                      have r4037 := hand1 (x 10 2) (x 10 7)
                      have r4038 := hand2 (x 9 3) (x 9 8)
                      have r4039 := hand2 (x 8 4) (x 8 9)
                      have r4040 := hand2 (x 7 5) (x 7 10)
                      have r4041 := hand2 (x 6 6) (x 6 11)
                      have r4042 := hand2 (x 9 1) (x 9 7)
                      have r4043 := hand2 (x 9 1) (x 9 8)
                      have r4044 := hand2 (x 8 2) (x 8 9)
                      have r4045 := hand2 (x 7 3) (x 7 10)
                      have r4046 := hand2 (x 6 4) (x 6 11)
                      have r4047 := hand2 (x 13 1) (x 13 11)
                      have r4048 := hand2 (x 12 2) (x 12 12)
                      have r4049 := hand2 (x 11 3) (x 11 13)
                      have r4050 := hand1 (x 10 4) (x 10 14)
                      have r4051 := hand2 (x 12 1) (x 12 12)
                      have r4052 := hand2 (x 11 2) (x 11 13)
                      have r4053 := hand2 (x 10 3) (x 10 14)
                      have r4054 := hand1 (x 14 1) (x 14 12)
                      have r4055 := hand1 (x 13 2) (x 13 13)
                      have r4056 := hand1 (x 12 3) (x 12 14)
                      have r4057 := hand2 (x 10 1) (x 10 14)
                      have b4058 := hb (x (-5) 14)
                      have b4060 := hb (x (-4) 14)
                      linarith only [r3958, r3959, r3960, r3961, e3962, e3963, e3964, e3965, e3966, e3967, r3968, e3969, e3970, e3971, e3972, e3973, e3974, r3975, e3976, e3977, e3978, e3979, e3980, e3981, r3982, e3983, e3984, e3985, e3986, e3987, e3988, r3989, e3990, e3991, e3992, e3993, e3994, e3995, r3996, e3997, e3998, r3999, e4000, e4001, r4002, e4003, e4004, r4005, r4006, r4007, e4008, e4009, r4010, e4011, e4012, r4013, r4014, r4015, r4016, r4017, r4018, r4019, r4020, r4021, r4022, r4023, r4024, r4025, r4026, r4027, r4028, r4029, r4030, r4031, r4032, r4033, r4034, r4035, r4036, r4037, r4038, r4039, r4040, r4041, r4042, r4043, r4044, r4045, r4046, r4047, r4048, r4049, r4050, r4051, r4052, r4053, r4054, r4055, r4056, r4057, b4058, b4060, g9, g12, g13, g20, g21, g26, d1342, g35, g36, g42, g43, g44, g47, d2356, f2347, g49, g54, d2166, g56, g60, d2150, d2324, g64, d2300, d2276, d2252, d3882, d3906, d3930, d3954, g90, g91, d2122, d2146, d2272, d2296, d2320, d2340, g112, d2376, g113, g114, g115, g116, d3878, d3902, d3926, d3950, g133, g134, d2372, g140, g141, g142]
                  · have f4210 : (x 2 10).toNat = 1 := by rw [h2346]; rfl
                    have d4211 : (x 4 8).toNat = 0 := by
                      have r4212 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e4213 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e4214 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e4215 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e4216 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e4217 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e4218 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have b4219 := hb (x (-3) 7)
                      have b4220 := hb (x (-2) 6)
                      have b4221 := hb (x (-1) 5)
                      have b4222 := hb (x 0 4)
                      have b4223 := hb (x 1 11)
                      have b4224 := hb (x 2 10)
                      have b4225 := hb (x 3 9)
                      have b4226 := hb (x 4 8)
                      clear * - r4212 e4213 e4214 e4215 e4216 e4217 e4218 b4219 b4220 b4221 b4222 b4223 b4224 b4225 b4226 f4210 g44 g30 g25 g17
                      omega
                    have d4227 : (x 3 9).toNat = 0 := by
                      have r4228 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e4229 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e4230 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e4231 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e4232 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e4233 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e4234 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have b4235 := hb (x (-3) 7)
                      have b4236 := hb (x (-2) 6)
                      have b4237 := hb (x (-1) 5)
                      have b4238 := hb (x 0 4)
                      have b4239 := hb (x 1 11)
                      have b4240 := hb (x 2 10)
                      have b4241 := hb (x 3 9)
                      have b4242 := hb (x 4 8)
                      clear * - r4228 e4229 e4230 e4231 e4232 e4233 e4234 b4235 b4236 b4237 b4238 b4239 b4240 b4241 b4242 d4211 f4210 g44 g30 g25 g17
                      omega
                    have d4243 : (x (-3) 7).toNat = 0 := by
                      have r4244 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e4245 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e4246 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e4247 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e4248 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e4249 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e4250 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have b4251 := hb (x (-3) 7)
                      have b4252 := hb (x (-2) 6)
                      have b4253 := hb (x (-1) 5)
                      have b4254 := hb (x 0 4)
                      have b4255 := hb (x 1 11)
                      have b4256 := hb (x 2 10)
                      have b4257 := hb (x 3 9)
                      have b4258 := hb (x 4 8)
                      clear * - r4244 e4245 e4246 e4247 e4248 e4249 e4250 b4251 b4252 b4253 b4254 b4255 b4256 b4257 b4258 d4211 d4227 f4210 g44 g30 g25 g17
                      omega
                    have d4259 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
                      have r4260 := hand2 (x (-3) 3) (x (-3) 7)
                      have b4261 := hb (x (-3) 7)
                      have b4262 := hb (x (-3) 3 && x (-3) 7)
                      clear * - r4260 b4261 b4262 d4243
                      omega
                    have d4263 : (x (-3) 4 && x (-3) 7).toNat = 0 := by
                      have r4264 := hand2 (x (-3) 4) (x (-3) 7)
                      have b4265 := hb (x (-3) 7)
                      have b4266 := hb (x (-3) 4 && x (-3) 7)
                      clear * - r4264 b4265 b4266 d4243
                      omega
                    have r4267 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r4268 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r4269 : 1 ≤ (x 1 3).toNat + (x 0 1 && x 0 4).toNat + (x (-1) 2 && x (-1) 5).toNat + (x (-2) 3 && x (-2) 6).toNat + (x (-3) 4 && x (-3) 7).toNat + (x (-4) 5 && x (-4) 8).toNat + (x (-5) 6 && x (-5) 9).toNat + (x (-6) 7 && x (-6) 10).toNat + (x (-7) 8 && x (-7) 11).toNat + (x (-8) 9 && x (-8) 12).toNat + (x (-9) 10 && x (-9) 13).toNat + (x (-10) 11 && x (-10) 14).toNat + (x (-11) 12).toNat := by have q := hcov3 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r4270 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4271 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
                    have e4272 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
                    have r4273 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r4274 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
                    have r4275 := hand1 (x (-7) 8) (x (-7) 11)
                    have r4276 := hand1 (x (-8) 9) (x (-8) 12)
                    have r4277 := hand1 (x (-9) 10) (x (-9) 13)
                    have r4278 := hand1 (x (-10) 11) (x (-10) 14)
                    have r4279 := hand1 (x (-4) 4) (x (-4) 8)
                    have r4280 := hand1 (x (-5) 5) (x (-5) 9)
                    have r4281 := hand1 (x (-6) 6) (x (-6) 10)
                    have r4282 := hand1 (x (-7) 7) (x (-7) 11)
                    have r4283 := hand1 (x (-8) 8) (x (-8) 12)
                    have r4284 := hand1 (x (-9) 9) (x (-9) 13)
                    have r4285 := hand2 (x (-13) 1) (x (-13) 14)
                    linarith only [r4267, r4268, r4269, r4270, e4271, e4272, r4273, r4274, r4275, r4276, r4277, r4278, r4279, r4280, r4281, r4282, r4283, r4284, r4285, g0, g2, g5, g10, g11, g14, g15, g22, g23, g25, g28, g30, g39, g67, g68, g69, d4263, g70, g71, g72, g73, d4259]
                · have f4338 : (x (-2) 8).toNat = 1 := by rw [h2344]; rfl
                  have d4339 : (x (-3) 9).toNat = 0 := by
                    have r4340 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4341 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e4342 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e4343 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e4344 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e4345 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e4346 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b4347 := hb (x (-9) 7)
                    have b4348 := hb (x (-8) 6)
                    have b4349 := hb (x (-7) 5)
                    have b4350 := hb (x (-6) 4)
                    have b4351 := hb (x (-5) 11)
                    have b4352 := hb (x (-4) 10)
                    have b4353 := hb (x (-3) 9)
                    have b4354 := hb (x (-2) 8)
                    clear * - r4340 e4341 e4342 e4343 e4344 e4345 e4346 b4347 b4348 b4349 b4350 b4351 b4352 b4353 b4354 f4338 g7 g4
                    omega
                  have d4355 : (x (-3) 3 && x (-3) 9).toNat = 0 := by
                    have r4356 := hand2 (x (-3) 3) (x (-3) 9)
                    have b4357 := hb (x (-3) 9)
                    have b4358 := hb (x (-3) 3 && x (-3) 9)
                    clear * - r4356 b4357 b4358 d4339
                    omega
                  have d4359 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
                    have r4360 := hand2 (x (-3) 4) (x (-3) 9)
                    have b4361 := hb (x (-3) 9)
                    have b4362 := hb (x (-3) 4 && x (-3) 9)
                    clear * - r4360 b4361 b4362 d4339
                    omega
                  have d4363 : (x (-6) 4).toNat = 0 := by
                    have r4364 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4365 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e4366 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e4367 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e4368 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e4369 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e4370 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b4371 := hb (x (-9) 7)
                    have b4372 := hb (x (-8) 6)
                    have b4373 := hb (x (-7) 5)
                    have b4374 := hb (x (-6) 4)
                    have b4375 := hb (x (-5) 11)
                    have b4376 := hb (x (-4) 10)
                    have b4377 := hb (x (-3) 9)
                    have b4378 := hb (x (-2) 8)
                    clear * - r4364 e4365 e4366 e4367 e4368 e4369 e4370 b4371 b4372 b4373 b4374 b4375 b4376 b4377 b4378 f4338 d4339 g7 g4
                    omega
                  have d4379 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
                    have r4380 := hand1 (x (-6) 4) (x (-6) 14)
                    have b4381 := hb (x (-6) 4)
                    have b4382 := hb (x (-6) 4 && x (-6) 14)
                    clear * - r4380 b4381 b4382 d4363
                    omega
                  have d4383 : (x (-7) 5).toNat = 0 := by
                    have r4384 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4385 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e4386 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e4387 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e4388 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e4389 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e4390 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have b4391 := hb (x (-9) 7)
                    have b4392 := hb (x (-8) 6)
                    have b4393 := hb (x (-7) 5)
                    have b4394 := hb (x (-6) 4)
                    have b4395 := hb (x (-5) 11)
                    have b4396 := hb (x (-4) 10)
                    have b4397 := hb (x (-3) 9)
                    have b4398 := hb (x (-2) 8)
                    clear * - r4384 e4385 e4386 e4387 e4388 e4389 e4390 b4391 b4392 b4393 b4394 b4395 b4396 b4397 b4398 f4338 d4339 g7 g4 d4363
                    omega
                  have d4399 : (x (-3) 1 && x (-3) 11).toNat = 1 := by
                    have r4400 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b4401 := hb (x (-7) 5)
                    have b4402 := hb (x (-2) 10)
                    have b4403 := hb (x (-3) 1 && x (-3) 11)
                    have b4404 := hb (x (-4) 2 && x (-4) 12)
                    have b4405 := hb (x (-5) 3 && x (-5) 13)
                    have b4406 := hb (x (-6) 4 && x (-6) 14)
                    clear * - r4400 b4401 b4402 b4403 b4404 b4405 b4406 g19 g149 g150 d4379 d4383
                    omega
                  have d4407 : (x (-3) 11).toNat = 1 := by
                    have r4408 := hand2 (x (-3) 1) (x (-3) 11)
                    have b4409 := hb (x (-3) 11)
                    have b4410 := hb (x (-3) 1 && x (-3) 11)
                    clear * - r4408 b4409 b4410 d4399
                    omega
                  have d4411 : (x (-4) 4).toNat = 0 := by
                    have r4412 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4413 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                    have e4414 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                    have e4415 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                    have e4416 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                    have e4417 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                    have e4418 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                    have b4419 := hb (x (-7) 7)
                    have b4420 := hb (x (-6) 6)
                    have b4421 := hb (x (-5) 5)
                    have b4422 := hb (x (-4) 4)
                    have b4423 := hb (x (-3) 11)
                    have b4424 := hb (x (-2) 10)
                    have b4425 := hb (x (-1) 9)
                    have b4426 := hb (x 0 8)
                    clear * - r4412 e4413 e4414 e4415 e4416 e4417 e4418 b4419 b4420 b4421 b4422 b4423 b4424 b4425 b4426 g34 f1379 g19 d4407
                    omega
                  have d4427 : (x (-5) 5).toNat = 0 := by
                    have r4428 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4429 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                    have e4430 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                    have e4431 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                    have e4432 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                    have e4433 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                    have e4434 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                    have b4435 := hb (x (-7) 7)
                    have b4436 := hb (x (-6) 6)
                    have b4437 := hb (x (-5) 5)
                    have b4438 := hb (x (-4) 4)
                    have b4439 := hb (x (-3) 11)
                    have b4440 := hb (x (-2) 10)
                    have b4441 := hb (x (-1) 9)
                    have b4442 := hb (x 0 8)
                    clear * - r4428 e4429 e4430 e4431 e4432 e4433 e4434 b4435 b4436 b4437 b4438 b4439 b4440 b4441 b4442 g34 f1379 g19 d4407 d4411
                    omega
                  have d4443 : (x (-6) 6).toNat = 0 := by
                    have r4444 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4445 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                    have e4446 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                    have e4447 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                    have e4448 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                    have e4449 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                    have e4450 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                    have b4451 := hb (x (-7) 7)
                    have b4452 := hb (x (-6) 6)
                    have b4453 := hb (x (-5) 5)
                    have b4454 := hb (x (-4) 4)
                    have b4455 := hb (x (-3) 11)
                    have b4456 := hb (x (-2) 10)
                    have b4457 := hb (x (-1) 9)
                    have b4458 := hb (x 0 8)
                    clear * - r4444 e4445 e4446 e4447 e4448 e4449 e4450 b4451 b4452 b4453 b4454 b4455 b4456 b4457 b4458 g34 f1379 g19 d4407 d4411 d4427
                    omega
                  have d4459 : (x (-6) 6 && x (-6) 12).toNat = 0 := by
                    have r4460 := hand1 (x (-6) 6) (x (-6) 12)
                    have b4461 := hb (x (-6) 6)
                    have b4462 := hb (x (-6) 6 && x (-6) 12)
                    clear * - r4460 b4461 b4462 d4443
                    omega
                  have d4463 : (x (-7) 7).toNat = 0 := by
                    have r4464 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e4465 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                    have e4466 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                    have e4467 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                    have e4468 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                    have e4469 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                    have e4470 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                    have b4471 := hb (x (-7) 7)
                    have b4472 := hb (x (-6) 6)
                    have b4473 := hb (x (-5) 5)
                    have b4474 := hb (x (-4) 4)
                    have b4475 := hb (x (-3) 11)
                    have b4476 := hb (x (-2) 10)
                    have b4477 := hb (x (-1) 9)
                    have b4478 := hb (x 0 8)
                    clear * - r4464 e4465 e4466 e4467 e4468 e4469 e4470 b4471 b4472 b4473 b4474 b4475 b4476 b4477 b4478 g34 f1379 g19 d4407 d4411 d4427 d4443
                    omega
                  have d4479 : (x (-7) 7 && x (-7) 13).toNat = 0 := by
                    have r4480 := hand1 (x (-7) 7) (x (-7) 13)
                    have b4481 := hb (x (-7) 7)
                    have b4482 := hb (x (-7) 7 && x (-7) 13)
                    clear * - r4480 b4481 b4482 d4463
                    omega
                  have r4483 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r4484 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r4485 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r4486 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r4487 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r4488 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
                  have r4489 := hand1 (x (-7) 8) (x (-7) 13)
                  have r4490 := hand1 (x (-8) 9) (x (-8) 14)
                  have r4491 := hand1 (x (-8) 8) (x (-8) 14)
                  have r4492 := hand2 (x (-13) 1) (x (-13) 14)
                  linarith only [r4483, r4484, r4485, r4486, r4487, r4488, r4489, r4490, r4491, r4492, d4463, d4443, g0, d4427, g2, d4411, g5, g10, g11, g14, g15, g22, g23, g28, g32, g41, g97, d1362, g98, d4359, g99, g100, g101, d1358, g117, d4355, g118, g119, d4459, d4479]
          · have f4542 : (x (-1) 9).toNat = 1 := by rw [h1378]; rfl
            have d4543 : (x (-3) 11).toNat = 0 := by
              have r4544 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4545 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e4546 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e4547 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e4548 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e4549 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e4550 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b4551 := hb (x (-7) 7)
              have b4552 := hb (x (-6) 6)
              have b4553 := hb (x (-5) 5)
              have b4554 := hb (x (-4) 4)
              have b4555 := hb (x (-3) 11)
              have b4556 := hb (x (-2) 10)
              have b4557 := hb (x (-1) 9)
              have b4558 := hb (x 0 8)
              clear * - r4544 e4545 e4546 e4547 e4548 e4549 e4550 b4551 b4552 b4553 b4554 b4555 b4556 b4557 b4558 g34 f4542 g19
              omega
            have d4559 : (x (-7) 4).toNat = 1 := by
              have r4560 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4561 := hb (x (-7) 4)
              have b4562 := hb (x (-3) 11)
              have b4563 := hb (x (-4) 1 && x (-4) 12)
              have b4564 := hb (x (-5) 2 && x (-5) 13)
              have b4565 := hb (x (-6) 3 && x (-6) 14)
              clear * - r4560 b4561 b4562 b4563 b4564 b4565 d4543 g159 g160 g161
              omega
            have d4566 : (x (-7) 12).toNat = 1 := by
              have r4567 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
              have b4568 := hb (x (-7) 4)
              have b4569 := hb (x (-7) 12)
              clear * - r4567 b4568 b4569 d4559
              omega
            have d4570 : (x (-8) 13).toNat = 0 := by
              have r4571 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4572 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e4573 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b4574 := hb (x (-10) 3)
              have b4575 := hb (x (-9) 2)
              have b4576 := hb (x (-8) 13)
              have b4577 := hb (x (-7) 12)
              clear * - r4571 e4572 e4573 b4574 b4575 b4576 b4577 d4566
              omega
            have d4578 : (x (-8) 8 && x (-8) 13).toNat = 0 := by
              have r4579 := hand2 (x (-8) 8) (x (-8) 13)
              have b4580 := hb (x (-8) 13)
              have b4581 := hb (x (-8) 8 && x (-8) 13)
              clear * - r4579 b4580 b4581 d4570
              omega
            have d4582 : (x (-8) 9 && x (-8) 13).toNat = 0 := by
              have r4583 := hand2 (x (-8) 9) (x (-8) 13)
              have b4584 := hb (x (-8) 13)
              have b4585 := hb (x (-8) 9 && x (-8) 13)
              clear * - r4583 b4584 b4585 d4570
              omega
            have d4586 : (x (-8) 5).toNat = 0 := by
              have r4587 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
              have b4588 := hb (x (-8) 5)
              have b4589 := hb (x (-8) 13)
              clear * - r4587 b4588 b4589 d4570
              omega
            have d4590 : (x (-9) 2).toNat = 0 := by
              have r4591 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4592 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e4593 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b4594 := hb (x (-10) 3)
              have b4595 := hb (x (-9) 2)
              have b4596 := hb (x (-8) 13)
              have b4597 := hb (x (-7) 12)
              clear * - r4591 e4592 e4593 b4594 b4595 b4596 b4597 d4566 d4570
              omega
            have d4598 : (x (-9) 10).toNat = 0 := by
              have r4599 : (x (-9) 10).toNat ≤ (x (-9) 2).toNat := himp _ _ (hp10 (-9))
              have b4600 := hb (x (-9) 2)
              have b4601 := hb (x (-9) 10)
              clear * - r4599 b4600 b4601 d4590
              omega
            have d4602 : (x (-9) 1 && x (-9) 10).toNat = 0 := by
              have r4603 := hand2 (x (-9) 1) (x (-9) 10)
              have b4604 := hb (x (-9) 10)
              have b4605 := hb (x (-9) 1 && x (-9) 10)
              clear * - r4603 b4604 b4605 d4598
              omega
            have d4606 : (x (-10) 3).toNat = 0 := by
              have r4607 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4608 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e4609 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b4610 := hb (x (-10) 3)
              have b4611 := hb (x (-9) 2)
              have b4612 := hb (x (-8) 13)
              have b4613 := hb (x (-7) 12)
              clear * - r4607 e4608 e4609 b4610 b4611 b4612 b4613 d4566 d4570 d4590
              omega
            have d4614 : (x (-10) 11).toNat = 0 := by
              have r4615 : (x (-10) 11).toNat ≤ (x (-10) 3).toNat := himp _ _ (hp11 (-10))
              have b4616 := hb (x (-10) 3)
              have b4617 := hb (x (-10) 11)
              clear * - r4615 b4616 b4617 d4606
              omega
            have d4618 : (x (-10) 2 && x (-10) 11).toNat = 0 := by
              have r4619 := hand2 (x (-10) 2) (x (-10) 11)
              have b4620 := hb (x (-10) 11)
              have b4621 := hb (x (-10) 2 && x (-10) 11)
              clear * - r4619 b4620 b4621 d4614
              omega
            have d4622 : (x (-4) 4).toNat = 0 := by
              have r4623 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4624 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e4625 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e4626 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e4627 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e4628 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e4629 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b4630 := hb (x (-7) 7)
              have b4631 := hb (x (-6) 6)
              have b4632 := hb (x (-5) 5)
              have b4633 := hb (x (-4) 4)
              have b4634 := hb (x (-3) 11)
              have b4635 := hb (x (-2) 10)
              have b4636 := hb (x (-1) 9)
              have b4637 := hb (x 0 8)
              clear * - r4623 e4624 e4625 e4626 e4627 e4628 e4629 b4630 b4631 b4632 b4633 b4634 b4635 b4636 b4637 g34 f4542 g19 d4543
              omega
            have d4638 : (x (-5) 5).toNat = 0 := by
              have r4639 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4640 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e4641 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e4642 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e4643 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e4644 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e4645 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b4646 := hb (x (-7) 7)
              have b4647 := hb (x (-6) 6)
              have b4648 := hb (x (-5) 5)
              have b4649 := hb (x (-4) 4)
              have b4650 := hb (x (-3) 11)
              have b4651 := hb (x (-2) 10)
              have b4652 := hb (x (-1) 9)
              have b4653 := hb (x 0 8)
              clear * - r4639 e4640 e4641 e4642 e4643 e4644 e4645 b4646 b4647 b4648 b4649 b4650 b4651 b4652 b4653 g34 f4542 g19 d4543 d4622
              omega
            have d4654 : (x (-6) 6).toNat = 0 := by
              have r4655 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4656 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e4657 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e4658 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e4659 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e4660 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e4661 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b4662 := hb (x (-7) 7)
              have b4663 := hb (x (-6) 6)
              have b4664 := hb (x (-5) 5)
              have b4665 := hb (x (-4) 4)
              have b4666 := hb (x (-3) 11)
              have b4667 := hb (x (-2) 10)
              have b4668 := hb (x (-1) 9)
              have b4669 := hb (x 0 8)
              clear * - r4655 e4656 e4657 e4658 e4659 e4660 e4661 b4662 b4663 b4664 b4665 b4666 b4667 b4668 b4669 g34 f4542 g19 d4543 d4622 d4638
              omega
            have d4670 : (x (-7) 7).toNat = 0 := by
              have r4671 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4672 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e4673 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e4674 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e4675 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e4676 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e4677 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b4678 := hb (x (-7) 7)
              have b4679 := hb (x (-6) 6)
              have b4680 := hb (x (-5) 5)
              have b4681 := hb (x (-4) 4)
              have b4682 := hb (x (-3) 11)
              have b4683 := hb (x (-2) 10)
              have b4684 := hb (x (-1) 9)
              have b4685 := hb (x 0 8)
              clear * - r4671 e4672 e4673 e4674 e4675 e4676 e4677 b4678 b4679 b4680 b4681 b4682 b4683 b4684 b4685 g34 f4542 g19 d4543 d4622 d4638 d4654
              omega
            have d4686 : (x (-7) 7 && x (-7) 12).toNat = 0 := by
              have r4687 := hand1 (x (-7) 7) (x (-7) 12)
              have b4688 := hb (x (-7) 7)
              have b4689 := hb (x (-7) 7 && x (-7) 12)
              clear * - r4687 b4688 b4689 d4670
              omega
            have d4690 : (x (-3) 8).toNat = 0 := by
              have r4691 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4692 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
              have e4693 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
              have e4694 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
              have e4695 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
              have e4696 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
              have e4697 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
              have b4698 := hb (x (-10) 7)
              have b4699 := hb (x (-9) 6)
              have b4700 := hb (x (-8) 5)
              have b4701 := hb (x (-7) 4)
              have b4702 := hb (x (-6) 11)
              have b4703 := hb (x (-5) 10)
              have b4704 := hb (x (-4) 9)
              have b4705 := hb (x (-3) 8)
              clear * - r4691 e4692 e4693 e4694 e4695 e4696 e4697 b4698 b4699 b4700 b4701 b4702 b4703 b4704 b4705 g6 g3 g1 d4559 d4586
              omega
            have d4706 : (x (-3) 3 && x (-3) 8).toNat = 0 := by
              have r4707 := hand2 (x (-3) 3) (x (-3) 8)
              have b4708 := hb (x (-3) 8)
              have b4709 := hb (x (-3) 3 && x (-3) 8)
              clear * - r4707 b4708 b4709 d4690
              omega
            have d4710 : (x (-3) 4 && x (-3) 8).toNat = 0 := by
              have r4711 := hand2 (x (-3) 4) (x (-3) 8)
              have b4712 := hb (x (-3) 8)
              have b4713 := hb (x (-3) 4 && x (-3) 8)
              clear * - r4711 b4712 b4713 d4690
              omega
            have d4714 : (x (-7) 8 && x (-7) 12).toNat = 1 := by
              have r4715 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := by have q := hcov4 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4716 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
              have e4717 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
              have b4718 := hb (x (-10) 11)
              have b4719 := hb (x (-9) 10)
              have b4720 := hb (x 0 5)
              have b4721 := hb (x 1 4)
              have b4722 := hb (x (-1) 2 && x (-1) 6)
              have b4723 := hb (x (-2) 3 && x (-2) 7)
              have b4724 := hb (x (-3) 4 && x (-3) 8)
              have b4725 := hb (x (-4) 5 && x (-4) 9)
              have b4726 := hb (x (-5) 6 && x (-5) 10)
              have b4727 := hb (x (-6) 7 && x (-6) 11)
              have b4728 := hb (x (-7) 8 && x (-7) 12)
              have b4729 := hb (x (-8) 9 && x (-8) 13)
              clear * - r4715 e4716 e4717 b4718 b4719 b4720 b4721 b4722 b4723 b4724 b4725 b4726 b4727 b4728 b4729 g40 g31 g74 g75 d4710 g76 g77 g78 d4582 d4598 d4614
              omega
            have d4730 : (x (-7) 8).toNat = 1 := by
              have r4731 := hand1 (x (-7) 8) (x (-7) 12)
              have b4732 := hb (x (-7) 8)
              have b4733 := hb (x (-7) 8 && x (-7) 12)
              clear * - r4731 b4732 b4733 d4714
              omega
            have d4734 : (x (-8) 9).toNat = 0 := by
              have r4735 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4736 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e4737 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e4738 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e4739 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e4740 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e4741 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have b4742 := hb (x (-14) 7)
              have b4743 := hb (x (-13) 6)
              have b4744 := hb (x (-12) 5)
              have b4745 := hb (x (-11) 4)
              have b4746 := hb (x (-10) 11)
              have b4747 := hb (x (-9) 10)
              have b4748 := hb (x (-8) 9)
              have b4749 := hb (x (-7) 8)
              clear * - r4735 e4736 e4737 e4738 e4739 e4740 e4741 b4742 b4743 b4744 b4745 b4746 b4747 b4748 b4749 d4730 d4598 d4614
              omega
            have d4750 : (x (-11) 12).toNat = 0 := by
              have r4751 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4752 := hb (x (-13) 14)
              have b4753 := hb (x (-12) 13)
              have b4754 := hb (x (-11) 12)
              have b4755 := hb (x (-10) 11)
              have b4756 := hb (x (-9) 10)
              have b4757 := hb (x (-8) 9)
              have b4758 := hb (x (-7) 8)
              have b4759 := hb (x (-6) 7)
              have b4760 := hb (x (-5) 6)
              have b4761 := hb (x (-4) 5)
              have b4762 := hb (x (-3) 4)
              have b4763 := hb (x (-2) 3)
              have b4764 := hb (x (-1) 2)
              have b4765 := hb (x 0 1)
              clear * - r4751 b4752 b4753 b4754 b4755 b4756 b4757 b4758 b4759 b4760 b4761 b4762 b4763 b4764 b4765 g28 g23 g15 g11 g5 g2 g0 d4730 d4734 d4598 d4614
              omega
            have d4766 : (x (-11) 3 && x (-11) 12).toNat = 0 := by
              have r4767 := hand2 (x (-11) 3) (x (-11) 12)
              have b4768 := hb (x (-11) 12)
              have b4769 := hb (x (-11) 3 && x (-11) 12)
              clear * - r4767 b4768 b4769 d4750
              omega
            have d4770 : (x (-12) 13).toNat = 0 := by
              have r4771 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4772 := hb (x (-13) 14)
              have b4773 := hb (x (-12) 13)
              have b4774 := hb (x (-11) 12)
              have b4775 := hb (x (-10) 11)
              have b4776 := hb (x (-9) 10)
              have b4777 := hb (x (-8) 9)
              have b4778 := hb (x (-7) 8)
              have b4779 := hb (x (-6) 7)
              have b4780 := hb (x (-5) 6)
              have b4781 := hb (x (-4) 5)
              have b4782 := hb (x (-3) 4)
              have b4783 := hb (x (-2) 3)
              have b4784 := hb (x (-1) 2)
              have b4785 := hb (x 0 1)
              clear * - r4771 b4772 b4773 b4774 b4775 b4776 b4777 b4778 b4779 b4780 b4781 b4782 b4783 b4784 b4785 g28 g23 g15 g11 g5 g2 g0 d4730 d4734 d4598 d4614 d4750
              omega
            have d4786 : (x (-12) 4 && x (-12) 13).toNat = 0 := by
              have r4787 := hand2 (x (-12) 4) (x (-12) 13)
              have b4788 := hb (x (-12) 13)
              have b4789 := hb (x (-12) 4 && x (-12) 13)
              clear * - r4787 b4788 b4789 d4770
              omega
            have d4790 : (x (-13) 14).toNat = 0 := by
              have r4791 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4792 := hb (x (-13) 14)
              have b4793 := hb (x (-12) 13)
              have b4794 := hb (x (-11) 12)
              have b4795 := hb (x (-10) 11)
              have b4796 := hb (x (-9) 10)
              have b4797 := hb (x (-8) 9)
              have b4798 := hb (x (-7) 8)
              have b4799 := hb (x (-6) 7)
              have b4800 := hb (x (-5) 6)
              have b4801 := hb (x (-4) 5)
              have b4802 := hb (x (-3) 4)
              have b4803 := hb (x (-2) 3)
              have b4804 := hb (x (-1) 2)
              have b4805 := hb (x 0 1)
              clear * - r4791 b4792 b4793 b4794 b4795 b4796 b4797 b4798 b4799 b4800 b4801 b4802 b4803 b4804 b4805 g28 g23 g15 g11 g5 g2 g0 d4730 d4734 d4598 d4614 d4750 d4770
              omega
            have d4806 : (x (-13) 1 && x (-13) 14).toNat = 0 := by
              have r4807 := hand2 (x (-13) 1) (x (-13) 14)
              have b4808 := hb (x (-13) 14)
              have b4809 := hb (x (-13) 1 && x (-13) 14)
              clear * - r4807 b4808 b4809 d4790
              omega
            have d4810 : (x (-14) 2).toNat = 1 := by
              have r4811 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4812 := hb (x (-14) 2)
              have b4813 := hb (x (-12) 13)
              have b4814 := hb (x (-13) 1 && x (-13) 14)
              clear * - r4811 b4812 b4813 b4814 d4770 d4806
              omega
            have d4815 : (x (-12) 12).toNat = 0 := by
              have r4816 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4817 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
              have e4818 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
              have b4819 := hb (x (-15) 3)
              have b4820 := hb (x (-14) 2)
              have b4821 := hb (x (-13) 13)
              have b4822 := hb (x (-12) 12)
              clear * - r4816 e4817 e4818 b4819 b4820 b4821 b4822 d4810
              omega
            have d4823 : (x (-12) 4).toNat = 0 := by
              have r4824 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
              have b4825 := hb (x (-12) 4)
              have b4826 := hb (x (-12) 12)
              clear * - r4824 b4825 b4826 d4815
              omega
            have d4827 : (x (-13) 13).toNat = 0 := by
              have r4828 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4829 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
              have e4830 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
              have b4831 := hb (x (-15) 3)
              have b4832 := hb (x (-14) 2)
              have b4833 := hb (x (-13) 13)
              have b4834 := hb (x (-12) 12)
              clear * - r4828 e4829 e4830 b4831 b4832 b4833 b4834 d4815 d4810
              omega
            have d4835 : (x (-13) 5).toNat = 0 := by
              have r4836 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
              have b4837 := hb (x (-13) 5)
              have b4838 := hb (x (-13) 13)
              clear * - r4836 b4837 b4838 d4827
              omega
            have d4839 : (x (-13) 5 && x (-13) 14).toNat = 0 := by
              have r4840 := hand1 (x (-13) 5) (x (-13) 14)
              have b4841 := hb (x (-13) 5)
              have b4842 := hb (x (-13) 5 && x (-13) 14)
              clear * - r4840 b4841 b4842 d4835
              omega
            have d4843 : (x (-14) 6).toNat = 1 := by
              have r4844 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4845 := hb (x (-14) 6)
              have b4846 := hb (x (-8) 9)
              have b4847 := hb (x (-9) 1 && x (-9) 10)
              have b4848 := hb (x (-10) 2 && x (-10) 11)
              have b4849 := hb (x (-11) 3 && x (-11) 12)
              have b4850 := hb (x (-12) 4 && x (-12) 13)
              have b4851 := hb (x (-13) 5 && x (-13) 14)
              clear * - r4844 b4845 b4846 b4847 b4848 b4849 b4850 b4851 d4734 d4602 d4618 d4766 d4786 d4839
              omega
            have d4852 : (x (-8) 8).toNat = 0 := by
              have r4853 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4854 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
              have e4855 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
              have e4856 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
              have e4857 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
              have e4858 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
              have e4859 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
              have b4860 := hb (x (-15) 7)
              have b4861 := hb (x (-14) 6)
              have b4862 := hb (x (-13) 5)
              have b4863 := hb (x (-12) 4)
              have b4864 := hb (x (-11) 11)
              have b4865 := hb (x (-10) 10)
              have b4866 := hb (x (-9) 9)
              have b4867 := hb (x (-8) 8)
              clear * - r4853 e4854 e4855 e4856 e4857 e4858 e4859 b4860 b4861 b4862 b4863 b4864 b4865 b4866 b4867 d4823 d4835 d4843
              omega
            have d4868 : (x (-9) 9).toNat = 0 := by
              have r4869 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4870 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
              have e4871 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
              have e4872 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
              have e4873 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
              have e4874 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
              have e4875 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
              have b4876 := hb (x (-15) 7)
              have b4877 := hb (x (-14) 6)
              have b4878 := hb (x (-13) 5)
              have b4879 := hb (x (-12) 4)
              have b4880 := hb (x (-11) 11)
              have b4881 := hb (x (-10) 10)
              have b4882 := hb (x (-9) 9)
              have b4883 := hb (x (-8) 8)
              clear * - r4869 e4870 e4871 e4872 e4873 e4874 e4875 b4876 b4877 b4878 b4879 b4880 b4881 b4882 b4883 d4852 d4823 d4835 d4843
              omega
            have d4884 : (x (-9) 9 && x (-9) 14).toNat = 0 := by
              have r4885 := hand1 (x (-9) 9) (x (-9) 14)
              have b4886 := hb (x (-9) 9)
              have b4887 := hb (x (-9) 9 && x (-9) 14)
              clear * - r4885 b4886 b4887 d4868
              omega
            have d4888 : (x (-10) 10).toNat = 1 := by
              have r4889 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := by have q := hcov5 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b4890 := hb (x (-10) 10)
              have b4891 := hb (x 0 5)
              have b4892 := hb (x (-1) 1 && x (-1) 6)
              have b4893 := hb (x (-2) 2 && x (-2) 7)
              have b4894 := hb (x (-3) 3 && x (-3) 8)
              have b4895 := hb (x (-4) 4 && x (-4) 9)
              have b4896 := hb (x (-5) 5 && x (-5) 10)
              have b4897 := hb (x (-6) 6 && x (-6) 11)
              have b4898 := hb (x (-7) 7 && x (-7) 12)
              have b4899 := hb (x (-8) 8 && x (-8) 13)
              have b4900 := hb (x (-9) 9 && x (-9) 14)
              clear * - r4889 b4890 b4891 b4892 b4893 b4894 b4895 b4896 b4897 b4898 b4899 b4900 g31 g92 g93 d4706 g94 g95 g96 d4686 d4578 d4884
              omega
            have d4901 : (x (-10) 2).toNat = 1 := by
              have r4902 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
              have b4903 := hb (x (-10) 2)
              have b4904 := hb (x (-10) 10)
              clear * - r4902 b4903 b4904 d4888
              omega
            have d4905 : (x (-8) 12).toNat = 0 := by
              have r4906 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4907 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e4908 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b4909 := hb (x (-11) 3)
              have b4910 := hb (x (-10) 2)
              have b4911 := hb (x (-9) 13)
              have b4912 := hb (x (-8) 12)
              clear * - r4906 e4907 e4908 b4909 b4910 b4911 b4912 d4901
              omega
            have d4913 : (x (-9) 13).toNat = 0 := by
              have r4914 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4915 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e4916 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b4917 := hb (x (-11) 3)
              have b4918 := hb (x (-10) 2)
              have b4919 := hb (x (-9) 13)
              have b4920 := hb (x (-8) 12)
              clear * - r4914 e4915 e4916 b4917 b4918 b4919 b4920 d4905 d4901
              omega
            have d4921 : (x (-11) 3).toNat = 0 := by
              have r4922 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e4923 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e4924 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b4925 := hb (x (-11) 3)
              have b4926 := hb (x (-10) 2)
              have b4927 := hb (x (-9) 13)
              have b4928 := hb (x (-8) 12)
              clear * - r4922 e4923 e4924 b4925 b4926 b4927 b4928 d4905 d4913 d4901
              omega
            have d4929 : (x (-11) 11).toNat = 0 := by
              have r4930 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
              have b4931 := hb (x (-11) 3)
              have b4932 := hb (x (-11) 11)
              clear * - r4930 b4931 b4932 d4921
              omega
            have r4933 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4934 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
            have e4935 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
            have e4936 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
            have e4937 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
            have e4938 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
            have e4939 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
            have b4940 := hb (x (-15) 7)
            have b4941 := hb (x (-14) 6)
            have b4942 := hb (x (-13) 5)
            have b4943 := hb (x (-12) 4)
            have b4944 := hb (x (-11) 11)
            have b4945 := hb (x (-10) 10)
            have b4946 := hb (x (-9) 9)
            have b4947 := hb (x (-8) 8)
            linarith only [r4933, e4934, e4935, e4936, e4937, e4938, e4939, b4940, b4941, b4942, b4943, b4944, b4945, b4946, b4947, d4852, d4868, d4888, d4929, d4823, d4835, d4843]
        · have f4948 : (x (-1) 8).toNat = 1 := by rw [h1372]; rfl
          have d4949 : (x (-3) 10).toNat = 0 := by
            have r4950 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e4951 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e4952 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e4953 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e4954 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e4955 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e4956 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have b4957 := hb (x (-8) 7)
            have b4958 := hb (x (-7) 6)
            have b4959 := hb (x (-6) 5)
            have b4960 := hb (x (-5) 4)
            have b4961 := hb (x (-4) 11)
            have b4962 := hb (x (-3) 10)
            have b4963 := hb (x (-2) 9)
            have b4964 := hb (x (-1) 8)
            clear * - r4950 e4951 e4952 e4953 e4954 e4955 e4956 b4957 b4958 b4959 b4960 b4961 b4962 b4963 b4964 f4948 g18 g8
            omega
          have r4965 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4966 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4967 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4968 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
          have e4969 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
          have e4970 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
          have e4971 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
          have e4972 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
          have e4973 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
          have r4974 : 1 ≤ (x 1 4).toNat + (x 0 1 && x 0 5).toNat + (x (-1) 2 && x (-1) 6).toNat + (x (-2) 3 && x (-2) 7).toNat + (x (-3) 4 && x (-3) 8).toNat + (x (-4) 5 && x (-4) 9).toNat + (x (-5) 6 && x (-5) 10).toNat + (x (-6) 7 && x (-6) 11).toNat + (x (-7) 8 && x (-7) 12).toNat + (x (-8) 9 && x (-8) 13).toNat + (x (-9) 10 && x (-9) 14).toNat + (x (-10) 11).toNat := by have q := hcov4 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e4975 : (x 0 1 && x 0 5).toNat = (x 0 5).toNat := handr _ _ (fun h => hp13 0 (hp5 0 (h)))
          have e4976 : (x (-9) 10 && x (-9) 14).toNat = (x (-9) 10).toNat := handl _ _ (fun h => hp2 (-9) (hp10 (-9) (h)))
          have r4977 : 1 ≤ (x 0 5).toNat + (x (-1) 1 && x (-1) 6).toNat + (x (-2) 2 && x (-2) 7).toNat + (x (-3) 3 && x (-3) 8).toNat + (x (-4) 4 && x (-4) 9).toNat + (x (-5) 5 && x (-5) 10).toNat + (x (-6) 6 && x (-6) 11).toNat + (x (-7) 7 && x (-7) 12).toNat + (x (-8) 8 && x (-8) 13).toNat + (x (-9) 9 && x (-9) 14).toNat + (x (-10) 10).toNat := by have q := hcov5 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4978 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4979 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r4980 : (x (-14) 2).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp2 (-14))
          have r4981 := hand2 (x (-3) 4) (x (-3) 8)
          have r4982 := hand1 (x (-7) 8) (x (-7) 12)
          have r4983 := hand1 (x (-8) 9) (x (-8) 13)
          have r4984 := hand2 (x (-3) 3) (x (-3) 8)
          have r4985 := hand1 (x (-7) 7) (x (-7) 12)
          have r4986 := hand1 (x (-8) 8) (x (-8) 13)
          have r4987 := hand1 (x (-9) 9) (x (-9) 14)
          have r4988 := hand1 (x (-7) 4) (x (-7) 14)
          have r4989 := hand2 (x (-13) 1) (x (-13) 14)
          linarith only [r4965, r4966, r4967, e4968, e4969, e4970, e4971, e4972, e4973, r4974, e4975, e4976, r4977, r4978, r4979, r4980, r4981, r4982, r4983, r4984, r4985, r4986, r4987, r4988, r4989, g0, g1, g2, g3, g5, g6, g10, g11, d4949, g14, g15, g22, g23, g28, g31, g40, g74, g75, g76, g77, g78, g92, g93, g94, g95, g96, g146, g147, g148]
      · have f5052 : (x 1 7).toNat = 1 := by rw [h1366]; rfl
        have d5053 : (x 8 8).toNat = 0 := by
          have r5054 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5055 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e5056 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e5057 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e5058 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e5059 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e5060 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b5061 := hb (x 1 7)
          have b5062 := hb (x 2 6)
          have b5063 := hb (x 3 5)
          have b5064 := hb (x 4 4)
          have b5065 := hb (x 5 11)
          have b5066 := hb (x 6 10)
          have b5067 := hb (x 7 9)
          have b5068 := hb (x 8 8)
          clear * - r5054 e5055 e5056 e5057 e5058 e5059 e5060 b5061 b5062 b5063 b5064 b5065 b5066 b5067 b5068 g59 g53 f5052
          omega
        have d5069 : (x 8 1 && x 8 8).toNat = 0 := by
          have r5070 := hand2 (x 8 1) (x 8 8)
          have b5071 := hb (x 8 8)
          have b5072 := hb (x 8 1 && x 8 8)
          clear * - r5070 b5071 b5072 d5053
          omega
        have d5073 : (x 7 9).toNat = 0 := by
          have r5074 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5075 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e5076 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e5077 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e5078 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e5079 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e5080 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b5081 := hb (x 1 7)
          have b5082 := hb (x 2 6)
          have b5083 := hb (x 3 5)
          have b5084 := hb (x 4 4)
          have b5085 := hb (x 5 11)
          have b5086 := hb (x 6 10)
          have b5087 := hb (x 7 9)
          have b5088 := hb (x 8 8)
          clear * - r5074 e5075 e5076 e5077 e5078 e5079 e5080 b5081 b5082 b5083 b5084 b5085 b5086 b5087 b5088 d5053 g59 g53 f5052
          omega
        have d5089 : (x 7 2 && x 7 9).toNat = 0 := by
          have r5090 := hand2 (x 7 2) (x 7 9)
          have b5091 := hb (x 7 9)
          have b5092 := hb (x 7 2 && x 7 9)
          clear * - r5090 b5091 b5092 d5073
          omega
        have d5093 : (x 6 10).toNat = 0 := by
          have r5094 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5095 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e5096 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e5097 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e5098 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e5099 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e5100 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b5101 := hb (x 1 7)
          have b5102 := hb (x 2 6)
          have b5103 := hb (x 3 5)
          have b5104 := hb (x 4 4)
          have b5105 := hb (x 5 11)
          have b5106 := hb (x 6 10)
          have b5107 := hb (x 7 9)
          have b5108 := hb (x 8 8)
          clear * - r5094 e5095 e5096 e5097 e5098 e5099 e5100 b5101 b5102 b5103 b5104 b5105 b5106 b5107 b5108 d5053 d5073 g59 g53 f5052
          omega
        have d5109 : (x 6 3 && x 6 10).toNat = 0 := by
          have r5110 := hand2 (x 6 3) (x 6 10)
          have b5111 := hb (x 6 10)
          have b5112 := hb (x 6 3 && x 6 10)
          clear * - r5110 b5111 b5112 d5093
          omega
        have d5113 : (x 5 11).toNat = 0 := by
          have r5114 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5115 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e5116 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e5117 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e5118 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e5119 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e5120 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b5121 := hb (x 1 7)
          have b5122 := hb (x 2 6)
          have b5123 := hb (x 3 5)
          have b5124 := hb (x 4 4)
          have b5125 := hb (x 5 11)
          have b5126 := hb (x 6 10)
          have b5127 := hb (x 7 9)
          have b5128 := hb (x 8 8)
          clear * - r5114 e5115 e5116 e5117 e5118 e5119 e5120 b5121 b5122 b5123 b5124 b5125 b5126 b5127 b5128 d5053 d5073 d5093 g59 g53 f5052
          omega
        have d5129 : (x 2 6).toNat = 0 := by
          have r5130 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e5131 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e5132 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e5133 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e5134 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e5135 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e5136 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have b5137 := hb (x 1 7)
          have b5138 := hb (x 2 6)
          have b5139 := hb (x 3 5)
          have b5140 := hb (x 4 4)
          have b5141 := hb (x 5 11)
          have b5142 := hb (x 6 10)
          have b5143 := hb (x 7 9)
          have b5144 := hb (x 8 8)
          clear * - r5130 e5131 e5132 e5133 e5134 e5135 e5136 b5137 b5138 b5139 b5140 b5141 b5142 b5143 b5144 d5053 d5073 d5093 d5113 g59 g53 f5052
          omega
        have d5145 : (x 2 6 && x 2 11).toNat = 0 := by
          have r5146 := hand1 (x 2 6) (x 2 11)
          have b5147 := hb (x 2 6)
          have b5148 := hb (x 2 6 && x 2 11)
          clear * - r5146 b5147 b5148 d5129
          omega
        have r5149 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r5150 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5151 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
        have e5152 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
        have e5153 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
        have e5154 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
        have e5155 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
        have e5156 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
        have r5157 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5158 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
        have e5159 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
        have e5160 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
        have e5161 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
        have e5162 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
        have e5163 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
        have r5164 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5165 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e5166 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e5167 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e5168 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e5169 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e5170 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have r5171 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5172 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e5173 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e5174 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e5175 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e5176 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e5177 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have r5178 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5179 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
        have e5180 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
        have r5181 : 1 ≤ (x 8 5).toNat + (x 7 1 && x 7 6).toNat + (x 6 2 && x 6 7).toNat + (x 5 3 && x 5 8).toNat + (x 4 4 && x 4 9).toNat + (x 3 5 && x 3 10).toNat + (x 2 6 && x 2 11).toNat + (x 1 7 && x 1 12).toNat + (x 0 8 && x 0 13).toNat + (x (-1) 9 && x (-1) 14).toNat + (x (-2) 10).toNat := by have q := hcov5 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r5182 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r5183 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r5184 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r5185 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r5186 := hand2 (x 2 3) (x 2 7)
        have r5187 := hand1 (x (-3) 8) (x (-3) 12)
        have r5188 := hand2 (x 7 1) (x 7 6)
        have r5189 := hand2 (x 6 2) (x 6 7)
        have r5190 := hand1 (x (-1) 9) (x (-1) 14)
        have r5191 := hand1 (x 2 7) (x 2 14)
        have r5192 := hand2 (x 7 1) (x 7 10)
        have r5193 := hand2 (x 6 2) (x 6 11)
        have r5194 := hand1 (x 12 1) (x 12 12)
        have r5195 := hand1 (x 11 2) (x 11 13)
        have r5196 := hand1 (x 10 3) (x 10 14)
        linarith only [r5149, r5150, e5151, e5152, e5153, e5154, e5155, e5156, r5157, e5158, e5159, e5160, e5161, e5162, e5163, r5164, e5165, e5166, e5167, e5168, e5169, e5170, r5171, e5172, e5173, e5174, e5175, e5176, e5177, r5178, e5179, e5180, r5181, r5182, r5183, r5184, r5185, r5186, r5187, r5188, r5189, r5190, r5191, r5192, r5193, r5194, r5195, r5196, g1, g3, g6, g19, g27, g34, g37, g42, g45, d5129, g48, g54, g55, g60, g61, g64, g65, g79, g80, g81, g82, g83, g84, g102, g103, g104, d5145, g105, g106, d5069, d5089, d5109, g137, g138, g139, g143, g144, g145, g159, g160, g161]
    · have f5280 : (x (-1) 7).toNat = 1 := by rw [h1356]; rfl
      have d5281 : (x 6 8).toNat = 0 := by
        have r5282 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5283 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e5284 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e5285 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e5286 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e5287 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e5288 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b5289 := hb (x (-1) 7)
        have b5290 := hb (x 0 6)
        have b5291 := hb (x 1 5)
        have b5292 := hb (x 2 4)
        have b5293 := hb (x 3 11)
        have b5294 := hb (x 4 10)
        have b5295 := hb (x 5 9)
        have b5296 := hb (x 6 8)
        clear * - r5282 e5283 e5284 e5285 e5286 e5287 e5288 b5289 b5290 b5291 b5292 b5293 b5294 b5295 b5296 g41 g32 f5280
        omega
      have d5297 : (x 6 3 && x 6 8).toNat = 0 := by
        have r5298 := hand2 (x 6 3) (x 6 8)
        have b5299 := hb (x 6 8)
        have b5300 := hb (x 6 3 && x 6 8)
        clear * - r5298 b5299 b5300 d5281
        omega
      have d5301 : (x 6 8 && x 6 12).toNat = 0 := by
        have r5302 := hand1 (x 6 8) (x 6 12)
        have b5303 := hb (x 6 8)
        have b5304 := hb (x 6 8 && x 6 12)
        clear * - r5302 b5303 b5304 d5281
        omega
      have d5305 : (x 5 9).toNat = 0 := by
        have r5306 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5307 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e5308 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e5309 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e5310 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e5311 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e5312 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b5313 := hb (x (-1) 7)
        have b5314 := hb (x 0 6)
        have b5315 := hb (x 1 5)
        have b5316 := hb (x 2 4)
        have b5317 := hb (x 3 11)
        have b5318 := hb (x 4 10)
        have b5319 := hb (x 5 9)
        have b5320 := hb (x 6 8)
        clear * - r5306 e5307 e5308 e5309 e5310 e5311 e5312 b5313 b5314 b5315 b5316 b5317 b5318 b5319 b5320 d5281 g41 g32 f5280
        omega
      have d5321 : (x 5 9 && x 5 13).toNat = 0 := by
        have r5322 := hand1 (x 5 9) (x 5 13)
        have b5323 := hb (x 5 9)
        have b5324 := hb (x 5 9 && x 5 13)
        clear * - r5322 b5323 b5324 d5305
        omega
      have d5325 : (x 4 10).toNat = 0 := by
        have r5326 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5327 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e5328 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e5329 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e5330 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e5331 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e5332 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b5333 := hb (x (-1) 7)
        have b5334 := hb (x 0 6)
        have b5335 := hb (x 1 5)
        have b5336 := hb (x 2 4)
        have b5337 := hb (x 3 11)
        have b5338 := hb (x 4 10)
        have b5339 := hb (x 5 9)
        have b5340 := hb (x 6 8)
        clear * - r5326 e5327 e5328 e5329 e5330 e5331 e5332 b5333 b5334 b5335 b5336 b5337 b5338 b5339 b5340 d5281 d5305 g41 g32 f5280
        omega
      have d5341 : (x 3 11).toNat = 0 := by
        have r5342 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5343 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e5344 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e5345 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e5346 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e5347 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e5348 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b5349 := hb (x (-1) 7)
        have b5350 := hb (x 0 6)
        have b5351 := hb (x 1 5)
        have b5352 := hb (x 2 4)
        have b5353 := hb (x 3 11)
        have b5354 := hb (x 4 10)
        have b5355 := hb (x 5 9)
        have b5356 := hb (x 6 8)
        clear * - r5342 e5343 e5344 e5345 e5346 e5347 e5348 b5349 b5350 b5351 b5352 b5353 b5354 b5355 b5356 d5281 d5305 d5325 g41 g32 f5280
        omega
      have d5357 : (x 2 4).toNat = 0 := by
        have r5358 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5359 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e5360 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e5361 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e5362 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e5363 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e5364 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b5365 := hb (x (-1) 7)
        have b5366 := hb (x 0 6)
        have b5367 := hb (x 1 5)
        have b5368 := hb (x 2 4)
        have b5369 := hb (x 3 11)
        have b5370 := hb (x 4 10)
        have b5371 := hb (x 5 9)
        have b5372 := hb (x 6 8)
        clear * - r5358 e5359 e5360 e5361 e5362 e5363 e5364 b5365 b5366 b5367 b5368 b5369 b5370 b5371 b5372 d5281 d5305 d5325 d5341 g41 g32 f5280
        omega
      have d5373 : (x 6 11).toNat = 1 := by
        have r5374 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5375 := hb (x 2 4)
        have b5376 := hb (x 6 11)
        have b5377 := hb (x 5 1 && x 5 12)
        have b5378 := hb (x 4 2 && x 4 13)
        have b5379 := hb (x 3 3 && x 3 14)
        clear * - r5374 b5375 b5376 b5377 b5378 b5379 g162 g163 g164 d5357
        omega
      have d5380 : (x 6 3).toNat = 1 := by
        have r5381 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
        have b5382 := hb (x 6 3)
        have b5383 := hb (x 6 11)
        clear * - r5381 b5382 b5383 d5373
        omega
      have d5384 : (x 9 12).toNat = 0 := by
        have r5385 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5386 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e5387 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b5388 := hb (x 6 3)
        have b5389 := hb (x 7 2)
        have b5390 := hb (x 8 13)
        have b5391 := hb (x 9 12)
        clear * - r5385 e5386 e5387 b5388 b5389 b5390 b5391 d5380
        omega
      have d5392 : (x 9 3 && x 9 12).toNat = 0 := by
        have r5393 := hand2 (x 9 3) (x 9 12)
        have b5394 := hb (x 9 12)
        have b5395 := hb (x 9 3 && x 9 12)
        clear * - r5393 b5394 b5395 d5384
        omega
      have d5396 : (x 9 5 && x 9 12).toNat = 0 := by
        have r5397 := hand2 (x 9 5) (x 9 12)
        have b5398 := hb (x 9 12)
        have b5399 := hb (x 9 5 && x 9 12)
        clear * - r5397 b5398 b5399 d5384
        omega
      have d5400 : (x 9 4).toNat = 0 := by
        have r5401 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
        have b5402 := hb (x 9 4)
        have b5403 := hb (x 9 12)
        clear * - r5401 b5402 b5403 d5384
        omega
      have d5404 : (x 9 4 && x 9 13).toNat = 0 := by
        have r5405 := hand1 (x 9 4) (x 9 13)
        have b5406 := hb (x 9 4)
        have b5407 := hb (x 9 4 && x 9 13)
        clear * - r5405 b5406 b5407 d5400
        omega
      have d5408 : (x 8 13).toNat = 0 := by
        have r5409 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5410 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e5411 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b5412 := hb (x 6 3)
        have b5413 := hb (x 7 2)
        have b5414 := hb (x 8 13)
        have b5415 := hb (x 9 12)
        clear * - r5409 e5410 e5411 b5412 b5413 b5414 b5415 d5384 d5380
        omega
      have d5416 : (x 8 4 && x 8 13).toNat = 0 := by
        have r5417 := hand2 (x 8 4) (x 8 13)
        have b5418 := hb (x 8 13)
        have b5419 := hb (x 8 4 && x 8 13)
        clear * - r5417 b5418 b5419 d5408
        omega
      have d5420 : (x 8 6 && x 8 13).toNat = 0 := by
        have r5421 := hand2 (x 8 6) (x 8 13)
        have b5422 := hb (x 8 13)
        have b5423 := hb (x 8 6 && x 8 13)
        clear * - r5421 b5422 b5423 d5408
        omega
      have d5424 : (x 8 5).toNat = 0 := by
        have r5425 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
        have b5426 := hb (x 8 5)
        have b5427 := hb (x 8 13)
        clear * - r5425 b5426 b5427 d5408
        omega
      have d5428 : (x 8 5 && x 8 14).toNat = 0 := by
        have r5429 := hand1 (x 8 5) (x 8 14)
        have b5430 := hb (x 8 5)
        have b5431 := hb (x 8 5 && x 8 14)
        clear * - r5429 b5430 b5431 d5424
        omega
      have d5432 : (x 7 2).toNat = 0 := by
        have r5433 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5434 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e5435 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b5436 := hb (x 6 3)
        have b5437 := hb (x 7 2)
        have b5438 := hb (x 8 13)
        have b5439 := hb (x 9 12)
        clear * - r5433 e5434 e5435 b5436 b5437 b5438 b5439 d5384 d5408 d5380
        omega
      have d5440 : (x 7 2 && x 7 8).toNat = 0 := by
        have r5441 := hand1 (x 7 2) (x 7 8)
        have b5442 := hb (x 7 2)
        have b5443 := hb (x 7 2 && x 7 8)
        clear * - r5441 b5442 b5443 d5432
        omega
      have d5444 : (x 7 2 && x 7 7).toNat = 0 := by
        have r5445 := hand1 (x 7 2) (x 7 7)
        have b5446 := hb (x 7 2)
        have b5447 := hb (x 7 2 && x 7 7)
        clear * - r5445 b5446 b5447 d5432
        omega
      have d5448 : (x 7 2 && x 7 6).toNat = 0 := by
        have r5449 := hand1 (x 7 2) (x 7 6)
        have b5450 := hb (x 7 2)
        have b5451 := hb (x 7 2 && x 7 6)
        clear * - r5449 b5450 b5451 d5432
        omega
      have d5452 : (x 7 10).toNat = 0 := by
        have r5453 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
        have b5454 := hb (x 7 2)
        have b5455 := hb (x 7 10)
        clear * - r5453 b5454 b5455 d5432
        omega
      have d5456 : (x 9 8).toNat = 0 := by
        have r5457 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5458 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e5459 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e5460 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e5461 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e5462 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e5463 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b5464 := hb (x 2 7)
        have b5465 := hb (x 3 6)
        have b5466 := hb (x 4 5)
        have b5467 := hb (x 5 4)
        have b5468 := hb (x 6 11)
        have b5469 := hb (x 7 10)
        have b5470 := hb (x 8 9)
        have b5471 := hb (x 9 8)
        clear * - r5457 e5458 e5459 e5460 e5461 e5462 e5463 b5464 b5465 b5466 b5467 b5468 b5469 b5470 b5471 d5452 d5373 g64 g60 g54
        omega
      have d5472 : (x 8 9).toNat = 0 := by
        have r5473 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5474 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e5475 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e5476 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e5477 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e5478 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e5479 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b5480 := hb (x 2 7)
        have b5481 := hb (x 3 6)
        have b5482 := hb (x 4 5)
        have b5483 := hb (x 5 4)
        have b5484 := hb (x 6 11)
        have b5485 := hb (x 7 10)
        have b5486 := hb (x 8 9)
        have b5487 := hb (x 9 8)
        clear * - r5473 e5474 e5475 e5476 e5477 e5478 e5479 b5480 b5481 b5482 b5483 b5484 b5485 b5486 b5487 d5456 d5452 d5373 g64 g60 g54
        omega
      have d5488 : (x 2 7).toNat = 0 := by
        have r5489 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5490 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
        have e5491 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
        have e5492 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
        have e5493 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
        have e5494 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
        have e5495 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
        have b5496 := hb (x 2 7)
        have b5497 := hb (x 3 6)
        have b5498 := hb (x 4 5)
        have b5499 := hb (x 5 4)
        have b5500 := hb (x 6 11)
        have b5501 := hb (x 7 10)
        have b5502 := hb (x 8 9)
        have b5503 := hb (x 9 8)
        clear * - r5489 e5490 e5491 e5492 e5493 e5494 e5495 b5496 b5497 b5498 b5499 b5500 b5501 b5502 b5503 d5456 d5472 d5452 d5373 g64 g60 g54
        omega
      have d5504 : (x 2 7 && x 2 13).toNat = 0 := by
        have r5505 := hand1 (x 2 7) (x 2 13)
        have b5506 := hb (x 2 7)
        have b5507 := hb (x 2 7 && x 2 13)
        clear * - r5505 b5506 b5507 d5488
        omega
      have d5508 : (x 2 7 && x 2 12).toNat = 0 := by
        have r5509 := hand1 (x 2 7) (x 2 12)
        have b5510 := hb (x 2 7)
        have b5511 := hb (x 2 7 && x 2 12)
        clear * - r5509 b5510 b5511 d5488
        omega
      have d5512 : (x 2 7 && x 2 11).toNat = 0 := by
        have r5513 := hand1 (x 2 7) (x 2 11)
        have b5514 := hb (x 2 7)
        have b5515 := hb (x 2 7 && x 2 11)
        clear * - r5513 b5514 b5515 d5488
        omega
      have d5516 : (x 6 3 && x 6 7).toNat = 1 := by
        have r5517 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5518 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
        have e5519 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
        have b5520 := hb (x (-2) 11)
        have b5521 := hb (x (-1) 10)
        have b5522 := hb (x 8 5)
        have b5523 := hb (x 9 4)
        have b5524 := hb (x 7 2 && x 7 6)
        have b5525 := hb (x 6 3 && x 6 7)
        have b5526 := hb (x 5 4 && x 5 8)
        have b5527 := hb (x 4 5 && x 4 9)
        have b5528 := hb (x 3 6 && x 3 10)
        have b5529 := hb (x 2 7 && x 2 11)
        have b5530 := hb (x 1 8 && x 1 12)
        have b5531 := hb (x 0 9 && x 0 13)
        clear * - r5517 e5518 e5519 b5520 b5521 b5522 b5523 b5524 b5525 b5526 b5527 b5528 b5529 b5530 b5531 d5400 d5424 d5448 g85 g86 g87 d5512 g88 g89 g26 g20
        omega
      have d5532 : (x 6 7).toNat = 1 := by
        have r5533 := hand2 (x 6 3) (x 6 7)
        have b5534 := hb (x 6 7)
        have b5535 := hb (x 6 3 && x 6 7)
        clear * - r5533 b5534 b5535 d5516
        omega
      have d5536 : (x 13 8).toNat = 0 := by
        have r5537 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5538 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
        have e5539 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
        have e5540 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
        have e5541 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
        have e5542 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
        have e5543 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
        have b5544 := hb (x 6 7)
        have b5545 := hb (x 7 6)
        have b5546 := hb (x 8 5)
        have b5547 := hb (x 9 4)
        have b5548 := hb (x 10 11)
        have b5549 := hb (x 11 10)
        have b5550 := hb (x 12 9)
        have b5551 := hb (x 13 8)
        clear * - r5537 e5538 e5539 e5540 e5541 e5542 e5543 b5544 b5545 b5546 b5547 b5548 b5549 b5550 b5551 d5400 d5424 d5532
        omega
      have d5552 : (x 13 1 && x 13 8).toNat = 0 := by
        have r5553 := hand2 (x 13 1) (x 13 8)
        have b5554 := hb (x 13 8)
        have b5555 := hb (x 13 1 && x 13 8)
        clear * - r5553 b5554 b5555 d5536
        omega
      have d5556 : (x 12 9).toNat = 0 := by
        have r5557 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5558 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
        have e5559 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
        have e5560 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
        have e5561 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
        have e5562 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
        have e5563 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
        have b5564 := hb (x 6 7)
        have b5565 := hb (x 7 6)
        have b5566 := hb (x 8 5)
        have b5567 := hb (x 9 4)
        have b5568 := hb (x 10 11)
        have b5569 := hb (x 11 10)
        have b5570 := hb (x 12 9)
        have b5571 := hb (x 13 8)
        clear * - r5557 e5558 e5559 e5560 e5561 e5562 e5563 b5564 b5565 b5566 b5567 b5568 b5569 b5570 b5571 d5536 d5400 d5424 d5532
        omega
      have d5572 : (x 12 2 && x 12 9).toNat = 0 := by
        have r5573 := hand2 (x 12 2) (x 12 9)
        have b5574 := hb (x 12 9)
        have b5575 := hb (x 12 2 && x 12 9)
        clear * - r5573 b5574 b5575 d5556
        omega
      have d5576 : (x 11 10).toNat = 0 := by
        have r5577 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5578 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
        have e5579 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
        have e5580 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
        have e5581 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
        have e5582 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
        have e5583 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
        have b5584 := hb (x 6 7)
        have b5585 := hb (x 7 6)
        have b5586 := hb (x 8 5)
        have b5587 := hb (x 9 4)
        have b5588 := hb (x 10 11)
        have b5589 := hb (x 11 10)
        have b5590 := hb (x 12 9)
        have b5591 := hb (x 13 8)
        clear * - r5577 e5578 e5579 e5580 e5581 e5582 e5583 b5584 b5585 b5586 b5587 b5588 b5589 b5590 b5591 d5536 d5556 d5400 d5424 d5532
        omega
      have d5592 : (x 11 1 && x 11 10).toNat = 0 := by
        have r5593 := hand2 (x 11 1) (x 11 10)
        have b5594 := hb (x 11 10)
        have b5595 := hb (x 11 1 && x 11 10)
        clear * - r5593 b5594 b5595 d5576
        omega
      have d5596 : (x 11 3 && x 11 10).toNat = 0 := by
        have r5597 := hand2 (x 11 3) (x 11 10)
        have b5598 := hb (x 11 10)
        have b5599 := hb (x 11 3 && x 11 10)
        clear * - r5597 b5598 b5599 d5576
        omega
      have d5600 : (x 10 11).toNat = 0 := by
        have r5601 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5602 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
        have e5603 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
        have e5604 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
        have e5605 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
        have e5606 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
        have e5607 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
        have b5608 := hb (x 6 7)
        have b5609 := hb (x 7 6)
        have b5610 := hb (x 8 5)
        have b5611 := hb (x 9 4)
        have b5612 := hb (x 10 11)
        have b5613 := hb (x 11 10)
        have b5614 := hb (x 12 9)
        have b5615 := hb (x 13 8)
        clear * - r5601 e5602 e5603 e5604 e5605 e5606 e5607 b5608 b5609 b5610 b5611 b5612 b5613 b5614 b5615 d5536 d5556 d5576 d5400 d5424 d5532
        omega
      have d5616 : (x 10 2 && x 10 11).toNat = 0 := by
        have r5617 := hand2 (x 10 2) (x 10 11)
        have b5618 := hb (x 10 11)
        have b5619 := hb (x 10 2 && x 10 11)
        clear * - r5617 b5618 b5619 d5600
        omega
      have d5620 : (x 10 4 && x 10 11).toNat = 0 := by
        have r5621 := hand2 (x 10 4) (x 10 11)
        have b5622 := hb (x 10 11)
        have b5623 := hb (x 10 4 && x 10 11)
        clear * - r5621 b5622 b5623 d5600
        omega
      have d5624 : (x 7 6).toNat = 0 := by
        have r5625 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5626 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
        have e5627 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
        have e5628 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
        have e5629 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
        have e5630 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
        have e5631 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
        have b5632 := hb (x 6 7)
        have b5633 := hb (x 7 6)
        have b5634 := hb (x 8 5)
        have b5635 := hb (x 9 4)
        have b5636 := hb (x 10 11)
        have b5637 := hb (x 11 10)
        have b5638 := hb (x 12 9)
        have b5639 := hb (x 13 8)
        clear * - r5625 e5626 e5627 e5628 e5629 e5630 e5631 b5632 b5633 b5634 b5635 b5636 b5637 b5638 b5639 d5536 d5556 d5576 d5600 d5400 d5424 d5532
        omega
      have d5640 : (x 12 1).toNat = 0 := by
        have r5641 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5642 := hb (x (-1) 14)
        have b5643 := hb (x 0 13)
        have b5644 := hb (x 1 12)
        have b5645 := hb (x 2 11)
        have b5646 := hb (x 3 10)
        have b5647 := hb (x 4 9)
        have b5648 := hb (x 5 8)
        have b5649 := hb (x 6 7)
        have b5650 := hb (x 7 6)
        have b5651 := hb (x 8 5)
        have b5652 := hb (x 9 4)
        have b5653 := hb (x 10 3)
        have b5654 := hb (x 11 2)
        have b5655 := hb (x 12 1)
        clear * - r5641 b5642 b5643 b5644 b5645 b5646 b5647 b5648 b5649 b5650 b5651 b5652 b5653 b5654 b5655 d5400 d5424 d5624 d5532 g65 g61 g55 g48 g45 g37 g27
        omega
      have d5656 : (x 12 1 && x 12 14).toNat = 0 := by
        have r5657 := hand1 (x 12 1) (x 12 14)
        have b5658 := hb (x 12 1)
        have b5659 := hb (x 12 1 && x 12 14)
        clear * - r5657 b5658 b5659 d5640
        omega
      have d5660 : (x 12 1 && x 12 12).toNat = 0 := by
        have r5661 := hand1 (x 12 1) (x 12 12)
        have b5662 := hb (x 12 1)
        have b5663 := hb (x 12 1 && x 12 12)
        clear * - r5661 b5662 b5663 d5640
        omega
      have d5664 : (x 12 1 && x 12 10).toNat = 0 := by
        have r5665 := hand1 (x 12 1) (x 12 10)
        have b5666 := hb (x 12 1)
        have b5667 := hb (x 12 1 && x 12 10)
        clear * - r5665 b5666 b5667 d5640
        omega
      have d5668 : (x 11 2).toNat = 0 := by
        have r5669 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5670 := hb (x (-1) 14)
        have b5671 := hb (x 0 13)
        have b5672 := hb (x 1 12)
        have b5673 := hb (x 2 11)
        have b5674 := hb (x 3 10)
        have b5675 := hb (x 4 9)
        have b5676 := hb (x 5 8)
        have b5677 := hb (x 6 7)
        have b5678 := hb (x 7 6)
        have b5679 := hb (x 8 5)
        have b5680 := hb (x 9 4)
        have b5681 := hb (x 10 3)
        have b5682 := hb (x 11 2)
        have b5683 := hb (x 12 1)
        clear * - r5669 b5670 b5671 b5672 b5673 b5674 b5675 b5676 b5677 b5678 b5679 b5680 b5681 b5682 b5683 d5640 d5400 d5424 d5624 d5532 g65 g61 g55 g48 g45 g37 g27
        omega
      have d5684 : (x 11 2 && x 11 13).toNat = 0 := by
        have r5685 := hand1 (x 11 2) (x 11 13)
        have b5686 := hb (x 11 2)
        have b5687 := hb (x 11 2 && x 11 13)
        clear * - r5685 b5686 b5687 d5668
        omega
      have d5688 : (x 11 2 && x 11 11).toNat = 0 := by
        have r5689 := hand1 (x 11 2) (x 11 11)
        have b5690 := hb (x 11 2)
        have b5691 := hb (x 11 2 && x 11 11)
        clear * - r5689 b5690 b5691 d5668
        omega
      have d5692 : (x 13 13).toNat = 1 := by
        have r5693 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5694 := hb (x 11 2)
        have b5695 := hb (x 13 13)
        have b5696 := hb (x 12 1 && x 12 14)
        clear * - r5693 b5694 b5695 b5696 d5656 d5668
        omega
      have d5697 : (x 13 1).toNat = 1 := by
        have r5698 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
        have b5699 := hb (x 13 1)
        have b5700 := hb (x 13 13)
        clear * - r5698 b5699 b5700 d5692
        omega
      have d5701 : (x 14 14).toNat = 0 := by
        have r5702 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5703 := hb (x 13 1)
        have b5704 := hb (x 14 14)
        clear * - r5702 b5703 b5704 d5697
        omega
      have d5705 : (x 14 1 && x 14 14).toNat = 0 := by
        have r5706 := hand2 (x 14 1) (x 14 14)
        have b5707 := hb (x 14 14)
        have b5708 := hb (x 14 1 && x 14 14)
        clear * - r5706 b5707 b5708 d5701
        omega
      have d5709 : (x 14 2).toNat = 0 := by
        have r5710 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
        have b5711 := hb (x 14 2)
        have b5712 := hb (x 14 14)
        clear * - r5710 b5711 b5712 d5701
        omega
      have d5713 : (x 14 12).toNat = 0 := by
        have r5714 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5715 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e5716 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b5717 := hb (x 11 3)
        have b5718 := hb (x 12 2)
        have b5719 := hb (x 13 13)
        have b5720 := hb (x 14 12)
        clear * - r5714 e5715 e5716 b5717 b5718 b5719 b5720 d5692
        omega
      have d5721 : (x 14 4).toNat = 0 := by
        have r5722 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
        have b5723 := hb (x 14 4)
        have b5724 := hb (x 14 12)
        clear * - r5722 b5723 b5724 d5713
        omega
      have d5725 : (x 12 2).toNat = 0 := by
        have r5726 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5727 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e5728 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b5729 := hb (x 11 3)
        have b5730 := hb (x 12 2)
        have b5731 := hb (x 13 13)
        have b5732 := hb (x 14 12)
        clear * - r5726 e5727 e5728 b5729 b5730 b5731 b5732 d5713 d5692
        omega
      have d5733 : (x 12 2 && x 12 6).toNat = 0 := by
        have r5734 := hand1 (x 12 2) (x 12 6)
        have b5735 := hb (x 12 2)
        have b5736 := hb (x 12 2 && x 12 6)
        clear * - r5734 b5735 b5736 d5725
        omega
      have d5737 : (x 12 10).toNat = 0 := by
        have r5738 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
        have b5739 := hb (x 12 2)
        have b5740 := hb (x 12 10)
        clear * - r5738 b5739 b5740 d5725
        omega
      have d5741 : (x 11 3).toNat = 0 := by
        have r5742 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5743 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e5744 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b5745 := hb (x 11 3)
        have b5746 := hb (x 12 2)
        have b5747 := hb (x 13 13)
        have b5748 := hb (x 14 12)
        clear * - r5742 e5743 e5744 b5745 b5746 b5747 b5748 d5713 d5692 d5725
        omega
      have d5749 : (x 11 3 && x 11 7).toNat = 0 := by
        have r5750 := hand1 (x 11 3) (x 11 7)
        have b5751 := hb (x 11 3)
        have b5752 := hb (x 11 3 && x 11 7)
        clear * - r5750 b5751 b5752 d5741
        omega
      have d5753 : (x 11 11).toNat = 0 := by
        have r5754 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
        have b5755 := hb (x 11 3)
        have b5756 := hb (x 11 11)
        clear * - r5754 b5755 b5756 d5741
        omega
      have d5757 : (x 10 3).toNat = 0 := by
        have r5758 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5759 := hb (x (-1) 14)
        have b5760 := hb (x 0 13)
        have b5761 := hb (x 1 12)
        have b5762 := hb (x 2 11)
        have b5763 := hb (x 3 10)
        have b5764 := hb (x 4 9)
        have b5765 := hb (x 5 8)
        have b5766 := hb (x 6 7)
        have b5767 := hb (x 7 6)
        have b5768 := hb (x 8 5)
        have b5769 := hb (x 9 4)
        have b5770 := hb (x 10 3)
        have b5771 := hb (x 11 2)
        have b5772 := hb (x 12 1)
        clear * - r5758 b5759 b5760 b5761 b5762 b5763 b5764 b5765 b5766 b5767 b5768 b5769 b5770 b5771 b5772 d5640 d5668 d5400 d5424 d5624 d5532 g65 g61 g55 g48 g45 g37 g27
        omega
      have d5773 : (x 10 3 && x 10 14).toNat = 0 := by
        have r5774 := hand1 (x 10 3) (x 10 14)
        have b5775 := hb (x 10 3)
        have b5776 := hb (x 10 3 && x 10 14)
        clear * - r5774 b5775 b5776 d5757
        omega
      have d5777 : (x 13 11).toNat = 1 := by
        have r5778 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5779 := hb (x 9 4)
        have b5780 := hb (x 13 11)
        have b5781 := hb (x 12 1 && x 12 12)
        have b5782 := hb (x 11 2 && x 11 13)
        have b5783 := hb (x 10 3 && x 10 14)
        clear * - r5778 b5779 b5780 b5781 b5782 b5783 d5660 d5684 d5773 d5400
        omega
      have d5784 : (x 13 3).toNat = 1 := by
        have r5785 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
        have b5786 := hb (x 13 3)
        have b5787 := hb (x 13 11)
        clear * - r5785 b5786 b5787 d5777
        omega
      have d5788 : (x 16 12).toNat = 0 := by
        have r5789 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5790 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e5791 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b5792 := hb (x 13 3)
        have b5793 := hb (x 14 2)
        have b5794 := hb (x 15 13)
        have b5795 := hb (x 16 12)
        clear * - r5789 e5790 e5791 b5792 b5793 b5794 b5795 d5709 d5784
        omega
      have d5796 : (x 15 13).toNat = 0 := by
        have r5797 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5798 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e5799 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b5800 := hb (x 13 3)
        have b5801 := hb (x 14 2)
        have b5802 := hb (x 15 13)
        have b5803 := hb (x 16 12)
        clear * - r5797 e5798 e5799 b5800 b5801 b5802 b5803 d5788 d5709 d5784
        omega
      have d5804 : (x 13 2).toNat = 1 := by
        have r5805 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5806 := hb (x 13 2)
        have b5807 := hb (x 15 13)
        have b5808 := hb (x 14 1 && x 14 14)
        clear * - r5805 b5806 b5807 b5808 d5796 d5705
        omega
      have d5809 : (x 15 12).toNat = 0 := by
        have r5810 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5811 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e5812 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b5813 := hb (x 12 3)
        have b5814 := hb (x 13 2)
        have b5815 := hb (x 14 13)
        have b5816 := hb (x 15 12)
        clear * - r5810 e5811 e5812 b5813 b5814 b5815 b5816 d5804
        omega
      have d5817 : (x 14 13).toNat = 0 := by
        have r5818 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5819 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e5820 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b5821 := hb (x 12 3)
        have b5822 := hb (x 13 2)
        have b5823 := hb (x 14 13)
        have b5824 := hb (x 15 12)
        clear * - r5818 e5819 e5820 b5821 b5822 b5823 b5824 d5809 d5804
        omega
      have d5825 : (x 12 3).toNat = 0 := by
        have r5826 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5827 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e5828 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b5829 := hb (x 12 3)
        have b5830 := hb (x 13 2)
        have b5831 := hb (x 14 13)
        have b5832 := hb (x 15 12)
        clear * - r5826 e5827 e5828 b5829 b5830 b5831 b5832 d5809 d5817 d5804
        omega
      have d5833 : (x 14 1).toNat = 0 := by
        have r5834 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5835 := hb (x 1 14)
        have b5836 := hb (x 2 13)
        have b5837 := hb (x 3 12)
        have b5838 := hb (x 4 11)
        have b5839 := hb (x 5 10)
        have b5840 := hb (x 6 9)
        have b5841 := hb (x 7 8)
        have b5842 := hb (x 8 7)
        have b5843 := hb (x 9 6)
        have b5844 := hb (x 10 5)
        have b5845 := hb (x 11 4)
        have b5846 := hb (x 12 3)
        have b5847 := hb (x 13 2)
        have b5848 := hb (x 14 1)
        clear * - r5834 b5835 b5836 b5837 b5838 b5839 b5840 b5841 b5842 b5843 b5844 b5845 b5846 b5847 b5848 d5804 d5825 g56 g49 g47
        omega
      have d5849 : (x 11 4).toNat = 0 := by
        have r5850 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5851 := hb (x 1 14)
        have b5852 := hb (x 2 13)
        have b5853 := hb (x 3 12)
        have b5854 := hb (x 4 11)
        have b5855 := hb (x 5 10)
        have b5856 := hb (x 6 9)
        have b5857 := hb (x 7 8)
        have b5858 := hb (x 8 7)
        have b5859 := hb (x 9 6)
        have b5860 := hb (x 10 5)
        have b5861 := hb (x 11 4)
        have b5862 := hb (x 12 3)
        have b5863 := hb (x 13 2)
        have b5864 := hb (x 14 1)
        clear * - r5850 b5851 b5852 b5853 b5854 b5855 b5856 b5857 b5858 b5859 b5860 b5861 b5862 b5863 b5864 d5833 d5804 d5825 g56 g49 g47
        omega
      have d5865 : (x 10 5).toNat = 0 := by
        have r5866 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5867 := hb (x 1 14)
        have b5868 := hb (x 2 13)
        have b5869 := hb (x 3 12)
        have b5870 := hb (x 4 11)
        have b5871 := hb (x 5 10)
        have b5872 := hb (x 6 9)
        have b5873 := hb (x 7 8)
        have b5874 := hb (x 8 7)
        have b5875 := hb (x 9 6)
        have b5876 := hb (x 10 5)
        have b5877 := hb (x 11 4)
        have b5878 := hb (x 12 3)
        have b5879 := hb (x 13 2)
        have b5880 := hb (x 14 1)
        clear * - r5866 b5867 b5868 b5869 b5870 b5871 b5872 b5873 b5874 b5875 b5876 b5877 b5878 b5879 b5880 d5833 d5804 d5825 d5849 g56 g49 g47
        omega
      have d5881 : (x 9 6).toNat = 0 := by
        have r5882 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5883 := hb (x 1 14)
        have b5884 := hb (x 2 13)
        have b5885 := hb (x 3 12)
        have b5886 := hb (x 4 11)
        have b5887 := hb (x 5 10)
        have b5888 := hb (x 6 9)
        have b5889 := hb (x 7 8)
        have b5890 := hb (x 8 7)
        have b5891 := hb (x 9 6)
        have b5892 := hb (x 10 5)
        have b5893 := hb (x 11 4)
        have b5894 := hb (x 12 3)
        have b5895 := hb (x 13 2)
        have b5896 := hb (x 14 1)
        clear * - r5882 b5883 b5884 b5885 b5886 b5887 b5888 b5889 b5890 b5891 b5892 b5893 b5894 b5895 b5896 d5833 d5804 d5825 d5849 d5865 g56 g49 g47
        omega
      have d5897 : (x 8 7).toNat = 0 := by
        have r5898 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5899 := hb (x 1 14)
        have b5900 := hb (x 2 13)
        have b5901 := hb (x 3 12)
        have b5902 := hb (x 4 11)
        have b5903 := hb (x 5 10)
        have b5904 := hb (x 6 9)
        have b5905 := hb (x 7 8)
        have b5906 := hb (x 8 7)
        have b5907 := hb (x 9 6)
        have b5908 := hb (x 10 5)
        have b5909 := hb (x 11 4)
        have b5910 := hb (x 12 3)
        have b5911 := hb (x 13 2)
        have b5912 := hb (x 14 1)
        clear * - r5898 b5899 b5900 b5901 b5902 b5903 b5904 b5905 b5906 b5907 b5908 b5909 b5910 b5911 b5912 d5833 d5804 d5825 d5849 d5865 d5881 g56 g49 g47
        omega
      have d5913 : (x 8 1 && x 8 7).toNat = 0 := by
        have r5914 := hand2 (x 8 1) (x 8 7)
        have b5915 := hb (x 8 7)
        have b5916 := hb (x 8 1 && x 8 7)
        clear * - r5914 b5915 b5916 d5897
        omega
      have d5917 : (x 6 3 && x 6 9).toNat = 1 := by
        have r5918 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := by have q := hcov6 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5919 := hb (x 0 9)
        have b5920 := hb (x 9 6)
        have b5921 := hb (x 8 1 && x 8 7)
        have b5922 := hb (x 7 2 && x 7 8)
        have b5923 := hb (x 6 3 && x 6 9)
        have b5924 := hb (x 5 4 && x 5 10)
        have b5925 := hb (x 4 5 && x 4 11)
        have b5926 := hb (x 3 6 && x 3 12)
        have b5927 := hb (x 2 7 && x 2 13)
        have b5928 := hb (x 1 8 && x 1 14)
        clear * - r5918 b5919 b5920 b5921 b5922 b5923 b5924 b5925 b5926 b5927 b5928 d5881 d5913 d5440 g129 g130 g131 d5504 g132 g35
        omega
      have d5929 : (x 6 9).toNat = 1 := by
        have r5930 := hand2 (x 6 3) (x 6 9)
        have b5931 := hb (x 6 9)
        have b5932 := hb (x 6 3 && x 6 9)
        clear * - r5930 b5931 b5932 d5917
        omega
      have d5933 : (x 6 1).toNat = 1 := by
        have r5934 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
        have b5935 := hb (x 6 1)
        have b5936 := hb (x 6 9)
        clear * - r5934 b5935 b5936 d5929
        omega
      have d5937 : (x 7 14).toNat = 0 := by
        have r5938 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5939 := hb (x 6 1)
        have b5940 := hb (x 7 14)
        clear * - r5938 b5939 b5940 d5933
        omega
      have d5941 : (x 7 1 && x 7 14).toNat = 0 := by
        have r5942 := hand2 (x 7 1) (x 7 14)
        have b5943 := hb (x 7 14)
        have b5944 := hb (x 7 1 && x 7 14)
        clear * - r5942 b5943 b5944 d5937
        omega
      have d5945 : (x 6 2).toNat = 1 := by
        have r5946 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5947 := hb (x 6 2)
        have b5948 := hb (x 8 13)
        have b5949 := hb (x 7 1 && x 7 14)
        clear * - r5946 b5947 b5948 b5949 d5408 d5941
        omega
      have d5950 : (x 6 14).toNat = 1 := by
        have r5951 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have b5952 := hb (x 6 2)
        have b5953 := hb (x 6 14)
        clear * - r5951 b5952 b5953 d5945
        omega
      have d5954 : (x 5 1).toNat = 0 := by
        have r5955 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5956 := hb (x 5 1)
        have b5957 := hb (x 6 14)
        clear * - r5955 b5956 b5957 d5950
        omega
      have d5958 : (x 5 13).toNat = 0 := by
        have r5959 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
        have b5960 := hb (x 5 1)
        have b5961 := hb (x 5 13)
        clear * - r5959 b5960 b5961 d5954
        omega
      have d5962 : (x 5 5).toNat = 0 := by
        have r5963 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
        have b5964 := hb (x 5 5)
        have b5965 := hb (x 5 13)
        clear * - r5963 b5964 b5965 d5958
        omega
      have d5966 : (x 4 1 && x 4 14).toNat = 1 := by
        have r5967 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b5968 := hb (x 3 2)
        have b5969 := hb (x 5 13)
        have b5970 := hb (x 4 1 && x 4 14)
        clear * - r5967 b5968 b5969 b5970 d5958 g51
        omega
      have d5971 : (x 4 14).toNat = 1 := by
        have r5972 := hand2 (x 4 1) (x 4 14)
        have b5973 := hb (x 4 14)
        have b5974 := hb (x 4 1 && x 4 14)
        clear * - r5972 b5973 b5974 d5966
        omega
      have d5975 : (x 8 12).toNat = 0 := by
        have r5976 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5977 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e5978 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b5979 := hb (x 5 3)
        have b5980 := hb (x 6 2)
        have b5981 := hb (x 7 13)
        have b5982 := hb (x 8 12)
        clear * - r5976 e5977 e5978 b5979 b5980 b5981 b5982 d5945
        omega
      have d5983 : (x 8 2 && x 8 12).toNat = 0 := by
        have r5984 := hand2 (x 8 2) (x 8 12)
        have b5985 := hb (x 8 12)
        have b5986 := hb (x 8 2 && x 8 12)
        clear * - r5984 b5985 b5986 d5975
        omega
      have d5987 : (x 8 4).toNat = 0 := by
        have r5988 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b5989 := hb (x 8 4)
        have b5990 := hb (x 8 12)
        clear * - r5988 b5989 b5990 d5975
        omega
      have d5991 : (x 7 13).toNat = 0 := by
        have r5992 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e5993 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e5994 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b5995 := hb (x 5 3)
        have b5996 := hb (x 6 2)
        have b5997 := hb (x 7 13)
        have b5998 := hb (x 8 12)
        clear * - r5992 e5993 e5994 b5995 b5996 b5997 b5998 d5975 d5945
        omega
      have d5999 : (x 7 3 && x 7 13).toNat = 0 := by
        have r6000 := hand2 (x 7 3) (x 7 13)
        have b6001 := hb (x 7 13)
        have b6002 := hb (x 7 3 && x 7 13)
        clear * - r6000 b6001 b6002 d5991
        omega
      have d6003 : (x 7 5).toNat = 0 := by
        have r6004 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
        have b6005 := hb (x 7 5)
        have b6006 := hb (x 7 13)
        clear * - r6004 b6005 b6006 d5991
        omega
      have d6007 : (x 7 5 && x 7 14).toNat = 0 := by
        have r6008 := hand1 (x 7 5) (x 7 14)
        have b6009 := hb (x 7 5)
        have b6010 := hb (x 7 5 && x 7 14)
        clear * - r6008 b6009 b6010 d6003
        omega
      have d6011 : (x 6 6).toNat = 1 := by
        have r6012 : 1 ≤ (x 12 9).toNat + (x 11 1 && x 11 10).toNat + (x 10 2 && x 10 11).toNat + (x 9 3 && x 9 12).toNat + (x 8 4 && x 8 13).toNat + (x 7 5 && x 7 14).toNat + (x 6 6).toNat := by have q := hcov9 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6013 := hb (x 6 6)
        have b6014 := hb (x 12 9)
        have b6015 := hb (x 11 1 && x 11 10)
        have b6016 := hb (x 10 2 && x 10 11)
        have b6017 := hb (x 9 3 && x 9 12)
        have b6018 := hb (x 8 4 && x 8 13)
        have b6019 := hb (x 7 5 && x 7 14)
        clear * - r6012 b6013 b6014 b6015 b6016 b6017 b6018 b6019 d5556 d5592 d5616 d5392 d5416 d6007
        omega
      have d6020 : (x 12 8).toNat = 0 := by
        have r6021 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6022 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e6023 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e6024 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e6025 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e6026 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e6027 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b6028 := hb (x 5 7)
        have b6029 := hb (x 6 6)
        have b6030 := hb (x 7 5)
        have b6031 := hb (x 8 4)
        have b6032 := hb (x 9 11)
        have b6033 := hb (x 10 10)
        have b6034 := hb (x 11 9)
        have b6035 := hb (x 12 8)
        clear * - r6021 e6022 e6023 e6024 e6025 e6026 e6027 b6028 b6029 b6030 b6031 b6032 b6033 b6034 b6035 d5987 d6003 d6011
        omega
      have d6036 : (x 11 9).toNat = 0 := by
        have r6037 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6038 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e6039 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e6040 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e6041 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e6042 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e6043 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b6044 := hb (x 5 7)
        have b6045 := hb (x 6 6)
        have b6046 := hb (x 7 5)
        have b6047 := hb (x 8 4)
        have b6048 := hb (x 9 11)
        have b6049 := hb (x 10 10)
        have b6050 := hb (x 11 9)
        have b6051 := hb (x 12 8)
        clear * - r6037 e6038 e6039 e6040 e6041 e6042 e6043 b6044 b6045 b6046 b6047 b6048 b6049 b6050 b6051 d6020 d5987 d6003 d6011
        omega
      have d6052 : (x 10 10).toNat = 0 := by
        have r6053 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6054 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e6055 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e6056 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e6057 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e6058 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e6059 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b6060 := hb (x 5 7)
        have b6061 := hb (x 6 6)
        have b6062 := hb (x 7 5)
        have b6063 := hb (x 8 4)
        have b6064 := hb (x 9 11)
        have b6065 := hb (x 10 10)
        have b6066 := hb (x 11 9)
        have b6067 := hb (x 12 8)
        clear * - r6053 e6054 e6055 e6056 e6057 e6058 e6059 b6060 b6061 b6062 b6063 b6064 b6065 b6066 b6067 d6020 d6036 d5987 d6003 d6011
        omega
      have d6068 : (x 9 11).toNat = 0 := by
        have r6069 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6070 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e6071 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e6072 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e6073 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e6074 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e6075 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have b6076 := hb (x 5 7)
        have b6077 := hb (x 6 6)
        have b6078 := hb (x 7 5)
        have b6079 := hb (x 8 4)
        have b6080 := hb (x 9 11)
        have b6081 := hb (x 10 10)
        have b6082 := hb (x 11 9)
        have b6083 := hb (x 12 8)
        clear * - r6069 e6070 e6071 e6072 e6073 e6074 e6075 b6076 b6077 b6078 b6079 b6080 b6081 b6082 b6083 d6020 d6036 d6052 d5987 d6003 d6011
        omega
      have d6084 : (x 9 1 && x 9 11).toNat = 0 := by
        have r6085 := hand2 (x 9 1) (x 9 11)
        have b6086 := hb (x 9 11)
        have b6087 := hb (x 9 1 && x 9 11)
        clear * - r6085 b6086 b6087 d6068
        omega
      have d6088 : (x 6 4 && x 6 14).toNat = 1 := by
        have r6089 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6090 := hb (x 5 5)
        have b6091 := hb (x 10 10)
        have b6092 := hb (x 9 1 && x 9 11)
        have b6093 := hb (x 8 2 && x 8 12)
        have b6094 := hb (x 7 3 && x 7 13)
        have b6095 := hb (x 6 4 && x 6 14)
        clear * - r6089 b6090 b6091 b6092 b6093 b6094 b6095 d6052 d6084 d5983 d5999 d5962
        omega
      have d6096 : (x 6 4).toNat = 1 := by
        have r6097 := hand1 (x 6 4) (x 6 14)
        have b6098 := hb (x 6 4)
        have b6099 := hb (x 6 4 && x 6 14)
        clear * - r6097 b6098 b6099 d6088
        omega
      have d6100 : (x 6 12).toNat = 1 := by
        have r6101 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
        have b6102 := hb (x 6 4)
        have b6103 := hb (x 6 12)
        clear * - r6101 b6102 b6103 d6096
        omega
      have d6104 : (x 10 8).toNat = 0 := by
        have r6105 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6106 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e6107 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e6108 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e6109 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e6110 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e6111 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b6112 := hb (x 3 7)
        have b6113 := hb (x 4 6)
        have b6114 := hb (x 5 5)
        have b6115 := hb (x 6 4)
        have b6116 := hb (x 7 11)
        have b6117 := hb (x 8 10)
        have b6118 := hb (x 9 9)
        have b6119 := hb (x 10 8)
        clear * - r6105 e6106 e6107 e6108 e6109 e6110 e6111 b6112 b6113 b6114 b6115 b6116 b6117 b6118 b6119 d6096 d5962
        omega
      have d6120 : (x 10 4 && x 10 8).toNat = 0 := by
        have r6121 := hand2 (x 10 4) (x 10 8)
        have b6122 := hb (x 10 8)
        have b6123 := hb (x 10 4 && x 10 8)
        clear * - r6121 b6122 b6123 d6104
        omega
      have d6124 : (x 9 9).toNat = 0 := by
        have r6125 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6126 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e6127 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e6128 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e6129 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e6130 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e6131 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b6132 := hb (x 3 7)
        have b6133 := hb (x 4 6)
        have b6134 := hb (x 5 5)
        have b6135 := hb (x 6 4)
        have b6136 := hb (x 7 11)
        have b6137 := hb (x 8 10)
        have b6138 := hb (x 9 9)
        have b6139 := hb (x 10 8)
        clear * - r6125 e6126 e6127 e6128 e6129 e6130 e6131 b6132 b6133 b6134 b6135 b6136 b6137 b6138 b6139 d6104 d6096 d5962
        omega
      have d6140 : (x 9 5 && x 9 9).toNat = 0 := by
        have r6141 := hand2 (x 9 5) (x 9 9)
        have b6142 := hb (x 9 9)
        have b6143 := hb (x 9 5 && x 9 9)
        clear * - r6141 b6142 b6143 d6124
        omega
      have d6144 : (x 8 10).toNat = 0 := by
        have r6145 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6146 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e6147 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e6148 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e6149 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e6150 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e6151 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b6152 := hb (x 3 7)
        have b6153 := hb (x 4 6)
        have b6154 := hb (x 5 5)
        have b6155 := hb (x 6 4)
        have b6156 := hb (x 7 11)
        have b6157 := hb (x 8 10)
        have b6158 := hb (x 9 9)
        have b6159 := hb (x 10 8)
        clear * - r6145 e6146 e6147 e6148 e6149 e6150 e6151 b6152 b6153 b6154 b6155 b6156 b6157 b6158 b6159 d6104 d6124 d6096 d5962
        omega
      have d6160 : (x 8 6 && x 8 10).toNat = 0 := by
        have r6161 := hand2 (x 8 6) (x 8 10)
        have b6162 := hb (x 8 10)
        have b6163 := hb (x 8 6 && x 8 10)
        clear * - r6161 b6162 b6163 d6144
        omega
      have d6164 : (x 7 11).toNat = 0 := by
        have r6165 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6166 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e6167 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e6168 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e6169 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e6170 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e6171 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have b6172 := hb (x 3 7)
        have b6173 := hb (x 4 6)
        have b6174 := hb (x 5 5)
        have b6175 := hb (x 6 4)
        have b6176 := hb (x 7 11)
        have b6177 := hb (x 8 10)
        have b6178 := hb (x 9 9)
        have b6179 := hb (x 10 8)
        clear * - r6165 e6166 e6167 e6168 e6169 e6170 e6171 b6172 b6173 b6174 b6175 b6176 b6177 b6178 b6179 d6104 d6124 d6144 d6096 d5962
        omega
      have d6180 : (x 7 7 && x 7 11).toNat = 0 := by
        have r6181 := hand2 (x 7 7) (x 7 11)
        have b6182 := hb (x 7 11)
        have b6183 := hb (x 7 7 && x 7 11)
        clear * - r6181 b6182 b6183 d6164
        omega
      have d6184 : (x 13 5).toNat = 1 := by
        have r6185 : 1 ≤ (x 14 4).toNat + (x 13 1 && x 13 5).toNat + (x 12 2 && x 12 6).toNat + (x 11 3 && x 11 7).toNat + (x 10 4 && x 10 8).toNat + (x 9 5 && x 9 9).toNat + (x 8 6 && x 8 10).toNat + (x 7 7 && x 7 11).toNat + (x 6 8 && x 6 12).toNat + (x 5 9 && x 5 13).toNat + (x 4 10 && x 4 14).toNat + (x 3 11).toNat := by have q := hcov4 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6186 : (x 13 1 && x 13 5).toNat = (x 13 5).toNat := handr _ _ (fun h => hp13 13 (hp5 13 (h)))
        have e6187 : (x 4 10 && x 4 14).toNat = (x 4 10).toNat := handl _ _ (fun h => hp2 4 (hp10 4 (h)))
        have b6188 := hb (x 3 11)
        have b6189 := hb (x 4 10)
        have b6190 := hb (x 13 5)
        have b6191 := hb (x 14 4)
        have b6192 := hb (x 12 2 && x 12 6)
        have b6193 := hb (x 11 3 && x 11 7)
        have b6194 := hb (x 10 4 && x 10 8)
        have b6195 := hb (x 9 5 && x 9 9)
        have b6196 := hb (x 8 6 && x 8 10)
        have b6197 := hb (x 7 7 && x 7 11)
        have b6198 := hb (x 6 8 && x 6 12)
        have b6199 := hb (x 5 9 && x 5 13)
        clear * - r6185 e6186 e6187 b6188 b6189 b6190 b6191 b6192 b6193 b6194 b6195 b6196 b6197 b6198 b6199 d5721 d5733 d5749 d6120 d6140 d6160 d6180 d5301 d5321 d5325 d5341
        omega
      have d6200 : (x 18 8).toNat = 0 := by
        have r6201 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6202 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
        have e6203 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
        have e6204 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
        have e6205 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
        have e6206 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
        have e6207 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
        have b6208 := hb (x 11 7)
        have b6209 := hb (x 12 6)
        have b6210 := hb (x 13 5)
        have b6211 := hb (x 14 4)
        have b6212 := hb (x 15 11)
        have b6213 := hb (x 16 10)
        have b6214 := hb (x 17 9)
        have b6215 := hb (x 18 8)
        clear * - r6201 e6202 e6203 e6204 e6205 e6206 e6207 b6208 b6209 b6210 b6211 b6212 b6213 b6214 b6215 d5721 d6184
        omega
      have d6216 : (x 17 9).toNat = 0 := by
        have r6217 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6218 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
        have e6219 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
        have e6220 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
        have e6221 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
        have e6222 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
        have e6223 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
        have b6224 := hb (x 11 7)
        have b6225 := hb (x 12 6)
        have b6226 := hb (x 13 5)
        have b6227 := hb (x 14 4)
        have b6228 := hb (x 15 11)
        have b6229 := hb (x 16 10)
        have b6230 := hb (x 17 9)
        have b6231 := hb (x 18 8)
        clear * - r6217 e6218 e6219 e6220 e6221 e6222 e6223 b6224 b6225 b6226 b6227 b6228 b6229 b6230 b6231 d6200 d5721 d6184
        omega
      have d6232 : (x 16 10).toNat = 0 := by
        have r6233 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6234 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
        have e6235 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
        have e6236 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
        have e6237 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
        have e6238 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
        have e6239 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
        have b6240 := hb (x 11 7)
        have b6241 := hb (x 12 6)
        have b6242 := hb (x 13 5)
        have b6243 := hb (x 14 4)
        have b6244 := hb (x 15 11)
        have b6245 := hb (x 16 10)
        have b6246 := hb (x 17 9)
        have b6247 := hb (x 18 8)
        clear * - r6233 e6234 e6235 e6236 e6237 e6238 e6239 b6240 b6241 b6242 b6243 b6244 b6245 b6246 b6247 d6200 d6216 d5721 d6184
        omega
      have d6248 : (x 15 11).toNat = 0 := by
        have r6249 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6250 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
        have e6251 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
        have e6252 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
        have e6253 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
        have e6254 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
        have e6255 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
        have b6256 := hb (x 11 7)
        have b6257 := hb (x 12 6)
        have b6258 := hb (x 13 5)
        have b6259 := hb (x 14 4)
        have b6260 := hb (x 15 11)
        have b6261 := hb (x 16 10)
        have b6262 := hb (x 17 9)
        have b6263 := hb (x 18 8)
        clear * - r6249 e6250 e6251 e6252 e6253 e6254 e6255 b6256 b6257 b6258 b6259 b6260 b6261 b6262 b6263 d6200 d6216 d6232 d5721 d6184
        omega
      have d6264 : (x 12 6).toNat = 0 := by
        have r6265 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6266 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
        have e6267 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
        have e6268 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
        have e6269 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
        have e6270 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
        have e6271 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
        have b6272 := hb (x 11 7)
        have b6273 := hb (x 12 6)
        have b6274 := hb (x 13 5)
        have b6275 := hb (x 14 4)
        have b6276 := hb (x 15 11)
        have b6277 := hb (x 16 10)
        have b6278 := hb (x 17 9)
        have b6279 := hb (x 18 8)
        clear * - r6265 e6266 e6267 e6268 e6269 e6270 e6271 b6272 b6273 b6274 b6275 b6276 b6277 b6278 b6279 d6200 d6216 d6232 d6248 d5721 d6184
        omega
      have d6280 : (x 11 7).toNat = 0 := by
        have r6281 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6282 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
        have e6283 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
        have e6284 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
        have e6285 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
        have e6286 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
        have e6287 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
        have b6288 := hb (x 11 7)
        have b6289 := hb (x 12 6)
        have b6290 := hb (x 13 5)
        have b6291 := hb (x 14 4)
        have b6292 := hb (x 15 11)
        have b6293 := hb (x 16 10)
        have b6294 := hb (x 17 9)
        have b6295 := hb (x 18 8)
        clear * - r6281 e6282 e6283 e6284 e6285 e6286 e6287 b6288 b6289 b6290 b6291 b6292 b6293 b6294 b6295 d6200 d6216 d6232 d6248 d5721 d6184 d6264
        omega
      have d6296 : (x 17 1).toNat = 0 := by
        have r6297 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6298 := hb (x 4 14)
        have b6299 := hb (x 5 13)
        have b6300 := hb (x 6 12)
        have b6301 := hb (x 7 11)
        have b6302 := hb (x 8 10)
        have b6303 := hb (x 9 9)
        have b6304 := hb (x 10 8)
        have b6305 := hb (x 11 7)
        have b6306 := hb (x 12 6)
        have b6307 := hb (x 13 5)
        have b6308 := hb (x 14 4)
        have b6309 := hb (x 15 3)
        have b6310 := hb (x 16 2)
        have b6311 := hb (x 17 1)
        clear * - r6297 b6298 b6299 b6300 b6301 b6302 b6303 b6304 b6305 b6306 b6307 b6308 b6309 b6310 b6311 d5721 d6184 d6264 d6280 d6104 d6124 d6144 d6164 d6100 d5958 d5971
        omega
      have d6312 : (x 17 1 && x 17 12).toNat = 0 := by
        have r6313 := hand1 (x 17 1) (x 17 12)
        have b6314 := hb (x 17 1)
        have b6315 := hb (x 17 1 && x 17 12)
        clear * - r6313 b6314 b6315 d6296
        omega
      have d6316 : (x 16 2).toNat = 0 := by
        have r6317 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6318 := hb (x 4 14)
        have b6319 := hb (x 5 13)
        have b6320 := hb (x 6 12)
        have b6321 := hb (x 7 11)
        have b6322 := hb (x 8 10)
        have b6323 := hb (x 9 9)
        have b6324 := hb (x 10 8)
        have b6325 := hb (x 11 7)
        have b6326 := hb (x 12 6)
        have b6327 := hb (x 13 5)
        have b6328 := hb (x 14 4)
        have b6329 := hb (x 15 3)
        have b6330 := hb (x 16 2)
        have b6331 := hb (x 17 1)
        clear * - r6317 b6318 b6319 b6320 b6321 b6322 b6323 b6324 b6325 b6326 b6327 b6328 b6329 b6330 b6331 d6296 d5721 d6184 d6264 d6280 d6104 d6124 d6144 d6164 d6100 d5958 d5971
        omega
      have d6332 : (x 16 2 && x 16 13).toNat = 0 := by
        have r6333 := hand1 (x 16 2) (x 16 13)
        have b6334 := hb (x 16 2)
        have b6335 := hb (x 16 2 && x 16 13)
        clear * - r6333 b6334 b6335 d6316
        omega
      have d6336 : (x 15 3).toNat = 0 := by
        have r6337 : (x 17 1).toNat + (x 16 2).toNat + (x 15 3).toNat + (x 14 4).toNat + (x 13 5).toNat + (x 12 6).toNat + (x 11 7).toNat + (x 10 8).toNat + (x 9 9).toNat + (x 8 10).toNat + (x 7 11).toNat + (x 6 12).toNat + (x 5 13).toNat + (x 4 14).toNat = 3 := by have q := hcount 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6338 := hb (x 4 14)
        have b6339 := hb (x 5 13)
        have b6340 := hb (x 6 12)
        have b6341 := hb (x 7 11)
        have b6342 := hb (x 8 10)
        have b6343 := hb (x 9 9)
        have b6344 := hb (x 10 8)
        have b6345 := hb (x 11 7)
        have b6346 := hb (x 12 6)
        have b6347 := hb (x 13 5)
        have b6348 := hb (x 14 4)
        have b6349 := hb (x 15 3)
        have b6350 := hb (x 16 2)
        have b6351 := hb (x 17 1)
        clear * - r6337 b6338 b6339 b6340 b6341 b6342 b6343 b6344 b6345 b6346 b6347 b6348 b6349 b6350 b6351 d6296 d6316 d5721 d6184 d6264 d6280 d6104 d6124 d6144 d6164 d6100 d5958 d5971
        omega
      have d6352 : (x 15 3 && x 15 14).toNat = 0 := by
        have r6353 := hand1 (x 15 3) (x 15 14)
        have b6354 := hb (x 15 3)
        have b6355 := hb (x 15 3 && x 15 14)
        clear * - r6353 b6354 b6355 d6336
        omega
      have d6356 : (x 18 11).toNat = 1 := by
        have r6357 : 1 ≤ (x 18 11).toNat + (x 17 1 && x 17 12).toNat + (x 16 2 && x 16 13).toNat + (x 15 3 && x 15 14).toNat + (x 14 4).toNat := by have q := hcov11 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6358 := hb (x 14 4)
        have b6359 := hb (x 18 11)
        have b6360 := hb (x 17 1 && x 17 12)
        have b6361 := hb (x 16 2 && x 16 13)
        have b6362 := hb (x 15 3 && x 15 14)
        clear * - r6357 b6358 b6359 b6360 b6361 b6362 d6312 d6332 d6352 d5721
        omega
      have d6363 : (x 21 8).toNat = 0 := by
        have r6364 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6365 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
        have e6366 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
        have e6367 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
        have e6368 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
        have e6369 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
        have e6370 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
        have b6371 := hb (x 14 7)
        have b6372 := hb (x 15 6)
        have b6373 := hb (x 16 5)
        have b6374 := hb (x 17 4)
        have b6375 := hb (x 18 11)
        have b6376 := hb (x 19 10)
        have b6377 := hb (x 20 9)
        have b6378 := hb (x 21 8)
        clear * - r6364 e6365 e6366 e6367 e6368 e6369 e6370 b6371 b6372 b6373 b6374 b6375 b6376 b6377 b6378 d6356
        omega
      have d6379 : (x 20 9).toNat = 0 := by
        have r6380 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6381 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
        have e6382 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
        have e6383 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
        have e6384 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
        have e6385 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
        have e6386 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
        have b6387 := hb (x 14 7)
        have b6388 := hb (x 15 6)
        have b6389 := hb (x 16 5)
        have b6390 := hb (x 17 4)
        have b6391 := hb (x 18 11)
        have b6392 := hb (x 19 10)
        have b6393 := hb (x 20 9)
        have b6394 := hb (x 21 8)
        clear * - r6380 e6381 e6382 e6383 e6384 e6385 e6386 b6387 b6388 b6389 b6390 b6391 b6392 b6393 b6394 d6363 d6356
        omega
      have d6395 : (x 19 10).toNat = 0 := by
        have r6396 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6397 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
        have e6398 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
        have e6399 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
        have e6400 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
        have e6401 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
        have e6402 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
        have b6403 := hb (x 14 7)
        have b6404 := hb (x 15 6)
        have b6405 := hb (x 16 5)
        have b6406 := hb (x 17 4)
        have b6407 := hb (x 18 11)
        have b6408 := hb (x 19 10)
        have b6409 := hb (x 20 9)
        have b6410 := hb (x 21 8)
        clear * - r6396 e6397 e6398 e6399 e6400 e6401 e6402 b6403 b6404 b6405 b6406 b6407 b6408 b6409 b6410 d6363 d6379 d6356
        omega
      have d6411 : (x 17 4).toNat = 0 := by
        have r6412 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6413 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
        have e6414 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
        have e6415 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
        have e6416 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
        have e6417 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
        have e6418 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
        have b6419 := hb (x 14 7)
        have b6420 := hb (x 15 6)
        have b6421 := hb (x 16 5)
        have b6422 := hb (x 17 4)
        have b6423 := hb (x 18 11)
        have b6424 := hb (x 19 10)
        have b6425 := hb (x 20 9)
        have b6426 := hb (x 21 8)
        clear * - r6412 e6413 e6414 e6415 e6416 e6417 e6418 b6419 b6420 b6421 b6422 b6423 b6424 b6425 b6426 d6363 d6379 d6395 d6356
        omega
      have d6427 : (x 16 5).toNat = 0 := by
        have r6428 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6429 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
        have e6430 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
        have e6431 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
        have e6432 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
        have e6433 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
        have e6434 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
        have b6435 := hb (x 14 7)
        have b6436 := hb (x 15 6)
        have b6437 := hb (x 16 5)
        have b6438 := hb (x 17 4)
        have b6439 := hb (x 18 11)
        have b6440 := hb (x 19 10)
        have b6441 := hb (x 20 9)
        have b6442 := hb (x 21 8)
        clear * - r6428 e6429 e6430 e6431 e6432 e6433 e6434 b6435 b6436 b6437 b6438 b6439 b6440 b6441 b6442 d6363 d6379 d6395 d6356 d6411
        omega
      have d6443 : (x 15 6).toNat = 0 := by
        have r6444 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6445 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
        have e6446 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
        have e6447 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
        have e6448 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
        have e6449 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
        have e6450 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
        have b6451 := hb (x 14 7)
        have b6452 := hb (x 15 6)
        have b6453 := hb (x 16 5)
        have b6454 := hb (x 17 4)
        have b6455 := hb (x 18 11)
        have b6456 := hb (x 19 10)
        have b6457 := hb (x 20 9)
        have b6458 := hb (x 21 8)
        clear * - r6444 e6445 e6446 e6447 e6448 e6449 e6450 b6451 b6452 b6453 b6454 b6455 b6456 b6457 b6458 d6363 d6379 d6395 d6356 d6411 d6427
        omega
      have d6459 : (x 14 7).toNat = 0 := by
        have r6460 : (x 21 8).toNat + (x 20 1 && x 20 9).toNat + (x 19 2 && x 19 10).toNat + (x 18 3 && x 18 11).toNat + (x 17 4 && x 17 12).toNat + (x 16 5 && x 16 13).toNat + (x 15 6 && x 15 14).toNat + (x 14 7).toNat = 1 := by have q := hd8 21; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6461 : (x 20 1 && x 20 9).toNat = (x 20 9).toNat := handr _ _ (fun h => hp9 20 (h))
        have e6462 : (x 19 2 && x 19 10).toNat = (x 19 10).toNat := handr _ _ (fun h => hp10 19 (h))
        have e6463 : (x 18 3 && x 18 11).toNat = (x 18 11).toNat := handr _ _ (fun h => hp11 18 (h))
        have e6464 : (x 17 4 && x 17 12).toNat = (x 17 4).toNat := handl _ _ (fun h => hp4 17 (h))
        have e6465 : (x 16 5 && x 16 13).toNat = (x 16 5).toNat := handl _ _ (fun h => hp5 16 (h))
        have e6466 : (x 15 6 && x 15 14).toNat = (x 15 6).toNat := handl _ _ (fun h => hp6 15 (h))
        have b6467 := hb (x 14 7)
        have b6468 := hb (x 15 6)
        have b6469 := hb (x 16 5)
        have b6470 := hb (x 17 4)
        have b6471 := hb (x 18 11)
        have b6472 := hb (x 19 10)
        have b6473 := hb (x 20 9)
        have b6474 := hb (x 21 8)
        clear * - r6460 e6461 e6462 e6463 e6464 e6465 e6466 b6467 b6468 b6469 b6470 b6471 b6472 b6473 b6474 d6363 d6379 d6395 d6356 d6411 d6427 d6443
        omega
      have d6475 : (x 7 7 && x 7 14).toNat = 1 := by
        have r6476 : 1 ≤ (x 14 7).toNat + (x 13 1 && x 13 8).toNat + (x 12 2 && x 12 9).toNat + (x 11 3 && x 11 10).toNat + (x 10 4 && x 10 11).toNat + (x 9 5 && x 9 12).toNat + (x 8 6 && x 8 13).toNat + (x 7 7 && x 7 14).toNat + (x 6 8).toNat := by have q := hcov7 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6477 := hb (x 6 8)
        have b6478 := hb (x 14 7)
        have b6479 := hb (x 13 1 && x 13 8)
        have b6480 := hb (x 12 2 && x 12 9)
        have b6481 := hb (x 11 3 && x 11 10)
        have b6482 := hb (x 10 4 && x 10 11)
        have b6483 := hb (x 9 5 && x 9 12)
        have b6484 := hb (x 8 6 && x 8 13)
        have b6485 := hb (x 7 7 && x 7 14)
        clear * - r6476 b6477 b6478 b6479 b6480 b6481 b6482 b6483 b6484 b6485 d6459 d5552 d5572 d5596 d5620 d5396 d5420 d5281
        omega
      have d6486 : (x 7 7).toNat = 1 := by
        have r6487 := hand1 (x 7 7) (x 7 14)
        have b6488 := hb (x 7 7)
        have b6489 := hb (x 7 7 && x 7 14)
        clear * - r6487 b6488 b6489 d6475
        omega
      have d6490 : (x 14 8).toNat = 0 := by
        have r6491 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6492 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e6493 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e6494 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e6495 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e6496 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e6497 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b6498 := hb (x 7 7)
        have b6499 := hb (x 8 6)
        have b6500 := hb (x 9 5)
        have b6501 := hb (x 10 4)
        have b6502 := hb (x 11 11)
        have b6503 := hb (x 12 10)
        have b6504 := hb (x 13 9)
        have b6505 := hb (x 14 8)
        clear * - r6491 e6492 e6493 e6494 e6495 e6496 e6497 b6498 b6499 b6500 b6501 b6502 b6503 b6504 b6505 d5737 d5753 d6486
        omega
      have d6506 : (x 13 9).toNat = 0 := by
        have r6507 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6508 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
        have e6509 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
        have e6510 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
        have e6511 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
        have e6512 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
        have e6513 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
        have b6514 := hb (x 7 7)
        have b6515 := hb (x 8 6)
        have b6516 := hb (x 9 5)
        have b6517 := hb (x 10 4)
        have b6518 := hb (x 11 11)
        have b6519 := hb (x 12 10)
        have b6520 := hb (x 13 9)
        have b6521 := hb (x 14 8)
        clear * - r6507 e6508 e6509 e6510 e6511 e6512 e6513 b6514 b6515 b6516 b6517 b6518 b6519 b6520 b6521 d6490 d5737 d5753 d6486
        omega
      have d6522 : (x 10 3 && x 10 12).toNat = 1 := by
        have r6523 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6524 := hb (x 7 6)
        have b6525 := hb (x 13 9)
        have b6526 := hb (x 12 1 && x 12 10)
        have b6527 := hb (x 11 2 && x 11 11)
        have b6528 := hb (x 10 3 && x 10 12)
        have b6529 := hb (x 9 4 && x 9 13)
        have b6530 := hb (x 8 5 && x 8 14)
        clear * - r6523 b6524 b6525 b6526 b6527 b6528 b6529 b6530 d6506 d5664 d5688 d5404 d5428 d5624
        omega
      have d6531 : (x 10 12).toNat = 1 := by
        have r6532 := hand2 (x 10 3) (x 10 12)
        have b6533 := hb (x 10 12)
        have b6534 := hb (x 10 3 && x 10 12)
        clear * - r6532 b6533 b6534 d6522
        omega
      have d6535 : (x 9 13).toNat = 0 := by
        have r6536 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e6537 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e6538 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b6539 := hb (x 7 3)
        have b6540 := hb (x 8 2)
        have b6541 := hb (x 9 13)
        have b6542 := hb (x 10 12)
        clear * - r6536 e6537 e6538 b6539 b6540 b6541 b6542 d6531
        omega
      have d6543 : (x 9 5).toNat = 0 := by
        have r6544 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
        have b6545 := hb (x 9 5)
        have b6546 := hb (x 9 13)
        clear * - r6544 b6545 b6546 d6535
        omega
      have d6547 : (x 8 1 && x 8 6).toNat = 1 := by
        have r6548 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6549 := hb (x (-1) 10)
        have b6550 := hb (x 9 5)
        have b6551 := hb (x 8 1 && x 8 6)
        have b6552 := hb (x 7 2 && x 7 7)
        have b6553 := hb (x 6 3 && x 6 8)
        have b6554 := hb (x 5 4 && x 5 9)
        have b6555 := hb (x 4 5 && x 4 10)
        have b6556 := hb (x 3 6 && x 3 11)
        have b6557 := hb (x 2 7 && x 2 12)
        have b6558 := hb (x 1 8 && x 1 13)
        have b6559 := hb (x 0 9 && x 0 14)
        clear * - r6548 b6549 b6550 b6551 b6552 b6553 b6554 b6555 b6556 b6557 b6558 b6559 d6543 d5444 d5297 g107 g108 g109 d5508 g110 g111 g26
        omega
      have d6560 : (x 8 6).toNat = 1 := by
        have r6561 := hand2 (x 8 1) (x 8 6)
        have b6562 := hb (x 8 6)
        have b6563 := hb (x 8 1 && x 8 6)
        clear * - r6561 b6562 b6563 d6547
        omega
      have r6564 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6565 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e6566 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e6567 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e6568 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e6569 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e6570 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b6571 := hb (x 7 7)
      have b6572 := hb (x 8 6)
      have b6573 := hb (x 9 5)
      have b6574 := hb (x 10 4)
      have b6575 := hb (x 11 11)
      have b6576 := hb (x 12 10)
      have b6577 := hb (x 13 9)
      have b6578 := hb (x 14 8)
      linarith only [r6564, e6565, e6566, e6567, e6568, e6569, e6570, b6571, b6572, b6573, b6574, b6575, b6576, b6577, b6578, d6490, d6506, d5737, d5753, d6543, d6560, d6486]
  · have f6579 : (x 1 6).toNat = 1 := by rw [h1354]; rfl
    have d6580 : (x 7 8).toNat = 0 := by
      have r6581 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6582 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e6583 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e6584 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e6585 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e6586 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e6587 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b6588 := hb (x 0 7)
      have b6589 := hb (x 1 6)
      have b6590 := hb (x 2 5)
      have b6591 := hb (x 3 4)
      have b6592 := hb (x 4 11)
      have b6593 := hb (x 5 10)
      have b6594 := hb (x 6 9)
      have b6595 := hb (x 7 8)
      clear * - r6581 e6582 e6583 e6584 e6585 e6586 e6587 b6588 b6589 b6590 b6591 b6592 b6593 b6594 b6595 g52 f6579 g33
      omega
    have d6596 : (x 7 2 && x 7 8).toNat = 0 := by
      have r6597 := hand2 (x 7 2) (x 7 8)
      have b6598 := hb (x 7 8)
      have b6599 := hb (x 7 2 && x 7 8)
      clear * - r6597 b6598 b6599 d6580
      omega
    have d6600 : (x 6 9).toNat = 0 := by
      have r6601 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6602 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e6603 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e6604 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e6605 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e6606 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e6607 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b6608 := hb (x 0 7)
      have b6609 := hb (x 1 6)
      have b6610 := hb (x 2 5)
      have b6611 := hb (x 3 4)
      have b6612 := hb (x 4 11)
      have b6613 := hb (x 5 10)
      have b6614 := hb (x 6 9)
      have b6615 := hb (x 7 8)
      clear * - r6601 e6602 e6603 e6604 e6605 e6606 e6607 b6608 b6609 b6610 b6611 b6612 b6613 b6614 b6615 d6580 g52 f6579 g33
      omega
    have d6616 : (x 6 3 && x 6 9).toNat = 0 := by
      have r6617 := hand2 (x 6 3) (x 6 9)
      have b6618 := hb (x 6 9)
      have b6619 := hb (x 6 3 && x 6 9)
      clear * - r6617 b6618 b6619 d6600
      omega
    have d6620 : (x 5 10).toNat = 0 := by
      have r6621 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6622 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e6623 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e6624 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e6625 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e6626 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e6627 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b6628 := hb (x 0 7)
      have b6629 := hb (x 1 6)
      have b6630 := hb (x 2 5)
      have b6631 := hb (x 3 4)
      have b6632 := hb (x 4 11)
      have b6633 := hb (x 5 10)
      have b6634 := hb (x 6 9)
      have b6635 := hb (x 7 8)
      clear * - r6621 e6622 e6623 e6624 e6625 e6626 e6627 b6628 b6629 b6630 b6631 b6632 b6633 b6634 b6635 d6580 d6600 g52 f6579 g33
      omega
    have d6636 : (x 4 11).toNat = 0 := by
      have r6637 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6638 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e6639 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e6640 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e6641 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e6642 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e6643 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b6644 := hb (x 0 7)
      have b6645 := hb (x 1 6)
      have b6646 := hb (x 2 5)
      have b6647 := hb (x 3 4)
      have b6648 := hb (x 4 11)
      have b6649 := hb (x 5 10)
      have b6650 := hb (x 6 9)
      have b6651 := hb (x 7 8)
      clear * - r6637 e6638 e6639 e6640 e6641 e6642 e6643 b6644 b6645 b6646 b6647 b6648 b6649 b6650 b6651 d6580 d6600 d6620 g52 f6579 g33
      omega
    have d6652 : (x 2 5).toNat = 0 := by
      have r6653 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e6654 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e6655 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e6656 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e6657 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e6658 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e6659 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b6660 := hb (x 0 7)
      have b6661 := hb (x 1 6)
      have b6662 := hb (x 2 5)
      have b6663 := hb (x 3 4)
      have b6664 := hb (x 4 11)
      have b6665 := hb (x 5 10)
      have b6666 := hb (x 6 9)
      have b6667 := hb (x 7 8)
      clear * - r6653 e6654 e6655 e6656 e6657 e6658 e6659 b6660 b6661 b6662 b6663 b6664 b6665 b6666 b6667 d6580 d6600 d6620 d6636 g52 f6579 g33
      omega
    have d6668 : (x 2 5 && x 2 11).toNat = 0 := by
      have r6669 := hand1 (x 2 5) (x 2 11)
      have b6670 := hb (x 2 5)
      have b6671 := hb (x 2 5 && x 2 11)
      clear * - r6669 b6670 b6671 d6652
      omega
    have r6672 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6673 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6674 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
    have e6675 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
    have e6676 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
    have e6677 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
    have e6678 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
    have e6679 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
    have r6680 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6681 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e6682 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e6683 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e6684 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e6685 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e6686 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have r6687 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6688 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e6689 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e6690 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e6691 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e6692 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e6693 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have r6694 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6695 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e6696 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e6697 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e6698 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e6699 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e6700 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have r6701 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6702 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
    have e6703 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
    have r6704 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6705 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := by have q := hcov6 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6706 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6707 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6708 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6709 := hand2 (x 2 3) (x 2 7)
    have r6710 := hand1 (x (-3) 8) (x (-3) 12)
    have r6711 := hand2 (x 6 1) (x 6 7)
    have r6712 := hand1 (x (-1) 8) (x (-1) 14)
    have r6713 := hand2 (x 8 1) (x 8 7)
    have r6714 := hand1 (x 2 7) (x 2 13)
    have r6715 := hand1 (x (-7) 4) (x (-7) 14)
    have r6716 := hand2 (x 6 1) (x 6 11)
    have r6717 := hand1 (x 12 1) (x 12 11)
    have r6718 := hand1 (x 11 2) (x 11 12)
    have r6719 := hand1 (x 10 3) (x 10 13)
    have r6720 := hand1 (x 9 4) (x 9 14)
    linarith only [r6672, r6673, e6674, e6675, e6676, e6677, e6678, e6679, r6680, e6681, e6682, e6683, e6684, e6685, e6686, r6687, e6688, e6689, e6690, e6691, e6692, e6693, r6694, e6695, e6696, e6697, e6698, e6699, e6700, r6701, e6702, e6703, r6704, r6705, r6706, r6707, r6708, r6709, r6710, r6711, r6712, r6713, r6714, r6715, r6716, r6717, r6718, r6719, r6720, g1, g3, g6, g8, g18, g27, g35, g37, g45, d6652, g48, g54, g55, g60, g61, g64, g65, g79, g80, g81, g82, g83, g84, g120, g121, g122, d6668, g123, g124, d6596, d6616, g129, g130, g131, g132, g146, g147, g148, g155, g156, g157]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt0000000000 (x : ℤ → Fin 16 → Bool)
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
    (g5 : (x (-4) 5).toNat = 0)
    (g6 : (x (-4) 9).toNat = 0)
    (g7 : (x (-4) 10).toNat = 0)
    (g8 : (x (-4) 11).toNat = 0)
    (g9 : (x (-4) 13).toNat = 0)
    (g10 : (x (-3) 3).toNat = 1)
    (g11 : (x (-3) 4).toNat = 1)
    (g12 : (x (-3) 12).toNat = 1)
    (g13 : (x (-3) 13).toNat = 1)
    (g14 : (x (-2) 2).toNat = 0)
    (g15 : (x (-2) 3).toNat = 0)
    (g16 : (x (-2) 4).toNat = 0)
    (g17 : (x (-2) 6).toNat = 0)
    (g18 : (x (-2) 9).toNat = 0)
    (g19 : (x (-2) 10).toNat = 0)
    (g20 : (x (-2) 11).toNat = 0)
    (g21 : (x (-2) 12).toNat = 0)
    (g22 : (x (-1) 1).toNat = 1)
    (g23 : (x (-1) 2).toNat = 1)
    (g24 : (x (-1) 3).toNat = 0)
    (g25 : (x (-1) 5).toNat = 0)
    (g26 : (x (-1) 10).toNat = 0)
    (g27 : (x (-1) 14).toNat = 1)
    (g28 : (x 0 1).toNat = 0)
    (g29 : (x 0 2).toNat = 0)
    (g30 : (x 0 4).toNat = 0)
    (g31 : (x 0 5).toNat = 0)
    (g32 : (x 0 6).toNat = 0)
    (g33 : (x 0 7).toNat = 0)
    (g34 : (x 0 8).toNat = 0)
    (g35 : (x 0 9).toNat = 0)
    (g36 : (x 0 10).toNat = 0)
    (g37 : (x 0 13).toNat = 0)
    (g38 : (x 0 14).toNat = 0)
    (g39 : (x 1 3).toNat = 0)
    (g40 : (x 1 4).toNat = 0)
    (g41 : (x 1 5).toNat = 0)
    (g42 : (x 1 8).toNat = 0)
    (g43 : (x 1 9).toNat = 0)
    (g44 : (x 1 11).toNat = 0)
    (g45 : (x 1 12).toNat = 0)
    (g46 : (x 1 13).toNat = 0)
    (g47 : (x 1 14).toNat = 1)
    (g48 : (x 2 11).toNat = 1)
    (g49 : (x 2 13).toNat = 1)
    (g50 : (x 2 14).toNat = 1)
    (g51 : (x 3 2).toNat = 0)
    (g52 : (x 3 4).toNat = 0)
    (g53 : (x 3 5).toNat = 0)
    (g54 : (x 3 6).toNat = 0)
    (g55 : (x 3 10).toNat = 0)
    (g56 : (x 3 12).toNat = 0)
    (g57 : (x 3 13).toNat = 0)
    (g58 : (x 3 14).toNat = 0)
    (g59 : (x 4 4).toNat = 0)
    (g60 : (x 4 5).toNat = 0)
    (g61 : (x 4 9).toNat = 0)
    (g62 : (x 4 12).toNat = 0)
    (g63 : (x 4 13).toNat = 0)
    (g64 : (x 5 4).toNat = 0)
    (g65 : (x 5 8).toNat = 0)
    (g66 : (x 5 12).toNat = 0)
    (g67 : (x 0 1 && x 0 4).toNat = 0)
    (g68 : (x (-1) 2 && x (-1) 5).toNat = 0)
    (g69 : (x (-2) 3 && x (-2) 6).toNat = 0)
    (g70 : (x (-4) 5 && x (-4) 8).toNat = 0)
    (g71 : (x (-5) 6 && x (-5) 9).toNat = 0)
    (g72 : (x (-6) 7 && x (-6) 10).toNat = 0)
    (g73 : (x (-2) 2 && x (-2) 6).toNat = 0)
    (g74 : (x (-1) 2 && x (-1) 6).toNat = 0)
    (g75 : (x (-2) 3 && x (-2) 7).toNat = 0)
    (g76 : (x (-4) 5 && x (-4) 9).toNat = 0)
    (g77 : (x (-5) 6 && x (-5) 10).toNat = 0)
    (g78 : (x (-6) 7 && x (-6) 11).toNat = 0)
    (g79 : (x 3 2 && x 3 6).toNat = 0)
    (g80 : (x 1 4 && x 1 8).toNat = 0)
    (g81 : (x 0 5 && x 0 9).toNat = 0)
    (g82 : (x (-1) 6 && x (-1) 10).toNat = 0)
    (g83 : (x (-2) 7 && x (-2) 11).toNat = 0)
    (g84 : (x (-4) 9 && x (-4) 13).toNat = 0)
    (g85 : (x 5 4 && x 5 8).toNat = 0)
    (g86 : (x 4 5 && x 4 9).toNat = 0)
    (g87 : (x 3 6 && x 3 10).toNat = 0)
    (g88 : (x 1 8 && x 1 12).toNat = 0)
    (g89 : (x 0 9 && x 0 13).toNat = 0)
    (g90 : (x 4 8 && x 4 12).toNat = 0)
    (g91 : (x 3 9 && x 3 13).toNat = 0)
    (g92 : (x (-1) 1 && x (-1) 6).toNat = 0)
    (g93 : (x (-2) 2 && x (-2) 7).toNat = 0)
    (g94 : (x (-4) 4 && x (-4) 9).toNat = 0)
    (g95 : (x (-5) 5 && x (-5) 10).toNat = 0)
    (g96 : (x (-6) 6 && x (-6) 11).toNat = 0)
    (g97 : (x 0 1 && x 0 6).toNat = 0)
    (g98 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g99 : (x (-4) 5 && x (-4) 10).toNat = 0)
    (g100 : (x (-5) 6 && x (-5) 11).toNat = 0)
    (g101 : (x (-6) 7 && x (-6) 12).toNat = 0)
    (g102 : (x 5 3 && x 5 8).toNat = 0)
    (g103 : (x 4 4 && x 4 9).toNat = 0)
    (g104 : (x 3 5 && x 3 10).toNat = 0)
    (g105 : (x 1 7 && x 1 12).toNat = 0)
    (g106 : (x 0 8 && x 0 13).toNat = 0)
    (g107 : (x 5 4 && x 5 9).toNat = 0)
    (g108 : (x 4 5 && x 4 10).toNat = 0)
    (g109 : (x 3 6 && x 3 11).toNat = 0)
    (g110 : (x 1 8 && x 1 13).toNat = 0)
    (g111 : (x 0 9 && x 0 14).toNat = 0)
    (g112 : (x 3 7 && x 3 12).toNat = 0)
    (g113 : (x 1 9 && x 1 14).toNat = 0)
    (g114 : (x 5 7 && x 5 12).toNat = 0)
    (g115 : (x 4 8 && x 4 13).toNat = 0)
    (g116 : (x 3 9 && x 3 14).toNat = 0)
    (g117 : (x (-2) 2 && x (-2) 8).toNat = 0)
    (g118 : (x (-4) 4 && x (-4) 10).toNat = 0)
    (g119 : (x (-5) 5 && x (-5) 11).toNat = 0)
    (g120 : (x 5 2 && x 5 8).toNat = 0)
    (g121 : (x 4 3 && x 4 9).toNat = 0)
    (g122 : (x 3 4 && x 3 10).toNat = 0)
    (g123 : (x 1 6 && x 1 12).toNat = 0)
    (g124 : (x 0 7 && x 0 13).toNat = 0)
    (g125 : (x 4 4 && x 4 10).toNat = 0)
    (g126 : (x 3 5 && x 3 11).toNat = 0)
    (g127 : (x 1 7 && x 1 13).toNat = 0)
    (g128 : (x 0 8 && x 0 14).toNat = 0)
    (g129 : (x 5 4 && x 5 10).toNat = 0)
    (g130 : (x 4 5 && x 4 11).toNat = 0)
    (g131 : (x 3 6 && x 3 12).toNat = 0)
    (g132 : (x 1 8 && x 1 14).toNat = 0)
    (g133 : (x 4 6 && x 4 12).toNat = 0)
    (g134 : (x 3 7 && x 3 13).toNat = 0)
    (g135 : (x 4 4 && x 4 11).toNat = 0)
    (g136 : (x 3 5 && x 3 12).toNat = 0)
    (g137 : (x 5 4 && x 5 11).toNat = 0)
    (g138 : (x 4 5 && x 4 12).toNat = 0)
    (g139 : (x 3 6 && x 3 13).toNat = 0)
    (g140 : (x 5 5 && x 5 12).toNat = 0)
    (g141 : (x 4 6 && x 4 13).toNat = 0)
    (g142 : (x 3 7 && x 3 14).toNat = 0)
    (g143 : (x 5 3 && x 5 12).toNat = 0)
    (g144 : (x 4 4 && x 4 13).toNat = 0)
    (g145 : (x 3 5 && x 3 14).toNat = 0)
    (g146 : (x (-4) 1 && x (-4) 11).toNat = 0)
    (g147 : (x (-5) 2 && x (-5) 12).toNat = 0)
    (g148 : (x (-6) 3 && x (-6) 13).toNat = 0)
    (g149 : (x (-4) 2 && x (-4) 12).toNat = 0)
    (g150 : (x (-5) 3 && x (-5) 13).toNat = 0)
    (g151 : (x 1 1 && x 1 11).toNat = 0)
    (g152 : (x 0 2 && x 0 12).toNat = 0)
    (g153 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g154 : (x (-2) 4 && x (-2) 14).toNat = 0)
    (g155 : (x 5 2 && x 5 12).toNat = 0)
    (g156 : (x 4 3 && x 4 13).toNat = 0)
    (g157 : (x 3 4 && x 3 14).toNat = 0)
    (g158 : (x 5 4 && x 5 14).toNat = 0)
    (g159 : (x (-4) 1 && x (-4) 12).toNat = 0)
    (g160 : (x (-5) 2 && x (-5) 13).toNat = 0)
    (g161 : (x (-6) 3 && x (-6) 14).toNat = 0)
    (g162 : (x 5 1 && x 5 12).toNat = 0)
    (g163 : (x 4 2 && x 4 13).toNat = 0)
    (g164 : (x 3 3 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt0000000000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125 g126 g127 g128 g129 g130 g131 g132 g133 g134 g135 g136 g137 g138 g139 g140 g141 g142 g143 g144 g145 g146 g147 g148 g149 g150 g151 g152 g153 g154 g155 g156 g157 g158 g159 g160 g161 g162 g163 g164
