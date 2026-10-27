import AFTD.Prelude

/-!
# cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a11000100

Topic: combinatorics   Node: e3fd01a9792a

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_four_iff_five_core: under the layer-free tight-cover constraints for k = 15 and 126 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a11000100_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 7).toNat = 0)
    (g1 : (x (-3) 6).toNat = 0)
    (g2 : (x (-3) 7).toNat = 0)
    (g3 : (x (-3) 11).toNat = 0)
    (g4 : (x (-2) 5).toNat = 0)
    (g5 : (x (-2) 6).toNat = 0)
    (g6 : (x (-2) 10).toNat = 0)
    (g7 : (x (-2) 11).toNat = 0)
    (g8 : (x (-1) 4).toNat = 0)
    (g9 : (x (-1) 5).toNat = 0)
    (g10 : (x (-1) 9).toNat = 0)
    (g11 : (x (-1) 10).toNat = 0)
    (g12 : (x (-1) 11).toNat = 0)
    (g13 : (x (-1) 13).toNat = 0)
    (g14 : (x 0 3).toNat = 1)
    (g15 : (x 0 4).toNat = 1)
    (g16 : (x 0 5).toNat = 0)
    (g17 : (x 0 6).toNat = 0)
    (g18 : (x 0 7).toNat = 0)
    (g19 : (x 0 8).toNat = 0)
    (g20 : (x 0 11).toNat = 1)
    (g21 : (x 0 13).toNat = 1)
    (g22 : (x 1 2).toNat = 0)
    (g23 : (x 1 3).toNat = 0)
    (g24 : (x 1 4).toNat = 0)
    (g25 : (x 1 5).toNat = 0)
    (g26 : (x 1 6).toNat = 0)
    (g27 : (x 1 10).toNat = 0)
    (g28 : (x 1 11).toNat = 0)
    (g29 : (x 1 12).toNat = 0)
    (g30 : (x 2 4).toNat = 0)
    (g31 : (x 2 5).toNat = 0)
    (g32 : (x 2 9).toNat = 0)
    (g33 : (x 2 10).toNat = 0)
    (g34 : (x 2 14).toNat = 1)
    (g35 : (x 3 4).toNat = 0)
    (g36 : (x 3 8).toNat = 0)
    (g37 : (x 0 2 && x 0 6).toNat = 0)
    (g38 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g39 : (x (-2) 4 && x (-2) 8).toNat = 0)
    (g40 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g41 : (x (-4) 6 && x (-4) 10).toNat = 0)
    (g42 : (x (-5) 7 && x (-5) 11).toNat = 0)
    (g43 : (x 1 2 && x 1 6).toNat = 0)
    (g44 : (x 0 3 && x 0 7).toNat = 0)
    (g45 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g46 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g47 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g48 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g49 : (x 0 4 && x 0 8).toNat = 0)
    (g50 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g51 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g52 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g53 : (x 3 4 && x 3 8).toNat = 0)
    (g54 : (x 2 5 && x 2 9).toNat = 0)
    (g55 : (x 1 6 && x 1 10).toNat = 0)
    (g56 : (x 0 7 && x 0 11).toNat = 0)
    (g57 : (x 4 4 && x 4 8).toNat = 0)
    (g58 : (x 3 5 && x 3 9).toNat = 0)
    (g59 : (x 2 6 && x 2 10).toNat = 0)
    (g60 : (x 1 7 && x 1 11).toNat = 0)
    (g61 : (x 0 8 && x 0 12).toNat = 0)
    (g62 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g63 : (x 4 8 && x 4 12).toNat = 0)
    (g64 : (x 3 9 && x 3 13).toNat = 0)
    (g65 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g66 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g67 : (x 0 1 && x 0 6).toNat = 0)
    (g68 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g69 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g70 : (x 1 1 && x 1 6).toNat = 0)
    (g71 : (x 0 2 && x 0 7).toNat = 0)
    (g72 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g73 : (x (-2) 4 && x (-2) 9).toNat = 0)
    (g74 : (x (-3) 5 && x (-3) 10).toNat = 0)
    (g75 : (x (-4) 6 && x (-4) 11).toNat = 0)
    (g76 : (x (-5) 7 && x (-5) 12).toNat = 0)
    (g77 : (x 3 8 && x 3 13).toNat = 0)
    (g78 : (x 2 9 && x 2 14).toNat = 0)
    (g79 : (x 1 1 && x 1 7).toNat = 0)
    (g80 : (x 0 2 && x 0 8).toNat = 0)
    (g81 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g82 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g83 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g84 : (x (-4) 6 && x (-4) 12).toNat = 0)
    (g85 : (x (-5) 7 && x (-5) 13).toNat = 0)
    (g86 : (x 4 2 && x 4 8).toNat = 0)
    (g87 : (x 3 3 && x 3 9).toNat = 0)
    (g88 : (x 2 4 && x 2 10).toNat = 0)
    (g89 : (x 1 5 && x 1 11).toNat = 0)
    (g90 : (x 0 6 && x 0 12).toNat = 0)
    (g91 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g92 : (x 3 4 && x 3 10).toNat = 0)
    (g93 : (x 2 5 && x 2 11).toNat = 0)
    (g94 : (x 1 6 && x 1 12).toNat = 0)
    (g95 : (x 0 7 && x 0 13).toNat = 0)
    (g96 : (x 0 1 && x 0 8).toNat = 0)
    (g97 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g98 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g99 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g100 : (x 1 1 && x 1 8).toNat = 0)
    (g101 : (x (-1) 3 && x (-1) 10).toNat = 0)
    (g102 : (x (-2) 4 && x (-2) 11).toNat = 0)
    (g103 : (x (-3) 5 && x (-3) 12).toNat = 0)
    (g104 : (x (-4) 6 && x (-4) 13).toNat = 0)
    (g105 : (x (-5) 7 && x (-5) 14).toNat = 0)
    (g106 : (x 3 5 && x 3 12).toNat = 0)
    (g107 : (x 2 6 && x 2 13).toNat = 0)
    (g108 : (x 1 7 && x 1 14).toNat = 0)
    (g109 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g110 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g111 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g112 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g113 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g114 : (x 2 3 && x 2 12).toNat = 0)
    (g115 : (x 1 4 && x 1 13).toNat = 0)
    (g116 : (x 0 5 && x 0 14).toNat = 0)
    (g117 : (x 3 4 && x 3 13).toNat = 0)
    (g118 : (x 2 5 && x 2 14).toNat = 0)
    (g119 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g120 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g121 : (x 3 2 && x 3 12).toNat = 0)
    (g122 : (x 2 3 && x 2 13).toNat = 0)
    (g123 : (x 1 4 && x 1 14).toNat = 0)
    (g124 : (x 2 4 && x 2 14).toNat = 0)
    (g125 : (x 3 4 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d27600 : (x 1 3 && x 1 7).toNat = 0 := by
    have r27601 := hand1 (x 1 3) (x 1 7)
    have b27602 := hb (x 1 3)
    have b27603 := hb (x 1 3 && x 1 7)
    clear * - r27601 b27602 b27603 g23
    omega
  cases h27604 : x 1 7
  · have f27605 : (x 1 7).toNat = 0 := by rw [h27604]; rfl
    cases h27606 : x (-1) 8
    · have f27607 : (x (-1) 8).toNat = 0 := by rw [h27606]; rfl
      have d27608 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
        have r27609 := hand1 (x (-1) 8) (x (-1) 14)
        have b27610 := hb (x (-1) 8)
        have b27611 := hb (x (-1) 8 && x (-1) 14)
        clear * - r27609 b27610 b27611 f27607
        omega
      have d27612 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
        have r27613 := hand1 (x (-1) 8) (x (-1) 12)
        have b27614 := hb (x (-1) 8)
        have b27615 := hb (x (-1) 8 && x (-1) 12)
        clear * - r27613 b27614 b27615 f27607
        omega
      cases h27616 : x (-1) 12
      · have f27617 : (x (-1) 12).toNat = 0 := by rw [h27616]; rfl
        cases h27618 : x 2 1
        · have f27619 : (x 2 1).toNat = 0 := by rw [h27618]; rfl
          have d27620 : (x 2 1 && x 2 14).toNat = 0 := by
            have r27621 := hand1 (x 2 1) (x 2 14)
            have b27622 := hb (x 2 1)
            have b27623 := hb (x 2 1 && x 2 14)
            clear * - r27621 b27622 b27623 f27619
            omega
          have d27624 : (x 3 13).toNat = 1 := by
            have r27625 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b27626 := hb (x 1 2)
            have b27627 := hb (x 3 13)
            have b27628 := hb (x 2 1 && x 2 14)
            clear * - r27625 b27626 b27627 b27628 d27620 g22
            omega
          have d27629 : (x 3 1).toNat = 1 := by
            have r27630 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
            have b27631 := hb (x 3 1)
            have b27632 := hb (x 3 13)
            clear * - r27630 b27631 b27632 d27624
            omega
          have d27633 : (x 4 14).toNat = 0 := by
            have r27634 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b27635 := hb (x 3 1)
            have b27636 := hb (x 4 14)
            clear * - r27634 b27635 b27636 d27629
            omega
          have d27637 : (x 4 1 && x 4 14).toNat = 0 := by
            have r27638 := hand2 (x 4 1) (x 4 14)
            have b27639 := hb (x 4 14)
            have b27640 := hb (x 4 1 && x 4 14)
            clear * - r27638 b27639 b27640 d27633
            omega
          have d27641 : (x 4 2).toNat = 0 := by
            have r27642 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
            have b27643 := hb (x 4 2)
            have b27644 := hb (x 4 14)
            clear * - r27642 b27643 b27644 d27633
            omega
          have d27645 : (x 4 2 && x 4 13).toNat = 0 := by
            have r27646 := hand1 (x 4 2) (x 4 13)
            have b27647 := hb (x 4 2)
            have b27648 := hb (x 4 2 && x 4 13)
            clear * - r27646 b27647 b27648 d27641
            omega
          have d27649 : (x 4 10).toNat = 0 := by
            have r27650 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
            have b27651 := hb (x 4 2)
            have b27652 := hb (x 4 10)
            clear * - r27650 b27651 b27652 d27641
            omega
          have d27653 : (x 4 1 && x 4 10).toNat = 0 := by
            have r27654 := hand2 (x 4 1) (x 4 10)
            have b27655 := hb (x 4 10)
            have b27656 := hb (x 4 1 && x 4 10)
            clear * - r27654 b27655 b27656 d27649
            omega
          have d27657 : (x 4 12).toNat = 0 := by
            have r27658 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e27659 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e27660 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b27661 := hb (x 1 3)
            have b27662 := hb (x 2 2)
            have b27663 := hb (x 3 13)
            have b27664 := hb (x 4 12)
            clear * - r27658 e27659 e27660 b27661 b27662 b27663 b27664 d27624 g23
            omega
          have d27665 : (x 4 3 && x 4 12).toNat = 0 := by
            have r27666 := hand2 (x 4 3) (x 4 12)
            have b27667 := hb (x 4 12)
            have b27668 := hb (x 4 3 && x 4 12)
            clear * - r27666 b27667 b27668 d27657
            omega
          have d27669 : (x 4 7 && x 4 12).toNat = 0 := by
            have r27670 := hand2 (x 4 7) (x 4 12)
            have b27671 := hb (x 4 12)
            have b27672 := hb (x 4 7 && x 4 12)
            clear * - r27670 b27671 b27672 d27657
            omega
          have d27673 : (x 4 4).toNat = 0 := by
            have r27674 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
            have b27675 := hb (x 4 4)
            have b27676 := hb (x 4 12)
            clear * - r27674 b27675 b27676 d27657
            omega
          have d27677 : (x 2 2).toNat = 0 := by
            have r27678 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e27679 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e27680 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b27681 := hb (x 1 3)
            have b27682 := hb (x 2 2)
            have b27683 := hb (x 3 13)
            have b27684 := hb (x 4 12)
            clear * - r27678 e27679 e27680 b27681 b27682 b27683 b27684 d27657 d27624 g23
            omega
          cases h27685 : x 0 9
          · have f27686 : (x 0 9).toNat = 0 := by rw [h27685]; rfl
            have d27687 : (x 0 2 && x 0 9).toNat = 0 := by
              have r27688 := hand2 (x 0 2) (x 0 9)
              have b27689 := hb (x 0 9)
              have b27690 := hb (x 0 2 && x 0 9)
              clear * - r27688 b27689 b27690 f27686
              omega
            cases h27691 : x (-1) 6
            · have f27692 : (x (-1) 6).toNat = 0 := by rw [h27691]; rfl
              cases h27693 : x (-1) 7
              · have f27694 : (x (-1) 7).toNat = 0 := by rw [h27693]; rfl
                cases h27695 : x 1 8
                · have f27696 : (x 1 8).toNat = 0 := by rw [h27695]; rfl
                  cases h27697 : x (-1) 14
                  · have f27698 : (x (-1) 14).toNat = 0 := by rw [h27697]; rfl
                    cases h27699 : x 2 3
                    · have f27700 : (x 2 3).toNat = 0 := by rw [h27699]; rfl
                      cases h27701 : x 2 6
                      · have f27702 : (x 2 6).toNat = 0 := by rw [h27701]; rfl
                        cases h27703 : x 2 7
                        · have f27704 : (x 2 7).toNat = 0 := by rw [h27703]; rfl
                          have d27705 : (x (-6) 8).toNat = 1 := by
                            have r27706 : 1 ≤ (x 2 7).toNat + (x 1 1 && x 1 8).toNat + (x 0 2 && x 0 9).toNat + (x (-1) 3 && x (-1) 10).toNat + (x (-2) 4 && x (-2) 11).toNat + (x (-3) 5 && x (-3) 12).toNat + (x (-4) 6 && x (-4) 13).toNat + (x (-5) 7 && x (-5) 14).toNat + (x (-6) 8).toNat := by have q := hcov7 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b27707 := hb (x (-6) 8)
                            have b27708 := hb (x 2 7)
                            have b27709 := hb (x 1 1 && x 1 8)
                            have b27710 := hb (x 0 2 && x 0 9)
                            have b27711 := hb (x (-1) 3 && x (-1) 10)
                            have b27712 := hb (x (-2) 4 && x (-2) 11)
                            have b27713 := hb (x (-3) 5 && x (-3) 12)
                            have b27714 := hb (x (-4) 6 && x (-4) 13)
                            have b27715 := hb (x (-5) 7 && x (-5) 14)
                            clear * - r27706 b27707 b27708 b27709 b27710 b27711 b27712 b27713 b27714 b27715 f27704 g100 d27687 g101 g102 g103 g104 g105
                            omega
                          have d27716 : (x (-7) 9).toNat = 0 := by
                            have r27717 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27718 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                            have e27719 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                            have e27720 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                            have e27721 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                            have e27722 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                            have e27723 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                            have b27724 := hb (x (-13) 7)
                            have b27725 := hb (x (-12) 6)
                            have b27726 := hb (x (-11) 5)
                            have b27727 := hb (x (-10) 4)
                            have b27728 := hb (x (-9) 11)
                            have b27729 := hb (x (-8) 10)
                            have b27730 := hb (x (-7) 9)
                            have b27731 := hb (x (-6) 8)
                            clear * - r27717 e27718 e27719 e27720 e27721 e27722 e27723 b27724 b27725 b27726 b27727 b27728 b27729 b27730 b27731 d27705
                            omega
                          have d27732 : (x (-7) 9 && x (-7) 14).toNat = 0 := by
                            have r27733 := hand1 (x (-7) 9) (x (-7) 14)
                            have b27734 := hb (x (-7) 9)
                            have b27735 := hb (x (-7) 9 && x (-7) 14)
                            clear * - r27733 b27734 b27735 d27716
                            omega
                          have d27736 : (x (-8) 10).toNat = 0 := by
                            have r27737 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27738 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                            have e27739 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                            have e27740 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                            have e27741 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                            have e27742 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                            have e27743 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                            have b27744 := hb (x (-13) 7)
                            have b27745 := hb (x (-12) 6)
                            have b27746 := hb (x (-11) 5)
                            have b27747 := hb (x (-10) 4)
                            have b27748 := hb (x (-9) 11)
                            have b27749 := hb (x (-8) 10)
                            have b27750 := hb (x (-7) 9)
                            have b27751 := hb (x (-6) 8)
                            clear * - r27737 e27738 e27739 e27740 e27741 e27742 e27743 b27744 b27745 b27746 b27747 b27748 b27749 b27750 b27751 d27705 d27716
                            omega
                          have d27752 : (x (-9) 11).toNat = 0 := by
                            have r27753 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27754 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                            have e27755 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                            have e27756 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                            have e27757 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                            have e27758 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                            have e27759 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                            have b27760 := hb (x (-13) 7)
                            have b27761 := hb (x (-12) 6)
                            have b27762 := hb (x (-11) 5)
                            have b27763 := hb (x (-10) 4)
                            have b27764 := hb (x (-9) 11)
                            have b27765 := hb (x (-8) 10)
                            have b27766 := hb (x (-7) 9)
                            have b27767 := hb (x (-6) 8)
                            clear * - r27753 e27754 e27755 e27756 e27757 e27758 e27759 b27760 b27761 b27762 b27763 b27764 b27765 b27766 b27767 d27705 d27716 d27736
                            omega
                          have d27768 : (x (-10) 4).toNat = 0 := by
                            have r27769 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27770 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                            have e27771 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                            have e27772 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                            have e27773 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                            have e27774 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                            have e27775 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                            have b27776 := hb (x (-13) 7)
                            have b27777 := hb (x (-12) 6)
                            have b27778 := hb (x (-11) 5)
                            have b27779 := hb (x (-10) 4)
                            have b27780 := hb (x (-9) 11)
                            have b27781 := hb (x (-8) 10)
                            have b27782 := hb (x (-7) 9)
                            have b27783 := hb (x (-6) 8)
                            clear * - r27769 e27770 e27771 e27772 e27773 e27774 e27775 b27776 b27777 b27778 b27779 b27780 b27781 b27782 b27783 d27705 d27716 d27736 d27752
                            omega
                          have d27784 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
                            have r27785 := hand1 (x (-10) 4) (x (-10) 14)
                            have b27786 := hb (x (-10) 4)
                            have b27787 := hb (x (-10) 4 && x (-10) 14)
                            clear * - r27785 b27786 b27787 d27768
                            omega
                          have d27788 : (x (-11) 5).toNat = 0 := by
                            have r27789 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27790 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                            have e27791 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                            have e27792 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                            have e27793 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                            have e27794 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                            have e27795 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                            have b27796 := hb (x (-13) 7)
                            have b27797 := hb (x (-12) 6)
                            have b27798 := hb (x (-11) 5)
                            have b27799 := hb (x (-10) 4)
                            have b27800 := hb (x (-9) 11)
                            have b27801 := hb (x (-8) 10)
                            have b27802 := hb (x (-7) 9)
                            have b27803 := hb (x (-6) 8)
                            clear * - r27789 e27790 e27791 e27792 e27793 e27794 e27795 b27796 b27797 b27798 b27799 b27800 b27801 b27802 b27803 d27705 d27716 d27736 d27752 d27768
                            omega
                          have d27804 : (x (-6) 8 && x (-6) 14).toNat = 1 := by
                            have r27805 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b27806 := hb (x (-7) 9)
                            have b27807 := hb (x 2 6)
                            have b27808 := hb (x 1 1 && x 1 7)
                            have b27809 := hb (x 0 2 && x 0 8)
                            have b27810 := hb (x (-1) 3 && x (-1) 9)
                            have b27811 := hb (x (-2) 4 && x (-2) 10)
                            have b27812 := hb (x (-3) 5 && x (-3) 11)
                            have b27813 := hb (x (-4) 6 && x (-4) 12)
                            have b27814 := hb (x (-5) 7 && x (-5) 13)
                            have b27815 := hb (x (-6) 8 && x (-6) 14)
                            clear * - r27805 b27806 b27807 b27808 b27809 b27810 b27811 b27812 b27813 b27814 b27815 f27702 g79 g80 g81 g82 g83 g84 g85 d27716
                            omega
                          have d27816 : (x (-6) 14).toNat = 1 := by
                            have r27817 := hand2 (x (-6) 8) (x (-6) 14)
                            have b27818 := hb (x (-6) 14)
                            have b27819 := hb (x (-6) 8 && x (-6) 14)
                            clear * - r27817 b27818 b27819 d27804
                            omega
                          have d27820 : (x (-7) 1).toNat = 0 := by
                            have r27821 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b27822 := hb (x (-7) 1)
                            have b27823 := hb (x (-6) 14)
                            clear * - r27821 b27822 b27823 d27816
                            omega
                          have d27824 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
                            have r27825 := hand1 (x (-7) 1) (x (-7) 11)
                            have b27826 := hb (x (-7) 1)
                            have b27827 := hb (x (-7) 1 && x (-7) 11)
                            clear * - r27825 b27826 b27827 d27820
                            omega
                          have d27828 : (x (-7) 13).toNat = 0 := by
                            have r27829 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
                            have b27830 := hb (x (-7) 1)
                            have b27831 := hb (x (-7) 13)
                            clear * - r27829 b27830 b27831 d27820
                            omega
                          have d27832 : (x (-7) 5).toNat = 0 := by
                            have r27833 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
                            have b27834 := hb (x (-7) 5)
                            have b27835 := hb (x (-7) 13)
                            clear * - r27833 b27834 b27835 d27828
                            omega
                          have d27836 : (x (-6) 8 && x (-6) 13).toNat = 1 := by
                            have r27837 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b27838 := hb (x (-8) 10)
                            have b27839 := hb (x 2 5)
                            have b27840 := hb (x 1 1 && x 1 6)
                            have b27841 := hb (x 0 2 && x 0 7)
                            have b27842 := hb (x (-1) 3 && x (-1) 8)
                            have b27843 := hb (x (-2) 4 && x (-2) 9)
                            have b27844 := hb (x (-3) 5 && x (-3) 10)
                            have b27845 := hb (x (-4) 6 && x (-4) 11)
                            have b27846 := hb (x (-5) 7 && x (-5) 12)
                            have b27847 := hb (x (-6) 8 && x (-6) 13)
                            have b27848 := hb (x (-7) 9 && x (-7) 14)
                            clear * - r27837 b27838 b27839 b27840 b27841 b27842 b27843 b27844 b27845 b27846 b27847 b27848 g31 g70 g71 g72 g73 g74 g75 g76 d27732 d27736
                            omega
                          have d27849 : (x (-6) 13).toNat = 1 := by
                            have r27850 := hand2 (x (-6) 8) (x (-6) 13)
                            have b27851 := hb (x (-6) 13)
                            have b27852 := hb (x (-6) 8 && x (-6) 13)
                            clear * - r27850 b27851 b27852 d27836
                            omega
                          have d27853 : (x (-6) 1).toNat = 1 := by
                            have r27854 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
                            have b27855 := hb (x (-6) 1)
                            have b27856 := hb (x (-6) 13)
                            clear * - r27854 b27855 b27856 d27849
                            omega
                          have d27857 : (x (-5) 14).toNat = 0 := by
                            have r27858 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b27859 := hb (x (-6) 1)
                            have b27860 := hb (x (-5) 14)
                            clear * - r27858 b27859 b27860 d27853
                            omega
                          have d27861 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
                            have r27862 := hand2 (x (-5) 3) (x (-5) 14)
                            have b27863 := hb (x (-5) 14)
                            have b27864 := hb (x (-5) 3 && x (-5) 14)
                            clear * - r27862 b27863 b27864 d27857
                            omega
                          have d27865 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                            have r27866 := hand2 (x (-5) 4) (x (-5) 14)
                            have b27867 := hb (x (-5) 14)
                            have b27868 := hb (x (-5) 4 && x (-5) 14)
                            clear * - r27866 b27867 b27868 d27857
                            omega
                          have d27869 : (x (-5) 2).toNat = 0 := by
                            have r27870 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
                            have b27871 := hb (x (-5) 2)
                            have b27872 := hb (x (-5) 14)
                            clear * - r27870 b27871 b27872 d27857
                            omega
                          have d27873 : (x (-5) 10).toNat = 0 := by
                            have r27874 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
                            have b27875 := hb (x (-5) 2)
                            have b27876 := hb (x (-5) 10)
                            clear * - r27874 b27875 b27876 d27869
                            omega
                          have d27877 : (x (-5) 12).toNat = 0 := by
                            have r27878 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27879 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                            have e27880 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                            have b27881 := hb (x (-8) 3)
                            have b27882 := hb (x (-7) 2)
                            have b27883 := hb (x (-6) 13)
                            have b27884 := hb (x (-5) 12)
                            clear * - r27878 e27879 e27880 b27881 b27882 b27883 b27884 d27849
                            omega
                          have d27885 : (x (-5) 8 && x (-5) 12).toNat = 0 := by
                            have r27886 := hand2 (x (-5) 8) (x (-5) 12)
                            have b27887 := hb (x (-5) 12)
                            have b27888 := hb (x (-5) 8 && x (-5) 12)
                            clear * - r27886 b27887 b27888 d27877
                            omega
                          have d27889 : (x (-5) 4).toNat = 0 := by
                            have r27890 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                            have b27891 := hb (x (-5) 4)
                            have b27892 := hb (x (-5) 12)
                            clear * - r27890 b27891 b27892 d27877
                            omega
                          have d27893 : (x (-7) 2).toNat = 0 := by
                            have r27894 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27895 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                            have e27896 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                            have b27897 := hb (x (-8) 3)
                            have b27898 := hb (x (-7) 2)
                            have b27899 := hb (x (-6) 13)
                            have b27900 := hb (x (-5) 12)
                            clear * - r27894 e27895 e27896 b27897 b27898 b27899 b27900 d27877 d27849
                            omega
                          have d27901 : (x (-7) 2 && x (-7) 12).toNat = 0 := by
                            have r27902 := hand1 (x (-7) 2) (x (-7) 12)
                            have b27903 := hb (x (-7) 2)
                            have b27904 := hb (x (-7) 2 && x (-7) 12)
                            clear * - r27902 b27903 b27904 d27893
                            omega
                          have d27905 : (x (-7) 10).toNat = 0 := by
                            have r27906 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
                            have b27907 := hb (x (-7) 2)
                            have b27908 := hb (x (-7) 10)
                            clear * - r27906 b27907 b27908 d27893
                            omega
                          have d27909 : (x (-8) 3).toNat = 0 := by
                            have r27910 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27911 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                            have e27912 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                            have b27913 := hb (x (-8) 3)
                            have b27914 := hb (x (-7) 2)
                            have b27915 := hb (x (-6) 13)
                            have b27916 := hb (x (-5) 12)
                            clear * - r27910 e27911 e27912 b27913 b27914 b27915 b27916 d27877 d27849 d27893
                            omega
                          have d27917 : (x (-8) 3 && x (-8) 13).toNat = 0 := by
                            have r27918 := hand1 (x (-8) 3) (x (-8) 13)
                            have b27919 := hb (x (-8) 3)
                            have b27920 := hb (x (-8) 3 && x (-8) 13)
                            clear * - r27918 b27919 b27920 d27909
                            omega
                          have d27921 : (x (-8) 11).toNat = 0 := by
                            have r27922 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
                            have b27923 := hb (x (-8) 3)
                            have b27924 := hb (x (-8) 11)
                            clear * - r27922 b27923 b27924 d27909
                            omega
                          have d27925 : (x (-6) 9 && x (-6) 13).toNat = 1 := by
                            have r27926 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27927 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                            have e27928 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                            have b27929 := hb (x (-8) 11)
                            have b27930 := hb (x (-7) 10)
                            have b27931 := hb (x 2 5)
                            have b27932 := hb (x 3 4)
                            have b27933 := hb (x 1 2 && x 1 6)
                            have b27934 := hb (x 0 3 && x 0 7)
                            have b27935 := hb (x (-1) 4 && x (-1) 8)
                            have b27936 := hb (x (-2) 5 && x (-2) 9)
                            have b27937 := hb (x (-3) 6 && x (-3) 10)
                            have b27938 := hb (x (-4) 7 && x (-4) 11)
                            have b27939 := hb (x (-5) 8 && x (-5) 12)
                            have b27940 := hb (x (-6) 9 && x (-6) 13)
                            clear * - r27926 e27927 e27928 b27929 b27930 b27931 b27932 b27933 b27934 b27935 b27936 b27937 b27938 b27939 b27940 g35 g31 g43 g44 g45 g46 g47 g48 d27885 d27905 d27921
                            omega
                          have d27941 : (x (-6) 9).toNat = 1 := by
                            have r27942 := hand1 (x (-6) 9) (x (-6) 13)
                            have b27943 := hb (x (-6) 9)
                            have b27944 := hb (x (-6) 9 && x (-6) 13)
                            clear * - r27942 b27943 b27944 d27925
                            omega
                          have d27945 : (x (-5) 8).toNat = 0 := by
                            have r27946 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27947 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
                            have e27948 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
                            have e27949 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
                            have e27950 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
                            have e27951 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
                            have e27952 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
                            have b27953 := hb (x (-12) 7)
                            have b27954 := hb (x (-11) 6)
                            have b27955 := hb (x (-10) 5)
                            have b27956 := hb (x (-9) 4)
                            have b27957 := hb (x (-8) 11)
                            have b27958 := hb (x (-7) 10)
                            have b27959 := hb (x (-6) 9)
                            have b27960 := hb (x (-5) 8)
                            clear * - r27946 e27947 e27948 e27949 e27950 e27951 e27952 b27953 b27954 b27955 b27956 b27957 b27958 b27959 b27960 d27941 d27905 d27921
                            omega
                          have d27961 : (x (-9) 4).toNat = 0 := by
                            have r27962 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27963 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
                            have e27964 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
                            have e27965 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
                            have e27966 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
                            have e27967 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
                            have e27968 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
                            have b27969 := hb (x (-12) 7)
                            have b27970 := hb (x (-11) 6)
                            have b27971 := hb (x (-10) 5)
                            have b27972 := hb (x (-9) 4)
                            have b27973 := hb (x (-8) 11)
                            have b27974 := hb (x (-7) 10)
                            have b27975 := hb (x (-6) 9)
                            have b27976 := hb (x (-5) 8)
                            clear * - r27962 e27963 e27964 e27965 e27966 e27967 e27968 b27969 b27970 b27971 b27972 b27973 b27974 b27975 b27976 d27945 d27941 d27905 d27921
                            omega
                          have d27977 : (x (-9) 4 && x (-9) 14).toNat = 0 := by
                            have r27978 := hand1 (x (-9) 4) (x (-9) 14)
                            have b27979 := hb (x (-9) 4)
                            have b27980 := hb (x (-9) 4 && x (-9) 14)
                            clear * - r27978 b27979 b27980 d27961
                            omega
                          have d27981 : (x (-10) 5).toNat = 0 := by
                            have r27982 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e27983 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
                            have e27984 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
                            have e27985 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
                            have e27986 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
                            have e27987 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
                            have e27988 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
                            have b27989 := hb (x (-12) 7)
                            have b27990 := hb (x (-11) 6)
                            have b27991 := hb (x (-10) 5)
                            have b27992 := hb (x (-9) 4)
                            have b27993 := hb (x (-8) 11)
                            have b27994 := hb (x (-7) 10)
                            have b27995 := hb (x (-6) 9)
                            have b27996 := hb (x (-5) 8)
                            clear * - r27982 e27983 e27984 e27985 e27986 e27987 e27988 b27989 b27990 b27991 b27992 b27993 b27994 b27995 b27996 d27945 d27941 d27905 d27921 d27961
                            omega
                          have d27997 : (x (-6) 1 && x (-6) 11).toNat = 1 := by
                            have r27998 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b27999 := hb (x (-10) 5)
                            have b28000 := hb (x (-5) 10)
                            have b28001 := hb (x (-6) 1 && x (-6) 11)
                            have b28002 := hb (x (-7) 2 && x (-7) 12)
                            have b28003 := hb (x (-8) 3 && x (-8) 13)
                            have b28004 := hb (x (-9) 4 && x (-9) 14)
                            clear * - r27998 b27999 b28000 b28001 b28002 b28003 b28004 d27873 d27901 d27917 d27977 d27981
                            omega
                          have d28005 : (x (-6) 11).toNat = 1 := by
                            have r28006 := hand2 (x (-6) 1) (x (-6) 11)
                            have b28007 := hb (x (-6) 11)
                            have b28008 := hb (x (-6) 1 && x (-6) 11)
                            clear * - r28006 b28007 b28008 d27997
                            omega
                          have d28009 : (x (-6) 3).toNat = 1 := by
                            have r28010 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
                            have b28011 := hb (x (-6) 3)
                            have b28012 := hb (x (-6) 11)
                            clear * - r28010 b28011 b28012 d28005
                            omega
                          have d28013 : (x (-3) 12).toNat = 0 := by
                            have r28014 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28015 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                            have e28016 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                            have b28017 := hb (x (-6) 3)
                            have b28018 := hb (x (-5) 2)
                            have b28019 := hb (x (-4) 13)
                            have b28020 := hb (x (-3) 12)
                            clear * - r28014 e28015 e28016 b28017 b28018 b28019 b28020 d27869 d28009
                            omega
                          have d28021 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
                            have r28022 := hand2 (x (-3) 1) (x (-3) 12)
                            have b28023 := hb (x (-3) 12)
                            have b28024 := hb (x (-3) 1 && x (-3) 12)
                            clear * - r28022 b28023 b28024 d28013
                            omega
                          have d28025 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                            have r28026 := hand2 (x (-3) 2) (x (-3) 12)
                            have b28027 := hb (x (-3) 12)
                            have b28028 := hb (x (-3) 2 && x (-3) 12)
                            clear * - r28026 b28027 b28028 d28013
                            omega
                          have d28029 : (x (-4) 13).toNat = 0 := by
                            have r28030 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28031 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                            have e28032 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                            have b28033 := hb (x (-6) 3)
                            have b28034 := hb (x (-5) 2)
                            have b28035 := hb (x (-4) 13)
                            have b28036 := hb (x (-3) 12)
                            clear * - r28030 e28031 e28032 b28033 b28034 b28035 b28036 d28013 d27869 d28009
                            omega
                          have d28037 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
                            have r28038 := hand2 (x (-4) 2) (x (-4) 13)
                            have b28039 := hb (x (-4) 13)
                            have b28040 := hb (x (-4) 2 && x (-4) 13)
                            clear * - r28038 b28039 b28040 d28029
                            omega
                          have d28041 : (x (-6) 4).toNat = 1 := by
                            have r28042 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b28043 := hb (x (-6) 4)
                            have b28044 := hb (x (-2) 11)
                            have b28045 := hb (x (-3) 1 && x (-3) 12)
                            have b28046 := hb (x (-4) 2 && x (-4) 13)
                            have b28047 := hb (x (-5) 3 && x (-5) 14)
                            clear * - r28042 b28043 b28044 b28045 b28046 b28047 g7 d28021 d28037 d27861
                            omega
                          have d28048 : (x (-6) 12).toNat = 1 := by
                            have r28049 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                            have b28050 := hb (x (-6) 4)
                            have b28051 := hb (x (-6) 12)
                            clear * - r28049 b28050 b28051 d28041
                            omega
                          have d28052 : (x (-8) 2).toNat = 0 := by
                            have r28053 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28054 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                            have e28055 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                            have b28056 := hb (x (-9) 3)
                            have b28057 := hb (x (-8) 2)
                            have b28058 := hb (x (-7) 13)
                            have b28059 := hb (x (-6) 12)
                            clear * - r28053 e28054 e28055 b28056 b28057 b28058 b28059 d28048 d27828
                            omega
                          have d28060 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
                            have r28061 := hand1 (x (-8) 2) (x (-8) 12)
                            have b28062 := hb (x (-8) 2)
                            have b28063 := hb (x (-8) 2 && x (-8) 12)
                            clear * - r28061 b28062 b28063 d28052
                            omega
                          have d28064 : (x (-9) 3).toNat = 0 := by
                            have r28065 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28066 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                            have e28067 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                            have b28068 := hb (x (-9) 3)
                            have b28069 := hb (x (-8) 2)
                            have b28070 := hb (x (-7) 13)
                            have b28071 := hb (x (-6) 12)
                            clear * - r28065 e28066 e28067 b28068 b28069 b28070 b28071 d28048 d27828 d28052
                            omega
                          have d28072 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
                            have r28073 := hand1 (x (-9) 3) (x (-9) 13)
                            have b28074 := hb (x (-9) 3)
                            have b28075 := hb (x (-9) 3 && x (-9) 13)
                            clear * - r28073 b28074 b28075 d28064
                            omega
                          have d28076 : (x (-6) 10).toNat = 1 := by
                            have r28077 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b28078 := hb (x (-11) 5)
                            have b28079 := hb (x (-6) 10)
                            have b28080 := hb (x (-7) 1 && x (-7) 11)
                            have b28081 := hb (x (-8) 2 && x (-8) 12)
                            have b28082 := hb (x (-9) 3 && x (-9) 13)
                            have b28083 := hb (x (-10) 4 && x (-10) 14)
                            clear * - r28077 b28078 b28079 b28080 b28081 b28082 b28083 d27824 d28060 d28072 d27784 d27788
                            omega
                          have d28084 : (x (-6) 2).toNat = 1 := by
                            have r28085 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                            have b28086 := hb (x (-6) 2)
                            have b28087 := hb (x (-6) 10)
                            clear * - r28085 b28086 b28087 d28076
                            omega
                          have d28088 : (x (-4) 12).toNat = 0 := by
                            have r28089 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28090 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                            have e28091 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                            have b28092 := hb (x (-7) 3)
                            have b28093 := hb (x (-6) 2)
                            have b28094 := hb (x (-5) 13)
                            have b28095 := hb (x (-4) 12)
                            clear * - r28089 e28090 e28091 b28092 b28093 b28094 b28095 d28084
                            omega
                          have d28096 : (x (-5) 13).toNat = 0 := by
                            have r28097 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28098 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                            have e28099 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                            have b28100 := hb (x (-7) 3)
                            have b28101 := hb (x (-6) 2)
                            have b28102 := hb (x (-5) 13)
                            have b28103 := hb (x (-4) 12)
                            clear * - r28097 e28098 e28099 b28100 b28101 b28102 b28103 d28088 d28084
                            omega
                          have d28104 : (x (-7) 3).toNat = 0 := by
                            have r28105 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28106 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                            have e28107 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                            have b28108 := hb (x (-7) 3)
                            have b28109 := hb (x (-6) 2)
                            have b28110 := hb (x (-5) 13)
                            have b28111 := hb (x (-4) 12)
                            clear * - r28105 e28106 e28107 b28108 b28109 b28110 b28111 d28088 d28096 d28084
                            omega
                          have d28112 : (x (-7) 11).toNat = 0 := by
                            have r28113 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                            have b28114 := hb (x (-7) 3)
                            have b28115 := hb (x (-7) 11)
                            clear * - r28113 b28114 b28115 d28104
                            omega
                          have d28116 : (x (-4) 8).toNat = 0 := by
                            have r28117 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28118 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                            have e28119 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                            have e28120 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                            have e28121 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                            have e28122 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                            have e28123 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                            have b28124 := hb (x (-11) 7)
                            have b28125 := hb (x (-10) 6)
                            have b28126 := hb (x (-9) 5)
                            have b28127 := hb (x (-8) 4)
                            have b28128 := hb (x (-7) 11)
                            have b28129 := hb (x (-6) 10)
                            have b28130 := hb (x (-5) 9)
                            have b28131 := hb (x (-4) 8)
                            clear * - r28117 e28118 e28119 e28120 e28121 e28122 e28123 b28124 b28125 b28126 b28127 b28128 b28129 b28130 b28131 d28076 d28112
                            omega
                          have d28132 : (x (-5) 9).toNat = 0 := by
                            have r28133 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28134 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                            have e28135 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                            have e28136 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                            have e28137 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                            have e28138 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                            have e28139 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                            have b28140 := hb (x (-11) 7)
                            have b28141 := hb (x (-10) 6)
                            have b28142 := hb (x (-9) 5)
                            have b28143 := hb (x (-8) 4)
                            have b28144 := hb (x (-7) 11)
                            have b28145 := hb (x (-6) 10)
                            have b28146 := hb (x (-5) 9)
                            have b28147 := hb (x (-4) 8)
                            clear * - r28133 e28134 e28135 e28136 e28137 e28138 e28139 b28140 b28141 b28142 b28143 b28144 b28145 b28146 b28147 d28116 d28076 d28112
                            omega
                          have d28148 : (x (-2) 8).toNat = 0 := by
                            have r28149 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28150 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e28151 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e28152 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e28153 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e28154 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e28155 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b28156 := hb (x (-9) 7)
                            have b28157 := hb (x (-8) 6)
                            have b28158 := hb (x (-7) 5)
                            have b28159 := hb (x (-6) 4)
                            have b28160 := hb (x (-5) 11)
                            have b28161 := hb (x (-4) 10)
                            have b28162 := hb (x (-3) 9)
                            have b28163 := hb (x (-2) 8)
                            clear * - r28149 e28150 e28151 e28152 e28153 e28154 e28155 b28156 b28157 b28158 b28159 b28160 b28161 b28162 b28163 d28041 d27832
                            omega
                          have d28164 : (x (-3) 9).toNat = 0 := by
                            have r28165 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28166 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e28167 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e28168 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e28169 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e28170 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e28171 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b28172 := hb (x (-9) 7)
                            have b28173 := hb (x (-8) 6)
                            have b28174 := hb (x (-7) 5)
                            have b28175 := hb (x (-6) 4)
                            have b28176 := hb (x (-5) 11)
                            have b28177 := hb (x (-4) 10)
                            have b28178 := hb (x (-3) 9)
                            have b28179 := hb (x (-2) 8)
                            clear * - r28165 e28166 e28167 e28168 e28169 e28170 e28171 b28172 b28173 b28174 b28175 b28176 b28177 b28178 b28179 d28148 d28041 d27832
                            omega
                          have d28180 : (x (-4) 10).toNat = 0 := by
                            have r28181 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28182 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e28183 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e28184 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e28185 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e28186 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e28187 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b28188 := hb (x (-9) 7)
                            have b28189 := hb (x (-8) 6)
                            have b28190 := hb (x (-7) 5)
                            have b28191 := hb (x (-6) 4)
                            have b28192 := hb (x (-5) 11)
                            have b28193 := hb (x (-4) 10)
                            have b28194 := hb (x (-3) 9)
                            have b28195 := hb (x (-2) 8)
                            clear * - r28181 e28182 e28183 e28184 e28185 e28186 e28187 b28188 b28189 b28190 b28191 b28192 b28193 b28194 b28195 d28148 d28164 d28041 d27832
                            omega
                          have d28196 : (x (-5) 11).toNat = 0 := by
                            have r28197 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28198 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e28199 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e28200 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e28201 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e28202 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e28203 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b28204 := hb (x (-9) 7)
                            have b28205 := hb (x (-8) 6)
                            have b28206 := hb (x (-7) 5)
                            have b28207 := hb (x (-6) 4)
                            have b28208 := hb (x (-5) 11)
                            have b28209 := hb (x (-4) 10)
                            have b28210 := hb (x (-3) 9)
                            have b28211 := hb (x (-2) 8)
                            clear * - r28197 e28198 e28199 e28200 e28201 e28202 e28203 b28204 b28205 b28206 b28207 b28208 b28209 b28210 b28211 d28148 d28164 d28180 d28041 d27832
                            omega
                          have d28212 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
                            have r28213 := hand2 (x (-4) 3) (x (-4) 13)
                            have b28214 := hb (x (-4) 13)
                            have b28215 := hb (x (-4) 3 && x (-4) 13)
                            clear * - r28213 b28214 b28215 d28029
                            omega
                          have d28216 : (x (-6) 5).toNat = 1 := by
                            have r28217 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b28218 := hb (x (-6) 5)
                            have b28219 := hb (x (-1) 10)
                            have b28220 := hb (x (-2) 1 && x (-2) 11)
                            have b28221 := hb (x (-3) 2 && x (-3) 12)
                            have b28222 := hb (x (-4) 3 && x (-4) 13)
                            have b28223 := hb (x (-5) 4 && x (-5) 14)
                            clear * - r28217 b28218 b28219 b28220 b28221 b28222 b28223 g11 g120 d28025 d28212 d27865
                            omega
                          have d28224 : (x (-2) 9).toNat = 0 := by
                            have r28225 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28226 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                            have e28227 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                            have e28228 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                            have e28229 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                            have e28230 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                            have e28231 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                            have b28232 := hb (x (-8) 7)
                            have b28233 := hb (x (-7) 6)
                            have b28234 := hb (x (-6) 5)
                            have b28235 := hb (x (-5) 4)
                            have b28236 := hb (x (-4) 11)
                            have b28237 := hb (x (-3) 10)
                            have b28238 := hb (x (-2) 9)
                            have b28239 := hb (x (-1) 8)
                            clear * - r28225 e28226 e28227 e28228 e28229 e28230 e28231 b28232 b28233 b28234 b28235 b28236 b28237 b28238 b28239 f27607 d27889 d28216
                            omega
                          have d28240 : (x (-3) 10).toNat = 0 := by
                            have r28241 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28242 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                            have e28243 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                            have e28244 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                            have e28245 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                            have e28246 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                            have e28247 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                            have b28248 := hb (x (-8) 7)
                            have b28249 := hb (x (-7) 6)
                            have b28250 := hb (x (-6) 5)
                            have b28251 := hb (x (-5) 4)
                            have b28252 := hb (x (-4) 11)
                            have b28253 := hb (x (-3) 10)
                            have b28254 := hb (x (-2) 9)
                            have b28255 := hb (x (-1) 8)
                            clear * - r28241 e28242 e28243 e28244 e28245 e28246 e28247 b28248 b28249 b28250 b28251 b28252 b28253 b28254 b28255 f27607 d28224 d27889 d28216
                            omega
                          have d28256 : (x (-4) 11).toNat = 0 := by
                            have r28257 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28258 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                            have e28259 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                            have e28260 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                            have e28261 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                            have e28262 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                            have e28263 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                            have b28264 := hb (x (-8) 7)
                            have b28265 := hb (x (-7) 6)
                            have b28266 := hb (x (-6) 5)
                            have b28267 := hb (x (-5) 4)
                            have b28268 := hb (x (-4) 11)
                            have b28269 := hb (x (-3) 10)
                            have b28270 := hb (x (-2) 9)
                            have b28271 := hb (x (-1) 8)
                            clear * - r28257 e28258 e28259 e28260 e28261 e28262 e28263 b28264 b28265 b28266 b28267 b28268 b28269 b28270 b28271 f27607 d28224 d28240 d27889 d28216
                            omega
                          have d28272 : (x (-8) 12).toNat = 0 := by
                            have r28273 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b28274 := hb (x (-10) 14)
                            have b28275 := hb (x (-9) 13)
                            have b28276 := hb (x (-8) 12)
                            have b28277 := hb (x (-7) 11)
                            have b28278 := hb (x (-6) 10)
                            have b28279 := hb (x (-5) 9)
                            have b28280 := hb (x (-4) 8)
                            have b28281 := hb (x (-3) 7)
                            have b28282 := hb (x (-2) 6)
                            have b28283 := hb (x (-1) 5)
                            have b28284 := hb (x 0 4)
                            have b28285 := hb (x 1 3)
                            have b28286 := hb (x 2 2)
                            have b28287 := hb (x 3 1)
                            clear * - r28273 b28274 b28275 b28276 b28277 b28278 b28279 b28280 b28281 b28282 b28283 b28284 b28285 b28286 b28287 d27629 d27677 g23 g15 g9 g5 g2 d28116 d28132 d28076 d28112
                            omega
                          have d28288 : (x (-9) 13).toNat = 0 := by
                            have r28289 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b28290 := hb (x (-10) 14)
                            have b28291 := hb (x (-9) 13)
                            have b28292 := hb (x (-8) 12)
                            have b28293 := hb (x (-7) 11)
                            have b28294 := hb (x (-6) 10)
                            have b28295 := hb (x (-5) 9)
                            have b28296 := hb (x (-4) 8)
                            have b28297 := hb (x (-3) 7)
                            have b28298 := hb (x (-2) 6)
                            have b28299 := hb (x (-1) 5)
                            have b28300 := hb (x 0 4)
                            have b28301 := hb (x 1 3)
                            have b28302 := hb (x 2 2)
                            have b28303 := hb (x 3 1)
                            clear * - r28289 b28290 b28291 b28292 b28293 b28294 b28295 b28296 b28297 b28298 b28299 b28300 b28301 b28302 b28303 d27629 d27677 g23 g15 g9 g5 g2 d28116 d28132 d28076 d28112 d28272
                            omega
                          have d28304 : (x (-10) 14).toNat = 0 := by
                            have r28305 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b28306 := hb (x (-10) 14)
                            have b28307 := hb (x (-9) 13)
                            have b28308 := hb (x (-8) 12)
                            have b28309 := hb (x (-7) 11)
                            have b28310 := hb (x (-6) 10)
                            have b28311 := hb (x (-5) 9)
                            have b28312 := hb (x (-4) 8)
                            have b28313 := hb (x (-3) 7)
                            have b28314 := hb (x (-2) 6)
                            have b28315 := hb (x (-1) 5)
                            have b28316 := hb (x 0 4)
                            have b28317 := hb (x 1 3)
                            have b28318 := hb (x 2 2)
                            have b28319 := hb (x 3 1)
                            clear * - r28305 b28306 b28307 b28308 b28309 b28310 b28311 b28312 b28313 b28314 b28315 b28316 b28317 b28318 b28319 d27629 d27677 g23 g15 g9 g5 g2 d28116 d28132 d28076 d28112 d28272 d28288
                            omega
                          have d28320 : (x (-10) 2).toNat = 0 := by
                            have r28321 : (x (-10) 2).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp2 (-10))
                            have b28322 := hb (x (-10) 2)
                            have b28323 := hb (x (-10) 14)
                            clear * - r28321 b28322 b28323 d28304
                            omega
                          have r28324 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28325 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28326 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28327 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28328 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e28329 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e28330 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e28331 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e28332 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e28333 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have r28334 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28335 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                          have e28336 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                          have r28337 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28338 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                          have e28339 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                          have r28340 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28341 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                          have e28342 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                          have r28343 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28344 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                          have e28345 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                          have r28346 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28347 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28348 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28349 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28350 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28351 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28352 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28353 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28354 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
                          have r28355 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                          have r28356 := hand2 (x 6 1) (x 6 11)
                          have r28357 := hand2 (x 5 2) (x 5 12)
                          have r28358 := hand2 (x 4 3) (x 4 13)
                          have r28359 := hand1 (x (-9) 1) (x (-9) 14)
                          have r28360 := hand2 (x 7 1) (x 7 14)
                          have b28419 := hb (x 8 1)
                          linarith only [r28324, r28325, r28326, r28327, e28328, e28329, e28330, e28331, e28332, e28333, r28334, e28335, e28336, r28337, e28338, e28339, r28340, e28341, e28342, r28343, e28344, e28345, r28346, r28347, r28348, r28349, r28350, r28351, r28352, r28353, r28354, r28355, r28356, r28357, r28358, r28359, r28360, b28419, d28320, d27828, d28048, d27849, d28196, d27877, d27857, d28180, d28256, d28029, d28164, d28240, d28013, d28148, d28224, g7, f27694, f27607, g11, g17, g18, f27686, g25, g26, f27696, f27700, g30, g31, f27704, g35, d27641, g125, d27637]
                        · have f28431 : (x 2 7).toNat = 1 := by rw [h27703]; rfl
                          have d28432 : (x 9 8).toNat = 0 := by
                            have r28433 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28434 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                            have e28435 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                            have e28436 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                            have e28437 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                            have e28438 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                            have e28439 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                            have b28440 := hb (x 2 7)
                            have b28441 := hb (x 3 6)
                            have b28442 := hb (x 4 5)
                            have b28443 := hb (x 5 4)
                            have b28444 := hb (x 6 11)
                            have b28445 := hb (x 7 10)
                            have b28446 := hb (x 8 9)
                            have b28447 := hb (x 9 8)
                            clear * - r28433 e28434 e28435 e28436 e28437 e28438 e28439 b28440 b28441 b28442 b28443 b28444 b28445 b28446 b28447 f28431
                            omega
                          have d28448 : (x 8 9).toNat = 0 := by
                            have r28449 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28450 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                            have e28451 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                            have e28452 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                            have e28453 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                            have e28454 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                            have e28455 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                            have b28456 := hb (x 2 7)
                            have b28457 := hb (x 3 6)
                            have b28458 := hb (x 4 5)
                            have b28459 := hb (x 5 4)
                            have b28460 := hb (x 6 11)
                            have b28461 := hb (x 7 10)
                            have b28462 := hb (x 8 9)
                            have b28463 := hb (x 9 8)
                            clear * - r28449 e28450 e28451 e28452 e28453 e28454 e28455 b28456 b28457 b28458 b28459 b28460 b28461 b28462 b28463 d28432 f28431
                            omega
                          have d28464 : (x 7 10).toNat = 0 := by
                            have r28465 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28466 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                            have e28467 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                            have e28468 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                            have e28469 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                            have e28470 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                            have e28471 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                            have b28472 := hb (x 2 7)
                            have b28473 := hb (x 3 6)
                            have b28474 := hb (x 4 5)
                            have b28475 := hb (x 5 4)
                            have b28476 := hb (x 6 11)
                            have b28477 := hb (x 7 10)
                            have b28478 := hb (x 8 9)
                            have b28479 := hb (x 9 8)
                            clear * - r28465 e28466 e28467 e28468 e28469 e28470 e28471 b28472 b28473 b28474 b28475 b28476 b28477 b28478 b28479 d28432 d28448 f28431
                            omega
                          have d28480 : (x 6 11).toNat = 0 := by
                            have r28481 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28482 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                            have e28483 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                            have e28484 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                            have e28485 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                            have e28486 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                            have e28487 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                            have b28488 := hb (x 2 7)
                            have b28489 := hb (x 3 6)
                            have b28490 := hb (x 4 5)
                            have b28491 := hb (x 5 4)
                            have b28492 := hb (x 6 11)
                            have b28493 := hb (x 7 10)
                            have b28494 := hb (x 8 9)
                            have b28495 := hb (x 9 8)
                            clear * - r28481 e28482 e28483 e28484 e28485 e28486 e28487 b28488 b28489 b28490 b28491 b28492 b28493 b28494 b28495 d28432 d28448 d28464 f28431
                            omega
                          have d28496 : (x 6 1 && x 6 11).toNat = 0 := by
                            have r28497 := hand2 (x 6 1) (x 6 11)
                            have b28498 := hb (x 6 11)
                            have b28499 := hb (x 6 1 && x 6 11)
                            clear * - r28497 b28498 b28499 d28480
                            omega
                          have d28500 : (x 5 4).toNat = 0 := by
                            have r28501 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28502 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                            have e28503 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                            have e28504 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                            have e28505 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                            have e28506 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                            have e28507 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                            have b28508 := hb (x 2 7)
                            have b28509 := hb (x 3 6)
                            have b28510 := hb (x 4 5)
                            have b28511 := hb (x 5 4)
                            have b28512 := hb (x 6 11)
                            have b28513 := hb (x 7 10)
                            have b28514 := hb (x 8 9)
                            have b28515 := hb (x 9 8)
                            clear * - r28501 e28502 e28503 e28504 e28505 e28506 e28507 b28508 b28509 b28510 b28511 b28512 b28513 b28514 b28515 d28432 d28448 d28464 d28480 f28431
                            omega
                          have d28516 : (x 5 4 && x 5 14).toNat = 0 := by
                            have r28517 := hand1 (x 5 4) (x 5 14)
                            have b28518 := hb (x 5 4)
                            have b28519 := hb (x 5 4 && x 5 14)
                            clear * - r28517 b28518 b28519 d28500
                            omega
                          have d28520 : (x 4 5).toNat = 0 := by
                            have r28521 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e28522 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                            have e28523 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                            have e28524 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                            have e28525 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                            have e28526 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                            have e28527 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                            have b28528 := hb (x 2 7)
                            have b28529 := hb (x 3 6)
                            have b28530 := hb (x 4 5)
                            have b28531 := hb (x 5 4)
                            have b28532 := hb (x 6 11)
                            have b28533 := hb (x 7 10)
                            have b28534 := hb (x 8 9)
                            have b28535 := hb (x 9 8)
                            clear * - r28521 e28522 e28523 e28524 e28525 e28526 e28527 b28528 b28529 b28530 b28531 b28532 b28533 b28534 b28535 d28432 d28448 d28464 d28480 d28500 f28431
                            omega
                          have r28536 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28537 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28538 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                          have e28539 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                          have e28540 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                          have e28541 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                          have e28542 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                          have e28543 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                          have r28544 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28545 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                          have e28546 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                          have r28547 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28548 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28549 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28550 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r28551 := hand2 (x 10 1) (x 10 6)
                          have r28552 := hand2 (x 9 2) (x 9 7)
                          have r28553 := hand2 (x 8 3) (x 8 8)
                          have r28554 := hand1 (x 7 4) (x 7 9)
                          have r28555 := hand1 (x 6 5) (x 6 10)
                          have r28556 := hand1 (x 5 6) (x 5 11)
                          have r28557 := hand2 (x 6 1) (x 6 10)
                          have r28558 := hand2 (x 5 2) (x 5 11)
                          have r28559 := hand1 (x 5 2) (x 5 12)
                          have r28560 := hand1 (x 4 3) (x 4 13)
                          have r28561 := hand2 (x 8 1) (x 8 11)
                          have r28562 := hand2 (x 7 2) (x 7 12)
                          have r28563 := hand2 (x 6 3) (x 6 13)
                          linarith only [r28536, r28537, e28538, e28539, e28540, e28541, e28542, e28543, r28544, e28545, e28546, r28547, r28548, r28549, r28550, r28551, r28552, r28553, r28554, r28555, r28556, r28557, r28558, r28559, r28560, r28561, r28562, r28563, g26, g27, g31, g34, d27624, d28520, d27657, d28464, d27669, g77, g78, d27665, g117, g118, d28496, g125, d28516]
                      · have f28617 : (x 2 6).toNat = 1 := by rw [h27701]; rfl
                        have d28618 : (x 8 8).toNat = 0 := by
                          have r28619 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28620 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e28621 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e28622 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e28623 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e28624 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e28625 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have b28626 := hb (x 1 7)
                          have b28627 := hb (x 2 6)
                          have b28628 := hb (x 3 5)
                          have b28629 := hb (x 4 4)
                          have b28630 := hb (x 5 11)
                          have b28631 := hb (x 6 10)
                          have b28632 := hb (x 7 9)
                          have b28633 := hb (x 8 8)
                          clear * - r28619 e28620 e28621 e28622 e28623 e28624 e28625 b28626 b28627 b28628 b28629 b28630 b28631 b28632 b28633 d27673 f28617 f27605
                          omega
                        have d28634 : (x 7 9).toNat = 0 := by
                          have r28635 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28636 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e28637 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e28638 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e28639 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e28640 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e28641 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have b28642 := hb (x 1 7)
                          have b28643 := hb (x 2 6)
                          have b28644 := hb (x 3 5)
                          have b28645 := hb (x 4 4)
                          have b28646 := hb (x 5 11)
                          have b28647 := hb (x 6 10)
                          have b28648 := hb (x 7 9)
                          have b28649 := hb (x 8 8)
                          clear * - r28635 e28636 e28637 e28638 e28639 e28640 e28641 b28642 b28643 b28644 b28645 b28646 b28647 b28648 b28649 d28618 d27673 f28617 f27605
                          omega
                        have d28650 : (x 6 10).toNat = 0 := by
                          have r28651 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e28652 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                          have e28653 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                          have e28654 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                          have e28655 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                          have e28656 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                          have e28657 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                          have b28658 := hb (x 1 7)
                          have b28659 := hb (x 2 6)
                          have b28660 := hb (x 3 5)
                          have b28661 := hb (x 4 4)
                          have b28662 := hb (x 5 11)
                          have b28663 := hb (x 6 10)
                          have b28664 := hb (x 7 9)
                          have b28665 := hb (x 8 8)
                          clear * - r28651 e28652 e28653 e28654 e28655 e28656 e28657 b28658 b28659 b28660 b28661 b28662 b28663 b28664 b28665 d28618 d28634 d27673 f28617 f27605
                          omega
                        have d28666 : (x 6 1 && x 6 10).toNat = 0 := by
                          have r28667 := hand2 (x 6 1) (x 6 10)
                          have b28668 := hb (x 6 10)
                          have b28669 := hb (x 6 1 && x 6 10)
                          clear * - r28667 b28668 b28669 d28650
                          omega
                        have d28670 : (x 5 2 && x 5 11).toNat = 1 := by
                          have r28671 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have b28672 := hb (x 1 6)
                          have b28673 := hb (x 7 9)
                          have b28674 := hb (x 6 1 && x 6 10)
                          have b28675 := hb (x 5 2 && x 5 11)
                          have b28676 := hb (x 4 3 && x 4 12)
                          have b28677 := hb (x 3 4 && x 3 13)
                          have b28678 := hb (x 2 5 && x 2 14)
                          clear * - r28671 b28672 b28673 b28674 b28675 b28676 b28677 b28678 d28634 d28666 d27665 g117 g118 g26
                          omega
                        have d28679 : (x 5 11).toNat = 1 := by
                          have r28680 := hand2 (x 5 2) (x 5 11)
                          have b28681 := hb (x 5 11)
                          have b28682 := hb (x 5 2 && x 5 11)
                          clear * - r28680 b28681 b28682 d28670
                          omega
                        have r28683 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28684 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e28685 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e28686 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e28687 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e28688 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e28689 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b28690 := hb (x 1 7)
                        have b28691 := hb (x 2 6)
                        have b28692 := hb (x 3 5)
                        have b28693 := hb (x 4 4)
                        have b28694 := hb (x 5 11)
                        have b28695 := hb (x 6 10)
                        have b28696 := hb (x 7 9)
                        have b28697 := hb (x 8 8)
                        linarith only [r28683, e28684, e28685, e28686, e28687, e28688, e28689, b28690, b28691, b28692, b28693, b28694, b28695, b28696, b28697, d28618, d28634, d28650, d28679, d27673, f28617, f27605]
                    · have f28698 : (x 2 3).toNat = 1 := by rw [h27699]; rfl
                      have d28699 : (x 5 12).toNat = 0 := by
                        have r28700 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28701 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                        have e28702 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                        have b28703 := hb (x 2 3)
                        have b28704 := hb (x 3 2)
                        have b28705 := hb (x 4 13)
                        have b28706 := hb (x 5 12)
                        clear * - r28700 e28701 e28702 b28703 b28704 b28705 b28706 f28698
                        omega
                      have d28707 : (x 5 1 && x 5 12).toNat = 0 := by
                        have r28708 := hand2 (x 5 1) (x 5 12)
                        have b28709 := hb (x 5 12)
                        have b28710 := hb (x 5 1 && x 5 12)
                        clear * - r28708 b28709 b28710 d28699
                        omega
                      have d28711 : (x 5 4).toNat = 0 := by
                        have r28712 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
                        have b28713 := hb (x 5 4)
                        have b28714 := hb (x 5 12)
                        clear * - r28712 b28713 b28714 d28699
                        omega
                      have d28715 : (x 4 13).toNat = 0 := by
                        have r28716 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28717 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                        have e28718 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                        have b28719 := hb (x 2 3)
                        have b28720 := hb (x 3 2)
                        have b28721 := hb (x 4 13)
                        have b28722 := hb (x 5 12)
                        clear * - r28716 e28717 e28718 b28719 b28720 b28721 b28722 d28699 f28698
                        omega
                      have d28723 : (x 3 2).toNat = 0 := by
                        have r28724 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28725 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                        have e28726 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                        have b28727 := hb (x 2 3)
                        have b28728 := hb (x 3 2)
                        have b28729 := hb (x 4 13)
                        have b28730 := hb (x 5 12)
                        clear * - r28724 e28725 e28726 b28727 b28728 b28729 b28730 d28699 d28715 f28698
                        omega
                      have d28731 : (x 5 13).toNat = 1 := by
                        have r28732 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28733 := hb (x 3 2)
                        have b28734 := hb (x 5 13)
                        have b28735 := hb (x 4 1 && x 4 14)
                        clear * - r28732 b28733 b28734 b28735 d27637 d28723
                        omega
                      have d28736 : (x 5 1).toNat = 1 := by
                        have r28737 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                        have b28738 := hb (x 5 1)
                        have b28739 := hb (x 5 13)
                        clear * - r28737 b28738 b28739 d28731
                        omega
                      have d28740 : (x 6 14).toNat = 0 := by
                        have r28741 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28742 := hb (x 5 1)
                        have b28743 := hb (x 6 14)
                        clear * - r28741 b28742 b28743 d28736
                        omega
                      have d28744 : (x 6 3 && x 6 14).toNat = 0 := by
                        have r28745 := hand2 (x 6 3) (x 6 14)
                        have b28746 := hb (x 6 14)
                        have b28747 := hb (x 6 3 && x 6 14)
                        clear * - r28745 b28746 b28747 d28740
                        omega
                      have d28748 : (x 6 2).toNat = 0 := by
                        have r28749 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                        have b28750 := hb (x 6 2)
                        have b28751 := hb (x 6 14)
                        clear * - r28749 b28750 b28751 d28740
                        omega
                      have d28752 : (x 6 12).toNat = 0 := by
                        have r28753 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28754 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                        have e28755 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                        have b28756 := hb (x 3 3)
                        have b28757 := hb (x 4 2)
                        have b28758 := hb (x 5 13)
                        have b28759 := hb (x 6 12)
                        clear * - r28753 e28754 e28755 b28756 b28757 b28758 b28759 d28731 d27641
                        omega
                      have d28760 : (x 6 4).toNat = 0 := by
                        have r28761 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
                        have b28762 := hb (x 6 4)
                        have b28763 := hb (x 6 12)
                        clear * - r28761 b28762 b28763 d28752
                        omega
                      have d28764 : (x 3 3).toNat = 0 := by
                        have r28765 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28766 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                        have e28767 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                        have b28768 := hb (x 3 3)
                        have b28769 := hb (x 4 2)
                        have b28770 := hb (x 5 13)
                        have b28771 := hb (x 6 12)
                        clear * - r28765 e28766 e28767 b28768 b28769 b28770 b28771 d28752 d28731 d27641
                        omega
                      have d28772 : (x 3 3 && x 3 14).toNat = 0 := by
                        have r28773 := hand1 (x 3 3) (x 3 14)
                        have b28774 := hb (x 3 3)
                        have b28775 := hb (x 3 3 && x 3 14)
                        clear * - r28773 b28774 b28775 d28764
                        omega
                      have d28776 : (x 6 11).toNat = 1 := by
                        have r28777 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28778 := hb (x 2 4)
                        have b28779 := hb (x 6 11)
                        have b28780 := hb (x 5 1 && x 5 12)
                        have b28781 := hb (x 4 2 && x 4 13)
                        have b28782 := hb (x 3 3 && x 3 14)
                        clear * - r28777 b28778 b28779 b28780 b28781 b28782 d28707 d27645 d28772 g30
                        omega
                      have d28783 : (x 6 3).toNat = 1 := by
                        have r28784 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                        have b28785 := hb (x 6 3)
                        have b28786 := hb (x 6 11)
                        clear * - r28784 b28785 b28786 d28776
                        omega
                      have d28787 : (x 9 12).toNat = 0 := by
                        have r28788 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28789 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e28790 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b28791 := hb (x 6 3)
                        have b28792 := hb (x 7 2)
                        have b28793 := hb (x 8 13)
                        have b28794 := hb (x 9 12)
                        clear * - r28788 e28789 e28790 b28791 b28792 b28793 b28794 d28783
                        omega
                      have d28795 : (x 9 1 && x 9 12).toNat = 0 := by
                        have r28796 := hand2 (x 9 1) (x 9 12)
                        have b28797 := hb (x 9 12)
                        have b28798 := hb (x 9 1 && x 9 12)
                        clear * - r28796 b28797 b28798 d28787
                        omega
                      have d28799 : (x 9 4).toNat = 0 := by
                        have r28800 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                        have b28801 := hb (x 9 4)
                        have b28802 := hb (x 9 12)
                        clear * - r28800 b28801 b28802 d28787
                        omega
                      have d28803 : (x 8 13).toNat = 0 := by
                        have r28804 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28805 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e28806 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b28807 := hb (x 6 3)
                        have b28808 := hb (x 7 2)
                        have b28809 := hb (x 8 13)
                        have b28810 := hb (x 9 12)
                        clear * - r28804 e28805 e28806 b28807 b28808 b28809 b28810 d28787 d28783
                        omega
                      have d28811 : (x 8 2 && x 8 13).toNat = 0 := by
                        have r28812 := hand2 (x 8 2) (x 8 13)
                        have b28813 := hb (x 8 13)
                        have b28814 := hb (x 8 2 && x 8 13)
                        clear * - r28812 b28813 b28814 d28803
                        omega
                      have d28815 : (x 7 1 && x 7 14).toNat = 1 := by
                        have r28816 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28817 := hb (x 6 2)
                        have b28818 := hb (x 8 13)
                        have b28819 := hb (x 7 1 && x 7 14)
                        clear * - r28816 b28817 b28818 b28819 d28803 d28748
                        omega
                      have d28820 : (x 7 1).toNat = 1 := by
                        have r28821 := hand1 (x 7 1) (x 7 14)
                        have b28822 := hb (x 7 1)
                        have b28823 := hb (x 7 1 && x 7 14)
                        clear * - r28821 b28822 b28823 d28815
                        omega
                      have d28824 : (x 8 14).toNat = 0 := by
                        have r28825 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28826 := hb (x 7 1)
                        have b28827 := hb (x 8 14)
                        clear * - r28825 b28826 b28827 d28820
                        omega
                      have d28828 : (x 8 1 && x 8 14).toNat = 0 := by
                        have r28829 := hand2 (x 8 1) (x 8 14)
                        have b28830 := hb (x 8 14)
                        have b28831 := hb (x 8 1 && x 8 14)
                        clear * - r28829 b28830 b28831 d28824
                        omega
                      have d28832 : (x 8 2).toNat = 0 := by
                        have r28833 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
                        have b28834 := hb (x 8 2)
                        have b28835 := hb (x 8 14)
                        clear * - r28833 b28834 b28835 d28824
                        omega
                      have d28836 : (x 7 2).toNat = 0 := by
                        have r28837 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28838 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e28839 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b28840 := hb (x 6 3)
                        have b28841 := hb (x 7 2)
                        have b28842 := hb (x 8 13)
                        have b28843 := hb (x 9 12)
                        clear * - r28837 e28838 e28839 b28840 b28841 b28842 b28843 d28787 d28803 d28783
                        omega
                      have d28844 : (x 7 2 && x 7 13).toNat = 0 := by
                        have r28845 := hand1 (x 7 2) (x 7 13)
                        have b28846 := hb (x 7 2)
                        have b28847 := hb (x 7 2 && x 7 13)
                        clear * - r28845 b28846 b28847 d28836
                        omega
                      have d28848 : (x 9 13).toNat = 1 := by
                        have r28849 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28850 := hb (x 7 2)
                        have b28851 := hb (x 9 13)
                        have b28852 := hb (x 8 1 && x 8 14)
                        clear * - r28849 b28850 b28851 b28852 d28828 d28836
                        omega
                      have d28853 : (x 9 1).toNat = 1 := by
                        have r28854 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
                        have b28855 := hb (x 9 1)
                        have b28856 := hb (x 9 13)
                        clear * - r28854 b28855 b28856 d28848
                        omega
                      have d28857 : (x 10 14).toNat = 0 := by
                        have r28858 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28859 := hb (x 9 1)
                        have b28860 := hb (x 10 14)
                        clear * - r28858 b28859 b28860 d28853
                        omega
                      have d28861 : (x 10 1 && x 10 14).toNat = 0 := by
                        have r28862 := hand2 (x 10 1) (x 10 14)
                        have b28863 := hb (x 10 14)
                        have b28864 := hb (x 10 1 && x 10 14)
                        clear * - r28862 b28863 b28864 d28857
                        omega
                      have d28865 : (x 10 3 && x 10 14).toNat = 0 := by
                        have r28866 := hand2 (x 10 3) (x 10 14)
                        have b28867 := hb (x 10 14)
                        have b28868 := hb (x 10 3 && x 10 14)
                        clear * - r28866 b28867 b28868 d28857
                        omega
                      have d28869 : (x 10 2).toNat = 0 := by
                        have r28870 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
                        have b28871 := hb (x 10 2)
                        have b28872 := hb (x 10 14)
                        clear * - r28870 b28871 b28872 d28857
                        omega
                      have d28873 : (x 10 12).toNat = 0 := by
                        have r28874 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28875 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                        have e28876 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                        have b28877 := hb (x 7 3)
                        have b28878 := hb (x 8 2)
                        have b28879 := hb (x 9 13)
                        have b28880 := hb (x 10 12)
                        clear * - r28874 e28875 e28876 b28877 b28878 b28879 b28880 d28848 d28832
                        omega
                      have d28881 : (x 10 4).toNat = 0 := by
                        have r28882 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                        have b28883 := hb (x 10 4)
                        have b28884 := hb (x 10 12)
                        clear * - r28882 b28883 b28884 d28873
                        omega
                      have d28885 : (x 7 3).toNat = 0 := by
                        have r28886 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28887 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                        have e28888 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                        have b28889 := hb (x 7 3)
                        have b28890 := hb (x 8 2)
                        have b28891 := hb (x 9 13)
                        have b28892 := hb (x 10 12)
                        clear * - r28886 e28887 e28888 b28889 b28890 b28891 b28892 d28873 d28848 d28832
                        omega
                      have d28893 : (x 7 3 && x 7 14).toNat = 0 := by
                        have r28894 := hand1 (x 7 3) (x 7 14)
                        have b28895 := hb (x 7 3)
                        have b28896 := hb (x 7 3 && x 7 14)
                        clear * - r28894 b28895 b28896 d28885
                        omega
                      have d28897 : (x 10 11).toNat = 1 := by
                        have r28898 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28899 := hb (x 6 4)
                        have b28900 := hb (x 10 11)
                        have b28901 := hb (x 9 1 && x 9 12)
                        have b28902 := hb (x 8 2 && x 8 13)
                        have b28903 := hb (x 7 3 && x 7 14)
                        clear * - r28898 b28899 b28900 b28901 b28902 b28903 d28795 d28811 d28893 d28760
                        omega
                      have d28904 : (x 10 3).toNat = 1 := by
                        have r28905 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
                        have b28906 := hb (x 10 3)
                        have b28907 := hb (x 10 11)
                        clear * - r28905 b28906 b28907 d28897
                        omega
                      have d28908 : (x 13 12).toNat = 0 := by
                        have r28909 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28910 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                        have e28911 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                        have b28912 := hb (x 10 3)
                        have b28913 := hb (x 11 2)
                        have b28914 := hb (x 12 13)
                        have b28915 := hb (x 13 12)
                        clear * - r28909 e28910 e28911 b28912 b28913 b28914 b28915 d28904
                        omega
                      have d28916 : (x 13 1 && x 13 12).toNat = 0 := by
                        have r28917 := hand2 (x 13 1) (x 13 12)
                        have b28918 := hb (x 13 12)
                        have b28919 := hb (x 13 1 && x 13 12)
                        clear * - r28917 b28918 b28919 d28908
                        omega
                      have d28920 : (x 13 2 && x 13 12).toNat = 0 := by
                        have r28921 := hand2 (x 13 2) (x 13 12)
                        have b28922 := hb (x 13 12)
                        have b28923 := hb (x 13 2 && x 13 12)
                        clear * - r28921 b28922 b28923 d28908
                        omega
                      have d28924 : (x 12 13).toNat = 0 := by
                        have r28925 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28926 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                        have e28927 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                        have b28928 := hb (x 10 3)
                        have b28929 := hb (x 11 2)
                        have b28930 := hb (x 12 13)
                        have b28931 := hb (x 13 12)
                        clear * - r28925 e28926 e28927 b28928 b28929 b28930 b28931 d28908 d28904
                        omega
                      have d28932 : (x 12 2 && x 12 13).toNat = 0 := by
                        have r28933 := hand2 (x 12 2) (x 12 13)
                        have b28934 := hb (x 12 13)
                        have b28935 := hb (x 12 2 && x 12 13)
                        clear * - r28933 b28934 b28935 d28924
                        omega
                      have d28936 : (x 12 3 && x 12 13).toNat = 0 := by
                        have r28937 := hand2 (x 12 3) (x 12 13)
                        have b28938 := hb (x 12 13)
                        have b28939 := hb (x 12 3 && x 12 13)
                        clear * - r28937 b28938 b28939 d28924
                        omega
                      have d28940 : (x 11 1 && x 11 14).toNat = 1 := by
                        have r28941 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28942 := hb (x 10 2)
                        have b28943 := hb (x 12 13)
                        have b28944 := hb (x 11 1 && x 11 14)
                        clear * - r28941 b28942 b28943 b28944 d28924 d28869
                        omega
                      have d28945 : (x 11 14).toNat = 1 := by
                        have r28946 := hand2 (x 11 1) (x 11 14)
                        have b28947 := hb (x 11 14)
                        have b28948 := hb (x 11 1 && x 11 14)
                        clear * - r28946 b28947 b28948 d28940
                        omega
                      have d28949 : (x 10 1).toNat = 0 := by
                        have r28950 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28951 := hb (x 10 1)
                        have b28952 := hb (x 11 14)
                        clear * - r28950 b28951 b28952 d28945
                        omega
                      have d28953 : (x 10 13).toNat = 0 := by
                        have r28954 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
                        have b28955 := hb (x 10 1)
                        have b28956 := hb (x 10 13)
                        clear * - r28954 b28955 b28956 d28949
                        omega
                      have d28957 : (x 10 5).toNat = 0 := by
                        have r28958 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
                        have b28959 := hb (x 10 5)
                        have b28960 := hb (x 10 13)
                        clear * - r28958 b28959 b28960 d28953
                        omega
                      have d28961 : (x 9 1 && x 9 14).toNat = 1 := by
                        have r28962 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28963 := hb (x 8 2)
                        have b28964 := hb (x 10 13)
                        have b28965 := hb (x 9 1 && x 9 14)
                        clear * - r28962 b28963 b28964 b28965 d28953 d28832
                        omega
                      have d28966 : (x 9 14).toNat = 1 := by
                        have r28967 := hand2 (x 9 1) (x 9 14)
                        have b28968 := hb (x 9 14)
                        have b28969 := hb (x 9 1 && x 9 14)
                        clear * - r28967 b28968 b28969 d28961
                        omega
                      have d28970 : (x 8 1).toNat = 0 := by
                        have r28971 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28972 := hb (x 8 1)
                        have b28973 := hb (x 9 14)
                        clear * - r28971 b28972 b28973 d28966
                        omega
                      have d28974 : (x 8 1 && x 8 12).toNat = 0 := by
                        have r28975 := hand1 (x 8 1) (x 8 12)
                        have b28976 := hb (x 8 1)
                        have b28977 := hb (x 8 1 && x 8 12)
                        clear * - r28975 b28976 b28977 d28970
                        omega
                      have d28978 : (x 9 11).toNat = 1 := by
                        have r28979 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b28980 := hb (x 5 4)
                        have b28981 := hb (x 9 11)
                        have b28982 := hb (x 8 1 && x 8 12)
                        have b28983 := hb (x 7 2 && x 7 13)
                        have b28984 := hb (x 6 3 && x 6 14)
                        clear * - r28979 b28980 b28981 b28982 b28983 b28984 d28974 d28844 d28744 d28711
                        omega
                      have d28985 : (x 9 3).toNat = 1 := by
                        have r28986 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
                        have b28987 := hb (x 9 3)
                        have b28988 := hb (x 9 11)
                        clear * - r28986 b28987 b28988 d28978
                        omega
                      have d28989 : (x 12 12).toNat = 0 := by
                        have r28990 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e28991 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                        have e28992 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                        have b28993 := hb (x 9 3)
                        have b28994 := hb (x 10 2)
                        have b28995 := hb (x 11 13)
                        have b28996 := hb (x 12 12)
                        clear * - r28990 e28991 e28992 b28993 b28994 b28995 b28996 d28869 d28985
                        omega
                      have d28997 : (x 12 1 && x 12 12).toNat = 0 := by
                        have r28998 := hand2 (x 12 1) (x 12 12)
                        have b28999 := hb (x 12 12)
                        have b29000 := hb (x 12 1 && x 12 12)
                        clear * - r28998 b28999 b29000 d28989
                        omega
                      have d29001 : (x 11 13).toNat = 0 := by
                        have r29002 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29003 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                        have e29004 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                        have b29005 := hb (x 9 3)
                        have b29006 := hb (x 10 2)
                        have b29007 := hb (x 11 13)
                        have b29008 := hb (x 12 12)
                        clear * - r29002 e29003 e29004 b29005 b29006 b29007 b29008 d28989 d28869 d28985
                        omega
                      have d29009 : (x 11 2 && x 11 13).toNat = 0 := by
                        have r29010 := hand2 (x 11 2) (x 11 13)
                        have b29011 := hb (x 11 13)
                        have b29012 := hb (x 11 2 && x 11 13)
                        clear * - r29010 b29011 b29012 d29001
                        omega
                      have d29013 : (x 13 11).toNat = 1 := by
                        have r29014 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29015 := hb (x 9 4)
                        have b29016 := hb (x 13 11)
                        have b29017 := hb (x 12 1 && x 12 12)
                        have b29018 := hb (x 11 2 && x 11 13)
                        have b29019 := hb (x 10 3 && x 10 14)
                        clear * - r29014 b29015 b29016 b29017 b29018 b29019 d28997 d29009 d28865 d28799
                        omega
                      have d29020 : (x 13 3).toNat = 1 := by
                        have r29021 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                        have b29022 := hb (x 13 3)
                        have b29023 := hb (x 13 11)
                        clear * - r29021 b29022 b29023 d29013
                        omega
                      have d29024 : (x 16 12).toNat = 0 := by
                        have r29025 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29026 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                        have e29027 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                        have b29028 := hb (x 13 3)
                        have b29029 := hb (x 14 2)
                        have b29030 := hb (x 15 13)
                        have b29031 := hb (x 16 12)
                        clear * - r29025 e29026 e29027 b29028 b29029 b29030 b29031 d29020
                        omega
                      have d29032 : (x 15 13).toNat = 0 := by
                        have r29033 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29034 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                        have e29035 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                        have b29036 := hb (x 13 3)
                        have b29037 := hb (x 14 2)
                        have b29038 := hb (x 15 13)
                        have b29039 := hb (x 16 12)
                        clear * - r29033 e29034 e29035 b29036 b29037 b29038 b29039 d29024 d29020
                        omega
                      have d29040 : (x 14 2).toNat = 0 := by
                        have r29041 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29042 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
                        have e29043 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
                        have b29044 := hb (x 13 3)
                        have b29045 := hb (x 14 2)
                        have b29046 := hb (x 15 13)
                        have b29047 := hb (x 16 12)
                        clear * - r29041 e29042 e29043 b29044 b29045 b29046 b29047 d29024 d29032 d29020
                        omega
                      have d29048 : (x 9 2).toNat = 1 := by
                        have r29049 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29050 := hb (x 9 2)
                        have b29051 := hb (x 11 13)
                        have b29052 := hb (x 10 1 && x 10 14)
                        clear * - r29049 b29050 b29051 b29052 d29001 d28861
                        omega
                      have d29053 : (x 11 12).toNat = 0 := by
                        have r29054 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29055 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                        have e29056 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                        have b29057 := hb (x 8 3)
                        have b29058 := hb (x 9 2)
                        have b29059 := hb (x 10 13)
                        have b29060 := hb (x 11 12)
                        clear * - r29054 e29055 e29056 b29057 b29058 b29059 b29060 d28953 d29048
                        omega
                      have d29061 : (x 11 4).toNat = 0 := by
                        have r29062 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                        have b29063 := hb (x 11 4)
                        have b29064 := hb (x 11 12)
                        clear * - r29062 b29063 b29064 d29053
                        omega
                      have d29065 : (x 11 4 && x 11 14).toNat = 0 := by
                        have r29066 := hand1 (x 11 4) (x 11 14)
                        have b29067 := hb (x 11 4)
                        have b29068 := hb (x 11 4 && x 11 14)
                        clear * - r29066 b29067 b29068 d29061
                        omega
                      have d29069 : (x 11 1).toNat = 1 := by
                        have r29070 := hand1 (x 11 1) (x 11 14)
                        have b29071 := hb (x 11 1)
                        have b29072 := hb (x 11 1 && x 11 14)
                        clear * - r29070 b29071 b29072 d28940
                        omega
                      have d29073 : (x 12 14).toNat = 0 := by
                        have r29074 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29075 := hb (x 11 1)
                        have b29076 := hb (x 12 14)
                        clear * - r29074 b29075 b29076 d29069
                        omega
                      have d29077 : (x 12 1 && x 12 14).toNat = 0 := by
                        have r29078 := hand2 (x 12 1) (x 12 14)
                        have b29079 := hb (x 12 14)
                        have b29080 := hb (x 12 1 && x 12 14)
                        clear * - r29078 b29079 b29080 d29073
                        omega
                      have d29081 : (x 12 2).toNat = 0 := by
                        have r29082 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
                        have b29083 := hb (x 12 2)
                        have b29084 := hb (x 12 14)
                        clear * - r29082 b29083 b29084 d29073
                        omega
                      have d29085 : (x 11 2).toNat = 0 := by
                        have r29086 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29087 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
                        have e29088 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
                        have b29089 := hb (x 10 3)
                        have b29090 := hb (x 11 2)
                        have b29091 := hb (x 12 13)
                        have b29092 := hb (x 13 12)
                        clear * - r29086 e29087 e29088 b29089 b29090 b29091 b29092 d28908 d28924 d28904
                        omega
                      have d29093 : (x 13 13).toNat = 1 := by
                        have r29094 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29095 := hb (x 11 2)
                        have b29096 := hb (x 13 13)
                        have b29097 := hb (x 12 1 && x 12 14)
                        clear * - r29094 b29095 b29096 b29097 d29077 d29085
                        omega
                      have d29098 : (x 14 12).toNat = 0 := by
                        have r29099 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29100 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                        have e29101 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                        have b29102 := hb (x 11 3)
                        have b29103 := hb (x 12 2)
                        have b29104 := hb (x 13 13)
                        have b29105 := hb (x 14 12)
                        clear * - r29099 e29100 e29101 b29102 b29103 b29104 b29105 d29093 d29081
                        omega
                      have d29106 : (x 11 3).toNat = 0 := by
                        have r29107 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29108 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
                        have e29109 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
                        have b29110 := hb (x 11 3)
                        have b29111 := hb (x 12 2)
                        have b29112 := hb (x 13 13)
                        have b29113 := hb (x 14 12)
                        clear * - r29107 e29108 e29109 b29110 b29111 b29112 b29113 d29098 d29093 d29081
                        omega
                      have d29114 : (x 11 3 && x 11 14).toNat = 0 := by
                        have r29115 := hand1 (x 11 3) (x 11 14)
                        have b29116 := hb (x 11 3)
                        have b29117 := hb (x 11 3 && x 11 14)
                        clear * - r29115 b29116 b29117 d29106
                        omega
                      have d29118 : (x 14 11).toNat = 1 := by
                        have r29119 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29120 := hb (x 10 4)
                        have b29121 := hb (x 14 11)
                        have b29122 := hb (x 13 1 && x 13 12)
                        have b29123 := hb (x 12 2 && x 12 13)
                        have b29124 := hb (x 11 3 && x 11 14)
                        clear * - r29119 b29120 b29121 b29122 b29123 b29124 d28916 d28932 d29114 d28881
                        omega
                      have d29125 : (x 14 3).toNat = 1 := by
                        have r29126 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
                        have b29127 := hb (x 14 3)
                        have b29128 := hb (x 14 11)
                        clear * - r29126 b29127 b29128 d29118
                        omega
                      have d29129 : (x 17 12).toNat = 0 := by
                        have r29130 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29131 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                        have e29132 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                        have b29133 := hb (x 14 3)
                        have b29134 := hb (x 15 2)
                        have b29135 := hb (x 16 13)
                        have b29136 := hb (x 17 12)
                        clear * - r29130 e29131 e29132 b29133 b29134 b29135 b29136 d29125
                        omega
                      have d29137 : (x 16 13).toNat = 0 := by
                        have r29138 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29139 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                        have e29140 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                        have b29141 := hb (x 14 3)
                        have b29142 := hb (x 15 2)
                        have b29143 := hb (x 16 13)
                        have b29144 := hb (x 17 12)
                        clear * - r29138 e29139 e29140 b29141 b29142 b29143 b29144 d29129 d29125
                        omega
                      have d29145 : (x 15 1 && x 15 14).toNat = 1 := by
                        have r29146 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29147 := hb (x 14 2)
                        have b29148 := hb (x 16 13)
                        have b29149 := hb (x 15 1 && x 15 14)
                        clear * - r29146 b29147 b29148 b29149 d29137 d29040
                        omega
                      have d29150 : (x 15 14).toNat = 1 := by
                        have r29151 := hand2 (x 15 1) (x 15 14)
                        have b29152 := hb (x 15 14)
                        have b29153 := hb (x 15 1 && x 15 14)
                        clear * - r29151 b29152 b29153 d29145
                        omega
                      have d29154 : (x 14 1).toNat = 0 := by
                        have r29155 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b29156 := hb (x 14 1)
                        have b29157 := hb (x 15 14)
                        clear * - r29155 b29156 b29157 d29150
                        omega
                      have d29158 : (x 14 1 && x 14 11).toNat = 0 := by
                        have r29159 := hand1 (x 14 1) (x 14 11)
                        have b29160 := hb (x 14 1)
                        have b29161 := hb (x 14 1 && x 14 11)
                        clear * - r29159 b29160 b29161 d29154
                        omega
                      have d29162 : (x 15 2).toNat = 0 := by
                        have r29163 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e29164 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
                        have e29165 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
                        have b29166 := hb (x 14 3)
                        have b29167 := hb (x 15 2)
                        have b29168 := hb (x 16 13)
                        have b29169 := hb (x 17 12)
                        clear * - r29163 e29164 e29165 b29166 b29167 b29168 b29169 d29129 d29137 d29125
                        omega
                      have d29170 : (x 15 10).toNat = 0 := by
                        have r29171 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
                        have b29172 := hb (x 15 2)
                        have b29173 := hb (x 15 10)
                        clear * - r29171 b29172 b29173 d29162
                        omega
                      have r29174 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b29175 := hb (x 10 5)
                      have b29176 := hb (x 15 10)
                      have b29177 := hb (x 14 1 && x 14 11)
                      have b29178 := hb (x 13 2 && x 13 12)
                      have b29179 := hb (x 12 3 && x 12 13)
                      have b29180 := hb (x 11 4 && x 11 14)
                      linarith only [r29174, b29175, b29176, b29177, b29178, b29179, b29180, d29170, d29158, d28920, d28936, d29065, d28957]
                  · have f29181 : (x (-1) 14).toNat = 1 := by rw [h27697]; rfl
                    have d29182 : (x (-2) 1).toNat = 0 := by
                      have r29183 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b29184 := hb (x (-2) 1)
                      have b29185 := hb (x (-1) 14)
                      clear * - r29183 b29184 b29185 f29181
                      omega
                    have d29186 : (x (-2) 9).toNat = 0 := by
                      have r29187 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                      have b29188 := hb (x (-2) 1)
                      have b29189 := hb (x (-2) 9)
                      clear * - r29187 b29188 b29189 d29182
                      omega
                    have r29190 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r29191 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r29192 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r29193 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r29194 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r29195 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
                    have r29196 := hand2 (x 6 1) (x 6 7)
                    have r29197 := hand2 (x 5 2) (x 5 8)
                    have r29198 := hand2 (x 4 3) (x 4 9)
                    have r29199 := hand2 (x 6 1) (x 6 10)
                    have r29200 := hand2 (x 5 2) (x 5 11)
                    have r29201 := hand1 (x 12 1) (x 12 12)
                    have r29202 := hand1 (x 11 2) (x 11 13)
                    have r29203 := hand1 (x 10 3) (x 10 14)
                    linarith only [r29190, r29191, r29192, r29193, r29194, r29195, r29196, r29197, r29198, r29199, r29200, r29201, r29202, r29203, d29186, f29181, g21, g26, g29, g34, d27624, d27657, g92, g93, g94, g95, d27608, d27665, g117, g118]
                · have f29251 : (x 1 8).toNat = 1 := by rw [h27695]; rfl
                  have d29252 : (x (-3) 4).toNat = 0 := by
                    have r29253 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29254 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e29255 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e29256 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e29257 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e29258 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e29259 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b29260 := hb (x (-6) 7)
                    have b29261 := hb (x (-5) 6)
                    have b29262 := hb (x (-4) 5)
                    have b29263 := hb (x (-3) 4)
                    have b29264 := hb (x (-2) 11)
                    have b29265 := hb (x (-1) 10)
                    have b29266 := hb (x 0 9)
                    have b29267 := hb (x 1 8)
                    clear * - r29253 e29254 e29255 e29256 e29257 e29258 e29259 b29260 b29261 b29262 b29263 b29264 b29265 b29266 b29267 f29251 f27686 g11 g7
                    omega
                  have d29268 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
                    have r29269 := hand1 (x (-3) 4) (x (-3) 9)
                    have b29270 := hb (x (-3) 4)
                    have b29271 := hb (x (-3) 4 && x (-3) 9)
                    clear * - r29269 b29270 b29271 d29252
                    omega
                  have d29272 : (x (-4) 5).toNat = 0 := by
                    have r29273 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29274 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e29275 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e29276 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e29277 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e29278 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e29279 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b29280 := hb (x (-6) 7)
                    have b29281 := hb (x (-5) 6)
                    have b29282 := hb (x (-4) 5)
                    have b29283 := hb (x (-3) 4)
                    have b29284 := hb (x (-2) 11)
                    have b29285 := hb (x (-1) 10)
                    have b29286 := hb (x 0 9)
                    have b29287 := hb (x 1 8)
                    clear * - r29273 e29274 e29275 e29276 e29277 e29278 e29279 b29280 b29281 b29282 b29283 b29284 b29285 b29286 b29287 f29251 f27686 g11 g7 d29252
                    omega
                  have d29288 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
                    have r29289 := hand1 (x (-4) 5) (x (-4) 12)
                    have b29290 := hb (x (-4) 5)
                    have b29291 := hb (x (-4) 5 && x (-4) 12)
                    clear * - r29289 b29290 b29291 d29272
                    omega
                  have d29292 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
                    have r29293 := hand1 (x (-4) 5) (x (-4) 10)
                    have b29294 := hb (x (-4) 5)
                    have b29295 := hb (x (-4) 5 && x (-4) 10)
                    clear * - r29293 b29294 b29295 d29272
                    omega
                  have d29296 : (x (-5) 6).toNat = 0 := by
                    have r29297 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29298 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e29299 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e29300 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e29301 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e29302 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e29303 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b29304 := hb (x (-6) 7)
                    have b29305 := hb (x (-5) 6)
                    have b29306 := hb (x (-4) 5)
                    have b29307 := hb (x (-3) 4)
                    have b29308 := hb (x (-2) 11)
                    have b29309 := hb (x (-1) 10)
                    have b29310 := hb (x 0 9)
                    have b29311 := hb (x 1 8)
                    clear * - r29297 e29298 e29299 e29300 e29301 e29302 e29303 b29304 b29305 b29306 b29307 b29308 b29309 b29310 b29311 f29251 f27686 g11 g7 d29252 d29272
                    omega
                  have d29312 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
                    have r29313 := hand1 (x (-5) 6) (x (-5) 13)
                    have b29314 := hb (x (-5) 6)
                    have b29315 := hb (x (-5) 6 && x (-5) 13)
                    clear * - r29313 b29314 b29315 d29296
                    omega
                  have d29316 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
                    have r29317 := hand1 (x (-5) 6) (x (-5) 11)
                    have b29318 := hb (x (-5) 6)
                    have b29319 := hb (x (-5) 6 && x (-5) 11)
                    clear * - r29317 b29318 b29319 d29296
                    omega
                  have d29320 : (x (-6) 7).toNat = 0 := by
                    have r29321 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29322 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
                    have e29323 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
                    have e29324 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
                    have e29325 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
                    have e29326 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
                    have e29327 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
                    have b29328 := hb (x (-6) 7)
                    have b29329 := hb (x (-5) 6)
                    have b29330 := hb (x (-4) 5)
                    have b29331 := hb (x (-3) 4)
                    have b29332 := hb (x (-2) 11)
                    have b29333 := hb (x (-1) 10)
                    have b29334 := hb (x 0 9)
                    have b29335 := hb (x 1 8)
                    clear * - r29321 e29322 e29323 e29324 e29325 e29326 e29327 b29328 b29329 b29330 b29331 b29332 b29333 b29334 b29335 f29251 f27686 g11 g7 d29252 d29272 d29296
                    omega
                  have d29336 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
                    have r29337 := hand1 (x (-6) 7) (x (-6) 14)
                    have b29338 := hb (x (-6) 7)
                    have b29339 := hb (x (-6) 7 && x (-6) 14)
                    clear * - r29337 b29338 b29339 d29320
                    omega
                  have d29340 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
                    have r29341 := hand1 (x (-6) 7) (x (-6) 12)
                    have b29342 := hb (x (-6) 7)
                    have b29343 := hb (x (-6) 7 && x (-6) 12)
                    clear * - r29341 b29342 b29343 d29320
                    omega
                  have d29344 : (x (-7) 8).toNat = 1 := by
                    have r29345 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29346 := hb (x (-7) 8)
                    have b29347 := hb (x 1 7)
                    have b29348 := hb (x 0 1 && x 0 8)
                    have b29349 := hb (x (-1) 2 && x (-1) 9)
                    have b29350 := hb (x (-2) 3 && x (-2) 10)
                    have b29351 := hb (x (-3) 4 && x (-3) 11)
                    have b29352 := hb (x (-4) 5 && x (-4) 12)
                    have b29353 := hb (x (-5) 6 && x (-5) 13)
                    have b29354 := hb (x (-6) 7 && x (-6) 14)
                    clear * - r29345 b29346 b29347 b29348 b29349 b29350 b29351 b29352 b29353 b29354 f27605 g96 g97 g98 g99 d29288 d29312 d29336
                    omega
                  have d29355 : (x (-8) 9).toNat = 0 := by
                    have r29356 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29357 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                    have e29358 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                    have e29359 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                    have e29360 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                    have e29361 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                    have e29362 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                    have b29363 := hb (x (-14) 7)
                    have b29364 := hb (x (-13) 6)
                    have b29365 := hb (x (-12) 5)
                    have b29366 := hb (x (-11) 4)
                    have b29367 := hb (x (-10) 11)
                    have b29368 := hb (x (-9) 10)
                    have b29369 := hb (x (-8) 9)
                    have b29370 := hb (x (-7) 8)
                    clear * - r29356 e29357 e29358 e29359 e29360 e29361 e29362 b29363 b29364 b29365 b29366 b29367 b29368 b29369 b29370 d29344
                    omega
                  have d29371 : (x (-8) 9 && x (-8) 14).toNat = 0 := by
                    have r29372 := hand1 (x (-8) 9) (x (-8) 14)
                    have b29373 := hb (x (-8) 9)
                    have b29374 := hb (x (-8) 9 && x (-8) 14)
                    clear * - r29372 b29373 b29374 d29355
                    omega
                  have d29375 : (x (-9) 10).toNat = 0 := by
                    have r29376 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29377 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                    have e29378 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                    have e29379 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                    have e29380 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                    have e29381 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                    have e29382 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                    have b29383 := hb (x (-14) 7)
                    have b29384 := hb (x (-13) 6)
                    have b29385 := hb (x (-12) 5)
                    have b29386 := hb (x (-11) 4)
                    have b29387 := hb (x (-10) 11)
                    have b29388 := hb (x (-9) 10)
                    have b29389 := hb (x (-8) 9)
                    have b29390 := hb (x (-7) 8)
                    clear * - r29376 e29377 e29378 e29379 e29380 e29381 e29382 b29383 b29384 b29385 b29386 b29387 b29388 b29389 b29390 d29344 d29355
                    omega
                  have d29391 : (x (-7) 8 && x (-7) 13).toNat = 1 := by
                    have r29392 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29393 := hb (x (-9) 10)
                    have b29394 := hb (x 1 5)
                    have b29395 := hb (x 0 1 && x 0 6)
                    have b29396 := hb (x (-1) 2 && x (-1) 7)
                    have b29397 := hb (x (-2) 3 && x (-2) 8)
                    have b29398 := hb (x (-3) 4 && x (-3) 9)
                    have b29399 := hb (x (-4) 5 && x (-4) 10)
                    have b29400 := hb (x (-5) 6 && x (-5) 11)
                    have b29401 := hb (x (-6) 7 && x (-6) 12)
                    have b29402 := hb (x (-7) 8 && x (-7) 13)
                    have b29403 := hb (x (-8) 9 && x (-8) 14)
                    clear * - r29392 b29393 b29394 b29395 b29396 b29397 b29398 b29399 b29400 b29401 b29402 b29403 g25 g67 g68 g69 d29268 d29292 d29316 d29340 d29371 d29375
                    omega
                  have d29404 : (x (-7) 13).toNat = 1 := by
                    have r29405 := hand2 (x (-7) 8) (x (-7) 13)
                    have b29406 := hb (x (-7) 13)
                    have b29407 := hb (x (-7) 8 && x (-7) 13)
                    clear * - r29405 b29406 b29407 d29391
                    omega
                  have d29408 : (x (-7) 1).toNat = 1 := by
                    have r29409 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
                    have b29410 := hb (x (-7) 1)
                    have b29411 := hb (x (-7) 13)
                    clear * - r29409 b29410 b29411 d29404
                    omega
                  have d29412 : (x (-6) 14).toNat = 0 := by
                    have r29413 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29414 := hb (x (-7) 1)
                    have b29415 := hb (x (-6) 14)
                    clear * - r29413 b29414 b29415 d29408
                    omega
                  have d29416 : (x (-6) 6).toNat = 0 := by
                    have r29417 : (x (-6) 6).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp6 (-6))
                    have b29418 := hb (x (-6) 6)
                    have b29419 := hb (x (-6) 14)
                    clear * - r29417 b29418 b29419 d29412
                    omega
                  have d29420 : (x (-6) 2).toNat = 0 := by
                    have r29421 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
                    have b29422 := hb (x (-6) 2)
                    have b29423 := hb (x (-6) 14)
                    clear * - r29421 b29422 b29423 d29412
                    omega
                  have d29424 : (x (-6) 10).toNat = 0 := by
                    have r29425 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                    have b29426 := hb (x (-6) 2)
                    have b29427 := hb (x (-6) 10)
                    clear * - r29425 b29426 b29427 d29420
                    omega
                  have d29428 : (x (-6) 12).toNat = 0 := by
                    have r29429 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29430 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                    have e29431 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                    have b29432 := hb (x (-9) 3)
                    have b29433 := hb (x (-8) 2)
                    have b29434 := hb (x (-7) 13)
                    have b29435 := hb (x (-6) 12)
                    clear * - r29429 e29430 e29431 b29432 b29433 b29434 b29435 d29404
                    omega
                  have d29436 : (x (-6) 8 && x (-6) 12).toNat = 0 := by
                    have r29437 := hand2 (x (-6) 8) (x (-6) 12)
                    have b29438 := hb (x (-6) 12)
                    have b29439 := hb (x (-6) 8 && x (-6) 12)
                    clear * - r29437 b29438 b29439 d29428
                    omega
                  have d29440 : (x (-8) 2).toNat = 0 := by
                    have r29441 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29442 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                    have e29443 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                    have b29444 := hb (x (-9) 3)
                    have b29445 := hb (x (-8) 2)
                    have b29446 := hb (x (-7) 13)
                    have b29447 := hb (x (-6) 12)
                    clear * - r29441 e29442 e29443 b29444 b29445 b29446 b29447 d29428 d29404
                    omega
                  have d29448 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
                    have r29449 := hand1 (x (-8) 2) (x (-8) 12)
                    have b29450 := hb (x (-8) 2)
                    have b29451 := hb (x (-8) 2 && x (-8) 12)
                    clear * - r29449 b29450 b29451 d29440
                    omega
                  have d29452 : (x (-8) 10).toNat = 0 := by
                    have r29453 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
                    have b29454 := hb (x (-8) 2)
                    have b29455 := hb (x (-8) 10)
                    clear * - r29453 b29454 b29455 d29440
                    omega
                  have d29456 : (x (-9) 3).toNat = 0 := by
                    have r29457 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29458 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                    have e29459 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                    have b29460 := hb (x (-9) 3)
                    have b29461 := hb (x (-8) 2)
                    have b29462 := hb (x (-7) 13)
                    have b29463 := hb (x (-6) 12)
                    clear * - r29457 e29458 e29459 b29460 b29461 b29462 b29463 d29428 d29404 d29440
                    omega
                  have d29464 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
                    have r29465 := hand1 (x (-9) 3) (x (-9) 13)
                    have b29466 := hb (x (-9) 3)
                    have b29467 := hb (x (-9) 3 && x (-9) 13)
                    clear * - r29465 b29466 b29467 d29456
                    omega
                  have d29468 : (x (-9) 11).toNat = 0 := by
                    have r29469 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
                    have b29470 := hb (x (-9) 3)
                    have b29471 := hb (x (-9) 11)
                    clear * - r29469 b29470 b29471 d29456
                    omega
                  have d29472 : (x (-7) 9 && x (-7) 13).toNat = 1 := by
                    have r29473 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29474 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
                    have e29475 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
                    have b29476 := hb (x (-9) 11)
                    have b29477 := hb (x (-8) 10)
                    have b29478 := hb (x 1 5)
                    have b29479 := hb (x 2 4)
                    have b29480 := hb (x 0 2 && x 0 6)
                    have b29481 := hb (x (-1) 3 && x (-1) 7)
                    have b29482 := hb (x (-2) 4 && x (-2) 8)
                    have b29483 := hb (x (-3) 5 && x (-3) 9)
                    have b29484 := hb (x (-4) 6 && x (-4) 10)
                    have b29485 := hb (x (-5) 7 && x (-5) 11)
                    have b29486 := hb (x (-6) 8 && x (-6) 12)
                    have b29487 := hb (x (-7) 9 && x (-7) 13)
                    clear * - r29473 e29474 e29475 b29476 b29477 b29478 b29479 b29480 b29481 b29482 b29483 b29484 b29485 b29486 b29487 g30 g25 g37 g38 g39 g40 g41 g42 d29436 d29452 d29468
                    omega
                  have d29488 : (x (-7) 9).toNat = 1 := by
                    have r29489 := hand1 (x (-7) 9) (x (-7) 13)
                    have b29490 := hb (x (-7) 9)
                    have b29491 := hb (x (-7) 9 && x (-7) 13)
                    clear * - r29489 b29490 b29491 d29472
                    omega
                  have d29492 : (x (-6) 8).toNat = 0 := by
                    have r29493 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29494 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                    have e29495 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                    have e29496 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                    have e29497 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                    have e29498 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                    have e29499 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                    have b29500 := hb (x (-13) 7)
                    have b29501 := hb (x (-12) 6)
                    have b29502 := hb (x (-11) 5)
                    have b29503 := hb (x (-10) 4)
                    have b29504 := hb (x (-9) 11)
                    have b29505 := hb (x (-8) 10)
                    have b29506 := hb (x (-7) 9)
                    have b29507 := hb (x (-6) 8)
                    clear * - r29493 e29494 e29495 e29496 e29497 e29498 e29499 b29500 b29501 b29502 b29503 b29504 b29505 b29506 b29507 d29488 d29452 d29468
                    omega
                  have d29508 : (x (-10) 4).toNat = 0 := by
                    have r29509 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29510 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                    have e29511 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                    have e29512 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                    have e29513 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                    have e29514 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                    have e29515 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                    have b29516 := hb (x (-13) 7)
                    have b29517 := hb (x (-12) 6)
                    have b29518 := hb (x (-11) 5)
                    have b29519 := hb (x (-10) 4)
                    have b29520 := hb (x (-9) 11)
                    have b29521 := hb (x (-8) 10)
                    have b29522 := hb (x (-7) 9)
                    have b29523 := hb (x (-6) 8)
                    clear * - r29509 e29510 e29511 e29512 e29513 e29514 e29515 b29516 b29517 b29518 b29519 b29520 b29521 b29522 b29523 d29492 d29488 d29452 d29468
                    omega
                  have d29524 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
                    have r29525 := hand1 (x (-10) 4) (x (-10) 14)
                    have b29526 := hb (x (-10) 4)
                    have b29527 := hb (x (-10) 4 && x (-10) 14)
                    clear * - r29525 b29526 b29527 d29508
                    omega
                  have d29528 : (x (-11) 5).toNat = 0 := by
                    have r29529 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29530 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                    have e29531 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                    have e29532 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                    have e29533 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                    have e29534 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                    have e29535 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                    have b29536 := hb (x (-13) 7)
                    have b29537 := hb (x (-12) 6)
                    have b29538 := hb (x (-11) 5)
                    have b29539 := hb (x (-10) 4)
                    have b29540 := hb (x (-9) 11)
                    have b29541 := hb (x (-8) 10)
                    have b29542 := hb (x (-7) 9)
                    have b29543 := hb (x (-6) 8)
                    clear * - r29529 e29530 e29531 e29532 e29533 e29534 e29535 b29536 b29537 b29538 b29539 b29540 b29541 b29542 b29543 d29492 d29488 d29452 d29468 d29508
                    omega
                  have d29544 : (x (-7) 1 && x (-7) 11).toNat = 1 := by
                    have r29545 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29546 := hb (x (-11) 5)
                    have b29547 := hb (x (-6) 10)
                    have b29548 := hb (x (-7) 1 && x (-7) 11)
                    have b29549 := hb (x (-8) 2 && x (-8) 12)
                    have b29550 := hb (x (-9) 3 && x (-9) 13)
                    have b29551 := hb (x (-10) 4 && x (-10) 14)
                    clear * - r29545 b29546 b29547 b29548 b29549 b29550 b29551 d29424 d29448 d29464 d29524 d29528
                    omega
                  have d29552 : (x (-7) 11).toNat = 1 := by
                    have r29553 := hand2 (x (-7) 1) (x (-7) 11)
                    have b29554 := hb (x (-7) 11)
                    have b29555 := hb (x (-7) 1 && x (-7) 11)
                    clear * - r29553 b29554 b29555 d29544
                    omega
                  have d29556 : (x (-7) 3).toNat = 1 := by
                    have r29557 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                    have b29558 := hb (x (-7) 3)
                    have b29559 := hb (x (-7) 11)
                    clear * - r29557 b29558 b29559 d29552
                    omega
                  have d29560 : (x (-4) 12).toNat = 0 := by
                    have r29561 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e29562 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                    have e29563 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                    have b29564 := hb (x (-7) 3)
                    have b29565 := hb (x (-6) 2)
                    have b29566 := hb (x (-5) 13)
                    have b29567 := hb (x (-4) 12)
                    clear * - r29561 e29562 e29563 b29564 b29565 b29566 b29567 d29420 d29556
                    omega
                  have d29568 : (x (-4) 4).toNat = 0 := by
                    have r29569 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
                    have b29570 := hb (x (-4) 4)
                    have b29571 := hb (x (-4) 12)
                    clear * - r29569 b29570 b29571 d29560
                    omega
                  have d29572 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
                    have r29573 := hand1 (x (-4) 4) (x (-4) 13)
                    have b29574 := hb (x (-4) 4)
                    have b29575 := hb (x (-4) 4 && x (-4) 13)
                    clear * - r29573 b29574 b29575 d29568
                    omega
                  have d29576 : (x (-5) 5 && x (-5) 14).toNat = 1 := by
                    have r29577 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b29578 := hb (x (-6) 6)
                    have b29579 := hb (x 0 9)
                    have b29580 := hb (x (-1) 1 && x (-1) 10)
                    have b29581 := hb (x (-2) 2 && x (-2) 11)
                    have b29582 := hb (x (-3) 3 && x (-3) 12)
                    have b29583 := hb (x (-4) 4 && x (-4) 13)
                    have b29584 := hb (x (-5) 5 && x (-5) 14)
                    clear * - r29577 b29578 b29579 b29580 b29581 b29582 b29583 b29584 f27686 g111 g112 g113 d29572 d29416
                    omega
                  have d29585 : (x (-5) 5).toNat = 1 := by
                    have r29586 := hand1 (x (-5) 5) (x (-5) 14)
                    have b29587 := hb (x (-5) 5)
                    have b29588 := hb (x (-5) 5 && x (-5) 14)
                    clear * - r29586 b29587 b29588 d29576
                    omega
                  have d29589 : (x (-5) 13).toNat = 1 := by
                    have r29590 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
                    have b29591 := hb (x (-5) 5)
                    have b29592 := hb (x (-5) 13)
                    clear * - r29590 b29591 b29592 d29585
                    omega
                  have r29593 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29594 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e29595 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b29596 := hb (x (-7) 3)
                  have b29597 := hb (x (-6) 2)
                  have b29598 := hb (x (-5) 13)
                  have b29599 := hb (x (-4) 12)
                  linarith only [r29593, e29594, e29595, b29596, b29597, b29598, b29599, d29560, d29589, d29420, d29556]
              · have f29600 : (x (-1) 7).toNat = 1 := by rw [h27693]; rfl
                have d29601 : (x 6 8).toNat = 0 := by
                  have r29602 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29603 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e29604 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e29605 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e29606 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e29607 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e29608 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b29609 := hb (x (-1) 7)
                  have b29610 := hb (x 0 6)
                  have b29611 := hb (x 1 5)
                  have b29612 := hb (x 2 4)
                  have b29613 := hb (x 3 11)
                  have b29614 := hb (x 4 10)
                  have b29615 := hb (x 5 9)
                  have b29616 := hb (x 6 8)
                  clear * - r29602 e29603 e29604 e29605 e29606 e29607 e29608 b29609 b29610 b29611 b29612 b29613 b29614 b29615 b29616 d27649 g30 g25 g17 f29600
                  omega
                have d29617 : (x 5 9).toNat = 0 := by
                  have r29618 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29619 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                  have e29620 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                  have e29621 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                  have e29622 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                  have e29623 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                  have e29624 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                  have b29625 := hb (x (-1) 7)
                  have b29626 := hb (x 0 6)
                  have b29627 := hb (x 1 5)
                  have b29628 := hb (x 2 4)
                  have b29629 := hb (x 3 11)
                  have b29630 := hb (x 4 10)
                  have b29631 := hb (x 5 9)
                  have b29632 := hb (x 6 8)
                  clear * - r29618 e29619 e29620 e29621 e29622 e29623 e29624 b29625 b29626 b29627 b29628 b29629 b29630 b29631 b29632 d29601 d27649 g30 g25 g17 f29600
                  omega
                have d29633 : (x 3 2 && x 3 11).toNat = 1 := by
                  have r29634 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29635 := hb (x (-1) 6)
                  have b29636 := hb (x 5 9)
                  have b29637 := hb (x 4 1 && x 4 10)
                  have b29638 := hb (x 3 2 && x 3 11)
                  have b29639 := hb (x 2 3 && x 2 12)
                  have b29640 := hb (x 1 4 && x 1 13)
                  have b29641 := hb (x 0 5 && x 0 14)
                  clear * - r29634 b29635 b29636 b29637 b29638 b29639 b29640 b29641 d29617 d27653 g114 g115 g116 f27692
                  omega
                have d29642 : (x 3 11).toNat = 1 := by
                  have r29643 := hand2 (x 3 2) (x 3 11)
                  have b29644 := hb (x 3 11)
                  have b29645 := hb (x 3 2 && x 3 11)
                  clear * - r29643 b29644 b29645 d29633
                  omega
                have r29646 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e29647 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e29648 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e29649 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e29650 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e29651 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e29652 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b29653 := hb (x (-1) 7)
                have b29654 := hb (x 0 6)
                have b29655 := hb (x 1 5)
                have b29656 := hb (x 2 4)
                have b29657 := hb (x 3 11)
                have b29658 := hb (x 4 10)
                have b29659 := hb (x 5 9)
                have b29660 := hb (x 6 8)
                linarith only [r29646, e29647, e29648, e29649, e29650, e29651, e29652, b29653, b29654, b29655, b29656, b29657, b29658, b29659, b29660, d29601, d29617, d27649, d29642, g30, g25, g17, f29600]
            · have f29661 : (x (-1) 6).toNat = 1 := by rw [h27691]; rfl
              have d29662 : (x (-1) 14).toNat = 1 := by
                have r29663 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
                have b29664 := hb (x (-1) 6)
                have b29665 := hb (x (-1) 14)
                clear * - r29663 b29664 b29665 f29661
                omega
              have d29666 : (x (-2) 1).toNat = 0 := by
                have r29667 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b29668 := hb (x (-2) 1)
                have b29669 := hb (x (-1) 14)
                clear * - r29667 b29668 b29669 d29662
                omega
              have d29670 : (x (-2) 9).toNat = 0 := by
                have r29671 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                have b29672 := hb (x (-2) 1)
                have b29673 := hb (x (-2) 9)
                clear * - r29671 b29672 b29673 d29666
                omega
              have d29674 : (x 5 8).toNat = 0 := by
                have r29675 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e29676 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e29677 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e29678 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e29679 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e29680 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e29681 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b29682 := hb (x (-2) 7)
                have b29683 := hb (x (-1) 6)
                have b29684 := hb (x 0 5)
                have b29685 := hb (x 1 4)
                have b29686 := hb (x 2 11)
                have b29687 := hb (x 3 10)
                have b29688 := hb (x 4 9)
                have b29689 := hb (x 5 8)
                clear * - r29675 e29676 e29677 e29678 e29679 e29680 e29681 b29682 b29683 b29684 b29685 b29686 b29687 b29688 b29689 g24 g16 f29661
                omega
              have d29690 : (x 5 2 && x 5 8).toNat = 0 := by
                have r29691 := hand2 (x 5 2) (x 5 8)
                have b29692 := hb (x 5 8)
                have b29693 := hb (x 5 2 && x 5 8)
                clear * - r29691 b29692 b29693 d29674
                omega
              have d29694 : (x 4 9).toNat = 0 := by
                have r29695 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e29696 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e29697 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e29698 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e29699 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e29700 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e29701 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b29702 := hb (x (-2) 7)
                have b29703 := hb (x (-1) 6)
                have b29704 := hb (x 0 5)
                have b29705 := hb (x 1 4)
                have b29706 := hb (x 2 11)
                have b29707 := hb (x 3 10)
                have b29708 := hb (x 4 9)
                have b29709 := hb (x 5 8)
                clear * - r29695 e29696 e29697 e29698 e29699 e29700 e29701 b29702 b29703 b29704 b29705 b29706 b29707 b29708 b29709 d29674 g24 g16 f29661
                omega
              have d29710 : (x 4 3 && x 4 9).toNat = 0 := by
                have r29711 := hand2 (x 4 3) (x 4 9)
                have b29712 := hb (x 4 9)
                have b29713 := hb (x 4 3 && x 4 9)
                clear * - r29711 b29712 b29713 d29694
                omega
              have d29714 : (x 3 10).toNat = 0 := by
                have r29715 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e29716 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e29717 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e29718 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e29719 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e29720 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e29721 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b29722 := hb (x (-2) 7)
                have b29723 := hb (x (-1) 6)
                have b29724 := hb (x 0 5)
                have b29725 := hb (x 1 4)
                have b29726 := hb (x 2 11)
                have b29727 := hb (x 3 10)
                have b29728 := hb (x 4 9)
                have b29729 := hb (x 5 8)
                clear * - r29715 e29716 e29717 e29718 e29719 e29720 e29721 b29722 b29723 b29724 b29725 b29726 b29727 b29728 b29729 d29674 d29694 g24 g16 f29661
                omega
              have d29730 : (x 2 11).toNat = 0 := by
                have r29731 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e29732 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                have e29733 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                have e29734 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                have e29735 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                have e29736 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                have e29737 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                have b29738 := hb (x (-2) 7)
                have b29739 := hb (x (-1) 6)
                have b29740 := hb (x 0 5)
                have b29741 := hb (x 1 4)
                have b29742 := hb (x 2 11)
                have b29743 := hb (x 3 10)
                have b29744 := hb (x 4 9)
                have b29745 := hb (x 5 8)
                clear * - r29731 e29732 e29733 e29734 e29735 e29736 e29737 b29738 b29739 b29740 b29741 b29742 b29743 b29744 b29745 d29674 d29694 d29714 g24 g16 f29661
                omega
              have r29746 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r29747 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r29748 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r29749 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r29750 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r29751 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
              have r29752 := hand2 (x 6 1) (x 6 7)
              have r29753 := hand2 (x 6 1) (x 6 10)
              have r29754 := hand2 (x 5 2) (x 5 11)
              have r29755 := hand1 (x 12 1) (x 12 12)
              have r29756 := hand1 (x 11 2) (x 11 13)
              have r29757 := hand1 (x 10 3) (x 10 14)
              linarith only [r29746, r29747, r29748, r29749, r29750, r29751, r29752, r29753, r29754, r29755, r29756, r29757, d29670, d29662, g21, g26, g29, d29730, g34, d29714, d27624, d29694, d27657, d29674, d29690, d29710, g92, g93, g94, g95, d27608, d27665, g117, g118]
          · have f29805 : (x 0 9).toNat = 1 := by rw [h27685]; rfl
            have d29806 : (x 1 8).toNat = 0 := by
              have r29807 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e29808 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e29809 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e29810 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e29811 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e29812 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e29813 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b29814 := hb (x (-6) 7)
              have b29815 := hb (x (-5) 6)
              have b29816 := hb (x (-4) 5)
              have b29817 := hb (x (-3) 4)
              have b29818 := hb (x (-2) 11)
              have b29819 := hb (x (-1) 10)
              have b29820 := hb (x 0 9)
              have b29821 := hb (x 1 8)
              clear * - r29807 e29808 e29809 e29810 e29811 e29812 e29813 b29814 b29815 b29816 b29817 b29818 b29819 b29820 b29821 f29805 g11 g7
              omega
            have d29822 : (x (-3) 4).toNat = 0 := by
              have r29823 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e29824 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e29825 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e29826 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e29827 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e29828 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e29829 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b29830 := hb (x (-6) 7)
              have b29831 := hb (x (-5) 6)
              have b29832 := hb (x (-4) 5)
              have b29833 := hb (x (-3) 4)
              have b29834 := hb (x (-2) 11)
              have b29835 := hb (x (-1) 10)
              have b29836 := hb (x 0 9)
              have b29837 := hb (x 1 8)
              clear * - r29823 e29824 e29825 e29826 e29827 e29828 e29829 b29830 b29831 b29832 b29833 b29834 b29835 b29836 b29837 d29806 f29805 g11 g7
              omega
            have d29838 : (x (-3) 4 && x (-3) 9).toNat = 0 := by
              have r29839 := hand1 (x (-3) 4) (x (-3) 9)
              have b29840 := hb (x (-3) 4)
              have b29841 := hb (x (-3) 4 && x (-3) 9)
              clear * - r29839 b29840 b29841 d29822
              omega
            have d29842 : (x (-4) 5).toNat = 0 := by
              have r29843 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e29844 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e29845 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e29846 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e29847 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e29848 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e29849 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b29850 := hb (x (-6) 7)
              have b29851 := hb (x (-5) 6)
              have b29852 := hb (x (-4) 5)
              have b29853 := hb (x (-3) 4)
              have b29854 := hb (x (-2) 11)
              have b29855 := hb (x (-1) 10)
              have b29856 := hb (x 0 9)
              have b29857 := hb (x 1 8)
              clear * - r29843 e29844 e29845 e29846 e29847 e29848 e29849 b29850 b29851 b29852 b29853 b29854 b29855 b29856 b29857 d29806 f29805 g11 g7 d29822
              omega
            have d29858 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
              have r29859 := hand1 (x (-4) 5) (x (-4) 12)
              have b29860 := hb (x (-4) 5)
              have b29861 := hb (x (-4) 5 && x (-4) 12)
              clear * - r29859 b29860 b29861 d29842
              omega
            have d29862 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
              have r29863 := hand1 (x (-4) 5) (x (-4) 10)
              have b29864 := hb (x (-4) 5)
              have b29865 := hb (x (-4) 5 && x (-4) 10)
              clear * - r29863 b29864 b29865 d29842
              omega
            have d29866 : (x (-5) 6).toNat = 0 := by
              have r29867 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e29868 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e29869 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e29870 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e29871 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e29872 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e29873 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b29874 := hb (x (-6) 7)
              have b29875 := hb (x (-5) 6)
              have b29876 := hb (x (-4) 5)
              have b29877 := hb (x (-3) 4)
              have b29878 := hb (x (-2) 11)
              have b29879 := hb (x (-1) 10)
              have b29880 := hb (x 0 9)
              have b29881 := hb (x 1 8)
              clear * - r29867 e29868 e29869 e29870 e29871 e29872 e29873 b29874 b29875 b29876 b29877 b29878 b29879 b29880 b29881 d29806 f29805 g11 g7 d29822 d29842
              omega
            have d29882 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
              have r29883 := hand1 (x (-5) 6) (x (-5) 13)
              have b29884 := hb (x (-5) 6)
              have b29885 := hb (x (-5) 6 && x (-5) 13)
              clear * - r29883 b29884 b29885 d29866
              omega
            have d29886 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
              have r29887 := hand1 (x (-5) 6) (x (-5) 11)
              have b29888 := hb (x (-5) 6)
              have b29889 := hb (x (-5) 6 && x (-5) 11)
              clear * - r29887 b29888 b29889 d29866
              omega
            have d29890 : (x (-6) 7).toNat = 0 := by
              have r29891 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e29892 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
              have e29893 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
              have e29894 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
              have e29895 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
              have e29896 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
              have e29897 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
              have b29898 := hb (x (-6) 7)
              have b29899 := hb (x (-5) 6)
              have b29900 := hb (x (-4) 5)
              have b29901 := hb (x (-3) 4)
              have b29902 := hb (x (-2) 11)
              have b29903 := hb (x (-1) 10)
              have b29904 := hb (x 0 9)
              have b29905 := hb (x 1 8)
              clear * - r29891 e29892 e29893 e29894 e29895 e29896 e29897 b29898 b29899 b29900 b29901 b29902 b29903 b29904 b29905 d29806 f29805 g11 g7 d29822 d29842 d29866
              omega
            have d29906 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
              have r29907 := hand1 (x (-6) 7) (x (-6) 14)
              have b29908 := hb (x (-6) 7)
              have b29909 := hb (x (-6) 7 && x (-6) 14)
              clear * - r29907 b29908 b29909 d29890
              omega
            have d29910 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
              have r29911 := hand1 (x (-6) 7) (x (-6) 12)
              have b29912 := hb (x (-6) 7)
              have b29913 := hb (x (-6) 7 && x (-6) 12)
              clear * - r29911 b29912 b29913 d29890
              omega
            have d29914 : (x (-7) 8).toNat = 1 := by
              have r29915 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b29916 := hb (x (-7) 8)
              have b29917 := hb (x 1 7)
              have b29918 := hb (x 0 1 && x 0 8)
              have b29919 := hb (x (-1) 2 && x (-1) 9)
              have b29920 := hb (x (-2) 3 && x (-2) 10)
              have b29921 := hb (x (-3) 4 && x (-3) 11)
              have b29922 := hb (x (-4) 5 && x (-4) 12)
              have b29923 := hb (x (-5) 6 && x (-5) 13)
              have b29924 := hb (x (-6) 7 && x (-6) 14)
              clear * - r29915 b29916 b29917 b29918 b29919 b29920 b29921 b29922 b29923 b29924 f27605 g96 g97 g98 g99 d29858 d29882 d29906
              omega
            have d29925 : (x (-8) 9).toNat = 0 := by
              have r29926 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e29927 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e29928 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e29929 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e29930 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e29931 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e29932 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have b29933 := hb (x (-14) 7)
              have b29934 := hb (x (-13) 6)
              have b29935 := hb (x (-12) 5)
              have b29936 := hb (x (-11) 4)
              have b29937 := hb (x (-10) 11)
              have b29938 := hb (x (-9) 10)
              have b29939 := hb (x (-8) 9)
              have b29940 := hb (x (-7) 8)
              clear * - r29926 e29927 e29928 e29929 e29930 e29931 e29932 b29933 b29934 b29935 b29936 b29937 b29938 b29939 b29940 d29914
              omega
            have d29941 : (x (-8) 9 && x (-8) 14).toNat = 0 := by
              have r29942 := hand1 (x (-8) 9) (x (-8) 14)
              have b29943 := hb (x (-8) 9)
              have b29944 := hb (x (-8) 9 && x (-8) 14)
              clear * - r29942 b29943 b29944 d29925
              omega
            have d29945 : (x (-9) 10).toNat = 0 := by
              have r29946 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e29947 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
              have e29948 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
              have e29949 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
              have e29950 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
              have e29951 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
              have e29952 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
              have b29953 := hb (x (-14) 7)
              have b29954 := hb (x (-13) 6)
              have b29955 := hb (x (-12) 5)
              have b29956 := hb (x (-11) 4)
              have b29957 := hb (x (-10) 11)
              have b29958 := hb (x (-9) 10)
              have b29959 := hb (x (-8) 9)
              have b29960 := hb (x (-7) 8)
              clear * - r29946 e29947 e29948 e29949 e29950 e29951 e29952 b29953 b29954 b29955 b29956 b29957 b29958 b29959 b29960 d29914 d29925
              omega
            have d29961 : (x (-7) 8 && x (-7) 13).toNat = 1 := by
              have r29962 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b29963 := hb (x (-9) 10)
              have b29964 := hb (x 1 5)
              have b29965 := hb (x 0 1 && x 0 6)
              have b29966 := hb (x (-1) 2 && x (-1) 7)
              have b29967 := hb (x (-2) 3 && x (-2) 8)
              have b29968 := hb (x (-3) 4 && x (-3) 9)
              have b29969 := hb (x (-4) 5 && x (-4) 10)
              have b29970 := hb (x (-5) 6 && x (-5) 11)
              have b29971 := hb (x (-6) 7 && x (-6) 12)
              have b29972 := hb (x (-7) 8 && x (-7) 13)
              have b29973 := hb (x (-8) 9 && x (-8) 14)
              clear * - r29962 b29963 b29964 b29965 b29966 b29967 b29968 b29969 b29970 b29971 b29972 b29973 g25 g67 g68 g69 d29838 d29862 d29886 d29910 d29941 d29945
              omega
            have d29974 : (x (-7) 13).toNat = 1 := by
              have r29975 := hand2 (x (-7) 8) (x (-7) 13)
              have b29976 := hb (x (-7) 13)
              have b29977 := hb (x (-7) 8 && x (-7) 13)
              clear * - r29975 b29976 b29977 d29961
              omega
            have d29978 : (x (-7) 1).toNat = 1 := by
              have r29979 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
              have b29980 := hb (x (-7) 1)
              have b29981 := hb (x (-7) 13)
              clear * - r29979 b29980 b29981 d29974
              omega
            have d29982 : (x (-6) 14).toNat = 0 := by
              have r29983 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b29984 := hb (x (-7) 1)
              have b29985 := hb (x (-6) 14)
              clear * - r29983 b29984 b29985 d29978
              omega
            have d29986 : (x (-6) 2).toNat = 0 := by
              have r29987 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
              have b29988 := hb (x (-6) 2)
              have b29989 := hb (x (-6) 14)
              clear * - r29987 b29988 b29989 d29982
              omega
            have d29990 : (x (-6) 10).toNat = 0 := by
              have r29991 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
              have b29992 := hb (x (-6) 2)
              have b29993 := hb (x (-6) 10)
              clear * - r29991 b29992 b29993 d29986
              omega
            have d29994 : (x (-6) 12).toNat = 0 := by
              have r29995 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e29996 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e29997 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b29998 := hb (x (-9) 3)
              have b29999 := hb (x (-8) 2)
              have b30000 := hb (x (-7) 13)
              have b30001 := hb (x (-6) 12)
              clear * - r29995 e29996 e29997 b29998 b29999 b30000 b30001 d29974
              omega
            have d30002 : (x (-6) 8 && x (-6) 12).toNat = 0 := by
              have r30003 := hand2 (x (-6) 8) (x (-6) 12)
              have b30004 := hb (x (-6) 12)
              have b30005 := hb (x (-6) 8 && x (-6) 12)
              clear * - r30003 b30004 b30005 d29994
              omega
            have d30006 : (x (-8) 2).toNat = 0 := by
              have r30007 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30008 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e30009 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b30010 := hb (x (-9) 3)
              have b30011 := hb (x (-8) 2)
              have b30012 := hb (x (-7) 13)
              have b30013 := hb (x (-6) 12)
              clear * - r30007 e30008 e30009 b30010 b30011 b30012 b30013 d29994 d29974
              omega
            have d30014 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
              have r30015 := hand1 (x (-8) 2) (x (-8) 12)
              have b30016 := hb (x (-8) 2)
              have b30017 := hb (x (-8) 2 && x (-8) 12)
              clear * - r30015 b30016 b30017 d30006
              omega
            have d30018 : (x (-8) 10).toNat = 0 := by
              have r30019 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
              have b30020 := hb (x (-8) 2)
              have b30021 := hb (x (-8) 10)
              clear * - r30019 b30020 b30021 d30006
              omega
            have d30022 : (x (-9) 3).toNat = 0 := by
              have r30023 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30024 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e30025 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have b30026 := hb (x (-9) 3)
              have b30027 := hb (x (-8) 2)
              have b30028 := hb (x (-7) 13)
              have b30029 := hb (x (-6) 12)
              clear * - r30023 e30024 e30025 b30026 b30027 b30028 b30029 d29994 d29974 d30006
              omega
            have d30030 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
              have r30031 := hand1 (x (-9) 3) (x (-9) 13)
              have b30032 := hb (x (-9) 3)
              have b30033 := hb (x (-9) 3 && x (-9) 13)
              clear * - r30031 b30032 b30033 d30022
              omega
            have d30034 : (x (-9) 11).toNat = 0 := by
              have r30035 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
              have b30036 := hb (x (-9) 3)
              have b30037 := hb (x (-9) 11)
              clear * - r30035 b30036 b30037 d30022
              omega
            have d30038 : (x (-7) 9 && x (-7) 13).toNat = 1 := by
              have r30039 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30040 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
              have e30041 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
              have b30042 := hb (x (-9) 11)
              have b30043 := hb (x (-8) 10)
              have b30044 := hb (x 1 5)
              have b30045 := hb (x 2 4)
              have b30046 := hb (x 0 2 && x 0 6)
              have b30047 := hb (x (-1) 3 && x (-1) 7)
              have b30048 := hb (x (-2) 4 && x (-2) 8)
              have b30049 := hb (x (-3) 5 && x (-3) 9)
              have b30050 := hb (x (-4) 6 && x (-4) 10)
              have b30051 := hb (x (-5) 7 && x (-5) 11)
              have b30052 := hb (x (-6) 8 && x (-6) 12)
              have b30053 := hb (x (-7) 9 && x (-7) 13)
              clear * - r30039 e30040 e30041 b30042 b30043 b30044 b30045 b30046 b30047 b30048 b30049 b30050 b30051 b30052 b30053 g30 g25 g37 g38 g39 g40 g41 g42 d30002 d30018 d30034
              omega
            have d30054 : (x (-7) 9).toNat = 1 := by
              have r30055 := hand1 (x (-7) 9) (x (-7) 13)
              have b30056 := hb (x (-7) 9)
              have b30057 := hb (x (-7) 9 && x (-7) 13)
              clear * - r30055 b30056 b30057 d30038
              omega
            have d30058 : (x (-6) 8).toNat = 0 := by
              have r30059 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30060 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
              have e30061 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
              have e30062 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
              have e30063 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
              have e30064 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
              have e30065 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
              have b30066 := hb (x (-13) 7)
              have b30067 := hb (x (-12) 6)
              have b30068 := hb (x (-11) 5)
              have b30069 := hb (x (-10) 4)
              have b30070 := hb (x (-9) 11)
              have b30071 := hb (x (-8) 10)
              have b30072 := hb (x (-7) 9)
              have b30073 := hb (x (-6) 8)
              clear * - r30059 e30060 e30061 e30062 e30063 e30064 e30065 b30066 b30067 b30068 b30069 b30070 b30071 b30072 b30073 d30054 d30018 d30034
              omega
            have d30074 : (x (-10) 4).toNat = 0 := by
              have r30075 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30076 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
              have e30077 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
              have e30078 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
              have e30079 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
              have e30080 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
              have e30081 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
              have b30082 := hb (x (-13) 7)
              have b30083 := hb (x (-12) 6)
              have b30084 := hb (x (-11) 5)
              have b30085 := hb (x (-10) 4)
              have b30086 := hb (x (-9) 11)
              have b30087 := hb (x (-8) 10)
              have b30088 := hb (x (-7) 9)
              have b30089 := hb (x (-6) 8)
              clear * - r30075 e30076 e30077 e30078 e30079 e30080 e30081 b30082 b30083 b30084 b30085 b30086 b30087 b30088 b30089 d30058 d30054 d30018 d30034
              omega
            have d30090 : (x (-10) 4 && x (-10) 14).toNat = 0 := by
              have r30091 := hand1 (x (-10) 4) (x (-10) 14)
              have b30092 := hb (x (-10) 4)
              have b30093 := hb (x (-10) 4 && x (-10) 14)
              clear * - r30091 b30092 b30093 d30074
              omega
            have d30094 : (x (-11) 5).toNat = 0 := by
              have r30095 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30096 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
              have e30097 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
              have e30098 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
              have e30099 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
              have e30100 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
              have e30101 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
              have b30102 := hb (x (-13) 7)
              have b30103 := hb (x (-12) 6)
              have b30104 := hb (x (-11) 5)
              have b30105 := hb (x (-10) 4)
              have b30106 := hb (x (-9) 11)
              have b30107 := hb (x (-8) 10)
              have b30108 := hb (x (-7) 9)
              have b30109 := hb (x (-6) 8)
              clear * - r30095 e30096 e30097 e30098 e30099 e30100 e30101 b30102 b30103 b30104 b30105 b30106 b30107 b30108 b30109 d30058 d30054 d30018 d30034 d30074
              omega
            have d30110 : (x (-7) 1 && x (-7) 11).toNat = 1 := by
              have r30111 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b30112 := hb (x (-11) 5)
              have b30113 := hb (x (-6) 10)
              have b30114 := hb (x (-7) 1 && x (-7) 11)
              have b30115 := hb (x (-8) 2 && x (-8) 12)
              have b30116 := hb (x (-9) 3 && x (-9) 13)
              have b30117 := hb (x (-10) 4 && x (-10) 14)
              clear * - r30111 b30112 b30113 b30114 b30115 b30116 b30117 d29990 d30014 d30030 d30090 d30094
              omega
            have d30118 : (x (-7) 11).toNat = 1 := by
              have r30119 := hand2 (x (-7) 1) (x (-7) 11)
              have b30120 := hb (x (-7) 11)
              have b30121 := hb (x (-7) 1 && x (-7) 11)
              clear * - r30119 b30120 b30121 d30110
              omega
            have d30122 : (x (-7) 3).toNat = 1 := by
              have r30123 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
              have b30124 := hb (x (-7) 3)
              have b30125 := hb (x (-7) 11)
              clear * - r30123 b30124 b30125 d30118
              omega
            have d30126 : (x (-4) 12).toNat = 0 := by
              have r30127 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30128 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e30129 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b30130 := hb (x (-7) 3)
              have b30131 := hb (x (-6) 2)
              have b30132 := hb (x (-5) 13)
              have b30133 := hb (x (-4) 12)
              clear * - r30127 e30128 e30129 b30130 b30131 b30132 b30133 d29986 d30122
              omega
            have d30134 : (x (-5) 13).toNat = 0 := by
              have r30135 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30136 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e30137 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b30138 := hb (x (-7) 3)
              have b30139 := hb (x (-6) 2)
              have b30140 := hb (x (-5) 13)
              have b30141 := hb (x (-4) 12)
              clear * - r30135 e30136 e30137 b30138 b30139 b30140 b30141 d30126 d29986 d30122
              omega
            have r30142 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30143 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30144 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e30145 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e30146 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e30147 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e30148 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e30149 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have r30150 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30151 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e30152 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have r30153 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30154 := hand2 (x 6 1) (x 6 10)
            have r30155 := hand2 (x 5 2) (x 5 11)
            have b30172 := hb (x 7 1)
            linarith only [r30142, r30143, e30144, e30145, e30146, e30147, e30148, e30149, r30150, e30151, e30152, r30153, r30154, r30155, b30172, d29982, d30134, d30126, g3, g6, g10, g19, g26, f27605, d27673, d27665, g117, g118]
        · have f30182 : (x 2 1).toNat = 1 := by rw [h27618]; rfl
          have d30183 : (x 3 14).toNat = 0 := by
            have r30184 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b30185 := hb (x 2 1)
            have b30186 := hb (x 3 14)
            clear * - r30184 b30185 b30186 f30182
            omega
          have d30187 : (x 3 1 && x 3 14).toNat = 0 := by
            have r30188 := hand2 (x 3 1) (x 3 14)
            have b30189 := hb (x 3 14)
            have b30190 := hb (x 3 1 && x 3 14)
            clear * - r30188 b30189 b30190 d30183
            omega
          have d30191 : (x 3 2).toNat = 0 := by
            have r30192 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b30193 := hb (x 3 2)
            have b30194 := hb (x 3 14)
            clear * - r30192 b30193 b30194 d30183
            omega
          have d30195 : (x 3 10).toNat = 0 := by
            have r30196 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
            have b30197 := hb (x 3 2)
            have b30198 := hb (x 3 10)
            clear * - r30196 b30197 b30198 d30191
            omega
          cases h30199 : x (-1) 6
          · have f30200 : (x (-1) 6).toNat = 0 := by rw [h30199]; rfl
            cases h30201 : x (-1) 14
            · have f30202 : (x (-1) 14).toNat = 0 := by rw [h30201]; rfl
              cases h30203 : x 2 2
              · have f30204 : (x 2 2).toNat = 0 := by rw [h30203]; rfl
                have d30205 : (x 4 13).toNat = 1 := by
                  have r30206 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30207 := hb (x 2 2)
                  have b30208 := hb (x 4 13)
                  have b30209 := hb (x 3 1 && x 3 14)
                  clear * - r30206 b30207 b30208 b30209 d30187 f30204
                  omega
                have d30210 : (x 4 1).toNat = 1 := by
                  have r30211 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                  have b30212 := hb (x 4 1)
                  have b30213 := hb (x 4 13)
                  clear * - r30211 b30212 b30213 d30205
                  omega
                have d30214 : (x 5 14).toNat = 0 := by
                  have r30215 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30216 := hb (x 4 1)
                  have b30217 := hb (x 5 14)
                  clear * - r30215 b30216 b30217 d30210
                  omega
                have d30218 : (x 5 1 && x 5 14).toNat = 0 := by
                  have r30219 := hand2 (x 5 1) (x 5 14)
                  have b30220 := hb (x 5 14)
                  have b30221 := hb (x 5 1 && x 5 14)
                  clear * - r30219 b30220 b30221 d30214
                  omega
                have d30222 : (x 5 3 && x 5 14).toNat = 0 := by
                  have r30223 := hand2 (x 5 3) (x 5 14)
                  have b30224 := hb (x 5 14)
                  have b30225 := hb (x 5 3 && x 5 14)
                  clear * - r30223 b30224 b30225 d30214
                  omega
                have d30226 : (x 5 6).toNat = 0 := by
                  have r30227 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
                  have b30228 := hb (x 5 6)
                  have b30229 := hb (x 5 14)
                  clear * - r30227 b30228 b30229 d30214
                  omega
                have d30230 : (x 5 6 && x 5 11).toNat = 0 := by
                  have r30231 := hand1 (x 5 6) (x 5 11)
                  have b30232 := hb (x 5 6)
                  have b30233 := hb (x 5 6 && x 5 11)
                  clear * - r30231 b30232 b30233 d30226
                  omega
                have d30234 : (x 5 2).toNat = 0 := by
                  have r30235 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                  have b30236 := hb (x 5 2)
                  have b30237 := hb (x 5 14)
                  clear * - r30235 b30236 b30237 d30214
                  omega
                have d30238 : (x 5 10).toNat = 0 := by
                  have r30239 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                  have b30240 := hb (x 5 2)
                  have b30241 := hb (x 5 10)
                  clear * - r30239 b30240 b30241 d30234
                  omega
                have d30242 : (x 5 3 && x 5 10).toNat = 0 := by
                  have r30243 := hand2 (x 5 3) (x 5 10)
                  have b30244 := hb (x 5 10)
                  have b30245 := hb (x 5 3 && x 5 10)
                  clear * - r30243 b30244 b30245 d30238
                  omega
                have d30246 : (x 4 1 && x 4 11).toNat = 1 := by
                  have r30247 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30248 := hb (x 0 5)
                  have b30249 := hb (x 5 10)
                  have b30250 := hb (x 4 1 && x 4 11)
                  have b30251 := hb (x 3 2 && x 3 12)
                  have b30252 := hb (x 2 3 && x 2 13)
                  have b30253 := hb (x 1 4 && x 1 14)
                  clear * - r30247 b30248 b30249 b30250 b30251 b30252 b30253 d30238 g121 g122 g123 g16
                  omega
                have d30254 : (x 4 11).toNat = 1 := by
                  have r30255 := hand2 (x 4 1) (x 4 11)
                  have b30256 := hb (x 4 11)
                  have b30257 := hb (x 4 1 && x 4 11)
                  clear * - r30255 b30256 b30257 d30246
                  omega
                have d30258 : (x 4 3).toNat = 1 := by
                  have r30259 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                  have b30260 := hb (x 4 3)
                  have b30261 := hb (x 4 11)
                  clear * - r30259 b30260 b30261 d30254
                  omega
                have d30262 : (x 7 12).toNat = 0 := by
                  have r30263 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30264 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                  have e30265 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                  have b30266 := hb (x 4 3)
                  have b30267 := hb (x 5 2)
                  have b30268 := hb (x 6 13)
                  have b30269 := hb (x 7 12)
                  clear * - r30263 e30264 e30265 b30266 b30267 b30268 b30269 d30234 d30258
                  omega
                have d30270 : (x 7 1 && x 7 12).toNat = 0 := by
                  have r30271 := hand2 (x 7 1) (x 7 12)
                  have b30272 := hb (x 7 12)
                  have b30273 := hb (x 7 1 && x 7 12)
                  clear * - r30271 b30272 b30273 d30262
                  omega
                have d30274 : (x 7 4).toNat = 0 := by
                  have r30275 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                  have b30276 := hb (x 7 4)
                  have b30277 := hb (x 7 12)
                  clear * - r30275 b30276 b30277 d30262
                  omega
                have d30278 : (x 7 4 && x 7 13).toNat = 0 := by
                  have r30279 := hand1 (x 7 4) (x 7 13)
                  have b30280 := hb (x 7 4)
                  have b30281 := hb (x 7 4 && x 7 13)
                  clear * - r30279 b30280 b30281 d30274
                  omega
                have d30282 : (x 7 4 && x 7 9).toNat = 0 := by
                  have r30283 := hand1 (x 7 4) (x 7 9)
                  have b30284 := hb (x 7 4)
                  have b30285 := hb (x 7 4 && x 7 9)
                  clear * - r30283 b30284 b30285 d30274
                  omega
                have d30286 : (x 6 13).toNat = 0 := by
                  have r30287 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30288 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                  have e30289 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                  have b30290 := hb (x 4 3)
                  have b30291 := hb (x 5 2)
                  have b30292 := hb (x 6 13)
                  have b30293 := hb (x 7 12)
                  clear * - r30287 e30288 e30289 b30290 b30291 b30292 b30293 d30262 d30234 d30258
                  omega
                have d30294 : (x 6 2 && x 6 13).toNat = 0 := by
                  have r30295 := hand2 (x 6 2) (x 6 13)
                  have b30296 := hb (x 6 13)
                  have b30297 := hb (x 6 2 && x 6 13)
                  clear * - r30295 b30296 b30297 d30286
                  omega
                have d30298 : (x 6 5).toNat = 0 := by
                  have r30299 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
                  have b30300 := hb (x 6 5)
                  have b30301 := hb (x 6 13)
                  clear * - r30299 b30300 b30301 d30286
                  omega
                have d30302 : (x 6 5 && x 6 14).toNat = 0 := by
                  have r30303 := hand1 (x 6 5) (x 6 14)
                  have b30304 := hb (x 6 5)
                  have b30305 := hb (x 6 5 && x 6 14)
                  clear * - r30303 b30304 b30305 d30298
                  omega
                have d30306 : (x 6 5 && x 6 10).toNat = 0 := by
                  have r30307 := hand1 (x 6 5) (x 6 10)
                  have b30308 := hb (x 6 5)
                  have b30309 := hb (x 6 5 && x 6 10)
                  clear * - r30307 b30308 b30309 d30298
                  omega
                have d30310 : (x 4 2).toNat = 1 := by
                  have r30311 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30312 := hb (x 4 2)
                  have b30313 := hb (x 6 13)
                  have b30314 := hb (x 5 1 && x 5 14)
                  clear * - r30311 b30312 b30313 b30314 d30286 d30218
                  omega
                have d30315 : (x 4 14).toNat = 1 := by
                  have r30316 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
                  have b30317 := hb (x 4 2)
                  have b30318 := hb (x 4 14)
                  clear * - r30316 b30317 b30318 d30310
                  omega
                have d30319 : (x 3 1).toNat = 0 := by
                  have r30320 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30321 := hb (x 3 1)
                  have b30322 := hb (x 4 14)
                  clear * - r30320 b30321 b30322 d30315
                  omega
                have d30323 : (x 3 13).toNat = 0 := by
                  have r30324 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
                  have b30325 := hb (x 3 1)
                  have b30326 := hb (x 3 13)
                  clear * - r30324 b30325 b30326 d30319
                  omega
                have d30327 : (x 3 5).toNat = 0 := by
                  have r30328 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                  have b30329 := hb (x 3 5)
                  have b30330 := hb (x 3 13)
                  clear * - r30328 b30329 b30330 d30323
                  omega
                have d30331 : (x 7 8).toNat = 0 := by
                  have r30332 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30333 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                  have e30334 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                  have e30335 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                  have e30336 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                  have e30337 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                  have e30338 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                  have b30339 := hb (x 0 7)
                  have b30340 := hb (x 1 6)
                  have b30341 := hb (x 2 5)
                  have b30342 := hb (x 3 4)
                  have b30343 := hb (x 4 11)
                  have b30344 := hb (x 5 10)
                  have b30345 := hb (x 6 9)
                  have b30346 := hb (x 7 8)
                  clear * - r30332 e30333 e30334 e30335 e30336 e30337 e30338 b30339 b30340 b30341 b30342 b30343 b30344 b30345 b30346 d30238 d30254 g35 g31 g26 g18
                  omega
                have d30347 : (x 7 1 && x 7 8).toNat = 0 := by
                  have r30348 := hand2 (x 7 1) (x 7 8)
                  have b30349 := hb (x 7 8)
                  have b30350 := hb (x 7 1 && x 7 8)
                  clear * - r30348 b30349 b30350 d30331
                  omega
                have d30351 : (x 6 9).toNat = 0 := by
                  have r30352 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30353 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
                  have e30354 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
                  have e30355 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
                  have e30356 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
                  have e30357 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
                  have e30358 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
                  have b30359 := hb (x 0 7)
                  have b30360 := hb (x 1 6)
                  have b30361 := hb (x 2 5)
                  have b30362 := hb (x 3 4)
                  have b30363 := hb (x 4 11)
                  have b30364 := hb (x 5 10)
                  have b30365 := hb (x 6 9)
                  have b30366 := hb (x 7 8)
                  clear * - r30352 e30353 e30354 e30355 e30356 e30357 e30358 b30359 b30360 b30361 b30362 b30363 b30364 b30365 b30366 d30331 d30238 d30254 g35 g31 g26 g18
                  omega
                have d30367 : (x 6 2 && x 6 9).toNat = 0 := by
                  have r30368 := hand2 (x 6 2) (x 6 9)
                  have b30369 := hb (x 6 9)
                  have b30370 := hb (x 6 2 && x 6 9)
                  clear * - r30368 b30369 b30370 d30351
                  omega
                cases h30371 : x 2 6
                · have f30372 : (x 2 6).toNat = 0 := by rw [h30371]; rfl
                  have r30373 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30374 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                  have e30375 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                  have e30376 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                  have e30377 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                  have e30378 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                  have e30379 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                  have r30380 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30381 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                  have e30382 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                  have e30383 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                  have e30384 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                  have e30385 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                  have e30386 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                  have r30387 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30388 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                  have e30389 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                  have e30390 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                  have e30391 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                  have e30392 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                  have e30393 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                  have r30394 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30395 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                  have e30396 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                  have r30397 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30398 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e30399 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have r30400 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30401 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                  have e30402 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                  have r30403 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30404 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
                  have e30405 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
                  have r30406 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30407 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                  have e30408 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                  have r30409 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r30410 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r30411 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r30412 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r30413 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r30414 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                  have r30415 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                  have r30416 := hand2 (x (-6) 8) (x (-6) 12)
                  have r30417 := hand2 (x (-7) 9) (x (-7) 13)
                  have r30418 := hand1 (x 6 2) (x 6 6)
                  have r30419 := hand1 (x 5 3) (x 5 7)
                  have r30420 := hand1 (x (-6) 8) (x (-6) 14)
                  have r30421 := hand2 (x 5 1) (x 5 7)
                  have r30422 := hand1 (x (-2) 8) (x (-2) 14)
                  have r30423 := hand2 (x 10 1) (x 10 10)
                  have r30424 := hand2 (x 9 2) (x 9 11)
                  have r30425 := hand2 (x 8 3) (x 8 12)
                  have r30426 := hand2 (x (-7) 1) (x (-7) 11)
                  have r30427 := hand1 (x (-8) 2) (x (-8) 12)
                  have r30428 := hand1 (x (-9) 3) (x (-9) 13)
                  have r30429 := hand1 (x (-10) 4) (x (-10) 14)
                  have r30430 := hand2 (x (-4) 2) (x (-4) 12)
                  have r30431 := hand2 (x (-5) 3) (x (-5) 13)
                  have r30432 := hand1 (x (-6) 4) (x (-6) 14)
                  linarith only [r30373, e30374, e30375, e30376, e30377, e30378, e30379, r30380, e30381, e30382, e30383, e30384, e30385, e30386, r30387, e30388, e30389, e30390, e30391, e30392, e30393, r30394, e30395, e30396, r30397, e30398, e30399, r30400, e30401, e30402, r30403, e30404, e30405, r30406, e30407, e30408, r30409, r30410, r30411, r30412, r30413, r30414, r30415, r30416, r30417, r30418, r30419, r30420, r30421, r30422, r30423, r30424, r30425, r30426, r30427, r30428, r30429, r30430, r30431, r30432, g3, g6, g25, g30, f30372, d30226, g37, g38, g39, g40, g41, g42, g57, g58, g59, g60, g61, g62, g79, g80, g81, g82, g83, g84, g85, g86, g87, g88, g89, g90, g91, d30278, d30302, g119]
                · have f30522 : (x 2 6).toNat = 1 := by rw [h30371]; rfl
                  have d30523 : (x 8 8).toNat = 0 := by
                    have r30524 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30525 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e30526 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e30527 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e30528 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e30529 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e30530 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b30531 := hb (x 1 7)
                    have b30532 := hb (x 2 6)
                    have b30533 := hb (x 3 5)
                    have b30534 := hb (x 4 4)
                    have b30535 := hb (x 5 11)
                    have b30536 := hb (x 6 10)
                    have b30537 := hb (x 7 9)
                    have b30538 := hb (x 8 8)
                    clear * - r30524 e30525 e30526 e30527 e30528 e30529 e30530 b30531 b30532 b30533 b30534 b30535 b30536 b30537 b30538 d30327 f30522 f27605
                    omega
                  have d30539 : (x 8 3 && x 8 8).toNat = 0 := by
                    have r30540 := hand2 (x 8 3) (x 8 8)
                    have b30541 := hb (x 8 8)
                    have b30542 := hb (x 8 3 && x 8 8)
                    clear * - r30540 b30541 b30542 d30523
                    omega
                  have d30543 : (x 8 4 && x 8 8).toNat = 0 := by
                    have r30544 := hand2 (x 8 4) (x 8 8)
                    have b30545 := hb (x 8 8)
                    have b30546 := hb (x 8 4 && x 8 8)
                    clear * - r30544 b30545 b30546 d30523
                    omega
                  have d30547 : (x 7 9).toNat = 0 := by
                    have r30548 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30549 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e30550 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e30551 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e30552 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e30553 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e30554 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b30555 := hb (x 1 7)
                    have b30556 := hb (x 2 6)
                    have b30557 := hb (x 3 5)
                    have b30558 := hb (x 4 4)
                    have b30559 := hb (x 5 11)
                    have b30560 := hb (x 6 10)
                    have b30561 := hb (x 7 9)
                    have b30562 := hb (x 8 8)
                    clear * - r30548 e30549 e30550 e30551 e30552 e30553 e30554 b30555 b30556 b30557 b30558 b30559 b30560 b30561 b30562 d30523 d30327 f30522 f27605
                    omega
                  have d30563 : (x 7 5 && x 7 9).toNat = 0 := by
                    have r30564 := hand2 (x 7 5) (x 7 9)
                    have b30565 := hb (x 7 9)
                    have b30566 := hb (x 7 5 && x 7 9)
                    clear * - r30564 b30565 b30566 d30547
                    omega
                  have d30567 : (x 6 10).toNat = 0 := by
                    have r30568 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30569 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e30570 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e30571 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e30572 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e30573 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e30574 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b30575 := hb (x 1 7)
                    have b30576 := hb (x 2 6)
                    have b30577 := hb (x 3 5)
                    have b30578 := hb (x 4 4)
                    have b30579 := hb (x 5 11)
                    have b30580 := hb (x 6 10)
                    have b30581 := hb (x 7 9)
                    have b30582 := hb (x 8 8)
                    clear * - r30568 e30569 e30570 e30571 e30572 e30573 e30574 b30575 b30576 b30577 b30578 b30579 b30580 b30581 b30582 d30523 d30547 d30327 f30522 f27605
                    omega
                  have d30583 : (x 6 6 && x 6 10).toNat = 0 := by
                    have r30584 := hand2 (x 6 6) (x 6 10)
                    have b30585 := hb (x 6 10)
                    have b30586 := hb (x 6 6 && x 6 10)
                    clear * - r30584 b30585 b30586 d30567
                    omega
                  have d30587 : (x 5 11).toNat = 0 := by
                    have r30588 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30589 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e30590 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e30591 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e30592 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e30593 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e30594 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b30595 := hb (x 1 7)
                    have b30596 := hb (x 2 6)
                    have b30597 := hb (x 3 5)
                    have b30598 := hb (x 4 4)
                    have b30599 := hb (x 5 11)
                    have b30600 := hb (x 6 10)
                    have b30601 := hb (x 7 9)
                    have b30602 := hb (x 8 8)
                    clear * - r30588 e30589 e30590 e30591 e30592 e30593 e30594 b30595 b30596 b30597 b30598 b30599 b30600 b30601 b30602 d30523 d30547 d30567 d30327 f30522 f27605
                    omega
                  have d30603 : (x 5 7 && x 5 11).toNat = 0 := by
                    have r30604 := hand2 (x 5 7) (x 5 11)
                    have b30605 := hb (x 5 11)
                    have b30606 := hb (x 5 7 && x 5 11)
                    clear * - r30604 b30605 b30606 d30587
                    omega
                  have d30607 : (x 4 4).toNat = 0 := by
                    have r30608 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30609 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e30610 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e30611 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e30612 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e30613 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e30614 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b30615 := hb (x 1 7)
                    have b30616 := hb (x 2 6)
                    have b30617 := hb (x 3 5)
                    have b30618 := hb (x 4 4)
                    have b30619 := hb (x 5 11)
                    have b30620 := hb (x 6 10)
                    have b30621 := hb (x 7 9)
                    have b30622 := hb (x 8 8)
                    clear * - r30608 e30609 e30610 e30611 e30612 e30613 e30614 b30615 b30616 b30617 b30618 b30619 b30620 b30621 b30622 d30523 d30547 d30567 d30587 d30327 f30522 f27605
                    omega
                  have d30623 : (x 4 4 && x 4 11).toNat = 0 := by
                    have r30624 := hand1 (x 4 4) (x 4 11)
                    have b30625 := hb (x 4 4)
                    have b30626 := hb (x 4 4 && x 4 11)
                    clear * - r30624 b30625 b30626 d30607
                    omega
                  have d30627 : (x 8 11).toNat = 1 := by
                    have r30628 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b30629 := hb (x 4 4)
                    have b30630 := hb (x 8 11)
                    have b30631 := hb (x 7 1 && x 7 12)
                    have b30632 := hb (x 6 2 && x 6 13)
                    have b30633 := hb (x 5 3 && x 5 14)
                    clear * - r30628 b30629 b30630 b30631 b30632 b30633 d30270 d30294 d30222 d30607
                    omega
                  have d30634 : (x 8 3).toNat = 1 := by
                    have r30635 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
                    have b30636 := hb (x 8 3)
                    have b30637 := hb (x 8 11)
                    clear * - r30635 b30636 b30637 d30627
                    omega
                  have d30638 : (x 11 12).toNat = 0 := by
                    have r30639 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30640 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e30641 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b30642 := hb (x 8 3)
                    have b30643 := hb (x 9 2)
                    have b30644 := hb (x 10 13)
                    have b30645 := hb (x 11 12)
                    clear * - r30639 e30640 e30641 b30642 b30643 b30644 b30645 d30634
                    omega
                  have d30646 : (x 11 4).toNat = 0 := by
                    have r30647 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
                    have b30648 := hb (x 11 4)
                    have b30649 := hb (x 11 12)
                    clear * - r30647 b30648 b30649 d30638
                    omega
                  have d30650 : (x 11 4 && x 11 13).toNat = 0 := by
                    have r30651 := hand1 (x 11 4) (x 11 13)
                    have b30652 := hb (x 11 4)
                    have b30653 := hb (x 11 4 && x 11 13)
                    clear * - r30651 b30652 b30653 d30646
                    omega
                  have d30654 : (x 10 13).toNat = 0 := by
                    have r30655 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30656 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e30657 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b30658 := hb (x 8 3)
                    have b30659 := hb (x 9 2)
                    have b30660 := hb (x 10 13)
                    have b30661 := hb (x 11 12)
                    clear * - r30655 e30656 e30657 b30658 b30659 b30660 b30661 d30638 d30634
                    omega
                  have d30662 : (x 10 5).toNat = 0 := by
                    have r30663 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
                    have b30664 := hb (x 10 5)
                    have b30665 := hb (x 10 13)
                    clear * - r30663 b30664 b30665 d30654
                    omega
                  have d30666 : (x 10 5 && x 10 14).toNat = 0 := by
                    have r30667 := hand1 (x 10 5) (x 10 14)
                    have b30668 := hb (x 10 5)
                    have b30669 := hb (x 10 5 && x 10 14)
                    clear * - r30667 b30668 b30669 d30662
                    omega
                  have d30670 : (x 9 2).toNat = 0 := by
                    have r30671 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30672 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
                    have e30673 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
                    have b30674 := hb (x 8 3)
                    have b30675 := hb (x 9 2)
                    have b30676 := hb (x 10 13)
                    have b30677 := hb (x 11 12)
                    clear * - r30671 e30672 e30673 b30674 b30675 b30676 b30677 d30638 d30654 d30634
                    omega
                  have d30678 : (x 9 2 && x 9 7).toNat = 0 := by
                    have r30679 := hand1 (x 9 2) (x 9 7)
                    have b30680 := hb (x 9 2)
                    have b30681 := hb (x 9 2 && x 9 7)
                    clear * - r30679 b30680 b30681 d30670
                    omega
                  have d30682 : (x 9 10).toNat = 0 := by
                    have r30683 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
                    have b30684 := hb (x 9 2)
                    have b30685 := hb (x 9 10)
                    clear * - r30683 b30684 b30685 d30670
                    omega
                  have d30686 : (x 11 8).toNat = 0 := by
                    have r30687 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30688 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                    have e30689 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                    have e30690 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                    have e30691 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                    have e30692 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                    have e30693 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                    have b30694 := hb (x 4 7)
                    have b30695 := hb (x 5 6)
                    have b30696 := hb (x 6 5)
                    have b30697 := hb (x 7 4)
                    have b30698 := hb (x 8 11)
                    have b30699 := hb (x 9 10)
                    have b30700 := hb (x 10 9)
                    have b30701 := hb (x 11 8)
                    clear * - r30687 e30688 e30689 e30690 e30691 e30692 e30693 b30694 b30695 b30696 b30697 b30698 b30699 b30700 b30701 d30682 d30627 d30274 d30298 d30226
                    omega
                  have d30702 : (x 10 9).toNat = 0 := by
                    have r30703 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30704 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                    have e30705 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                    have e30706 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                    have e30707 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                    have e30708 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                    have e30709 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                    have b30710 := hb (x 4 7)
                    have b30711 := hb (x 5 6)
                    have b30712 := hb (x 6 5)
                    have b30713 := hb (x 7 4)
                    have b30714 := hb (x 8 11)
                    have b30715 := hb (x 9 10)
                    have b30716 := hb (x 10 9)
                    have b30717 := hb (x 11 8)
                    clear * - r30703 e30704 e30705 e30706 e30707 e30708 e30709 b30710 b30711 b30712 b30713 b30714 b30715 b30716 b30717 d30686 d30682 d30627 d30274 d30298 d30226
                    omega
                  have d30718 : (x 4 7).toNat = 0 := by
                    have r30719 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30720 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
                    have e30721 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
                    have e30722 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
                    have e30723 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
                    have e30724 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
                    have e30725 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
                    have b30726 := hb (x 4 7)
                    have b30727 := hb (x 5 6)
                    have b30728 := hb (x 6 5)
                    have b30729 := hb (x 7 4)
                    have b30730 := hb (x 8 11)
                    have b30731 := hb (x 9 10)
                    have b30732 := hb (x 10 9)
                    have b30733 := hb (x 11 8)
                    clear * - r30719 e30720 e30721 e30722 e30723 e30724 e30725 b30726 b30727 b30728 b30729 b30730 b30731 b30732 b30733 d30686 d30702 d30682 d30627 d30274 d30298 d30226
                    omega
                  have d30734 : (x 4 7 && x 4 12).toNat = 0 := by
                    have r30735 := hand1 (x 4 7) (x 4 12)
                    have b30736 := hb (x 4 7)
                    have b30737 := hb (x 4 7 && x 4 12)
                    clear * - r30735 b30736 b30737 d30718
                    omega
                  have d30738 : (x 8 7).toNat = 1 := by
                    have r30739 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b30740 := hb (x 0 8)
                    have b30741 := hb (x 8 7)
                    have b30742 := hb (x 7 1 && x 7 8)
                    have b30743 := hb (x 6 2 && x 6 9)
                    have b30744 := hb (x 5 3 && x 5 10)
                    have b30745 := hb (x 4 4 && x 4 11)
                    have b30746 := hb (x 3 5 && x 3 12)
                    have b30747 := hb (x 2 6 && x 2 13)
                    have b30748 := hb (x 1 7 && x 1 14)
                    clear * - r30739 b30740 b30741 b30742 b30743 b30744 b30745 b30746 b30747 b30748 d30347 d30367 d30242 d30623 g106 g107 g108 g19
                    omega
                  have d30749 : (x 15 8).toNat = 0 := by
                    have r30750 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30751 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e30752 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e30753 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e30754 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e30755 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e30756 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b30757 := hb (x 8 7)
                    have b30758 := hb (x 9 6)
                    have b30759 := hb (x 10 5)
                    have b30760 := hb (x 11 4)
                    have b30761 := hb (x 12 11)
                    have b30762 := hb (x 13 10)
                    have b30763 := hb (x 14 9)
                    have b30764 := hb (x 15 8)
                    clear * - r30750 e30751 e30752 e30753 e30754 e30755 e30756 b30757 b30758 b30759 b30760 b30761 b30762 b30763 b30764 d30646 d30662 d30738
                    omega
                  have d30765 : (x 14 9).toNat = 0 := by
                    have r30766 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30767 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e30768 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e30769 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e30770 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e30771 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e30772 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b30773 := hb (x 8 7)
                    have b30774 := hb (x 9 6)
                    have b30775 := hb (x 10 5)
                    have b30776 := hb (x 11 4)
                    have b30777 := hb (x 12 11)
                    have b30778 := hb (x 13 10)
                    have b30779 := hb (x 14 9)
                    have b30780 := hb (x 15 8)
                    clear * - r30766 e30767 e30768 e30769 e30770 e30771 e30772 b30773 b30774 b30775 b30776 b30777 b30778 b30779 b30780 d30749 d30646 d30662 d30738
                    omega
                  have d30781 : (x 13 10).toNat = 0 := by
                    have r30782 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30783 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e30784 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e30785 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e30786 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e30787 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e30788 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b30789 := hb (x 8 7)
                    have b30790 := hb (x 9 6)
                    have b30791 := hb (x 10 5)
                    have b30792 := hb (x 11 4)
                    have b30793 := hb (x 12 11)
                    have b30794 := hb (x 13 10)
                    have b30795 := hb (x 14 9)
                    have b30796 := hb (x 15 8)
                    clear * - r30782 e30783 e30784 e30785 e30786 e30787 e30788 b30789 b30790 b30791 b30792 b30793 b30794 b30795 b30796 d30749 d30765 d30646 d30662 d30738
                    omega
                  have d30797 : (x 12 11).toNat = 0 := by
                    have r30798 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30799 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e30800 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e30801 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e30802 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e30803 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e30804 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b30805 := hb (x 8 7)
                    have b30806 := hb (x 9 6)
                    have b30807 := hb (x 10 5)
                    have b30808 := hb (x 11 4)
                    have b30809 := hb (x 12 11)
                    have b30810 := hb (x 13 10)
                    have b30811 := hb (x 14 9)
                    have b30812 := hb (x 15 8)
                    clear * - r30798 e30799 e30800 e30801 e30802 e30803 e30804 b30805 b30806 b30807 b30808 b30809 b30810 b30811 b30812 d30749 d30765 d30781 d30646 d30662 d30738
                    omega
                  have d30813 : (x 9 6).toNat = 0 := by
                    have r30814 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e30815 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
                    have e30816 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
                    have e30817 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
                    have e30818 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
                    have e30819 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
                    have e30820 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
                    have b30821 := hb (x 8 7)
                    have b30822 := hb (x 9 6)
                    have b30823 := hb (x 10 5)
                    have b30824 := hb (x 11 4)
                    have b30825 := hb (x 12 11)
                    have b30826 := hb (x 13 10)
                    have b30827 := hb (x 14 9)
                    have b30828 := hb (x 15 8)
                    clear * - r30814 e30815 e30816 e30817 e30818 e30819 e30820 b30821 b30822 b30823 b30824 b30825 b30826 b30827 b30828 d30749 d30765 d30781 d30797 d30646 d30662 d30738
                    omega
                  have r30829 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30830 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                  have e30831 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                  have e30832 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                  have e30833 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                  have e30834 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                  have e30835 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                  have r30836 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30837 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                  have e30838 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                  have r30839 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := by have q := hcov4 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30840 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
                  have e30841 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
                  have r30842 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r30843 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r30844 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
                  have r30845 := hand1 (x 10 2) (x 10 6)
                  have r30846 := hand2 (x 9 3) (x 9 7)
                  have r30847 := hand2 (x 10 1) (x 10 6)
                  have r30848 := hand2 (x 14 1) (x 14 10)
                  have r30849 := hand2 (x 13 2) (x 13 11)
                  have r30850 := hand2 (x 12 3) (x 12 12)
                  linarith only [r30829, e30830, e30831, e30832, e30833, e30834, e30835, r30836, e30837, e30838, r30839, e30840, e30841, r30842, r30843, r30844, r30845, r30846, r30847, r30848, r30849, r30850, g27, g28, g33, d30813, d30543, d30563, d30583, d30603, g63, g64, d30678, d30539, d30282, d30306, d30230, d30734, g77, g78, d30650, d30666]
              · have f30889 : (x 2 2).toNat = 1 := by rw [h30203]; rfl
                have d30890 : (x 4 12).toNat = 0 := by
                  have r30891 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30892 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e30893 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b30894 := hb (x 1 3)
                  have b30895 := hb (x 2 2)
                  have b30896 := hb (x 3 13)
                  have b30897 := hb (x 4 12)
                  clear * - r30891 e30892 e30893 b30894 b30895 b30896 b30897 f30889 g23
                  omega
                have d30898 : (x 4 2 && x 4 12).toNat = 0 := by
                  have r30899 := hand2 (x 4 2) (x 4 12)
                  have b30900 := hb (x 4 12)
                  have b30901 := hb (x 4 2 && x 4 12)
                  clear * - r30899 b30900 b30901 d30890
                  omega
                have d30902 : (x 4 4).toNat = 0 := by
                  have r30903 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
                  have b30904 := hb (x 4 4)
                  have b30905 := hb (x 4 12)
                  clear * - r30903 b30904 b30905 d30890
                  omega
                have d30906 : (x 3 13).toNat = 0 := by
                  have r30907 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30908 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e30909 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b30910 := hb (x 1 3)
                  have b30911 := hb (x 2 2)
                  have b30912 := hb (x 3 13)
                  have b30913 := hb (x 4 12)
                  clear * - r30907 e30908 e30909 b30910 b30911 b30912 b30913 d30890 f30889 g23
                  omega
                have d30914 : (x 3 3 && x 3 13).toNat = 0 := by
                  have r30915 := hand2 (x 3 3) (x 3 13)
                  have b30916 := hb (x 3 13)
                  have b30917 := hb (x 3 3 && x 3 13)
                  clear * - r30915 b30916 b30917 d30906
                  omega
                have d30918 : (x 3 5).toNat = 0 := by
                  have r30919 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                  have b30920 := hb (x 3 5)
                  have b30921 := hb (x 3 13)
                  clear * - r30919 b30920 b30921 d30906
                  omega
                have r30922 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30923 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30924 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30925 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e30926 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e30927 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e30928 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e30929 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e30930 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have r30931 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30932 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                have e30933 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                have r30934 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30935 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
                have e30936 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
                have r30937 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30938 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30939 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
                have r30940 := hand1 (x (-5) 8) (x (-5) 12)
                have r30941 := hand1 (x (-6) 9) (x (-6) 13)
                have r30942 := hand2 (x 2 2) (x 2 6)
                have r30943 := hand1 (x (-4) 8) (x (-4) 12)
                have r30944 := hand1 (x (-5) 9) (x (-5) 13)
                have r30945 := hand2 (x 5 1) (x 5 11)
                have r30946 := hand2 (x (-10) 1) (x (-10) 14)
                linarith only [r30922, r30923, r30924, e30925, e30926, e30927, e30928, e30929, e30930, r30931, e30932, e30933, r30934, e30935, e30936, r30937, r30938, r30939, r30940, r30941, r30942, r30943, r30944, r30945, r30946, g0, g1, g2, g4, g5, g8, g9, g14, g15, g22, g23, g25, f27605, f30182, f30889, g31, g35, d30918, d30902, g43, g44, g45, g46, g47, g48, d27600, g49, g50, g51, g52, d30898, d30914, g124]
            · have f31008 : (x (-1) 14).toNat = 1 := by rw [h30201]; rfl
              have d31009 : (x (-2) 1).toNat = 0 := by
                have r31010 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b31011 := hb (x (-2) 1)
                have b31012 := hb (x (-1) 14)
                clear * - r31010 b31011 b31012 f31008
                omega
              have d31013 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                have r31014 := hand1 (x (-2) 1) (x (-2) 14)
                have b31015 := hb (x (-2) 1)
                have b31016 := hb (x (-2) 1 && x (-2) 14)
                clear * - r31014 b31015 b31016 d31009
                omega
              have d31017 : (x (-2) 13).toNat = 0 := by
                have r31018 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                have b31019 := hb (x (-2) 1)
                have b31020 := hb (x (-2) 13)
                clear * - r31018 b31019 b31020 d31009
                omega
              have d31021 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
                have r31022 := hand2 (x (-2) 9) (x (-2) 13)
                have b31023 := hb (x (-2) 13)
                have b31024 := hb (x (-2) 9 && x (-2) 13)
                clear * - r31022 b31023 b31024 d31017
                omega
              have d31025 : (x (-2) 9).toNat = 0 := by
                have r31026 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                have b31027 := hb (x (-2) 1)
                have b31028 := hb (x (-2) 9)
                clear * - r31026 b31027 b31028 d31009
                omega
              have d31029 : (x (-3) 2).toNat = 1 := by
                have r31030 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b31031 := hb (x (-3) 2)
                have b31032 := hb (x (-1) 13)
                have b31033 := hb (x (-2) 1 && x (-2) 14)
                clear * - r31030 b31031 b31032 b31033 g13 d31013
                omega
              have d31034 : (x (-3) 14).toNat = 1 := by
                have r31035 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                have b31036 := hb (x (-3) 2)
                have b31037 := hb (x (-3) 14)
                clear * - r31035 b31036 b31037 d31029
                omega
              have d31038 : (x (-4) 3).toNat = 0 := by
                have r31039 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e31040 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e31041 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b31042 := hb (x (-4) 3)
                have b31043 := hb (x (-3) 2)
                have b31044 := hb (x (-2) 13)
                have b31045 := hb (x (-1) 12)
                clear * - r31039 e31040 e31041 b31042 b31043 b31044 b31045 f27617 d31017 d31029
                omega
              have d31046 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                have r31047 := hand1 (x (-4) 3) (x (-4) 12)
                have b31048 := hb (x (-4) 3)
                have b31049 := hb (x (-4) 3 && x (-4) 12)
                clear * - r31047 b31048 b31049 d31038
                omega
              have d31050 : (x (-4) 11).toNat = 0 := by
                have r31051 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                have b31052 := hb (x (-4) 3)
                have b31053 := hb (x (-4) 11)
                clear * - r31051 b31052 b31053 d31038
                omega
              have r31054 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r31055 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r31056 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31057 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e31058 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e31059 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e31060 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e31061 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e31062 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have r31063 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31064 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e31065 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have r31066 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31067 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
              have e31068 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
              have r31069 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r31070 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r31071 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r31072 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r31073 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
              have r31074 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
              have r31075 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
              have r31076 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
              have r31077 : (x 11 10).toNat ≤ (x 11 2).toNat := himp _ _ (hp10 11)
              have r31078 := hand2 (x 5 2) (x 5 6)
              have r31079 := hand2 (x 4 3) (x 4 7)
              have r31080 := hand2 (x 6 1) (x 6 7)
              have r31081 := hand2 (x 5 2) (x 5 8)
              have r31082 := hand2 (x 4 3) (x 4 9)
              have r31083 := hand1 (x (-5) 4) (x (-5) 13)
              have r31084 := hand1 (x (-6) 5) (x (-6) 14)
              have r31085 := hand2 (x 4 1) (x 4 11)
              have r31086 := hand1 (x 10 1) (x 10 11)
              have r31087 := hand1 (x 9 2) (x 9 12)
              have r31088 := hand1 (x 8 3) (x 8 13)
              have r31089 := hand1 (x 7 4) (x 7 14)
              linarith only [r31054, r31055, r31056, e31057, e31058, e31059, e31060, e31061, e31062, r31063, e31064, e31065, r31066, e31067, e31068, r31069, r31070, r31071, r31072, r31073, r31074, r31075, r31076, r31077, r31078, r31079, r31080, r31081, r31082, r31083, r31084, r31085, r31086, r31087, r31088, r31089, d31050, d31034, d31025, d31017, f27607, g10, f27617, f31008, g16, g20, g21, g27, g29, g32, g36, d30195, g53, g54, g55, g56, d27612, d31021, g92, g93, g94, g95, d27608, g109, g110, d31046, g121, g122, g123]
          · have f31164 : (x (-1) 6).toNat = 1 := by rw [h30199]; rfl
            have d31165 : (x (-1) 14).toNat = 1 := by
              have r31166 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
              have b31167 := hb (x (-1) 6)
              have b31168 := hb (x (-1) 14)
              clear * - r31166 b31167 b31168 f31164
              omega
            have d31169 : (x (-2) 1).toNat = 0 := by
              have r31170 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b31171 := hb (x (-2) 1)
              have b31172 := hb (x (-1) 14)
              clear * - r31170 b31171 b31172 d31165
              omega
            have d31173 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
              have r31174 := hand1 (x (-2) 1) (x (-2) 14)
              have b31175 := hb (x (-2) 1)
              have b31176 := hb (x (-2) 1 && x (-2) 14)
              clear * - r31174 b31175 b31176 d31169
              omega
            have d31177 : (x (-2) 13).toNat = 0 := by
              have r31178 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b31179 := hb (x (-2) 1)
              have b31180 := hb (x (-2) 13)
              clear * - r31178 b31179 b31180 d31169
              omega
            have d31181 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
              have r31182 := hand2 (x (-2) 9) (x (-2) 13)
              have b31183 := hb (x (-2) 13)
              have b31184 := hb (x (-2) 9 && x (-2) 13)
              clear * - r31182 b31183 b31184 d31177
              omega
            have d31185 : (x (-2) 9).toNat = 0 := by
              have r31186 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
              have b31187 := hb (x (-2) 1)
              have b31188 := hb (x (-2) 9)
              clear * - r31186 b31187 b31188 d31169
              omega
            have d31189 : (x (-3) 2).toNat = 1 := by
              have r31190 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b31191 := hb (x (-3) 2)
              have b31192 := hb (x (-1) 13)
              have b31193 := hb (x (-2) 1 && x (-2) 14)
              clear * - r31190 b31191 b31192 b31193 g13 d31173
              omega
            have d31194 : (x (-3) 14).toNat = 1 := by
              have r31195 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
              have b31196 := hb (x (-3) 2)
              have b31197 := hb (x (-3) 14)
              clear * - r31195 b31196 b31197 d31189
              omega
            have d31198 : (x (-4) 3).toNat = 0 := by
              have r31199 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31200 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e31201 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b31202 := hb (x (-4) 3)
              have b31203 := hb (x (-3) 2)
              have b31204 := hb (x (-2) 13)
              have b31205 := hb (x (-1) 12)
              clear * - r31199 e31200 e31201 b31202 b31203 b31204 b31205 f27617 d31177 d31189
              omega
            have d31206 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
              have r31207 := hand1 (x (-4) 3) (x (-4) 12)
              have b31208 := hb (x (-4) 3)
              have b31209 := hb (x (-4) 3 && x (-4) 12)
              clear * - r31207 b31208 b31209 d31198
              omega
            have d31210 : (x (-4) 11).toNat = 0 := by
              have r31211 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
              have b31212 := hb (x (-4) 3)
              have b31213 := hb (x (-4) 11)
              clear * - r31211 b31212 b31213 d31198
              omega
            have d31214 : (x 5 8).toNat = 0 := by
              have r31215 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31216 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e31217 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e31218 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e31219 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e31220 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e31221 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b31222 := hb (x (-2) 7)
              have b31223 := hb (x (-1) 6)
              have b31224 := hb (x 0 5)
              have b31225 := hb (x 1 4)
              have b31226 := hb (x 2 11)
              have b31227 := hb (x 3 10)
              have b31228 := hb (x 4 9)
              have b31229 := hb (x 5 8)
              clear * - r31215 e31216 e31217 e31218 e31219 e31220 e31221 b31222 b31223 b31224 b31225 b31226 b31227 b31228 b31229 d30195 g24 g16 f31164
              omega
            have d31230 : (x 5 2 && x 5 8).toNat = 0 := by
              have r31231 := hand2 (x 5 2) (x 5 8)
              have b31232 := hb (x 5 8)
              have b31233 := hb (x 5 2 && x 5 8)
              clear * - r31231 b31232 b31233 d31214
              omega
            have d31234 : (x 4 9).toNat = 0 := by
              have r31235 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e31236 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e31237 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e31238 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e31239 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e31240 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e31241 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b31242 := hb (x (-2) 7)
              have b31243 := hb (x (-1) 6)
              have b31244 := hb (x 0 5)
              have b31245 := hb (x 1 4)
              have b31246 := hb (x 2 11)
              have b31247 := hb (x 3 10)
              have b31248 := hb (x 4 9)
              have b31249 := hb (x 5 8)
              clear * - r31235 e31236 e31237 e31238 e31239 e31240 e31241 b31242 b31243 b31244 b31245 b31246 b31247 b31248 b31249 d31214 d30195 g24 g16 f31164
              omega
            have d31250 : (x 4 3 && x 4 9).toNat = 0 := by
              have r31251 := hand2 (x 4 3) (x 4 9)
              have b31252 := hb (x 4 9)
              have b31253 := hb (x 4 3 && x 4 9)
              clear * - r31251 b31252 b31253 d31234
              omega
            have r31254 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r31255 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31256 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
            have e31257 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
            have e31258 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
            have e31259 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
            have e31260 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
            have e31261 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
            have r31262 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31263 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
            have e31264 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
            have e31265 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
            have e31266 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
            have e31267 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
            have e31268 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
            have r31269 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31270 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e31271 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have r31272 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31273 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
            have e31274 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
            have r31275 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r31276 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r31277 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r31278 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r31279 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
            have r31280 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
            have r31281 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
            have r31282 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
            have r31283 := hand2 (x 5 2) (x 5 6)
            have r31284 := hand2 (x 4 3) (x 4 7)
            have r31285 := hand2 (x 6 1) (x 6 7)
            have r31286 := hand1 (x (-5) 4) (x (-5) 13)
            have r31287 := hand1 (x (-6) 5) (x (-6) 14)
            have r31288 := hand2 (x 4 1) (x 4 11)
            have r31289 := hand2 (x 10 1) (x 10 11)
            have r31290 := hand1 (x 9 2) (x 9 12)
            have r31291 := hand1 (x 8 3) (x 8 13)
            have r31292 := hand1 (x 7 4) (x 7 14)
            linarith only [r31254, r31255, e31256, e31257, e31258, e31259, e31260, e31261, r31262, e31263, e31264, e31265, e31266, e31267, e31268, r31269, e31270, e31271, r31272, e31273, e31274, r31275, r31276, r31277, r31278, r31279, r31280, r31281, r31282, r31283, r31284, r31285, r31286, r31287, r31288, r31289, r31290, r31291, r31292, d31210, d31194, d31185, d31177, f27607, g10, f27617, g16, g20, g27, g32, g36, g53, g54, g55, g56, d27612, d31181, d31230, d31250, g92, g93, g94, g95, d27608, g109, g110, d31206, g121, g122, g123]
      · have f31360 : (x (-1) 12).toNat = 1 := by rw [h27616]; rfl
        have d31361 : (x (-2) 13).toNat = 0 := by
          have r31362 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31363 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e31364 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b31365 := hb (x (-4) 3)
          have b31366 := hb (x (-3) 2)
          have b31367 := hb (x (-2) 13)
          have b31368 := hb (x (-1) 12)
          clear * - r31362 e31363 e31364 b31365 b31366 b31367 b31368 f31360
          omega
        have d31369 : (x (-3) 2).toNat = 0 := by
          have r31370 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31371 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e31372 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b31373 := hb (x (-4) 3)
          have b31374 := hb (x (-3) 2)
          have b31375 := hb (x (-2) 13)
          have b31376 := hb (x (-1) 12)
          clear * - r31370 e31371 e31372 b31373 b31374 b31375 b31376 f31360 d31361
          omega
        have d31377 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
          have r31378 := hand1 (x (-3) 2) (x (-3) 13)
          have b31379 := hb (x (-3) 2)
          have b31380 := hb (x (-3) 2 && x (-3) 13)
          clear * - r31378 b31379 b31380 d31369
          omega
        have d31381 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
          have r31382 := hand1 (x (-3) 2) (x (-3) 12)
          have b31383 := hb (x (-3) 2)
          have b31384 := hb (x (-3) 2 && x (-3) 12)
          clear * - r31382 b31383 b31384 d31369
          omega
        have d31385 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
          have r31386 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31387 := hb (x (-3) 2)
          have b31388 := hb (x (-1) 13)
          have b31389 := hb (x (-2) 1 && x (-2) 14)
          clear * - r31386 b31387 b31388 b31389 g13 d31369
          omega
        have d31390 : (x (-2) 14).toNat = 1 := by
          have r31391 := hand2 (x (-2) 1) (x (-2) 14)
          have b31392 := hb (x (-2) 14)
          have b31393 := hb (x (-2) 1 && x (-2) 14)
          clear * - r31391 b31392 b31393 d31385
          omega
        have d31394 : (x (-3) 1).toNat = 0 := by
          have r31395 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31396 := hb (x (-3) 1)
          have b31397 := hb (x (-2) 14)
          clear * - r31395 b31396 b31397 d31390
          omega
        have d31398 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
          have r31399 := hand1 (x (-3) 1) (x (-3) 14)
          have b31400 := hb (x (-3) 1)
          have b31401 := hb (x (-3) 1 && x (-3) 14)
          clear * - r31399 b31400 b31401 d31394
          omega
        have d31402 : (x (-4) 2).toNat = 1 := by
          have r31403 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31404 := hb (x (-4) 2)
          have b31405 := hb (x (-2) 13)
          have b31406 := hb (x (-3) 1 && x (-3) 14)
          clear * - r31403 b31404 b31405 b31406 d31361 d31398
          omega
        have d31407 : (x (-4) 14).toNat = 1 := by
          have r31408 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
          have b31409 := hb (x (-4) 2)
          have b31410 := hb (x (-4) 14)
          clear * - r31408 b31409 b31410 d31402
          omega
        have d31411 : (x (-5) 1).toNat = 0 := by
          have r31412 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31413 := hb (x (-5) 1)
          have b31414 := hb (x (-4) 14)
          clear * - r31412 b31413 b31414 d31407
          omega
        have d31415 : (x (-5) 13).toNat = 0 := by
          have r31416 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
          have b31417 := hb (x (-5) 1)
          have b31418 := hb (x (-5) 13)
          clear * - r31416 b31417 b31418 d31411
          omega
        have d31419 : (x (-3) 13).toNat = 0 := by
          have r31420 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b31421 := hb (x (-3) 1)
          have b31422 := hb (x (-3) 13)
          clear * - r31420 b31421 b31422 d31394
          omega
        have d31423 : (x (-4) 3).toNat = 0 := by
          have r31424 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31425 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e31426 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b31427 := hb (x (-4) 3)
          have b31428 := hb (x (-3) 2)
          have b31429 := hb (x (-2) 13)
          have b31430 := hb (x (-1) 12)
          clear * - r31424 e31425 e31426 b31427 b31428 b31429 b31430 f31360 d31361 d31369
          omega
        have d31431 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
          have r31432 := hand1 (x (-4) 3) (x (-4) 14)
          have b31433 := hb (x (-4) 3)
          have b31434 := hb (x (-4) 3 && x (-4) 14)
          clear * - r31432 b31433 b31434 d31423
          omega
        have d31435 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
          have r31436 := hand1 (x (-4) 3) (x (-4) 13)
          have b31437 := hb (x (-4) 3)
          have b31438 := hb (x (-4) 3 && x (-4) 13)
          clear * - r31436 b31437 b31438 d31423
          omega
        have d31439 : (x (-2) 12).toNat = 0 := by
          have r31440 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31441 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e31442 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b31443 := hb (x (-5) 3)
          have b31444 := hb (x (-4) 2)
          have b31445 := hb (x (-3) 13)
          have b31446 := hb (x (-2) 12)
          clear * - r31440 e31441 e31442 b31443 b31444 b31445 b31446 d31419 d31402
          omega
        have d31447 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
          have r31448 := hand2 (x (-2) 1) (x (-2) 12)
          have b31449 := hb (x (-2) 12)
          have b31450 := hb (x (-2) 1 && x (-2) 12)
          clear * - r31448 b31449 b31450 d31439
          omega
        have d31451 : (x (-5) 4).toNat = 1 := by
          have r31452 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31453 := hb (x (-5) 4)
          have b31454 := hb (x (-1) 11)
          have b31455 := hb (x (-2) 1 && x (-2) 12)
          have b31456 := hb (x (-3) 2 && x (-3) 13)
          have b31457 := hb (x (-4) 3 && x (-4) 14)
          clear * - r31452 b31453 b31454 b31455 b31456 b31457 g12 d31447 d31377 d31431
          omega
        have d31458 : (x (-5) 12).toNat = 1 := by
          have r31459 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
          have b31460 := hb (x (-5) 4)
          have b31461 := hb (x (-5) 12)
          clear * - r31459 b31460 b31461 d31451
          omega
        have d31462 : (x (-6) 13).toNat = 0 := by
          have r31463 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31464 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e31465 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b31466 := hb (x (-8) 3)
          have b31467 := hb (x (-7) 2)
          have b31468 := hb (x (-6) 13)
          have b31469 := hb (x (-5) 12)
          clear * - r31463 e31464 e31465 b31466 b31467 b31468 b31469 d31458
          omega
        have d31470 : (x (-6) 5).toNat = 0 := by
          have r31471 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
          have b31472 := hb (x (-6) 5)
          have b31473 := hb (x (-6) 13)
          clear * - r31471 b31472 b31473 d31462
          omega
        have d31474 : (x (-7) 2).toNat = 0 := by
          have r31475 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31476 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
          have e31477 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
          have b31478 := hb (x (-8) 3)
          have b31479 := hb (x (-7) 2)
          have b31480 := hb (x (-6) 13)
          have b31481 := hb (x (-5) 12)
          clear * - r31475 e31476 e31477 b31478 b31479 b31480 b31481 d31458 d31462
          omega
        have d31482 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
          have r31483 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31484 := hb (x (-7) 2)
          have b31485 := hb (x (-5) 13)
          have b31486 := hb (x (-6) 1 && x (-6) 14)
          clear * - r31483 b31484 b31485 b31486 d31415 d31474
          omega
        have d31487 : (x (-6) 1).toNat = 1 := by
          have r31488 := hand1 (x (-6) 1) (x (-6) 14)
          have b31489 := hb (x (-6) 1)
          have b31490 := hb (x (-6) 1 && x (-6) 14)
          clear * - r31488 b31489 b31490 d31482
          omega
        have d31491 : (x (-5) 14).toNat = 0 := by
          have r31492 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31493 := hb (x (-6) 1)
          have b31494 := hb (x (-5) 14)
          clear * - r31492 b31493 b31494 d31487
          omega
        have d31495 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
          have r31496 := hand2 (x (-5) 4) (x (-5) 14)
          have b31497 := hb (x (-5) 14)
          have b31498 := hb (x (-5) 4 && x (-5) 14)
          clear * - r31496 b31497 b31498 d31491
          omega
        have r31499 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31500 := hb (x (-6) 5)
        have b31501 := hb (x (-1) 10)
        have b31502 := hb (x (-2) 1 && x (-2) 11)
        have b31503 := hb (x (-3) 2 && x (-3) 12)
        have b31504 := hb (x (-4) 3 && x (-4) 13)
        have b31505 := hb (x (-5) 4 && x (-5) 14)
        linarith only [r31499, b31500, b31501, b31502, b31503, b31504, b31505, g11, g120, d31381, d31435, d31495, d31470]
    · have f31506 : (x (-1) 8).toNat = 1 := by rw [h27606]; rfl
      have d31507 : (x (-2) 9).toNat = 0 := by
        have r31508 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31509 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e31510 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e31511 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e31512 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e31513 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e31514 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b31515 := hb (x (-8) 7)
        have b31516 := hb (x (-7) 6)
        have b31517 := hb (x (-6) 5)
        have b31518 := hb (x (-5) 4)
        have b31519 := hb (x (-4) 11)
        have b31520 := hb (x (-3) 10)
        have b31521 := hb (x (-2) 9)
        have b31522 := hb (x (-1) 8)
        clear * - r31508 e31509 e31510 e31511 e31512 e31513 e31514 b31515 b31516 b31517 b31518 b31519 b31520 b31521 b31522 f31506
        omega
      have d31523 : (x (-3) 10).toNat = 0 := by
        have r31524 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31525 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e31526 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e31527 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e31528 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e31529 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e31530 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b31531 := hb (x (-8) 7)
        have b31532 := hb (x (-7) 6)
        have b31533 := hb (x (-6) 5)
        have b31534 := hb (x (-5) 4)
        have b31535 := hb (x (-4) 11)
        have b31536 := hb (x (-3) 10)
        have b31537 := hb (x (-2) 9)
        have b31538 := hb (x (-1) 8)
        clear * - r31524 e31525 e31526 e31527 e31528 e31529 e31530 b31531 b31532 b31533 b31534 b31535 b31536 b31537 b31538 f31506 d31507
        omega
      have d31539 : (x (-3) 1 && x (-3) 10).toNat = 0 := by
        have r31540 := hand2 (x (-3) 1) (x (-3) 10)
        have b31541 := hb (x (-3) 10)
        have b31542 := hb (x (-3) 1 && x (-3) 10)
        clear * - r31540 b31541 b31542 d31523
        omega
      have d31543 : (x (-4) 11).toNat = 0 := by
        have r31544 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31545 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e31546 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e31547 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e31548 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e31549 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e31550 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b31551 := hb (x (-8) 7)
        have b31552 := hb (x (-7) 6)
        have b31553 := hb (x (-6) 5)
        have b31554 := hb (x (-5) 4)
        have b31555 := hb (x (-4) 11)
        have b31556 := hb (x (-3) 10)
        have b31557 := hb (x (-2) 9)
        have b31558 := hb (x (-1) 8)
        clear * - r31544 e31545 e31546 e31547 e31548 e31549 e31550 b31551 b31552 b31553 b31554 b31555 b31556 b31557 b31558 f31506 d31507 d31523
        omega
      have d31559 : (x (-4) 2 && x (-4) 11).toNat = 0 := by
        have r31560 := hand2 (x (-4) 2) (x (-4) 11)
        have b31561 := hb (x (-4) 11)
        have b31562 := hb (x (-4) 2 && x (-4) 11)
        clear * - r31560 b31561 b31562 d31543
        omega
      have d31563 : (x (-5) 4).toNat = 0 := by
        have r31564 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31565 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e31566 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e31567 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e31568 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e31569 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e31570 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b31571 := hb (x (-8) 7)
        have b31572 := hb (x (-7) 6)
        have b31573 := hb (x (-6) 5)
        have b31574 := hb (x (-5) 4)
        have b31575 := hb (x (-4) 11)
        have b31576 := hb (x (-3) 10)
        have b31577 := hb (x (-2) 9)
        have b31578 := hb (x (-1) 8)
        clear * - r31564 e31565 e31566 e31567 e31568 e31569 e31570 b31571 b31572 b31573 b31574 b31575 b31576 b31577 b31578 f31506 d31507 d31523 d31543
        omega
      have d31579 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
        have r31580 := hand1 (x (-5) 4) (x (-5) 14)
        have b31581 := hb (x (-5) 4)
        have b31582 := hb (x (-5) 4 && x (-5) 14)
        clear * - r31580 b31581 b31582 d31563
        omega
      have d31583 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
        have r31584 := hand1 (x (-5) 4) (x (-5) 13)
        have b31585 := hb (x (-5) 4)
        have b31586 := hb (x (-5) 4 && x (-5) 13)
        clear * - r31584 b31585 b31586 d31563
        omega
      have d31587 : (x (-5) 4 && x (-5) 11).toNat = 0 := by
        have r31588 := hand1 (x (-5) 4) (x (-5) 11)
        have b31589 := hb (x (-5) 4)
        have b31590 := hb (x (-5) 4 && x (-5) 11)
        clear * - r31588 b31589 b31590 d31563
        omega
      have d31591 : (x (-5) 4 && x (-5) 9).toNat = 0 := by
        have r31592 := hand1 (x (-5) 4) (x (-5) 9)
        have b31593 := hb (x (-5) 4)
        have b31594 := hb (x (-5) 4 && x (-5) 9)
        clear * - r31592 b31593 b31594 d31563
        omega
      have d31595 : (x (-6) 5).toNat = 0 := by
        have r31596 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31597 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e31598 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e31599 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e31600 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e31601 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e31602 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b31603 := hb (x (-8) 7)
        have b31604 := hb (x (-7) 6)
        have b31605 := hb (x (-6) 5)
        have b31606 := hb (x (-5) 4)
        have b31607 := hb (x (-4) 11)
        have b31608 := hb (x (-3) 10)
        have b31609 := hb (x (-2) 9)
        have b31610 := hb (x (-1) 8)
        clear * - r31596 e31597 e31598 e31599 e31600 e31601 e31602 b31603 b31604 b31605 b31606 b31607 b31608 b31609 b31610 f31506 d31507 d31523 d31543 d31563
        omega
      have d31611 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
        have r31612 := hand1 (x (-6) 5) (x (-6) 14)
        have b31613 := hb (x (-6) 5)
        have b31614 := hb (x (-6) 5 && x (-6) 14)
        clear * - r31612 b31613 b31614 d31595
        omega
      have d31615 : (x (-6) 5 && x (-6) 12).toNat = 0 := by
        have r31616 := hand1 (x (-6) 5) (x (-6) 12)
        have b31617 := hb (x (-6) 5)
        have b31618 := hb (x (-6) 5 && x (-6) 12)
        clear * - r31616 b31617 b31618 d31595
        omega
      have d31619 : (x (-6) 5 && x (-6) 10).toNat = 0 := by
        have r31620 := hand1 (x (-6) 5) (x (-6) 10)
        have b31621 := hb (x (-6) 5)
        have b31622 := hb (x (-6) 5 && x (-6) 10)
        clear * - r31620 b31621 b31622 d31595
        omega
      have d31623 : (x (-7) 6).toNat = 0 := by
        have r31624 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31625 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e31626 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e31627 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e31628 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e31629 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e31630 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b31631 := hb (x (-8) 7)
        have b31632 := hb (x (-7) 6)
        have b31633 := hb (x (-6) 5)
        have b31634 := hb (x (-5) 4)
        have b31635 := hb (x (-4) 11)
        have b31636 := hb (x (-3) 10)
        have b31637 := hb (x (-2) 9)
        have b31638 := hb (x (-1) 8)
        clear * - r31624 e31625 e31626 e31627 e31628 e31629 e31630 b31631 b31632 b31633 b31634 b31635 b31636 b31637 b31638 f31506 d31507 d31523 d31543 d31563 d31595
        omega
      have d31639 : (x (-7) 6 && x (-7) 13).toNat = 0 := by
        have r31640 := hand1 (x (-7) 6) (x (-7) 13)
        have b31641 := hb (x (-7) 6)
        have b31642 := hb (x (-7) 6 && x (-7) 13)
        clear * - r31640 b31641 b31642 d31623
        omega
      have d31643 : (x (-7) 6 && x (-7) 11).toNat = 0 := by
        have r31644 := hand1 (x (-7) 6) (x (-7) 11)
        have b31645 := hb (x (-7) 6)
        have b31646 := hb (x (-7) 6 && x (-7) 11)
        clear * - r31644 b31645 b31646 d31623
        omega
      have d31647 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
        have r31648 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31649 := hb (x (-7) 6)
        have b31650 := hb (x (-1) 9)
        have b31651 := hb (x (-2) 1 && x (-2) 10)
        have b31652 := hb (x (-3) 2 && x (-3) 11)
        have b31653 := hb (x (-4) 3 && x (-4) 12)
        have b31654 := hb (x (-5) 4 && x (-5) 13)
        have b31655 := hb (x (-6) 5 && x (-6) 14)
        clear * - r31648 b31649 b31650 b31651 b31652 b31653 b31654 b31655 g10 g109 g110 d31583 d31611 d31623
        omega
      have d31656 : (x (-4) 12).toNat = 1 := by
        have r31657 := hand2 (x (-4) 3) (x (-4) 12)
        have b31658 := hb (x (-4) 12)
        have b31659 := hb (x (-4) 3 && x (-4) 12)
        clear * - r31657 b31658 b31659 d31647
        omega
      have d31660 : (x (-5) 13).toNat = 0 := by
        have r31661 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31662 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e31663 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b31664 := hb (x (-7) 3)
        have b31665 := hb (x (-6) 2)
        have b31666 := hb (x (-5) 13)
        have b31667 := hb (x (-4) 12)
        clear * - r31661 e31662 e31663 b31664 b31665 b31666 b31667 d31656
        omega
      have d31668 : (x (-6) 2).toNat = 0 := by
        have r31669 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31670 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e31671 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b31672 := hb (x (-7) 3)
        have b31673 := hb (x (-6) 2)
        have b31674 := hb (x (-5) 13)
        have b31675 := hb (x (-4) 12)
        clear * - r31669 e31670 e31671 b31672 b31673 b31674 b31675 d31656 d31660
        omega
      have d31676 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
        have r31677 := hand1 (x (-6) 2) (x (-6) 13)
        have b31678 := hb (x (-6) 2)
        have b31679 := hb (x (-6) 2 && x (-6) 13)
        clear * - r31677 b31678 b31679 d31668
        omega
      have d31680 : (x (-6) 10).toNat = 0 := by
        have r31681 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
        have b31682 := hb (x (-6) 2)
        have b31683 := hb (x (-6) 10)
        clear * - r31681 b31682 b31683 d31668
        omega
      have d31684 : (x (-7) 3).toNat = 0 := by
        have r31685 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31686 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e31687 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b31688 := hb (x (-7) 3)
        have b31689 := hb (x (-6) 2)
        have b31690 := hb (x (-5) 13)
        have b31691 := hb (x (-4) 12)
        clear * - r31685 e31686 e31687 b31688 b31689 b31690 b31691 d31656 d31660 d31668
        omega
      have d31692 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
        have r31693 := hand1 (x (-7) 3) (x (-7) 14)
        have b31694 := hb (x (-7) 3)
        have b31695 := hb (x (-7) 3 && x (-7) 14)
        clear * - r31693 b31694 b31695 d31684
        omega
      have d31696 : (x (-7) 11).toNat = 0 := by
        have r31697 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have b31698 := hb (x (-7) 3)
        have b31699 := hb (x (-7) 11)
        clear * - r31697 b31698 b31699 d31684
        omega
      have d31700 : (x (-4) 3).toNat = 1 := by
        have r31701 := hand1 (x (-4) 3) (x (-4) 12)
        have b31702 := hb (x (-4) 3)
        have b31703 := hb (x (-4) 3 && x (-4) 12)
        clear * - r31701 b31702 b31703 d31647
        omega
      have d31704 : (x (-1) 12).toNat = 0 := by
        have r31705 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31706 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e31707 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b31708 := hb (x (-4) 3)
        have b31709 := hb (x (-3) 2)
        have b31710 := hb (x (-2) 13)
        have b31711 := hb (x (-1) 12)
        clear * - r31705 e31706 e31707 b31708 b31709 b31710 b31711 d31700
        omega
      have d31712 : (x (-2) 13).toNat = 0 := by
        have r31713 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31714 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e31715 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b31716 := hb (x (-4) 3)
        have b31717 := hb (x (-3) 2)
        have b31718 := hb (x (-2) 13)
        have b31719 := hb (x (-1) 12)
        clear * - r31713 e31714 e31715 b31716 b31717 b31718 b31719 d31704 d31700
        omega
      have d31720 : (x (-3) 2).toNat = 0 := by
        have r31721 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31722 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e31723 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b31724 := hb (x (-4) 3)
        have b31725 := hb (x (-3) 2)
        have b31726 := hb (x (-2) 13)
        have b31727 := hb (x (-1) 12)
        clear * - r31721 e31722 e31723 b31724 b31725 b31726 b31727 d31704 d31712 d31700
        omega
      have d31728 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
        have r31729 := hand1 (x (-3) 2) (x (-3) 12)
        have b31730 := hb (x (-3) 2)
        have b31731 := hb (x (-3) 2 && x (-3) 12)
        clear * - r31729 b31730 b31731 d31720
        omega
      have d31732 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
        have r31733 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31734 := hb (x (-6) 5)
        have b31735 := hb (x (-1) 10)
        have b31736 := hb (x (-2) 1 && x (-2) 11)
        have b31737 := hb (x (-3) 2 && x (-3) 12)
        have b31738 := hb (x (-4) 3 && x (-4) 13)
        have b31739 := hb (x (-5) 4 && x (-5) 14)
        clear * - r31733 b31734 b31735 b31736 b31737 b31738 b31739 g11 g120 d31728 d31579 d31595
        omega
      have d31740 : (x (-4) 13).toNat = 1 := by
        have r31741 := hand2 (x (-4) 3) (x (-4) 13)
        have b31742 := hb (x (-4) 13)
        have b31743 := hb (x (-4) 3 && x (-4) 13)
        clear * - r31741 b31742 b31743 d31732
        omega
      have d31744 : (x (-4) 1).toNat = 1 := by
        have r31745 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b31746 := hb (x (-4) 1)
        have b31747 := hb (x (-4) 13)
        clear * - r31745 b31746 b31747 d31740
        omega
      have d31748 : (x (-3) 14).toNat = 0 := by
        have r31749 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31750 := hb (x (-4) 1)
        have b31751 := hb (x (-3) 14)
        clear * - r31749 b31750 b31751 d31744
        omega
      have d31752 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
        have r31753 := hand2 (x (-3) 1) (x (-3) 14)
        have b31754 := hb (x (-3) 14)
        have b31755 := hb (x (-3) 1 && x (-3) 14)
        clear * - r31753 b31754 b31755 d31748
        omega
      have d31756 : (x (-4) 2).toNat = 1 := by
        have r31757 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31758 := hb (x (-4) 2)
        have b31759 := hb (x (-2) 13)
        have b31760 := hb (x (-3) 1 && x (-3) 14)
        clear * - r31757 b31758 b31759 b31760 d31712 d31752
        omega
      have d31761 : (x (-4) 14).toNat = 1 := by
        have r31762 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
        have b31763 := hb (x (-4) 2)
        have b31764 := hb (x (-4) 14)
        clear * - r31762 b31763 b31764 d31756
        omega
      have d31765 : (x (-5) 1).toNat = 0 := by
        have r31766 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31767 := hb (x (-5) 1)
        have b31768 := hb (x (-4) 14)
        clear * - r31766 b31767 b31768 d31761
        omega
      have d31769 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
        have r31770 := hand1 (x (-5) 1) (x (-5) 12)
        have b31771 := hb (x (-5) 1)
        have b31772 := hb (x (-5) 1 && x (-5) 12)
        clear * - r31770 b31771 b31772 d31765
        omega
      have d31773 : (x (-8) 4).toNat = 1 := by
        have r31774 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31775 := hb (x (-8) 4)
        have b31776 := hb (x (-4) 11)
        have b31777 := hb (x (-5) 1 && x (-5) 12)
        have b31778 := hb (x (-6) 2 && x (-6) 13)
        have b31779 := hb (x (-7) 3 && x (-7) 14)
        clear * - r31774 b31775 b31776 b31777 b31778 b31779 d31543 d31769 d31676 d31692
        omega
      have d31780 : (x (-8) 12).toNat = 1 := by
        have r31781 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
        have b31782 := hb (x (-8) 4)
        have b31783 := hb (x (-8) 12)
        clear * - r31781 b31782 b31783 d31773
        omega
      have d31784 : (x (-9) 13).toNat = 0 := by
        have r31785 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31786 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e31787 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b31788 := hb (x (-11) 3)
        have b31789 := hb (x (-10) 2)
        have b31790 := hb (x (-9) 13)
        have b31791 := hb (x (-8) 12)
        clear * - r31785 e31786 e31787 b31788 b31789 b31790 b31791 d31780
        omega
      have d31792 : (x (-9) 8 && x (-9) 13).toNat = 0 := by
        have r31793 := hand2 (x (-9) 8) (x (-9) 13)
        have b31794 := hb (x (-9) 13)
        have b31795 := hb (x (-9) 8 && x (-9) 13)
        clear * - r31793 b31794 b31795 d31784
        omega
      have d31796 : (x (-9) 5).toNat = 0 := by
        have r31797 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
        have b31798 := hb (x (-9) 5)
        have b31799 := hb (x (-9) 13)
        clear * - r31797 b31798 b31799 d31784
        omega
      have d31800 : (x (-5) 9).toNat = 0 := by
        have r31801 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
        have b31802 := hb (x (-5) 1)
        have b31803 := hb (x (-5) 9)
        clear * - r31801 b31802 b31803 d31765
        omega
      have d31804 : (x (-2) 12).toNat = 0 := by
        have r31805 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31806 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e31807 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b31808 := hb (x (-5) 3)
        have b31809 := hb (x (-4) 2)
        have b31810 := hb (x (-3) 13)
        have b31811 := hb (x (-2) 12)
        clear * - r31805 e31806 e31807 b31808 b31809 b31810 b31811 d31756
        omega
      have d31812 : (x (-3) 13).toNat = 0 := by
        have r31813 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31814 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e31815 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b31816 := hb (x (-5) 3)
        have b31817 := hb (x (-4) 2)
        have b31818 := hb (x (-3) 13)
        have b31819 := hb (x (-2) 12)
        clear * - r31813 e31814 e31815 b31816 b31817 b31818 b31819 d31804 d31756
        omega
      have d31820 : (x (-5) 3).toNat = 0 := by
        have r31821 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31822 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e31823 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have b31824 := hb (x (-5) 3)
        have b31825 := hb (x (-4) 2)
        have b31826 := hb (x (-3) 13)
        have b31827 := hb (x (-2) 12)
        clear * - r31821 e31822 e31823 b31824 b31825 b31826 b31827 d31804 d31812 d31756
        omega
      have d31828 : (x (-5) 3 && x (-5) 12).toNat = 0 := by
        have r31829 := hand1 (x (-5) 3) (x (-5) 12)
        have b31830 := hb (x (-5) 3)
        have b31831 := hb (x (-5) 3 && x (-5) 12)
        clear * - r31829 b31830 b31831 d31820
        omega
      have d31832 : (x (-5) 11).toNat = 0 := by
        have r31833 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
        have b31834 := hb (x (-5) 3)
        have b31835 := hb (x (-5) 11)
        clear * - r31833 b31834 b31835 d31820
        omega
      have d31836 : (x (-3) 2 && x (-3) 9).toNat = 0 := by
        have r31837 := hand1 (x (-3) 2) (x (-3) 9)
        have b31838 := hb (x (-3) 2)
        have b31839 := hb (x (-3) 2 && x (-3) 9)
        clear * - r31837 b31838 b31839 d31720
        omega
      have d31840 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
        have r31841 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31842 := hb (x (-3) 2)
        have b31843 := hb (x (-1) 13)
        have b31844 := hb (x (-2) 1 && x (-2) 14)
        clear * - r31841 b31842 b31843 b31844 g13 d31720
        omega
      have d31845 : (x (-2) 14).toNat = 1 := by
        have r31846 := hand2 (x (-2) 1) (x (-2) 14)
        have b31847 := hb (x (-2) 14)
        have b31848 := hb (x (-2) 1 && x (-2) 14)
        clear * - r31846 b31847 b31848 d31840
        omega
      have d31849 : (x (-3) 1).toNat = 0 := by
        have r31850 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31851 := hb (x (-3) 1)
        have b31852 := hb (x (-2) 14)
        clear * - r31850 b31851 b31852 d31845
        omega
      have d31853 : (x (-3) 9).toNat = 0 := by
        have r31854 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
        have b31855 := hb (x (-3) 1)
        have b31856 := hb (x (-3) 9)
        clear * - r31854 b31855 b31856 d31849
        omega
      have d31857 : (x (-2) 1).toNat = 1 := by
        have r31858 := hand1 (x (-2) 1) (x (-2) 14)
        have b31859 := hb (x (-2) 1)
        have b31860 := hb (x (-2) 1 && x (-2) 14)
        clear * - r31858 b31859 b31860 d31840
        omega
      have d31861 : (x (-1) 14).toNat = 0 := by
        have r31862 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31863 := hb (x (-2) 1)
        have b31864 := hb (x (-1) 14)
        clear * - r31862 b31863 b31864 d31857
        omega
      have d31865 : (x (-1) 6).toNat = 0 := by
        have r31866 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
        have b31867 := hb (x (-1) 6)
        have b31868 := hb (x (-1) 14)
        clear * - r31866 b31867 b31868 d31861
        omega
      have d31869 : (x (-8) 7).toNat = 0 := by
        have r31870 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31871 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e31872 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e31873 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e31874 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e31875 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e31876 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b31877 := hb (x (-8) 7)
        have b31878 := hb (x (-7) 6)
        have b31879 := hb (x (-6) 5)
        have b31880 := hb (x (-5) 4)
        have b31881 := hb (x (-4) 11)
        have b31882 := hb (x (-3) 10)
        have b31883 := hb (x (-2) 9)
        have b31884 := hb (x (-1) 8)
        clear * - r31870 e31871 e31872 e31873 e31874 e31875 e31876 b31877 b31878 b31879 b31880 b31881 b31882 b31883 b31884 f31506 d31507 d31523 d31543 d31563 d31595 d31623
        omega
      have d31885 : (x (-8) 7 && x (-8) 14).toNat = 0 := by
        have r31886 := hand1 (x (-8) 7) (x (-8) 14)
        have b31887 := hb (x (-8) 7)
        have b31888 := hb (x (-8) 7 && x (-8) 14)
        clear * - r31886 b31887 b31888 d31869
        omega
      have d31889 : (x (-8) 7 && x (-8) 12).toNat = 0 := by
        have r31890 := hand1 (x (-8) 7) (x (-8) 12)
        have b31891 := hb (x (-8) 7)
        have b31892 := hb (x (-8) 7 && x (-8) 12)
        clear * - r31890 b31891 b31892 d31869
        omega
      have d31893 : (x (-4) 8).toNat = 0 := by
        have r31894 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31895 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e31896 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e31897 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e31898 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e31899 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e31900 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have b31901 := hb (x (-11) 7)
        have b31902 := hb (x (-10) 6)
        have b31903 := hb (x (-9) 5)
        have b31904 := hb (x (-8) 4)
        have b31905 := hb (x (-7) 11)
        have b31906 := hb (x (-6) 10)
        have b31907 := hb (x (-5) 9)
        have b31908 := hb (x (-4) 8)
        clear * - r31894 e31895 e31896 e31897 e31898 e31899 e31900 b31901 b31902 b31903 b31904 b31905 b31906 b31907 b31908 d31800 d31680 d31696 d31773 d31796
        omega
      have d31909 : (x (-4) 3 && x (-4) 8).toNat = 0 := by
        have r31910 := hand2 (x (-4) 3) (x (-4) 8)
        have b31911 := hb (x (-4) 8)
        have b31912 := hb (x (-4) 3 && x (-4) 8)
        clear * - r31910 b31911 b31912 d31893
        omega
      have r31913 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r31914 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e31915 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e31916 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e31917 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e31918 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e31919 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e31920 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have r31921 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e31922 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e31923 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e31924 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e31925 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e31926 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e31927 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have r31928 : 1 ≤ (x (-1) 5).toNat + (x (-2) 1 && x (-2) 6).toNat + (x (-3) 2 && x (-3) 7).toNat + (x (-4) 3 && x (-4) 8).toNat + (x (-5) 4 && x (-5) 9).toNat + (x (-6) 5 && x (-6) 10).toNat + (x (-7) 6 && x (-7) 11).toNat + (x (-8) 7 && x (-8) 12).toNat + (x (-9) 8 && x (-9) 13).toNat + (x (-10) 9 && x (-10) 14).toNat + (x (-11) 10).toNat := by have q := hcov5 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r31929 : 1 ≤ (x (-1) 7).toNat + (x (-2) 1 && x (-2) 8).toNat + (x (-3) 2 && x (-3) 9).toNat + (x (-4) 3 && x (-4) 10).toNat + (x (-5) 4 && x (-5) 11).toNat + (x (-6) 5 && x (-6) 12).toNat + (x (-7) 6 && x (-7) 13).toNat + (x (-8) 7 && x (-8) 14).toNat + (x (-9) 8).toNat := by have q := hcov7 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r31930 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r31931 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r31932 := hand1 (x (-10) 9) (x (-10) 14)
      have r31933 := hand2 (x (-2) 1) (x (-2) 8)
      have r31934 := hand2 (x (-4) 3) (x (-4) 10)
      have r31935 := hand1 (x (-6) 4) (x (-6) 13)
      have r31936 := hand1 (x (-7) 5) (x (-7) 14)
      have r31937 := hand2 (x 4 1) (x 4 10)
      have r31938 := hand2 (x 3 2) (x 3 11)
      linarith only [r31913, r31914, e31915, e31916, e31917, e31918, e31919, e31920, r31921, e31922, e31923, e31924, e31925, e31926, e31927, r31928, r31929, r31930, r31931, r31932, r31933, r31934, r31935, r31936, r31937, r31938, d31869, d31623, d31595, d31563, d31832, d31700, d31720, d31853, d31857, d31507, g9, d31865, g17, g25, g30, g65, g66, d31909, d31591, d31619, d31643, d31889, d31792, d31836, d31587, d31615, d31639, d31885, d31539, d31559, d31828, g114, g115, g116]
  · have f31998 : (x 1 7).toNat = 1 := by rw [h27604]; rfl
    have d31999 : (x 8 8).toNat = 0 := by
      have r32000 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32001 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e32002 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e32003 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e32004 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e32005 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e32006 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b32007 := hb (x 1 7)
      have b32008 := hb (x 2 6)
      have b32009 := hb (x 3 5)
      have b32010 := hb (x 4 4)
      have b32011 := hb (x 5 11)
      have b32012 := hb (x 6 10)
      have b32013 := hb (x 7 9)
      have b32014 := hb (x 8 8)
      clear * - r32000 e32001 e32002 e32003 e32004 e32005 e32006 b32007 b32008 b32009 b32010 b32011 b32012 b32013 b32014 f31998
      omega
    have d32015 : (x 8 3 && x 8 8).toNat = 0 := by
      have r32016 := hand2 (x 8 3) (x 8 8)
      have b32017 := hb (x 8 8)
      have b32018 := hb (x 8 3 && x 8 8)
      clear * - r32016 b32017 b32018 d31999
      omega
    have d32019 : (x 8 4 && x 8 8).toNat = 0 := by
      have r32020 := hand2 (x 8 4) (x 8 8)
      have b32021 := hb (x 8 8)
      have b32022 := hb (x 8 4 && x 8 8)
      clear * - r32020 b32021 b32022 d31999
      omega
    have d32023 : (x 7 9).toNat = 0 := by
      have r32024 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32025 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e32026 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e32027 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e32028 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e32029 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e32030 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b32031 := hb (x 1 7)
      have b32032 := hb (x 2 6)
      have b32033 := hb (x 3 5)
      have b32034 := hb (x 4 4)
      have b32035 := hb (x 5 11)
      have b32036 := hb (x 6 10)
      have b32037 := hb (x 7 9)
      have b32038 := hb (x 8 8)
      clear * - r32024 e32025 e32026 e32027 e32028 e32029 e32030 b32031 b32032 b32033 b32034 b32035 b32036 b32037 b32038 d31999 f31998
      omega
    have d32039 : (x 7 4 && x 7 9).toNat = 0 := by
      have r32040 := hand2 (x 7 4) (x 7 9)
      have b32041 := hb (x 7 9)
      have b32042 := hb (x 7 4 && x 7 9)
      clear * - r32040 b32041 b32042 d32023
      omega
    have d32043 : (x 7 5 && x 7 9).toNat = 0 := by
      have r32044 := hand2 (x 7 5) (x 7 9)
      have b32045 := hb (x 7 9)
      have b32046 := hb (x 7 5 && x 7 9)
      clear * - r32044 b32045 b32046 d32023
      omega
    have d32047 : (x 6 10).toNat = 0 := by
      have r32048 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32049 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e32050 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e32051 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e32052 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e32053 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e32054 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b32055 := hb (x 1 7)
      have b32056 := hb (x 2 6)
      have b32057 := hb (x 3 5)
      have b32058 := hb (x 4 4)
      have b32059 := hb (x 5 11)
      have b32060 := hb (x 6 10)
      have b32061 := hb (x 7 9)
      have b32062 := hb (x 8 8)
      clear * - r32048 e32049 e32050 e32051 e32052 e32053 e32054 b32055 b32056 b32057 b32058 b32059 b32060 b32061 b32062 d31999 d32023 f31998
      omega
    have d32063 : (x 6 1 && x 6 10).toNat = 0 := by
      have r32064 := hand2 (x 6 1) (x 6 10)
      have b32065 := hb (x 6 10)
      have b32066 := hb (x 6 1 && x 6 10)
      clear * - r32064 b32065 b32066 d32047
      omega
    have d32067 : (x 6 5 && x 6 10).toNat = 0 := by
      have r32068 := hand2 (x 6 5) (x 6 10)
      have b32069 := hb (x 6 10)
      have b32070 := hb (x 6 5 && x 6 10)
      clear * - r32068 b32069 b32070 d32047
      omega
    have d32071 : (x 6 6 && x 6 10).toNat = 0 := by
      have r32072 := hand2 (x 6 6) (x 6 10)
      have b32073 := hb (x 6 10)
      have b32074 := hb (x 6 6 && x 6 10)
      clear * - r32072 b32073 b32074 d32047
      omega
    have d32075 : (x 5 11).toNat = 0 := by
      have r32076 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32077 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e32078 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e32079 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e32080 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e32081 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e32082 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b32083 := hb (x 1 7)
      have b32084 := hb (x 2 6)
      have b32085 := hb (x 3 5)
      have b32086 := hb (x 4 4)
      have b32087 := hb (x 5 11)
      have b32088 := hb (x 6 10)
      have b32089 := hb (x 7 9)
      have b32090 := hb (x 8 8)
      clear * - r32076 e32077 e32078 e32079 e32080 e32081 e32082 b32083 b32084 b32085 b32086 b32087 b32088 b32089 b32090 d31999 d32023 d32047 f31998
      omega
    have d32091 : (x 5 1 && x 5 11).toNat = 0 := by
      have r32092 := hand2 (x 5 1) (x 5 11)
      have b32093 := hb (x 5 11)
      have b32094 := hb (x 5 1 && x 5 11)
      clear * - r32092 b32093 b32094 d32075
      omega
    have d32095 : (x 5 2 && x 5 11).toNat = 0 := by
      have r32096 := hand2 (x 5 2) (x 5 11)
      have b32097 := hb (x 5 11)
      have b32098 := hb (x 5 2 && x 5 11)
      clear * - r32096 b32097 b32098 d32075
      omega
    have d32099 : (x 4 3 && x 4 12).toNat = 1 := by
      have r32100 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32101 := hb (x 1 6)
      have b32102 := hb (x 7 9)
      have b32103 := hb (x 6 1 && x 6 10)
      have b32104 := hb (x 5 2 && x 5 11)
      have b32105 := hb (x 4 3 && x 4 12)
      have b32106 := hb (x 3 4 && x 3 13)
      have b32107 := hb (x 2 5 && x 2 14)
      clear * - r32100 b32101 b32102 b32103 b32104 b32105 b32106 b32107 d32023 d32063 d32095 g117 g118 g26
      omega
    have d32108 : (x 4 12).toNat = 1 := by
      have r32109 := hand2 (x 4 3) (x 4 12)
      have b32110 := hb (x 4 12)
      have b32111 := hb (x 4 3 && x 4 12)
      clear * - r32109 b32110 b32111 d32099
      omega
    have d32112 : (x 3 13).toNat = 0 := by
      have r32113 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32114 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e32115 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b32116 := hb (x 1 3)
      have b32117 := hb (x 2 2)
      have b32118 := hb (x 3 13)
      have b32119 := hb (x 4 12)
      clear * - r32113 e32114 e32115 b32116 b32117 b32118 b32119 d32108 g23
      omega
    have d32120 : (x 3 3 && x 3 13).toNat = 0 := by
      have r32121 := hand2 (x 3 3) (x 3 13)
      have b32122 := hb (x 3 13)
      have b32123 := hb (x 3 3 && x 3 13)
      clear * - r32121 b32122 b32123 d32112
      omega
    have d32124 : (x 4 2 && x 4 12).toNat = 1 := by
      have r32125 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32126 := hb (x 1 5)
      have b32127 := hb (x 6 10)
      have b32128 := hb (x 5 1 && x 5 11)
      have b32129 := hb (x 4 2 && x 4 12)
      have b32130 := hb (x 3 3 && x 3 13)
      have b32131 := hb (x 2 4 && x 2 14)
      clear * - r32125 b32126 b32127 b32128 b32129 b32130 b32131 d32047 d32091 d32120 g124 g25
      omega
    have d32132 : (x 4 2).toNat = 1 := by
      have r32133 := hand1 (x 4 2) (x 4 12)
      have b32134 := hb (x 4 2)
      have b32135 := hb (x 4 2 && x 4 12)
      clear * - r32133 b32134 b32135 d32124
      omega
    have d32136 : (x 6 12).toNat = 0 := by
      have r32137 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32138 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e32139 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b32140 := hb (x 3 3)
      have b32141 := hb (x 4 2)
      have b32142 := hb (x 5 13)
      have b32143 := hb (x 6 12)
      clear * - r32137 e32138 e32139 b32140 b32141 b32142 b32143 d32132
      omega
    have d32144 : (x 5 13).toNat = 0 := by
      have r32145 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32146 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e32147 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b32148 := hb (x 3 3)
      have b32149 := hb (x 4 2)
      have b32150 := hb (x 5 13)
      have b32151 := hb (x 6 12)
      clear * - r32145 e32146 e32147 b32148 b32149 b32150 b32151 d32136 d32132
      omega
    have d32152 : (x 3 5).toNat = 0 := by
      have r32153 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b32154 := hb (x 3 5)
      have b32155 := hb (x 3 13)
      clear * - r32153 b32154 b32155 d32112
      omega
    have d32156 : (x 2 1 && x 2 14).toNat = 1 := by
      have r32157 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32158 := hb (x 1 2)
      have b32159 := hb (x 3 13)
      have b32160 := hb (x 2 1 && x 2 14)
      clear * - r32157 b32158 b32159 b32160 d32112 g22
      omega
    have d32161 : (x 2 1).toNat = 1 := by
      have r32162 := hand1 (x 2 1) (x 2 14)
      have b32163 := hb (x 2 1)
      have b32164 := hb (x 2 1 && x 2 14)
      clear * - r32162 b32163 b32164 d32156
      omega
    have d32165 : (x 3 14).toNat = 0 := by
      have r32166 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32167 := hb (x 2 1)
      have b32168 := hb (x 3 14)
      clear * - r32166 b32167 b32168 d32161
      omega
    have d32169 : (x 3 2).toNat = 0 := by
      have r32170 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b32171 := hb (x 3 2)
      have b32172 := hb (x 3 14)
      clear * - r32170 b32171 b32172 d32165
      omega
    have d32173 : (x 4 1 && x 4 14).toNat = 1 := by
      have r32174 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32175 := hb (x 3 2)
      have b32176 := hb (x 5 13)
      have b32177 := hb (x 4 1 && x 4 14)
      clear * - r32174 b32175 b32176 b32177 d32144 d32169
      omega
    have d32178 : (x 4 1).toNat = 1 := by
      have r32179 := hand1 (x 4 1) (x 4 14)
      have b32180 := hb (x 4 1)
      have b32181 := hb (x 4 1 && x 4 14)
      clear * - r32179 b32180 b32181 d32173
      omega
    have d32182 : (x 5 14).toNat = 0 := by
      have r32183 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32184 := hb (x 4 1)
      have b32185 := hb (x 5 14)
      clear * - r32183 b32184 b32185 d32178
      omega
    have d32186 : (x 5 3 && x 5 14).toNat = 0 := by
      have r32187 := hand2 (x 5 3) (x 5 14)
      have b32188 := hb (x 5 14)
      have b32189 := hb (x 5 3 && x 5 14)
      clear * - r32187 b32188 b32189 d32182
      omega
    have d32190 : (x 5 6).toNat = 0 := by
      have r32191 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
      have b32192 := hb (x 5 6)
      have b32193 := hb (x 5 14)
      clear * - r32191 b32192 b32193 d32182
      omega
    have d32194 : (x 5 6 && x 5 11).toNat = 0 := by
      have r32195 := hand1 (x 5 6) (x 5 11)
      have b32196 := hb (x 5 6)
      have b32197 := hb (x 5 6 && x 5 11)
      clear * - r32195 b32196 b32197 d32190
      omega
    have d32198 : (x 5 2).toNat = 0 := by
      have r32199 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b32200 := hb (x 5 2)
      have b32201 := hb (x 5 14)
      clear * - r32199 b32200 b32201 d32182
      omega
    have d32202 : (x 5 10).toNat = 0 := by
      have r32203 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
      have b32204 := hb (x 5 2)
      have b32205 := hb (x 5 10)
      clear * - r32203 b32204 b32205 d32198
      omega
    have d32206 : (x 5 3 && x 5 10).toNat = 0 := by
      have r32207 := hand2 (x 5 3) (x 5 10)
      have b32208 := hb (x 5 10)
      have b32209 := hb (x 5 3 && x 5 10)
      clear * - r32207 b32208 b32209 d32202
      omega
    have d32210 : (x 4 1 && x 4 11).toNat = 1 := by
      have r32211 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32212 := hb (x 0 5)
      have b32213 := hb (x 5 10)
      have b32214 := hb (x 4 1 && x 4 11)
      have b32215 := hb (x 3 2 && x 3 12)
      have b32216 := hb (x 2 3 && x 2 13)
      have b32217 := hb (x 1 4 && x 1 14)
      clear * - r32211 b32212 b32213 b32214 b32215 b32216 b32217 d32202 g121 g122 g123 g16
      omega
    have d32218 : (x 4 11).toNat = 1 := by
      have r32219 := hand2 (x 4 1) (x 4 11)
      have b32220 := hb (x 4 11)
      have b32221 := hb (x 4 1 && x 4 11)
      clear * - r32219 b32220 b32221 d32210
      omega
    have d32222 : (x 4 3).toNat = 1 := by
      have r32223 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b32224 := hb (x 4 3)
      have b32225 := hb (x 4 11)
      clear * - r32223 b32224 b32225 d32218
      omega
    have d32226 : (x 7 12).toNat = 0 := by
      have r32227 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32228 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e32229 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b32230 := hb (x 4 3)
      have b32231 := hb (x 5 2)
      have b32232 := hb (x 6 13)
      have b32233 := hb (x 7 12)
      clear * - r32227 e32228 e32229 b32230 b32231 b32232 b32233 d32198 d32222
      omega
    have d32234 : (x 7 1 && x 7 12).toNat = 0 := by
      have r32235 := hand2 (x 7 1) (x 7 12)
      have b32236 := hb (x 7 12)
      have b32237 := hb (x 7 1 && x 7 12)
      clear * - r32235 b32236 b32237 d32226
      omega
    have d32238 : (x 7 4).toNat = 0 := by
      have r32239 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
      have b32240 := hb (x 7 4)
      have b32241 := hb (x 7 12)
      clear * - r32239 b32240 b32241 d32226
      omega
    have d32242 : (x 6 13).toNat = 0 := by
      have r32243 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32244 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e32245 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b32246 := hb (x 4 3)
      have b32247 := hb (x 5 2)
      have b32248 := hb (x 6 13)
      have b32249 := hb (x 7 12)
      clear * - r32243 e32244 e32245 b32246 b32247 b32248 b32249 d32226 d32198 d32222
      omega
    have d32250 : (x 6 2 && x 6 13).toNat = 0 := by
      have r32251 := hand2 (x 6 2) (x 6 13)
      have b32252 := hb (x 6 13)
      have b32253 := hb (x 6 2 && x 6 13)
      clear * - r32251 b32252 b32253 d32242
      omega
    have d32254 : (x 6 5).toNat = 0 := by
      have r32255 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
      have b32256 := hb (x 6 5)
      have b32257 := hb (x 6 13)
      clear * - r32255 b32256 b32257 d32242
      omega
    have d32258 : (x 5 7 && x 5 11).toNat = 0 := by
      have r32259 := hand2 (x 5 7) (x 5 11)
      have b32260 := hb (x 5 11)
      have b32261 := hb (x 5 7 && x 5 11)
      clear * - r32259 b32260 b32261 d32075
      omega
    have d32262 : (x 4 4).toNat = 0 := by
      have r32263 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32264 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e32265 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e32266 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e32267 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e32268 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e32269 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b32270 := hb (x 1 7)
      have b32271 := hb (x 2 6)
      have b32272 := hb (x 3 5)
      have b32273 := hb (x 4 4)
      have b32274 := hb (x 5 11)
      have b32275 := hb (x 6 10)
      have b32276 := hb (x 7 9)
      have b32277 := hb (x 8 8)
      clear * - r32263 e32264 e32265 e32266 e32267 e32268 e32269 b32270 b32271 b32272 b32273 b32274 b32275 b32276 b32277 d31999 d32023 d32047 d32075 d32152 f31998
      omega
    have d32278 : (x 4 4 && x 4 11).toNat = 0 := by
      have r32279 := hand1 (x 4 4) (x 4 11)
      have b32280 := hb (x 4 4)
      have b32281 := hb (x 4 4 && x 4 11)
      clear * - r32279 b32280 b32281 d32262
      omega
    have d32282 : (x 8 11).toNat = 1 := by
      have r32283 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32284 := hb (x 4 4)
      have b32285 := hb (x 8 11)
      have b32286 := hb (x 7 1 && x 7 12)
      have b32287 := hb (x 6 2 && x 6 13)
      have b32288 := hb (x 5 3 && x 5 14)
      clear * - r32283 b32284 b32285 b32286 b32287 b32288 d32234 d32250 d32186 d32262
      omega
    have d32289 : (x 8 3).toNat = 1 := by
      have r32290 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b32291 := hb (x 8 3)
      have b32292 := hb (x 8 11)
      clear * - r32290 b32291 b32292 d32282
      omega
    have d32293 : (x 11 12).toNat = 0 := by
      have r32294 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32295 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e32296 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b32297 := hb (x 8 3)
      have b32298 := hb (x 9 2)
      have b32299 := hb (x 10 13)
      have b32300 := hb (x 11 12)
      clear * - r32294 e32295 e32296 b32297 b32298 b32299 b32300 d32289
      omega
    have d32301 : (x 11 4).toNat = 0 := by
      have r32302 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
      have b32303 := hb (x 11 4)
      have b32304 := hb (x 11 12)
      clear * - r32302 b32303 b32304 d32293
      omega
    have d32305 : (x 11 4 && x 11 13).toNat = 0 := by
      have r32306 := hand1 (x 11 4) (x 11 13)
      have b32307 := hb (x 11 4)
      have b32308 := hb (x 11 4 && x 11 13)
      clear * - r32306 b32307 b32308 d32301
      omega
    have d32309 : (x 10 13).toNat = 0 := by
      have r32310 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32311 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e32312 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b32313 := hb (x 8 3)
      have b32314 := hb (x 9 2)
      have b32315 := hb (x 10 13)
      have b32316 := hb (x 11 12)
      clear * - r32310 e32311 e32312 b32313 b32314 b32315 b32316 d32293 d32289
      omega
    have d32317 : (x 10 5).toNat = 0 := by
      have r32318 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
      have b32319 := hb (x 10 5)
      have b32320 := hb (x 10 13)
      clear * - r32318 b32319 b32320 d32309
      omega
    have d32321 : (x 10 5 && x 10 14).toNat = 0 := by
      have r32322 := hand1 (x 10 5) (x 10 14)
      have b32323 := hb (x 10 5)
      have b32324 := hb (x 10 5 && x 10 14)
      clear * - r32322 b32323 b32324 d32317
      omega
    have d32325 : (x 9 2).toNat = 0 := by
      have r32326 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32327 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e32328 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b32329 := hb (x 8 3)
      have b32330 := hb (x 9 2)
      have b32331 := hb (x 10 13)
      have b32332 := hb (x 11 12)
      clear * - r32326 e32327 e32328 b32329 b32330 b32331 b32332 d32293 d32309 d32289
      omega
    have d32333 : (x 9 2 && x 9 7).toNat = 0 := by
      have r32334 := hand1 (x 9 2) (x 9 7)
      have b32335 := hb (x 9 2)
      have b32336 := hb (x 9 2 && x 9 7)
      clear * - r32334 b32335 b32336 d32325
      omega
    have d32337 : (x 9 10).toNat = 0 := by
      have r32338 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
      have b32339 := hb (x 9 2)
      have b32340 := hb (x 9 10)
      clear * - r32338 b32339 b32340 d32325
      omega
    have d32341 : (x 11 8).toNat = 0 := by
      have r32342 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32343 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e32344 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e32345 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e32346 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e32347 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e32348 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b32349 := hb (x 4 7)
      have b32350 := hb (x 5 6)
      have b32351 := hb (x 6 5)
      have b32352 := hb (x 7 4)
      have b32353 := hb (x 8 11)
      have b32354 := hb (x 9 10)
      have b32355 := hb (x 10 9)
      have b32356 := hb (x 11 8)
      clear * - r32342 e32343 e32344 e32345 e32346 e32347 e32348 b32349 b32350 b32351 b32352 b32353 b32354 b32355 b32356 d32337 d32282 d32238 d32254 d32190
      omega
    have d32357 : (x 10 9).toNat = 0 := by
      have r32358 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32359 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e32360 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e32361 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e32362 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e32363 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e32364 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b32365 := hb (x 4 7)
      have b32366 := hb (x 5 6)
      have b32367 := hb (x 6 5)
      have b32368 := hb (x 7 4)
      have b32369 := hb (x 8 11)
      have b32370 := hb (x 9 10)
      have b32371 := hb (x 10 9)
      have b32372 := hb (x 11 8)
      clear * - r32358 e32359 e32360 e32361 e32362 e32363 e32364 b32365 b32366 b32367 b32368 b32369 b32370 b32371 b32372 d32341 d32337 d32282 d32238 d32254 d32190
      omega
    have d32373 : (x 4 7).toNat = 0 := by
      have r32374 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32375 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e32376 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e32377 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e32378 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e32379 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e32380 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have b32381 := hb (x 4 7)
      have b32382 := hb (x 5 6)
      have b32383 := hb (x 6 5)
      have b32384 := hb (x 7 4)
      have b32385 := hb (x 8 11)
      have b32386 := hb (x 9 10)
      have b32387 := hb (x 10 9)
      have b32388 := hb (x 11 8)
      clear * - r32374 e32375 e32376 e32377 e32378 e32379 e32380 b32381 b32382 b32383 b32384 b32385 b32386 b32387 b32388 d32341 d32357 d32337 d32282 d32238 d32254 d32190
      omega
    have d32389 : (x 4 7 && x 4 12).toNat = 0 := by
      have r32390 := hand1 (x 4 7) (x 4 12)
      have b32391 := hb (x 4 7)
      have b32392 := hb (x 4 7 && x 4 12)
      clear * - r32390 b32391 b32392 d32373
      omega
    have d32393 : (x 7 8).toNat = 0 := by
      have r32394 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32395 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e32396 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e32397 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e32398 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e32399 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e32400 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b32401 := hb (x 0 7)
      have b32402 := hb (x 1 6)
      have b32403 := hb (x 2 5)
      have b32404 := hb (x 3 4)
      have b32405 := hb (x 4 11)
      have b32406 := hb (x 5 10)
      have b32407 := hb (x 6 9)
      have b32408 := hb (x 7 8)
      clear * - r32394 e32395 e32396 e32397 e32398 e32399 e32400 b32401 b32402 b32403 b32404 b32405 b32406 b32407 b32408 d32202 d32218 g35 g31 g26 g18
      omega
    have d32409 : (x 7 1 && x 7 8).toNat = 0 := by
      have r32410 := hand2 (x 7 1) (x 7 8)
      have b32411 := hb (x 7 8)
      have b32412 := hb (x 7 1 && x 7 8)
      clear * - r32410 b32411 b32412 d32393
      omega
    have d32413 : (x 6 9).toNat = 0 := by
      have r32414 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32415 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e32416 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e32417 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e32418 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e32419 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e32420 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have b32421 := hb (x 0 7)
      have b32422 := hb (x 1 6)
      have b32423 := hb (x 2 5)
      have b32424 := hb (x 3 4)
      have b32425 := hb (x 4 11)
      have b32426 := hb (x 5 10)
      have b32427 := hb (x 6 9)
      have b32428 := hb (x 7 8)
      clear * - r32414 e32415 e32416 e32417 e32418 e32419 e32420 b32421 b32422 b32423 b32424 b32425 b32426 b32427 b32428 d32393 d32202 d32218 g35 g31 g26 g18
      omega
    have d32429 : (x 6 2 && x 6 9).toNat = 0 := by
      have r32430 := hand2 (x 6 2) (x 6 9)
      have b32431 := hb (x 6 9)
      have b32432 := hb (x 6 2 && x 6 9)
      clear * - r32430 b32431 b32432 d32413
      omega
    have d32433 : (x 8 7).toNat = 1 := by
      have r32434 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b32435 := hb (x 0 8)
      have b32436 := hb (x 8 7)
      have b32437 := hb (x 7 1 && x 7 8)
      have b32438 := hb (x 6 2 && x 6 9)
      have b32439 := hb (x 5 3 && x 5 10)
      have b32440 := hb (x 4 4 && x 4 11)
      have b32441 := hb (x 3 5 && x 3 12)
      have b32442 := hb (x 2 6 && x 2 13)
      have b32443 := hb (x 1 7 && x 1 14)
      clear * - r32434 b32435 b32436 b32437 b32438 b32439 b32440 b32441 b32442 b32443 d32409 d32429 d32206 d32278 g106 g107 g108 g19
      omega
    have d32444 : (x 15 8).toNat = 0 := by
      have r32445 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32446 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e32447 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e32448 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e32449 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e32450 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e32451 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b32452 := hb (x 8 7)
      have b32453 := hb (x 9 6)
      have b32454 := hb (x 10 5)
      have b32455 := hb (x 11 4)
      have b32456 := hb (x 12 11)
      have b32457 := hb (x 13 10)
      have b32458 := hb (x 14 9)
      have b32459 := hb (x 15 8)
      clear * - r32445 e32446 e32447 e32448 e32449 e32450 e32451 b32452 b32453 b32454 b32455 b32456 b32457 b32458 b32459 d32301 d32317 d32433
      omega
    have d32460 : (x 14 9).toNat = 0 := by
      have r32461 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32462 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e32463 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e32464 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e32465 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e32466 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e32467 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b32468 := hb (x 8 7)
      have b32469 := hb (x 9 6)
      have b32470 := hb (x 10 5)
      have b32471 := hb (x 11 4)
      have b32472 := hb (x 12 11)
      have b32473 := hb (x 13 10)
      have b32474 := hb (x 14 9)
      have b32475 := hb (x 15 8)
      clear * - r32461 e32462 e32463 e32464 e32465 e32466 e32467 b32468 b32469 b32470 b32471 b32472 b32473 b32474 b32475 d32444 d32301 d32317 d32433
      omega
    have d32476 : (x 13 10).toNat = 0 := by
      have r32477 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32478 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e32479 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e32480 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e32481 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e32482 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e32483 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b32484 := hb (x 8 7)
      have b32485 := hb (x 9 6)
      have b32486 := hb (x 10 5)
      have b32487 := hb (x 11 4)
      have b32488 := hb (x 12 11)
      have b32489 := hb (x 13 10)
      have b32490 := hb (x 14 9)
      have b32491 := hb (x 15 8)
      clear * - r32477 e32478 e32479 e32480 e32481 e32482 e32483 b32484 b32485 b32486 b32487 b32488 b32489 b32490 b32491 d32444 d32460 d32301 d32317 d32433
      omega
    have d32492 : (x 12 11).toNat = 0 := by
      have r32493 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32494 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e32495 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e32496 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e32497 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e32498 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e32499 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b32500 := hb (x 8 7)
      have b32501 := hb (x 9 6)
      have b32502 := hb (x 10 5)
      have b32503 := hb (x 11 4)
      have b32504 := hb (x 12 11)
      have b32505 := hb (x 13 10)
      have b32506 := hb (x 14 9)
      have b32507 := hb (x 15 8)
      clear * - r32493 e32494 e32495 e32496 e32497 e32498 e32499 b32500 b32501 b32502 b32503 b32504 b32505 b32506 b32507 d32444 d32460 d32476 d32301 d32317 d32433
      omega
    have d32508 : (x 9 6).toNat = 0 := by
      have r32509 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e32510 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e32511 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e32512 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e32513 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e32514 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e32515 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b32516 := hb (x 8 7)
      have b32517 := hb (x 9 6)
      have b32518 := hb (x 10 5)
      have b32519 := hb (x 11 4)
      have b32520 := hb (x 12 11)
      have b32521 := hb (x 13 10)
      have b32522 := hb (x 14 9)
      have b32523 := hb (x 15 8)
      clear * - r32509 e32510 e32511 e32512 e32513 e32514 e32515 b32516 b32517 b32518 b32519 b32520 b32521 b32522 b32523 d32444 d32460 d32476 d32492 d32301 d32317 d32433
      omega
    have r32524 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32525 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e32526 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e32527 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e32528 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e32529 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e32530 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have r32531 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32532 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e32533 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have r32534 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := by have q := hcov4 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e32535 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
    have e32536 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
    have r32537 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32538 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r32539 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
    have r32540 := hand1 (x 10 2) (x 10 6)
    have r32541 := hand1 (x 9 3) (x 9 7)
    have r32542 := hand2 (x 10 1) (x 10 6)
    have r32543 := hand2 (x 14 1) (x 14 10)
    have r32544 := hand2 (x 13 2) (x 13 11)
    have r32545 := hand2 (x 12 3) (x 12 12)
    linarith only [r32524, e32525, e32526, e32527, e32528, e32529, e32530, r32531, e32532, e32533, r32534, e32535, e32536, r32537, r32538, r32539, r32540, r32541, r32542, r32543, r32544, r32545, g27, g28, g33, d32508, d32019, d32043, d32071, d32258, g63, g64, d32333, d32015, d32039, d32067, d32194, d32389, g77, g78, d32305, d32321]

theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a11000100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 7).toNat = 0)
    (g1 : (x (-3) 6).toNat = 0)
    (g2 : (x (-3) 7).toNat = 0)
    (g3 : (x (-3) 11).toNat = 0)
    (g4 : (x (-2) 5).toNat = 0)
    (g5 : (x (-2) 6).toNat = 0)
    (g6 : (x (-2) 10).toNat = 0)
    (g7 : (x (-2) 11).toNat = 0)
    (g8 : (x (-1) 4).toNat = 0)
    (g9 : (x (-1) 5).toNat = 0)
    (g10 : (x (-1) 9).toNat = 0)
    (g11 : (x (-1) 10).toNat = 0)
    (g12 : (x (-1) 11).toNat = 0)
    (g13 : (x (-1) 13).toNat = 0)
    (g14 : (x 0 3).toNat = 1)
    (g15 : (x 0 4).toNat = 1)
    (g16 : (x 0 5).toNat = 0)
    (g17 : (x 0 6).toNat = 0)
    (g18 : (x 0 7).toNat = 0)
    (g19 : (x 0 8).toNat = 0)
    (g20 : (x 0 11).toNat = 1)
    (g21 : (x 0 13).toNat = 1)
    (g22 : (x 1 2).toNat = 0)
    (g23 : (x 1 3).toNat = 0)
    (g24 : (x 1 4).toNat = 0)
    (g25 : (x 1 5).toNat = 0)
    (g26 : (x 1 6).toNat = 0)
    (g27 : (x 1 10).toNat = 0)
    (g28 : (x 1 11).toNat = 0)
    (g29 : (x 1 12).toNat = 0)
    (g30 : (x 2 4).toNat = 0)
    (g31 : (x 2 5).toNat = 0)
    (g32 : (x 2 9).toNat = 0)
    (g33 : (x 2 10).toNat = 0)
    (g34 : (x 2 14).toNat = 1)
    (g35 : (x 3 4).toNat = 0)
    (g36 : (x 3 8).toNat = 0)
    (g37 : (x 0 2 && x 0 6).toNat = 0)
    (g38 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g39 : (x (-2) 4 && x (-2) 8).toNat = 0)
    (g40 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g41 : (x (-4) 6 && x (-4) 10).toNat = 0)
    (g42 : (x (-5) 7 && x (-5) 11).toNat = 0)
    (g43 : (x 1 2 && x 1 6).toNat = 0)
    (g44 : (x 0 3 && x 0 7).toNat = 0)
    (g45 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g46 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g47 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g48 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g49 : (x 0 4 && x 0 8).toNat = 0)
    (g50 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g51 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g52 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g53 : (x 3 4 && x 3 8).toNat = 0)
    (g54 : (x 2 5 && x 2 9).toNat = 0)
    (g55 : (x 1 6 && x 1 10).toNat = 0)
    (g56 : (x 0 7 && x 0 11).toNat = 0)
    (g57 : (x 4 4 && x 4 8).toNat = 0)
    (g58 : (x 3 5 && x 3 9).toNat = 0)
    (g59 : (x 2 6 && x 2 10).toNat = 0)
    (g60 : (x 1 7 && x 1 11).toNat = 0)
    (g61 : (x 0 8 && x 0 12).toNat = 0)
    (g62 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g63 : (x 4 8 && x 4 12).toNat = 0)
    (g64 : (x 3 9 && x 3 13).toNat = 0)
    (g65 : (x (-2) 1 && x (-2) 6).toNat = 0)
    (g66 : (x (-3) 2 && x (-3) 7).toNat = 0)
    (g67 : (x 0 1 && x 0 6).toNat = 0)
    (g68 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g69 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g70 : (x 1 1 && x 1 6).toNat = 0)
    (g71 : (x 0 2 && x 0 7).toNat = 0)
    (g72 : (x (-1) 3 && x (-1) 8).toNat = 0)
    (g73 : (x (-2) 4 && x (-2) 9).toNat = 0)
    (g74 : (x (-3) 5 && x (-3) 10).toNat = 0)
    (g75 : (x (-4) 6 && x (-4) 11).toNat = 0)
    (g76 : (x (-5) 7 && x (-5) 12).toNat = 0)
    (g77 : (x 3 8 && x 3 13).toNat = 0)
    (g78 : (x 2 9 && x 2 14).toNat = 0)
    (g79 : (x 1 1 && x 1 7).toNat = 0)
    (g80 : (x 0 2 && x 0 8).toNat = 0)
    (g81 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g82 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g83 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g84 : (x (-4) 6 && x (-4) 12).toNat = 0)
    (g85 : (x (-5) 7 && x (-5) 13).toNat = 0)
    (g86 : (x 4 2 && x 4 8).toNat = 0)
    (g87 : (x 3 3 && x 3 9).toNat = 0)
    (g88 : (x 2 4 && x 2 10).toNat = 0)
    (g89 : (x 1 5 && x 1 11).toNat = 0)
    (g90 : (x 0 6 && x 0 12).toNat = 0)
    (g91 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g92 : (x 3 4 && x 3 10).toNat = 0)
    (g93 : (x 2 5 && x 2 11).toNat = 0)
    (g94 : (x 1 6 && x 1 12).toNat = 0)
    (g95 : (x 0 7 && x 0 13).toNat = 0)
    (g96 : (x 0 1 && x 0 8).toNat = 0)
    (g97 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g98 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g99 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g100 : (x 1 1 && x 1 8).toNat = 0)
    (g101 : (x (-1) 3 && x (-1) 10).toNat = 0)
    (g102 : (x (-2) 4 && x (-2) 11).toNat = 0)
    (g103 : (x (-3) 5 && x (-3) 12).toNat = 0)
    (g104 : (x (-4) 6 && x (-4) 13).toNat = 0)
    (g105 : (x (-5) 7 && x (-5) 14).toNat = 0)
    (g106 : (x 3 5 && x 3 12).toNat = 0)
    (g107 : (x 2 6 && x 2 13).toNat = 0)
    (g108 : (x 1 7 && x 1 14).toNat = 0)
    (g109 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g110 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g111 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g112 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g113 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g114 : (x 2 3 && x 2 12).toNat = 0)
    (g115 : (x 1 4 && x 1 13).toNat = 0)
    (g116 : (x 0 5 && x 0 14).toNat = 0)
    (g117 : (x 3 4 && x 3 13).toNat = 0)
    (g118 : (x 2 5 && x 2 14).toNat = 0)
    (g119 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g120 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g121 : (x 3 2 && x 3 12).toNat = 0)
    (g122 : (x 2 3 && x 2 13).toNat = 0)
    (g123 : (x 1 4 && x 1 14).toNat = 0)
    (g124 : (x 2 4 && x 2 14).toNat = 0)
    (g125 : (x 3 4 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a11000100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125
