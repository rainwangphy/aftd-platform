import AFTD.Prelude

/-!
# cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b100

Topic: combinatorics   Node: 8683443f9de2

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_four_iff_five_core: under the layer-free tight-cover constraints for k = 15 and 131 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b100_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 5).toNat = 0)
    (g1 : (x (-3) 9).toNat = 0)
    (g2 : (x (-3) 13).toNat = 0)
    (g3 : (x (-2) 11).toNat = 0)
    (g4 : (x (-2) 14).toNat = 1)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 10).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x (-1) 13).toNat = 0)
    (g9 : (x 0 3).toNat = 1)
    (g10 : (x 0 6).toNat = 0)
    (g11 : (x 0 7).toNat = 0)
    (g12 : (x 0 8).toNat = 0)
    (g13 : (x 0 14).toNat = 1)
    (g14 : (x 1 2).toNat = 0)
    (g15 : (x 1 5).toNat = 0)
    (g16 : (x 1 9).toNat = 0)
    (g17 : (x 1 10).toNat = 0)
    (g18 : (x 1 11).toNat = 0)
    (g19 : (x 1 13).toNat = 0)
    (g20 : (x 2 1).toNat = 1)
    (g21 : (x 2 10).toNat = 0)
    (g22 : (x 2 11).toNat = 0)
    (g23 : (x 2 12).toNat = 0)
    (g24 : (x 3 2).toNat = 0)
    (g25 : (x 3 5).toNat = 0)
    (g26 : (x 3 6).toNat = 0)
    (g27 : (x 3 9).toNat = 0)
    (g28 : (x 3 10).toNat = 0)
    (g29 : (x 3 11).toNat = 0)
    (g30 : (x 4 8).toNat = 0)
    (g31 : (x 4 10).toNat = 1)
    (g32 : (x 5 5).toNat = 0)
    (g33 : (x 5 6).toNat = 0)
    (g34 : (x 5 9).toNat = 0)
    (g35 : (x 6 4).toNat = 0)
    (g36 : (x 6 5).toNat = 0)
    (g37 : (x 6 8).toNat = 0)
    (g38 : (x 7 4).toNat = 0)
    (g39 : (x 5 2 && x 5 6).toNat = 0)
    (g40 : (x 3 4 && x 3 8).toNat = 0)
    (g41 : (x 2 5 && x 2 9).toNat = 0)
    (g42 : (x 1 6 && x 1 10).toNat = 0)
    (g43 : (x 0 7 && x 0 11).toNat = 0)
    (g44 : (x 4 4 && x 4 8).toNat = 0)
    (g45 : (x 3 5 && x 3 9).toNat = 0)
    (g46 : (x 2 6 && x 2 10).toNat = 0)
    (g47 : (x 1 7 && x 1 11).toNat = 0)
    (g48 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g49 : (x 5 4 && x 5 8).toNat = 0)
    (g50 : (x 4 5 && x 4 9).toNat = 0)
    (g51 : (x 3 6 && x 3 10).toNat = 0)
    (g52 : (x 2 7 && x 2 11).toNat = 0)
    (g53 : (x 1 8 && x 1 12).toNat = 0)
    (g54 : (x 4 8 && x 4 12).toNat = 0)
    (g55 : (x 3 9 && x 3 13).toNat = 0)
    (g56 : (x 5 8 && x 5 12).toNat = 0)
    (g57 : (x 4 9 && x 4 13).toNat = 0)
    (g58 : (x 0 1 && x 0 6).toNat = 0)
    (g59 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g60 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g61 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g62 : (x 6 3 && x 6 8).toNat = 0)
    (g63 : (x 5 4 && x 5 9).toNat = 0)
    (g64 : (x 3 6 && x 3 11).toNat = 0)
    (g65 : (x 2 7 && x 2 12).toNat = 0)
    (g66 : (x 1 8 && x 1 13).toNat = 0)
    (g67 : (x (-1) 1 && x (-1) 7).toNat = 0)
    (g68 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g69 : (x 1 1 && x 1 7).toNat = 0)
    (g70 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g71 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g72 : (x 1 2 && x 1 8).toNat = 0)
    (g73 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g74 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g75 : (x 4 2 && x 4 8).toNat = 0)
    (g76 : (x 3 3 && x 3 9).toNat = 0)
    (g77 : (x 2 4 && x 2 10).toNat = 0)
    (g78 : (x 1 5 && x 1 11).toNat = 0)
    (g79 : (x 0 6 && x 0 12).toNat = 0)
    (g80 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g81 : (x 5 2 && x 5 8).toNat = 0)
    (g82 : (x 4 3 && x 4 9).toNat = 0)
    (g83 : (x 3 4 && x 3 10).toNat = 0)
    (g84 : (x 2 5 && x 2 11).toNat = 0)
    (g85 : (x 1 6 && x 1 12).toNat = 0)
    (g86 : (x 0 7 && x 0 13).toNat = 0)
    (g87 : (x 6 2 && x 6 8).toNat = 0)
    (g88 : (x 5 3 && x 5 9).toNat = 0)
    (g89 : (x 3 5 && x 3 11).toNat = 0)
    (g90 : (x 2 6 && x 2 12).toNat = 0)
    (g91 : (x 1 7 && x 1 13).toNat = 0)
    (g92 : (x 6 4 && x 6 10).toNat = 0)
    (g93 : (x 5 5 && x 5 11).toNat = 0)
    (g94 : (x 3 7 && x 3 13).toNat = 0)
    (g95 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g96 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g97 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g98 : (x 5 1 && x 5 8).toNat = 0)
    (g99 : (x 4 2 && x 4 9).toNat = 0)
    (g100 : (x 3 3 && x 3 10).toNat = 0)
    (g101 : (x 2 4 && x 2 11).toNat = 0)
    (g102 : (x 1 5 && x 1 12).toNat = 0)
    (g103 : (x 0 6 && x 0 13).toNat = 0)
    (g104 : (x (-1) 7 && x (-1) 14).toNat = 0)
    (g105 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g106 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g107 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g108 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g109 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g110 : (x 1 1 && x 1 10).toNat = 0)
    (g111 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g112 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g113 : (x 7 4 && x 7 13).toNat = 0)
    (g114 : (x 6 5 && x 6 14).toNat = 0)
    (g115 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g116 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g117 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g118 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g119 : (x 1 1 && x 1 11).toNat = 0)
    (g120 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g121 : (x 6 2 && x 6 12).toNat = 0)
    (g122 : (x 5 3 && x 5 13).toNat = 0)
    (g123 : (x 7 2 && x 7 12).toNat = 0)
    (g124 : (x 6 3 && x 6 13).toNat = 0)
    (g125 : (x 5 4 && x 5 14).toNat = 0)
    (g126 : (x 7 4 && x 7 14).toNat = 0)
    (g127 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g128 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g129 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g130 : (x (-3) 1 && x (-3) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d5995 : (x 0 1 && x 0 8).toNat = 0 := by
    have r5996 := hand2 (x 0 1) (x 0 8)
    have b5997 := hb (x 0 8)
    have b5998 := hb (x 0 1 && x 0 8)
    clear * - r5996 b5997 b5998 g12
    omega
  have d5999 : (x 0 8 && x 0 14).toNat = 0 := by
    have r6000 := hand1 (x 0 8) (x 0 14)
    have b6001 := hb (x 0 8)
    have b6002 := hb (x 0 8 && x 0 14)
    clear * - r6000 b6001 b6002 g12
    omega
  have d6003 : (x 0 2 && x 0 8).toNat = 0 := by
    have r6004 := hand2 (x 0 2) (x 0 8)
    have b6005 := hb (x 0 8)
    have b6006 := hb (x 0 2 && x 0 8)
    clear * - r6004 b6005 b6006 g12
    omega
  have d6007 : (x 0 8 && x 0 12).toNat = 0 := by
    have r6008 := hand1 (x 0 8) (x 0 12)
    have b6009 := hb (x 0 8)
    have b6010 := hb (x 0 8 && x 0 12)
    clear * - r6008 b6009 b6010 g12
    omega
  cases h6011 : x 0 9
  · have f6012 : (x 0 9).toNat = 0 := by rw [h6011]; rfl
    have d6013 : (x 0 3 && x 0 9).toNat = 0 := by
      have r6014 := hand2 (x 0 3) (x 0 9)
      have b6015 := hb (x 0 9)
      have b6016 := hb (x 0 3 && x 0 9)
      clear * - r6014 b6015 b6016 f6012
      omega
    have d6017 : (x 0 9 && x 0 14).toNat = 0 := by
      have r6018 := hand1 (x 0 9) (x 0 14)
      have b6019 := hb (x 0 9)
      have b6020 := hb (x 0 9 && x 0 14)
      clear * - r6018 b6019 b6020 f6012
      omega
    have d6021 : (x 0 9 && x 0 13).toNat = 0 := by
      have r6022 := hand1 (x 0 9) (x 0 13)
      have b6023 := hb (x 0 9)
      have b6024 := hb (x 0 9 && x 0 13)
      clear * - r6022 b6023 b6024 f6012
      omega
    cases h6025 : x 0 10
    · have f6026 : (x 0 10).toNat = 0 := by rw [h6025]; rfl
      cases h6027 : x 0 12
      · have f6028 : (x 0 12).toNat = 0 := by rw [h6027]; rfl
        have d6029 : (x 0 1 && x 0 12).toNat = 0 := by
          have r6030 := hand2 (x 0 1) (x 0 12)
          have b6031 := hb (x 0 12)
          have b6032 := hb (x 0 1 && x 0 12)
          clear * - r6030 b6031 b6032 f6028
          omega
        have d6033 : (x 0 2 && x 0 12).toNat = 0 := by
          have r6034 := hand2 (x 0 2) (x 0 12)
          have b6035 := hb (x 0 12)
          have b6036 := hb (x 0 2 && x 0 12)
          clear * - r6034 b6035 b6036 f6028
          omega
        have d6037 : (x (-3) 4).toNat = 1 := by
          have r6038 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6039 := hb (x (-3) 4)
          have b6040 := hb (x 1 11)
          have b6041 := hb (x 0 1 && x 0 12)
          have b6042 := hb (x (-1) 2 && x (-1) 13)
          have b6043 := hb (x (-2) 3 && x (-2) 14)
          clear * - r6038 b6039 b6040 b6041 b6042 b6043 g18 d6029 g128 g129
          omega
        have d6044 : (x (-3) 12).toNat = 1 := by
          have r6045 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b6046 := hb (x (-3) 4)
          have b6047 := hb (x (-3) 12)
          clear * - r6045 b6046 b6047 d6037
          omega
        have d6048 : (x (-4) 13).toNat = 0 := by
          have r6049 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6050 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e6051 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b6052 := hb (x (-6) 3)
          have b6053 := hb (x (-5) 2)
          have b6054 := hb (x (-4) 13)
          have b6055 := hb (x (-3) 12)
          clear * - r6049 e6050 e6051 b6052 b6053 b6054 b6055 d6044
          omega
        have d6056 : (x (-5) 2).toNat = 0 := by
          have r6057 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6058 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e6059 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b6060 := hb (x (-6) 3)
          have b6061 := hb (x (-5) 2)
          have b6062 := hb (x (-4) 13)
          have b6063 := hb (x (-3) 12)
          clear * - r6057 e6058 e6059 b6060 b6061 b6062 b6063 d6044 d6048
          omega
        have d6064 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
          have r6065 := hand1 (x (-5) 2) (x (-5) 13)
          have b6066 := hb (x (-5) 2)
          have b6067 := hb (x (-5) 2 && x (-5) 13)
          clear * - r6065 b6066 b6067 d6056
          omega
        have d6068 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
          have r6069 := hand1 (x (-5) 2) (x (-5) 12)
          have b6070 := hb (x (-5) 2)
          have b6071 := hb (x (-5) 2 && x (-5) 12)
          clear * - r6069 b6070 b6071 d6056
          omega
        have d6072 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
          have r6073 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6074 := hb (x (-5) 2)
          have b6075 := hb (x (-3) 13)
          have b6076 := hb (x (-4) 1 && x (-4) 14)
          clear * - r6073 b6074 b6075 b6076 g2 d6056
          omega
        have d6077 : (x (-4) 14).toNat = 1 := by
          have r6078 := hand2 (x (-4) 1) (x (-4) 14)
          have b6079 := hb (x (-4) 14)
          have b6080 := hb (x (-4) 1 && x (-4) 14)
          clear * - r6078 b6079 b6080 d6072
          omega
        have d6081 : (x (-5) 1).toNat = 0 := by
          have r6082 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6083 := hb (x (-5) 1)
          have b6084 := hb (x (-4) 14)
          clear * - r6082 b6083 b6084 d6077
          omega
        have d6085 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
          have r6086 := hand1 (x (-5) 1) (x (-5) 14)
          have b6087 := hb (x (-5) 1)
          have b6088 := hb (x (-5) 1 && x (-5) 14)
          clear * - r6086 b6087 b6088 d6081
          omega
        have d6089 : (x (-6) 2).toNat = 1 := by
          have r6090 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6091 := hb (x (-6) 2)
          have b6092 := hb (x (-4) 13)
          have b6093 := hb (x (-5) 1 && x (-5) 14)
          clear * - r6090 b6091 b6092 b6093 d6048 d6085
          omega
        have d6094 : (x (-6) 14).toNat = 1 := by
          have r6095 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
          have b6096 := hb (x (-6) 2)
          have b6097 := hb (x (-6) 14)
          clear * - r6095 b6096 b6097 d6089
          omega
        have d6098 : (x (-7) 1).toNat = 0 := by
          have r6099 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6100 := hb (x (-7) 1)
          have b6101 := hb (x (-6) 14)
          clear * - r6099 b6100 b6101 d6094
          omega
        have d6102 : (x (-7) 13).toNat = 0 := by
          have r6103 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
          have b6104 := hb (x (-7) 1)
          have b6105 := hb (x (-7) 13)
          clear * - r6103 b6104 b6105 d6098
          omega
        have d6106 : (x (-4) 12).toNat = 0 := by
          have r6107 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6108 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e6109 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b6110 := hb (x (-7) 3)
          have b6111 := hb (x (-6) 2)
          have b6112 := hb (x (-5) 13)
          have b6113 := hb (x (-4) 12)
          clear * - r6107 e6108 e6109 b6110 b6111 b6112 b6113 d6089
          omega
        have d6114 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
          have r6115 := hand2 (x (-4) 1) (x (-4) 12)
          have b6116 := hb (x (-4) 12)
          have b6117 := hb (x (-4) 1 && x (-4) 12)
          clear * - r6115 b6116 b6117 d6106
          omega
        have d6118 : (x (-4) 4).toNat = 0 := by
          have r6119 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have b6120 := hb (x (-4) 4)
          have b6121 := hb (x (-4) 12)
          clear * - r6119 b6120 b6121 d6106
          omega
        have d6122 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
          have r6123 := hand1 (x (-4) 4) (x (-4) 14)
          have b6124 := hb (x (-4) 4)
          have b6125 := hb (x (-4) 4 && x (-4) 14)
          clear * - r6123 b6124 b6125 d6118
          omega
        have d6126 : (x (-5) 13).toNat = 0 := by
          have r6127 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6128 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e6129 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b6130 := hb (x (-7) 3)
          have b6131 := hb (x (-6) 2)
          have b6132 := hb (x (-5) 13)
          have b6133 := hb (x (-4) 12)
          clear * - r6127 e6128 e6129 b6130 b6131 b6132 b6133 d6106 d6089
          omega
        have d6134 : (x (-5) 5).toNat = 0 := by
          have r6135 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
          have b6136 := hb (x (-5) 5)
          have b6137 := hb (x (-5) 13)
          clear * - r6135 b6136 b6137 d6126
          omega
        have d6138 : (x (-4) 1).toNat = 1 := by
          have r6139 := hand1 (x (-4) 1) (x (-4) 14)
          have b6140 := hb (x (-4) 1)
          have b6141 := hb (x (-4) 1 && x (-4) 14)
          clear * - r6139 b6140 b6141 d6072
          omega
        have d6142 : (x (-3) 14).toNat = 0 := by
          have r6143 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6144 := hb (x (-4) 1)
          have b6145 := hb (x (-3) 14)
          clear * - r6143 b6144 b6145 d6138
          omega
        have d6146 : (x (-3) 2).toNat = 0 := by
          have r6147 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
          have b6148 := hb (x (-3) 2)
          have b6149 := hb (x (-3) 14)
          clear * - r6147 b6148 b6149 d6142
          omega
        have d6150 : (x (-3) 10).toNat = 0 := by
          have r6151 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
          have b6152 := hb (x (-3) 2)
          have b6153 := hb (x (-3) 10)
          clear * - r6151 b6152 b6153 d6146
          omega
        have d6154 : (x (-6) 3).toNat = 0 := by
          have r6155 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6156 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e6157 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b6158 := hb (x (-6) 3)
          have b6159 := hb (x (-5) 2)
          have b6160 := hb (x (-4) 13)
          have b6161 := hb (x (-3) 12)
          clear * - r6155 e6156 e6157 b6158 b6159 b6160 b6161 d6044 d6048 d6056
          omega
        have d6162 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
          have r6163 := hand1 (x (-6) 3) (x (-6) 14)
          have b6164 := hb (x (-6) 3)
          have b6165 := hb (x (-6) 3 && x (-6) 14)
          clear * - r6163 b6164 b6165 d6154
          omega
        have d6166 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
          have r6167 := hand1 (x (-6) 3) (x (-6) 13)
          have b6168 := hb (x (-6) 3)
          have b6169 := hb (x (-6) 3 && x (-6) 13)
          clear * - r6167 b6168 b6169 d6154
          omega
        have d6170 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
          have r6171 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6172 := hb (x (-3) 5)
          have b6173 := hb (x 2 10)
          have b6174 := hb (x 1 1 && x 1 11)
          have b6175 := hb (x 0 2 && x 0 12)
          have b6176 := hb (x (-1) 3 && x (-1) 13)
          have b6177 := hb (x (-2) 4 && x (-2) 14)
          clear * - r6171 b6172 b6173 b6174 b6175 b6176 b6177 g21 g119 d6033 g120 g0
          omega
        have d6178 : (x (-2) 4).toNat = 1 := by
          have r6179 := hand1 (x (-2) 4) (x (-2) 14)
          have b6180 := hb (x (-2) 4)
          have b6181 := hb (x (-2) 4 && x (-2) 14)
          clear * - r6179 b6180 b6181 d6170
          omega
        have d6182 : (x (-2) 12).toNat = 1 := by
          have r6183 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
          have b6184 := hb (x (-2) 4)
          have b6185 := hb (x (-2) 12)
          clear * - r6183 b6184 b6185 d6178
          omega
        have d6186 : (x (-4) 2).toNat = 0 := by
          have r6187 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6188 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
          have e6189 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
          have b6190 := hb (x (-5) 3)
          have b6191 := hb (x (-4) 2)
          have b6192 := hb (x (-3) 13)
          have b6193 := hb (x (-2) 12)
          clear * - r6187 e6188 e6189 b6190 b6191 b6192 b6193 d6182 g2
          omega
        have d6194 : (x (-2) 13).toNat = 1 := by
          have r6195 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6196 := hb (x (-4) 2)
          have b6197 := hb (x (-2) 13)
          have b6198 := hb (x (-3) 1 && x (-3) 14)
          clear * - r6195 b6196 b6197 b6198 g130 d6186
          omega
        have d6199 : (x (-1) 12).toNat = 0 := by
          have r6200 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6201 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e6202 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b6203 := hb (x (-4) 3)
          have b6204 := hb (x (-3) 2)
          have b6205 := hb (x (-2) 13)
          have b6206 := hb (x (-1) 12)
          clear * - r6200 e6201 e6202 b6203 b6204 b6205 b6206 d6194 d6146
          omega
        have d6207 : (x (-4) 3).toNat = 0 := by
          have r6208 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6209 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e6210 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b6211 := hb (x (-4) 3)
          have b6212 := hb (x (-3) 2)
          have b6213 := hb (x (-2) 13)
          have b6214 := hb (x (-1) 12)
          clear * - r6208 e6209 e6210 b6211 b6212 b6213 b6214 d6199 d6194 d6146
          omega
        have d6215 : (x (-4) 11).toNat = 0 := by
          have r6216 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
          have b6217 := hb (x (-4) 3)
          have b6218 := hb (x (-4) 11)
          clear * - r6216 b6217 b6218 d6207
          omega
        have d6219 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
          have r6220 := hand2 (x (-4) 1) (x (-4) 11)
          have b6221 := hb (x (-4) 11)
          have b6222 := hb (x (-4) 1 && x (-4) 11)
          clear * - r6220 b6221 b6222 d6215
          omega
        have d6223 : (x (-2) 2 && x (-2) 12).toNat = 1 := by
          have r6224 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6225 := hb (x (-5) 5)
          have b6226 := hb (x 0 10)
          have b6227 := hb (x (-1) 1 && x (-1) 11)
          have b6228 := hb (x (-2) 2 && x (-2) 12)
          have b6229 := hb (x (-3) 3 && x (-3) 13)
          have b6230 := hb (x (-4) 4 && x (-4) 14)
          clear * - r6224 b6225 b6226 b6227 b6228 b6229 b6230 f6026 g117 g118 d6122 d6134
          omega
        have d6231 : (x (-2) 2).toNat = 1 := by
          have r6232 := hand1 (x (-2) 2) (x (-2) 12)
          have b6233 := hb (x (-2) 2)
          have b6234 := hb (x (-2) 2 && x (-2) 12)
          clear * - r6232 b6233 b6234 d6223
          omega
        have d6235 : (x (-3) 3).toNat = 0 := by
          have r6236 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6237 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e6238 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b6239 := hb (x (-3) 3)
          have b6240 := hb (x (-2) 2)
          have b6241 := hb (x (-1) 13)
          have b6242 := hb (x 0 12)
          clear * - r6236 e6237 e6238 b6239 b6240 b6241 b6242 f6028 g8 d6231
          omega
        have d6243 : (x (-3) 11).toNat = 0 := by
          have r6244 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
          have b6245 := hb (x (-3) 3)
          have b6246 := hb (x (-3) 11)
          clear * - r6244 b6245 b6246 d6235
          omega
        have d6247 : (x (-7) 4).toNat = 1 := by
          have r6248 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6249 := hb (x (-7) 4)
          have b6250 := hb (x (-3) 11)
          have b6251 := hb (x (-4) 1 && x (-4) 12)
          have b6252 := hb (x (-5) 2 && x (-5) 13)
          have b6253 := hb (x (-6) 3 && x (-6) 14)
          clear * - r6248 b6249 b6250 b6251 b6252 b6253 d6243 d6114 d6064 d6162
          omega
        have d6254 : (x (-7) 12).toNat = 1 := by
          have r6255 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
          have b6256 := hb (x (-7) 4)
          have b6257 := hb (x (-7) 12)
          clear * - r6255 b6256 b6257 d6247
          omega
        have d6258 : (x (-8) 13).toNat = 0 := by
          have r6259 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6260 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
          have e6261 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
          have b6262 := hb (x (-10) 3)
          have b6263 := hb (x (-9) 2)
          have b6264 := hb (x (-8) 13)
          have b6265 := hb (x (-7) 12)
          clear * - r6259 e6260 e6261 b6262 b6263 b6264 b6265 d6254
          omega
        have d6266 : (x (-8) 5).toNat = 0 := by
          have r6267 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
          have b6268 := hb (x (-8) 5)
          have b6269 := hb (x (-8) 13)
          clear * - r6267 b6268 b6269 d6258
          omega
        have d6270 : (x (-9) 2).toNat = 0 := by
          have r6271 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6272 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
          have e6273 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
          have b6274 := hb (x (-10) 3)
          have b6275 := hb (x (-9) 2)
          have b6276 := hb (x (-8) 13)
          have b6277 := hb (x (-7) 12)
          clear * - r6271 e6272 e6273 b6274 b6275 b6276 b6277 d6254 d6258
          omega
        have d6278 : (x (-8) 1 && x (-8) 14).toNat = 1 := by
          have r6279 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6280 := hb (x (-9) 2)
          have b6281 := hb (x (-7) 13)
          have b6282 := hb (x (-8) 1 && x (-8) 14)
          clear * - r6279 b6280 b6281 b6282 d6102 d6270
          omega
        have d6283 : (x (-8) 1).toNat = 1 := by
          have r6284 := hand1 (x (-8) 1) (x (-8) 14)
          have b6285 := hb (x (-8) 1)
          have b6286 := hb (x (-8) 1 && x (-8) 14)
          clear * - r6284 b6285 b6286 d6278
          omega
        have d6287 : (x (-7) 14).toNat = 0 := by
          have r6288 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b6289 := hb (x (-8) 1)
          have b6290 := hb (x (-7) 14)
          clear * - r6288 b6289 b6290 d6283
          omega
        have d6291 : (x (-7) 4 && x (-7) 14).toNat = 0 := by
          have r6292 := hand2 (x (-7) 4) (x (-7) 14)
          have b6293 := hb (x (-7) 14)
          have b6294 := hb (x (-7) 4 && x (-7) 14)
          clear * - r6292 b6293 b6294 d6287
          omega
        have r6295 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b6296 := hb (x (-8) 5)
        have b6297 := hb (x (-3) 10)
        have b6298 := hb (x (-4) 1 && x (-4) 11)
        have b6299 := hb (x (-5) 2 && x (-5) 12)
        have b6300 := hb (x (-6) 3 && x (-6) 13)
        have b6301 := hb (x (-7) 4 && x (-7) 14)
        linarith only [r6295, b6296, b6297, b6298, b6299, b6300, b6301, d6150, d6219, d6068, d6166, d6291, d6266]
      · have f6302 : (x 0 12).toNat = 1 := by rw [h6027]; rfl
        have d6303 : (x (-2) 2).toNat = 0 := by
          have r6304 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6305 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e6306 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b6307 := hb (x (-3) 3)
          have b6308 := hb (x (-2) 2)
          have b6309 := hb (x (-1) 13)
          have b6310 := hb (x 0 12)
          clear * - r6304 e6305 e6306 b6307 b6308 b6309 b6310 f6302 g8
          omega
        have d6311 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
          have r6312 := hand1 (x (-2) 2) (x (-2) 12)
          have b6313 := hb (x (-2) 2)
          have b6314 := hb (x (-2) 2 && x (-2) 12)
          clear * - r6312 b6313 b6314 d6303
          omega
        have d6315 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
          have r6316 := hand1 (x (-2) 2) (x (-2) 9)
          have b6317 := hb (x (-2) 2)
          have b6318 := hb (x (-2) 2 && x (-2) 9)
          clear * - r6316 b6317 b6318 d6303
          omega
        have d6319 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
          have r6320 := hand1 (x (-2) 2) (x (-2) 8)
          have b6321 := hb (x (-2) 2)
          have b6322 := hb (x (-2) 2 && x (-2) 8)
          clear * - r6320 b6321 b6322 d6303
          omega
        have d6323 : (x (-2) 10).toNat = 0 := by
          have r6324 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
          have b6325 := hb (x (-2) 2)
          have b6326 := hb (x (-2) 10)
          clear * - r6324 b6325 b6326 d6303
          omega
        have d6327 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
          have r6328 := hand2 (x (-2) 1) (x (-2) 10)
          have b6329 := hb (x (-2) 10)
          have b6330 := hb (x (-2) 1 && x (-2) 10)
          clear * - r6328 b6329 b6330 d6323
          omega
        have d6331 : (x (-3) 3).toNat = 0 := by
          have r6332 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e6333 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e6334 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b6335 := hb (x (-3) 3)
          have b6336 := hb (x (-2) 2)
          have b6337 := hb (x (-1) 13)
          have b6338 := hb (x 0 12)
          clear * - r6332 e6333 e6334 b6335 b6336 b6337 b6338 f6302 g8 d6303
          omega
        have d6339 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
          have r6340 := hand1 (x (-3) 3) (x (-3) 12)
          have b6341 := hb (x (-3) 3)
          have b6342 := hb (x (-3) 3 && x (-3) 12)
          clear * - r6340 b6341 b6342 d6331
          omega
        have d6343 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
          have r6344 := hand1 (x (-3) 3) (x (-3) 10)
          have b6345 := hb (x (-3) 3)
          have b6346 := hb (x (-3) 3 && x (-3) 10)
          clear * - r6344 b6345 b6346 d6331
          omega
        have d6347 : (x (-3) 11).toNat = 0 := by
          have r6348 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
          have b6349 := hb (x (-3) 3)
          have b6350 := hb (x (-3) 11)
          clear * - r6348 b6349 b6350 d6331
          omega
        have d6351 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
          have r6352 := hand2 (x (-3) 2) (x (-3) 11)
          have b6353 := hb (x (-3) 11)
          have b6354 := hb (x (-3) 2 && x (-3) 11)
          clear * - r6352 b6353 b6354 d6347
          omega
        cases h6355 : x (-1) 4
        · have f6356 : (x (-1) 4).toNat = 0 := by rw [h6355]; rfl
          cases h6357 : x (-1) 8
          · have f6358 : (x (-1) 8).toNat = 0 := by rw [h6357]; rfl
            cases h6359 : x 1 7
            · have f6360 : (x 1 7).toNat = 0 := by rw [h6359]; rfl
              have r6361 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6362 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6363 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6364 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
              have e6365 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
              have e6366 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
              have e6367 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
              have e6368 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
              have e6369 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
              have r6370 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6371 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e6372 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e6373 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e6374 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e6375 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e6376 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have r6377 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6378 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e6379 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e6380 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e6381 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e6382 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e6383 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have r6384 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6385 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e6386 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e6387 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e6388 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e6389 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e6390 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have r6391 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6392 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
              have e6393 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
              have e6394 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
              have e6395 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
              have e6396 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
              have e6397 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
              have r6398 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6399 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
              have e6400 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
              have e6401 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
              have e6402 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
              have e6403 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
              have e6404 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
              have r6405 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6406 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e6407 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have r6408 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6409 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
              have e6410 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
              have r6411 : 1 ≤ (x 13 4).toNat + (x 12 1 && x 12 5).toNat + (x 11 2 && x 11 6).toNat + (x 10 3 && x 10 7).toNat + (x 9 4 && x 9 8).toNat + (x 8 5 && x 8 9).toNat + (x 7 6 && x 7 10).toNat + (x 6 7 && x 6 11).toNat + (x 5 8 && x 5 12).toNat + (x 4 9 && x 4 13).toNat + (x 3 10 && x 3 14).toNat + (x 2 11).toNat := by have q := hcov4 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6412 : (x 12 1 && x 12 5).toNat = (x 12 5).toNat := handr _ _ (fun h => hp13 12 (hp5 12 (h)))
              have e6413 : (x 3 10 && x 3 14).toNat = (x 3 10).toNat := handl _ _ (fun h => hp2 3 (hp10 3 (h)))
              have r6414 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6415 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6416 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6417 : 1 ≤ (x 6 7).toNat + (x 5 1 && x 5 8).toNat + (x 4 2 && x 4 9).toNat + (x 3 3 && x 3 10).toNat + (x 2 4 && x 2 11).toNat + (x 1 5 && x 1 12).toNat + (x 0 6 && x 0 13).toNat + (x (-1) 7 && x (-1) 14).toNat + (x (-2) 8).toNat := by have q := hcov7 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6418 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6419 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6420 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6421 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6422 := hand2 (x 7 2) (x 7 6)
              have r6423 := hand1 (x 6 3) (x 6 7)
              have r6424 := hand2 (x 11 2) (x 11 6)
              have r6425 := hand2 (x 10 3) (x 10 7)
              have r6426 := hand2 (x 9 4) (x 9 8)
              have r6427 := hand2 (x 8 5) (x 8 9)
              have r6428 := hand2 (x 7 6) (x 7 10)
              have r6429 := hand2 (x 6 7) (x 6 11)
              have r6430 := hand2 (x 8 1) (x 8 6)
              have r6431 := hand1 (x 7 2) (x 7 7)
              have r6432 := hand1 (x 4 5) (x 4 10)
              have r6433 := hand2 (x (-4) 4) (x (-4) 10)
              have r6434 := hand2 (x (-5) 5) (x (-5) 11)
              have r6435 := hand1 (x (-6) 6) (x (-6) 12)
              have r6436 := hand1 (x (-7) 7) (x (-7) 13)
              have r6437 := hand1 (x (-8) 8) (x (-8) 14)
              have r6438 := hand2 (x 2 1) (x 2 7)
              have r6439 := hand1 (x (-3) 6) (x (-3) 12)
              have r6440 := hand1 (x (-4) 7) (x (-4) 13)
              have r6441 := hand1 (x (-5) 8) (x (-5) 14)
              have r6442 := hand1 (x (-4) 4) (x (-4) 14)
              have r6443 := hand2 (x 10 1) (x 10 11)
              have r6444 := hand2 (x 9 2) (x 9 12)
              have r6445 := hand2 (x 8 3) (x 8 13)
              have r6446 := hand2 (x (-9) 1) (x (-9) 12)
              have r6447 := hand2 (x (-10) 2) (x (-10) 13)
              have r6448 := hand2 (x (-11) 3) (x (-11) 14)
              have r6449 := hand1 (x 13 1) (x 13 12)
              have r6450 := hand1 (x 12 2) (x 12 13)
              have r6451 := hand1 (x 11 3) (x 11 14)
              linarith only [r6361, r6362, r6363, e6364, e6365, e6366, e6367, e6368, e6369, r6370, e6371, e6372, e6373, e6374, e6375, e6376, r6377, e6378, e6379, e6380, e6381, e6382, e6383, r6384, e6385, e6386, e6387, e6388, e6389, e6390, r6391, e6392, e6393, e6394, e6395, e6396, e6397, r6398, e6399, e6400, e6401, e6402, e6403, e6404, r6405, e6406, e6407, r6408, e6409, e6410, r6411, e6412, e6413, r6414, r6415, r6416, r6417, r6418, r6419, r6420, r6421, r6422, r6423, r6424, r6425, r6426, r6427, r6428, r6429, r6430, r6431, r6432, r6433, r6434, r6435, r6436, r6437, r6438, r6439, r6440, r6441, r6442, r6443, r6444, r6445, r6446, r6447, r6448, r6449, r6450, r6451, g1, d6347, d6323, g3, f6356, g5, g6, g9, g10, g12, f6026, g13, g14, g19, g20, g22, g23, g26, g28, g29, g31, g34, g36, g37, g49, g50, g51, g52, g53, d6021, g56, g57, g62, g63, g64, g65, g66, d6017, g67, d6319, g68, g72, d6013, g73, g74, g98, g99, g100, g101, g102, g103, g104, g117, d6311, g118, g126]
            · have f6601 : (x 1 7).toNat = 1 := by rw [h6359]; rfl
              have d6602 : (x 8 8).toNat = 0 := by
                have r6603 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e6604 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e6605 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e6606 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e6607 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e6608 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e6609 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b6610 := hb (x 1 7)
                have b6611 := hb (x 2 6)
                have b6612 := hb (x 3 5)
                have b6613 := hb (x 4 4)
                have b6614 := hb (x 5 11)
                have b6615 := hb (x 6 10)
                have b6616 := hb (x 7 9)
                have b6617 := hb (x 8 8)
                clear * - r6603 e6604 e6605 e6606 e6607 e6608 e6609 b6610 b6611 b6612 b6613 b6614 b6615 b6616 b6617 g25 f6601
                omega
              have d6618 : (x 8 4 && x 8 8).toNat = 0 := by
                have r6619 := hand2 (x 8 4) (x 8 8)
                have b6620 := hb (x 8 8)
                have b6621 := hb (x 8 4 && x 8 8)
                clear * - r6619 b6620 b6621 d6602
                omega
              have d6622 : (x 7 9).toNat = 0 := by
                have r6623 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e6624 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e6625 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e6626 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e6627 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e6628 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e6629 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b6630 := hb (x 1 7)
                have b6631 := hb (x 2 6)
                have b6632 := hb (x 3 5)
                have b6633 := hb (x 4 4)
                have b6634 := hb (x 5 11)
                have b6635 := hb (x 6 10)
                have b6636 := hb (x 7 9)
                have b6637 := hb (x 8 8)
                clear * - r6623 e6624 e6625 e6626 e6627 e6628 e6629 b6630 b6631 b6632 b6633 b6634 b6635 b6636 b6637 d6602 g25 f6601
                omega
              have d6638 : (x 7 5 && x 7 9).toNat = 0 := by
                have r6639 := hand2 (x 7 5) (x 7 9)
                have b6640 := hb (x 7 9)
                have b6641 := hb (x 7 5 && x 7 9)
                clear * - r6639 b6640 b6641 d6622
                omega
              have d6642 : (x 6 10).toNat = 0 := by
                have r6643 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e6644 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e6645 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e6646 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e6647 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e6648 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e6649 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b6650 := hb (x 1 7)
                have b6651 := hb (x 2 6)
                have b6652 := hb (x 3 5)
                have b6653 := hb (x 4 4)
                have b6654 := hb (x 5 11)
                have b6655 := hb (x 6 10)
                have b6656 := hb (x 7 9)
                have b6657 := hb (x 8 8)
                clear * - r6643 e6644 e6645 e6646 e6647 e6648 e6649 b6650 b6651 b6652 b6653 b6654 b6655 b6656 b6657 d6602 d6622 g25 f6601
                omega
              have d6658 : (x 6 6 && x 6 10).toNat = 0 := by
                have r6659 := hand2 (x 6 6) (x 6 10)
                have b6660 := hb (x 6 10)
                have b6661 := hb (x 6 6 && x 6 10)
                clear * - r6659 b6660 b6661 d6642
                omega
              have d6662 : (x 5 11).toNat = 0 := by
                have r6663 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e6664 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e6665 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e6666 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e6667 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e6668 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e6669 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b6670 := hb (x 1 7)
                have b6671 := hb (x 2 6)
                have b6672 := hb (x 3 5)
                have b6673 := hb (x 4 4)
                have b6674 := hb (x 5 11)
                have b6675 := hb (x 6 10)
                have b6676 := hb (x 7 9)
                have b6677 := hb (x 8 8)
                clear * - r6663 e6664 e6665 e6666 e6667 e6668 e6669 b6670 b6671 b6672 b6673 b6674 b6675 b6676 b6677 d6602 d6622 d6642 g25 f6601
                omega
              have d6678 : (x 5 7 && x 5 11).toNat = 0 := by
                have r6679 := hand2 (x 5 7) (x 5 11)
                have b6680 := hb (x 5 11)
                have b6681 := hb (x 5 7 && x 5 11)
                clear * - r6679 b6680 b6681 d6662
                omega
              have d6682 : (x 4 4).toNat = 0 := by
                have r6683 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e6684 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e6685 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e6686 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e6687 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e6688 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e6689 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b6690 := hb (x 1 7)
                have b6691 := hb (x 2 6)
                have b6692 := hb (x 3 5)
                have b6693 := hb (x 4 4)
                have b6694 := hb (x 5 11)
                have b6695 := hb (x 6 10)
                have b6696 := hb (x 7 9)
                have b6697 := hb (x 8 8)
                clear * - r6683 e6684 e6685 e6686 e6687 e6688 e6689 b6690 b6691 b6692 b6693 b6694 b6695 b6696 b6697 d6602 d6622 d6642 d6662 g25 f6601
                omega
              have d6698 : (x 4 4 && x 4 10).toNat = 0 := by
                have r6699 := hand1 (x 4 4) (x 4 10)
                have b6700 := hb (x 4 4)
                have b6701 := hb (x 4 4 && x 4 10)
                clear * - r6699 b6700 b6701 d6682
                omega
              have r6702 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6703 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6704 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
              have e6705 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
              have e6706 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
              have e6707 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
              have e6708 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
              have e6709 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
              have r6710 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := by have q := hcov4 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6711 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
              have e6712 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
              have r6713 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6714 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r6715 := hand2 (x 10 2) (x 10 6)
              have r6716 := hand2 (x 9 3) (x 9 7)
              have r6717 := hand2 (x 7 1) (x 7 7)
              have r6718 := hand1 (x 13 1) (x 13 11)
              have r6719 := hand1 (x 12 2) (x 12 12)
              have r6720 := hand1 (x 11 3) (x 11 13)
              have r6721 := hand1 (x 10 4) (x 10 14)
              linarith only [r6702, r6703, e6704, e6705, e6706, e6707, e6708, e6709, r6710, e6711, e6712, r6713, r6714, r6715, r6716, r6717, r6718, r6719, r6720, r6721, g5, g13, g18, g19, g21, g23, g29, g31, g34, g37, d6618, d6638, d6658, d6678, g54, g55, g87, g88, d6698, g89, g90, g91, d5999]
          · have f6767 : (x (-1) 8).toNat = 1 := by rw [h6357]; rfl
            have d6768 : (x (-2) 9).toNat = 0 := by
              have r6769 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6770 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e6771 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e6772 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e6773 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e6774 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e6775 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b6776 := hb (x (-8) 7)
              have b6777 := hb (x (-7) 6)
              have b6778 := hb (x (-6) 5)
              have b6779 := hb (x (-5) 4)
              have b6780 := hb (x (-4) 11)
              have b6781 := hb (x (-3) 10)
              have b6782 := hb (x (-2) 9)
              have b6783 := hb (x (-1) 8)
              clear * - r6769 e6770 e6771 e6772 e6773 e6774 e6775 b6776 b6777 b6778 b6779 b6780 b6781 b6782 b6783 f6767
              omega
            have d6784 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
              have r6785 := hand1 (x (-2) 9) (x (-2) 13)
              have b6786 := hb (x (-2) 9)
              have b6787 := hb (x (-2) 9 && x (-2) 13)
              clear * - r6785 b6786 b6787 d6768
              omega
            have d6788 : (x (-3) 10).toNat = 0 := by
              have r6789 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6790 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e6791 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e6792 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e6793 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e6794 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e6795 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b6796 := hb (x (-8) 7)
              have b6797 := hb (x (-7) 6)
              have b6798 := hb (x (-6) 5)
              have b6799 := hb (x (-5) 4)
              have b6800 := hb (x (-4) 11)
              have b6801 := hb (x (-3) 10)
              have b6802 := hb (x (-2) 9)
              have b6803 := hb (x (-1) 8)
              clear * - r6789 e6790 e6791 e6792 e6793 e6794 e6795 b6796 b6797 b6798 b6799 b6800 b6801 b6802 b6803 f6767 d6768
              omega
            have d6804 : (x (-4) 11).toNat = 0 := by
              have r6805 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6806 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e6807 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e6808 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e6809 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e6810 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e6811 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b6812 := hb (x (-8) 7)
              have b6813 := hb (x (-7) 6)
              have b6814 := hb (x (-6) 5)
              have b6815 := hb (x (-5) 4)
              have b6816 := hb (x (-4) 11)
              have b6817 := hb (x (-3) 10)
              have b6818 := hb (x (-2) 9)
              have b6819 := hb (x (-1) 8)
              clear * - r6805 e6806 e6807 e6808 e6809 e6810 e6811 b6812 b6813 b6814 b6815 b6816 b6817 b6818 b6819 f6767 d6768 d6788
              omega
            have d6820 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
              have r6821 := hand2 (x (-4) 4) (x (-4) 11)
              have b6822 := hb (x (-4) 11)
              have b6823 := hb (x (-4) 4 && x (-4) 11)
              clear * - r6821 b6822 b6823 d6804
              omega
            have d6824 : (x (-5) 4).toNat = 0 := by
              have r6825 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6826 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e6827 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e6828 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e6829 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e6830 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e6831 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b6832 := hb (x (-8) 7)
              have b6833 := hb (x (-7) 6)
              have b6834 := hb (x (-6) 5)
              have b6835 := hb (x (-5) 4)
              have b6836 := hb (x (-4) 11)
              have b6837 := hb (x (-3) 10)
              have b6838 := hb (x (-2) 9)
              have b6839 := hb (x (-1) 8)
              clear * - r6825 e6826 e6827 e6828 e6829 e6830 e6831 b6832 b6833 b6834 b6835 b6836 b6837 b6838 b6839 f6767 d6768 d6788 d6804
              omega
            have d6840 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
              have r6841 := hand1 (x (-5) 4) (x (-5) 14)
              have b6842 := hb (x (-5) 4)
              have b6843 := hb (x (-5) 4 && x (-5) 14)
              clear * - r6841 b6842 b6843 d6824
              omega
            have d6844 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
              have r6845 := hand1 (x (-5) 4) (x (-5) 13)
              have b6846 := hb (x (-5) 4)
              have b6847 := hb (x (-5) 4 && x (-5) 13)
              clear * - r6845 b6846 b6847 d6824
              omega
            have d6848 : (x (-6) 5).toNat = 0 := by
              have r6849 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6850 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e6851 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e6852 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e6853 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e6854 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e6855 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b6856 := hb (x (-8) 7)
              have b6857 := hb (x (-7) 6)
              have b6858 := hb (x (-6) 5)
              have b6859 := hb (x (-5) 4)
              have b6860 := hb (x (-4) 11)
              have b6861 := hb (x (-3) 10)
              have b6862 := hb (x (-2) 9)
              have b6863 := hb (x (-1) 8)
              clear * - r6849 e6850 e6851 e6852 e6853 e6854 e6855 b6856 b6857 b6858 b6859 b6860 b6861 b6862 b6863 f6767 d6768 d6788 d6804 d6824
              omega
            have d6864 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
              have r6865 := hand1 (x (-6) 5) (x (-6) 14)
              have b6866 := hb (x (-6) 5)
              have b6867 := hb (x (-6) 5 && x (-6) 14)
              clear * - r6865 b6866 b6867 d6848
              omega
            have d6868 : (x (-7) 6).toNat = 0 := by
              have r6869 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6870 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e6871 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e6872 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e6873 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e6874 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e6875 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b6876 := hb (x (-8) 7)
              have b6877 := hb (x (-7) 6)
              have b6878 := hb (x (-6) 5)
              have b6879 := hb (x (-5) 4)
              have b6880 := hb (x (-4) 11)
              have b6881 := hb (x (-3) 10)
              have b6882 := hb (x (-2) 9)
              have b6883 := hb (x (-1) 8)
              clear * - r6869 e6870 e6871 e6872 e6873 e6874 e6875 b6876 b6877 b6878 b6879 b6880 b6881 b6882 b6883 f6767 d6768 d6788 d6804 d6824 d6848
              omega
            have d6884 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
              have r6885 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b6886 := hb (x (-7) 6)
              have b6887 := hb (x (-1) 9)
              have b6888 := hb (x (-2) 1 && x (-2) 10)
              have b6889 := hb (x (-3) 2 && x (-3) 11)
              have b6890 := hb (x (-4) 3 && x (-4) 12)
              have b6891 := hb (x (-5) 4 && x (-5) 13)
              have b6892 := hb (x (-6) 5 && x (-6) 14)
              clear * - r6885 b6886 b6887 b6888 b6889 b6890 b6891 b6892 g5 d6327 d6351 d6844 d6864 d6868
              omega
            have d6893 : (x (-4) 12).toNat = 1 := by
              have r6894 := hand2 (x (-4) 3) (x (-4) 12)
              have b6895 := hb (x (-4) 12)
              have b6896 := hb (x (-4) 3 && x (-4) 12)
              clear * - r6894 b6895 b6896 d6884
              omega
            have d6897 : (x (-5) 13).toNat = 0 := by
              have r6898 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6899 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e6900 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b6901 := hb (x (-7) 3)
              have b6902 := hb (x (-6) 2)
              have b6903 := hb (x (-5) 13)
              have b6904 := hb (x (-4) 12)
              clear * - r6898 e6899 e6900 b6901 b6902 b6903 b6904 d6893
              omega
            have d6905 : (x (-5) 5).toNat = 0 := by
              have r6906 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
              have b6907 := hb (x (-5) 5)
              have b6908 := hb (x (-5) 13)
              clear * - r6906 b6907 b6908 d6897
              omega
            have d6909 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
              have r6910 := hand1 (x (-5) 5) (x (-5) 14)
              have b6911 := hb (x (-5) 5)
              have b6912 := hb (x (-5) 5 && x (-5) 14)
              clear * - r6910 b6911 b6912 d6905
              omega
            have d6913 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
              have r6914 := hand1 (x (-5) 5) (x (-5) 12)
              have b6915 := hb (x (-5) 5)
              have b6916 := hb (x (-5) 5 && x (-5) 12)
              clear * - r6914 b6915 b6916 d6905
              omega
            have d6917 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
              have r6918 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b6919 := hb (x (-5) 5)
              have b6920 := hb (x 0 10)
              have b6921 := hb (x (-1) 1 && x (-1) 11)
              have b6922 := hb (x (-2) 2 && x (-2) 12)
              have b6923 := hb (x (-3) 3 && x (-3) 13)
              have b6924 := hb (x (-4) 4 && x (-4) 14)
              clear * - r6918 b6919 b6920 b6921 b6922 b6923 b6924 f6026 g117 d6311 g118 d6905
              omega
            have d6925 : (x (-4) 14).toNat = 1 := by
              have r6926 := hand2 (x (-4) 4) (x (-4) 14)
              have b6927 := hb (x (-4) 14)
              have b6928 := hb (x (-4) 4 && x (-4) 14)
              clear * - r6926 b6927 b6928 d6917
              omega
            have d6929 : (x (-5) 1).toNat = 0 := by
              have r6930 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b6931 := hb (x (-5) 1)
              have b6932 := hb (x (-4) 14)
              clear * - r6930 b6931 b6932 d6925
              omega
            have d6933 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
              have r6934 := hand1 (x (-5) 1) (x (-5) 12)
              have b6935 := hb (x (-5) 1)
              have b6936 := hb (x (-5) 1 && x (-5) 12)
              clear * - r6934 b6935 b6936 d6929
              omega
            have d6937 : (x (-4) 4).toNat = 1 := by
              have r6938 := hand1 (x (-4) 4) (x (-4) 14)
              have b6939 := hb (x (-4) 4)
              have b6940 := hb (x (-4) 4 && x (-4) 14)
              clear * - r6938 b6939 b6940 d6917
              omega
            have d6941 : (x (-6) 6).toNat = 0 := by
              have r6942 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e6943 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e6944 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e6945 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e6946 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e6947 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e6948 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b6949 := hb (x (-7) 7)
              have b6950 := hb (x (-6) 6)
              have b6951 := hb (x (-5) 5)
              have b6952 := hb (x (-4) 4)
              have b6953 := hb (x (-3) 11)
              have b6954 := hb (x (-2) 10)
              have b6955 := hb (x (-1) 9)
              have b6956 := hb (x 0 8)
              clear * - r6942 e6943 e6944 e6945 e6946 e6947 e6948 b6949 b6950 b6951 b6952 b6953 b6954 b6955 b6956 g12 g5 d6323 d6347 d6937 d6905
              omega
            have d6957 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
              have r6958 := hand1 (x (-6) 6) (x (-6) 13)
              have b6959 := hb (x (-6) 6)
              have b6960 := hb (x (-6) 6 && x (-6) 13)
              clear * - r6958 b6959 b6960 d6941
              omega
            have d6961 : (x (-4) 4 && x (-4) 13).toNat = 1 := by
              have r6962 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b6963 := hb (x (-6) 6)
              have b6964 := hb (x 0 9)
              have b6965 := hb (x (-1) 1 && x (-1) 10)
              have b6966 := hb (x (-2) 2 && x (-2) 11)
              have b6967 := hb (x (-3) 3 && x (-3) 12)
              have b6968 := hb (x (-4) 4 && x (-4) 13)
              have b6969 := hb (x (-5) 5 && x (-5) 14)
              clear * - r6962 b6963 b6964 b6965 b6966 b6967 b6968 b6969 f6012 g105 g106 d6339 d6909 d6941
              omega
            have d6970 : (x (-4) 13).toNat = 1 := by
              have r6971 := hand2 (x (-4) 4) (x (-4) 13)
              have b6972 := hb (x (-4) 13)
              have b6973 := hb (x (-4) 4 && x (-4) 13)
              clear * - r6971 b6972 b6973 d6961
              omega
            have d6974 : (x (-4) 1).toNat = 1 := by
              have r6975 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
              have b6976 := hb (x (-4) 1)
              have b6977 := hb (x (-4) 13)
              clear * - r6975 b6976 b6977 d6970
              omega
            have d6978 : (x (-3) 14).toNat = 0 := by
              have r6979 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b6980 := hb (x (-4) 1)
              have b6981 := hb (x (-3) 14)
              clear * - r6979 b6980 b6981 d6974
              omega
            have d6982 : (x (-3) 6).toNat = 0 := by
              have r6983 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
              have b6984 := hb (x (-3) 6)
              have b6985 := hb (x (-3) 14)
              clear * - r6983 b6984 b6985 d6978
              omega
            have d6986 : (x (-3) 6 && x (-3) 12).toNat = 0 := by
              have r6987 := hand1 (x (-3) 6) (x (-3) 12)
              have b6988 := hb (x (-3) 6)
              have b6989 := hb (x (-3) 6 && x (-3) 12)
              clear * - r6987 b6988 b6989 d6982
              omega
            have d6990 : (x (-3) 2).toNat = 0 := by
              have r6991 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
              have b6992 := hb (x (-3) 2)
              have b6993 := hb (x (-3) 14)
              clear * - r6991 b6992 b6993 d6978
              omega
            have d6994 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
              have r6995 := hand1 (x (-3) 2) (x (-3) 12)
              have b6996 := hb (x (-3) 2)
              have b6997 := hb (x (-3) 2 && x (-3) 12)
              clear * - r6995 b6996 b6997 d6990
              omega
            have d6998 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
              have r6999 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b7000 := hb (x (-6) 5)
              have b7001 := hb (x (-1) 10)
              have b7002 := hb (x (-2) 1 && x (-2) 11)
              have b7003 := hb (x (-3) 2 && x (-3) 12)
              have b7004 := hb (x (-4) 3 && x (-4) 13)
              have b7005 := hb (x (-5) 4 && x (-5) 14)
              clear * - r6999 b7000 b7001 b7002 b7003 b7004 b7005 g6 g116 d6994 d6840 d6848
              omega
            have d7006 : (x (-4) 3).toNat = 1 := by
              have r7007 := hand1 (x (-4) 3) (x (-4) 13)
              have b7008 := hb (x (-4) 3)
              have b7009 := hb (x (-4) 3 && x (-4) 13)
              clear * - r7007 b7008 b7009 d6998
              omega
            have d7010 : (x (-1) 12).toNat = 0 := by
              have r7011 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7012 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e7013 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b7014 := hb (x (-4) 3)
              have b7015 := hb (x (-3) 2)
              have b7016 := hb (x (-2) 13)
              have b7017 := hb (x (-1) 12)
              clear * - r7011 e7012 e7013 b7014 b7015 b7016 b7017 d6990 d7006
              omega
            have d7018 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
              have r7019 := hand2 (x (-1) 8) (x (-1) 12)
              have b7020 := hb (x (-1) 12)
              have b7021 := hb (x (-1) 8 && x (-1) 12)
              clear * - r7019 b7020 b7021 d7010
              omega
            have d7022 : (x (-2) 13).toNat = 0 := by
              have r7023 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7024 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e7025 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b7026 := hb (x (-4) 3)
              have b7027 := hb (x (-3) 2)
              have b7028 := hb (x (-2) 13)
              have b7029 := hb (x (-1) 12)
              clear * - r7023 e7024 e7025 b7026 b7027 b7028 b7029 d7010 d6990 d7006
              omega
            have d7030 : (x (-2) 5).toNat = 0 := by
              have r7031 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
              have b7032 := hb (x (-2) 5)
              have b7033 := hb (x (-2) 13)
              clear * - r7031 b7032 b7033 d7022
              omega
            have d7034 : (x (-7) 7).toNat = 0 := by
              have r7035 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7036 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e7037 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e7038 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e7039 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e7040 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e7041 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b7042 := hb (x (-7) 7)
              have b7043 := hb (x (-6) 6)
              have b7044 := hb (x (-5) 5)
              have b7045 := hb (x (-4) 4)
              have b7046 := hb (x (-3) 11)
              have b7047 := hb (x (-2) 10)
              have b7048 := hb (x (-1) 9)
              have b7049 := hb (x 0 8)
              clear * - r7035 e7036 e7037 e7038 e7039 e7040 e7041 b7042 b7043 b7044 b7045 b7046 b7047 b7048 b7049 g12 g5 d6323 d6347 d6937 d6905 d6941
              omega
            have d7050 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
              have r7051 := hand1 (x (-7) 7) (x (-7) 14)
              have b7052 := hb (x (-7) 7)
              have b7053 := hb (x (-7) 7 && x (-7) 14)
              clear * - r7051 b7052 b7053 d7034
              omega
            have d7054 : (x (-6) 2).toNat = 0 := by
              have r7055 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7056 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e7057 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b7058 := hb (x (-7) 3)
              have b7059 := hb (x (-6) 2)
              have b7060 := hb (x (-5) 13)
              have b7061 := hb (x (-4) 12)
              clear * - r7055 e7056 e7057 b7058 b7059 b7060 b7061 d6893 d6897
              omega
            have d7062 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
              have r7063 := hand1 (x (-6) 2) (x (-6) 13)
              have b7064 := hb (x (-6) 2)
              have b7065 := hb (x (-6) 2 && x (-6) 13)
              clear * - r7063 b7064 b7065 d7054
              omega
            have d7066 : (x (-7) 3).toNat = 0 := by
              have r7067 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7068 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e7069 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b7070 := hb (x (-7) 3)
              have b7071 := hb (x (-6) 2)
              have b7072 := hb (x (-5) 13)
              have b7073 := hb (x (-4) 12)
              clear * - r7067 e7068 e7069 b7070 b7071 b7072 b7073 d6893 d6897 d7054
              omega
            have d7074 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
              have r7075 := hand1 (x (-7) 3) (x (-7) 14)
              have b7076 := hb (x (-7) 3)
              have b7077 := hb (x (-7) 3 && x (-7) 14)
              clear * - r7075 b7076 b7077 d7066
              omega
            have d7078 : (x (-8) 4).toNat = 1 := by
              have r7079 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b7080 := hb (x (-8) 4)
              have b7081 := hb (x (-4) 11)
              have b7082 := hb (x (-5) 1 && x (-5) 12)
              have b7083 := hb (x (-6) 2 && x (-6) 13)
              have b7084 := hb (x (-7) 3 && x (-7) 14)
              clear * - r7079 b7080 b7081 b7082 b7083 b7084 d6804 d6933 d7062 d7074
              omega
            have d7085 : (x (-8) 12).toNat = 1 := by
              have r7086 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
              have b7087 := hb (x (-8) 4)
              have b7088 := hb (x (-8) 12)
              clear * - r7086 b7087 b7088 d7078
              omega
            have d7089 : (x (-9) 13).toNat = 0 := by
              have r7090 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7091 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e7092 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b7093 := hb (x (-11) 3)
              have b7094 := hb (x (-10) 2)
              have b7095 := hb (x (-9) 13)
              have b7096 := hb (x (-8) 12)
              clear * - r7090 e7091 e7092 b7093 b7094 b7095 b7096 d7085
              omega
            have d7097 : (x (-10) 2).toNat = 0 := by
              have r7098 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7099 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e7100 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b7101 := hb (x (-11) 3)
              have b7102 := hb (x (-10) 2)
              have b7103 := hb (x (-9) 13)
              have b7104 := hb (x (-8) 12)
              clear * - r7098 e7099 e7100 b7101 b7102 b7103 b7104 d7085 d7089
              omega
            have d7105 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
              have r7106 := hand1 (x (-10) 2) (x (-10) 13)
              have b7107 := hb (x (-10) 2)
              have b7108 := hb (x (-10) 2 && x (-10) 13)
              clear * - r7106 b7107 b7108 d7097
              omega
            have d7109 : (x (-10) 10).toNat = 0 := by
              have r7110 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
              have b7111 := hb (x (-10) 2)
              have b7112 := hb (x (-10) 10)
              clear * - r7110 b7111 b7112 d7097
              omega
            have d7113 : (x (-11) 3).toNat = 0 := by
              have r7114 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7115 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e7116 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b7117 := hb (x (-11) 3)
              have b7118 := hb (x (-10) 2)
              have b7119 := hb (x (-9) 13)
              have b7120 := hb (x (-8) 12)
              clear * - r7114 e7115 e7116 b7117 b7118 b7119 b7120 d7085 d7089 d7097
              omega
            have d7121 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
              have r7122 := hand1 (x (-11) 3) (x (-11) 14)
              have b7123 := hb (x (-11) 3)
              have b7124 := hb (x (-11) 3 && x (-11) 14)
              clear * - r7122 b7123 b7124 d7113
              omega
            have d7125 : (x (-11) 11).toNat = 0 := by
              have r7126 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
              have b7127 := hb (x (-11) 3)
              have b7128 := hb (x (-11) 11)
              clear * - r7126 b7127 b7128 d7113
              omega
            have d7129 : (x (-8) 8).toNat = 1 := by
              have r7130 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b7131 := hb (x (-8) 8)
              have b7132 := hb (x 0 7)
              have b7133 := hb (x (-1) 1 && x (-1) 8)
              have b7134 := hb (x (-2) 2 && x (-2) 9)
              have b7135 := hb (x (-3) 3 && x (-3) 10)
              have b7136 := hb (x (-4) 4 && x (-4) 11)
              have b7137 := hb (x (-5) 5 && x (-5) 12)
              have b7138 := hb (x (-6) 6 && x (-6) 13)
              have b7139 := hb (x (-7) 7 && x (-7) 14)
              clear * - r7130 b7131 b7132 b7133 b7134 b7135 b7136 b7137 b7138 b7139 g11 g95 d6315 d6343 d6820 d6913 d6957 d7050
              omega
            have d7140 : (x (-9) 9).toNat = 0 := by
              have r7141 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7142 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
              have e7143 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
              have e7144 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
              have e7145 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
              have e7146 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
              have e7147 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
              have b7148 := hb (x (-15) 7)
              have b7149 := hb (x (-14) 6)
              have b7150 := hb (x (-13) 5)
              have b7151 := hb (x (-12) 4)
              have b7152 := hb (x (-11) 11)
              have b7153 := hb (x (-10) 10)
              have b7154 := hb (x (-9) 9)
              have b7155 := hb (x (-8) 8)
              clear * - r7141 e7142 e7143 e7144 e7145 e7146 e7147 b7148 b7149 b7150 b7151 b7152 b7153 b7154 b7155 d7129 d7109 d7125
              omega
            have d7156 : (x (-12) 4).toNat = 0 := by
              have r7157 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7158 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
              have e7159 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
              have e7160 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
              have e7161 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
              have e7162 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
              have e7163 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
              have b7164 := hb (x (-15) 7)
              have b7165 := hb (x (-14) 6)
              have b7166 := hb (x (-13) 5)
              have b7167 := hb (x (-12) 4)
              have b7168 := hb (x (-11) 11)
              have b7169 := hb (x (-10) 10)
              have b7170 := hb (x (-9) 9)
              have b7171 := hb (x (-8) 8)
              clear * - r7157 e7158 e7159 e7160 e7161 e7162 e7163 b7164 b7165 b7166 b7167 b7168 b7169 b7170 b7171 d7129 d7140 d7109 d7125
              omega
            have d7172 : (x 4 3 && x 4 7).toNat = 1 := by
              have r7173 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7174 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
              have e7175 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
              have b7176 := hb (x (-4) 11)
              have b7177 := hb (x (-3) 10)
              have b7178 := hb (x 6 5)
              have b7179 := hb (x 7 4)
              have b7180 := hb (x 5 2 && x 5 6)
              have b7181 := hb (x 4 3 && x 4 7)
              have b7182 := hb (x 3 4 && x 3 8)
              have b7183 := hb (x 2 5 && x 2 9)
              have b7184 := hb (x 1 6 && x 1 10)
              have b7185 := hb (x 0 7 && x 0 11)
              have b7186 := hb (x (-1) 8 && x (-1) 12)
              have b7187 := hb (x (-2) 9 && x (-2) 13)
              clear * - r7173 e7174 e7175 b7176 b7177 b7178 b7179 b7180 b7181 b7182 b7183 b7184 b7185 b7186 b7187 g38 g36 g39 g40 g41 g42 g43 d7018 d6784 d6788 d6804
              omega
            have d7188 : (x 4 7).toNat = 1 := by
              have r7189 := hand2 (x 4 3) (x 4 7)
              have b7190 := hb (x 4 7)
              have b7191 := hb (x 4 3 && x 4 7)
              clear * - r7189 b7190 b7191 d7172
              omega
            have d7192 : (x 11 8).toNat = 0 := by
              have r7193 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7194 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e7195 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e7196 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e7197 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e7198 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e7199 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b7200 := hb (x 4 7)
              have b7201 := hb (x 5 6)
              have b7202 := hb (x 6 5)
              have b7203 := hb (x 7 4)
              have b7204 := hb (x 8 11)
              have b7205 := hb (x 9 10)
              have b7206 := hb (x 10 9)
              have b7207 := hb (x 11 8)
              clear * - r7193 e7194 e7195 e7196 e7197 e7198 e7199 b7200 b7201 b7202 b7203 b7204 b7205 b7206 b7207 g38 g36 g33 d7188
              omega
            have d7208 : (x 10 9).toNat = 0 := by
              have r7209 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7210 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e7211 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e7212 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e7213 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e7214 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e7215 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b7216 := hb (x 4 7)
              have b7217 := hb (x 5 6)
              have b7218 := hb (x 6 5)
              have b7219 := hb (x 7 4)
              have b7220 := hb (x 8 11)
              have b7221 := hb (x 9 10)
              have b7222 := hb (x 10 9)
              have b7223 := hb (x 11 8)
              clear * - r7209 e7210 e7211 e7212 e7213 e7214 e7215 b7216 b7217 b7218 b7219 b7220 b7221 b7222 b7223 d7192 g38 g36 g33 d7188
              omega
            have d7224 : (x 9 10).toNat = 0 := by
              have r7225 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7226 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e7227 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e7228 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e7229 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e7230 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e7231 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b7232 := hb (x 4 7)
              have b7233 := hb (x 5 6)
              have b7234 := hb (x 6 5)
              have b7235 := hb (x 7 4)
              have b7236 := hb (x 8 11)
              have b7237 := hb (x 9 10)
              have b7238 := hb (x 10 9)
              have b7239 := hb (x 11 8)
              clear * - r7225 e7226 e7227 e7228 e7229 e7230 e7231 b7232 b7233 b7234 b7235 b7236 b7237 b7238 b7239 d7192 d7208 g38 g36 g33 d7188
              omega
            have d7240 : (x 8 11).toNat = 0 := by
              have r7241 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7242 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
              have e7243 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
              have e7244 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
              have e7245 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
              have e7246 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
              have e7247 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
              have b7248 := hb (x 4 7)
              have b7249 := hb (x 5 6)
              have b7250 := hb (x 6 5)
              have b7251 := hb (x 7 4)
              have b7252 := hb (x 8 11)
              have b7253 := hb (x 9 10)
              have b7254 := hb (x 10 9)
              have b7255 := hb (x 11 8)
              clear * - r7241 e7242 e7243 e7244 e7245 e7246 e7247 b7248 b7249 b7250 b7251 b7252 b7253 b7254 b7255 d7192 d7208 d7224 g38 g36 g33 d7188
              omega
            have d7256 : (x 8 1 && x 8 11).toNat = 0 := by
              have r7257 := hand2 (x 8 1) (x 8 11)
              have b7258 := hb (x 8 11)
              have b7259 := hb (x 8 1 && x 8 11)
              clear * - r7257 b7258 b7259 d7240
              omega
            have d7260 : (x 4 5).toNat = 1 := by
              have r7261 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b7262 := hb (x 4 5)
              have b7263 := hb (x 9 10)
              have b7264 := hb (x 8 1 && x 8 11)
              have b7265 := hb (x 7 2 && x 7 12)
              have b7266 := hb (x 6 3 && x 6 13)
              have b7267 := hb (x 5 4 && x 5 14)
              clear * - r7261 b7262 b7263 b7264 b7265 b7266 b7267 d7224 d7256 g123 g124 g125
              omega
            have d7268 : (x 4 13).toNat = 1 := by
              have r7269 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
              have b7270 := hb (x 4 5)
              have b7271 := hb (x 4 13)
              clear * - r7269 b7270 b7271 d7260
              omega
            have d7272 : (x 5 12).toNat = 0 := by
              have r7273 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7274 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e7275 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b7276 := hb (x 2 3)
              have b7277 := hb (x 3 2)
              have b7278 := hb (x 4 13)
              have b7279 := hb (x 5 12)
              clear * - r7273 e7274 e7275 b7276 b7277 b7278 b7279 d7268 g24
              omega
            have d7280 : (x 5 4).toNat = 0 := by
              have r7281 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
              have b7282 := hb (x 5 4)
              have b7283 := hb (x 5 12)
              clear * - r7281 b7282 b7283 d7272
              omega
            have d7284 : (x 9 8).toNat = 0 := by
              have r7285 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7286 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e7287 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e7288 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e7289 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e7290 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e7291 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b7292 := hb (x 2 7)
              have b7293 := hb (x 3 6)
              have b7294 := hb (x 4 5)
              have b7295 := hb (x 5 4)
              have b7296 := hb (x 6 11)
              have b7297 := hb (x 7 10)
              have b7298 := hb (x 8 9)
              have b7299 := hb (x 9 8)
              clear * - r7285 e7286 e7287 e7288 e7289 e7290 e7291 b7292 b7293 b7294 b7295 b7296 b7297 b7298 b7299 d7280 d7260 g26
              omega
            have d7300 : (x 8 9).toNat = 0 := by
              have r7301 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7302 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e7303 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e7304 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e7305 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e7306 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e7307 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b7308 := hb (x 2 7)
              have b7309 := hb (x 3 6)
              have b7310 := hb (x 4 5)
              have b7311 := hb (x 5 4)
              have b7312 := hb (x 6 11)
              have b7313 := hb (x 7 10)
              have b7314 := hb (x 8 9)
              have b7315 := hb (x 9 8)
              clear * - r7301 e7302 e7303 e7304 e7305 e7306 e7307 b7308 b7309 b7310 b7311 b7312 b7313 b7314 b7315 d7284 d7280 d7260 g26
              omega
            have d7316 : (x 7 10).toNat = 0 := by
              have r7317 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7318 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e7319 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e7320 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e7321 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e7322 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e7323 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b7324 := hb (x 2 7)
              have b7325 := hb (x 3 6)
              have b7326 := hb (x 4 5)
              have b7327 := hb (x 5 4)
              have b7328 := hb (x 6 11)
              have b7329 := hb (x 7 10)
              have b7330 := hb (x 8 9)
              have b7331 := hb (x 9 8)
              clear * - r7317 e7318 e7319 e7320 e7321 e7322 e7323 b7324 b7325 b7326 b7327 b7328 b7329 b7330 b7331 d7284 d7300 d7280 d7260 g26
              omega
            have d7332 : (x 6 11).toNat = 0 := by
              have r7333 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7334 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e7335 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e7336 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e7337 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e7338 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e7339 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b7340 := hb (x 2 7)
              have b7341 := hb (x 3 6)
              have b7342 := hb (x 4 5)
              have b7343 := hb (x 5 4)
              have b7344 := hb (x 6 11)
              have b7345 := hb (x 7 10)
              have b7346 := hb (x 8 9)
              have b7347 := hb (x 9 8)
              clear * - r7333 e7334 e7335 e7336 e7337 e7338 e7339 b7340 b7341 b7342 b7343 b7344 b7345 b7346 b7347 d7284 d7300 d7316 d7280 d7260 g26
              omega
            have d7348 : (x 2 7).toNat = 0 := by
              have r7349 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e7350 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
              have e7351 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
              have e7352 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
              have e7353 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
              have e7354 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
              have e7355 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
              have b7356 := hb (x 2 7)
              have b7357 := hb (x 3 6)
              have b7358 := hb (x 4 5)
              have b7359 := hb (x 5 4)
              have b7360 := hb (x 6 11)
              have b7361 := hb (x 7 10)
              have b7362 := hb (x 8 9)
              have b7363 := hb (x 9 8)
              clear * - r7349 e7350 e7351 e7352 e7353 e7354 e7355 b7356 b7357 b7358 b7359 b7360 b7361 b7362 b7363 d7284 d7300 d7316 d7332 d7280 d7260 g26
              omega
            have d7364 : (x 2 1 && x 2 7).toNat = 0 := by
              have r7365 := hand2 (x 2 1) (x 2 7)
              have b7366 := hb (x 2 7)
              have b7367 := hb (x 2 1 && x 2 7)
              clear * - r7365 b7366 b7367 d7348
              omega
            have r7368 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r7369 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r7370 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r7371 := hand1 (x (-4) 7) (x (-4) 13)
            have r7372 := hand1 (x (-5) 8) (x (-5) 14)
            have r7373 := hand2 (x (-9) 1) (x (-9) 12)
            linarith only [r7368, r7369, r7370, r7371, r7372, r7373, d7156, d6982, d7030, f6356, g9, g14, g20, g26, d7364, g72, d6013, g73, g74, d6986, d7105, d7121]
        · have f7401 : (x (-1) 4).toNat = 1 := by rw [h6355]; rfl
          have d7402 : (x (-1) 12).toNat = 1 := by
            have r7403 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b7404 := hb (x (-1) 4)
            have b7405 := hb (x (-1) 12)
            clear * - r7403 b7404 b7405 f7401
            omega
          have d7406 : (x (-2) 13).toNat = 0 := by
            have r7407 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e7408 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e7409 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b7410 := hb (x (-4) 3)
            have b7411 := hb (x (-3) 2)
            have b7412 := hb (x (-2) 13)
            have b7413 := hb (x (-1) 12)
            clear * - r7407 e7408 e7409 b7410 b7411 b7412 b7413 d7402
            omega
          have d7414 : (x (-4) 2).toNat = 1 := by
            have r7415 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b7416 := hb (x (-4) 2)
            have b7417 := hb (x (-2) 13)
            have b7418 := hb (x (-3) 1 && x (-3) 14)
            clear * - r7415 b7416 b7417 b7418 d7406 g130
            omega
          have d7419 : (x (-4) 14).toNat = 1 := by
            have r7420 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
            have b7421 := hb (x (-4) 2)
            have b7422 := hb (x (-4) 14)
            clear * - r7420 b7421 b7422 d7414
            omega
          have d7423 : (x (-5) 1).toNat = 0 := by
            have r7424 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b7425 := hb (x (-5) 1)
            have b7426 := hb (x (-4) 14)
            clear * - r7424 b7425 b7426 d7419
            omega
          have d7427 : (x (-5) 13).toNat = 0 := by
            have r7428 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
            have b7429 := hb (x (-5) 1)
            have b7430 := hb (x (-5) 13)
            clear * - r7428 b7429 b7430 d7423
            omega
          have d7431 : (x (-3) 2).toNat = 0 := by
            have r7432 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e7433 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e7434 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b7435 := hb (x (-4) 3)
            have b7436 := hb (x (-3) 2)
            have b7437 := hb (x (-2) 13)
            have b7438 := hb (x (-1) 12)
            clear * - r7432 e7433 e7434 b7435 b7436 b7437 b7438 d7402 d7406
            omega
          have d7439 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
            have r7440 := hand1 (x (-3) 2) (x (-3) 12)
            have b7441 := hb (x (-3) 2)
            have b7442 := hb (x (-3) 2 && x (-3) 12)
            clear * - r7440 b7441 b7442 d7431
            omega
          have d7443 : (x (-4) 3).toNat = 0 := by
            have r7444 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e7445 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e7446 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b7447 := hb (x (-4) 3)
            have b7448 := hb (x (-3) 2)
            have b7449 := hb (x (-2) 13)
            have b7450 := hb (x (-1) 12)
            clear * - r7444 e7445 e7446 b7447 b7448 b7449 b7450 d7402 d7406 d7431
            omega
          have d7451 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
            have r7452 := hand1 (x (-4) 3) (x (-4) 14)
            have b7453 := hb (x (-4) 3)
            have b7454 := hb (x (-4) 3 && x (-4) 14)
            clear * - r7452 b7453 b7454 d7443
            omega
          have d7455 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
            have r7456 := hand1 (x (-4) 3) (x (-4) 13)
            have b7457 := hb (x (-4) 3)
            have b7458 := hb (x (-4) 3 && x (-4) 13)
            clear * - r7456 b7457 b7458 d7443
            omega
          have d7459 : (x (-2) 12).toNat = 0 := by
            have r7460 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e7461 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e7462 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have b7463 := hb (x (-5) 3)
            have b7464 := hb (x (-4) 2)
            have b7465 := hb (x (-3) 13)
            have b7466 := hb (x (-2) 12)
            clear * - r7460 e7461 e7462 b7463 b7464 b7465 b7466 g2 d7414
            omega
          have d7467 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
            have r7468 := hand2 (x (-2) 1) (x (-2) 12)
            have b7469 := hb (x (-2) 12)
            have b7470 := hb (x (-2) 1 && x (-2) 12)
            clear * - r7468 b7469 b7470 d7459
            omega
          have d7471 : (x (-5) 4).toNat = 1 := by
            have r7472 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b7473 := hb (x (-5) 4)
            have b7474 := hb (x (-1) 11)
            have b7475 := hb (x (-2) 1 && x (-2) 12)
            have b7476 := hb (x (-3) 2 && x (-3) 13)
            have b7477 := hb (x (-4) 3 && x (-4) 14)
            clear * - r7472 b7473 b7474 b7475 b7476 b7477 g7 d7467 g127 d7451
            omega
          have d7478 : (x (-5) 12).toNat = 1 := by
            have r7479 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
            have b7480 := hb (x (-5) 4)
            have b7481 := hb (x (-5) 12)
            clear * - r7479 b7480 b7481 d7471
            omega
          have d7482 : (x (-6) 13).toNat = 0 := by
            have r7483 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e7484 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e7485 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b7486 := hb (x (-8) 3)
            have b7487 := hb (x (-7) 2)
            have b7488 := hb (x (-6) 13)
            have b7489 := hb (x (-5) 12)
            clear * - r7483 e7484 e7485 b7486 b7487 b7488 b7489 d7478
            omega
          have d7490 : (x (-6) 5).toNat = 0 := by
            have r7491 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
            have b7492 := hb (x (-6) 5)
            have b7493 := hb (x (-6) 13)
            clear * - r7491 b7492 b7493 d7482
            omega
          have d7494 : (x (-7) 2).toNat = 0 := by
            have r7495 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e7496 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e7497 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b7498 := hb (x (-8) 3)
            have b7499 := hb (x (-7) 2)
            have b7500 := hb (x (-6) 13)
            have b7501 := hb (x (-5) 12)
            clear * - r7495 e7496 e7497 b7498 b7499 b7500 b7501 d7478 d7482
            omega
          have d7502 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
            have r7503 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b7504 := hb (x (-7) 2)
            have b7505 := hb (x (-5) 13)
            have b7506 := hb (x (-6) 1 && x (-6) 14)
            clear * - r7503 b7504 b7505 b7506 d7427 d7494
            omega
          have d7507 : (x (-6) 1).toNat = 1 := by
            have r7508 := hand1 (x (-6) 1) (x (-6) 14)
            have b7509 := hb (x (-6) 1)
            have b7510 := hb (x (-6) 1 && x (-6) 14)
            clear * - r7508 b7509 b7510 d7502
            omega
          have d7511 : (x (-5) 14).toNat = 0 := by
            have r7512 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b7513 := hb (x (-6) 1)
            have b7514 := hb (x (-5) 14)
            clear * - r7512 b7513 b7514 d7507
            omega
          have d7515 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
            have r7516 := hand2 (x (-5) 4) (x (-5) 14)
            have b7517 := hb (x (-5) 14)
            have b7518 := hb (x (-5) 4 && x (-5) 14)
            clear * - r7516 b7517 b7518 d7511
            omega
          have r7519 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b7520 := hb (x (-6) 5)
          have b7521 := hb (x (-1) 10)
          have b7522 := hb (x (-2) 1 && x (-2) 11)
          have b7523 := hb (x (-3) 2 && x (-3) 12)
          have b7524 := hb (x (-4) 3 && x (-4) 13)
          have b7525 := hb (x (-5) 4 && x (-5) 14)
          linarith only [r7519, b7520, b7521, b7522, b7523, b7524, b7525, g6, g116, d7439, d7455, d7515, d7490]
    · have f7526 : (x 0 10).toNat = 1 := by rw [h6025]; rfl
      have d7527 : (x 2 8).toNat = 0 := by
        have r7528 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7529 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e7530 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e7531 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e7532 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e7533 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e7534 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b7535 := hb (x (-5) 7)
        have b7536 := hb (x (-4) 6)
        have b7537 := hb (x (-3) 5)
        have b7538 := hb (x (-2) 4)
        have b7539 := hb (x (-1) 11)
        have b7540 := hb (x 0 10)
        have b7541 := hb (x 1 9)
        have b7542 := hb (x 2 8)
        clear * - r7528 e7529 e7530 e7531 e7532 e7533 e7534 b7535 b7536 b7537 b7538 b7539 b7540 b7541 b7542 g16 f7526 g7 g0
        omega
      have d7543 : (x (-2) 4).toNat = 0 := by
        have r7544 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7545 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e7546 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e7547 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e7548 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e7549 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e7550 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b7551 := hb (x (-5) 7)
        have b7552 := hb (x (-4) 6)
        have b7553 := hb (x (-3) 5)
        have b7554 := hb (x (-2) 4)
        have b7555 := hb (x (-1) 11)
        have b7556 := hb (x 0 10)
        have b7557 := hb (x 1 9)
        have b7558 := hb (x 2 8)
        clear * - r7544 e7545 e7546 e7547 e7548 e7549 e7550 b7551 b7552 b7553 b7554 b7555 b7556 b7557 b7558 d7527 g16 f7526 g7 g0
        omega
      have d7559 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
        have r7560 := hand1 (x (-2) 4) (x (-2) 14)
        have b7561 := hb (x (-2) 4)
        have b7562 := hb (x (-2) 4 && x (-2) 14)
        clear * - r7560 b7561 b7562 d7543
        omega
      have d7563 : (x 0 2 && x 0 12).toNat = 1 := by
        have r7564 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b7565 := hb (x (-3) 5)
        have b7566 := hb (x 2 10)
        have b7567 := hb (x 1 1 && x 1 11)
        have b7568 := hb (x 0 2 && x 0 12)
        have b7569 := hb (x (-1) 3 && x (-1) 13)
        have b7570 := hb (x (-2) 4 && x (-2) 14)
        clear * - r7564 b7565 b7566 b7567 b7568 b7569 b7570 g21 g119 g120 d7559 g0
        omega
      have d7571 : (x 0 12).toNat = 1 := by
        have r7572 := hand2 (x 0 2) (x 0 12)
        have b7573 := hb (x 0 12)
        have b7574 := hb (x 0 2 && x 0 12)
        clear * - r7572 b7573 b7574 d7563
        omega
      have d7575 : (x (-2) 2).toNat = 0 := by
        have r7576 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7577 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e7578 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b7579 := hb (x (-3) 3)
        have b7580 := hb (x (-2) 2)
        have b7581 := hb (x (-1) 13)
        have b7582 := hb (x 0 12)
        clear * - r7576 e7577 e7578 b7579 b7580 b7581 b7582 d7571 g8
        omega
      have d7583 : (x (-2) 10).toNat = 0 := by
        have r7584 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
        have b7585 := hb (x (-2) 2)
        have b7586 := hb (x (-2) 10)
        clear * - r7584 b7585 b7586 d7575
        omega
      have d7587 : (x (-3) 3).toNat = 0 := by
        have r7588 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7589 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e7590 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b7591 := hb (x (-3) 3)
        have b7592 := hb (x (-2) 2)
        have b7593 := hb (x (-1) 13)
        have b7594 := hb (x 0 12)
        clear * - r7588 e7589 e7590 b7591 b7592 b7593 b7594 d7571 g8 d7575
        omega
      have d7595 : (x (-3) 11).toNat = 0 := by
        have r7596 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
        have b7597 := hb (x (-3) 3)
        have b7598 := hb (x (-3) 11)
        clear * - r7596 b7597 b7598 d7587
        omega
      have d7599 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
        have r7600 := hand1 (x (-2) 4) (x (-2) 13)
        have b7601 := hb (x (-2) 4)
        have b7602 := hb (x (-2) 4 && x (-2) 13)
        clear * - r7600 b7601 b7602 d7543
        omega
      have d7603 : (x (-4) 6).toNat = 0 := by
        have r7604 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7605 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e7606 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e7607 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e7608 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e7609 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e7610 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have b7611 := hb (x (-5) 7)
        have b7612 := hb (x (-4) 6)
        have b7613 := hb (x (-3) 5)
        have b7614 := hb (x (-2) 4)
        have b7615 := hb (x (-1) 11)
        have b7616 := hb (x 0 10)
        have b7617 := hb (x 1 9)
        have b7618 := hb (x 2 8)
        clear * - r7604 e7605 e7606 e7607 e7608 e7609 e7610 b7611 b7612 b7613 b7614 b7615 b7616 b7617 b7618 d7527 g16 f7526 g7 d7543 g0
        omega
      have r7619 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7620 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7621 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7622 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e7623 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e7624 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e7625 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e7626 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e7627 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have r7628 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7629 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e7630 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e7631 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e7632 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e7633 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e7634 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have r7635 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7636 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
      have e7637 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
      have e7638 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
      have e7639 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
      have e7640 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
      have e7641 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
      have r7642 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7643 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e7644 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have r7645 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7646 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
      have e7647 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
      have r7648 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7649 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
      have e7650 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
      have r7651 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := by have q := hcov4 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7652 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
      have e7653 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
      have r7654 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7655 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7656 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7657 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7658 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7659 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have r7660 := hand2 (x 4 3) (x 4 7)
      have r7661 := hand2 (x (-1) 8) (x (-1) 12)
      have r7662 := hand2 (x (-2) 9) (x (-2) 13)
      have r7663 := hand2 (x 6 2) (x 6 6)
      have r7664 := hand2 (x 5 3) (x 5 7)
      have r7665 := hand1 (x 7 2) (x 7 6)
      have r7666 := hand1 (x 6 3) (x 6 7)
      have r7667 := hand2 (x 6 1) (x 6 7)
      have r7668 := hand1 (x (-1) 8) (x (-1) 14)
      have r7669 := hand2 (x 0 2) (x 0 11)
      have r7670 := hand2 (x 10 1) (x 10 10)
      have r7671 := hand2 (x 9 2) (x 9 11)
      have r7672 := hand1 (x 8 3) (x 8 12)
      have r7673 := hand2 (x 10 1) (x 10 11)
      have r7674 := hand2 (x 9 2) (x 9 12)
      have r7675 := hand2 (x 8 3) (x 8 13)
      have r7676 := hand1 (x 10 1) (x 10 14)
      linarith only [r7619, r7620, r7621, e7622, e7623, e7624, e7625, e7626, e7627, r7628, e7629, e7630, e7631, e7632, e7633, e7634, r7635, e7636, e7637, e7638, e7639, e7640, e7641, r7642, e7643, e7644, r7645, e7646, e7647, r7648, e7649, e7650, r7651, e7652, e7653, r7654, r7655, r7656, r7657, r7658, r7659, r7660, r7661, r7662, r7663, r7664, r7665, r7666, r7667, r7668, r7669, r7670, r7671, r7672, r7673, r7674, r7675, r7676, d7603, d7595, d7583, g3, g4, g6, g8, d7571, g17, g18, g21, g27, g30, g33, g36, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, d6007, g48, g49, g50, g51, g52, g53, d6021, g81, g82, g83, g84, g85, g86, g110, g111, d7599, g112, g113, g114, g126]
  · have f7782 : (x 0 9).toNat = 1 := by rw [h6011]; rfl
    have d7783 : (x 1 8).toNat = 0 := by
      have r7784 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7785 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e7786 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e7787 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e7788 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e7789 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e7790 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b7791 := hb (x (-6) 7)
      have b7792 := hb (x (-5) 6)
      have b7793 := hb (x (-4) 5)
      have b7794 := hb (x (-3) 4)
      have b7795 := hb (x (-2) 11)
      have b7796 := hb (x (-1) 10)
      have b7797 := hb (x 0 9)
      have b7798 := hb (x 1 8)
      clear * - r7784 e7785 e7786 e7787 e7788 e7789 e7790 b7791 b7792 b7793 b7794 b7795 b7796 b7797 b7798 f7782 g6 g3
      omega
    have d7799 : (x (-3) 4).toNat = 0 := by
      have r7800 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7801 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e7802 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e7803 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e7804 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e7805 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e7806 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b7807 := hb (x (-6) 7)
      have b7808 := hb (x (-5) 6)
      have b7809 := hb (x (-4) 5)
      have b7810 := hb (x (-3) 4)
      have b7811 := hb (x (-2) 11)
      have b7812 := hb (x (-1) 10)
      have b7813 := hb (x 0 9)
      have b7814 := hb (x 1 8)
      clear * - r7800 e7801 e7802 e7803 e7804 e7805 e7806 b7807 b7808 b7809 b7810 b7811 b7812 b7813 b7814 d7783 f7782 g6 g3
      omega
    have d7815 : (x (-3) 4 && x (-3) 11).toNat = 0 := by
      have r7816 := hand1 (x (-3) 4) (x (-3) 11)
      have b7817 := hb (x (-3) 4)
      have b7818 := hb (x (-3) 4 && x (-3) 11)
      clear * - r7816 b7817 b7818 d7799
      omega
    have d7819 : (x 0 1 && x 0 12).toNat = 1 := by
      have r7820 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7821 := hb (x (-3) 4)
      have b7822 := hb (x 1 11)
      have b7823 := hb (x 0 1 && x 0 12)
      have b7824 := hb (x (-1) 2 && x (-1) 13)
      have b7825 := hb (x (-2) 3 && x (-2) 14)
      clear * - r7820 b7821 b7822 b7823 b7824 b7825 g18 g128 g129 d7799
      omega
    have d7826 : (x 0 12).toNat = 1 := by
      have r7827 := hand2 (x 0 1) (x 0 12)
      have b7828 := hb (x 0 12)
      have b7829 := hb (x 0 1 && x 0 12)
      clear * - r7827 b7828 b7829 d7819
      omega
    have d7830 : (x (-2) 2).toNat = 0 := by
      have r7831 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7832 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e7833 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b7834 := hb (x (-3) 3)
      have b7835 := hb (x (-2) 2)
      have b7836 := hb (x (-1) 13)
      have b7837 := hb (x 0 12)
      clear * - r7831 e7832 e7833 b7834 b7835 b7836 b7837 d7826 g8
      omega
    have d7838 : (x (-2) 10).toNat = 0 := by
      have r7839 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
      have b7840 := hb (x (-2) 2)
      have b7841 := hb (x (-2) 10)
      clear * - r7839 b7840 b7841 d7830
      omega
    have d7842 : (x (-2) 4 && x (-2) 10).toNat = 0 := by
      have r7843 := hand2 (x (-2) 4) (x (-2) 10)
      have b7844 := hb (x (-2) 10)
      have b7845 := hb (x (-2) 4 && x (-2) 10)
      clear * - r7843 b7844 b7845 d7838
      omega
    have d7846 : (x (-3) 3).toNat = 0 := by
      have r7847 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7848 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e7849 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b7850 := hb (x (-3) 3)
      have b7851 := hb (x (-2) 2)
      have b7852 := hb (x (-1) 13)
      have b7853 := hb (x 0 12)
      clear * - r7847 e7848 e7849 b7850 b7851 b7852 b7853 d7826 g8 d7830
      omega
    have d7854 : (x (-3) 11).toNat = 0 := by
      have r7855 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
      have b7856 := hb (x (-3) 3)
      have b7857 := hb (x (-3) 11)
      clear * - r7855 b7856 b7857 d7846
      omega
    have d7858 : (x (-4) 5).toNat = 0 := by
      have r7859 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7860 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e7861 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e7862 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e7863 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e7864 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e7865 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b7866 := hb (x (-6) 7)
      have b7867 := hb (x (-5) 6)
      have b7868 := hb (x (-4) 5)
      have b7869 := hb (x (-3) 4)
      have b7870 := hb (x (-2) 11)
      have b7871 := hb (x (-1) 10)
      have b7872 := hb (x 0 9)
      have b7873 := hb (x 1 8)
      clear * - r7859 e7860 e7861 e7862 e7863 e7864 e7865 b7866 b7867 b7868 b7869 b7870 b7871 b7872 b7873 d7783 f7782 g6 g3 d7799
      omega
    have d7874 : (x (-4) 5 && x (-4) 14).toNat = 0 := by
      have r7875 := hand1 (x (-4) 5) (x (-4) 14)
      have b7876 := hb (x (-4) 5)
      have b7877 := hb (x (-4) 5 && x (-4) 14)
      clear * - r7875 b7876 b7877 d7858
      omega
    have d7878 : (x (-4) 5 && x (-4) 12).toNat = 0 := by
      have r7879 := hand1 (x (-4) 5) (x (-4) 12)
      have b7880 := hb (x (-4) 5)
      have b7881 := hb (x (-4) 5 && x (-4) 12)
      clear * - r7879 b7880 b7881 d7858
      omega
    have d7882 : (x (-4) 5 && x (-4) 10).toNat = 0 := by
      have r7883 := hand1 (x (-4) 5) (x (-4) 10)
      have b7884 := hb (x (-4) 5)
      have b7885 := hb (x (-4) 5 && x (-4) 10)
      clear * - r7883 b7884 b7885 d7858
      omega
    have d7886 : (x (-5) 6).toNat = 0 := by
      have r7887 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7888 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e7889 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e7890 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e7891 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e7892 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e7893 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b7894 := hb (x (-6) 7)
      have b7895 := hb (x (-5) 6)
      have b7896 := hb (x (-4) 5)
      have b7897 := hb (x (-3) 4)
      have b7898 := hb (x (-2) 11)
      have b7899 := hb (x (-1) 10)
      have b7900 := hb (x 0 9)
      have b7901 := hb (x 1 8)
      clear * - r7887 e7888 e7889 e7890 e7891 e7892 e7893 b7894 b7895 b7896 b7897 b7898 b7899 b7900 b7901 d7783 f7782 g6 g3 d7799 d7858
      omega
    have d7902 : (x (-5) 6 && x (-5) 13).toNat = 0 := by
      have r7903 := hand1 (x (-5) 6) (x (-5) 13)
      have b7904 := hb (x (-5) 6)
      have b7905 := hb (x (-5) 6 && x (-5) 13)
      clear * - r7903 b7904 b7905 d7886
      omega
    have d7906 : (x (-5) 6 && x (-5) 11).toNat = 0 := by
      have r7907 := hand1 (x (-5) 6) (x (-5) 11)
      have b7908 := hb (x (-5) 6)
      have b7909 := hb (x (-5) 6 && x (-5) 11)
      clear * - r7907 b7908 b7909 d7886
      omega
    have d7910 : (x 0 1 && x 0 10).toNat = 1 := by
      have r7911 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7912 := hb (x (-5) 6)
      have b7913 := hb (x 1 9)
      have b7914 := hb (x 0 1 && x 0 10)
      have b7915 := hb (x (-1) 2 && x (-1) 11)
      have b7916 := hb (x (-2) 3 && x (-2) 12)
      have b7917 := hb (x (-3) 4 && x (-3) 13)
      have b7918 := hb (x (-4) 5 && x (-4) 14)
      clear * - r7911 b7912 b7913 b7914 b7915 b7916 b7917 b7918 g16 g107 g108 g109 d7874 d7886
      omega
    have d7919 : (x 0 10).toNat = 1 := by
      have r7920 := hand2 (x 0 1) (x 0 10)
      have b7921 := hb (x 0 10)
      have b7922 := hb (x 0 1 && x 0 10)
      clear * - r7920 b7921 b7922 d7910
      omega
    have d7923 : (x 2 8).toNat = 0 := by
      have r7924 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7925 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e7926 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e7927 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e7928 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e7929 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e7930 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b7931 := hb (x (-5) 7)
      have b7932 := hb (x (-4) 6)
      have b7933 := hb (x (-3) 5)
      have b7934 := hb (x (-2) 4)
      have b7935 := hb (x (-1) 11)
      have b7936 := hb (x 0 10)
      have b7937 := hb (x 1 9)
      have b7938 := hb (x 2 8)
      clear * - r7924 e7925 e7926 e7927 e7928 e7929 e7930 b7931 b7932 b7933 b7934 b7935 b7936 b7937 b7938 g16 d7919 g7 g0
      omega
    have d7939 : (x 2 8 && x 2 14).toNat = 0 := by
      have r7940 := hand1 (x 2 8) (x 2 14)
      have b7941 := hb (x 2 8)
      have b7942 := hb (x 2 8 && x 2 14)
      clear * - r7940 b7941 b7942 d7923
      omega
    have d7943 : (x (-2) 4).toNat = 0 := by
      have r7944 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7945 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e7946 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e7947 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e7948 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e7949 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e7950 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b7951 := hb (x (-5) 7)
      have b7952 := hb (x (-4) 6)
      have b7953 := hb (x (-3) 5)
      have b7954 := hb (x (-2) 4)
      have b7955 := hb (x (-1) 11)
      have b7956 := hb (x 0 10)
      have b7957 := hb (x 1 9)
      have b7958 := hb (x 2 8)
      clear * - r7944 e7945 e7946 e7947 e7948 e7949 e7950 b7951 b7952 b7953 b7954 b7955 b7956 b7957 b7958 d7923 g16 d7919 g7 g0
      omega
    have d7959 : (x (-4) 6).toNat = 0 := by
      have r7960 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7961 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e7962 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e7963 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e7964 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e7965 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e7966 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b7967 := hb (x (-5) 7)
      have b7968 := hb (x (-4) 6)
      have b7969 := hb (x (-3) 5)
      have b7970 := hb (x (-2) 4)
      have b7971 := hb (x (-1) 11)
      have b7972 := hb (x 0 10)
      have b7973 := hb (x 1 9)
      have b7974 := hb (x 2 8)
      clear * - r7960 e7961 e7962 e7963 e7964 e7965 e7966 b7967 b7968 b7969 b7970 b7971 b7972 b7973 b7974 d7923 g16 d7919 g7 d7943 g0
      omega
    have d7975 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
      have r7976 := hand1 (x (-4) 6) (x (-4) 12)
      have b7977 := hb (x (-4) 6)
      have b7978 := hb (x (-4) 6 && x (-4) 12)
      clear * - r7976 b7977 b7978 d7959
      omega
    have d7979 : (x (-5) 7).toNat = 0 := by
      have r7980 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7981 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e7982 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e7983 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e7984 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e7985 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e7986 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b7987 := hb (x (-5) 7)
      have b7988 := hb (x (-4) 6)
      have b7989 := hb (x (-3) 5)
      have b7990 := hb (x (-2) 4)
      have b7991 := hb (x (-1) 11)
      have b7992 := hb (x 0 10)
      have b7993 := hb (x 1 9)
      have b7994 := hb (x 2 8)
      clear * - r7980 e7981 e7982 e7983 e7984 e7985 e7986 b7987 b7988 b7989 b7990 b7991 b7992 b7993 b7994 d7923 g16 d7919 g7 d7943 g0 d7959
      omega
    have d7995 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
      have r7996 := hand1 (x (-5) 7) (x (-5) 13)
      have b7997 := hb (x (-5) 7)
      have b7998 := hb (x (-5) 7 && x (-5) 13)
      clear * - r7996 b7997 b7998 d7979
      omega
    have d7999 : (x (-6) 7).toNat = 0 := by
      have r8000 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8001 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e8002 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e8003 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e8004 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e8005 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e8006 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b8007 := hb (x (-6) 7)
      have b8008 := hb (x (-5) 6)
      have b8009 := hb (x (-4) 5)
      have b8010 := hb (x (-3) 4)
      have b8011 := hb (x (-2) 11)
      have b8012 := hb (x (-1) 10)
      have b8013 := hb (x 0 9)
      have b8014 := hb (x 1 8)
      clear * - r8000 e8001 e8002 e8003 e8004 e8005 e8006 b8007 b8008 b8009 b8010 b8011 b8012 b8013 b8014 d7783 f7782 g6 g3 d7799 d7858 d7886
      omega
    have d8015 : (x (-6) 7 && x (-6) 14).toNat = 0 := by
      have r8016 := hand1 (x (-6) 7) (x (-6) 14)
      have b8017 := hb (x (-6) 7)
      have b8018 := hb (x (-6) 7 && x (-6) 14)
      clear * - r8016 b8017 b8018 d7999
      omega
    have d8019 : (x (-6) 7 && x (-6) 12).toNat = 0 := by
      have r8020 := hand1 (x (-6) 7) (x (-6) 12)
      have b8021 := hb (x (-6) 7)
      have b8022 := hb (x (-6) 7 && x (-6) 12)
      clear * - r8020 b8021 b8022 d7999
      omega
    have r8023 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8024 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8025 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
    have e8026 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
    have e8027 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
    have e8028 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
    have e8029 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
    have e8030 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
    have r8031 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8032 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
    have e8033 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
    have e8034 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
    have e8035 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
    have e8036 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
    have e8037 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
    have r8038 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8039 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e8040 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e8041 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e8042 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e8043 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e8044 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have r8045 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8046 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e8047 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e8048 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e8049 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e8050 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e8051 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have r8052 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8053 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e8054 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e8055 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e8056 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e8057 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e8058 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have r8059 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8060 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e8061 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e8062 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e8063 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e8064 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e8065 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have r8066 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8067 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e8068 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e8069 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e8070 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e8071 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e8072 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have r8073 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8074 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
    have e8075 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
    have r8076 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8077 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e8078 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have r8079 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8080 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e8081 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have r8082 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e8083 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
    have e8084 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
    have r8085 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8086 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8087 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8088 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8089 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8090 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8091 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8092 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8093 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8094 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8095 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r8096 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have r8097 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
    have r8098 := hand1 (x 6 2) (x 6 6)
    have r8099 := hand1 (x 5 3) (x 5 7)
    have r8100 := hand2 (x (-7) 8) (x (-7) 13)
    have r8101 := hand1 (x (-8) 9) (x (-8) 14)
    have r8102 := hand1 (x (-6) 8) (x (-6) 14)
    have r8103 := hand2 (x 5 1) (x 5 7)
    have r8104 := hand1 (x (-2) 8) (x (-2) 14)
    have r8105 := hand2 (x 7 1) (x 7 7)
    have r8106 := hand1 (x 4 4) (x 4 10)
    have r8107 := hand2 (x 9 1) (x 9 7)
    have r8108 := hand2 (x 8 2) (x 8 8)
    have r8109 := hand2 (x 7 3) (x 7 9)
    have r8110 := hand1 (x 4 6) (x 4 12)
    have r8111 := hand2 (x 10 1) (x 10 10)
    have r8112 := hand2 (x 9 2) (x 9 11)
    have r8113 := hand2 (x 8 3) (x 8 12)
    have r8114 := hand2 (x (-7) 1) (x (-7) 11)
    have r8115 := hand1 (x (-8) 2) (x (-8) 12)
    have r8116 := hand1 (x (-9) 3) (x (-9) 13)
    have r8117 := hand1 (x (-10) 4) (x (-10) 14)
    have r8118 := hand2 (x (-4) 2) (x (-4) 12)
    have r8119 := hand2 (x (-5) 3) (x (-5) 13)
    have r8120 := hand1 (x (-6) 4) (x (-6) 14)
    have r8121 := hand2 (x 7 1) (x 7 11)
    have r8122 := hand1 (x 4 4) (x 4 14)
    have r8123 := hand1 (x 13 1) (x 13 11)
    have r8124 := hand1 (x 12 2) (x 12 12)
    have r8125 := hand1 (x 11 3) (x 11 13)
    have r8126 := hand1 (x 10 4) (x 10 14)
    linarith only [r8023, r8024, e8025, e8026, e8027, e8028, e8029, e8030, r8031, e8032, e8033, e8034, e8035, e8036, e8037, r8038, e8039, e8040, e8041, e8042, e8043, e8044, r8045, e8046, e8047, e8048, e8049, e8050, e8051, r8052, e8053, e8054, e8055, e8056, e8057, e8058, r8059, e8060, e8061, e8062, e8063, e8064, e8065, r8066, e8067, e8068, e8069, e8070, e8071, e8072, r8073, e8074, e8075, r8076, e8077, e8078, r8079, e8080, e8081, r8082, e8083, e8084, r8085, r8086, r8087, r8088, r8089, r8090, r8091, r8092, r8093, r8094, r8095, r8096, r8097, r8098, r8099, r8100, r8101, r8102, r8103, r8104, r8105, r8106, r8107, r8108, r8109, r8110, r8111, r8112, r8113, r8114, r8115, r8116, r8117, r8118, r8119, r8120, r8121, r8122, r8123, r8124, r8125, r8126, g1, d7854, d7838, g5, g13, g15, g16, g19, g23, g25, g29, g31, g32, g33, g34, g35, g37, g44, g45, g46, g47, d6007, g48, g58, g59, g60, g61, d7882, d7906, d8019, g69, d6003, g70, d7842, g71, d7975, d7995, g75, g76, g77, g78, g79, g80, g87, g88, g89, g90, g91, d5999, g92, g93, g94, d7939, d5995, g96, g97, d7815, d7878, d7902, d8015, g113, g114, g115, g121, g122]

theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b100 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 5).toNat = 0)
    (g1 : (x (-3) 9).toNat = 0)
    (g2 : (x (-3) 13).toNat = 0)
    (g3 : (x (-2) 11).toNat = 0)
    (g4 : (x (-2) 14).toNat = 1)
    (g5 : (x (-1) 9).toNat = 0)
    (g6 : (x (-1) 10).toNat = 0)
    (g7 : (x (-1) 11).toNat = 0)
    (g8 : (x (-1) 13).toNat = 0)
    (g9 : (x 0 3).toNat = 1)
    (g10 : (x 0 6).toNat = 0)
    (g11 : (x 0 7).toNat = 0)
    (g12 : (x 0 8).toNat = 0)
    (g13 : (x 0 14).toNat = 1)
    (g14 : (x 1 2).toNat = 0)
    (g15 : (x 1 5).toNat = 0)
    (g16 : (x 1 9).toNat = 0)
    (g17 : (x 1 10).toNat = 0)
    (g18 : (x 1 11).toNat = 0)
    (g19 : (x 1 13).toNat = 0)
    (g20 : (x 2 1).toNat = 1)
    (g21 : (x 2 10).toNat = 0)
    (g22 : (x 2 11).toNat = 0)
    (g23 : (x 2 12).toNat = 0)
    (g24 : (x 3 2).toNat = 0)
    (g25 : (x 3 5).toNat = 0)
    (g26 : (x 3 6).toNat = 0)
    (g27 : (x 3 9).toNat = 0)
    (g28 : (x 3 10).toNat = 0)
    (g29 : (x 3 11).toNat = 0)
    (g30 : (x 4 8).toNat = 0)
    (g31 : (x 4 10).toNat = 1)
    (g32 : (x 5 5).toNat = 0)
    (g33 : (x 5 6).toNat = 0)
    (g34 : (x 5 9).toNat = 0)
    (g35 : (x 6 4).toNat = 0)
    (g36 : (x 6 5).toNat = 0)
    (g37 : (x 6 8).toNat = 0)
    (g38 : (x 7 4).toNat = 0)
    (g39 : (x 5 2 && x 5 6).toNat = 0)
    (g40 : (x 3 4 && x 3 8).toNat = 0)
    (g41 : (x 2 5 && x 2 9).toNat = 0)
    (g42 : (x 1 6 && x 1 10).toNat = 0)
    (g43 : (x 0 7 && x 0 11).toNat = 0)
    (g44 : (x 4 4 && x 4 8).toNat = 0)
    (g45 : (x 3 5 && x 3 9).toNat = 0)
    (g46 : (x 2 6 && x 2 10).toNat = 0)
    (g47 : (x 1 7 && x 1 11).toNat = 0)
    (g48 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g49 : (x 5 4 && x 5 8).toNat = 0)
    (g50 : (x 4 5 && x 4 9).toNat = 0)
    (g51 : (x 3 6 && x 3 10).toNat = 0)
    (g52 : (x 2 7 && x 2 11).toNat = 0)
    (g53 : (x 1 8 && x 1 12).toNat = 0)
    (g54 : (x 4 8 && x 4 12).toNat = 0)
    (g55 : (x 3 9 && x 3 13).toNat = 0)
    (g56 : (x 5 8 && x 5 12).toNat = 0)
    (g57 : (x 4 9 && x 4 13).toNat = 0)
    (g58 : (x 0 1 && x 0 6).toNat = 0)
    (g59 : (x (-1) 2 && x (-1) 7).toNat = 0)
    (g60 : (x (-2) 3 && x (-2) 8).toNat = 0)
    (g61 : (x (-3) 4 && x (-3) 9).toNat = 0)
    (g62 : (x 6 3 && x 6 8).toNat = 0)
    (g63 : (x 5 4 && x 5 9).toNat = 0)
    (g64 : (x 3 6 && x 3 11).toNat = 0)
    (g65 : (x 2 7 && x 2 12).toNat = 0)
    (g66 : (x 1 8 && x 1 13).toNat = 0)
    (g67 : (x (-1) 1 && x (-1) 7).toNat = 0)
    (g68 : (x (-3) 3 && x (-3) 9).toNat = 0)
    (g69 : (x 1 1 && x 1 7).toNat = 0)
    (g70 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g71 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g72 : (x 1 2 && x 1 8).toNat = 0)
    (g73 : (x (-1) 4 && x (-1) 10).toNat = 0)
    (g74 : (x (-2) 5 && x (-2) 11).toNat = 0)
    (g75 : (x 4 2 && x 4 8).toNat = 0)
    (g76 : (x 3 3 && x 3 9).toNat = 0)
    (g77 : (x 2 4 && x 2 10).toNat = 0)
    (g78 : (x 1 5 && x 1 11).toNat = 0)
    (g79 : (x 0 6 && x 0 12).toNat = 0)
    (g80 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g81 : (x 5 2 && x 5 8).toNat = 0)
    (g82 : (x 4 3 && x 4 9).toNat = 0)
    (g83 : (x 3 4 && x 3 10).toNat = 0)
    (g84 : (x 2 5 && x 2 11).toNat = 0)
    (g85 : (x 1 6 && x 1 12).toNat = 0)
    (g86 : (x 0 7 && x 0 13).toNat = 0)
    (g87 : (x 6 2 && x 6 8).toNat = 0)
    (g88 : (x 5 3 && x 5 9).toNat = 0)
    (g89 : (x 3 5 && x 3 11).toNat = 0)
    (g90 : (x 2 6 && x 2 12).toNat = 0)
    (g91 : (x 1 7 && x 1 13).toNat = 0)
    (g92 : (x 6 4 && x 6 10).toNat = 0)
    (g93 : (x 5 5 && x 5 11).toNat = 0)
    (g94 : (x 3 7 && x 3 13).toNat = 0)
    (g95 : (x (-1) 1 && x (-1) 8).toNat = 0)
    (g96 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g97 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g98 : (x 5 1 && x 5 8).toNat = 0)
    (g99 : (x 4 2 && x 4 9).toNat = 0)
    (g100 : (x 3 3 && x 3 10).toNat = 0)
    (g101 : (x 2 4 && x 2 11).toNat = 0)
    (g102 : (x 1 5 && x 1 12).toNat = 0)
    (g103 : (x 0 6 && x 0 13).toNat = 0)
    (g104 : (x (-1) 7 && x (-1) 14).toNat = 0)
    (g105 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g106 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g107 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g108 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g109 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g110 : (x 1 1 && x 1 10).toNat = 0)
    (g111 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g112 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g113 : (x 7 4 && x 7 13).toNat = 0)
    (g114 : (x 6 5 && x 6 14).toNat = 0)
    (g115 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g116 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g117 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g118 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g119 : (x 1 1 && x 1 11).toNat = 0)
    (g120 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g121 : (x 6 2 && x 6 12).toNat = 0)
    (g122 : (x 5 3 && x 5 13).toNat = 0)
    (g123 : (x 7 2 && x 7 12).toNat = 0)
    (g124 : (x 6 3 && x 6 13).toNat = 0)
    (g125 : (x 5 4 && x 5 14).toNat = 0)
    (g126 : (x 7 4 && x 7 14).toNat = 0)
    (g127 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g128 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g129 : (x (-2) 3 && x (-2) 14).toNat = 0)
    (g130 : (x (-3) 1 && x (-3) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_four_iff_five_core_b100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114 g115 g116 g117 g118 g119 g120 g121 g122 g123 g124 g125 g126 g127 g128 g129 g130
