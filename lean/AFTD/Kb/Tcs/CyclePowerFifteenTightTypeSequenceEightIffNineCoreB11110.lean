import AFTD.Prelude

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b11110

Topic: combinatorics   Node: 4246887b3893

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 115 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b11110_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 6).toNat = 0)
    (g1 : (x (-3) 7).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 6).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-1) 2).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 7).toNat = 0)
    (g9 : (x (-1) 9).toNat = 0)
    (g10 : (x (-1) 10).toNat = 0)
    (g11 : (x (-1) 11).toNat = 0)
    (g12 : (x (-1) 13).toNat = 0)
    (g13 : (x 0 4).toNat = 1)
    (g14 : (x 0 6).toNat = 1)
    (g15 : (x 0 7).toNat = 0)
    (g16 : (x 0 8).toNat = 0)
    (g17 : (x 0 9).toNat = 1)
    (g18 : (x 0 11).toNat = 1)
    (g19 : (x 0 12).toNat = 1)
    (g20 : (x 0 13).toNat = 1)
    (g21 : (x 1 2).toNat = 0)
    (g22 : (x 1 4).toNat = 0)
    (g23 : (x 1 5).toNat = 0)
    (g24 : (x 1 6).toNat = 0)
    (g25 : (x 1 8).toNat = 0)
    (g26 : (x 1 10).toNat = 0)
    (g27 : (x 1 11).toNat = 0)
    (g28 : (x 1 12).toNat = 0)
    (g29 : (x 2 4).toNat = 0)
    (g30 : (x 2 5).toNat = 0)
    (g31 : (x 2 9).toNat = 0)
    (g32 : (x 2 10).toNat = 0)
    (g33 : (x 2 11).toNat = 0)
    (g34 : (x 3 4).toNat = 0)
    (g35 : (x 3 8).toNat = 0)
    (g36 : (x 3 9).toNat = 0)
    (g37 : (x 3 10).toNat = 0)
    (g38 : (x 4 8).toNat = 0)
    (g39 : (x 4 9).toNat = 0)
    (g40 : (x 5 8).toNat = 0)
    (g41 : (x (-2) 1 && x (-2) 3).toNat = 0)
    (g42 : (x (-3) 2 && x (-3) 4).toNat = 0)
    (g43 : (x (-4) 3 && x (-4) 5).toNat = 0)
    (g44 : (x (-5) 4 && x (-5) 6).toNat = 0)
    (g45 : (x (-6) 5 && x (-6) 7).toNat = 0)
    (g46 : (x 1 2 && x 1 6).toNat = 0)
    (g47 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g48 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g49 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g50 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g51 : (x 0 4 && x 0 8).toNat = 0)
    (g52 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g53 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g54 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g55 : (x 3 4 && x 3 8).toNat = 0)
    (g56 : (x 2 5 && x 2 9).toNat = 0)
    (g57 : (x 1 6 && x 1 10).toNat = 0)
    (g58 : (x 4 4 && x 4 8).toNat = 0)
    (g59 : (x 3 5 && x 3 9).toNat = 0)
    (g60 : (x 2 6 && x 2 10).toNat = 0)
    (g61 : (x 1 7 && x 1 11).toNat = 0)
    (g62 : (x 0 8 && x 0 12).toNat = 0)
    (g63 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g64 : (x 3 8 && x 3 13).toNat = 0)
    (g65 : (x 2 9 && x 2 14).toNat = 0)
    (g66 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g67 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g68 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g69 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g70 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g71 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g72 : (x 0 2 && x 0 8).toNat = 0)
    (g73 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g74 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g75 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g76 : (x 5 2 && x 5 8).toNat = 0)
    (g77 : (x 4 3 && x 4 9).toNat = 0)
    (g78 : (x 3 4 && x 3 10).toNat = 0)
    (g79 : (x 2 5 && x 2 11).toNat = 0)
    (g80 : (x 1 6 && x 1 12).toNat = 0)
    (g81 : (x 6 2 && x 6 8).toNat = 0)
    (g82 : (x 5 3 && x 5 9).toNat = 0)
    (g83 : (x 4 4 && x 4 10).toNat = 0)
    (g84 : (x 3 5 && x 3 11).toNat = 0)
    (g85 : (x 2 6 && x 2 12).toNat = 0)
    (g86 : (x 1 7 && x 1 13).toNat = 0)
    (g87 : (x 0 8 && x 0 14).toNat = 0)
    (g88 : (x 0 1 && x 0 8).toNat = 0)
    (g89 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g90 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g91 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g92 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g93 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g94 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g95 : (x 6 1 && x 6 8).toNat = 0)
    (g96 : (x 5 2 && x 5 9).toNat = 0)
    (g97 : (x 4 3 && x 4 10).toNat = 0)
    (g98 : (x 3 4 && x 3 11).toNat = 0)
    (g99 : (x 2 5 && x 2 12).toNat = 0)
    (g100 : (x 1 6 && x 1 13).toNat = 0)
    (g101 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g102 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g103 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g104 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g105 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g106 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g107 : (x 3 4 && x 3 13).toNat = 0)
    (g108 : (x 2 5 && x 2 14).toNat = 0)
    (g109 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g110 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g111 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g112 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g113 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g114 : (x 2 4 && x 2 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d19327 : (x 0 7 && x 0 14).toNat = 0 := by
    have r19328 := hand1 (x 0 7) (x 0 14)
    have b19329 := hb (x 0 7)
    have b19330 := hb (x 0 7 && x 0 14)
    clear * - r19328 b19329 b19330 g15
    omega
  have d19331 : (x 0 7 && x 0 13).toNat = 0 := by
    have r19332 := hand1 (x 0 7) (x 0 13)
    have b19333 := hb (x 0 7)
    have b19334 := hb (x 0 7 && x 0 13)
    clear * - r19332 b19333 b19334 g15
    omega
  have d19335 : (x 0 1 && x 0 7).toNat = 0 := by
    have r19336 := hand2 (x 0 1) (x 0 7)
    have b19337 := hb (x 0 7)
    have b19338 := hb (x 0 1 && x 0 7)
    clear * - r19336 b19337 b19338 g15
    omega
  have d19339 : (x 0 7 && x 0 11).toNat = 0 := by
    have r19340 := hand1 (x 0 7) (x 0 11)
    have b19341 := hb (x 0 7)
    have b19342 := hb (x 0 7 && x 0 11)
    clear * - r19340 b19341 b19342 g15
    omega
  have d19343 : (x 0 3 && x 0 7).toNat = 0 := by
    have r19344 := hand2 (x 0 3) (x 0 7)
    have b19345 := hb (x 0 7)
    have b19346 := hb (x 0 3 && x 0 7)
    clear * - r19344 b19345 b19346 g15
    omega
  cases h19347 : x 0 10
  · have f19348 : (x 0 10).toNat = 0 := by rw [h19347]; rfl
    have d19349 : (x 0 1 && x 0 10).toNat = 0 := by
      have r19350 := hand2 (x 0 1) (x 0 10)
      have b19351 := hb (x 0 10)
      have b19352 := hb (x 0 1 && x 0 10)
      clear * - r19350 b19351 b19352 f19348
      omega
    have d19353 : (x 1 9).toNat = 1 := by
      have r19354 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19355 := hb (x (-5) 6)
      have b19356 := hb (x 1 9)
      have b19357 := hb (x 0 1 && x 0 10)
      have b19358 := hb (x (-1) 2 && x (-1) 11)
      have b19359 := hb (x (-2) 3 && x (-2) 12)
      have b19360 := hb (x (-3) 4 && x (-3) 13)
      have b19361 := hb (x (-4) 5 && x (-4) 14)
      clear * - r19354 b19355 b19356 b19357 b19358 b19359 b19360 b19361 d19349 g103 g104 g105 g106 g0
      omega
    have d19362 : (x 1 1).toNat = 1 := by
      have r19363 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b19364 := hb (x 1 1)
      have b19365 := hb (x 1 9)
      clear * - r19363 b19364 b19365 d19353
      omega
    have d19366 : (x 2 14).toNat = 0 := by
      have r19367 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19368 := hb (x 1 1)
      have b19369 := hb (x 2 14)
      clear * - r19367 b19368 b19369 d19362
      omega
    have d19370 : (x 2 1 && x 2 14).toNat = 0 := by
      have r19371 := hand2 (x 2 1) (x 2 14)
      have b19372 := hb (x 2 14)
      have b19373 := hb (x 2 1 && x 2 14)
      clear * - r19371 b19372 b19373 d19366
      omega
    have d19374 : (x 3 13).toNat = 1 := by
      have r19375 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19376 := hb (x 1 2)
      have b19377 := hb (x 3 13)
      have b19378 := hb (x 2 1 && x 2 14)
      clear * - r19375 b19376 b19377 b19378 d19370 g21
      omega
    have d19379 : (x 3 1).toNat = 1 := by
      have r19380 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b19381 := hb (x 3 1)
      have b19382 := hb (x 3 13)
      clear * - r19380 b19381 b19382 d19374
      omega
    have d19383 : (x 4 12).toNat = 0 := by
      have r19384 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19385 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e19386 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b19387 := hb (x 1 3)
      have b19388 := hb (x 2 2)
      have b19389 := hb (x 3 13)
      have b19390 := hb (x 4 12)
      clear * - r19384 e19385 e19386 b19387 b19388 b19389 b19390 d19374
      omega
    have d19391 : (x 4 3 && x 4 12).toNat = 0 := by
      have r19392 := hand2 (x 4 3) (x 4 12)
      have b19393 := hb (x 4 12)
      have b19394 := hb (x 4 3 && x 4 12)
      clear * - r19392 b19393 b19394 d19383
      omega
    have d19395 : (x 4 4).toNat = 0 := by
      have r19396 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b19397 := hb (x 4 4)
      have b19398 := hb (x 4 12)
      clear * - r19396 b19397 b19398 d19383
      omega
    have d19399 : (x 2 2).toNat = 0 := by
      have r19400 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19401 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e19402 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b19403 := hb (x 1 3)
      have b19404 := hb (x 2 2)
      have b19405 := hb (x 3 13)
      have b19406 := hb (x 4 12)
      clear * - r19400 e19401 e19402 b19403 b19404 b19405 b19406 d19383 d19374
      omega
    have d19407 : (x 2 2 && x 2 6).toNat = 0 := by
      have r19408 := hand1 (x 2 2) (x 2 6)
      have b19409 := hb (x 2 2)
      have b19410 := hb (x 2 2 && x 2 6)
      clear * - r19408 b19409 b19410 d19399
      omega
    have d19411 : (x 1 3).toNat = 0 := by
      have r19412 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19413 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e19414 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b19415 := hb (x 1 3)
      have b19416 := hb (x 2 2)
      have b19417 := hb (x 3 13)
      have b19418 := hb (x 4 12)
      clear * - r19412 e19413 e19414 b19415 b19416 b19417 b19418 d19383 d19374 d19399
      omega
    have d19419 : (x 1 3 && x 1 7).toNat = 0 := by
      have r19420 := hand1 (x 1 3) (x 1 7)
      have b19421 := hb (x 1 3)
      have b19422 := hb (x 1 3 && x 1 7)
      clear * - r19420 b19421 b19422 d19411
      omega
    have d19423 : (x 2 6).toNat = 0 := by
      have r19424 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
      have b19425 := hb (x 2 6)
      have b19426 := hb (x 2 14)
      clear * - r19424 b19425 b19426 d19366
      omega
    have r19427 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r19428 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19429 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
    have e19430 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
    have e19431 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
    have e19432 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
    have e19433 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
    have e19434 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
    have r19435 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19436 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e19437 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e19438 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e19439 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e19440 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e19441 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have r19442 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19443 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e19444 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have r19445 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19446 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
    have e19447 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
    have r19448 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r19449 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r19450 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r19451 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r19452 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have r19453 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have r19454 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have r19455 := hand1 (x (-4) 8) (x (-4) 12)
    have r19456 := hand1 (x (-5) 9) (x (-5) 13)
    have r19457 := hand2 (x 6 1) (x 6 10)
    have r19458 := hand2 (x 5 2) (x 5 11)
    have r19459 := hand1 (x (-4) 4) (x (-4) 14)
    have r19460 := hand2 (x (-8) 1) (x (-8) 12)
    have r19461 := hand2 (x (-9) 2) (x (-9) 13)
    have r19462 := hand2 (x (-10) 3) (x (-10) 14)
    linarith only [r19427, r19428, e19429, e19430, e19431, e19432, e19433, e19434, r19435, e19436, e19437, e19438, e19439, e19440, e19441, r19442, e19443, e19444, r19445, e19446, e19447, r19448, r19449, r19450, r19451, r19452, r19453, r19454, r19455, r19456, r19457, r19458, r19459, r19460, r19461, r19462, g1, g3, g7, g13, f19348, d19411, g24, d19399, d19423, d19379, d19395, d19407, d19419, g51, g52, g53, g54, g88, g89, g90, g91, g92, g93, g94, d19391, g107, g108, g111, g112, g113]
  · have f19528 : (x 0 10).toNat = 1 := by rw [h19347]; rfl
    have d19529 : (x 2 8).toNat = 0 := by
      have r19530 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19531 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19532 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19533 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19534 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19535 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19536 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19537 := hb (x (-5) 7)
      have b19538 := hb (x (-4) 6)
      have b19539 := hb (x (-3) 5)
      have b19540 := hb (x (-2) 4)
      have b19541 := hb (x (-1) 11)
      have b19542 := hb (x 0 10)
      have b19543 := hb (x 1 9)
      have b19544 := hb (x 2 8)
      clear * - r19530 e19531 e19532 e19533 e19534 e19535 e19536 b19537 b19538 b19539 b19540 b19541 b19542 b19543 b19544 f19528 g11
      omega
    have d19545 : (x 1 9).toNat = 0 := by
      have r19546 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19547 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19548 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19549 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19550 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19551 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19552 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19553 := hb (x (-5) 7)
      have b19554 := hb (x (-4) 6)
      have b19555 := hb (x (-3) 5)
      have b19556 := hb (x (-2) 4)
      have b19557 := hb (x (-1) 11)
      have b19558 := hb (x 0 10)
      have b19559 := hb (x 1 9)
      have b19560 := hb (x 2 8)
      clear * - r19546 e19547 e19548 e19549 e19550 e19551 e19552 b19553 b19554 b19555 b19556 b19557 b19558 b19559 b19560 d19529 f19528 g11
      omega
    have d19561 : (x (-2) 4).toNat = 0 := by
      have r19562 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19563 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19564 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19565 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19566 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19567 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19568 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19569 := hb (x (-5) 7)
      have b19570 := hb (x (-4) 6)
      have b19571 := hb (x (-3) 5)
      have b19572 := hb (x (-2) 4)
      have b19573 := hb (x (-1) 11)
      have b19574 := hb (x 0 10)
      have b19575 := hb (x 1 9)
      have b19576 := hb (x 2 8)
      clear * - r19562 e19563 e19564 e19565 e19566 e19567 e19568 b19569 b19570 b19571 b19572 b19573 b19574 b19575 b19576 d19529 d19545 f19528 g11
      omega
    have d19577 : (x (-3) 5).toNat = 0 := by
      have r19578 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19579 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19580 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19581 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19582 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19583 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19584 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19585 := hb (x (-5) 7)
      have b19586 := hb (x (-4) 6)
      have b19587 := hb (x (-3) 5)
      have b19588 := hb (x (-2) 4)
      have b19589 := hb (x (-1) 11)
      have b19590 := hb (x 0 10)
      have b19591 := hb (x 1 9)
      have b19592 := hb (x 2 8)
      clear * - r19578 e19579 e19580 e19581 e19582 e19583 e19584 b19585 b19586 b19587 b19588 b19589 b19590 b19591 b19592 d19529 d19545 f19528 g11 d19561
      omega
    have d19593 : (x (-4) 6).toNat = 0 := by
      have r19594 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19595 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19596 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19597 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19598 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19599 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19600 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19601 := hb (x (-5) 7)
      have b19602 := hb (x (-4) 6)
      have b19603 := hb (x (-3) 5)
      have b19604 := hb (x (-2) 4)
      have b19605 := hb (x (-1) 11)
      have b19606 := hb (x 0 10)
      have b19607 := hb (x 1 9)
      have b19608 := hb (x 2 8)
      clear * - r19594 e19595 e19596 e19597 e19598 e19599 e19600 b19601 b19602 b19603 b19604 b19605 b19606 b19607 b19608 d19529 d19545 f19528 g11 d19561 d19577
      omega
    have d19609 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
      have r19610 := hand1 (x (-4) 6) (x (-4) 12)
      have b19611 := hb (x (-4) 6)
      have b19612 := hb (x (-4) 6 && x (-4) 12)
      clear * - r19610 b19611 b19612 d19593
      omega
    have d19613 : (x (-5) 7).toNat = 0 := by
      have r19614 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19615 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19616 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19617 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19618 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19619 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19620 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19621 := hb (x (-5) 7)
      have b19622 := hb (x (-4) 6)
      have b19623 := hb (x (-3) 5)
      have b19624 := hb (x (-2) 4)
      have b19625 := hb (x (-1) 11)
      have b19626 := hb (x 0 10)
      have b19627 := hb (x 1 9)
      have b19628 := hb (x 2 8)
      clear * - r19614 e19615 e19616 e19617 e19618 e19619 e19620 b19621 b19622 b19623 b19624 b19625 b19626 b19627 b19628 d19529 d19545 f19528 g11 d19561 d19577 d19593
      omega
    have d19629 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
      have r19630 := hand1 (x (-5) 7) (x (-5) 13)
      have b19631 := hb (x (-5) 7)
      have b19632 := hb (x (-5) 7 && x (-5) 13)
      clear * - r19630 b19631 b19632 d19613
      omega
    cases h19633 : x 1 1
    · have f19634 : (x 1 1).toNat = 0 := by rw [h19633]; rfl
      have d19635 : (x 1 1 && x 1 7).toNat = 0 := by
        have r19636 := hand1 (x 1 1) (x 1 7)
        have b19637 := hb (x 1 1)
        have b19638 := hb (x 1 1 && x 1 7)
        clear * - r19636 b19637 b19638 f19634
        omega
      have d19639 : (x 2 14).toNat = 1 := by
        have r19640 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b19641 := hb (x 1 1)
        have b19642 := hb (x 2 14)
        clear * - r19640 b19641 b19642 f19634
        omega
      cases h19643 : x 1 3
      · have f19644 : (x 1 3).toNat = 0 := by rw [h19643]; rfl
        cases h19645 : x 1 7
        · have f19646 : (x 1 7).toNat = 0 := by rw [h19645]; rfl
          have d19647 : (x (-7) 8).toNat = 1 := by
            have r19648 : 1 ≤ (x 1 7).toNat + (x 0 1 && x 0 8).toNat + (x (-1) 2 && x (-1) 9).toNat + (x (-2) 3 && x (-2) 10).toNat + (x (-3) 4 && x (-3) 11).toNat + (x (-4) 5 && x (-4) 12).toNat + (x (-5) 6 && x (-5) 13).toNat + (x (-6) 7 && x (-6) 14).toNat + (x (-7) 8).toNat := by have q := hcov7 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19649 := hb (x (-7) 8)
            have b19650 := hb (x 1 7)
            have b19651 := hb (x 0 1 && x 0 8)
            have b19652 := hb (x (-1) 2 && x (-1) 9)
            have b19653 := hb (x (-2) 3 && x (-2) 10)
            have b19654 := hb (x (-3) 4 && x (-3) 11)
            have b19655 := hb (x (-4) 5 && x (-4) 12)
            have b19656 := hb (x (-5) 6 && x (-5) 13)
            have b19657 := hb (x (-6) 7 && x (-6) 14)
            clear * - r19648 b19649 b19650 b19651 b19652 b19653 b19654 b19655 b19656 b19657 f19646 g88 g89 g90 g91 g92 g93 g94
            omega
          have d19658 : (x (-8) 9).toNat = 0 := by
            have r19659 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19660 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e19661 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e19662 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e19663 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e19664 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e19665 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b19666 := hb (x (-14) 7)
            have b19667 := hb (x (-13) 6)
            have b19668 := hb (x (-12) 5)
            have b19669 := hb (x (-11) 4)
            have b19670 := hb (x (-10) 11)
            have b19671 := hb (x (-9) 10)
            have b19672 := hb (x (-8) 9)
            have b19673 := hb (x (-7) 8)
            clear * - r19659 e19660 e19661 e19662 e19663 e19664 e19665 b19666 b19667 b19668 b19669 b19670 b19671 b19672 b19673 d19647
            omega
          have d19674 : (x (-8) 7 && x (-8) 9).toNat = 0 := by
            have r19675 := hand2 (x (-8) 7) (x (-8) 9)
            have b19676 := hb (x (-8) 9)
            have b19677 := hb (x (-8) 7 && x (-8) 9)
            clear * - r19675 b19676 b19677 d19658
            omega
          have d19678 : (x (-9) 10).toNat = 0 := by
            have r19679 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19680 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e19681 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e19682 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e19683 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e19684 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e19685 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b19686 := hb (x (-14) 7)
            have b19687 := hb (x (-13) 6)
            have b19688 := hb (x (-12) 5)
            have b19689 := hb (x (-11) 4)
            have b19690 := hb (x (-10) 11)
            have b19691 := hb (x (-9) 10)
            have b19692 := hb (x (-8) 9)
            have b19693 := hb (x (-7) 8)
            clear * - r19679 e19680 e19681 e19682 e19683 e19684 e19685 b19686 b19687 b19688 b19689 b19690 b19691 b19692 b19693 d19647 d19658
            omega
          have d19694 : (x (-9) 8 && x (-9) 10).toNat = 0 := by
            have r19695 := hand2 (x (-9) 8) (x (-9) 10)
            have b19696 := hb (x (-9) 10)
            have b19697 := hb (x (-9) 8 && x (-9) 10)
            clear * - r19695 b19696 b19697 d19678
            omega
          have d19698 : (x (-10) 11).toNat = 0 := by
            have r19699 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19700 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e19701 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e19702 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e19703 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e19704 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e19705 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b19706 := hb (x (-14) 7)
            have b19707 := hb (x (-13) 6)
            have b19708 := hb (x (-12) 5)
            have b19709 := hb (x (-11) 4)
            have b19710 := hb (x (-10) 11)
            have b19711 := hb (x (-9) 10)
            have b19712 := hb (x (-8) 9)
            have b19713 := hb (x (-7) 8)
            clear * - r19699 e19700 e19701 e19702 e19703 e19704 e19705 b19706 b19707 b19708 b19709 b19710 b19711 b19712 b19713 d19647 d19658 d19678
            omega
          have d19714 : (x (-10) 9 && x (-10) 11).toNat = 0 := by
            have r19715 := hand2 (x (-10) 9) (x (-10) 11)
            have b19716 := hb (x (-10) 11)
            have b19717 := hb (x (-10) 9 && x (-10) 11)
            clear * - r19715 b19716 b19717 d19698
            omega
          have d19718 : (x (-11) 4).toNat = 0 := by
            have r19719 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19720 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e19721 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e19722 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e19723 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e19724 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e19725 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b19726 := hb (x (-14) 7)
            have b19727 := hb (x (-13) 6)
            have b19728 := hb (x (-12) 5)
            have b19729 := hb (x (-11) 4)
            have b19730 := hb (x (-10) 11)
            have b19731 := hb (x (-9) 10)
            have b19732 := hb (x (-8) 9)
            have b19733 := hb (x (-7) 8)
            clear * - r19719 e19720 e19721 e19722 e19723 e19724 e19725 b19726 b19727 b19728 b19729 b19730 b19731 b19732 b19733 d19647 d19658 d19678 d19698
            omega
          have d19734 : (x (-11) 4 && x (-11) 13).toNat = 0 := by
            have r19735 := hand1 (x (-11) 4) (x (-11) 13)
            have b19736 := hb (x (-11) 4)
            have b19737 := hb (x (-11) 4 && x (-11) 13)
            clear * - r19735 b19736 b19737 d19718
            omega
          have d19738 : (x (-12) 5).toNat = 0 := by
            have r19739 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19740 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e19741 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e19742 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e19743 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e19744 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e19745 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b19746 := hb (x (-14) 7)
            have b19747 := hb (x (-13) 6)
            have b19748 := hb (x (-12) 5)
            have b19749 := hb (x (-11) 4)
            have b19750 := hb (x (-10) 11)
            have b19751 := hb (x (-9) 10)
            have b19752 := hb (x (-8) 9)
            have b19753 := hb (x (-7) 8)
            clear * - r19739 e19740 e19741 e19742 e19743 e19744 e19745 b19746 b19747 b19748 b19749 b19750 b19751 b19752 b19753 d19647 d19658 d19678 d19698 d19718
            omega
          have d19754 : (x (-12) 5 && x (-12) 14).toNat = 0 := by
            have r19755 := hand1 (x (-12) 5) (x (-12) 14)
            have b19756 := hb (x (-12) 5)
            have b19757 := hb (x (-12) 5 && x (-12) 14)
            clear * - r19755 b19756 b19757 d19738
            omega
          have d19758 : (x (-13) 6).toNat = 0 := by
            have r19759 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e19760 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
            have e19761 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
            have e19762 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
            have e19763 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
            have e19764 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
            have e19765 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
            have b19766 := hb (x (-14) 7)
            have b19767 := hb (x (-13) 6)
            have b19768 := hb (x (-12) 5)
            have b19769 := hb (x (-11) 4)
            have b19770 := hb (x (-10) 11)
            have b19771 := hb (x (-9) 10)
            have b19772 := hb (x (-8) 9)
            have b19773 := hb (x (-7) 8)
            clear * - r19759 e19760 e19761 e19762 e19763 e19764 e19765 b19766 b19767 b19768 b19769 b19770 b19771 b19772 b19773 d19647 d19658 d19678 d19698 d19718 d19738
            omega
          have d19774 : (x (-7) 8 && x (-7) 14).toNat = 1 := by
            have r19775 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19776 := hb (x (-8) 9)
            have b19777 := hb (x 1 6)
            have b19778 := hb (x 0 1 && x 0 7)
            have b19779 := hb (x (-1) 2 && x (-1) 8)
            have b19780 := hb (x (-2) 3 && x (-2) 9)
            have b19781 := hb (x (-3) 4 && x (-3) 10)
            have b19782 := hb (x (-4) 5 && x (-4) 11)
            have b19783 := hb (x (-5) 6 && x (-5) 12)
            have b19784 := hb (x (-6) 7 && x (-6) 13)
            have b19785 := hb (x (-7) 8 && x (-7) 14)
            clear * - r19775 b19776 b19777 b19778 b19779 b19780 b19781 b19782 b19783 b19784 b19785 g24 d19335 g66 g67 g68 g69 g70 g71 d19658
            omega
          have d19786 : (x (-7) 14).toNat = 1 := by
            have r19787 := hand2 (x (-7) 8) (x (-7) 14)
            have b19788 := hb (x (-7) 14)
            have b19789 := hb (x (-7) 8 && x (-7) 14)
            clear * - r19787 b19788 b19789 d19774
            omega
          have d19790 : (x (-8) 1).toNat = 0 := by
            have r19791 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b19792 := hb (x (-8) 1)
            have b19793 := hb (x (-7) 14)
            clear * - r19791 b19792 b19793 d19786
            omega
          have d19794 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
            have r19795 := hand1 (x (-8) 1) (x (-8) 14)
            have b19796 := hb (x (-8) 1)
            have b19797 := hb (x (-8) 1 && x (-8) 14)
            clear * - r19795 b19796 b19797 d19790
            omega
          have d19798 : (x (-8) 1 && x (-8) 12).toNat = 0 := by
            have r19799 := hand1 (x (-8) 1) (x (-8) 12)
            have b19800 := hb (x (-8) 1)
            have b19801 := hb (x (-8) 1 && x (-8) 12)
            clear * - r19799 b19800 b19801 d19790
            omega
          have d19802 : (x (-8) 1 && x (-8) 10).toNat = 0 := by
            have r19803 := hand1 (x (-8) 1) (x (-8) 10)
            have b19804 := hb (x (-8) 1)
            have b19805 := hb (x (-8) 1 && x (-8) 10)
            clear * - r19803 b19804 b19805 d19790
            omega
          have d19806 : (x (-8) 13).toNat = 0 := by
            have r19807 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
            have b19808 := hb (x (-8) 1)
            have b19809 := hb (x (-8) 13)
            clear * - r19807 b19808 b19809 d19790
            omega
          have d19810 : (x (-8) 3 && x (-8) 13).toNat = 0 := by
            have r19811 := hand2 (x (-8) 3) (x (-8) 13)
            have b19812 := hb (x (-8) 13)
            have b19813 := hb (x (-8) 3 && x (-8) 13)
            clear * - r19811 b19812 b19813 d19806
            omega
          have d19814 : (x (-8) 5).toNat = 0 := by
            have r19815 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
            have b19816 := hb (x (-8) 5)
            have b19817 := hb (x (-8) 13)
            clear * - r19815 b19816 b19817 d19806
            omega
          cases h19818 : x (-1) 8
          · have f19819 : (x (-1) 8).toNat = 0 := by rw [h19818]; rfl
            have d19820 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
              have r19821 := hand1 (x (-1) 8) (x (-1) 14)
              have b19822 := hb (x (-1) 8)
              have b19823 := hb (x (-1) 8 && x (-1) 14)
              clear * - r19821 b19822 b19823 f19819
              omega
            have d19824 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
              have r19825 := hand1 (x (-1) 8) (x (-1) 12)
              have b19826 := hb (x (-1) 8)
              have b19827 := hb (x (-1) 8 && x (-1) 12)
              clear * - r19825 b19826 b19827 f19819
              omega
            have d19828 : (x 7 7).toNat = 1 := by
              have r19829 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19830 := hb (x (-1) 8)
              have b19831 := hb (x 7 7)
              have b19832 := hb (x 6 1 && x 6 8)
              have b19833 := hb (x 5 2 && x 5 9)
              have b19834 := hb (x 4 3 && x 4 10)
              have b19835 := hb (x 3 4 && x 3 11)
              have b19836 := hb (x 2 5 && x 2 12)
              have b19837 := hb (x 1 6 && x 1 13)
              have b19838 := hb (x 0 7 && x 0 14)
              clear * - r19829 b19830 b19831 b19832 b19833 b19834 b19835 b19836 b19837 b19838 g95 g96 g97 g98 g99 g100 d19327 f19819
              omega
            have d19839 : (x 14 8).toNat = 0 := by
              have r19840 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19841 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e19842 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e19843 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e19844 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e19845 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e19846 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b19847 := hb (x 7 7)
              have b19848 := hb (x 8 6)
              have b19849 := hb (x 9 5)
              have b19850 := hb (x 10 4)
              have b19851 := hb (x 11 11)
              have b19852 := hb (x 12 10)
              have b19853 := hb (x 13 9)
              have b19854 := hb (x 14 8)
              clear * - r19840 e19841 e19842 e19843 e19844 e19845 e19846 b19847 b19848 b19849 b19850 b19851 b19852 b19853 b19854 d19828
              omega
            have d19855 : (x 13 9).toNat = 0 := by
              have r19856 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19857 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e19858 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e19859 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e19860 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e19861 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e19862 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b19863 := hb (x 7 7)
              have b19864 := hb (x 8 6)
              have b19865 := hb (x 9 5)
              have b19866 := hb (x 10 4)
              have b19867 := hb (x 11 11)
              have b19868 := hb (x 12 10)
              have b19869 := hb (x 13 9)
              have b19870 := hb (x 14 8)
              clear * - r19856 e19857 e19858 e19859 e19860 e19861 e19862 b19863 b19864 b19865 b19866 b19867 b19868 b19869 b19870 d19839 d19828
              omega
            have d19871 : (x 12 10).toNat = 0 := by
              have r19872 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19873 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e19874 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e19875 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e19876 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e19877 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e19878 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b19879 := hb (x 7 7)
              have b19880 := hb (x 8 6)
              have b19881 := hb (x 9 5)
              have b19882 := hb (x 10 4)
              have b19883 := hb (x 11 11)
              have b19884 := hb (x 12 10)
              have b19885 := hb (x 13 9)
              have b19886 := hb (x 14 8)
              clear * - r19872 e19873 e19874 e19875 e19876 e19877 e19878 b19879 b19880 b19881 b19882 b19883 b19884 b19885 b19886 d19839 d19855 d19828
              omega
            have d19887 : (x 12 1 && x 12 10).toNat = 0 := by
              have r19888 := hand2 (x 12 1) (x 12 10)
              have b19889 := hb (x 12 10)
              have b19890 := hb (x 12 1 && x 12 10)
              clear * - r19888 b19889 b19890 d19871
              omega
            have d19891 : (x 11 11).toNat = 0 := by
              have r19892 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19893 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e19894 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e19895 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e19896 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e19897 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e19898 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b19899 := hb (x 7 7)
              have b19900 := hb (x 8 6)
              have b19901 := hb (x 9 5)
              have b19902 := hb (x 10 4)
              have b19903 := hb (x 11 11)
              have b19904 := hb (x 12 10)
              have b19905 := hb (x 13 9)
              have b19906 := hb (x 14 8)
              clear * - r19892 e19893 e19894 e19895 e19896 e19897 e19898 b19899 b19900 b19901 b19902 b19903 b19904 b19905 b19906 d19839 d19855 d19871 d19828
              omega
            have d19907 : (x 11 1 && x 11 11).toNat = 0 := by
              have r19908 := hand2 (x 11 1) (x 11 11)
              have b19909 := hb (x 11 11)
              have b19910 := hb (x 11 1 && x 11 11)
              clear * - r19908 b19909 b19910 d19891
              omega
            have d19911 : (x 11 2 && x 11 11).toNat = 0 := by
              have r19912 := hand2 (x 11 2) (x 11 11)
              have b19913 := hb (x 11 11)
              have b19914 := hb (x 11 2 && x 11 11)
              clear * - r19912 b19913 b19914 d19891
              omega
            have d19915 : (x 10 4).toNat = 0 := by
              have r19916 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19917 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e19918 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e19919 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e19920 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e19921 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e19922 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b19923 := hb (x 7 7)
              have b19924 := hb (x 8 6)
              have b19925 := hb (x 9 5)
              have b19926 := hb (x 10 4)
              have b19927 := hb (x 11 11)
              have b19928 := hb (x 12 10)
              have b19929 := hb (x 13 9)
              have b19930 := hb (x 14 8)
              clear * - r19916 e19917 e19918 e19919 e19920 e19921 e19922 b19923 b19924 b19925 b19926 b19927 b19928 b19929 b19930 d19839 d19855 d19871 d19891 d19828
              omega
            have d19931 : (x 9 5).toNat = 0 := by
              have r19932 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19933 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e19934 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e19935 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e19936 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e19937 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e19938 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b19939 := hb (x 7 7)
              have b19940 := hb (x 8 6)
              have b19941 := hb (x 9 5)
              have b19942 := hb (x 10 4)
              have b19943 := hb (x 11 11)
              have b19944 := hb (x 12 10)
              have b19945 := hb (x 13 9)
              have b19946 := hb (x 14 8)
              clear * - r19932 e19933 e19934 e19935 e19936 e19937 e19938 b19939 b19940 b19941 b19942 b19943 b19944 b19945 b19946 d19839 d19855 d19871 d19891 d19915 d19828
              omega
            have d19947 : (x 8 6).toNat = 0 := by
              have r19948 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e19949 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
              have e19950 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
              have e19951 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
              have e19952 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
              have e19953 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
              have e19954 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
              have b19955 := hb (x 7 7)
              have b19956 := hb (x 8 6)
              have b19957 := hb (x 9 5)
              have b19958 := hb (x 10 4)
              have b19959 := hb (x 11 11)
              have b19960 := hb (x 12 10)
              have b19961 := hb (x 13 9)
              have b19962 := hb (x 14 8)
              clear * - r19948 e19949 e19950 e19951 e19952 e19953 e19954 b19955 b19956 b19957 b19958 b19959 b19960 b19961 b19962 d19839 d19855 d19871 d19891 d19915 d19931 d19828
              omega
            have d19963 : (x 7 1 && x 7 7).toNat = 1 := by
              have r19964 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19965 := hb (x (-1) 9)
              have b19966 := hb (x 8 6)
              have b19967 := hb (x 7 1 && x 7 7)
              have b19968 := hb (x 6 2 && x 6 8)
              have b19969 := hb (x 5 3 && x 5 9)
              have b19970 := hb (x 4 4 && x 4 10)
              have b19971 := hb (x 3 5 && x 3 11)
              have b19972 := hb (x 2 6 && x 2 12)
              have b19973 := hb (x 1 7 && x 1 13)
              have b19974 := hb (x 0 8 && x 0 14)
              clear * - r19964 b19965 b19966 b19967 b19968 b19969 b19970 b19971 b19972 b19973 b19974 d19947 g81 g82 g83 g84 g85 g86 g87 g9
              omega
            have d19975 : (x 7 1).toNat = 1 := by
              have r19976 := hand1 (x 7 1) (x 7 7)
              have b19977 := hb (x 7 1)
              have b19978 := hb (x 7 1 && x 7 7)
              clear * - r19976 b19977 b19978 d19963
              omega
            have d19979 : (x 8 14).toNat = 0 := by
              have r19980 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b19981 := hb (x 7 1)
              have b19982 := hb (x 8 14)
              clear * - r19980 b19981 b19982 d19975
              omega
            have d19983 : (x 8 3 && x 8 14).toNat = 0 := by
              have r19984 := hand2 (x 8 3) (x 8 14)
              have b19985 := hb (x 8 14)
              have b19986 := hb (x 8 3 && x 8 14)
              clear * - r19984 b19985 b19986 d19979
              omega
            have d19987 : (x 8 4 && x 8 14).toNat = 0 := by
              have r19988 := hand2 (x 8 4) (x 8 14)
              have b19989 := hb (x 8 14)
              have b19990 := hb (x 8 4 && x 8 14)
              clear * - r19988 b19989 b19990 d19979
              omega
            have d19991 : (x 8 5 && x 8 14).toNat = 0 := by
              have r19992 := hand2 (x 8 5) (x 8 14)
              have b19993 := hb (x 8 14)
              have b19994 := hb (x 8 5 && x 8 14)
              clear * - r19992 b19993 b19994 d19979
              omega
            have d19995 : (x 8 2).toNat = 0 := by
              have r19996 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
              have b19997 := hb (x 8 2)
              have b19998 := hb (x 8 14)
              clear * - r19996 b19997 b19998 d19979
              omega
            have d19999 : (x 8 10).toNat = 0 := by
              have r20000 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
              have b20001 := hb (x 8 2)
              have b20002 := hb (x 8 10)
              clear * - r20000 b20001 b20002 d19995
              omega
            cases h20003 : x (-1) 12
            · have f20004 : (x (-1) 12).toNat = 0 := by rw [h20003]; rfl
              cases h20005 : x (-1) 14
              · have f20006 : (x (-1) 14).toNat = 0 := by rw [h20005]; rfl
                have d20007 : (x (-2) 1).toNat = 1 := by
                  have r20008 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20009 := hb (x (-2) 1)
                  have b20010 := hb (x (-1) 14)
                  clear * - r20008 b20009 b20010 f20006
                  omega
                cases h20011 : x 2 6
                · have f20012 : (x 2 6).toNat = 0 := by rw [h20011]; rfl
                  cases h20013 : x (-2) 9
                  · have f20014 : (x (-2) 9).toNat = 0 := by rw [h20013]; rfl
                    have d20015 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
                      have r20016 := hand1 (x (-2) 9) (x (-2) 13)
                      have b20017 := hb (x (-2) 9)
                      have b20018 := hb (x (-2) 9 && x (-2) 13)
                      clear * - r20016 b20017 b20018 f20014
                      omega
                    cases h20019 : x (-2) 13
                    · have f20020 : (x (-2) 13).toNat = 0 := by rw [h20019]; rfl
                      cases h20021 : x 2 7
                      · have f20022 : (x 2 7).toNat = 0 := by rw [h20021]; rfl
                        cases h20023 : x (-2) 8
                        · have f20024 : (x (-2) 8).toNat = 0 := by rw [h20023]; rfl
                          cases h20025 : x (-2) 12
                          · have f20026 : (x (-2) 12).toNat = 0 := by rw [h20025]; rfl
                            cases h20027 : x (-2) 14
                            · have f20028 : (x (-2) 14).toNat = 0 := by rw [h20027]; rfl
                              have d20029 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                                have r20030 := hand2 (x (-2) 1) (x (-2) 14)
                                have b20031 := hb (x (-2) 14)
                                have b20032 := hb (x (-2) 1 && x (-2) 14)
                                clear * - r20030 b20031 b20032 f20028
                                omega
                              have d20033 : (x (-3) 2).toNat = 1 := by
                                have r20034 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have b20035 := hb (x (-3) 2)
                                have b20036 := hb (x (-1) 13)
                                have b20037 := hb (x (-2) 1 && x (-2) 14)
                                clear * - r20034 b20035 b20036 b20037 g12 d20029
                                omega
                              have d20038 : (x (-3) 14).toNat = 1 := by
                                have r20039 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                                have b20040 := hb (x (-3) 2)
                                have b20041 := hb (x (-3) 14)
                                clear * - r20039 b20040 b20041 d20033
                                omega
                              have d20042 : (x (-4) 3).toNat = 0 := by
                                have r20043 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have e20044 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                                have e20045 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                                have b20046 := hb (x (-4) 3)
                                have b20047 := hb (x (-3) 2)
                                have b20048 := hb (x (-2) 13)
                                have b20049 := hb (x (-1) 12)
                                clear * - r20043 e20044 e20045 b20046 b20047 b20048 b20049 f20004 f20020 d20033
                                omega
                              have d20050 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                                have r20051 := hand1 (x (-4) 3) (x (-4) 12)
                                have b20052 := hb (x (-4) 3)
                                have b20053 := hb (x (-4) 3 && x (-4) 12)
                                clear * - r20051 b20052 b20053 d20042
                                omega
                              have d20054 : (x (-4) 11).toNat = 0 := by
                                have r20055 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                                have b20056 := hb (x (-4) 3)
                                have b20057 := hb (x (-4) 11)
                                clear * - r20055 b20056 b20057 d20042
                                omega
                              have r20058 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20059 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20060 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20061 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                              have e20062 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                              have e20063 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                              have e20064 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                              have e20065 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                              have e20066 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                              have r20067 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20068 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
                              have e20069 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
                              have e20070 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
                              have e20071 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
                              have e20072 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
                              have e20073 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
                              have r20074 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20075 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                              have e20076 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                              have r20077 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20078 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                              have e20079 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                              have r20080 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20081 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20082 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
                              have e20083 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
                              have r20084 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20085 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20086 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20087 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20088 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                              have r20089 := hand2 (x 5 2) (x 5 6)
                              have r20090 := hand2 (x 4 3) (x 4 7)
                              have r20091 := hand2 (x 6 1) (x 6 7)
                              have r20092 := hand1 (x (-5) 4) (x (-5) 13)
                              have r20093 := hand1 (x (-6) 5) (x (-6) 14)
                              have r20094 := hand2 (x 10 1) (x 10 11)
                              have r20095 := hand1 (x 9 2) (x 9 12)
                              have r20096 := hand1 (x 8 3) (x 8 13)
                              have r20097 := hand2 (x 7 4) (x 7 14)
                              have r20098 := hand1 (x 10 1) (x 10 12)
                              have r20099 := hand1 (x 9 2) (x 9 13)
                              linarith only [r20058, r20059, r20060, e20061, e20062, e20063, e20064, e20065, e20066, r20067, e20068, e20069, e20070, e20071, e20072, e20073, r20074, e20075, e20076, r20077, e20078, e20079, r20080, r20081, e20082, e20083, r20084, r20085, r20086, r20087, r20088, r20089, r20090, r20091, r20092, r20093, r20094, r20095, r20096, r20097, r20098, r20099, d19786, d20054, d20038, f20014, f20020, f19819, g9, f20004, g15, g18, g24, g26, g30, g31, g34, g35, d19891, g55, g56, g57, d19339, d19824, d20015, g76, g77, g78, g79, g80, d19331, d19820, g101, g102, d20050, d19983]
                            · have f20175 : (x (-2) 14).toNat = 1 := by rw [h20027]; rfl
                              have d20176 : (x (-3) 1).toNat = 0 := by
                                have r20177 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have b20178 := hb (x (-3) 1)
                                have b20179 := hb (x (-2) 14)
                                clear * - r20177 b20178 b20179 f20175
                                omega
                              have d20180 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                                have r20181 := hand1 (x (-3) 1) (x (-3) 14)
                                have b20182 := hb (x (-3) 1)
                                have b20183 := hb (x (-3) 1 && x (-3) 14)
                                clear * - r20181 b20182 b20183 d20176
                                omega
                              have d20184 : (x (-4) 2).toNat = 1 := by
                                have r20185 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have b20186 := hb (x (-4) 2)
                                have b20187 := hb (x (-2) 13)
                                have b20188 := hb (x (-3) 1 && x (-3) 14)
                                clear * - r20185 b20186 b20187 b20188 f20020 d20180
                                omega
                              have d20189 : (x (-4) 14).toNat = 1 := by
                                have r20190 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                                have b20191 := hb (x (-4) 2)
                                have b20192 := hb (x (-4) 14)
                                clear * - r20190 b20191 b20192 d20184
                                omega
                              have d20193 : (x (-5) 1).toNat = 0 := by
                                have r20194 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                                have b20195 := hb (x (-5) 1)
                                have b20196 := hb (x (-4) 14)
                                clear * - r20194 b20195 b20196 d20189
                                omega
                              have d20197 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
                                have r20198 := hand1 (x (-5) 1) (x (-5) 14)
                                have b20199 := hb (x (-5) 1)
                                have b20200 := hb (x (-5) 1 && x (-5) 14)
                                clear * - r20198 b20199 b20200 d20193
                                omega
                              have d20201 : (x (-5) 13).toNat = 0 := by
                                have r20202 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                                have b20203 := hb (x (-5) 1)
                                have b20204 := hb (x (-5) 13)
                                clear * - r20202 b20203 b20204 d20193
                                omega
                              have d20205 : (x (-5) 9).toNat = 0 := by
                                have r20206 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
                                have b20207 := hb (x (-5) 1)
                                have b20208 := hb (x (-5) 9)
                                clear * - r20206 b20207 b20208 d20193
                                omega
                              have r20209 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20210 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20211 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20212 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
                              have e20213 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
                              have e20214 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
                              have e20215 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
                              have e20216 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
                              have e20217 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
                              have r20218 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20219 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
                              have e20220 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
                              have e20221 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
                              have e20222 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
                              have e20223 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
                              have e20224 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
                              have r20225 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20226 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                              have e20227 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                              have e20228 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                              have e20229 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                              have e20230 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                              have e20231 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                              have r20232 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20233 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                              have e20234 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                              have r20235 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20236 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                              have e20237 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                              have r20238 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20239 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                              have e20240 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                              have r20241 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20242 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                              have e20243 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                              have r20244 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20245 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                              have e20246 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                              have r20247 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20248 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20249 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                              have e20250 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                              have r20251 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20252 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                              have e20253 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                              have r20254 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20255 : 1 ≤ (x (-7) 9).toNat + (x (-8) 1 && x (-8) 10).toNat + (x (-9) 2 && x (-9) 11).toNat + (x (-10) 3 && x (-10) 12).toNat + (x (-11) 4 && x (-11) 13).toNat + (x (-12) 5 && x (-12) 14).toNat + (x (-13) 6).toNat := by have q := hcov9 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20256 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20257 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20258 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20259 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20260 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20261 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have r20262 : (x (-7) 9).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp9 (-7))
                              have r20263 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                              have r20264 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
                              have r20265 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
                              have r20266 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
                              have r20267 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
                              have r20268 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
                              have r20269 := hand1 (x (-5) 8) (x (-5) 12)
                              have r20270 := hand1 (x (-6) 9) (x (-6) 13)
                              have r20271 := hand2 (x 6 2) (x 6 6)
                              have r20272 := hand2 (x 5 3) (x 5 7)
                              have r20273 := hand1 (x (-6) 8) (x (-6) 14)
                              have r20274 := hand2 (x (-9) 2) (x (-9) 11)
                              have r20275 := hand1 (x (-10) 3) (x (-10) 12)
                              have r20276 := hand2 (x (-6) 1) (x (-6) 10)
                              have r20277 := hand2 (x (-7) 2) (x (-7) 11)
                              have r20278 := hand2 (x (-8) 3) (x (-8) 12)
                              have r20279 := hand1 (x (-9) 4) (x (-9) 13)
                              have r20280 := hand1 (x (-10) 5) (x (-10) 14)
                              have r20281 := hand2 (x (-6) 1) (x (-6) 11)
                              have r20282 := hand2 (x (-7) 2) (x (-7) 12)
                              have r20283 := hand1 (x (-9) 4) (x (-9) 14)
                              have r20284 := hand1 (x 10 2) (x 10 12)
                              have r20285 := hand1 (x 9 3) (x 9 13)
                              have r20286 := hand2 (x (-9) 2) (x (-9) 13)
                              have r20287 := hand1 (x (-10) 3) (x (-10) 14)
                              linarith only [r20209, r20210, r20211, e20212, e20213, e20214, e20215, e20216, e20217, r20218, e20219, e20220, e20221, e20222, e20223, e20224, r20225, e20226, e20227, e20228, e20229, e20230, e20231, r20232, e20233, e20234, r20235, e20236, e20237, r20238, e20239, e20240, r20241, e20242, e20243, r20244, e20245, e20246, r20247, r20248, e20249, e20250, r20251, e20252, e20253, r20254, r20255, r20256, r20257, r20258, r20259, r20260, r20261, r20262, r20263, r20264, r20265, r20266, r20267, r20268, r20269, r20270, r20271, r20272, r20273, r20274, r20275, r20276, r20277, r20278, r20279, r20280, r20281, r20282, r20283, r20284, r20285, r20286, r20287, d19758, d19718, d19806, d20205, d20201, g2, g4, f20175, g9, g12, g16, g19, f19646, g27, g30, f20012, g32, g34, g36, g38, d19975, d19871, g46, d19343, g47, g48, g49, g50, g58, g59, g60, g61, g62, g63, d19635, g72, g73, g74, g75, d19609, d19629, d19802, d19734, d19754, d19810, d19907, d19987, d19798, d19794, d20197]
                          · have f20411 : (x (-2) 12).toNat = 1 := by rw [h20025]; rfl
                            have d20412 : (x (-3) 13).toNat = 0 := by
                              have r20413 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20414 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                              have e20415 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                              have b20416 := hb (x (-5) 3)
                              have b20417 := hb (x (-4) 2)
                              have b20418 := hb (x (-3) 13)
                              have b20419 := hb (x (-2) 12)
                              clear * - r20413 e20414 e20415 b20416 b20417 b20418 b20419 f20411
                              omega
                            have d20420 : (x (-4) 2).toNat = 0 := by
                              have r20421 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20422 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                              have e20423 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                              have b20424 := hb (x (-5) 3)
                              have b20425 := hb (x (-4) 2)
                              have b20426 := hb (x (-3) 13)
                              have b20427 := hb (x (-2) 12)
                              clear * - r20421 e20422 e20423 b20424 b20425 b20426 b20427 f20411 d20412
                              omega
                            have d20428 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
                              have r20429 := hand1 (x (-4) 2) (x (-4) 13)
                              have b20430 := hb (x (-4) 2)
                              have b20431 := hb (x (-4) 2 && x (-4) 13)
                              clear * - r20429 b20430 b20431 d20420
                              omega
                            have d20432 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
                              have r20433 := hand1 (x (-4) 2) (x (-4) 12)
                              have b20434 := hb (x (-4) 2)
                              have b20435 := hb (x (-4) 2 && x (-4) 12)
                              clear * - r20433 b20434 b20435 d20420
                              omega
                            have d20436 : (x (-3) 1 && x (-3) 14).toNat = 1 := by
                              have r20437 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b20438 := hb (x (-4) 2)
                              have b20439 := hb (x (-2) 13)
                              have b20440 := hb (x (-3) 1 && x (-3) 14)
                              clear * - r20437 b20438 b20439 b20440 f20020 d20420
                              omega
                            have d20441 : (x (-3) 14).toNat = 1 := by
                              have r20442 := hand2 (x (-3) 1) (x (-3) 14)
                              have b20443 := hb (x (-3) 14)
                              have b20444 := hb (x (-3) 1 && x (-3) 14)
                              clear * - r20442 b20443 b20444 d20436
                              omega
                            have d20445 : (x (-4) 1).toNat = 0 := by
                              have r20446 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b20447 := hb (x (-4) 1)
                              have b20448 := hb (x (-3) 14)
                              clear * - r20446 b20447 b20448 d20441
                              omega
                            have d20449 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
                              have r20450 := hand1 (x (-4) 1) (x (-4) 14)
                              have b20451 := hb (x (-4) 1)
                              have b20452 := hb (x (-4) 1 && x (-4) 14)
                              clear * - r20450 b20451 b20452 d20445
                              omega
                            have d20453 : (x (-5) 2).toNat = 1 := by
                              have r20454 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b20455 := hb (x (-5) 2)
                              have b20456 := hb (x (-3) 13)
                              have b20457 := hb (x (-4) 1 && x (-4) 14)
                              clear * - r20454 b20455 b20456 b20457 d20412 d20449
                              omega
                            have d20458 : (x (-5) 14).toNat = 1 := by
                              have r20459 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
                              have b20460 := hb (x (-5) 2)
                              have b20461 := hb (x (-5) 14)
                              clear * - r20459 b20460 b20461 d20453
                              omega
                            have d20462 : (x (-6) 1).toNat = 0 := by
                              have r20463 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b20464 := hb (x (-6) 1)
                              have b20465 := hb (x (-5) 14)
                              clear * - r20463 b20464 b20465 d20458
                              omega
                            have d20466 : (x (-6) 13).toNat = 0 := by
                              have r20467 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
                              have b20468 := hb (x (-6) 1)
                              have b20469 := hb (x (-6) 13)
                              clear * - r20467 b20468 b20469 d20462
                              omega
                            have d20470 : (x (-4) 13).toNat = 0 := by
                              have r20471 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                              have b20472 := hb (x (-4) 1)
                              have b20473 := hb (x (-4) 13)
                              clear * - r20471 b20472 b20473 d20445
                              omega
                            have d20474 : (x (-5) 3).toNat = 0 := by
                              have r20475 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20476 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                              have e20477 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                              have b20478 := hb (x (-5) 3)
                              have b20479 := hb (x (-4) 2)
                              have b20480 := hb (x (-3) 13)
                              have b20481 := hb (x (-2) 12)
                              clear * - r20475 e20476 e20477 b20478 b20479 b20480 b20481 f20411 d20412 d20420
                              omega
                            have d20482 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
                              have r20483 := hand1 (x (-5) 3) (x (-5) 14)
                              have b20484 := hb (x (-5) 3)
                              have b20485 := hb (x (-5) 3 && x (-5) 14)
                              clear * - r20483 b20484 b20485 d20474
                              omega
                            have d20486 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
                              have r20487 := hand1 (x (-5) 3) (x (-5) 13)
                              have b20488 := hb (x (-5) 3)
                              have b20489 := hb (x (-5) 3 && x (-5) 13)
                              clear * - r20487 b20488 b20489 d20474
                              omega
                            have d20490 : (x (-3) 12).toNat = 0 := by
                              have r20491 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20492 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                              have e20493 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                              have b20494 := hb (x (-6) 3)
                              have b20495 := hb (x (-5) 2)
                              have b20496 := hb (x (-4) 13)
                              have b20497 := hb (x (-3) 12)
                              clear * - r20491 e20492 e20493 b20494 b20495 b20496 b20497 d20470 d20453
                              omega
                            have d20498 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
                              have r20499 := hand2 (x (-3) 1) (x (-3) 12)
                              have b20500 := hb (x (-3) 12)
                              have b20501 := hb (x (-3) 1 && x (-3) 12)
                              clear * - r20499 b20500 b20501 d20490
                              omega
                            have d20502 : (x (-6) 4).toNat = 1 := by
                              have r20503 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b20504 := hb (x (-6) 4)
                              have b20505 := hb (x (-2) 11)
                              have b20506 := hb (x (-3) 1 && x (-3) 12)
                              have b20507 := hb (x (-4) 2 && x (-4) 13)
                              have b20508 := hb (x (-5) 3 && x (-5) 14)
                              clear * - r20503 b20504 b20505 b20506 b20507 b20508 g5 d20498 d20428 d20482
                              omega
                            have d20509 : (x (-6) 12).toNat = 1 := by
                              have r20510 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                              have b20511 := hb (x (-6) 4)
                              have b20512 := hb (x (-6) 12)
                              clear * - r20510 b20511 b20512 d20502
                              omega
                            have d20513 : (x (-7) 13).toNat = 0 := by
                              have r20514 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20515 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                              have e20516 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                              have b20517 := hb (x (-9) 3)
                              have b20518 := hb (x (-8) 2)
                              have b20519 := hb (x (-7) 13)
                              have b20520 := hb (x (-6) 12)
                              clear * - r20514 e20515 e20516 b20517 b20518 b20519 b20520 d20509
                              omega
                            have d20521 : (x (-7) 5).toNat = 0 := by
                              have r20522 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
                              have b20523 := hb (x (-7) 5)
                              have b20524 := hb (x (-7) 13)
                              clear * - r20522 b20523 b20524 d20513
                              omega
                            have d20525 : (x (-8) 2).toNat = 0 := by
                              have r20526 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have e20527 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                              have e20528 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                              have b20529 := hb (x (-9) 3)
                              have b20530 := hb (x (-8) 2)
                              have b20531 := hb (x (-7) 13)
                              have b20532 := hb (x (-6) 12)
                              clear * - r20526 e20527 e20528 b20529 b20530 b20531 b20532 d20509 d20513
                              omega
                            have d20533 : (x (-7) 1 && x (-7) 14).toNat = 1 := by
                              have r20534 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b20535 := hb (x (-8) 2)
                              have b20536 := hb (x (-6) 13)
                              have b20537 := hb (x (-7) 1 && x (-7) 14)
                              clear * - r20534 b20535 b20536 b20537 d20466 d20525
                              omega
                            have d20538 : (x (-7) 1).toNat = 1 := by
                              have r20539 := hand1 (x (-7) 1) (x (-7) 14)
                              have b20540 := hb (x (-7) 1)
                              have b20541 := hb (x (-7) 1 && x (-7) 14)
                              clear * - r20539 b20540 b20541 d20533
                              omega
                            have d20542 : (x (-6) 14).toNat = 0 := by
                              have r20543 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                              have b20544 := hb (x (-7) 1)
                              have b20545 := hb (x (-6) 14)
                              clear * - r20543 b20544 b20545 d20538
                              omega
                            have d20546 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
                              have r20547 := hand2 (x (-6) 4) (x (-6) 14)
                              have b20548 := hb (x (-6) 14)
                              have b20549 := hb (x (-6) 4 && x (-6) 14)
                              clear * - r20547 b20548 b20549 d20542
                              omega
                            have r20550 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have b20551 := hb (x (-7) 5)
                            have b20552 := hb (x (-2) 10)
                            have b20553 := hb (x (-3) 1 && x (-3) 11)
                            have b20554 := hb (x (-4) 2 && x (-4) 12)
                            have b20555 := hb (x (-5) 3 && x (-5) 13)
                            have b20556 := hb (x (-6) 4 && x (-6) 14)
                            linarith only [r20550, b20551, b20552, b20553, b20554, b20555, b20556, g4, g109, d20432, d20486, d20546, d20521]
                        · have f20557 : (x (-2) 8).toNat = 1 := by rw [h20023]; rfl
                          have d20558 : (x (-3) 9).toNat = 0 := by
                            have r20559 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e20560 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e20561 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e20562 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e20563 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e20564 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e20565 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b20566 := hb (x (-9) 7)
                            have b20567 := hb (x (-8) 6)
                            have b20568 := hb (x (-7) 5)
                            have b20569 := hb (x (-6) 4)
                            have b20570 := hb (x (-5) 11)
                            have b20571 := hb (x (-4) 10)
                            have b20572 := hb (x (-3) 9)
                            have b20573 := hb (x (-2) 8)
                            clear * - r20559 e20560 e20561 e20562 e20563 e20564 e20565 b20566 b20567 b20568 b20569 b20570 b20571 b20572 b20573 f20557
                            omega
                          have d20574 : (x (-4) 10).toNat = 0 := by
                            have r20575 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e20576 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e20577 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e20578 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e20579 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e20580 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e20581 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b20582 := hb (x (-9) 7)
                            have b20583 := hb (x (-8) 6)
                            have b20584 := hb (x (-7) 5)
                            have b20585 := hb (x (-6) 4)
                            have b20586 := hb (x (-5) 11)
                            have b20587 := hb (x (-4) 10)
                            have b20588 := hb (x (-3) 9)
                            have b20589 := hb (x (-2) 8)
                            clear * - r20575 e20576 e20577 e20578 e20579 e20580 e20581 b20582 b20583 b20584 b20585 b20586 b20587 b20588 b20589 f20557 d20558
                            omega
                          have d20590 : (x (-5) 11).toNat = 0 := by
                            have r20591 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e20592 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e20593 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e20594 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e20595 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e20596 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e20597 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b20598 := hb (x (-9) 7)
                            have b20599 := hb (x (-8) 6)
                            have b20600 := hb (x (-7) 5)
                            have b20601 := hb (x (-6) 4)
                            have b20602 := hb (x (-5) 11)
                            have b20603 := hb (x (-4) 10)
                            have b20604 := hb (x (-3) 9)
                            have b20605 := hb (x (-2) 8)
                            clear * - r20591 e20592 e20593 e20594 e20595 e20596 e20597 b20598 b20599 b20600 b20601 b20602 b20603 b20604 b20605 f20557 d20558 d20574
                            omega
                          have d20606 : (x (-5) 1 && x (-5) 11).toNat = 0 := by
                            have r20607 := hand2 (x (-5) 1) (x (-5) 11)
                            have b20608 := hb (x (-5) 11)
                            have b20609 := hb (x (-5) 1 && x (-5) 11)
                            clear * - r20607 b20608 b20609 d20590
                            omega
                          have d20610 : (x (-6) 4).toNat = 0 := by
                            have r20611 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e20612 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e20613 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e20614 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e20615 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e20616 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e20617 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b20618 := hb (x (-9) 7)
                            have b20619 := hb (x (-8) 6)
                            have b20620 := hb (x (-7) 5)
                            have b20621 := hb (x (-6) 4)
                            have b20622 := hb (x (-5) 11)
                            have b20623 := hb (x (-4) 10)
                            have b20624 := hb (x (-3) 9)
                            have b20625 := hb (x (-2) 8)
                            clear * - r20611 e20612 e20613 e20614 e20615 e20616 e20617 b20618 b20619 b20620 b20621 b20622 b20623 b20624 b20625 f20557 d20558 d20574 d20590
                            omega
                          have d20626 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
                            have r20627 := hand1 (x (-6) 4) (x (-6) 14)
                            have b20628 := hb (x (-6) 4)
                            have b20629 := hb (x (-6) 4 && x (-6) 14)
                            clear * - r20627 b20628 b20629 d20610
                            omega
                          have d20630 : (x (-7) 5).toNat = 0 := by
                            have r20631 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                            have e20632 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                            have e20633 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                            have e20634 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                            have e20635 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                            have e20636 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                            have e20637 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                            have b20638 := hb (x (-9) 7)
                            have b20639 := hb (x (-8) 6)
                            have b20640 := hb (x (-7) 5)
                            have b20641 := hb (x (-6) 4)
                            have b20642 := hb (x (-5) 11)
                            have b20643 := hb (x (-4) 10)
                            have b20644 := hb (x (-3) 9)
                            have b20645 := hb (x (-2) 8)
                            clear * - r20631 e20632 e20633 e20634 e20635 e20636 e20637 b20638 b20639 b20640 b20641 b20642 b20643 b20644 b20645 f20557 d20558 d20574 d20590 d20610
                            omega
                          have r20646 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r20647 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20648 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
                          have e20649 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
                          have e20650 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
                          have e20651 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
                          have e20652 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
                          have e20653 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
                          have r20654 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20655 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
                          have e20656 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
                          have e20657 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
                          have e20658 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
                          have e20659 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
                          have e20660 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
                          have r20661 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20662 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                          have e20663 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                          have r20664 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20665 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                          have e20666 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                          have r20667 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20668 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                          have e20669 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                          have r20670 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20671 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
                          have e20672 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
                          have r20673 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r20674 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r20675 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r20676 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r20677 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have r20678 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
                          have r20679 := hand1 (x (-5) 8) (x (-5) 12)
                          have r20680 := hand1 (x (-6) 9) (x (-6) 13)
                          have r20681 := hand2 (x (-6) 1) (x (-6) 10)
                          have r20682 := hand2 (x (-7) 2) (x (-7) 11)
                          have r20683 := hand2 (x (-8) 3) (x (-8) 12)
                          have r20684 := hand1 (x (-9) 4) (x (-9) 13)
                          have r20685 := hand1 (x (-10) 5) (x (-10) 14)
                          have r20686 := hand1 (x (-6) 2) (x (-6) 12)
                          have r20687 := hand1 (x (-7) 3) (x (-7) 13)
                          have r20688 := hand1 (x (-8) 4) (x (-8) 14)
                          have r20689 := hand2 (x (-8) 4) (x (-8) 14)
                          have r20690 := hand2 (x (-4) 2) (x (-4) 12)
                          have r20691 := hand2 (x (-5) 3) (x (-5) 13)
                          have r20692 := hand2 (x (-9) 2) (x (-9) 13)
                          have r20693 := hand1 (x (-10) 3) (x (-10) 14)
                          linarith only [r20646, r20647, e20648, e20649, e20650, e20651, e20652, e20653, r20654, e20655, e20656, e20657, e20658, e20659, e20660, r20661, e20662, e20663, r20664, e20665, e20666, r20667, e20668, e20669, r20670, e20671, e20672, r20673, r20674, r20675, r20676, r20677, r20678, r20679, r20680, r20681, r20682, r20683, r20684, r20685, r20686, r20687, r20688, r20689, r20690, r20691, r20692, r20693, d19718, d19806, d20630, d20590, d20574, d20558, f20557, g4, g8, g14, g23, g29, g30, g34, g46, d19343, g47, g48, g49, g50, d20606, g109, d20626, d19798, d19794]
                      · have f20766 : (x 2 7).toNat = 1 := by rw [h20021]; rfl
                        have d20767 : (x 9 8).toNat = 0 := by
                          have r20768 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20769 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e20770 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e20771 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e20772 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e20773 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e20774 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b20775 := hb (x 2 7)
                          have b20776 := hb (x 3 6)
                          have b20777 := hb (x 4 5)
                          have b20778 := hb (x 5 4)
                          have b20779 := hb (x 6 11)
                          have b20780 := hb (x 7 10)
                          have b20781 := hb (x 8 9)
                          have b20782 := hb (x 9 8)
                          clear * - r20768 e20769 e20770 e20771 e20772 e20773 e20774 b20775 b20776 b20777 b20778 b20779 b20780 b20781 b20782 f20766
                          omega
                        have d20783 : (x 8 9).toNat = 0 := by
                          have r20784 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20785 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e20786 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e20787 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e20788 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e20789 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e20790 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b20791 := hb (x 2 7)
                          have b20792 := hb (x 3 6)
                          have b20793 := hb (x 4 5)
                          have b20794 := hb (x 5 4)
                          have b20795 := hb (x 6 11)
                          have b20796 := hb (x 7 10)
                          have b20797 := hb (x 8 9)
                          have b20798 := hb (x 9 8)
                          clear * - r20784 e20785 e20786 e20787 e20788 e20789 e20790 b20791 b20792 b20793 b20794 b20795 b20796 b20797 b20798 d20767 f20766
                          omega
                        have d20799 : (x 7 10).toNat = 0 := by
                          have r20800 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20801 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e20802 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e20803 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e20804 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e20805 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e20806 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b20807 := hb (x 2 7)
                          have b20808 := hb (x 3 6)
                          have b20809 := hb (x 4 5)
                          have b20810 := hb (x 5 4)
                          have b20811 := hb (x 6 11)
                          have b20812 := hb (x 7 10)
                          have b20813 := hb (x 8 9)
                          have b20814 := hb (x 9 8)
                          clear * - r20800 e20801 e20802 e20803 e20804 e20805 e20806 b20807 b20808 b20809 b20810 b20811 b20812 b20813 b20814 d20767 d20783 f20766
                          omega
                        have d20815 : (x 6 11).toNat = 0 := by
                          have r20816 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20817 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e20818 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e20819 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e20820 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e20821 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e20822 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b20823 := hb (x 2 7)
                          have b20824 := hb (x 3 6)
                          have b20825 := hb (x 4 5)
                          have b20826 := hb (x 5 4)
                          have b20827 := hb (x 6 11)
                          have b20828 := hb (x 7 10)
                          have b20829 := hb (x 8 9)
                          have b20830 := hb (x 9 8)
                          clear * - r20816 e20817 e20818 e20819 e20820 e20821 e20822 b20823 b20824 b20825 b20826 b20827 b20828 b20829 b20830 d20767 d20783 d20799 f20766
                          omega
                        have d20831 : (x 5 4).toNat = 0 := by
                          have r20832 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20833 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e20834 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e20835 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e20836 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e20837 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e20838 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b20839 := hb (x 2 7)
                          have b20840 := hb (x 3 6)
                          have b20841 := hb (x 4 5)
                          have b20842 := hb (x 5 4)
                          have b20843 := hb (x 6 11)
                          have b20844 := hb (x 7 10)
                          have b20845 := hb (x 8 9)
                          have b20846 := hb (x 9 8)
                          clear * - r20832 e20833 e20834 e20835 e20836 e20837 e20838 b20839 b20840 b20841 b20842 b20843 b20844 b20845 b20846 d20767 d20783 d20799 d20815 f20766
                          omega
                        have d20847 : (x 4 5).toNat = 0 := by
                          have r20848 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20849 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e20850 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e20851 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e20852 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e20853 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e20854 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b20855 := hb (x 2 7)
                          have b20856 := hb (x 3 6)
                          have b20857 := hb (x 4 5)
                          have b20858 := hb (x 5 4)
                          have b20859 := hb (x 6 11)
                          have b20860 := hb (x 7 10)
                          have b20861 := hb (x 8 9)
                          have b20862 := hb (x 9 8)
                          clear * - r20848 e20849 e20850 e20851 e20852 e20853 e20854 b20855 b20856 b20857 b20858 b20859 b20860 b20861 b20862 d20767 d20783 d20799 d20815 d20831 f20766
                          omega
                        have d20863 : (x 3 6).toNat = 0 := by
                          have r20864 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                          have e20865 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                          have e20866 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                          have e20867 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                          have e20868 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                          have e20869 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                          have e20870 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                          have b20871 := hb (x 2 7)
                          have b20872 := hb (x 3 6)
                          have b20873 := hb (x 4 5)
                          have b20874 := hb (x 5 4)
                          have b20875 := hb (x 6 11)
                          have b20876 := hb (x 7 10)
                          have b20877 := hb (x 8 9)
                          have b20878 := hb (x 9 8)
                          clear * - r20864 e20865 e20866 e20867 e20868 e20869 e20870 b20871 b20872 b20873 b20874 b20875 b20876 b20877 b20878 d20767 d20783 d20799 d20815 d20831 d20847 f20766
                          omega
                        have r20879 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r20880 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r20881 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20882 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                        have e20883 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                        have e20884 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                        have e20885 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                        have e20886 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                        have e20887 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                        have r20888 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20889 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                        have e20890 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                        have r20891 : 1 ≤ (x (-1) 2).toNat + (x (-2) 1 && x (-2) 3).toNat + (x (-3) 2 && x (-3) 4).toNat + (x (-4) 3 && x (-4) 5).toNat + (x (-5) 4 && x (-5) 6).toNat + (x (-6) 5 && x (-6) 7).toNat + (x (-7) 6 && x (-7) 8).toNat + (x (-8) 7 && x (-8) 9).toNat + (x (-9) 8 && x (-9) 10).toNat + (x (-10) 9 && x (-10) 11).toNat + (x (-11) 10 && x (-11) 12).toNat + (x (-12) 11 && x (-12) 13).toNat + (x (-13) 12 && x (-13) 14).toNat + (x (-14) 13).toNat := by have q := hcov2 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r20892 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20893 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                        have e20894 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                        have r20895 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r20896 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have r20897 := hand1 (x (-7) 6) (x (-7) 8)
                        have r20898 := hand1 (x (-11) 10) (x (-11) 12)
                        have r20899 := hand1 (x (-12) 11) (x (-12) 13)
                        have r20900 := hand1 (x (-13) 12) (x (-13) 14)
                        have r20901 := hand2 (x 6 2) (x 6 6)
                        have r20902 := hand2 (x 5 3) (x 5 7)
                        have r20903 := hand2 (x (-3) 2) (x (-3) 12)
                        have r20904 := hand2 (x (-4) 3) (x (-4) 13)
                        have r20905 := hand2 (x (-5) 4) (x (-5) 14)
                        have r20906 := hand1 (x 8 1) (x 8 12)
                        have r20907 := hand1 (x 7 2) (x 7 13)
                        have r20908 := hand1 (x 6 3) (x 6 14)
                        linarith only [r20879, r20880, r20881, e20882, e20883, e20884, e20885, e20886, e20887, r20888, e20889, e20890, r20891, r20892, e20893, e20894, r20895, r20896, r20897, r20898, r20899, r20900, r20901, r20902, r20903, r20904, r20905, r20906, r20907, r20908, g2, d20007, g4, g5, f20020, g6, g10, f20004, g17, g25, f20766, d20863, d20847, d20831, g41, g42, g43, g44, g45, d19674, d19694, d19714, g58, g59, g60, g61, g62, g63, g110]
                    · have f20977 : (x (-2) 13).toNat = 1 := by rw [h20019]; rfl
                      have d20978 : (x (-3) 2).toNat = 0 := by
                        have r20979 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20980 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                        have e20981 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                        have b20982 := hb (x (-4) 3)
                        have b20983 := hb (x (-3) 2)
                        have b20984 := hb (x (-2) 13)
                        have b20985 := hb (x (-1) 12)
                        clear * - r20979 e20980 e20981 b20982 b20983 b20984 b20985 f20004 f20977
                        omega
                      have d20986 : (x (-3) 10).toNat = 0 := by
                        have r20987 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
                        have b20988 := hb (x (-3) 2)
                        have b20989 := hb (x (-3) 10)
                        clear * - r20987 b20988 b20989 d20978
                        omega
                      have d20990 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                        have r20991 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20992 := hb (x (-3) 2)
                        have b20993 := hb (x (-1) 13)
                        have b20994 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r20991 b20992 b20993 b20994 g12 d20978
                        omega
                      have d20995 : (x (-2) 14).toNat = 1 := by
                        have r20996 := hand2 (x (-2) 1) (x (-2) 14)
                        have b20997 := hb (x (-2) 14)
                        have b20998 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r20996 b20997 b20998 d20990
                        omega
                      have d20999 : (x (-4) 3).toNat = 0 := by
                        have r21000 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e21001 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                        have e21002 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                        have b21003 := hb (x (-4) 3)
                        have b21004 := hb (x (-3) 2)
                        have b21005 := hb (x (-2) 13)
                        have b21006 := hb (x (-1) 12)
                        clear * - r21000 e21001 e21002 b21003 b21004 b21005 b21006 f20004 f20977 d20978
                        omega
                      have d21007 : (x (-4) 11).toNat = 0 := by
                        have r21008 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                        have b21009 := hb (x (-4) 3)
                        have b21010 := hb (x (-4) 11)
                        clear * - r21008 b21009 b21010 d20999
                        omega
                      have r21011 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r21012 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r21013 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21014 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
                      have e21015 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
                      have r21016 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21017 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
                      have e21018 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
                      have r21019 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r21020 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
                      have r21021 := hand2 (x 5 2) (x 5 6)
                      have r21022 := hand2 (x 4 3) (x 4 7)
                      have r21023 := hand2 (x 6 2) (x 6 6)
                      have r21024 := hand2 (x 5 3) (x 5 7)
                      have r21025 := hand1 (x 10 1) (x 10 14)
                      linarith only [r21011, r21012, r21013, e21014, e21015, r21016, e21017, e21018, r21019, r21020, r21021, r21022, r21023, r21024, r21025, d21007, d20986, g2, g4, f20977, d20995, f20004, g12, g18, g19, g26, g27, g31, g32, g35, g36, g38, g55, g56, g57, d19339, d19824, d20015, g58, g59, g60, g61, g62, g63]
                  · have f21076 : (x (-2) 9).toNat = 1 := by rw [h20013]; rfl
                    have d21077 : (x (-3) 10).toNat = 0 := by
                      have r21078 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21079 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e21080 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e21081 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e21082 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e21083 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e21084 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b21085 := hb (x (-8) 7)
                      have b21086 := hb (x (-7) 6)
                      have b21087 := hb (x (-6) 5)
                      have b21088 := hb (x (-5) 4)
                      have b21089 := hb (x (-4) 11)
                      have b21090 := hb (x (-3) 10)
                      have b21091 := hb (x (-2) 9)
                      have b21092 := hb (x (-1) 8)
                      clear * - r21078 e21079 e21080 e21081 e21082 e21083 e21084 b21085 b21086 b21087 b21088 b21089 b21090 b21091 b21092 f19819 f21076
                      omega
                    have d21093 : (x (-4) 11).toNat = 0 := by
                      have r21094 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21095 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e21096 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e21097 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e21098 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e21099 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e21100 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b21101 := hb (x (-8) 7)
                      have b21102 := hb (x (-7) 6)
                      have b21103 := hb (x (-6) 5)
                      have b21104 := hb (x (-5) 4)
                      have b21105 := hb (x (-4) 11)
                      have b21106 := hb (x (-3) 10)
                      have b21107 := hb (x (-2) 9)
                      have b21108 := hb (x (-1) 8)
                      clear * - r21094 e21095 e21096 e21097 e21098 e21099 e21100 b21101 b21102 b21103 b21104 b21105 b21106 b21107 b21108 f19819 f21076 d21077
                      omega
                    have d21109 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
                      have r21110 := hand2 (x (-4) 1) (x (-4) 11)
                      have b21111 := hb (x (-4) 11)
                      have b21112 := hb (x (-4) 1 && x (-4) 11)
                      clear * - r21110 b21111 b21112 d21093
                      omega
                    have d21113 : (x (-5) 4).toNat = 0 := by
                      have r21114 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21115 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e21116 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e21117 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e21118 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e21119 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e21120 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b21121 := hb (x (-8) 7)
                      have b21122 := hb (x (-7) 6)
                      have b21123 := hb (x (-6) 5)
                      have b21124 := hb (x (-5) 4)
                      have b21125 := hb (x (-4) 11)
                      have b21126 := hb (x (-3) 10)
                      have b21127 := hb (x (-2) 9)
                      have b21128 := hb (x (-1) 8)
                      clear * - r21114 e21115 e21116 e21117 e21118 e21119 e21120 b21121 b21122 b21123 b21124 b21125 b21126 b21127 b21128 f19819 f21076 d21077 d21093
                      omega
                    have d21129 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
                      have r21130 := hand1 (x (-5) 4) (x (-5) 14)
                      have b21131 := hb (x (-5) 4)
                      have b21132 := hb (x (-5) 4 && x (-5) 14)
                      clear * - r21130 b21131 b21132 d21113
                      omega
                    have d21133 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                      have r21134 := hand1 (x (-5) 4) (x (-5) 13)
                      have b21135 := hb (x (-5) 4)
                      have b21136 := hb (x (-5) 4 && x (-5) 13)
                      clear * - r21134 b21135 b21136 d21113
                      omega
                    have d21137 : (x (-6) 5).toNat = 0 := by
                      have r21138 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21139 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e21140 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e21141 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e21142 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e21143 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e21144 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b21145 := hb (x (-8) 7)
                      have b21146 := hb (x (-7) 6)
                      have b21147 := hb (x (-6) 5)
                      have b21148 := hb (x (-5) 4)
                      have b21149 := hb (x (-4) 11)
                      have b21150 := hb (x (-3) 10)
                      have b21151 := hb (x (-2) 9)
                      have b21152 := hb (x (-1) 8)
                      clear * - r21138 e21139 e21140 e21141 e21142 e21143 e21144 b21145 b21146 b21147 b21148 b21149 b21150 b21151 b21152 f19819 f21076 d21077 d21093 d21113
                      omega
                    have d21153 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                      have r21154 := hand1 (x (-6) 5) (x (-6) 14)
                      have b21155 := hb (x (-6) 5)
                      have b21156 := hb (x (-6) 5 && x (-6) 14)
                      clear * - r21154 b21155 b21156 d21137
                      omega
                    have d21157 : (x (-7) 6).toNat = 0 := by
                      have r21158 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21159 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                      have e21160 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                      have e21161 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                      have e21162 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                      have e21163 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                      have e21164 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                      have b21165 := hb (x (-8) 7)
                      have b21166 := hb (x (-7) 6)
                      have b21167 := hb (x (-6) 5)
                      have b21168 := hb (x (-5) 4)
                      have b21169 := hb (x (-4) 11)
                      have b21170 := hb (x (-3) 10)
                      have b21171 := hb (x (-2) 9)
                      have b21172 := hb (x (-1) 8)
                      clear * - r21158 e21159 e21160 e21161 e21162 e21163 e21164 b21165 b21166 b21167 b21168 b21169 b21170 b21171 b21172 f19819 f21076 d21077 d21093 d21113 d21137
                      omega
                    have d21173 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
                      have r21174 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21175 := hb (x (-7) 6)
                      have b21176 := hb (x (-1) 9)
                      have b21177 := hb (x (-2) 1 && x (-2) 10)
                      have b21178 := hb (x (-3) 2 && x (-3) 11)
                      have b21179 := hb (x (-4) 3 && x (-4) 12)
                      have b21180 := hb (x (-5) 4 && x (-5) 13)
                      have b21181 := hb (x (-6) 5 && x (-6) 14)
                      clear * - r21174 b21175 b21176 b21177 b21178 b21179 b21180 b21181 g9 g101 g102 d21133 d21153 d21157
                      omega
                    have d21182 : (x (-4) 12).toNat = 1 := by
                      have r21183 := hand2 (x (-4) 3) (x (-4) 12)
                      have b21184 := hb (x (-4) 12)
                      have b21185 := hb (x (-4) 3 && x (-4) 12)
                      clear * - r21183 b21184 b21185 d21173
                      omega
                    have d21186 : (x (-5) 13).toNat = 0 := by
                      have r21187 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21188 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                      have e21189 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                      have b21190 := hb (x (-7) 3)
                      have b21191 := hb (x (-6) 2)
                      have b21192 := hb (x (-5) 13)
                      have b21193 := hb (x (-4) 12)
                      clear * - r21187 e21188 e21189 b21190 b21191 b21192 b21193 d21182
                      omega
                    have d21194 : (x (-6) 2).toNat = 0 := by
                      have r21195 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21196 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                      have e21197 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                      have b21198 := hb (x (-7) 3)
                      have b21199 := hb (x (-6) 2)
                      have b21200 := hb (x (-5) 13)
                      have b21201 := hb (x (-4) 12)
                      clear * - r21195 e21196 e21197 b21198 b21199 b21200 b21201 d21182 d21186
                      omega
                    have d21202 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
                      have r21203 := hand1 (x (-6) 2) (x (-6) 13)
                      have b21204 := hb (x (-6) 2)
                      have b21205 := hb (x (-6) 2 && x (-6) 13)
                      clear * - r21203 b21204 b21205 d21194
                      omega
                    have d21206 : (x (-7) 3).toNat = 0 := by
                      have r21207 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21208 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                      have e21209 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                      have b21210 := hb (x (-7) 3)
                      have b21211 := hb (x (-6) 2)
                      have b21212 := hb (x (-5) 13)
                      have b21213 := hb (x (-4) 12)
                      clear * - r21207 e21208 e21209 b21210 b21211 b21212 b21213 d21182 d21186 d21194
                      omega
                    have d21214 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
                      have r21215 := hand1 (x (-7) 3) (x (-7) 14)
                      have b21216 := hb (x (-7) 3)
                      have b21217 := hb (x (-7) 3 && x (-7) 14)
                      clear * - r21215 b21216 b21217 d21206
                      omega
                    have d21218 : (x (-7) 11).toNat = 0 := by
                      have r21219 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                      have b21220 := hb (x (-7) 3)
                      have b21221 := hb (x (-7) 11)
                      clear * - r21219 b21220 b21221 d21206
                      omega
                    have d21222 : (x (-4) 3).toNat = 1 := by
                      have r21223 := hand1 (x (-4) 3) (x (-4) 12)
                      have b21224 := hb (x (-4) 3)
                      have b21225 := hb (x (-4) 3 && x (-4) 12)
                      clear * - r21223 b21224 b21225 d21173
                      omega
                    have d21226 : (x (-2) 13).toNat = 0 := by
                      have r21227 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21228 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e21229 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b21230 := hb (x (-4) 3)
                      have b21231 := hb (x (-3) 2)
                      have b21232 := hb (x (-2) 13)
                      have b21233 := hb (x (-1) 12)
                      clear * - r21227 e21228 e21229 b21230 b21231 b21232 b21233 f20004 d21222
                      omega
                    have d21234 : (x (-3) 2).toNat = 0 := by
                      have r21235 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21236 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e21237 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b21238 := hb (x (-4) 3)
                      have b21239 := hb (x (-3) 2)
                      have b21240 := hb (x (-2) 13)
                      have b21241 := hb (x (-1) 12)
                      clear * - r21235 e21236 e21237 b21238 b21239 b21240 b21241 f20004 d21226 d21222
                      omega
                    have d21242 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
                      have r21243 := hand1 (x (-3) 2) (x (-3) 12)
                      have b21244 := hb (x (-3) 2)
                      have b21245 := hb (x (-3) 2 && x (-3) 12)
                      clear * - r21243 b21244 b21245 d21234
                      omega
                    have d21246 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
                      have r21247 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21248 := hb (x (-6) 5)
                      have b21249 := hb (x (-1) 10)
                      have b21250 := hb (x (-2) 1 && x (-2) 11)
                      have b21251 := hb (x (-3) 2 && x (-3) 12)
                      have b21252 := hb (x (-4) 3 && x (-4) 13)
                      have b21253 := hb (x (-5) 4 && x (-5) 14)
                      clear * - r21247 b21248 b21249 b21250 b21251 b21252 b21253 g10 g110 d21242 d21129 d21137
                      omega
                    have d21254 : (x (-4) 13).toNat = 1 := by
                      have r21255 := hand2 (x (-4) 3) (x (-4) 13)
                      have b21256 := hb (x (-4) 13)
                      have b21257 := hb (x (-4) 3 && x (-4) 13)
                      clear * - r21255 b21256 b21257 d21246
                      omega
                    have d21258 : (x (-4) 1).toNat = 1 := by
                      have r21259 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                      have b21260 := hb (x (-4) 1)
                      have b21261 := hb (x (-4) 13)
                      clear * - r21259 b21260 b21261 d21254
                      omega
                    have d21262 : (x (-3) 14).toNat = 0 := by
                      have r21263 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21264 := hb (x (-4) 1)
                      have b21265 := hb (x (-3) 14)
                      clear * - r21263 b21264 b21265 d21258
                      omega
                    have d21266 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                      have r21267 := hand2 (x (-3) 1) (x (-3) 14)
                      have b21268 := hb (x (-3) 14)
                      have b21269 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r21267 b21268 b21269 d21262
                      omega
                    have d21270 : (x (-4) 2).toNat = 1 := by
                      have r21271 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21272 := hb (x (-4) 2)
                      have b21273 := hb (x (-2) 13)
                      have b21274 := hb (x (-3) 1 && x (-3) 14)
                      clear * - r21271 b21272 b21273 b21274 d21226 d21266
                      omega
                    have d21275 : (x (-4) 14).toNat = 1 := by
                      have r21276 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                      have b21277 := hb (x (-4) 2)
                      have b21278 := hb (x (-4) 14)
                      clear * - r21276 b21277 b21278 d21270
                      omega
                    have d21279 : (x (-5) 1).toNat = 0 := by
                      have r21280 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21281 := hb (x (-5) 1)
                      have b21282 := hb (x (-4) 14)
                      clear * - r21280 b21281 b21282 d21275
                      omega
                    have d21283 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
                      have r21284 := hand1 (x (-5) 1) (x (-5) 12)
                      have b21285 := hb (x (-5) 1)
                      have b21286 := hb (x (-5) 1 && x (-5) 12)
                      clear * - r21284 b21285 b21286 d21279
                      omega
                    have d21287 : (x (-8) 4).toNat = 1 := by
                      have r21288 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21289 := hb (x (-8) 4)
                      have b21290 := hb (x (-4) 11)
                      have b21291 := hb (x (-5) 1 && x (-5) 12)
                      have b21292 := hb (x (-6) 2 && x (-6) 13)
                      have b21293 := hb (x (-7) 3 && x (-7) 14)
                      clear * - r21288 b21289 b21290 b21291 b21292 b21293 d21093 d21283 d21202 d21214
                      omega
                    have d21294 : (x (-8) 12).toNat = 1 := by
                      have r21295 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                      have b21296 := hb (x (-8) 4)
                      have b21297 := hb (x (-8) 12)
                      clear * - r21295 b21296 b21297 d21287
                      omega
                    have d21298 : (x (-9) 13).toNat = 0 := by
                      have r21299 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21300 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                      have e21301 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                      have b21302 := hb (x (-11) 3)
                      have b21303 := hb (x (-10) 2)
                      have b21304 := hb (x (-9) 13)
                      have b21305 := hb (x (-8) 12)
                      clear * - r21299 e21300 e21301 b21302 b21303 b21304 b21305 d21294
                      omega
                    have d21306 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
                      have r21307 := hand2 (x (-9) 2) (x (-9) 13)
                      have b21308 := hb (x (-9) 13)
                      have b21309 := hb (x (-9) 2 && x (-9) 13)
                      clear * - r21307 b21308 b21309 d21298
                      omega
                    have d21310 : (x (-10) 3 && x (-10) 14).toNat = 1 := by
                      have r21311 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21312 := hb (x (-11) 4)
                      have b21313 := hb (x (-7) 11)
                      have b21314 := hb (x (-8) 1 && x (-8) 12)
                      have b21315 := hb (x (-9) 2 && x (-9) 13)
                      have b21316 := hb (x (-10) 3 && x (-10) 14)
                      clear * - r21311 b21312 b21313 b21314 b21315 b21316 d21218 d19798 d21306 d19718
                      omega
                    have d21317 : (x (-10) 3).toNat = 1 := by
                      have r21318 := hand1 (x (-10) 3) (x (-10) 14)
                      have b21319 := hb (x (-10) 3)
                      have b21320 := hb (x (-10) 3 && x (-10) 14)
                      clear * - r21318 b21319 b21320 d21310
                      omega
                    have d21321 : (x (-7) 12).toNat = 0 := by
                      have r21322 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21323 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                      have e21324 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                      have b21325 := hb (x (-10) 3)
                      have b21326 := hb (x (-9) 2)
                      have b21327 := hb (x (-8) 13)
                      have b21328 := hb (x (-7) 12)
                      clear * - r21322 e21323 e21324 b21325 b21326 b21327 b21328 d19806 d21317
                      omega
                    have d21329 : (x (-7) 4).toNat = 0 := by
                      have r21330 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                      have b21331 := hb (x (-7) 4)
                      have b21332 := hb (x (-7) 12)
                      clear * - r21330 b21331 b21332 d21321
                      omega
                    have d21333 : (x (-7) 4 && x (-7) 14).toNat = 0 := by
                      have r21334 := hand1 (x (-7) 4) (x (-7) 14)
                      have b21335 := hb (x (-7) 4)
                      have b21336 := hb (x (-7) 4 && x (-7) 14)
                      clear * - r21334 b21335 b21336 d21329
                      omega
                    have d21337 : (x (-9) 2).toNat = 0 := by
                      have r21338 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21339 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                      have e21340 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                      have b21341 := hb (x (-10) 3)
                      have b21342 := hb (x (-9) 2)
                      have b21343 := hb (x (-8) 13)
                      have b21344 := hb (x (-7) 12)
                      clear * - r21338 e21339 e21340 b21341 b21342 b21343 b21344 d21321 d19806 d21317
                      omega
                    have d21345 : (x (-7) 13).toNat = 1 := by
                      have r21346 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21347 := hb (x (-9) 2)
                      have b21348 := hb (x (-7) 13)
                      have b21349 := hb (x (-8) 1 && x (-8) 14)
                      clear * - r21346 b21347 b21348 b21349 d19794 d21337
                      omega
                    have d21350 : (x (-7) 1).toNat = 1 := by
                      have r21351 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
                      have b21352 := hb (x (-7) 1)
                      have b21353 := hb (x (-7) 13)
                      clear * - r21351 b21352 b21353 d21345
                      omega
                    have d21354 : (x (-6) 14).toNat = 0 := by
                      have r21355 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21356 := hb (x (-7) 1)
                      have b21357 := hb (x (-6) 14)
                      clear * - r21355 b21356 b21357 d21350
                      omega
                    have d21358 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
                      have r21359 := hand2 (x (-6) 1) (x (-6) 14)
                      have b21360 := hb (x (-6) 14)
                      have b21361 := hb (x (-6) 1 && x (-6) 14)
                      clear * - r21359 b21360 b21361 d21354
                      omega
                    have d21362 : (x (-7) 2).toNat = 1 := by
                      have r21363 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21364 := hb (x (-7) 2)
                      have b21365 := hb (x (-5) 13)
                      have b21366 := hb (x (-6) 1 && x (-6) 14)
                      clear * - r21363 b21364 b21365 b21366 d21186 d21358
                      omega
                    have d21367 : (x (-5) 12).toNat = 0 := by
                      have r21368 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e21369 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                      have e21370 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                      have b21371 := hb (x (-8) 3)
                      have b21372 := hb (x (-7) 2)
                      have b21373 := hb (x (-6) 13)
                      have b21374 := hb (x (-5) 12)
                      clear * - r21368 e21369 e21370 b21371 b21372 b21373 b21374 d21362
                      omega
                    have d21375 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
                      have r21376 := hand2 (x (-5) 2) (x (-5) 12)
                      have b21377 := hb (x (-5) 12)
                      have b21378 := hb (x (-5) 2 && x (-5) 12)
                      clear * - r21376 b21377 b21378 d21367
                      omega
                    have d21379 : (x (-6) 3 && x (-6) 13).toNat = 1 := by
                      have r21380 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b21381 := hb (x (-8) 5)
                      have b21382 := hb (x (-3) 10)
                      have b21383 := hb (x (-4) 1 && x (-4) 11)
                      have b21384 := hb (x (-5) 2 && x (-5) 12)
                      have b21385 := hb (x (-6) 3 && x (-6) 13)
                      have b21386 := hb (x (-7) 4 && x (-7) 14)
                      clear * - r21380 b21381 b21382 b21383 b21384 b21385 b21386 d21077 d21109 d21375 d21333 d19814
                      omega
                    have d21387 : (x (-6) 13).toNat = 1 := by
                      have r21388 := hand2 (x (-6) 3) (x (-6) 13)
                      have b21389 := hb (x (-6) 13)
                      have b21390 := hb (x (-6) 3 && x (-6) 13)
                      clear * - r21388 b21389 b21390 d21379
                      omega
                    have r21391 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21392 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                    have e21393 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                    have b21394 := hb (x (-8) 3)
                    have b21395 := hb (x (-7) 2)
                    have b21396 := hb (x (-6) 13)
                    have b21397 := hb (x (-5) 12)
                    linarith only [r21391, e21392, e21393, b21394, b21395, b21396, b21397, d21367, d21387, d21362]
                · have f21398 : (x 2 6).toNat = 1 := by rw [h20011]; rfl
                  have d21399 : (x 8 8).toNat = 0 := by
                    have r21400 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21401 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e21402 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e21403 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e21404 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e21405 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e21406 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b21407 := hb (x 1 7)
                    have b21408 := hb (x 2 6)
                    have b21409 := hb (x 3 5)
                    have b21410 := hb (x 4 4)
                    have b21411 := hb (x 5 11)
                    have b21412 := hb (x 6 10)
                    have b21413 := hb (x 7 9)
                    have b21414 := hb (x 8 8)
                    clear * - r21400 e21401 e21402 e21403 e21404 e21405 e21406 b21407 b21408 b21409 b21410 b21411 b21412 b21413 b21414 f21398 f19646
                    omega
                  have d21415 : (x 7 9).toNat = 0 := by
                    have r21416 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21417 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e21418 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e21419 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e21420 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e21421 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e21422 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b21423 := hb (x 1 7)
                    have b21424 := hb (x 2 6)
                    have b21425 := hb (x 3 5)
                    have b21426 := hb (x 4 4)
                    have b21427 := hb (x 5 11)
                    have b21428 := hb (x 6 10)
                    have b21429 := hb (x 7 9)
                    have b21430 := hb (x 8 8)
                    clear * - r21416 e21417 e21418 e21419 e21420 e21421 e21422 b21423 b21424 b21425 b21426 b21427 b21428 b21429 b21430 d21399 f21398 f19646
                    omega
                  have d21431 : (x 6 10).toNat = 0 := by
                    have r21432 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21433 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e21434 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e21435 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e21436 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e21437 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e21438 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b21439 := hb (x 1 7)
                    have b21440 := hb (x 2 6)
                    have b21441 := hb (x 3 5)
                    have b21442 := hb (x 4 4)
                    have b21443 := hb (x 5 11)
                    have b21444 := hb (x 6 10)
                    have b21445 := hb (x 7 9)
                    have b21446 := hb (x 8 8)
                    clear * - r21432 e21433 e21434 e21435 e21436 e21437 e21438 b21439 b21440 b21441 b21442 b21443 b21444 b21445 b21446 d21399 d21415 f21398 f19646
                    omega
                  have d21447 : (x 6 1 && x 6 10).toNat = 0 := by
                    have r21448 := hand2 (x 6 1) (x 6 10)
                    have b21449 := hb (x 6 10)
                    have b21450 := hb (x 6 1 && x 6 10)
                    clear * - r21448 b21449 b21450 d21431
                    omega
                  have d21451 : (x 5 11).toNat = 0 := by
                    have r21452 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21453 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e21454 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e21455 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e21456 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e21457 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e21458 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b21459 := hb (x 1 7)
                    have b21460 := hb (x 2 6)
                    have b21461 := hb (x 3 5)
                    have b21462 := hb (x 4 4)
                    have b21463 := hb (x 5 11)
                    have b21464 := hb (x 6 10)
                    have b21465 := hb (x 7 9)
                    have b21466 := hb (x 8 8)
                    clear * - r21452 e21453 e21454 e21455 e21456 e21457 e21458 b21459 b21460 b21461 b21462 b21463 b21464 b21465 b21466 d21399 d21415 d21431 f21398 f19646
                    omega
                  have d21467 : (x 5 1 && x 5 11).toNat = 0 := by
                    have r21468 := hand2 (x 5 1) (x 5 11)
                    have b21469 := hb (x 5 11)
                    have b21470 := hb (x 5 1 && x 5 11)
                    clear * - r21468 b21469 b21470 d21451
                    omega
                  have d21471 : (x 5 2 && x 5 11).toNat = 0 := by
                    have r21472 := hand2 (x 5 2) (x 5 11)
                    have b21473 := hb (x 5 11)
                    have b21474 := hb (x 5 2 && x 5 11)
                    clear * - r21472 b21473 b21474 d21451
                    omega
                  have d21475 : (x 4 3 && x 4 12).toNat = 1 := by
                    have r21476 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b21477 := hb (x 1 6)
                    have b21478 := hb (x 7 9)
                    have b21479 := hb (x 6 1 && x 6 10)
                    have b21480 := hb (x 5 2 && x 5 11)
                    have b21481 := hb (x 4 3 && x 4 12)
                    have b21482 := hb (x 3 4 && x 3 13)
                    have b21483 := hb (x 2 5 && x 2 14)
                    clear * - r21476 b21477 b21478 b21479 b21480 b21481 b21482 b21483 d21415 d21447 d21471 g107 g108 g24
                    omega
                  have d21484 : (x 4 12).toNat = 1 := by
                    have r21485 := hand2 (x 4 3) (x 4 12)
                    have b21486 := hb (x 4 12)
                    have b21487 := hb (x 4 3 && x 4 12)
                    clear * - r21485 b21486 b21487 d21475
                    omega
                  have d21488 : (x 3 13).toNat = 0 := by
                    have r21489 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21490 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e21491 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b21492 := hb (x 1 3)
                    have b21493 := hb (x 2 2)
                    have b21494 := hb (x 3 13)
                    have b21495 := hb (x 4 12)
                    clear * - r21489 e21490 e21491 b21492 b21493 b21494 b21495 d21484 f19644
                    omega
                  have d21496 : (x 3 3 && x 3 13).toNat = 0 := by
                    have r21497 := hand2 (x 3 3) (x 3 13)
                    have b21498 := hb (x 3 13)
                    have b21499 := hb (x 3 3 && x 3 13)
                    clear * - r21497 b21498 b21499 d21488
                    omega
                  have d21500 : (x 4 2 && x 4 12).toNat = 1 := by
                    have r21501 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b21502 := hb (x 1 5)
                    have b21503 := hb (x 6 10)
                    have b21504 := hb (x 5 1 && x 5 11)
                    have b21505 := hb (x 4 2 && x 4 12)
                    have b21506 := hb (x 3 3 && x 3 13)
                    have b21507 := hb (x 2 4 && x 2 14)
                    clear * - r21501 b21502 b21503 b21504 b21505 b21506 b21507 d21431 d21467 d21496 g114 g23
                    omega
                  have d21508 : (x 4 2).toNat = 1 := by
                    have r21509 := hand1 (x 4 2) (x 4 12)
                    have b21510 := hb (x 4 2)
                    have b21511 := hb (x 4 2 && x 4 12)
                    clear * - r21509 b21510 b21511 d21500
                    omega
                  have d21512 : (x 6 12).toNat = 0 := by
                    have r21513 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21514 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e21515 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b21516 := hb (x 3 3)
                    have b21517 := hb (x 4 2)
                    have b21518 := hb (x 5 13)
                    have b21519 := hb (x 6 12)
                    clear * - r21513 e21514 e21515 b21516 b21517 b21518 b21519 d21508
                    omega
                  have d21520 : (x 6 2 && x 6 12).toNat = 0 := by
                    have r21521 := hand2 (x 6 2) (x 6 12)
                    have b21522 := hb (x 6 12)
                    have b21523 := hb (x 6 2 && x 6 12)
                    clear * - r21521 b21522 b21523 d21512
                    omega
                  have d21524 : (x 5 13).toNat = 0 := by
                    have r21525 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21526 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e21527 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b21528 := hb (x 3 3)
                    have b21529 := hb (x 4 2)
                    have b21530 := hb (x 5 13)
                    have b21531 := hb (x 6 12)
                    clear * - r21525 e21526 e21527 b21528 b21529 b21530 b21531 d21512 d21508
                    omega
                  have d21532 : (x 5 3 && x 5 13).toNat = 0 := by
                    have r21533 := hand2 (x 5 3) (x 5 13)
                    have b21534 := hb (x 5 13)
                    have b21535 := hb (x 5 3 && x 5 13)
                    clear * - r21533 b21534 b21535 d21524
                    omega
                  have d21536 : (x 3 5).toNat = 0 := by
                    have r21537 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
                    have b21538 := hb (x 3 5)
                    have b21539 := hb (x 3 13)
                    clear * - r21537 b21538 b21539 d21488
                    omega
                  have d21540 : (x 2 1 && x 2 14).toNat = 1 := by
                    have r21541 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b21542 := hb (x 1 2)
                    have b21543 := hb (x 3 13)
                    have b21544 := hb (x 2 1 && x 2 14)
                    clear * - r21541 b21542 b21543 b21544 d21488 g21
                    omega
                  have d21545 : (x 2 1).toNat = 1 := by
                    have r21546 := hand1 (x 2 1) (x 2 14)
                    have b21547 := hb (x 2 1)
                    have b21548 := hb (x 2 1 && x 2 14)
                    clear * - r21546 b21547 b21548 d21540
                    omega
                  have d21549 : (x 3 14).toNat = 0 := by
                    have r21550 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b21551 := hb (x 2 1)
                    have b21552 := hb (x 3 14)
                    clear * - r21550 b21551 b21552 d21545
                    omega
                  have d21553 : (x 3 2).toNat = 0 := by
                    have r21554 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                    have b21555 := hb (x 3 2)
                    have b21556 := hb (x 3 14)
                    clear * - r21554 b21555 b21556 d21549
                    omega
                  have d21557 : (x 4 1 && x 4 14).toNat = 1 := by
                    have r21558 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b21559 := hb (x 3 2)
                    have b21560 := hb (x 5 13)
                    have b21561 := hb (x 4 1 && x 4 14)
                    clear * - r21558 b21559 b21560 b21561 d21524 d21553
                    omega
                  have d21562 : (x 4 1).toNat = 1 := by
                    have r21563 := hand1 (x 4 1) (x 4 14)
                    have b21564 := hb (x 4 1)
                    have b21565 := hb (x 4 1 && x 4 14)
                    clear * - r21563 b21564 b21565 d21557
                    omega
                  have d21566 : (x 5 14).toNat = 0 := by
                    have r21567 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b21568 := hb (x 4 1)
                    have b21569 := hb (x 5 14)
                    clear * - r21567 b21568 b21569 d21562
                    omega
                  have d21570 : (x 5 2).toNat = 0 := by
                    have r21571 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                    have b21572 := hb (x 5 2)
                    have b21573 := hb (x 5 14)
                    clear * - r21571 b21572 b21573 d21566
                    omega
                  have d21574 : (x 4 3).toNat = 1 := by
                    have r21575 := hand1 (x 4 3) (x 4 12)
                    have b21576 := hb (x 4 3)
                    have b21577 := hb (x 4 3 && x 4 12)
                    clear * - r21575 b21576 b21577 d21475
                    omega
                  have d21578 : (x 7 12).toNat = 0 := by
                    have r21579 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21580 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                    have e21581 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                    have b21582 := hb (x 4 3)
                    have b21583 := hb (x 5 2)
                    have b21584 := hb (x 6 13)
                    have b21585 := hb (x 7 12)
                    clear * - r21579 e21580 e21581 b21582 b21583 b21584 b21585 d21570 d21574
                    omega
                  have d21586 : (x 7 4).toNat = 0 := by
                    have r21587 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                    have b21588 := hb (x 7 4)
                    have b21589 := hb (x 7 12)
                    clear * - r21587 b21588 b21589 d21578
                    omega
                  have d21590 : (x 4 4).toNat = 0 := by
                    have r21591 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21592 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                    have e21593 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                    have e21594 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                    have e21595 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                    have e21596 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                    have e21597 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                    have b21598 := hb (x 1 7)
                    have b21599 := hb (x 2 6)
                    have b21600 := hb (x 3 5)
                    have b21601 := hb (x 4 4)
                    have b21602 := hb (x 5 11)
                    have b21603 := hb (x 6 10)
                    have b21604 := hb (x 7 9)
                    have b21605 := hb (x 8 8)
                    clear * - r21591 e21592 e21593 e21594 e21595 e21596 e21597 b21598 b21599 b21600 b21601 b21602 b21603 b21604 b21605 d21399 d21415 d21431 d21451 d21536 f21398 f19646
                    omega
                  have d21606 : (x 4 4 && x 4 14).toNat = 0 := by
                    have r21607 := hand1 (x 4 4) (x 4 14)
                    have b21608 := hb (x 4 4)
                    have b21609 := hb (x 4 4 && x 4 14)
                    clear * - r21607 b21608 b21609 d21590
                    omega
                  have d21610 : (x 7 1 && x 7 11).toNat = 1 := by
                    have r21611 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b21612 := hb (x 3 5)
                    have b21613 := hb (x 8 10)
                    have b21614 := hb (x 7 1 && x 7 11)
                    have b21615 := hb (x 6 2 && x 6 12)
                    have b21616 := hb (x 5 3 && x 5 13)
                    have b21617 := hb (x 4 4 && x 4 14)
                    clear * - r21611 b21612 b21613 b21614 b21615 b21616 b21617 d19999 d21520 d21532 d21606 d21536
                    omega
                  have d21618 : (x 7 11).toNat = 1 := by
                    have r21619 := hand2 (x 7 1) (x 7 11)
                    have b21620 := hb (x 7 11)
                    have b21621 := hb (x 7 1 && x 7 11)
                    clear * - r21619 b21620 b21621 d21610
                    omega
                  have d21622 : (x 7 3).toNat = 1 := by
                    have r21623 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
                    have b21624 := hb (x 7 3)
                    have b21625 := hb (x 7 11)
                    clear * - r21623 b21624 b21625 d21618
                    omega
                  have d21626 : (x 10 12).toNat = 0 := by
                    have r21627 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e21628 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                    have e21629 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                    have b21630 := hb (x 7 3)
                    have b21631 := hb (x 8 2)
                    have b21632 := hb (x 9 13)
                    have b21633 := hb (x 10 12)
                    clear * - r21627 e21628 e21629 b21630 b21631 b21632 b21633 d19995 d21622
                    omega
                  have d21634 : (x 10 1 && x 10 12).toNat = 0 := by
                    have r21635 := hand2 (x 10 1) (x 10 12)
                    have b21636 := hb (x 10 12)
                    have b21637 := hb (x 10 1 && x 10 12)
                    clear * - r21635 b21636 b21637 d21626
                    omega
                  have d21638 : (x 9 2 && x 9 13).toNat = 1 := by
                    have r21639 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b21640 := hb (x 7 4)
                    have b21641 := hb (x 11 11)
                    have b21642 := hb (x 10 1 && x 10 12)
                    have b21643 := hb (x 9 2 && x 9 13)
                    have b21644 := hb (x 8 3 && x 8 14)
                    clear * - r21639 b21640 b21641 b21642 b21643 b21644 d19891 d21634 d19983 d21586
                    omega
                  have d21645 : (x 9 13).toNat = 1 := by
                    have r21646 := hand2 (x 9 2) (x 9 13)
                    have b21647 := hb (x 9 13)
                    have b21648 := hb (x 9 2 && x 9 13)
                    clear * - r21646 b21647 b21648 d21638
                    omega
                  have r21649 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21650 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                  have e21651 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                  have b21652 := hb (x 7 3)
                  have b21653 := hb (x 8 2)
                  have b21654 := hb (x 9 13)
                  have b21655 := hb (x 10 12)
                  linarith only [r21649, e21650, e21651, b21652, b21653, b21654, b21655, d21626, d21645, d19995, d21622]
              · have f21656 : (x (-1) 14).toNat = 1 := by rw [h20005]; rfl
                have d21657 : (x (-2) 1).toNat = 0 := by
                  have r21658 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21659 := hb (x (-2) 1)
                  have b21660 := hb (x (-1) 14)
                  clear * - r21658 b21659 b21660 f21656
                  omega
                have d21661 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                  have r21662 := hand1 (x (-2) 1) (x (-2) 14)
                  have b21663 := hb (x (-2) 1)
                  have b21664 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r21662 b21663 b21664 d21657
                  omega
                have d21665 : (x (-2) 13).toNat = 0 := by
                  have r21666 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                  have b21667 := hb (x (-2) 1)
                  have b21668 := hb (x (-2) 13)
                  clear * - r21666 b21667 b21668 d21657
                  omega
                have d21669 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
                  have r21670 := hand2 (x (-2) 9) (x (-2) 13)
                  have b21671 := hb (x (-2) 13)
                  have b21672 := hb (x (-2) 9 && x (-2) 13)
                  clear * - r21670 b21671 b21672 d21665
                  omega
                have d21673 : (x (-2) 9).toNat = 0 := by
                  have r21674 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
                  have b21675 := hb (x (-2) 1)
                  have b21676 := hb (x (-2) 9)
                  clear * - r21674 b21675 b21676 d21657
                  omega
                have d21677 : (x (-3) 2).toNat = 1 := by
                  have r21678 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21679 := hb (x (-3) 2)
                  have b21680 := hb (x (-1) 13)
                  have b21681 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r21678 b21679 b21680 b21681 g12 d21661
                  omega
                have d21682 : (x (-3) 14).toNat = 1 := by
                  have r21683 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                  have b21684 := hb (x (-3) 2)
                  have b21685 := hb (x (-3) 14)
                  clear * - r21683 b21684 b21685 d21677
                  omega
                have d21686 : (x (-4) 3).toNat = 0 := by
                  have r21687 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21688 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e21689 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b21690 := hb (x (-4) 3)
                  have b21691 := hb (x (-3) 2)
                  have b21692 := hb (x (-2) 13)
                  have b21693 := hb (x (-1) 12)
                  clear * - r21687 e21688 e21689 b21690 b21691 b21692 b21693 f20004 d21665 d21677
                  omega
                have d21694 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                  have r21695 := hand1 (x (-4) 3) (x (-4) 12)
                  have b21696 := hb (x (-4) 3)
                  have b21697 := hb (x (-4) 3 && x (-4) 12)
                  clear * - r21695 b21696 b21697 d21686
                  omega
                have d21698 : (x (-4) 11).toNat = 0 := by
                  have r21699 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                  have b21700 := hb (x (-4) 3)
                  have b21701 := hb (x (-4) 11)
                  clear * - r21699 b21700 b21701 d21686
                  omega
                have r21702 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r21703 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r21704 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r21705 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21706 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                have e21707 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                have e21708 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                have e21709 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                have e21710 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                have e21711 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                have r21712 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21713 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e21714 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have r21715 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21716 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                have e21717 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                have r21718 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r21719 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21720 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
                have e21721 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
                have r21722 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r21723 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r21724 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r21725 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r21726 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
                have r21727 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
                have r21728 := hand2 (x 5 2) (x 5 6)
                have r21729 := hand2 (x 4 3) (x 4 7)
                have r21730 := hand2 (x 6 1) (x 6 7)
                have r21731 := hand1 (x (-5) 4) (x (-5) 13)
                have r21732 := hand1 (x (-6) 5) (x (-6) 14)
                have r21733 := hand1 (x 10 3) (x 10 12)
                have r21734 := hand1 (x 9 4) (x 9 13)
                have r21735 := hand1 (x 10 1) (x 10 12)
                have r21736 := hand1 (x 9 2) (x 9 13)
                linarith only [r21702, r21703, r21704, r21705, e21706, e21707, e21708, e21709, e21710, e21711, r21712, e21713, e21714, r21715, e21716, e21717, r21718, r21719, e21720, e21721, r21722, r21723, r21724, r21725, r21726, r21727, r21728, r21729, r21730, r21731, r21732, r21733, r21734, r21735, r21736, d19786, d21698, d21682, d21673, d21665, f19819, g9, f20004, f21656, g15, g18, g20, g24, g26, g28, g30, g31, g33, g34, g35, g37, g39, g40, d19891, d19855, g55, g56, g57, d19339, d19824, d21669, g76, g77, g78, g79, g80, d19331, d19820, g101, g102, d21694, d19887, d19911, d19991, d19983]
            · have f21820 : (x (-1) 12).toNat = 1 := by rw [h20003]; rfl
              have d21821 : (x (-2) 13).toNat = 0 := by
                have r21822 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21823 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e21824 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b21825 := hb (x (-4) 3)
                have b21826 := hb (x (-3) 2)
                have b21827 := hb (x (-2) 13)
                have b21828 := hb (x (-1) 12)
                clear * - r21822 e21823 e21824 b21825 b21826 b21827 b21828 f21820
                omega
              have d21829 : (x (-3) 2).toNat = 0 := by
                have r21830 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21831 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e21832 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b21833 := hb (x (-4) 3)
                have b21834 := hb (x (-3) 2)
                have b21835 := hb (x (-2) 13)
                have b21836 := hb (x (-1) 12)
                clear * - r21830 e21831 e21832 b21833 b21834 b21835 b21836 f21820 d21821
                omega
              have d21837 : (x (-3) 2 && x (-3) 13).toNat = 0 := by
                have r21838 := hand1 (x (-3) 2) (x (-3) 13)
                have b21839 := hb (x (-3) 2)
                have b21840 := hb (x (-3) 2 && x (-3) 13)
                clear * - r21838 b21839 b21840 d21829
                omega
              have d21841 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                have r21842 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21843 := hb (x (-3) 2)
                have b21844 := hb (x (-1) 13)
                have b21845 := hb (x (-2) 1 && x (-2) 14)
                clear * - r21842 b21843 b21844 b21845 g12 d21829
                omega
              have d21846 : (x (-2) 14).toNat = 1 := by
                have r21847 := hand2 (x (-2) 1) (x (-2) 14)
                have b21848 := hb (x (-2) 14)
                have b21849 := hb (x (-2) 1 && x (-2) 14)
                clear * - r21847 b21848 b21849 d21841
                omega
              have d21850 : (x (-3) 1).toNat = 0 := by
                have r21851 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21852 := hb (x (-3) 1)
                have b21853 := hb (x (-2) 14)
                clear * - r21851 b21852 b21853 d21846
                omega
              have d21854 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                have r21855 := hand1 (x (-3) 1) (x (-3) 14)
                have b21856 := hb (x (-3) 1)
                have b21857 := hb (x (-3) 1 && x (-3) 14)
                clear * - r21855 b21856 b21857 d21850
                omega
              have d21858 : (x (-4) 2).toNat = 1 := by
                have r21859 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21860 := hb (x (-4) 2)
                have b21861 := hb (x (-2) 13)
                have b21862 := hb (x (-3) 1 && x (-3) 14)
                clear * - r21859 b21860 b21861 b21862 d21821 d21854
                omega
              have d21863 : (x (-4) 14).toNat = 1 := by
                have r21864 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
                have b21865 := hb (x (-4) 2)
                have b21866 := hb (x (-4) 14)
                clear * - r21864 b21865 b21866 d21858
                omega
              have d21867 : (x (-5) 1).toNat = 0 := by
                have r21868 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21869 := hb (x (-5) 1)
                have b21870 := hb (x (-4) 14)
                clear * - r21868 b21869 b21870 d21863
                omega
              have d21871 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
                have r21872 := hand1 (x (-5) 1) (x (-5) 12)
                have b21873 := hb (x (-5) 1)
                have b21874 := hb (x (-5) 1 && x (-5) 12)
                clear * - r21872 b21873 b21874 d21867
                omega
              have d21875 : (x (-5) 13).toNat = 0 := by
                have r21876 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
                have b21877 := hb (x (-5) 1)
                have b21878 := hb (x (-5) 13)
                clear * - r21876 b21877 b21878 d21867
                omega
              have d21879 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
                have r21880 := hand2 (x (-5) 2) (x (-5) 13)
                have b21881 := hb (x (-5) 13)
                have b21882 := hb (x (-5) 2 && x (-5) 13)
                clear * - r21880 b21881 b21882 d21875
                omega
              have d21883 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
                have r21884 := hand1 (x (-3) 1) (x (-3) 12)
                have b21885 := hb (x (-3) 1)
                have b21886 := hb (x (-3) 1 && x (-3) 12)
                clear * - r21884 b21885 b21886 d21850
                omega
              have d21887 : (x (-3) 13).toNat = 0 := by
                have r21888 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                have b21889 := hb (x (-3) 1)
                have b21890 := hb (x (-3) 13)
                clear * - r21888 b21889 b21890 d21850
                omega
              have d21891 : (x (-4) 3).toNat = 0 := by
                have r21892 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21893 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                have e21894 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                have b21895 := hb (x (-4) 3)
                have b21896 := hb (x (-3) 2)
                have b21897 := hb (x (-2) 13)
                have b21898 := hb (x (-1) 12)
                clear * - r21892 e21893 e21894 b21895 b21896 b21897 b21898 f21820 d21821 d21829
                omega
              have d21899 : (x (-4) 3 && x (-4) 14).toNat = 0 := by
                have r21900 := hand1 (x (-4) 3) (x (-4) 14)
                have b21901 := hb (x (-4) 3)
                have b21902 := hb (x (-4) 3 && x (-4) 14)
                clear * - r21900 b21901 b21902 d21891
                omega
              have d21903 : (x (-4) 11).toNat = 0 := by
                have r21904 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                have b21905 := hb (x (-4) 3)
                have b21906 := hb (x (-4) 11)
                clear * - r21904 b21905 b21906 d21891
                omega
              have d21907 : (x (-2) 12).toNat = 0 := by
                have r21908 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21909 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e21910 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b21911 := hb (x (-5) 3)
                have b21912 := hb (x (-4) 2)
                have b21913 := hb (x (-3) 13)
                have b21914 := hb (x (-2) 12)
                clear * - r21908 e21909 e21910 b21911 b21912 b21913 b21914 d21887 d21858
                omega
              have d21915 : (x (-2) 1 && x (-2) 12).toNat = 0 := by
                have r21916 := hand2 (x (-2) 1) (x (-2) 12)
                have b21917 := hb (x (-2) 12)
                have b21918 := hb (x (-2) 1 && x (-2) 12)
                clear * - r21916 b21917 b21918 d21907
                omega
              have d21919 : (x (-5) 3).toNat = 0 := by
                have r21920 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21921 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                have e21922 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                have b21923 := hb (x (-5) 3)
                have b21924 := hb (x (-4) 2)
                have b21925 := hb (x (-3) 13)
                have b21926 := hb (x (-2) 12)
                clear * - r21920 e21921 e21922 b21923 b21924 b21925 b21926 d21907 d21887 d21858
                omega
              have d21927 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
                have r21928 := hand1 (x (-5) 3) (x (-5) 14)
                have b21929 := hb (x (-5) 3)
                have b21930 := hb (x (-5) 3 && x (-5) 14)
                clear * - r21928 b21929 b21930 d21919
                omega
              have d21931 : (x (-5) 4).toNat = 1 := by
                have r21932 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21933 := hb (x (-5) 4)
                have b21934 := hb (x (-1) 11)
                have b21935 := hb (x (-2) 1 && x (-2) 12)
                have b21936 := hb (x (-3) 2 && x (-3) 13)
                have b21937 := hb (x (-4) 3 && x (-4) 14)
                clear * - r21932 b21933 b21934 b21935 b21936 b21937 g11 d21915 d21837 d21899
                omega
              have d21938 : (x (-5) 12).toNat = 1 := by
                have r21939 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
                have b21940 := hb (x (-5) 4)
                have b21941 := hb (x (-5) 12)
                clear * - r21939 b21940 b21941 d21931
                omega
              have d21942 : (x (-6) 13).toNat = 0 := by
                have r21943 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21944 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e21945 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b21946 := hb (x (-8) 3)
                have b21947 := hb (x (-7) 2)
                have b21948 := hb (x (-6) 13)
                have b21949 := hb (x (-5) 12)
                clear * - r21943 e21944 e21945 b21946 b21947 b21948 b21949 d21938
                omega
              have d21950 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
                have r21951 := hand2 (x (-6) 2) (x (-6) 13)
                have b21952 := hb (x (-6) 13)
                have b21953 := hb (x (-6) 2 && x (-6) 13)
                clear * - r21951 b21952 b21953 d21942
                omega
              have d21954 : (x (-7) 2).toNat = 0 := by
                have r21955 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21956 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                have e21957 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                have b21958 := hb (x (-8) 3)
                have b21959 := hb (x (-7) 2)
                have b21960 := hb (x (-6) 13)
                have b21961 := hb (x (-5) 12)
                clear * - r21955 e21956 e21957 b21958 b21959 b21960 b21961 d21938 d21942
                omega
              have d21962 : (x (-6) 1 && x (-6) 14).toNat = 1 := by
                have r21963 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21964 := hb (x (-7) 2)
                have b21965 := hb (x (-5) 13)
                have b21966 := hb (x (-6) 1 && x (-6) 14)
                clear * - r21963 b21964 b21965 b21966 d21875 d21954
                omega
              have d21967 : (x (-6) 14).toNat = 1 := by
                have r21968 := hand2 (x (-6) 1) (x (-6) 14)
                have b21969 := hb (x (-6) 14)
                have b21970 := hb (x (-6) 1 && x (-6) 14)
                clear * - r21968 b21969 b21970 d21962
                omega
              have d21971 : (x (-7) 1).toNat = 0 := by
                have r21972 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21973 := hb (x (-7) 1)
                have b21974 := hb (x (-6) 14)
                clear * - r21972 b21973 b21974 d21967
                omega
              have d21975 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
                have r21976 := hand1 (x (-7) 1) (x (-7) 14)
                have b21977 := hb (x (-7) 1)
                have b21978 := hb (x (-7) 1 && x (-7) 14)
                clear * - r21976 b21977 b21978 d21971
                omega
              have d21979 : (x (-8) 2).toNat = 1 := by
                have r21980 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21981 := hb (x (-8) 2)
                have b21982 := hb (x (-6) 13)
                have b21983 := hb (x (-7) 1 && x (-7) 14)
                clear * - r21980 b21981 b21982 b21983 d21942 d21975
                omega
              have d21984 : (x (-8) 14).toNat = 1 := by
                have r21985 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
                have b21986 := hb (x (-8) 2)
                have b21987 := hb (x (-8) 14)
                clear * - r21985 b21986 b21987 d21979
                omega
              have d21988 : (x (-9) 1).toNat = 0 := by
                have r21989 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21990 := hb (x (-9) 1)
                have b21991 := hb (x (-8) 14)
                clear * - r21989 b21990 b21991 d21984
                omega
              have d21992 : (x (-9) 1 && x (-9) 14).toNat = 0 := by
                have r21993 := hand1 (x (-9) 1) (x (-9) 14)
                have b21994 := hb (x (-9) 1)
                have b21995 := hb (x (-9) 1 && x (-9) 14)
                clear * - r21993 b21994 b21995 d21988
                omega
              have d21996 : (x (-10) 2).toNat = 1 := by
                have r21997 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21998 := hb (x (-10) 2)
                have b21999 := hb (x (-8) 13)
                have b22000 := hb (x (-9) 1 && x (-9) 14)
                clear * - r21997 b21998 b21999 b22000 d19806 d21992
                omega
              have d22001 : (x (-8) 12).toNat = 0 := by
                have r22002 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22003 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                have e22004 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                have b22005 := hb (x (-11) 3)
                have b22006 := hb (x (-10) 2)
                have b22007 := hb (x (-9) 13)
                have b22008 := hb (x (-8) 12)
                clear * - r22002 e22003 e22004 b22005 b22006 b22007 b22008 d21996
                omega
              have d22009 : (x (-8) 4).toNat = 0 := by
                have r22010 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                have b22011 := hb (x (-8) 4)
                have b22012 := hb (x (-8) 12)
                clear * - r22010 b22011 b22012 d22001
                omega
              have d22013 : (x (-6) 12).toNat = 0 := by
                have r22014 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22015 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                have e22016 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                have b22017 := hb (x (-9) 3)
                have b22018 := hb (x (-8) 2)
                have b22019 := hb (x (-7) 13)
                have b22020 := hb (x (-6) 12)
                clear * - r22014 e22015 e22016 b22017 b22018 b22019 b22020 d21979
                omega
              have d22021 : (x (-6) 4).toNat = 0 := by
                have r22022 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                have b22023 := hb (x (-6) 4)
                have b22024 := hb (x (-6) 12)
                clear * - r22022 b22023 b22024 d22013
                omega
              have d22025 : (x (-7) 13).toNat = 0 := by
                have r22026 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22027 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                have e22028 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                have b22029 := hb (x (-9) 3)
                have b22030 := hb (x (-8) 2)
                have b22031 := hb (x (-7) 13)
                have b22032 := hb (x (-6) 12)
                clear * - r22026 e22027 e22028 b22029 b22030 b22031 b22032 d22013 d21979
                omega
              have d22033 : (x (-9) 2).toNat = 1 := by
                have r22034 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22035 := hb (x (-9) 2)
                have b22036 := hb (x (-7) 13)
                have b22037 := hb (x (-8) 1 && x (-8) 14)
                clear * - r22034 b22035 b22036 b22037 d22025 d19794
                omega
              have d22038 : (x (-7) 12).toNat = 0 := by
                have r22039 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22040 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                have e22041 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                have b22042 := hb (x (-10) 3)
                have b22043 := hb (x (-9) 2)
                have b22044 := hb (x (-8) 13)
                have b22045 := hb (x (-7) 12)
                clear * - r22039 e22040 e22041 b22042 b22043 b22044 b22045 d19806 d22033
                omega
              have d22046 : (x (-7) 4).toNat = 0 := by
                have r22047 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                have b22048 := hb (x (-7) 4)
                have b22049 := hb (x (-7) 12)
                clear * - r22047 b22048 b22049 d22038
                omega
              have d22050 : (x (-6) 1).toNat = 1 := by
                have r22051 := hand1 (x (-6) 1) (x (-6) 14)
                have b22052 := hb (x (-6) 1)
                have b22053 := hb (x (-6) 1 && x (-6) 14)
                clear * - r22051 b22052 b22053 d21962
                omega
              have d22054 : (x (-5) 14).toNat = 0 := by
                have r22055 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22056 := hb (x (-6) 1)
                have b22057 := hb (x (-5) 14)
                clear * - r22055 b22056 b22057 d22050
                omega
              have d22058 : (x (-5) 2).toNat = 0 := by
                have r22059 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
                have b22060 := hb (x (-5) 2)
                have b22061 := hb (x (-5) 14)
                clear * - r22059 b22060 b22061 d22054
                omega
              have d22062 : (x (-4) 2 && x (-4) 13).toNat = 1 := by
                have r22063 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22064 := hb (x (-6) 4)
                have b22065 := hb (x (-2) 11)
                have b22066 := hb (x (-3) 1 && x (-3) 12)
                have b22067 := hb (x (-4) 2 && x (-4) 13)
                have b22068 := hb (x (-5) 3 && x (-5) 14)
                clear * - r22063 b22064 b22065 b22066 b22067 b22068 g5 d21883 d21927 d22021
                omega
              have d22069 : (x (-4) 13).toNat = 1 := by
                have r22070 := hand2 (x (-4) 2) (x (-4) 13)
                have b22071 := hb (x (-4) 13)
                have b22072 := hb (x (-4) 2 && x (-4) 13)
                clear * - r22070 b22071 b22072 d22062
                omega
              have d22073 : (x (-3) 12).toNat = 0 := by
                have r22074 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22075 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e22076 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b22077 := hb (x (-6) 3)
                have b22078 := hb (x (-5) 2)
                have b22079 := hb (x (-4) 13)
                have b22080 := hb (x (-3) 12)
                clear * - r22074 e22075 e22076 b22077 b22078 b22079 b22080 d22069 d22058
                omega
              have d22081 : (x (-6) 3).toNat = 0 := by
                have r22082 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22083 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                have e22084 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                have b22085 := hb (x (-6) 3)
                have b22086 := hb (x (-5) 2)
                have b22087 := hb (x (-4) 13)
                have b22088 := hb (x (-3) 12)
                clear * - r22082 e22083 e22084 b22085 b22086 b22087 b22088 d22073 d22069 d22058
                omega
              have d22089 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
                have r22090 := hand1 (x (-6) 3) (x (-6) 14)
                have b22091 := hb (x (-6) 3)
                have b22092 := hb (x (-6) 3 && x (-6) 14)
                clear * - r22090 b22091 b22092 d22081
                omega
              have d22093 : (x (-4) 1 && x (-4) 12).toNat = 1 := by
                have r22094 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b22095 := hb (x (-7) 4)
                have b22096 := hb (x (-3) 11)
                have b22097 := hb (x (-4) 1 && x (-4) 12)
                have b22098 := hb (x (-5) 2 && x (-5) 13)
                have b22099 := hb (x (-6) 3 && x (-6) 14)
                clear * - r22094 b22095 b22096 b22097 b22098 b22099 g2 d21879 d22089 d22046
                omega
              have d22100 : (x (-4) 12).toNat = 1 := by
                have r22101 := hand2 (x (-4) 1) (x (-4) 12)
                have b22102 := hb (x (-4) 12)
                have b22103 := hb (x (-4) 1 && x (-4) 12)
                clear * - r22101 b22102 b22103 d22093
                omega
              have d22104 : (x (-6) 2).toNat = 0 := by
                have r22105 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22106 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e22107 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b22108 := hb (x (-7) 3)
                have b22109 := hb (x (-6) 2)
                have b22110 := hb (x (-5) 13)
                have b22111 := hb (x (-4) 12)
                clear * - r22105 e22106 e22107 b22108 b22109 b22110 b22111 d22100 d21875
                omega
              have d22112 : (x (-7) 3).toNat = 0 := by
                have r22113 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e22114 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                have e22115 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                have b22116 := hb (x (-7) 3)
                have b22117 := hb (x (-6) 2)
                have b22118 := hb (x (-5) 13)
                have b22119 := hb (x (-4) 12)
                clear * - r22113 e22114 e22115 b22116 b22117 b22118 b22119 d22100 d21875 d22104
                omega
              have d22120 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
                have r22121 := hand1 (x (-7) 3) (x (-7) 14)
                have b22122 := hb (x (-7) 3)
                have b22123 := hb (x (-7) 3 && x (-7) 14)
                clear * - r22121 b22122 b22123 d22112
                omega
              have r22124 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22125 := hb (x (-8) 4)
              have b22126 := hb (x (-4) 11)
              have b22127 := hb (x (-5) 1 && x (-5) 12)
              have b22128 := hb (x (-6) 2 && x (-6) 13)
              have b22129 := hb (x (-7) 3 && x (-7) 14)
              linarith only [r22124, b22125, b22126, b22127, b22128, b22129, d21903, d21871, d21950, d22120, d22009]
          · have f22130 : (x (-1) 8).toNat = 1 := by rw [h19818]; rfl
            have d22131 : (x (-2) 9).toNat = 0 := by
              have r22132 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22133 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e22134 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e22135 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e22136 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e22137 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e22138 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b22139 := hb (x (-8) 7)
              have b22140 := hb (x (-7) 6)
              have b22141 := hb (x (-6) 5)
              have b22142 := hb (x (-5) 4)
              have b22143 := hb (x (-4) 11)
              have b22144 := hb (x (-3) 10)
              have b22145 := hb (x (-2) 9)
              have b22146 := hb (x (-1) 8)
              clear * - r22132 e22133 e22134 e22135 e22136 e22137 e22138 b22139 b22140 b22141 b22142 b22143 b22144 b22145 b22146 f22130
              omega
            have d22147 : (x (-3) 10).toNat = 0 := by
              have r22148 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22149 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e22150 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e22151 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e22152 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e22153 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e22154 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b22155 := hb (x (-8) 7)
              have b22156 := hb (x (-7) 6)
              have b22157 := hb (x (-6) 5)
              have b22158 := hb (x (-5) 4)
              have b22159 := hb (x (-4) 11)
              have b22160 := hb (x (-3) 10)
              have b22161 := hb (x (-2) 9)
              have b22162 := hb (x (-1) 8)
              clear * - r22148 e22149 e22150 e22151 e22152 e22153 e22154 b22155 b22156 b22157 b22158 b22159 b22160 b22161 b22162 f22130 d22131
              omega
            have d22163 : (x (-4) 11).toNat = 0 := by
              have r22164 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22165 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e22166 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e22167 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e22168 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e22169 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e22170 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b22171 := hb (x (-8) 7)
              have b22172 := hb (x (-7) 6)
              have b22173 := hb (x (-6) 5)
              have b22174 := hb (x (-5) 4)
              have b22175 := hb (x (-4) 11)
              have b22176 := hb (x (-3) 10)
              have b22177 := hb (x (-2) 9)
              have b22178 := hb (x (-1) 8)
              clear * - r22164 e22165 e22166 e22167 e22168 e22169 e22170 b22171 b22172 b22173 b22174 b22175 b22176 b22177 b22178 f22130 d22131 d22147
              omega
            have d22179 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
              have r22180 := hand2 (x (-4) 1) (x (-4) 11)
              have b22181 := hb (x (-4) 11)
              have b22182 := hb (x (-4) 1 && x (-4) 11)
              clear * - r22180 b22181 b22182 d22163
              omega
            have d22183 : (x (-5) 4).toNat = 0 := by
              have r22184 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22185 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e22186 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e22187 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e22188 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e22189 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e22190 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b22191 := hb (x (-8) 7)
              have b22192 := hb (x (-7) 6)
              have b22193 := hb (x (-6) 5)
              have b22194 := hb (x (-5) 4)
              have b22195 := hb (x (-4) 11)
              have b22196 := hb (x (-3) 10)
              have b22197 := hb (x (-2) 9)
              have b22198 := hb (x (-1) 8)
              clear * - r22184 e22185 e22186 e22187 e22188 e22189 e22190 b22191 b22192 b22193 b22194 b22195 b22196 b22197 b22198 f22130 d22131 d22147 d22163
              omega
            have d22199 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
              have r22200 := hand1 (x (-5) 4) (x (-5) 14)
              have b22201 := hb (x (-5) 4)
              have b22202 := hb (x (-5) 4 && x (-5) 14)
              clear * - r22200 b22201 b22202 d22183
              omega
            have d22203 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
              have r22204 := hand1 (x (-5) 4) (x (-5) 13)
              have b22205 := hb (x (-5) 4)
              have b22206 := hb (x (-5) 4 && x (-5) 13)
              clear * - r22204 b22205 b22206 d22183
              omega
            have d22207 : (x (-6) 5).toNat = 0 := by
              have r22208 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22209 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e22210 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e22211 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e22212 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e22213 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e22214 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b22215 := hb (x (-8) 7)
              have b22216 := hb (x (-7) 6)
              have b22217 := hb (x (-6) 5)
              have b22218 := hb (x (-5) 4)
              have b22219 := hb (x (-4) 11)
              have b22220 := hb (x (-3) 10)
              have b22221 := hb (x (-2) 9)
              have b22222 := hb (x (-1) 8)
              clear * - r22208 e22209 e22210 e22211 e22212 e22213 e22214 b22215 b22216 b22217 b22218 b22219 b22220 b22221 b22222 f22130 d22131 d22147 d22163 d22183
              omega
            have d22223 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
              have r22224 := hand1 (x (-6) 5) (x (-6) 14)
              have b22225 := hb (x (-6) 5)
              have b22226 := hb (x (-6) 5 && x (-6) 14)
              clear * - r22224 b22225 b22226 d22207
              omega
            have d22227 : (x (-7) 6).toNat = 0 := by
              have r22228 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22229 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
              have e22230 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
              have e22231 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
              have e22232 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
              have e22233 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
              have e22234 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
              have b22235 := hb (x (-8) 7)
              have b22236 := hb (x (-7) 6)
              have b22237 := hb (x (-6) 5)
              have b22238 := hb (x (-5) 4)
              have b22239 := hb (x (-4) 11)
              have b22240 := hb (x (-3) 10)
              have b22241 := hb (x (-2) 9)
              have b22242 := hb (x (-1) 8)
              clear * - r22228 e22229 e22230 e22231 e22232 e22233 e22234 b22235 b22236 b22237 b22238 b22239 b22240 b22241 b22242 f22130 d22131 d22147 d22163 d22183 d22207
              omega
            have d22243 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
              have r22244 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22245 := hb (x (-7) 6)
              have b22246 := hb (x (-1) 9)
              have b22247 := hb (x (-2) 1 && x (-2) 10)
              have b22248 := hb (x (-3) 2 && x (-3) 11)
              have b22249 := hb (x (-4) 3 && x (-4) 12)
              have b22250 := hb (x (-5) 4 && x (-5) 13)
              have b22251 := hb (x (-6) 5 && x (-6) 14)
              clear * - r22244 b22245 b22246 b22247 b22248 b22249 b22250 b22251 g9 g101 g102 d22203 d22223 d22227
              omega
            have d22252 : (x (-4) 12).toNat = 1 := by
              have r22253 := hand2 (x (-4) 3) (x (-4) 12)
              have b22254 := hb (x (-4) 12)
              have b22255 := hb (x (-4) 3 && x (-4) 12)
              clear * - r22253 b22254 b22255 d22243
              omega
            have d22256 : (x (-5) 13).toNat = 0 := by
              have r22257 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22258 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e22259 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b22260 := hb (x (-7) 3)
              have b22261 := hb (x (-6) 2)
              have b22262 := hb (x (-5) 13)
              have b22263 := hb (x (-4) 12)
              clear * - r22257 e22258 e22259 b22260 b22261 b22262 b22263 d22252
              omega
            have d22264 : (x (-6) 2).toNat = 0 := by
              have r22265 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22266 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e22267 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b22268 := hb (x (-7) 3)
              have b22269 := hb (x (-6) 2)
              have b22270 := hb (x (-5) 13)
              have b22271 := hb (x (-4) 12)
              clear * - r22265 e22266 e22267 b22268 b22269 b22270 b22271 d22252 d22256
              omega
            have d22272 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
              have r22273 := hand1 (x (-6) 2) (x (-6) 13)
              have b22274 := hb (x (-6) 2)
              have b22275 := hb (x (-6) 2 && x (-6) 13)
              clear * - r22273 b22274 b22275 d22264
              omega
            have d22276 : (x (-7) 3).toNat = 0 := by
              have r22277 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22278 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e22279 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b22280 := hb (x (-7) 3)
              have b22281 := hb (x (-6) 2)
              have b22282 := hb (x (-5) 13)
              have b22283 := hb (x (-4) 12)
              clear * - r22277 e22278 e22279 b22280 b22281 b22282 b22283 d22252 d22256 d22264
              omega
            have d22284 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
              have r22285 := hand1 (x (-7) 3) (x (-7) 14)
              have b22286 := hb (x (-7) 3)
              have b22287 := hb (x (-7) 3 && x (-7) 14)
              clear * - r22285 b22286 b22287 d22276
              omega
            have d22288 : (x (-7) 11).toNat = 0 := by
              have r22289 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
              have b22290 := hb (x (-7) 3)
              have b22291 := hb (x (-7) 11)
              clear * - r22289 b22290 b22291 d22276
              omega
            have d22292 : (x (-4) 3).toNat = 1 := by
              have r22293 := hand1 (x (-4) 3) (x (-4) 12)
              have b22294 := hb (x (-4) 3)
              have b22295 := hb (x (-4) 3 && x (-4) 12)
              clear * - r22293 b22294 b22295 d22243
              omega
            have d22296 : (x (-1) 12).toNat = 0 := by
              have r22297 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22298 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e22299 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b22300 := hb (x (-4) 3)
              have b22301 := hb (x (-3) 2)
              have b22302 := hb (x (-2) 13)
              have b22303 := hb (x (-1) 12)
              clear * - r22297 e22298 e22299 b22300 b22301 b22302 b22303 d22292
              omega
            have d22304 : (x (-2) 13).toNat = 0 := by
              have r22305 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22306 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e22307 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b22308 := hb (x (-4) 3)
              have b22309 := hb (x (-3) 2)
              have b22310 := hb (x (-2) 13)
              have b22311 := hb (x (-1) 12)
              clear * - r22305 e22306 e22307 b22308 b22309 b22310 b22311 d22296 d22292
              omega
            have d22312 : (x (-3) 2).toNat = 0 := by
              have r22313 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22314 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e22315 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b22316 := hb (x (-4) 3)
              have b22317 := hb (x (-3) 2)
              have b22318 := hb (x (-2) 13)
              have b22319 := hb (x (-1) 12)
              clear * - r22313 e22314 e22315 b22316 b22317 b22318 b22319 d22296 d22304 d22292
              omega
            have d22320 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
              have r22321 := hand1 (x (-3) 2) (x (-3) 12)
              have b22322 := hb (x (-3) 2)
              have b22323 := hb (x (-3) 2 && x (-3) 12)
              clear * - r22321 b22322 b22323 d22312
              omega
            have d22324 : (x (-4) 3 && x (-4) 13).toNat = 1 := by
              have r22325 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22326 := hb (x (-6) 5)
              have b22327 := hb (x (-1) 10)
              have b22328 := hb (x (-2) 1 && x (-2) 11)
              have b22329 := hb (x (-3) 2 && x (-3) 12)
              have b22330 := hb (x (-4) 3 && x (-4) 13)
              have b22331 := hb (x (-5) 4 && x (-5) 14)
              clear * - r22325 b22326 b22327 b22328 b22329 b22330 b22331 g10 g110 d22320 d22199 d22207
              omega
            have d22332 : (x (-4) 13).toNat = 1 := by
              have r22333 := hand2 (x (-4) 3) (x (-4) 13)
              have b22334 := hb (x (-4) 13)
              have b22335 := hb (x (-4) 3 && x (-4) 13)
              clear * - r22333 b22334 b22335 d22324
              omega
            have d22336 : (x (-4) 1).toNat = 1 := by
              have r22337 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
              have b22338 := hb (x (-4) 1)
              have b22339 := hb (x (-4) 13)
              clear * - r22337 b22338 b22339 d22332
              omega
            have d22340 : (x (-3) 14).toNat = 0 := by
              have r22341 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22342 := hb (x (-4) 1)
              have b22343 := hb (x (-3) 14)
              clear * - r22341 b22342 b22343 d22336
              omega
            have d22344 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
              have r22345 := hand2 (x (-3) 1) (x (-3) 14)
              have b22346 := hb (x (-3) 14)
              have b22347 := hb (x (-3) 1 && x (-3) 14)
              clear * - r22345 b22346 b22347 d22340
              omega
            have d22348 : (x (-4) 2).toNat = 1 := by
              have r22349 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22350 := hb (x (-4) 2)
              have b22351 := hb (x (-2) 13)
              have b22352 := hb (x (-3) 1 && x (-3) 14)
              clear * - r22349 b22350 b22351 b22352 d22304 d22344
              omega
            have d22353 : (x (-4) 14).toNat = 1 := by
              have r22354 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
              have b22355 := hb (x (-4) 2)
              have b22356 := hb (x (-4) 14)
              clear * - r22354 b22355 b22356 d22348
              omega
            have d22357 : (x (-5) 1).toNat = 0 := by
              have r22358 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22359 := hb (x (-5) 1)
              have b22360 := hb (x (-4) 14)
              clear * - r22358 b22359 b22360 d22353
              omega
            have d22361 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
              have r22362 := hand1 (x (-5) 1) (x (-5) 12)
              have b22363 := hb (x (-5) 1)
              have b22364 := hb (x (-5) 1 && x (-5) 12)
              clear * - r22362 b22363 b22364 d22357
              omega
            have d22365 : (x (-8) 4).toNat = 1 := by
              have r22366 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22367 := hb (x (-8) 4)
              have b22368 := hb (x (-4) 11)
              have b22369 := hb (x (-5) 1 && x (-5) 12)
              have b22370 := hb (x (-6) 2 && x (-6) 13)
              have b22371 := hb (x (-7) 3 && x (-7) 14)
              clear * - r22366 b22367 b22368 b22369 b22370 b22371 d22163 d22361 d22272 d22284
              omega
            have d22372 : (x (-8) 12).toNat = 1 := by
              have r22373 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
              have b22374 := hb (x (-8) 4)
              have b22375 := hb (x (-8) 12)
              clear * - r22373 b22374 b22375 d22365
              omega
            have d22376 : (x (-9) 13).toNat = 0 := by
              have r22377 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22378 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
              have e22379 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
              have b22380 := hb (x (-11) 3)
              have b22381 := hb (x (-10) 2)
              have b22382 := hb (x (-9) 13)
              have b22383 := hb (x (-8) 12)
              clear * - r22377 e22378 e22379 b22380 b22381 b22382 b22383 d22372
              omega
            have d22384 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
              have r22385 := hand2 (x (-9) 2) (x (-9) 13)
              have b22386 := hb (x (-9) 13)
              have b22387 := hb (x (-9) 2 && x (-9) 13)
              clear * - r22385 b22386 b22387 d22376
              omega
            have d22388 : (x (-10) 3 && x (-10) 14).toNat = 1 := by
              have r22389 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22390 := hb (x (-11) 4)
              have b22391 := hb (x (-7) 11)
              have b22392 := hb (x (-8) 1 && x (-8) 12)
              have b22393 := hb (x (-9) 2 && x (-9) 13)
              have b22394 := hb (x (-10) 3 && x (-10) 14)
              clear * - r22389 b22390 b22391 b22392 b22393 b22394 d22288 d19798 d22384 d19718
              omega
            have d22395 : (x (-10) 3).toNat = 1 := by
              have r22396 := hand1 (x (-10) 3) (x (-10) 14)
              have b22397 := hb (x (-10) 3)
              have b22398 := hb (x (-10) 3 && x (-10) 14)
              clear * - r22396 b22397 b22398 d22388
              omega
            have d22399 : (x (-7) 12).toNat = 0 := by
              have r22400 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22401 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e22402 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b22403 := hb (x (-10) 3)
              have b22404 := hb (x (-9) 2)
              have b22405 := hb (x (-8) 13)
              have b22406 := hb (x (-7) 12)
              clear * - r22400 e22401 e22402 b22403 b22404 b22405 b22406 d19806 d22395
              omega
            have d22407 : (x (-7) 4).toNat = 0 := by
              have r22408 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
              have b22409 := hb (x (-7) 4)
              have b22410 := hb (x (-7) 12)
              clear * - r22408 b22409 b22410 d22399
              omega
            have d22411 : (x (-7) 4 && x (-7) 14).toNat = 0 := by
              have r22412 := hand1 (x (-7) 4) (x (-7) 14)
              have b22413 := hb (x (-7) 4)
              have b22414 := hb (x (-7) 4 && x (-7) 14)
              clear * - r22412 b22413 b22414 d22407
              omega
            have d22415 : (x (-9) 2).toNat = 0 := by
              have r22416 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22417 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
              have e22418 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
              have b22419 := hb (x (-10) 3)
              have b22420 := hb (x (-9) 2)
              have b22421 := hb (x (-8) 13)
              have b22422 := hb (x (-7) 12)
              clear * - r22416 e22417 e22418 b22419 b22420 b22421 b22422 d22399 d19806 d22395
              omega
            have d22423 : (x (-7) 13).toNat = 1 := by
              have r22424 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22425 := hb (x (-9) 2)
              have b22426 := hb (x (-7) 13)
              have b22427 := hb (x (-8) 1 && x (-8) 14)
              clear * - r22424 b22425 b22426 b22427 d19794 d22415
              omega
            have d22428 : (x (-7) 1).toNat = 1 := by
              have r22429 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
              have b22430 := hb (x (-7) 1)
              have b22431 := hb (x (-7) 13)
              clear * - r22429 b22430 b22431 d22423
              omega
            have d22432 : (x (-6) 14).toNat = 0 := by
              have r22433 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22434 := hb (x (-7) 1)
              have b22435 := hb (x (-6) 14)
              clear * - r22433 b22434 b22435 d22428
              omega
            have d22436 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
              have r22437 := hand2 (x (-6) 1) (x (-6) 14)
              have b22438 := hb (x (-6) 14)
              have b22439 := hb (x (-6) 1 && x (-6) 14)
              clear * - r22437 b22438 b22439 d22432
              omega
            have d22440 : (x (-7) 2).toNat = 1 := by
              have r22441 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22442 := hb (x (-7) 2)
              have b22443 := hb (x (-5) 13)
              have b22444 := hb (x (-6) 1 && x (-6) 14)
              clear * - r22441 b22442 b22443 b22444 d22256 d22436
              omega
            have d22445 : (x (-5) 12).toNat = 0 := by
              have r22446 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e22447 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
              have e22448 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
              have b22449 := hb (x (-8) 3)
              have b22450 := hb (x (-7) 2)
              have b22451 := hb (x (-6) 13)
              have b22452 := hb (x (-5) 12)
              clear * - r22446 e22447 e22448 b22449 b22450 b22451 b22452 d22440
              omega
            have d22453 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
              have r22454 := hand2 (x (-5) 2) (x (-5) 12)
              have b22455 := hb (x (-5) 12)
              have b22456 := hb (x (-5) 2 && x (-5) 12)
              clear * - r22454 b22455 b22456 d22445
              omega
            have d22457 : (x (-6) 3 && x (-6) 13).toNat = 1 := by
              have r22458 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b22459 := hb (x (-8) 5)
              have b22460 := hb (x (-3) 10)
              have b22461 := hb (x (-4) 1 && x (-4) 11)
              have b22462 := hb (x (-5) 2 && x (-5) 12)
              have b22463 := hb (x (-6) 3 && x (-6) 13)
              have b22464 := hb (x (-7) 4 && x (-7) 14)
              clear * - r22458 b22459 b22460 b22461 b22462 b22463 b22464 d22147 d22179 d22453 d22411 d19814
              omega
            have d22465 : (x (-6) 13).toNat = 1 := by
              have r22466 := hand2 (x (-6) 3) (x (-6) 13)
              have b22467 := hb (x (-6) 13)
              have b22468 := hb (x (-6) 3 && x (-6) 13)
              clear * - r22466 b22467 b22468 d22457
              omega
            have r22469 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22470 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
            have e22471 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
            have b22472 := hb (x (-8) 3)
            have b22473 := hb (x (-7) 2)
            have b22474 := hb (x (-6) 13)
            have b22475 := hb (x (-5) 12)
            linarith only [r22469, e22470, e22471, b22472, b22473, b22474, b22475, d22445, d22465, d22440]
        · have f22476 : (x 1 7).toNat = 1 := by rw [h19645]; rfl
          have d22477 : (x 8 8).toNat = 0 := by
            have r22478 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22479 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e22480 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e22481 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e22482 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e22483 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e22484 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b22485 := hb (x 1 7)
            have b22486 := hb (x 2 6)
            have b22487 := hb (x 3 5)
            have b22488 := hb (x 4 4)
            have b22489 := hb (x 5 11)
            have b22490 := hb (x 6 10)
            have b22491 := hb (x 7 9)
            have b22492 := hb (x 8 8)
            clear * - r22478 e22479 e22480 e22481 e22482 e22483 e22484 b22485 b22486 b22487 b22488 b22489 b22490 b22491 b22492 f22476
            omega
          have d22493 : (x 8 1 && x 8 8).toNat = 0 := by
            have r22494 := hand2 (x 8 1) (x 8 8)
            have b22495 := hb (x 8 8)
            have b22496 := hb (x 8 1 && x 8 8)
            clear * - r22494 b22495 b22496 d22477
            omega
          have d22497 : (x 8 3 && x 8 8).toNat = 0 := by
            have r22498 := hand2 (x 8 3) (x 8 8)
            have b22499 := hb (x 8 8)
            have b22500 := hb (x 8 3 && x 8 8)
            clear * - r22498 b22499 b22500 d22477
            omega
          have d22501 : (x 7 9).toNat = 0 := by
            have r22502 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22503 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e22504 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e22505 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e22506 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e22507 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e22508 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b22509 := hb (x 1 7)
            have b22510 := hb (x 2 6)
            have b22511 := hb (x 3 5)
            have b22512 := hb (x 4 4)
            have b22513 := hb (x 5 11)
            have b22514 := hb (x 6 10)
            have b22515 := hb (x 7 9)
            have b22516 := hb (x 8 8)
            clear * - r22502 e22503 e22504 e22505 e22506 e22507 e22508 b22509 b22510 b22511 b22512 b22513 b22514 b22515 b22516 d22477 f22476
            omega
          have d22517 : (x 7 2 && x 7 9).toNat = 0 := by
            have r22518 := hand2 (x 7 2) (x 7 9)
            have b22519 := hb (x 7 9)
            have b22520 := hb (x 7 2 && x 7 9)
            clear * - r22518 b22519 b22520 d22501
            omega
          have d22521 : (x 7 4 && x 7 9).toNat = 0 := by
            have r22522 := hand2 (x 7 4) (x 7 9)
            have b22523 := hb (x 7 9)
            have b22524 := hb (x 7 4 && x 7 9)
            clear * - r22522 b22523 b22524 d22501
            omega
          have d22525 : (x 6 10).toNat = 0 := by
            have r22526 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22527 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e22528 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e22529 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e22530 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e22531 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e22532 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b22533 := hb (x 1 7)
            have b22534 := hb (x 2 6)
            have b22535 := hb (x 3 5)
            have b22536 := hb (x 4 4)
            have b22537 := hb (x 5 11)
            have b22538 := hb (x 6 10)
            have b22539 := hb (x 7 9)
            have b22540 := hb (x 8 8)
            clear * - r22526 e22527 e22528 e22529 e22530 e22531 e22532 b22533 b22534 b22535 b22536 b22537 b22538 b22539 b22540 d22477 d22501 f22476
            omega
          have d22541 : (x 6 1 && x 6 10).toNat = 0 := by
            have r22542 := hand2 (x 6 1) (x 6 10)
            have b22543 := hb (x 6 10)
            have b22544 := hb (x 6 1 && x 6 10)
            clear * - r22542 b22543 b22544 d22525
            omega
          have d22545 : (x 6 3 && x 6 10).toNat = 0 := by
            have r22546 := hand2 (x 6 3) (x 6 10)
            have b22547 := hb (x 6 10)
            have b22548 := hb (x 6 3 && x 6 10)
            clear * - r22546 b22547 b22548 d22525
            omega
          have d22549 : (x 6 5 && x 6 10).toNat = 0 := by
            have r22550 := hand2 (x 6 5) (x 6 10)
            have b22551 := hb (x 6 10)
            have b22552 := hb (x 6 5 && x 6 10)
            clear * - r22550 b22551 b22552 d22525
            omega
          have d22553 : (x 5 11).toNat = 0 := by
            have r22554 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22555 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e22556 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e22557 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e22558 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e22559 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e22560 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b22561 := hb (x 1 7)
            have b22562 := hb (x 2 6)
            have b22563 := hb (x 3 5)
            have b22564 := hb (x 4 4)
            have b22565 := hb (x 5 11)
            have b22566 := hb (x 6 10)
            have b22567 := hb (x 7 9)
            have b22568 := hb (x 8 8)
            clear * - r22554 e22555 e22556 e22557 e22558 e22559 e22560 b22561 b22562 b22563 b22564 b22565 b22566 b22567 b22568 d22477 d22501 d22525 f22476
            omega
          have d22569 : (x 5 1 && x 5 11).toNat = 0 := by
            have r22570 := hand2 (x 5 1) (x 5 11)
            have b22571 := hb (x 5 11)
            have b22572 := hb (x 5 1 && x 5 11)
            clear * - r22570 b22571 b22572 d22553
            omega
          have d22573 : (x 5 2 && x 5 11).toNat = 0 := by
            have r22574 := hand2 (x 5 2) (x 5 11)
            have b22575 := hb (x 5 11)
            have b22576 := hb (x 5 2 && x 5 11)
            clear * - r22574 b22575 b22576 d22553
            omega
          have d22577 : (x 4 3 && x 4 12).toNat = 1 := by
            have r22578 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22579 := hb (x 1 6)
            have b22580 := hb (x 7 9)
            have b22581 := hb (x 6 1 && x 6 10)
            have b22582 := hb (x 5 2 && x 5 11)
            have b22583 := hb (x 4 3 && x 4 12)
            have b22584 := hb (x 3 4 && x 3 13)
            have b22585 := hb (x 2 5 && x 2 14)
            clear * - r22578 b22579 b22580 b22581 b22582 b22583 b22584 b22585 d22501 d22541 d22573 g107 g108 g24
            omega
          have d22586 : (x 4 12).toNat = 1 := by
            have r22587 := hand2 (x 4 3) (x 4 12)
            have b22588 := hb (x 4 12)
            have b22589 := hb (x 4 3 && x 4 12)
            clear * - r22587 b22588 b22589 d22577
            omega
          have d22590 : (x 3 13).toNat = 0 := by
            have r22591 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22592 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e22593 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b22594 := hb (x 1 3)
            have b22595 := hb (x 2 2)
            have b22596 := hb (x 3 13)
            have b22597 := hb (x 4 12)
            clear * - r22591 e22592 e22593 b22594 b22595 b22596 b22597 d22586 f19644
            omega
          have d22598 : (x 3 3 && x 3 13).toNat = 0 := by
            have r22599 := hand2 (x 3 3) (x 3 13)
            have b22600 := hb (x 3 13)
            have b22601 := hb (x 3 3 && x 3 13)
            clear * - r22599 b22600 b22601 d22590
            omega
          have d22602 : (x 4 2 && x 4 12).toNat = 1 := by
            have r22603 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22604 := hb (x 1 5)
            have b22605 := hb (x 6 10)
            have b22606 := hb (x 5 1 && x 5 11)
            have b22607 := hb (x 4 2 && x 4 12)
            have b22608 := hb (x 3 3 && x 3 13)
            have b22609 := hb (x 2 4 && x 2 14)
            clear * - r22603 b22604 b22605 b22606 b22607 b22608 b22609 d22525 d22569 d22598 g114 g23
            omega
          have d22610 : (x 4 2).toNat = 1 := by
            have r22611 := hand1 (x 4 2) (x 4 12)
            have b22612 := hb (x 4 2)
            have b22613 := hb (x 4 2 && x 4 12)
            clear * - r22611 b22612 b22613 d22602
            omega
          have d22614 : (x 4 14).toNat = 1 := by
            have r22615 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
            have b22616 := hb (x 4 2)
            have b22617 := hb (x 4 14)
            clear * - r22615 b22616 b22617 d22610
            omega
          have d22618 : (x 3 1).toNat = 0 := by
            have r22619 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22620 := hb (x 3 1)
            have b22621 := hb (x 4 14)
            clear * - r22619 b22620 b22621 d22614
            omega
          have d22622 : (x 3 1 && x 3 14).toNat = 0 := by
            have r22623 := hand1 (x 3 1) (x 3 14)
            have b22624 := hb (x 3 1)
            have b22625 := hb (x 3 1 && x 3 14)
            clear * - r22623 b22624 b22625 d22618
            omega
          have d22626 : (x 6 12).toNat = 0 := by
            have r22627 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22628 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e22629 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b22630 := hb (x 3 3)
            have b22631 := hb (x 4 2)
            have b22632 := hb (x 5 13)
            have b22633 := hb (x 6 12)
            clear * - r22627 e22628 e22629 b22630 b22631 b22632 b22633 d22610
            omega
          have d22634 : (x 5 13).toNat = 0 := by
            have r22635 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22636 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e22637 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b22638 := hb (x 3 3)
            have b22639 := hb (x 4 2)
            have b22640 := hb (x 5 13)
            have b22641 := hb (x 6 12)
            clear * - r22635 e22636 e22637 b22638 b22639 b22640 b22641 d22626 d22610
            omega
          have d22642 : (x 3 6 && x 3 13).toNat = 0 := by
            have r22643 := hand2 (x 3 6) (x 3 13)
            have b22644 := hb (x 3 13)
            have b22645 := hb (x 3 6 && x 3 13)
            clear * - r22643 b22644 b22645 d22590
            omega
          have d22646 : (x 3 5).toNat = 0 := by
            have r22647 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
            have b22648 := hb (x 3 5)
            have b22649 := hb (x 3 13)
            clear * - r22647 b22648 b22649 d22590
            omega
          have d22650 : (x 3 5 && x 3 14).toNat = 0 := by
            have r22651 := hand1 (x 3 5) (x 3 14)
            have b22652 := hb (x 3 5)
            have b22653 := hb (x 3 5 && x 3 14)
            clear * - r22651 b22652 b22653 d22646
            omega
          have d22654 : (x 2 1 && x 2 14).toNat = 1 := by
            have r22655 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22656 := hb (x 1 2)
            have b22657 := hb (x 3 13)
            have b22658 := hb (x 2 1 && x 2 14)
            clear * - r22655 b22656 b22657 b22658 d22590 g21
            omega
          have d22659 : (x 2 1).toNat = 1 := by
            have r22660 := hand1 (x 2 1) (x 2 14)
            have b22661 := hb (x 2 1)
            have b22662 := hb (x 2 1 && x 2 14)
            clear * - r22660 b22661 b22662 d22654
            omega
          have d22663 : (x 3 14).toNat = 0 := by
            have r22664 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22665 := hb (x 2 1)
            have b22666 := hb (x 3 14)
            clear * - r22664 b22665 b22666 d22659
            omega
          have d22667 : (x 3 6).toNat = 0 := by
            have r22668 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
            have b22669 := hb (x 3 6)
            have b22670 := hb (x 3 14)
            clear * - r22668 b22669 b22670 d22663
            omega
          have d22671 : (x 3 2).toNat = 0 := by
            have r22672 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b22673 := hb (x 3 2)
            have b22674 := hb (x 3 14)
            clear * - r22672 b22673 b22674 d22663
            omega
          have d22675 : (x 4 1 && x 4 14).toNat = 1 := by
            have r22676 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22677 := hb (x 3 2)
            have b22678 := hb (x 5 13)
            have b22679 := hb (x 4 1 && x 4 14)
            clear * - r22676 b22677 b22678 b22679 d22634 d22671
            omega
          have d22680 : (x 4 1).toNat = 1 := by
            have r22681 := hand1 (x 4 1) (x 4 14)
            have b22682 := hb (x 4 1)
            have b22683 := hb (x 4 1 && x 4 14)
            clear * - r22681 b22682 b22683 d22675
            omega
          have d22684 : (x 5 14).toNat = 0 := by
            have r22685 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22686 := hb (x 4 1)
            have b22687 := hb (x 5 14)
            clear * - r22685 b22686 b22687 d22680
            omega
          have d22688 : (x 5 3 && x 5 14).toNat = 0 := by
            have r22689 := hand2 (x 5 3) (x 5 14)
            have b22690 := hb (x 5 14)
            have b22691 := hb (x 5 3 && x 5 14)
            clear * - r22689 b22690 b22691 d22684
            omega
          have d22692 : (x 5 6).toNat = 0 := by
            have r22693 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
            have b22694 := hb (x 5 6)
            have b22695 := hb (x 5 14)
            clear * - r22693 b22694 b22695 d22684
            omega
          have d22696 : (x 5 6 && x 5 11).toNat = 0 := by
            have r22697 := hand1 (x 5 6) (x 5 11)
            have b22698 := hb (x 5 6)
            have b22699 := hb (x 5 6 && x 5 11)
            clear * - r22697 b22698 b22699 d22692
            omega
          have d22700 : (x 5 2).toNat = 0 := by
            have r22701 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
            have b22702 := hb (x 5 2)
            have b22703 := hb (x 5 14)
            clear * - r22701 b22702 b22703 d22684
            omega
          have d22704 : (x 2 2).toNat = 0 := by
            have r22705 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22706 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
            have e22707 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
            have b22708 := hb (x 1 3)
            have b22709 := hb (x 2 2)
            have b22710 := hb (x 3 13)
            have b22711 := hb (x 4 12)
            clear * - r22705 e22706 e22707 b22708 b22709 b22710 b22711 d22586 d22590 f19644
            omega
          have d22712 : (x 4 13).toNat = 1 := by
            have r22713 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22714 := hb (x 2 2)
            have b22715 := hb (x 4 13)
            have b22716 := hb (x 3 1 && x 3 14)
            clear * - r22713 b22714 b22715 b22716 d22622 d22704
            omega
          have d22717 : (x 5 12).toNat = 0 := by
            have r22718 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22719 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e22720 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b22721 := hb (x 2 3)
            have b22722 := hb (x 3 2)
            have b22723 := hb (x 4 13)
            have b22724 := hb (x 5 12)
            clear * - r22718 e22719 e22720 b22721 b22722 b22723 b22724 d22712 d22671
            omega
          have d22725 : (x 5 3 && x 5 12).toNat = 0 := by
            have r22726 := hand2 (x 5 3) (x 5 12)
            have b22727 := hb (x 5 12)
            have b22728 := hb (x 5 3 && x 5 12)
            clear * - r22726 b22727 b22728 d22717
            omega
          have d22729 : (x 5 4).toNat = 0 := by
            have r22730 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b22731 := hb (x 5 4)
            have b22732 := hb (x 5 12)
            clear * - r22730 b22731 b22732 d22717
            omega
          have d22733 : (x 5 4 && x 5 11).toNat = 0 := by
            have r22734 := hand1 (x 5 4) (x 5 11)
            have b22735 := hb (x 5 4)
            have b22736 := hb (x 5 4 && x 5 11)
            clear * - r22734 b22735 b22736 d22729
            omega
          have d22737 : (x 4 3).toNat = 1 := by
            have r22738 := hand1 (x 4 3) (x 4 12)
            have b22739 := hb (x 4 3)
            have b22740 := hb (x 4 3 && x 4 12)
            clear * - r22738 b22739 b22740 d22577
            omega
          have d22741 : (x 7 12).toNat = 0 := by
            have r22742 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22743 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e22744 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b22745 := hb (x 4 3)
            have b22746 := hb (x 5 2)
            have b22747 := hb (x 6 13)
            have b22748 := hb (x 7 12)
            clear * - r22742 e22743 e22744 b22745 b22746 b22747 b22748 d22700 d22737
            omega
          have d22749 : (x 7 1 && x 7 12).toNat = 0 := by
            have r22750 := hand2 (x 7 1) (x 7 12)
            have b22751 := hb (x 7 12)
            have b22752 := hb (x 7 1 && x 7 12)
            clear * - r22750 b22751 b22752 d22741
            omega
          have d22753 : (x 7 4).toNat = 0 := by
            have r22754 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
            have b22755 := hb (x 7 4)
            have b22756 := hb (x 7 12)
            clear * - r22754 b22755 b22756 d22741
            omega
          have d22757 : (x 6 13).toNat = 0 := by
            have r22758 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22759 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
            have e22760 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
            have b22761 := hb (x 4 3)
            have b22762 := hb (x 5 2)
            have b22763 := hb (x 6 13)
            have b22764 := hb (x 7 12)
            clear * - r22758 e22759 e22760 b22761 b22762 b22763 b22764 d22741 d22700 d22737
            omega
          have d22765 : (x 6 2 && x 6 13).toNat = 0 := by
            have r22766 := hand2 (x 6 2) (x 6 13)
            have b22767 := hb (x 6 13)
            have b22768 := hb (x 6 2 && x 6 13)
            clear * - r22766 b22767 b22768 d22757
            omega
          have d22769 : (x 6 5).toNat = 0 := by
            have r22770 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
            have b22771 := hb (x 6 5)
            have b22772 := hb (x 6 13)
            clear * - r22770 b22771 b22772 d22757
            omega
          have d22773 : (x 4 4).toNat = 0 := by
            have r22774 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22775 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e22776 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e22777 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e22778 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e22779 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e22780 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b22781 := hb (x 1 7)
            have b22782 := hb (x 2 6)
            have b22783 := hb (x 3 5)
            have b22784 := hb (x 4 4)
            have b22785 := hb (x 5 11)
            have b22786 := hb (x 6 10)
            have b22787 := hb (x 7 9)
            have b22788 := hb (x 8 8)
            clear * - r22774 e22775 e22776 e22777 e22778 e22779 e22780 b22781 b22782 b22783 b22784 b22785 b22786 b22787 b22788 d22477 d22501 d22525 d22553 d22646 f22476
            omega
          have d22789 : (x 4 4 && x 4 13).toNat = 0 := by
            have r22790 := hand1 (x 4 4) (x 4 13)
            have b22791 := hb (x 4 4)
            have b22792 := hb (x 4 4 && x 4 13)
            clear * - r22790 b22791 b22792 d22773
            omega
          have d22793 : (x 8 11).toNat = 1 := by
            have r22794 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b22795 := hb (x 4 4)
            have b22796 := hb (x 8 11)
            have b22797 := hb (x 7 1 && x 7 12)
            have b22798 := hb (x 6 2 && x 6 13)
            have b22799 := hb (x 5 3 && x 5 14)
            clear * - r22794 b22795 b22796 b22797 b22798 b22799 d22749 d22765 d22688 d22773
            omega
          have d22800 : (x 8 3).toNat = 1 := by
            have r22801 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
            have b22802 := hb (x 8 3)
            have b22803 := hb (x 8 11)
            clear * - r22801 b22802 b22803 d22793
            omega
          have d22804 : (x 11 12).toNat = 0 := by
            have r22805 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22806 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e22807 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b22808 := hb (x 8 3)
            have b22809 := hb (x 9 2)
            have b22810 := hb (x 10 13)
            have b22811 := hb (x 11 12)
            clear * - r22805 e22806 e22807 b22808 b22809 b22810 b22811 d22800
            omega
          have d22812 : (x 10 13).toNat = 0 := by
            have r22813 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22814 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e22815 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b22816 := hb (x 8 3)
            have b22817 := hb (x 9 2)
            have b22818 := hb (x 10 13)
            have b22819 := hb (x 11 12)
            clear * - r22813 e22814 e22815 b22816 b22817 b22818 b22819 d22804 d22800
            omega
          have d22820 : (x 9 2).toNat = 0 := by
            have r22821 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22822 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
            have e22823 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
            have b22824 := hb (x 8 3)
            have b22825 := hb (x 9 2)
            have b22826 := hb (x 10 13)
            have b22827 := hb (x 11 12)
            clear * - r22821 e22822 e22823 b22824 b22825 b22826 b22827 d22804 d22812 d22800
            omega
          have d22828 : (x 9 2 && x 9 7).toNat = 0 := by
            have r22829 := hand1 (x 9 2) (x 9 7)
            have b22830 := hb (x 9 2)
            have b22831 := hb (x 9 2 && x 9 7)
            clear * - r22829 b22830 b22831 d22820
            omega
          have d22832 : (x 9 10).toNat = 0 := by
            have r22833 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
            have b22834 := hb (x 9 2)
            have b22835 := hb (x 9 10)
            clear * - r22833 b22834 b22835 d22820
            omega
          have d22836 : (x 11 8).toNat = 0 := by
            have r22837 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22838 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e22839 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e22840 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e22841 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e22842 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e22843 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b22844 := hb (x 4 7)
            have b22845 := hb (x 5 6)
            have b22846 := hb (x 6 5)
            have b22847 := hb (x 7 4)
            have b22848 := hb (x 8 11)
            have b22849 := hb (x 9 10)
            have b22850 := hb (x 10 9)
            have b22851 := hb (x 11 8)
            clear * - r22837 e22838 e22839 e22840 e22841 e22842 e22843 b22844 b22845 b22846 b22847 b22848 b22849 b22850 b22851 d22832 d22793 d22753 d22769 d22692
            omega
          have d22852 : (x 10 9).toNat = 0 := by
            have r22853 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22854 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e22855 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e22856 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e22857 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e22858 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e22859 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b22860 := hb (x 4 7)
            have b22861 := hb (x 5 6)
            have b22862 := hb (x 6 5)
            have b22863 := hb (x 7 4)
            have b22864 := hb (x 8 11)
            have b22865 := hb (x 9 10)
            have b22866 := hb (x 10 9)
            have b22867 := hb (x 11 8)
            clear * - r22853 e22854 e22855 e22856 e22857 e22858 e22859 b22860 b22861 b22862 b22863 b22864 b22865 b22866 b22867 d22836 d22832 d22793 d22753 d22769 d22692
            omega
          have d22868 : (x 4 7).toNat = 0 := by
            have r22869 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22870 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
            have e22871 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
            have e22872 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
            have e22873 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
            have e22874 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
            have e22875 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
            have b22876 := hb (x 4 7)
            have b22877 := hb (x 5 6)
            have b22878 := hb (x 6 5)
            have b22879 := hb (x 7 4)
            have b22880 := hb (x 8 11)
            have b22881 := hb (x 9 10)
            have b22882 := hb (x 10 9)
            have b22883 := hb (x 11 8)
            clear * - r22869 e22870 e22871 e22872 e22873 e22874 e22875 b22876 b22877 b22878 b22879 b22880 b22881 b22882 b22883 d22836 d22852 d22832 d22793 d22753 d22769 d22692
            omega
          have d22884 : (x 4 7 && x 4 12).toNat = 0 := by
            have r22885 := hand1 (x 4 7) (x 4 12)
            have b22886 := hb (x 4 7)
            have b22887 := hb (x 4 7 && x 4 12)
            clear * - r22885 b22886 b22887 d22868
            omega
          have d22888 : (x 2 6).toNat = 0 := by
            have r22889 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e22890 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e22891 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e22892 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e22893 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e22894 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e22895 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b22896 := hb (x 1 7)
            have b22897 := hb (x 2 6)
            have b22898 := hb (x 3 5)
            have b22899 := hb (x 4 4)
            have b22900 := hb (x 5 11)
            have b22901 := hb (x 6 10)
            have b22902 := hb (x 7 9)
            have b22903 := hb (x 8 8)
            clear * - r22889 e22890 e22891 e22892 e22893 e22894 e22895 b22896 b22897 b22898 b22899 b22900 b22901 b22902 b22903 d22477 d22501 d22525 d22553 d22773 d22646 f22476
            omega
          have r22904 : (x 15 1).toNat + (x 14 2).toNat + (x 13 3).toNat + (x 12 4).toNat + (x 11 5).toNat + (x 10 6).toNat + (x 9 7).toNat + (x 8 8).toNat + (x 7 9).toNat + (x 6 10).toNat + (x 5 11).toNat + (x 4 12).toNat + (x 3 13).toNat + (x 2 14).toNat = 3 := by have q := hcount 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r22905 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22906 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
          have e22907 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
          have e22908 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
          have e22909 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
          have e22910 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
          have e22911 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
          have r22912 : 1 ≤ (x 11 5).toNat + (x 10 1 && x 10 6).toNat + (x 9 2 && x 9 7).toNat + (x 8 3 && x 8 8).toNat + (x 7 4 && x 7 9).toNat + (x 6 5 && x 6 10).toNat + (x 5 6 && x 5 11).toNat + (x 4 7 && x 4 12).toNat + (x 3 8 && x 3 13).toNat + (x 2 9 && x 2 14).toNat + (x 1 10).toNat := by have q := hcov5 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r22913 : 1 ≤ (x 9 7).toNat + (x 8 1 && x 8 8).toNat + (x 7 2 && x 7 9).toNat + (x 6 3 && x 6 10).toNat + (x 5 4 && x 5 11).toNat + (x 4 5 && x 4 12).toNat + (x 3 6 && x 3 13).toNat + (x 2 7 && x 2 14).toNat + (x 1 8).toNat := by have q := hcov7 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r22914 : 1 ≤ (x 8 9).toNat + (x 7 1 && x 7 10).toNat + (x 6 2 && x 6 11).toNat + (x 5 3 && x 5 12).toNat + (x 4 4 && x 4 13).toNat + (x 3 5 && x 3 14).toNat + (x 2 6).toNat := by have q := hcov9 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r22915 := hand2 (x 10 1) (x 10 6)
          have r22916 := hand1 (x 4 5) (x 4 12)
          have r22917 := hand1 (x 2 7) (x 2 14)
          have r22918 := hand2 (x 7 1) (x 7 10)
          have r22919 := hand2 (x 6 2) (x 6 11)
          linarith only [r22904, r22905, e22906, e22907, e22908, e22909, e22910, e22911, r22912, r22913, r22914, r22915, r22916, r22917, r22918, r22919, g25, g26, d22888, d19639, d22667, d22590, d22586, d22729, d22553, d22525, d22501, d22477, d22828, d22497, d22521, d22549, d22696, d22884, g64, g65, d22493, d22517, d22545, d22733, d22642, d22725, d22789, d22650]
      · have f22966 : (x 1 3).toNat = 1 := by rw [h19643]; rfl
        have d22967 : (x 4 12).toNat = 0 := by
          have r22968 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22969 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e22970 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b22971 := hb (x 1 3)
          have b22972 := hb (x 2 2)
          have b22973 := hb (x 3 13)
          have b22974 := hb (x 4 12)
          clear * - r22968 e22969 e22970 b22971 b22972 b22973 b22974 f22966
          omega
        have d22975 : (x 4 1 && x 4 12).toNat = 0 := by
          have r22976 := hand2 (x 4 1) (x 4 12)
          have b22977 := hb (x 4 12)
          have b22978 := hb (x 4 1 && x 4 12)
          clear * - r22976 b22977 b22978 d22967
          omega
        have d22979 : (x 4 4).toNat = 0 := by
          have r22980 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b22981 := hb (x 4 4)
          have b22982 := hb (x 4 12)
          clear * - r22980 b22981 b22982 d22967
          omega
        have d22983 : (x 3 13).toNat = 0 := by
          have r22984 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e22985 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e22986 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b22987 := hb (x 1 3)
          have b22988 := hb (x 2 2)
          have b22989 := hb (x 3 13)
          have b22990 := hb (x 4 12)
          clear * - r22984 e22985 e22986 b22987 b22988 b22989 b22990 d22967 f22966
          omega
        have d22991 : (x 3 2 && x 3 13).toNat = 0 := by
          have r22992 := hand2 (x 3 2) (x 3 13)
          have b22993 := hb (x 3 13)
          have b22994 := hb (x 3 2 && x 3 13)
          clear * - r22992 b22993 b22994 d22983
          omega
        have d22995 : (x 2 1 && x 2 14).toNat = 1 := by
          have r22996 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b22997 := hb (x 1 2)
          have b22998 := hb (x 3 13)
          have b22999 := hb (x 2 1 && x 2 14)
          clear * - r22996 b22997 b22998 b22999 d22983 g21
          omega
        have d23000 : (x 2 1).toNat = 1 := by
          have r23001 := hand1 (x 2 1) (x 2 14)
          have b23002 := hb (x 2 1)
          have b23003 := hb (x 2 1 && x 2 14)
          clear * - r23001 b23002 b23003 d22995
          omega
        have d23004 : (x 3 14).toNat = 0 := by
          have r23005 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23006 := hb (x 2 1)
          have b23007 := hb (x 3 14)
          clear * - r23005 b23006 b23007 d23000
          omega
        have d23008 : (x 3 1 && x 3 14).toNat = 0 := by
          have r23009 := hand2 (x 3 1) (x 3 14)
          have b23010 := hb (x 3 14)
          have b23011 := hb (x 3 1 && x 3 14)
          clear * - r23009 b23010 b23011 d23004
          omega
        have d23012 : (x 3 2).toNat = 0 := by
          have r23013 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
          have b23014 := hb (x 3 2)
          have b23015 := hb (x 3 14)
          clear * - r23013 b23014 b23015 d23004
          omega
        have d23016 : (x 2 2).toNat = 0 := by
          have r23017 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23018 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e23019 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b23020 := hb (x 1 3)
          have b23021 := hb (x 2 2)
          have b23022 := hb (x 3 13)
          have b23023 := hb (x 4 12)
          clear * - r23017 e23018 e23019 b23020 b23021 b23022 b23023 d22967 d22983 f22966
          omega
        have d23024 : (x 4 13).toNat = 1 := by
          have r23025 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23026 := hb (x 2 2)
          have b23027 := hb (x 4 13)
          have b23028 := hb (x 3 1 && x 3 14)
          clear * - r23025 b23026 b23027 b23028 d23008 d23016
          omega
        have d23029 : (x 4 1).toNat = 1 := by
          have r23030 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
          have b23031 := hb (x 4 1)
          have b23032 := hb (x 4 13)
          clear * - r23030 b23031 b23032 d23024
          omega
        have d23033 : (x 5 14).toNat = 0 := by
          have r23034 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23035 := hb (x 4 1)
          have b23036 := hb (x 5 14)
          clear * - r23034 b23035 b23036 d23029
          omega
        have d23037 : (x 5 3 && x 5 14).toNat = 0 := by
          have r23038 := hand2 (x 5 3) (x 5 14)
          have b23039 := hb (x 5 14)
          have b23040 := hb (x 5 3 && x 5 14)
          clear * - r23038 b23039 b23040 d23033
          omega
        have d23041 : (x 5 2).toNat = 0 := by
          have r23042 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b23043 := hb (x 5 2)
          have b23044 := hb (x 5 14)
          clear * - r23042 b23043 b23044 d23033
          omega
        have d23045 : (x 5 12).toNat = 0 := by
          have r23046 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23047 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e23048 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b23049 := hb (x 2 3)
          have b23050 := hb (x 3 2)
          have b23051 := hb (x 4 13)
          have b23052 := hb (x 5 12)
          clear * - r23046 e23047 e23048 b23049 b23050 b23051 b23052 d23024 d23012
          omega
        have d23053 : (x 5 4).toNat = 0 := by
          have r23054 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
          have b23055 := hb (x 5 4)
          have b23056 := hb (x 5 12)
          clear * - r23054 b23055 b23056 d23045
          omega
        have d23057 : (x 2 3).toNat = 0 := by
          have r23058 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23059 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e23060 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b23061 := hb (x 2 3)
          have b23062 := hb (x 3 2)
          have b23063 := hb (x 4 13)
          have b23064 := hb (x 5 12)
          clear * - r23058 e23059 e23060 b23061 b23062 b23063 b23064 d23045 d23024 d23012
          omega
        have d23065 : (x 2 3 && x 2 14).toNat = 0 := by
          have r23066 := hand1 (x 2 3) (x 2 14)
          have b23067 := hb (x 2 3)
          have b23068 := hb (x 2 3 && x 2 14)
          clear * - r23066 b23067 b23068 d23057
          omega
        have d23069 : (x 5 11).toNat = 1 := by
          have r23070 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23071 := hb (x 1 4)
          have b23072 := hb (x 5 11)
          have b23073 := hb (x 4 1 && x 4 12)
          have b23074 := hb (x 3 2 && x 3 13)
          have b23075 := hb (x 2 3 && x 2 14)
          clear * - r23070 b23071 b23072 b23073 b23074 b23075 d22975 d22991 d23065 g22
          omega
        have d23076 : (x 5 3).toNat = 1 := by
          have r23077 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have b23078 := hb (x 5 3)
          have b23079 := hb (x 5 11)
          clear * - r23077 b23078 b23079 d23069
          omega
        have d23080 : (x 8 12).toNat = 0 := by
          have r23081 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23082 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e23083 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b23084 := hb (x 5 3)
          have b23085 := hb (x 6 2)
          have b23086 := hb (x 7 13)
          have b23087 := hb (x 8 12)
          clear * - r23081 e23082 e23083 b23084 b23085 b23086 b23087 d23076
          omega
        have d23088 : (x 8 1 && x 8 12).toNat = 0 := by
          have r23089 := hand2 (x 8 1) (x 8 12)
          have b23090 := hb (x 8 12)
          have b23091 := hb (x 8 1 && x 8 12)
          clear * - r23089 b23090 b23091 d23080
          omega
        have d23092 : (x 8 4).toNat = 0 := by
          have r23093 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
          have b23094 := hb (x 8 4)
          have b23095 := hb (x 8 12)
          clear * - r23093 b23094 b23095 d23080
          omega
        have d23096 : (x 7 13).toNat = 0 := by
          have r23097 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23098 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e23099 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b23100 := hb (x 5 3)
          have b23101 := hb (x 6 2)
          have b23102 := hb (x 7 13)
          have b23103 := hb (x 8 12)
          clear * - r23097 e23098 e23099 b23100 b23101 b23102 b23103 d23080 d23076
          omega
        have d23104 : (x 7 2 && x 7 13).toNat = 0 := by
          have r23105 := hand2 (x 7 2) (x 7 13)
          have b23106 := hb (x 7 13)
          have b23107 := hb (x 7 2 && x 7 13)
          clear * - r23105 b23106 b23107 d23096
          omega
        have d23108 : (x 6 1 && x 6 14).toNat = 1 := by
          have r23109 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23110 := hb (x 5 2)
          have b23111 := hb (x 7 13)
          have b23112 := hb (x 6 1 && x 6 14)
          clear * - r23109 b23110 b23111 b23112 d23096 d23041
          omega
        have d23113 : (x 6 1).toNat = 1 := by
          have r23114 := hand1 (x 6 1) (x 6 14)
          have b23115 := hb (x 6 1)
          have b23116 := hb (x 6 1 && x 6 14)
          clear * - r23114 b23115 b23116 d23108
          omega
        have d23117 : (x 7 14).toNat = 0 := by
          have r23118 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23119 := hb (x 6 1)
          have b23120 := hb (x 7 14)
          clear * - r23118 b23119 b23120 d23113
          omega
        have d23121 : (x 7 1 && x 7 14).toNat = 0 := by
          have r23122 := hand2 (x 7 1) (x 7 14)
          have b23123 := hb (x 7 14)
          have b23124 := hb (x 7 1 && x 7 14)
          clear * - r23122 b23123 b23124 d23117
          omega
        have d23125 : (x 7 2).toNat = 0 := by
          have r23126 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b23127 := hb (x 7 2)
          have b23128 := hb (x 7 14)
          clear * - r23126 b23127 b23128 d23117
          omega
        have d23129 : (x 6 2).toNat = 0 := by
          have r23130 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23131 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e23132 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have b23133 := hb (x 5 3)
          have b23134 := hb (x 6 2)
          have b23135 := hb (x 7 13)
          have b23136 := hb (x 8 12)
          clear * - r23130 e23131 e23132 b23133 b23134 b23135 b23136 d23080 d23096 d23076
          omega
        have d23137 : (x 6 2 && x 6 13).toNat = 0 := by
          have r23138 := hand1 (x 6 2) (x 6 13)
          have b23139 := hb (x 6 2)
          have b23140 := hb (x 6 2 && x 6 13)
          clear * - r23138 b23139 b23140 d23129
          omega
        have d23141 : (x 8 13).toNat = 1 := by
          have r23142 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23143 := hb (x 6 2)
          have b23144 := hb (x 8 13)
          have b23145 := hb (x 7 1 && x 7 14)
          clear * - r23142 b23143 b23144 b23145 d23121 d23129
          omega
        have d23146 : (x 8 1).toNat = 1 := by
          have r23147 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
          have b23148 := hb (x 8 1)
          have b23149 := hb (x 8 13)
          clear * - r23147 b23148 b23149 d23141
          omega
        have d23150 : (x 9 14).toNat = 0 := by
          have r23151 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23152 := hb (x 8 1)
          have b23153 := hb (x 9 14)
          clear * - r23151 b23152 b23153 d23146
          omega
        have d23154 : (x 9 3 && x 9 14).toNat = 0 := by
          have r23155 := hand2 (x 9 3) (x 9 14)
          have b23156 := hb (x 9 14)
          have b23157 := hb (x 9 3 && x 9 14)
          clear * - r23155 b23156 b23157 d23150
          omega
        have d23158 : (x 9 2).toNat = 0 := by
          have r23159 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b23160 := hb (x 9 2)
          have b23161 := hb (x 9 14)
          clear * - r23159 b23160 b23161 d23150
          omega
        have d23162 : (x 9 12).toNat = 0 := by
          have r23163 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23164 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e23165 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b23166 := hb (x 6 3)
          have b23167 := hb (x 7 2)
          have b23168 := hb (x 8 13)
          have b23169 := hb (x 9 12)
          clear * - r23163 e23164 e23165 b23166 b23167 b23168 b23169 d23141 d23125
          omega
        have d23170 : (x 9 4).toNat = 0 := by
          have r23171 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
          have b23172 := hb (x 9 4)
          have b23173 := hb (x 9 12)
          clear * - r23171 b23172 b23173 d23162
          omega
        have d23174 : (x 6 3).toNat = 0 := by
          have r23175 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23176 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e23177 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b23178 := hb (x 6 3)
          have b23179 := hb (x 7 2)
          have b23180 := hb (x 8 13)
          have b23181 := hb (x 9 12)
          clear * - r23175 e23176 e23177 b23178 b23179 b23180 b23181 d23162 d23141 d23125
          omega
        have d23182 : (x 6 3 && x 6 14).toNat = 0 := by
          have r23183 := hand1 (x 6 3) (x 6 14)
          have b23184 := hb (x 6 3)
          have b23185 := hb (x 6 3 && x 6 14)
          clear * - r23183 b23184 b23185 d23174
          omega
        have d23186 : (x 9 11).toNat = 1 := by
          have r23187 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23188 := hb (x 5 4)
          have b23189 := hb (x 9 11)
          have b23190 := hb (x 8 1 && x 8 12)
          have b23191 := hb (x 7 2 && x 7 13)
          have b23192 := hb (x 6 3 && x 6 14)
          clear * - r23187 b23188 b23189 b23190 b23191 b23192 d23088 d23104 d23182 d23053
          omega
        have d23193 : (x 9 3).toNat = 1 := by
          have r23194 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
          have b23195 := hb (x 9 3)
          have b23196 := hb (x 9 11)
          clear * - r23194 b23195 b23196 d23186
          omega
        have d23197 : (x 12 12).toNat = 0 := by
          have r23198 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23199 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e23200 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b23201 := hb (x 9 3)
          have b23202 := hb (x 10 2)
          have b23203 := hb (x 11 13)
          have b23204 := hb (x 12 12)
          clear * - r23198 e23199 e23200 b23201 b23202 b23203 b23204 d23193
          omega
        have d23205 : (x 12 1 && x 12 12).toNat = 0 := by
          have r23206 := hand2 (x 12 1) (x 12 12)
          have b23207 := hb (x 12 12)
          have b23208 := hb (x 12 1 && x 12 12)
          clear * - r23206 b23207 b23208 d23197
          omega
        have d23209 : (x 12 4).toNat = 0 := by
          have r23210 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
          have b23211 := hb (x 12 4)
          have b23212 := hb (x 12 12)
          clear * - r23210 b23211 b23212 d23197
          omega
        have d23213 : (x 11 13).toNat = 0 := by
          have r23214 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23215 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e23216 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b23217 := hb (x 9 3)
          have b23218 := hb (x 10 2)
          have b23219 := hb (x 11 13)
          have b23220 := hb (x 12 12)
          clear * - r23214 e23215 e23216 b23217 b23218 b23219 b23220 d23197 d23193
          omega
        have d23221 : (x 11 2 && x 11 13).toNat = 0 := by
          have r23222 := hand2 (x 11 2) (x 11 13)
          have b23223 := hb (x 11 13)
          have b23224 := hb (x 11 2 && x 11 13)
          clear * - r23222 b23223 b23224 d23213
          omega
        have d23225 : (x 10 1 && x 10 14).toNat = 1 := by
          have r23226 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23227 := hb (x 9 2)
          have b23228 := hb (x 11 13)
          have b23229 := hb (x 10 1 && x 10 14)
          clear * - r23226 b23227 b23228 b23229 d23213 d23158
          omega
        have d23230 : (x 10 14).toNat = 1 := by
          have r23231 := hand2 (x 10 1) (x 10 14)
          have b23232 := hb (x 10 14)
          have b23233 := hb (x 10 1 && x 10 14)
          clear * - r23231 b23232 b23233 d23225
          omega
        have d23234 : (x 9 1).toNat = 0 := by
          have r23235 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23236 := hb (x 9 1)
          have b23237 := hb (x 10 14)
          clear * - r23235 b23236 b23237 d23230
          omega
        have d23238 : (x 9 13).toNat = 0 := by
          have r23239 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
          have b23240 := hb (x 9 1)
          have b23241 := hb (x 9 13)
          clear * - r23239 b23240 b23241 d23234
          omega
        have d23242 : (x 8 1 && x 8 14).toNat = 1 := by
          have r23243 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23244 := hb (x 7 2)
          have b23245 := hb (x 9 13)
          have b23246 := hb (x 8 1 && x 8 14)
          clear * - r23243 b23244 b23245 b23246 d23238 d23125
          omega
        have d23247 : (x 8 14).toNat = 1 := by
          have r23248 := hand2 (x 8 1) (x 8 14)
          have b23249 := hb (x 8 14)
          have b23250 := hb (x 8 1 && x 8 14)
          clear * - r23248 b23249 b23250 d23242
          omega
        have d23251 : (x 7 1).toNat = 0 := by
          have r23252 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23253 := hb (x 7 1)
          have b23254 := hb (x 8 14)
          clear * - r23252 b23253 b23254 d23247
          omega
        have d23255 : (x 7 1 && x 7 12).toNat = 0 := by
          have r23256 := hand1 (x 7 1) (x 7 12)
          have b23257 := hb (x 7 1)
          have b23258 := hb (x 7 1 && x 7 12)
          clear * - r23256 b23257 b23258 d23251
          omega
        have d23259 : (x 8 11).toNat = 1 := by
          have r23260 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23261 := hb (x 4 4)
          have b23262 := hb (x 8 11)
          have b23263 := hb (x 7 1 && x 7 12)
          have b23264 := hb (x 6 2 && x 6 13)
          have b23265 := hb (x 5 3 && x 5 14)
          clear * - r23260 b23261 b23262 b23263 b23264 b23265 d23255 d23137 d23037 d22979
          omega
        have d23266 : (x 8 3).toNat = 1 := by
          have r23267 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
          have b23268 := hb (x 8 3)
          have b23269 := hb (x 8 11)
          clear * - r23267 b23268 b23269 d23259
          omega
        have d23270 : (x 11 12).toNat = 0 := by
          have r23271 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23272 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e23273 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b23274 := hb (x 8 3)
          have b23275 := hb (x 9 2)
          have b23276 := hb (x 10 13)
          have b23277 := hb (x 11 12)
          clear * - r23271 e23272 e23273 b23274 b23275 b23276 b23277 d23158 d23266
          omega
        have d23278 : (x 11 1 && x 11 12).toNat = 0 := by
          have r23279 := hand2 (x 11 1) (x 11 12)
          have b23280 := hb (x 11 12)
          have b23281 := hb (x 11 1 && x 11 12)
          clear * - r23279 b23280 b23281 d23270
          omega
        have d23282 : (x 10 13).toNat = 0 := by
          have r23283 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23284 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e23285 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b23286 := hb (x 8 3)
          have b23287 := hb (x 9 2)
          have b23288 := hb (x 10 13)
          have b23289 := hb (x 11 12)
          clear * - r23283 e23284 e23285 b23286 b23287 b23288 b23289 d23270 d23158 d23266
          omega
        have d23290 : (x 10 2 && x 10 13).toNat = 0 := by
          have r23291 := hand2 (x 10 2) (x 10 13)
          have b23292 := hb (x 10 13)
          have b23293 := hb (x 10 2 && x 10 13)
          clear * - r23291 b23292 b23293 d23282
          omega
        have d23294 : (x 12 11).toNat = 1 := by
          have r23295 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23296 := hb (x 8 4)
          have b23297 := hb (x 12 11)
          have b23298 := hb (x 11 1 && x 11 12)
          have b23299 := hb (x 10 2 && x 10 13)
          have b23300 := hb (x 9 3 && x 9 14)
          clear * - r23295 b23296 b23297 b23298 b23299 b23300 d23278 d23290 d23154 d23092
          omega
        have d23301 : (x 12 3).toNat = 1 := by
          have r23302 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
          have b23303 := hb (x 12 3)
          have b23304 := hb (x 12 11)
          clear * - r23302 b23303 b23304 d23294
          omega
        have d23305 : (x 15 12).toNat = 0 := by
          have r23306 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23307 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e23308 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b23309 := hb (x 12 3)
          have b23310 := hb (x 13 2)
          have b23311 := hb (x 14 13)
          have b23312 := hb (x 15 12)
          clear * - r23306 e23307 e23308 b23309 b23310 b23311 b23312 d23301
          omega
        have d23313 : (x 15 1 && x 15 12).toNat = 0 := by
          have r23314 := hand2 (x 15 1) (x 15 12)
          have b23315 := hb (x 15 12)
          have b23316 := hb (x 15 1 && x 15 12)
          clear * - r23314 b23315 b23316 d23305
          omega
        have d23317 : (x 14 13).toNat = 0 := by
          have r23318 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23319 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e23320 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b23321 := hb (x 12 3)
          have b23322 := hb (x 13 2)
          have b23323 := hb (x 14 13)
          have b23324 := hb (x 15 12)
          clear * - r23318 e23319 e23320 b23321 b23322 b23323 b23324 d23305 d23301
          omega
        have d23325 : (x 14 2 && x 14 13).toNat = 0 := by
          have r23326 := hand2 (x 14 2) (x 14 13)
          have b23327 := hb (x 14 13)
          have b23328 := hb (x 14 2 && x 14 13)
          clear * - r23326 b23327 b23328 d23317
          omega
        have d23329 : (x 13 2).toNat = 0 := by
          have r23330 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23331 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e23332 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b23333 := hb (x 12 3)
          have b23334 := hb (x 13 2)
          have b23335 := hb (x 14 13)
          have b23336 := hb (x 15 12)
          clear * - r23330 e23331 e23332 b23333 b23334 b23335 b23336 d23305 d23317 d23301
          omega
        have d23337 : (x 10 1).toNat = 1 := by
          have r23338 := hand1 (x 10 1) (x 10 14)
          have b23339 := hb (x 10 1)
          have b23340 := hb (x 10 1 && x 10 14)
          clear * - r23338 b23339 b23340 d23225
          omega
        have d23341 : (x 11 14).toNat = 0 := by
          have r23342 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23343 := hb (x 10 1)
          have b23344 := hb (x 11 14)
          clear * - r23342 b23343 b23344 d23337
          omega
        have d23345 : (x 11 1 && x 11 14).toNat = 0 := by
          have r23346 := hand2 (x 11 1) (x 11 14)
          have b23347 := hb (x 11 14)
          have b23348 := hb (x 11 1 && x 11 14)
          clear * - r23346 b23347 b23348 d23341
          omega
        have d23349 : (x 11 2).toNat = 0 := by
          have r23350 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
          have b23351 := hb (x 11 2)
          have b23352 := hb (x 11 14)
          clear * - r23350 b23351 b23352 d23341
          omega
        have d23353 : (x 10 2).toNat = 0 := by
          have r23354 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23355 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e23356 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b23357 := hb (x 9 3)
          have b23358 := hb (x 10 2)
          have b23359 := hb (x 11 13)
          have b23360 := hb (x 12 12)
          clear * - r23354 e23355 e23356 b23357 b23358 b23359 b23360 d23197 d23213 d23193
          omega
        have d23361 : (x 12 13).toNat = 1 := by
          have r23362 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23363 := hb (x 10 2)
          have b23364 := hb (x 12 13)
          have b23365 := hb (x 11 1 && x 11 14)
          clear * - r23362 b23363 b23364 b23365 d23345 d23353
          omega
        have d23366 : (x 12 1).toNat = 1 := by
          have r23367 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
          have b23368 := hb (x 12 1)
          have b23369 := hb (x 12 13)
          clear * - r23367 b23368 b23369 d23361
          omega
        have d23370 : (x 13 14).toNat = 0 := by
          have r23371 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23372 := hb (x 12 1)
          have b23373 := hb (x 13 14)
          clear * - r23371 b23372 b23373 d23366
          omega
        have d23374 : (x 13 1 && x 13 14).toNat = 0 := by
          have r23375 := hand2 (x 13 1) (x 13 14)
          have b23376 := hb (x 13 14)
          have b23377 := hb (x 13 1 && x 13 14)
          clear * - r23375 b23376 b23377 d23370
          omega
        have d23378 : (x 12 2).toNat = 1 := by
          have r23379 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23380 := hb (x 12 2)
          have b23381 := hb (x 14 13)
          have b23382 := hb (x 13 1 && x 13 14)
          clear * - r23379 b23380 b23381 b23382 d23317 d23374
          omega
        have d23383 : (x 14 12).toNat = 0 := by
          have r23384 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23385 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e23386 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b23387 := hb (x 11 3)
          have b23388 := hb (x 12 2)
          have b23389 := hb (x 13 13)
          have b23390 := hb (x 14 12)
          clear * - r23384 e23385 e23386 b23387 b23388 b23389 b23390 d23378
          omega
        have d23391 : (x 14 4).toNat = 0 := by
          have r23392 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
          have b23393 := hb (x 14 4)
          have b23394 := hb (x 14 12)
          clear * - r23392 b23393 b23394 d23383
          omega
        have d23395 : (x 14 4 && x 14 14).toNat = 0 := by
          have r23396 := hand1 (x 14 4) (x 14 14)
          have b23397 := hb (x 14 4)
          have b23398 := hb (x 14 4 && x 14 14)
          clear * - r23396 b23397 b23398 d23391
          omega
        have d23399 : (x 13 13).toNat = 0 := by
          have r23400 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23401 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e23402 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b23403 := hb (x 11 3)
          have b23404 := hb (x 12 2)
          have b23405 := hb (x 13 13)
          have b23406 := hb (x 14 12)
          clear * - r23400 e23401 e23402 b23403 b23404 b23405 b23406 d23383 d23378
          omega
        have d23407 : (x 13 5).toNat = 0 := by
          have r23408 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
          have b23409 := hb (x 13 5)
          have b23410 := hb (x 13 13)
          clear * - r23408 b23409 b23410 d23399
          omega
        have d23411 : (x 13 3 && x 13 14).toNat = 0 := by
          have r23412 := hand2 (x 13 3) (x 13 14)
          have b23413 := hb (x 13 14)
          have b23414 := hb (x 13 3 && x 13 14)
          clear * - r23412 b23413 b23414 d23370
          omega
        have d23415 : (x 16 11).toNat = 1 := by
          have r23416 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23417 := hb (x 12 4)
          have b23418 := hb (x 16 11)
          have b23419 := hb (x 15 1 && x 15 12)
          have b23420 := hb (x 14 2 && x 14 13)
          have b23421 := hb (x 13 3 && x 13 14)
          clear * - r23416 b23417 b23418 b23419 b23420 b23421 d23313 d23325 d23411 d23209
          omega
        have d23422 : (x 16 3).toNat = 1 := by
          have r23423 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
          have b23424 := hb (x 16 3)
          have b23425 := hb (x 16 11)
          clear * - r23423 b23424 b23425 d23415
          omega
        have d23426 : (x 19 12).toNat = 0 := by
          have r23427 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23428 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e23429 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b23430 := hb (x 16 3)
          have b23431 := hb (x 17 2)
          have b23432 := hb (x 18 13)
          have b23433 := hb (x 19 12)
          clear * - r23427 e23428 e23429 b23430 b23431 b23432 b23433 d23422
          omega
        have d23434 : (x 18 13).toNat = 0 := by
          have r23435 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23436 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e23437 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b23438 := hb (x 16 3)
          have b23439 := hb (x 17 2)
          have b23440 := hb (x 18 13)
          have b23441 := hb (x 19 12)
          clear * - r23435 e23436 e23437 b23438 b23439 b23440 b23441 d23426 d23422
          omega
        have d23442 : (x 17 2).toNat = 0 := by
          have r23443 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23444 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
          have e23445 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
          have b23446 := hb (x 16 3)
          have b23447 := hb (x 17 2)
          have b23448 := hb (x 18 13)
          have b23449 := hb (x 19 12)
          clear * - r23443 e23444 e23445 b23446 b23447 b23448 b23449 d23426 d23434 d23422
          omega
        have d23450 : (x 13 12).toNat = 0 := by
          have r23451 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23452 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e23453 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b23454 := hb (x 10 3)
          have b23455 := hb (x 11 2)
          have b23456 := hb (x 12 13)
          have b23457 := hb (x 13 12)
          clear * - r23451 e23452 e23453 b23454 b23455 b23456 b23457 d23361 d23349
          omega
        have d23458 : (x 13 4).toNat = 0 := by
          have r23459 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
          have b23460 := hb (x 13 4)
          have b23461 := hb (x 13 12)
          clear * - r23459 b23460 b23461 d23450
          omega
        have d23462 : (x 10 3).toNat = 0 := by
          have r23463 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23464 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e23465 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b23466 := hb (x 10 3)
          have b23467 := hb (x 11 2)
          have b23468 := hb (x 12 13)
          have b23469 := hb (x 13 12)
          clear * - r23463 e23464 e23465 b23466 b23467 b23468 b23469 d23450 d23361 d23349
          omega
        have d23470 : (x 10 3 && x 10 14).toNat = 0 := by
          have r23471 := hand1 (x 10 3) (x 10 14)
          have b23472 := hb (x 10 3)
          have b23473 := hb (x 10 3 && x 10 14)
          clear * - r23471 b23472 b23473 d23462
          omega
        have d23474 : (x 13 11).toNat = 1 := by
          have r23475 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23476 := hb (x 9 4)
          have b23477 := hb (x 13 11)
          have b23478 := hb (x 12 1 && x 12 12)
          have b23479 := hb (x 11 2 && x 11 13)
          have b23480 := hb (x 10 3 && x 10 14)
          clear * - r23475 b23476 b23477 b23478 b23479 b23480 d23205 d23221 d23470 d23170
          omega
        have d23481 : (x 13 3).toNat = 1 := by
          have r23482 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
          have b23483 := hb (x 13 3)
          have b23484 := hb (x 13 11)
          clear * - r23482 b23483 b23484 d23474
          omega
        have d23485 : (x 16 12).toNat = 0 := by
          have r23486 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23487 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e23488 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b23489 := hb (x 13 3)
          have b23490 := hb (x 14 2)
          have b23491 := hb (x 15 13)
          have b23492 := hb (x 16 12)
          clear * - r23486 e23487 e23488 b23489 b23490 b23491 b23492 d23481
          omega
        have d23493 : (x 16 1 && x 16 12).toNat = 0 := by
          have r23494 := hand2 (x 16 1) (x 16 12)
          have b23495 := hb (x 16 12)
          have b23496 := hb (x 16 1 && x 16 12)
          clear * - r23494 b23495 b23496 d23485
          omega
        have d23497 : (x 16 2 && x 16 12).toNat = 0 := by
          have r23498 := hand2 (x 16 2) (x 16 12)
          have b23499 := hb (x 16 12)
          have b23500 := hb (x 16 2 && x 16 12)
          clear * - r23498 b23499 b23500 d23485
          omega
        have d23501 : (x 15 13).toNat = 0 := by
          have r23502 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23503 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e23504 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b23505 := hb (x 13 3)
          have b23506 := hb (x 14 2)
          have b23507 := hb (x 15 13)
          have b23508 := hb (x 16 12)
          clear * - r23502 e23503 e23504 b23505 b23506 b23507 b23508 d23485 d23481
          omega
        have d23509 : (x 15 2 && x 15 13).toNat = 0 := by
          have r23510 := hand2 (x 15 2) (x 15 13)
          have b23511 := hb (x 15 13)
          have b23512 := hb (x 15 2 && x 15 13)
          clear * - r23510 b23511 b23512 d23501
          omega
        have d23513 : (x 15 3 && x 15 13).toNat = 0 := by
          have r23514 := hand2 (x 15 3) (x 15 13)
          have b23515 := hb (x 15 13)
          have b23516 := hb (x 15 3 && x 15 13)
          clear * - r23514 b23515 b23516 d23501
          omega
        have d23517 : (x 14 1 && x 14 14).toNat = 1 := by
          have r23518 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23519 := hb (x 13 2)
          have b23520 := hb (x 15 13)
          have b23521 := hb (x 14 1 && x 14 14)
          clear * - r23518 b23519 b23520 b23521 d23501 d23329
          omega
        have d23522 : (x 14 1).toNat = 1 := by
          have r23523 := hand1 (x 14 1) (x 14 14)
          have b23524 := hb (x 14 1)
          have b23525 := hb (x 14 1 && x 14 14)
          clear * - r23523 b23524 b23525 d23517
          omega
        have d23526 : (x 15 14).toNat = 0 := by
          have r23527 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23528 := hb (x 14 1)
          have b23529 := hb (x 15 14)
          clear * - r23527 b23528 b23529 d23522
          omega
        have d23530 : (x 15 1 && x 15 14).toNat = 0 := by
          have r23531 := hand2 (x 15 1) (x 15 14)
          have b23532 := hb (x 15 14)
          have b23533 := hb (x 15 1 && x 15 14)
          clear * - r23531 b23532 b23533 d23526
          omega
        have d23534 : (x 15 2).toNat = 0 := by
          have r23535 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
          have b23536 := hb (x 15 2)
          have b23537 := hb (x 15 14)
          clear * - r23535 b23536 b23537 d23526
          omega
        have d23538 : (x 14 2).toNat = 0 := by
          have r23539 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23540 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
          have e23541 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
          have b23542 := hb (x 13 3)
          have b23543 := hb (x 14 2)
          have b23544 := hb (x 15 13)
          have b23545 := hb (x 16 12)
          clear * - r23539 e23540 e23541 b23542 b23543 b23544 b23545 d23485 d23501 d23481
          omega
        have d23546 : (x 16 13).toNat = 1 := by
          have r23547 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23548 := hb (x 14 2)
          have b23549 := hb (x 16 13)
          have b23550 := hb (x 15 1 && x 15 14)
          clear * - r23547 b23548 b23549 b23550 d23530 d23538
          omega
        have d23551 : (x 17 12).toNat = 0 := by
          have r23552 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23553 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e23554 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b23555 := hb (x 14 3)
          have b23556 := hb (x 15 2)
          have b23557 := hb (x 16 13)
          have b23558 := hb (x 17 12)
          clear * - r23552 e23553 e23554 b23555 b23556 b23557 b23558 d23546 d23534
          omega
        have d23559 : (x 14 3).toNat = 0 := by
          have r23560 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23561 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e23562 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b23563 := hb (x 14 3)
          have b23564 := hb (x 15 2)
          have b23565 := hb (x 16 13)
          have b23566 := hb (x 17 12)
          clear * - r23560 e23561 e23562 b23563 b23564 b23565 b23566 d23551 d23546 d23534
          omega
        have d23567 : (x 14 3 && x 14 14).toNat = 0 := by
          have r23568 := hand1 (x 14 3) (x 14 14)
          have b23569 := hb (x 14 3)
          have b23570 := hb (x 14 3 && x 14 14)
          clear * - r23568 b23569 b23570 d23559
          omega
        have d23571 : (x 17 11).toNat = 1 := by
          have r23572 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23573 := hb (x 13 4)
          have b23574 := hb (x 17 11)
          have b23575 := hb (x 16 1 && x 16 12)
          have b23576 := hb (x 15 2 && x 15 13)
          have b23577 := hb (x 14 3 && x 14 14)
          clear * - r23572 b23573 b23574 b23575 b23576 b23577 d23493 d23509 d23567 d23458
          omega
        have d23578 : (x 17 3).toNat = 1 := by
          have r23579 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
          have b23580 := hb (x 17 3)
          have b23581 := hb (x 17 11)
          clear * - r23579 b23580 b23581 d23571
          omega
        have d23582 : (x 20 12).toNat = 0 := by
          have r23583 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23584 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e23585 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b23586 := hb (x 17 3)
          have b23587 := hb (x 18 2)
          have b23588 := hb (x 19 13)
          have b23589 := hb (x 20 12)
          clear * - r23583 e23584 e23585 b23586 b23587 b23588 b23589 d23578
          omega
        have d23590 : (x 19 13).toNat = 0 := by
          have r23591 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23592 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e23593 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b23594 := hb (x 17 3)
          have b23595 := hb (x 18 2)
          have b23596 := hb (x 19 13)
          have b23597 := hb (x 20 12)
          clear * - r23591 e23592 e23593 b23594 b23595 b23596 b23597 d23582 d23578
          omega
        have d23598 : (x 18 1 && x 18 14).toNat = 1 := by
          have r23599 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23600 := hb (x 17 2)
          have b23601 := hb (x 19 13)
          have b23602 := hb (x 18 1 && x 18 14)
          clear * - r23599 b23600 b23601 b23602 d23590 d23442
          omega
        have d23603 : (x 18 14).toNat = 1 := by
          have r23604 := hand2 (x 18 1) (x 18 14)
          have b23605 := hb (x 18 14)
          have b23606 := hb (x 18 1 && x 18 14)
          clear * - r23604 b23605 b23606 d23598
          omega
        have d23607 : (x 17 1).toNat = 0 := by
          have r23608 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b23609 := hb (x 17 1)
          have b23610 := hb (x 18 14)
          clear * - r23608 b23609 b23610 d23603
          omega
        have d23611 : (x 17 1 && x 17 11).toNat = 0 := by
          have r23612 := hand1 (x 17 1) (x 17 11)
          have b23613 := hb (x 17 1)
          have b23614 := hb (x 17 1 && x 17 11)
          clear * - r23612 b23613 b23614 d23607
          omega
        have d23615 : (x 18 2).toNat = 0 := by
          have r23616 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e23617 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
          have e23618 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
          have b23619 := hb (x 17 3)
          have b23620 := hb (x 18 2)
          have b23621 := hb (x 19 13)
          have b23622 := hb (x 20 12)
          clear * - r23616 e23617 e23618 b23619 b23620 b23621 b23622 d23582 d23590 d23578
          omega
        have d23623 : (x 18 10).toNat = 0 := by
          have r23624 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
          have b23625 := hb (x 18 2)
          have b23626 := hb (x 18 10)
          clear * - r23624 b23625 b23626 d23615
          omega
        have r23627 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23628 := hb (x 13 5)
        have b23629 := hb (x 18 10)
        have b23630 := hb (x 17 1 && x 17 11)
        have b23631 := hb (x 16 2 && x 16 12)
        have b23632 := hb (x 15 3 && x 15 13)
        have b23633 := hb (x 14 4 && x 14 14)
        linarith only [r23627, b23628, b23629, b23630, b23631, b23632, b23633, d23623, d23611, d23497, d23513, d23395, d23407]
    · have f23634 : (x 1 1).toNat = 1 := by rw [h19633]; rfl
      have d23635 : (x 2 14).toNat = 0 := by
        have r23636 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23637 := hb (x 1 1)
        have b23638 := hb (x 2 14)
        clear * - r23636 b23637 b23638 f23634
        omega
      have d23639 : (x 2 1 && x 2 14).toNat = 0 := by
        have r23640 := hand2 (x 2 1) (x 2 14)
        have b23641 := hb (x 2 14)
        have b23642 := hb (x 2 1 && x 2 14)
        clear * - r23640 b23641 b23642 d23635
        omega
      have d23643 : (x 2 6).toNat = 0 := by
        have r23644 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
        have b23645 := hb (x 2 6)
        have b23646 := hb (x 2 14)
        clear * - r23644 b23645 b23646 d23635
        omega
      have d23647 : (x 2 2 && x 2 6).toNat = 0 := by
        have r23648 := hand2 (x 2 2) (x 2 6)
        have b23649 := hb (x 2 6)
        have b23650 := hb (x 2 2 && x 2 6)
        clear * - r23648 b23649 b23650 d23643
        omega
      have d23651 : (x 2 2).toNat = 0 := by
        have r23652 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b23653 := hb (x 2 2)
        have b23654 := hb (x 2 14)
        clear * - r23652 b23653 b23654 d23635
        omega
      have d23655 : (x 3 13).toNat = 1 := by
        have r23656 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b23657 := hb (x 1 2)
        have b23658 := hb (x 3 13)
        have b23659 := hb (x 2 1 && x 2 14)
        clear * - r23656 b23657 b23658 b23659 d23639 g21
        omega
      have d23660 : (x 3 1).toNat = 1 := by
        have r23661 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
        have b23662 := hb (x 3 1)
        have b23663 := hb (x 3 13)
        clear * - r23661 b23662 b23663 d23655
        omega
      have d23664 : (x 4 12).toNat = 0 := by
        have r23665 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23666 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e23667 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b23668 := hb (x 1 3)
        have b23669 := hb (x 2 2)
        have b23670 := hb (x 3 13)
        have b23671 := hb (x 4 12)
        clear * - r23665 e23666 e23667 b23668 b23669 b23670 b23671 d23655 d23651
        omega
      have d23672 : (x 4 3 && x 4 12).toNat = 0 := by
        have r23673 := hand2 (x 4 3) (x 4 12)
        have b23674 := hb (x 4 12)
        have b23675 := hb (x 4 3 && x 4 12)
        clear * - r23673 b23674 b23675 d23664
        omega
      have d23676 : (x 4 4).toNat = 0 := by
        have r23677 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b23678 := hb (x 4 4)
        have b23679 := hb (x 4 12)
        clear * - r23677 b23678 b23679 d23664
        omega
      have d23680 : (x 1 3).toNat = 0 := by
        have r23681 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e23682 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e23683 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b23684 := hb (x 1 3)
        have b23685 := hb (x 2 2)
        have b23686 := hb (x 3 13)
        have b23687 := hb (x 4 12)
        clear * - r23681 e23682 e23683 b23684 b23685 b23686 b23687 d23664 d23655 d23651
        omega
      have d23688 : (x 1 3 && x 1 7).toNat = 0 := by
        have r23689 := hand1 (x 1 3) (x 1 7)
        have b23690 := hb (x 1 3)
        have b23691 := hb (x 1 3 && x 1 7)
        clear * - r23689 b23690 b23691 d23680
        omega
      have r23692 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23693 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23694 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23695 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23696 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23697 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
      have e23698 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
      have e23699 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
      have e23700 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
      have e23701 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
      have e23702 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
      have r23703 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23704 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e23705 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e23706 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e23707 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e23708 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e23709 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r23710 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23711 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
      have e23712 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
      have e23713 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
      have e23714 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
      have e23715 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
      have e23716 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
      have r23717 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23718 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e23719 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e23720 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e23721 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e23722 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e23723 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have r23724 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23725 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e23726 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have r23727 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23728 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e23729 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have r23730 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23731 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
      have e23732 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
      have r23733 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e23734 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
      have e23735 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
      have r23736 : 1 ≤ (x 1 6).toNat + (x 0 1 && x 0 7).toNat + (x (-1) 2 && x (-1) 8).toNat + (x (-2) 3 && x (-2) 9).toNat + (x (-3) 4 && x (-3) 10).toNat + (x (-4) 5 && x (-4) 11).toNat + (x (-5) 6 && x (-5) 12).toNat + (x (-6) 7 && x (-6) 13).toNat + (x (-7) 8 && x (-7) 14).toNat + (x (-8) 9).toNat := by have q := hcov6 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23737 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23738 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23739 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23740 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23741 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23742 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23743 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r23744 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have r23745 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have r23746 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
      have r23747 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
      have r23748 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have r23749 := hand1 (x (-4) 8) (x (-4) 12)
      have r23750 := hand1 (x (-5) 9) (x (-5) 13)
      have r23751 := hand2 (x 6 2) (x 6 6)
      have r23752 := hand2 (x 5 3) (x 5 7)
      have r23753 := hand1 (x (-7) 8) (x (-7) 14)
      have r23754 := hand2 (x 7 1) (x 7 7)
      have r23755 := hand2 (x 6 1) (x 6 10)
      have r23756 := hand2 (x 5 2) (x 5 11)
      have r23757 := hand2 (x 10 1) (x 10 10)
      have r23758 := hand2 (x 9 2) (x 9 11)
      have r23759 := hand1 (x 8 3) (x 8 12)
      have r23760 := hand1 (x 7 4) (x 7 13)
      have r23761 := hand1 (x 6 5) (x 6 14)
      have r23762 := hand2 (x 11 1) (x 11 11)
      have r23763 := hand1 (x 10 2) (x 10 12)
      have r23764 := hand1 (x 9 3) (x 9 13)
      have r23765 := hand1 (x 8 4) (x 8 14)
      have r23766 := hand2 (x (-8) 1) (x (-8) 12)
      have r23767 := hand2 (x (-9) 2) (x (-9) 13)
      have r23768 := hand2 (x (-10) 3) (x (-10) 14)
      have r23769 := hand2 (x (-2) 1) (x (-2) 14)
      have r23770 := hand1 (x 10 1) (x 10 14)
      have b23786 := hb (x (-6) 14)
      have b23831 := hb (x 7 1)
      linarith only [r23692, r23693, r23694, r23695, r23696, e23697, e23698, e23699, e23700, e23701, e23702, r23703, e23704, e23705, e23706, e23707, e23708, e23709, r23710, e23711, e23712, e23713, e23714, e23715, e23716, r23717, e23718, e23719, e23720, e23721, e23722, e23723, r23724, e23725, e23726, r23727, e23728, e23729, r23730, e23731, e23732, r23733, e23734, e23735, r23736, r23737, r23738, r23739, r23740, r23741, r23742, r23743, r23744, r23745, r23746, r23747, r23748, r23749, r23750, r23751, r23752, r23753, r23754, r23755, r23756, r23757, r23758, r23759, r23760, r23761, r23762, r23763, r23764, r23765, r23766, r23767, r23768, r23769, r23770, b23786, b23831, g1, g2, g3, g4, g7, g9, g12, g13, g16, g18, g19, d23680, g24, g26, g27, d23651, d23643, g31, g32, d23660, g35, g36, d23676, g38, d23647, d23688, g51, g52, g53, g54, g58, g59, g60, g61, g62, g63, d19335, g66, g67, g68, g69, g70, g71, g81, g82, g83, g84, g85, g86, g87, d23672, g107, g108]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b11110 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 6).toNat = 0)
    (g1 : (x (-3) 7).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 6).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-2) 11).toNat = 0)
    (g6 : (x (-1) 2).toNat = 0)
    (g7 : (x (-1) 5).toNat = 0)
    (g8 : (x (-1) 7).toNat = 0)
    (g9 : (x (-1) 9).toNat = 0)
    (g10 : (x (-1) 10).toNat = 0)
    (g11 : (x (-1) 11).toNat = 0)
    (g12 : (x (-1) 13).toNat = 0)
    (g13 : (x 0 4).toNat = 1)
    (g14 : (x 0 6).toNat = 1)
    (g15 : (x 0 7).toNat = 0)
    (g16 : (x 0 8).toNat = 0)
    (g17 : (x 0 9).toNat = 1)
    (g18 : (x 0 11).toNat = 1)
    (g19 : (x 0 12).toNat = 1)
    (g20 : (x 0 13).toNat = 1)
    (g21 : (x 1 2).toNat = 0)
    (g22 : (x 1 4).toNat = 0)
    (g23 : (x 1 5).toNat = 0)
    (g24 : (x 1 6).toNat = 0)
    (g25 : (x 1 8).toNat = 0)
    (g26 : (x 1 10).toNat = 0)
    (g27 : (x 1 11).toNat = 0)
    (g28 : (x 1 12).toNat = 0)
    (g29 : (x 2 4).toNat = 0)
    (g30 : (x 2 5).toNat = 0)
    (g31 : (x 2 9).toNat = 0)
    (g32 : (x 2 10).toNat = 0)
    (g33 : (x 2 11).toNat = 0)
    (g34 : (x 3 4).toNat = 0)
    (g35 : (x 3 8).toNat = 0)
    (g36 : (x 3 9).toNat = 0)
    (g37 : (x 3 10).toNat = 0)
    (g38 : (x 4 8).toNat = 0)
    (g39 : (x 4 9).toNat = 0)
    (g40 : (x 5 8).toNat = 0)
    (g41 : (x (-2) 1 && x (-2) 3).toNat = 0)
    (g42 : (x (-3) 2 && x (-3) 4).toNat = 0)
    (g43 : (x (-4) 3 && x (-4) 5).toNat = 0)
    (g44 : (x (-5) 4 && x (-5) 6).toNat = 0)
    (g45 : (x (-6) 5 && x (-6) 7).toNat = 0)
    (g46 : (x 1 2 && x 1 6).toNat = 0)
    (g47 : (x (-1) 4 && x (-1) 8).toNat = 0)
    (g48 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g49 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g50 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g51 : (x 0 4 && x 0 8).toNat = 0)
    (g52 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g53 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g54 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g55 : (x 3 4 && x 3 8).toNat = 0)
    (g56 : (x 2 5 && x 2 9).toNat = 0)
    (g57 : (x 1 6 && x 1 10).toNat = 0)
    (g58 : (x 4 4 && x 4 8).toNat = 0)
    (g59 : (x 3 5 && x 3 9).toNat = 0)
    (g60 : (x 2 6 && x 2 10).toNat = 0)
    (g61 : (x 1 7 && x 1 11).toNat = 0)
    (g62 : (x 0 8 && x 0 12).toNat = 0)
    (g63 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g64 : (x 3 8 && x 3 13).toNat = 0)
    (g65 : (x 2 9 && x 2 14).toNat = 0)
    (g66 : (x (-1) 2 && x (-1) 8).toNat = 0)
    (g67 : (x (-2) 3 && x (-2) 9).toNat = 0)
    (g68 : (x (-3) 4 && x (-3) 10).toNat = 0)
    (g69 : (x (-4) 5 && x (-4) 11).toNat = 0)
    (g70 : (x (-5) 6 && x (-5) 12).toNat = 0)
    (g71 : (x (-6) 7 && x (-6) 13).toNat = 0)
    (g72 : (x 0 2 && x 0 8).toNat = 0)
    (g73 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g74 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g75 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g76 : (x 5 2 && x 5 8).toNat = 0)
    (g77 : (x 4 3 && x 4 9).toNat = 0)
    (g78 : (x 3 4 && x 3 10).toNat = 0)
    (g79 : (x 2 5 && x 2 11).toNat = 0)
    (g80 : (x 1 6 && x 1 12).toNat = 0)
    (g81 : (x 6 2 && x 6 8).toNat = 0)
    (g82 : (x 5 3 && x 5 9).toNat = 0)
    (g83 : (x 4 4 && x 4 10).toNat = 0)
    (g84 : (x 3 5 && x 3 11).toNat = 0)
    (g85 : (x 2 6 && x 2 12).toNat = 0)
    (g86 : (x 1 7 && x 1 13).toNat = 0)
    (g87 : (x 0 8 && x 0 14).toNat = 0)
    (g88 : (x 0 1 && x 0 8).toNat = 0)
    (g89 : (x (-1) 2 && x (-1) 9).toNat = 0)
    (g90 : (x (-2) 3 && x (-2) 10).toNat = 0)
    (g91 : (x (-3) 4 && x (-3) 11).toNat = 0)
    (g92 : (x (-4) 5 && x (-4) 12).toNat = 0)
    (g93 : (x (-5) 6 && x (-5) 13).toNat = 0)
    (g94 : (x (-6) 7 && x (-6) 14).toNat = 0)
    (g95 : (x 6 1 && x 6 8).toNat = 0)
    (g96 : (x 5 2 && x 5 9).toNat = 0)
    (g97 : (x 4 3 && x 4 10).toNat = 0)
    (g98 : (x 3 4 && x 3 11).toNat = 0)
    (g99 : (x 2 5 && x 2 12).toNat = 0)
    (g100 : (x 1 6 && x 1 13).toNat = 0)
    (g101 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g102 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g103 : (x (-1) 2 && x (-1) 11).toNat = 0)
    (g104 : (x (-2) 3 && x (-2) 12).toNat = 0)
    (g105 : (x (-3) 4 && x (-3) 13).toNat = 0)
    (g106 : (x (-4) 5 && x (-4) 14).toNat = 0)
    (g107 : (x 3 4 && x 3 13).toNat = 0)
    (g108 : (x 2 5 && x 2 14).toNat = 0)
    (g109 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g110 : (x (-2) 1 && x (-2) 11).toNat = 0)
    (g111 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g112 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g113 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g114 : (x 2 4 && x 2 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_b11110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 g75 g76 g77 g78 g79 g80 g81 g82 g83 g84 g85 g86 g87 g88 g89 g90 g91 g92 g93 g94 g95 g96 g97 g98 g99 g100 g101 g102 g103 g104 g105 g106 g107 g108 g109 g110 g111 g112 g113 g114
